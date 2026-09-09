use super::*;

impl SpecializedMir {
    pub(super) fn freeze_layouts(
        &mut self,
        signatures: &crate::ElaboratedInterface,
    ) -> Result<(), SpecializedError> {
        fn collect(
            ty: &Type,
            signatures: &crate::ElaboratedInterface,
            layouts: &mut Vec<SpecializedLayout>,
            building: &mut BTreeSet<Vec<u8>>,
        ) -> Result<(), SpecializedError> {
            if let Some(callable) = crate::types::label::callable(ty) {
                return collect(&callable, signatures, layouts, building);
            }
            match ty {
                Type::Tuple(fields) => {
                    for field in fields {
                        collect(field, signatures, layouts, building)?;
                    }
                }
                Type::Array(element)
                | Type::FixedArray { element, .. }
                | Type::StaticData { element, .. }
                | Type::Reference {
                    referent: element, ..
                }
                | Type::RawPointer {
                    pointee: element, ..
                } => collect(element, signatures, layouts, building)?,
                Type::Callable {
                    parameters, result, ..
                } => {
                    // These types are leaving their callable binder when
                    // they become standalone layout obligations. Open that
                    // binder for layout collection only; retain the complete
                    // higher-ranked contract on the original callable value.
                    for parameter in parameters {
                        collect(&regions::body_type(parameter), signatures, layouts, building)?;
                    }
                    collect(&regions::body_type(result), signatures, layouts, building)?;
                }
                Type::Nominal {
                    definition,
                    arguments,
                } => {
                    if layouts.iter().any(|layout| &layout.ty == ty) {
                        return Ok(());
                    }
                    let key = crate::types::canonical_type_encoding(ty);
                    if building.len() >= 128 || key.len() > 65_536 || layouts.len() >= 8_192 {
                        return Err(SpecializedError("concrete nominal layout expansion exceeds its finite representation budget".into()));
                    }
                    if !building.insert(key.clone()) {
                        return Ok(());
                    }
                    if *definition == crate::refinement::bindings_definition() {
                        let fields = crate::refinement::binding_pack_fields(ty)
                            .ok_or_else(|| SpecializedError("binding pack lacks a canonical sealed environment layout".into()))?.to_vec();
                        let source_contract = crate::refinement::binding_pack_contract(ty).expect("checked binding pack");
                        layouts.push(SpecializedLayout { ty: ty.clone(), source_contract, is_enum: false, variants: vec![fields.clone()] });
                        for field in fields { collect(&field, signatures, layouts, building)?; }
                        building.remove(&key);
                        return Ok(());
                    }
                    let header = signatures.definitions.get(definition);
                    let (is_enum, variants) = match header {
                        Some(crate::ElaboratedHeader::Nominal {
                            layout: crate::signature::ElaboratedNominalLayout::Struct(_) | crate::signature::ElaboratedNominalLayout::TupleStruct(_),
                            ..
                        }) => (
                            false,
                            vec![
                                signatures
                                    .instantiate_struct_fields_generic(*definition, arguments)
                                    .map_err(|error| {
                                        SpecializedError(format!(
                                            "concrete record layout: {error:?}"
                                        ))
                                    })?
                                    .into_iter()
                                    .map(|field| field.ty)
                                    .collect::<Vec<_>>(),
                            ],
                        ),
                        Some(crate::ElaboratedHeader::Nominal {
                            layout: crate::signature::ElaboratedNominalLayout::Enum(variants),
                            ..
                        }) => (
                            true,
                            variants
                                .iter()
                                .enumerate()
                                .map(|(index, _)| {
                                    signatures
                                        .instantiate_enum_fields_generic(
                                            *definition,
                                            arguments,
                                            index as u32,
                                        )
                                        .map(|fields| {
                                            fields
                                                .into_iter()
                                                .map(|field| field.ty)
                                                .collect::<Vec<_>>()
                                        })
                                        .map_err(|error| {
                                            SpecializedError(format!(
                                                "concrete enum layout: {error:?}"
                                            ))
                                        })
                                })
                                .collect::<Result<Vec<_>, _>>()?,
                        ),
                        _ => {
                            building.remove(&key);
                            return Ok(());
                        }
                    };
                    let source_contract = header
                        .and_then(|header| {
                            crate::signature::nominal_contract_fingerprint(*definition, header)
                        })
                        .ok_or_else(|| {
                            SpecializedError("nominal layout has no declaration contract".into())
                        })?;
                    let mut solver = crate::TraitSolver::new(signatures);
                    let variants = variants
                        .into_iter()
                        .map(|fields| {
                            fields
                                .into_iter()
                                .map(|field| {
                                    let field = solver.normalize_type(field).map_err(|error| {
                                        SpecializedError(format!(
                                            "concrete field normalization: {error:?}"
                                        ))
                                    })?;
                                    crate::service::normalize_materialized_type(&field, &mut solver)
                                        .map_err(SpecializedError)
                                })
                                .collect::<Result<Vec<_>, _>>()
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    layouts.push(SpecializedLayout {
                        ty: ty.clone(),
                        source_contract,
                        is_enum,
                        variants: variants.clone(),
                    });
                    for fields in variants {
                        for field in fields {
                            collect(&field, signatures, layouts, building)?;
                        }
                    }
                    building.remove(&key);
                }
                _ => {}
            }
            Ok(())
        }
        for ty in self
            .values
            .iter()
            .map(|value| &value.ty)
            .chain(std::iter::once(&self.result))
        {
            collect(ty, signatures, &mut self.layouts, &mut BTreeSet::new())?;
        }
        Ok(())
    }
}

/// Distinct instantiations of a declaration are distinct layout obligations.
/// References do not require inline copy layout for their pointees; tuple and
/// array fields and nested nominal instances do.
pub(crate) fn validate_layout_closure(
    layouts: &[SpecializedLayout],
) -> Result<(), SpecializedError> {
    let definitions = layouts
        .iter()
        .filter_map(|layout| match layout.ty {
            Type::Nominal { definition, .. } => Some(definition),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    fn field(
        ty: &Type,
        layouts: &[SpecializedLayout],
        definitions: &BTreeSet<DefKey>,
    ) -> Result<(), SpecializedError> {
        match ty {
            Type::Nominal { definition, .. } if definitions.contains(definition) => {
                if !layouts.iter().any(|layout| &layout.ty == ty) {
                    return Err(SpecializedError(format!(
                        "concrete nominal layout closure omits a nested instance: {ty:?}"
                    )));
                }
            }
            Type::Tuple(fields) => {
                for ty in fields {
                    field(ty, layouts, definitions)?;
                }
            }
            Type::Array(ty) | Type::FixedArray { element: ty, .. } => field(ty, layouts, definitions)?,
            _ => {}
        }
        Ok(())
    }
    for layout in layouts {
        if matches!(&layout.ty, Type::Nominal { definition, .. } if *definition == crate::refinement::bindings_definition()) {
            let expected = crate::refinement::binding_pack_fields(&layout.ty)
                .ok_or_else(|| SpecializedError("binding pack has no canonical environment layout".into()))?;
            if layout.is_enum || layout.variants.as_slice() != [expected.to_vec()]
                || Some(layout.source_contract) != crate::refinement::binding_pack_contract(&layout.ty) {
                return Err(SpecializedError("binding pack layout disagrees with its sealed environment".into()));
            }
        }
        for ty in layout.variants.iter().flatten() {
            field(ty, layouts, &definitions)?;
        }
    }
    Ok(())
}
