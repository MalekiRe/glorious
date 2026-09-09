use super::*;
impl RuntimeMir {
    /// Import the immutable PlaceFlow ownership graph at the MIR boundary.
    /// This consumes the exact analysis IDs and never resolves a path from a
    /// source spelling, so nested bindings with the same spelling remain
    /// distinct in the frozen artifact.
    pub fn with_frozen_move_paths(mut self, flow: &PlaceFlow) -> Self {
        let bindings = flow
            .bindings
            .iter()
            .enumerate()
            .map(|(_index, binding)| MirPlaceBindingData {
                source: binding.id,
                origin: binding.origin.clone(),
                spelling: binding.spelling.clone(),
            })
            .collect::<Vec<_>>();
        let paths = flow
            .move_paths
            .iter()
            .enumerate()
            .map(|(_index, path)| MirMovePathData {
                parent: path.parent.map(|parent| MirMovePathId(parent.0)),
                binding: MirPlaceBindingId(path.binding.0),
                field: path.field,
            })
            .collect::<Vec<_>>();
        debug_assert!(
            bindings
                .iter()
                .enumerate()
                .all(|(index, binding)| { binding.source.0 as usize == index })
        );
        debug_assert!(paths.iter().enumerate().all(|(index, path)| {
            path.parent.is_none_or(|parent| (parent.0 as usize) < index)
                && (path.binding.0 as usize) < bindings.len()
        }));
        let cleanup_paths = (|| {
            if flow.final_move_paths.len() != flow.moved_places.len() {
                return None;
            }
            let mut seen = BTreeSet::new();
            flow.final_move_paths
                .iter()
                .zip(&flow.moved_places)
                .map(|(path, fact)| {
                    if !seen.insert(*path) {
                        return None;
                    }
                    let node = flow.move_paths.get(path.0 as usize)?;
                    let binding = flow.bindings.get(node.binding.0 as usize)?;
                    if binding.id != node.binding || binding.spelling != fact.root {
                        return None;
                    }
                    let mut fields = Vec::new();
                    let mut cursor = Some(*path);
                    while let Some(current) = cursor {
                        let node = flow.move_paths.get(current.0 as usize)?;
                        if node.binding != binding.id {
                            return None;
                        }
                        if let Some(field) = node.field {
                            fields.push(field);
                        }
                        cursor = node.parent;
                    }
                    fields.reverse();
                    (fields == fact.fields).then_some(MirMovePathId(path.0))
                })
                .collect::<Option<Vec<_>>>()
        })();
        self.control.move_paths = MirMovePathTables { bindings, paths };
        for block in &mut self.blocks {
            if let RuntimeTerminator::Leave { cleanup, .. } = &mut block.terminator {
                if cleanup.moved_places == flow.moved_places {
                    cleanup.moved_paths = cleanup_paths.clone().unwrap_or_default();
                }
            }
        }
        self
    }

    /// Import source-storage ownership boundaries from the same PlaceFlow
    /// product as move paths.  Consumers therefore obtain a typed lifetime
    /// graph rather than reconstructing lexical scope from local spellings.
    pub fn with_frozen_source_storage(mut self, flow: &PlaceFlow) -> Self {
        self = self.with_frozen_source_storage_bindings(flow, &BTreeMap::new());
        self
    }

    pub(super) fn with_frozen_source_storage_bindings(
        mut self,
        flow: &PlaceFlow,
        bindings: &BTreeMap<PlaceBindingOrigin, MirLocal>,
    ) -> Self {
        let mut storage = MirSourceStorageTables::from_placeflow(flow);
        for (index, binding) in self.control.move_paths.bindings.iter().enumerate() {
            let local = match binding.origin {
                PlaceBindingOrigin::Parameter { index } => {
                    self.parameters.get(index as usize).copied()
                }
                PlaceBindingOrigin::Let { expression } => self
                    .locals
                    .iter()
                    .position(|local| local.source == expression)
                    .map(|index| MirLocal(index as u32)),
                PlaceBindingOrigin::Temporary { .. }
                | PlaceBindingOrigin::HandlerBinder { .. }
                | PlaceBindingOrigin::HandlerResumption { .. }
                | PlaceBindingOrigin::CompletionBinder { .. } => {
                    bindings.get(&binding.origin).copied()
                }
            };
            storage.binding_locals[index] = local;
        }
        // Lowered payload/completion binders map to their real owning slots.
        // Statically eliminated binders and resumptions still receive a Unit
        // lifecycle marker, so the source-storage graph remains total without
        // pretending that such a marker owns an executable payload.
        for local in &mut storage.binding_locals {
            if local.is_some() {
                continue;
            }
            let id = MirLocal(u32::try_from(self.locals.len()).expect("MIR local arena overflow"));
            self.locals.push(MirLocalDecl {
                ty: Type::Unit,
                source: CoreId(u32::MAX),
            });
            *local = Some(id);
        }
        // Every executable source owner receives one compiler-created drop
        // flag.  An ordinary source assignment is not a raw register
        // overwrite: the old owner is first conditionally disarmed, then the
        // replacement initializes the exact same storage and rearms it. This
        // makes assignment after a whole move and replacement of an
        // initialized owner explicit without asking the VM to infer lifetime
        // from a register number.
        let parameter_locals = self.parameters.iter().copied().collect::<BTreeSet<_>>();
        let mut storage_flags = BTreeMap::new();
        for local in storage.binding_locals.iter().flatten().copied() {
            storage_flags.entry(local).or_insert_with(|| {
                let flag =
                    MirLocal(u32::try_from(self.locals.len()).expect("MIR local arena overflow"));
                self.locals.push(MirLocalDecl {
                    ty: Type::Scalar(crate::types::ScalarType::Bool),
                    source: CoreId(u32::MAX),
                });
                flag
            });
        }

        // Materialize the frozen lifecycle contract at the first executable
        // program point. Parameters are initialized by the call ABI; every
        // mapped non-parameter source slot begins dead and receives
        // `StorageLive` before any direct definition can make it readable.
        let lives = storage
            .binding_locals
            .iter()
            .enumerate()
            .filter_map(|(binding, local)| {
                local
                    .filter(|local| !parameter_locals.contains(local))
                    .map(|local| RuntimeOperation::StorageLive {
                        binding: MirPlaceBindingId(binding as u32),
                        local,
                    })
            })
            .collect::<Vec<_>>();
        let mut initial_flags = storage_flags
            .iter()
            .map(|(local, flag)| RuntimeOperation::SetDropFlag {
                flag: *flag,
                value: parameter_locals.contains(local),
            })
            .collect::<Vec<_>>();
        initial_flags.extend(lives);
        if !initial_flags.is_empty() {
            let entry = self.entry.0 as usize;
            if let Some(block) = self.blocks.get_mut(entry) {
                block.instructions.splice(0..0, initial_flags);
            }
        }

        for block_index in 0..self.blocks.len() {
            let instructions = std::mem::take(&mut self.blocks[block_index].instructions);
            let mut rewritten = Vec::with_capacity(instructions.len());
            // A block reached through a CFG edge may inherit an initialized
            // source owner. Start conservatively armed, then retain the
            // precise same-block transition for an immediately preceding
            // move. An unnecessary conditional destroy of an uninitialized
            // slot is a checked no-op; omitting a required destroy is not.
            let mut initialized = storage_flags.keys().copied().collect::<BTreeSet<_>>();
            for mut instruction in instructions {
                // The first definition of a lexical binding is source
                // storage too. Keep the evaluator's ordinary Copy/Move in a
                // fresh temporary and funnel the resulting value through the
                // same typed Store transition used by later assignment.
                match instruction {
                    RuntimeOperation::Copy { dst, src } if storage_flags.contains_key(&dst) => {
                        let temporary = MirLocal(
                            u32::try_from(self.locals.len()).expect("MIR local arena overflow"),
                        );
                        let ty = self.locals[dst.0 as usize].ty.clone();
                        self.locals.push(MirLocalDecl {
                            ty,
                            source: CoreId(u32::MAX),
                        });
                        rewritten.push(RuntimeOperation::Copy {
                            dst: temporary,
                            src,
                        });
                        instruction = RuntimeOperation::Store {
                            dst,
                            src: temporary,
                        };
                    }
                    RuntimeOperation::Move { dst, src } if storage_flags.contains_key(&dst) => {
                        let temporary = MirLocal(
                            u32::try_from(self.locals.len()).expect("MIR local arena overflow"),
                        );
                        let ty = self.locals[dst.0 as usize].ty.clone();
                        self.locals.push(MirLocalDecl {
                            ty,
                            source: CoreId(u32::MAX),
                        });
                        rewritten.push(RuntimeOperation::Move {
                            dst: temporary,
                            src,
                        });
                        instruction = RuntimeOperation::Store {
                            dst,
                            src: temporary,
                        };
                    }
                    _ => {}
                }
                if let RuntimeOperation::Store { dst, .. } = &instruction {
                    let dst = *dst;
                    if let Some(flag) = storage_flags.get(&dst) {
                        if initialized.contains(&dst) {
                            // Destroy while the flag is still armed, then
                            // disarm the old resident before publishing the
                            // replacement value.
                            rewritten.push(RuntimeOperation::DestroyIf {
                                local: dst,
                                flag: *flag,
                            });
                            rewritten.push(RuntimeOperation::SetDropFlag {
                                flag: *flag,
                                value: false,
                            });
                        }
                    }
                    rewritten.push(instruction);
                    if let Some(flag) = storage_flags.get(&dst) {
                        rewritten.push(RuntimeOperation::SetDropFlag {
                            flag: *flag,
                            value: true,
                        });
                    }
                    initialized.insert(dst);
                    continue;
                }

                let destination = destination(&instruction);
                let moved = match instruction {
                    RuntimeOperation::Move { src, .. } => Some(src),
                    _ => None,
                };
                rewritten.push(instruction);
                if let Some(destination) = destination {
                    if let Some(flag) = storage_flags.get(&destination) {
                        rewritten.push(RuntimeOperation::SetDropFlag {
                            flag: *flag,
                            value: true,
                        });
                        initialized.insert(destination);
                    }
                }
                if let Some(source) = moved {
                    if let Some(flag) = storage_flags.get(&source) {
                        rewritten.push(RuntimeOperation::SetDropFlag {
                            flag: *flag,
                            value: false,
                        });
                        initialized.remove(&source);
                    }
                }
            }
            self.blocks[block_index].instructions = rewritten;
        }
        self.elaborate_source_storage_leaves(&storage, &flow.label_storage_exits);
        self.control.source_storage = storage;
        self
    }

    /// Turn the lexical source-storage boundary recorded by PlaceFlow into
    /// the executable cleanup witness carried by every static `Leave`.
    ///
    /// This is deliberately an elaboration at the immutable PlaceFlow-to-MIR
    /// boundary: a label brand is the source authority for the scope exit,
    /// while the frozen storage table supplies the exact owners and locals.
    /// No CFG shape, local spelling, or individual source test is used to
    /// rediscover either fact.
    fn elaborate_source_storage_leaves(
        &mut self,
        storage: &MirSourceStorageTables,
        label_exits: &BTreeMap<
            crate::LabelBrand,
            (crate::SourceStorageScopeId, crate::SourceStorageScopeId),
        >,
    ) {
        for block in &mut self.blocks {
            let RuntimeTerminator::Leave {
                brand,
                arguments,
                cleanup,
                ..
            } = &mut block.terminator
            else {
                continue;
            };
            // Raw MIR is intentionally not elaborated here: only a boundary
            // explicitly supplied by the source ownership analysis may gain
            // an executable cleanup witness.
            let Some(&(source, target)) = label_exits.get(brand) else {
                continue;
            };
            let source = MirSourceStorageScopeId(source.0);
            let target = MirSourceStorageScopeId(target.0);
            let Ok(exited) = storage.exited_bindings(source, target) else {
                continue;
            };
            // Crossing an empty syntactic block does not end an addressable
            // source lifetime. Preserve the existing same-scope ownership
            // facts on that `Leave` (notably a residual partial move of an
            // outer owner) instead of fabricating a storage boundary.
            if exited.is_empty() {
                continue;
            }
            cleanup.source_storage_scope = source;
            cleanup.target_storage_scope = target;
            cleanup.drop_flags = exited
                .iter()
                .enumerate()
                .map(|(index, &binding)| MirCleanupDropFlag {
                    id: MirDropFlagId(index as u32),
                    binding,
                })
                .collect();
            cleanup.protected_values = arguments.clone();
            cleanup.actions.clear();
            for (index, binding) in exited.into_iter().enumerate() {
                let flag = MirDropFlagId(index as u32);
                if cleanup
                    .active_loans
                    .iter()
                    .any(|loan| loan.binding.0 == binding.0)
                {
                    cleanup
                        .actions
                        .push(MirCleanupAction::EndBorrow { binding });
                }
                match storage.binding_local(binding) {
                    Some(local) if arguments.contains(&local) => cleanup
                        .actions
                        .push(MirCleanupAction::Protect { binding, local }),
                    _ => cleanup
                        .actions
                        .push(MirCleanupAction::Drop { binding, flag }),
                }
                cleanup
                    .actions
                    .push(MirCleanupAction::ClearDropFlag { flag });
                cleanup
                    .actions
                    .push(MirCleanupAction::StorageDead { binding });
            }
        }
    }
}
