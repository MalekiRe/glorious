//! Finite machine-primitive authority bound to a trusted library identity.
//!
//! Source names are never authority.  A request host supplies selectors for a
//! distinguished standard-library package; binding resolves them to exact
//! public declaration identities and freezes a digestible table.

use std::collections::BTreeMap;

use crate::{
    ElaboratedHeader, ElaboratedInterface, PackageInterface, PackageKey, Quantity, ScalarType,
    Type,
    identity::{DefKey, Digest},
    types::EffectRow,
};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum PrimitiveRole {
    /// The finite control leaf used by the standard library's conventional
    /// conditional combinator. It is polymorphic in its result and receives
    /// two zero-argument callables, so source spelling alone cannot become a
    /// branch primitive.
    BranchBool,
}
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct PrimitiveSelector {
    pub role: PrimitiveRole,
    pub module_path: String,
    pub name: String,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuntimeManifestInput {
    pub standard_library: PackageKey,
    pub selectors: Vec<PrimitiveSelector>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TrustedRuntimeManifest {
    pub standard_library: PackageKey,
    pub primitives: BTreeMap<PrimitiveRole, DefKey>,
    pub digest: Digest,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ManifestError {
    MissingRole(PrimitiveRole),
    DuplicateRole(PrimitiveRole),
    MissingDeclaration {
        module_path: String,
        name: String,
    },
    AmbiguousDeclaration {
        module_path: String,
        name: String,
    },
    NonPublicDeclaration {
        definition: DefKey,
    },
    IncompatibleSignature {
        role: PrimitiveRole,
        definition: DefKey,
    },
}

impl RuntimeManifestInput {
    pub fn canonicalize(&mut self) -> Result<(), ManifestError> {
        self.selectors.sort();
        for pair in self.selectors.windows(2) {
            if pair[0].role == pair[1].role {
                return Err(ManifestError::DuplicateRole(pair[0].role));
            }
        }
        Ok(())
    }
    pub fn bind(
        &self,
        interfaces: impl IntoIterator<Item = PackageInterface>,
        signatures: &ElaboratedInterface,
    ) -> Result<TrustedRuntimeManifest, ManifestError> {
        let interfaces = interfaces
            .into_iter()
            .filter(|interface| interface.package == self.standard_library)
            .collect::<Vec<_>>();
        let mut selectors = BTreeMap::new();
        for selector in &self.selectors {
            if selectors.insert(selector.role, selector).is_some() {
                return Err(ManifestError::DuplicateRole(selector.role));
            }
        }
        let mut primitives = BTreeMap::new();
        let role = PrimitiveRole::BranchBool;
        let selector = selectors
            .get(&role)
            .ok_or(ManifestError::MissingRole(role))?;
        let candidates = interfaces
            .iter()
            .filter(|interface| interface.module.path == selector.module_path)
            .flat_map(|interface| interface.definitions.iter())
            .filter(|definition| definition.name.as_deref() == Some(selector.name.as_str()))
            .collect::<Vec<_>>();
        let definition = match candidates.as_slice() {
            [] => {
                return Err(ManifestError::MissingDeclaration {
                    module_path: selector.module_path.clone(),
                    name: selector.name.clone(),
                });
            }
            [definition] => *definition,
            _ => {
                return Err(ManifestError::AmbiguousDeclaration {
                    module_path: selector.module_path.clone(),
                    name: selector.name.clone(),
                });
            }
        };
        if !definition.public {
            return Err(ManifestError::NonPublicDeclaration {
                definition: definition.key,
            });
        }
        let Some(ElaboratedHeader::Callable(signature)) =
            signatures.definitions.get(&definition.key)
        else {
            return Err(ManifestError::IncompatibleSignature {
                role,
                definition: definition.key,
            });
        };
        if signature != &expected_signature(role) {
            return Err(ManifestError::IncompatibleSignature {
                role,
                definition: definition.key,
            });
        }
        primitives.insert(role, definition.key);
        Ok(TrustedRuntimeManifest {
            standard_library: self.standard_library.clone(),
            digest: manifest_digest(&self.standard_library, &primitives),
            primitives,
        })
    }
}
fn expected_signature(role: PrimitiveRole) -> crate::CallableSignature {
    match role {
        PrimitiveRole::BranchBool => {
            let result = Type::Generic(0);
            let thunk = Type::Callable {
                parameters: vec![],
                result: Box::new(result.clone()),
                effects: EffectRow::empty(),
                invocation: Quantity::ONCE,
            };
            crate::CallableSignature {
                generics: 1,
                parameters: vec![Type::Scalar(ScalarType::Bool), thunk.clone(), thunk],
                result,
                effects: EffectRow::empty(),
                invocation: Quantity::ONCE,
                where_bounds: vec![],
            }
        }
    }
}
fn manifest_digest(
    standard_library: &PackageKey,
    primitives: &BTreeMap<PrimitiveRole, DefKey>,
) -> Digest {
    let mut bytes = b"grandiose-stage0-runtime-manifest-v1".to_vec();
    bytes.extend_from_slice(&(standard_library.0.len() as u64).to_le_bytes());
    bytes.extend_from_slice(standard_library.0.as_bytes());
    for (role, definition) in primitives {
        bytes.push(match role {
            PrimitiveRole::BranchBool => 0,
        });
        bytes.extend_from_slice(&definition.0.as_bytes());
    }
    Digest::of_bytes(&bytes)
}
