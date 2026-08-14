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
    /// The capability-free byte-length operation for immutable UTF-8 `Text`.
    /// It is deliberately bound to one standard-library declaration identity;
    /// a source function named `text_byte_len` never receives primitive
    /// authority merely by spelling.
    TextByteLen,
    /// Capability-free concatenation over immutable UTF-8 text values.
    TextConcat,
    /// Capability-free equality predicate with the G1 `u32` boolean ABI.
    TextEq,
    /// Checked conversion from a frozen byte sequence to UTF-8 text.
    TextFromUtf8Checked,
    /// Borrow-free frozen byte snapshot of a UTF-8 text value.
    TextAsBytes,
    /// Checked Unicode scalar construction from the G1 `u32` character ABI.
    CharFromU32Checked,
    /// Canonical Unicode scalar extraction to the G1 `u32` character ABI.
    CharToU32,
}

impl PrimitiveRole {
    pub const fn selector_name(self) -> &'static str {
        match self {
            Self::BranchBool => "branch-bool",
            Self::TextByteLen => "text-byte-len",
            Self::TextConcat => "text-concat",
            Self::TextEq => "text-eq",
            Self::TextFromUtf8Checked => "text-from-utf8-checked",
            Self::TextAsBytes => "text-as-bytes",
            Self::CharFromU32Checked => "char-from-u32-checked",
            Self::CharToU32 => "char-to-u32",
        }
    }

    pub fn parse_selector_name(value: &str) -> Option<Self> {
        Some(match value {
            "branch-bool" => Self::BranchBool,
            "text-byte-len" => Self::TextByteLen,
            "text-concat" => Self::TextConcat,
            "text-eq" => Self::TextEq,
            "text-from-utf8-checked" => Self::TextFromUtf8Checked,
            "text-as-bytes" => Self::TextAsBytes,
            "char-from-u32-checked" => Self::CharFromU32Checked,
            "char-to-u32" => Self::CharToU32,
            _ => return None,
        })
    }
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
    DuplicateRole(PrimitiveRole),
    MissingDeclaration {
        module_path: String,
        name: String,
    },
    AmbiguousDeclaration {
        module_path: String,
        name: String,
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
        // A manifest is an exact finite grant set, rather than a statement
        // that every primitive known to this compiler generation is present.
        // A bootstrap world can therefore expose only the leaves supplied by
        // its standard-library revision; calls to an unbound leaf remain
        // ordinary source calls and its opaque placeholder body is rejected.
        for (role, selector) in selectors {
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
            // Runtime authority is a host-supplied binding to one exact
            // declaration in the distinguished standard-library package.
            // It is intentionally independent of ordinary source visibility:
            // canonical layer-1 leaves are private implementation details,
            // while downstream callers reach public wrappers.  Requiring
            // `pub` here would make the bootstrap source unable to bind its
            // own trusted leaves without incorrectly exporting them.
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
        }
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
                lifetime_binders: 0,
                parameters: vec![],
                result: Box::new(result.clone()),
                effects: EffectRow::empty(),
                invocation: Quantity::ONCE,
            };
            crate::CallableSignature {
                generics: 1,
                generic_kinds: vec![crate::GenericKind::Type],
                parameters: vec![Type::Scalar(ScalarType::Bool), thunk.clone(), thunk],
                result,
                effects: EffectRow::empty(),
                invocation: Quantity::ONCE,
                where_bounds: vec![],
                where_associated_type_bindings: vec![],
                where_associated_effect_bindings: vec![],
            }
        }
        PrimitiveRole::TextByteLen => crate::CallableSignature {
            generics: 0,
            generic_kinds: vec![],
            parameters: vec![Type::Scalar(ScalarType::Text)],
            result: Type::Scalar(ScalarType::Usize),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::TextConcat => crate::CallableSignature {
            generics: 0,
            generic_kinds: vec![],
            parameters: vec![
                Type::Scalar(ScalarType::Text),
                Type::Scalar(ScalarType::Text),
            ],
            result: Type::Scalar(ScalarType::Text),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::TextEq => crate::CallableSignature {
            generics: 0,
            generic_kinds: vec![],
            parameters: vec![
                Type::Scalar(ScalarType::Text),
                Type::Scalar(ScalarType::Text),
            ],
            result: Type::Scalar(ScalarType::U32),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::TextFromUtf8Checked => crate::CallableSignature {
            generics: 0,
            generic_kinds: vec![],
            parameters: vec![Type::Scalar(ScalarType::Bytes)],
            result: Type::Scalar(ScalarType::Text),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::TextAsBytes => crate::CallableSignature {
            generics: 0,
            generic_kinds: vec![],
            parameters: vec![Type::Scalar(ScalarType::Text)],
            result: Type::Scalar(ScalarType::Bytes),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::CharFromU32Checked => crate::CallableSignature {
            generics: 0,
            generic_kinds: vec![],
            parameters: vec![Type::Scalar(ScalarType::U32)],
            result: Type::Scalar(ScalarType::Char),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
        PrimitiveRole::CharToU32 => crate::CallableSignature {
            generics: 0,
            generic_kinds: vec![],
            parameters: vec![Type::Scalar(ScalarType::Char)],
            result: Type::Scalar(ScalarType::U32),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
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
            PrimitiveRole::TextByteLen => 1,
            PrimitiveRole::TextConcat => 2,
            PrimitiveRole::TextEq => 3,
            PrimitiveRole::TextFromUtf8Checked => 4,
            PrimitiveRole::TextAsBytes => 5,
            PrimitiveRole::CharFromU32Checked => 6,
            PrimitiveRole::CharToU32 => 7,
        });
        bytes.extend_from_slice(&definition.0.as_bytes());
    }
    Digest::of_bytes(&bytes)
}
