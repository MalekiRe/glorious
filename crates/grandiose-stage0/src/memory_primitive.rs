//! Machine memory operations, not collection algorithms. Each declaration is
//! bound by the host's runtime manifest; source spelling grants no authority.

use crate::{
    CallableSignature, EffectRow, GenericKind, Lifetime, Mutability, PointerMutability, Quantity,
    Safety, ScalarType, Type,
};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum MemoryPrimitive {
    SizeOf,
    AlignOf,
    Null,
    Dangling,
    Allocate,
    Reallocate,
    Deallocate,
    IsNull,
    Offset,
    OffsetConst,
    Cast,
    AsConst,
    Read,
    Write,
    Copy,
    CopyNonoverlapping,
    BorrowShared,
    BorrowUnique,
}

impl MemoryPrimitive {
    pub const ALL: [Self; 18] = [
        Self::SizeOf,
        Self::AlignOf,
        Self::Null,
        Self::Dangling,
        Self::Allocate,
        Self::Reallocate,
        Self::Deallocate,
        Self::IsNull,
        Self::Offset,
        Self::OffsetConst,
        Self::Cast,
        Self::AsConst,
        Self::Read,
        Self::Write,
        Self::Copy,
        Self::CopyNonoverlapping,
        Self::BorrowShared,
        Self::BorrowUnique,
    ];

    pub const fn selector_name(self) -> &'static str {
        match self {
            Self::SizeOf => "memory-size-of",
            Self::AlignOf => "memory-align-of",
            Self::Null => "memory-null",
            Self::Dangling => "memory-dangling",
            Self::Allocate => "memory-allocate",
            Self::Reallocate => "memory-reallocate",
            Self::Deallocate => "memory-deallocate",
            Self::IsNull => "memory-is-null",
            Self::Offset => "memory-offset",
            Self::OffsetConst => "memory-offset-const",
            Self::Cast => "memory-cast",
            Self::AsConst => "memory-as-const",
            Self::Read => "memory-read",
            Self::Write => "memory-write",
            Self::Copy => "memory-copy",
            Self::CopyNonoverlapping => "memory-copy-nonoverlapping",
            Self::BorrowShared => "memory-borrow-shared",
            Self::BorrowUnique => "memory-borrow-unique",
        }
    }

    pub(crate) fn ordinal(self) -> u8 {
        Self::ALL.iter().position(|value| *value == self).unwrap() as u8
    }

    pub fn safety(self) -> Safety {
        match self {
            Self::SizeOf | Self::AlignOf => Safety::Safe,
            // All raw-pointer operations require explicit unsafe scopes,
            // including address-only construction and conversion.
            _ => Safety::Unsafe,
        }
    }

    pub(crate) fn signature(self) -> CallableSignature {
        let t = Type::Generic(0);
        let ptr = |mutability, pointee| Type::RawPointer {
            mutability,
            pointee: Box::new(pointee),
        };
        let writable = |pointee| ptr(PointerMutability::Mut, pointee);
        let readable = |pointee| ptr(PointerMutability::Const, pointee);
        let count = Type::Scalar(ScalarType::Usize);
        let byte_pointer = writable(Type::Scalar(ScalarType::U8));
        let (generics, parameters, result) = match self {
            Self::SizeOf | Self::AlignOf => (1, vec![], count),
            Self::Null | Self::Dangling => (1, vec![], writable(t)),
            // Allocation failure returns null; reallocation failure leaves the
            // old allocation intact. Invalid layouts remain checked errors.
            Self::Allocate => (0, vec![count.clone(), count], byte_pointer),
            Self::Reallocate => (
                0,
                vec![byte_pointer.clone(), count.clone(), count.clone(), count],
                byte_pointer,
            ),
            Self::Deallocate => (0, vec![byte_pointer, count.clone(), count], Type::Unit),
            Self::IsNull => (1, vec![writable(t)], Type::Scalar(ScalarType::U32)),
            Self::Offset => (1, vec![writable(t.clone()), count], writable(t)),
            Self::OffsetConst => (1, vec![readable(t.clone()), count], readable(t)),
            Self::Cast => (2, vec![writable(t)], writable(Type::Generic(1))),
            Self::AsConst => (1, vec![writable(t.clone())], readable(t)),
            Self::Read => (1, vec![readable(t.clone())], t),
            Self::Write => (1, vec![writable(t.clone()), t], Type::Unit),
            Self::Copy | Self::CopyNonoverlapping => {
                (1, vec![readable(t.clone()), writable(t), count], Type::Unit)
            }
            Self::BorrowShared | Self::BorrowUnique => {
                let unique = self == Self::BorrowUnique;
                let t = Type::Generic(1);
                (
                    2,
                    vec![if unique {
                        writable(t.clone())
                    } else {
                        readable(t.clone())
                    }],
                    Type::Reference {
                        mutability: if unique {
                            Mutability::Unique
                        } else {
                            Mutability::Shared
                        },
                        lifetime: Lifetime::Generic(0),
                        referent: Box::new(t),
                    },
                )
            }
        };
        CallableSignature {
            safety: self.safety(),
            generics,
            generic_kinds: if self.constructs_reference() {
                vec![GenericKind::Lifetime, GenericKind::Type]
            } else {
                vec![GenericKind::Type; generics as usize]
            },
            parameters,
            result,
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        }
    }

    pub(crate) fn constructs_reference(self) -> bool {
        matches!(self, Self::BorrowShared | Self::BorrowUnique)
    }

    pub(crate) fn type_generic_indices(self) -> Vec<u32> {
        self.signature()
            .generic_kinds
            .iter()
            .enumerate()
            .filter_map(|(index, kind)| (*kind == GenericKind::Type).then_some(index as u32))
            .collect()
    }

    pub(crate) fn instantiated_signature(self, types: &[Type]) -> Option<CallableSignature> {
        fn substitute(ty: Type, types: &std::collections::BTreeMap<u32, Type>) -> Type {
            match ty {
                Type::Generic(index) => types[&index].clone(),
                Type::RawPointer {
                    mutability,
                    pointee,
                } => Type::RawPointer {
                    mutability,
                    pointee: Box::new(substitute(*pointee, types)),
                },
                Type::Reference {
                    mutability,
                    referent,
                    ..
                } => Type::Reference {
                    mutability,
                    lifetime: Lifetime::Elided,
                    referent: Box::new(substitute(*referent, types)),
                },
                ty => ty,
            }
        }
        let mut signature = self.signature();
        let indices = self.type_generic_indices();
        if indices.len() != types.len() {
            return None;
        }
        let types = indices.into_iter().zip(types.iter().cloned()).collect();
        signature.generics = 0;
        signature.generic_kinds.clear();
        signature.parameters = signature
            .parameters
            .into_iter()
            .map(|ty| substitute(ty, &types))
            .collect();
        signature.result = substitute(signature.result, &types);
        Some(signature)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn memory_contracts_are_closed_exact_and_preserve_unsafe_requirements() {
        let concrete = Type::Scalar(ScalarType::I64);
        for (index, primitive) in MemoryPrimitive::ALL.into_iter().enumerate() {
            assert_eq!(primitive.ordinal() as usize, index);
            let types = vec![concrete.clone(); primitive.type_generic_indices().len()];
            let instance = primitive.instantiated_signature(&types).unwrap();
            assert_eq!(instance.generics, 0);
            assert!(instance.generic_kinds.is_empty());
            assert_eq!(instance.safety, primitive.safety());
            assert_eq!(instance.safety == Safety::Safe, index < 2);
            assert_eq!(instance.effects, EffectRow::empty());
            let mut excessive = types.clone();
            excessive.push(concrete.clone());
            assert!(primitive.instantiated_signature(&excessive).is_none());
        }
        let write = MemoryPrimitive::Write
            .instantiated_signature(&[concrete.clone()])
            .unwrap();
        assert_eq!(write.parameters[1], concrete);
        assert_eq!(write.result, Type::Unit);
        let read = MemoryPrimitive::Read
            .instantiated_signature(&[Type::Unit])
            .unwrap();
        assert_eq!(read.result, Type::Unit);
    }
}
