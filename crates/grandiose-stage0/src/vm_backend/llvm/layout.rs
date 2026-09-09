use super::{LlvmError, VmType};
use crate::vm_backend::{
    VmNominalCopyDescriptor,
    native_memory::{NativeFields, NativeLayout, NativeShape, native_layout},
};
use std::sync::Arc;

/// An explicit selected profile, not an inference from a host compiler's
/// private struct layout. Other target profiles fail closed until implemented.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LlvmTarget {
    pub triple: String,
    pub data_layout: String,
    pub pointer_bits: u32,
    pub little_endian: bool,
}

impl LlvmTarget {
    pub fn x86_64_linux() -> Self {
        Self {
            triple: "x86_64-unknown-linux-gnu".into(),
            data_layout: "e-m:e-p:64:64-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128".into(),
            pointer_bits: 64,
            little_endian: true,
        }
    }

    pub fn host() -> Result<Self, LlvmError> {
        let target = Self::x86_64_linux();
        target.validate_host()?;
        Ok(target)
    }

    pub(super) fn validate_host(&self) -> Result<(), LlvmError> {
        if self != &Self::x86_64_linux()
            || !cfg!(all(
                target_arch = "x86_64",
                target_os = "linux",
                target_endian = "little",
                target_pointer_width = "64"
            ))
        {
            return Err(LlvmError::UnsupportedTarget(self.triple.clone()));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NativeTypeLayout {
    pub ty: VmType,
    pub size: u64,
    pub alignment: u32,
    pub shape: NativeTypeShape,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum NativeTypeShape {
    Scalar,
    Reference,
    Product(Vec<(u64, NativeTypeLayout)>),
    FixedArray {
        element: Box<NativeTypeLayout>,
        length: u64,
        stride: u64,
    },
    Enum {
        tag_bits: u32,
        payload_offset: u64,
        variants: Vec<Vec<(u64, NativeTypeLayout)>>,
    },
}

impl NativeTypeLayout {
    pub(super) fn from_native(layout: &NativeLayout) -> Self {
        let fields = |fields: &NativeFields| {
            fields
                .iter()
                .map(|field| (field.offset as u64, Self::from_native(&field.layout)))
                .collect()
        };
        Self {
            ty: layout.ty.clone(),
            size: layout.memory.size() as u64,
            alignment: layout.memory.alignment() as u32,
            shape: match &layout.shape {
                NativeShape::Scalar => NativeTypeShape::Scalar,
                NativeShape::Reference { .. } => NativeTypeShape::Reference,
                NativeShape::Product(NativeFields::Repeated {
                    element,
                    count,
                    stride,
                }) => NativeTypeShape::FixedArray {
                    element: Box::new(Self::from_native(element)),
                    length: *count as u64,
                    stride: *stride as u64,
                },
                NativeShape::Product(product) => NativeTypeShape::Product(fields(product)),
                NativeShape::Enum {
                    payload_offset,
                    variants,
                } => NativeTypeShape::Enum {
                    tag_bits: 32,
                    payload_offset: *payload_offset as u64,
                    variants: variants.iter().map(fields).collect(),
                },
            },
        }
    }

    pub(super) fn identity_bytes(&self, bytes: &mut Vec<u8>) {
        crate::vm_backend::codec::encode_type(&self.ty, bytes);
        bytes.extend_from_slice(&self.size.to_le_bytes());
        bytes.extend_from_slice(&self.alignment.to_le_bytes());
        let fields = |items: &[(u64, NativeTypeLayout)], bytes: &mut Vec<u8>| {
            bytes.extend_from_slice(&(items.len() as u64).to_le_bytes());
            for (offset, layout) in items {
                bytes.extend_from_slice(&offset.to_le_bytes());
                layout.identity_bytes(bytes);
            }
        };
        match &self.shape {
            NativeTypeShape::Scalar => bytes.push(0),
            NativeTypeShape::Reference => bytes.push(1),
            NativeTypeShape::Product(items) => {
                bytes.push(2);
                fields(items, bytes);
            }
            NativeTypeShape::Enum {
                tag_bits,
                payload_offset,
                variants,
            } => {
                bytes.push(3);
                bytes.extend_from_slice(&tag_bits.to_le_bytes());
                bytes.extend_from_slice(&payload_offset.to_le_bytes());
                bytes.extend_from_slice(&(variants.len() as u64).to_le_bytes());
                for items in variants {
                    fields(items, bytes);
                }
            }
            NativeTypeShape::FixedArray {
                element,
                length,
                stride,
            } => {
                bytes.push(4);
                bytes.extend_from_slice(&length.to_le_bytes());
                bytes.extend_from_slice(&stride.to_le_bytes());
                element.identity_bytes(bytes);
            }
        }
    }
}

pub(super) fn type_key(ty: &VmType) -> Vec<u8> {
    let mut bytes = vec![];
    crate::vm_backend::codec::encode_type(ty, &mut bytes);
    bytes
}

pub(super) fn concrete_layout(
    ty: &VmType,
    descriptors: &Arc<[VmNominalCopyDescriptor]>,
) -> Result<Arc<NativeLayout>, LlvmError> {
    let layout = native_layout(ty, descriptors, &mut vec![])?;
    validate_selected_layout(&layout)?;
    Ok(Arc::new(layout))
}

fn validate_selected_layout(layout: &NativeLayout) -> Result<(), LlvmError> {
    let expected = match &layout.ty {
        VmType::Unit => Some((0, 1)),
        VmType::I8 | VmType::U8 | VmType::Bool => Some((1, 1)),
        VmType::I16 | VmType::U16 => Some((2, 2)),
        VmType::I32 | VmType::U32 | VmType::F32 | VmType::Char => Some((4, 4)),
        VmType::I64
        | VmType::U64
        | VmType::Isize
        | VmType::Usize
        | VmType::F64
        | VmType::Reference { .. }
        | VmType::RawPointer { .. } => Some((8, 8)),
        VmType::I128 | VmType::U128 => Some((16, 16)),
        _ => None,
    };
    if let Some((size, alignment)) = expected
        && (layout.memory.size(), layout.memory.alignment()) != (size, alignment)
    {
        return Err(LlvmError::AbiMismatch(
            "VM scalar layout differs from the selected LLVM target profile",
        ));
    }
    match &layout.shape {
        NativeShape::Scalar | NativeShape::Reference { .. } => {}
        NativeShape::Product(fields) => {
            for field in fields.distinct() {
                validate_selected_layout(&field.layout)?;
            }
        }
        NativeShape::Enum { variants, .. } => {
            for fields in variants {
                for field in fields {
                    validate_selected_layout(&field.layout)?;
                }
            }
        }
    }
    Ok(())
}

pub(super) fn scalar_ir(ty: &VmType) -> Option<&'static str> {
    Some(match ty {
        VmType::I8 | VmType::U8 | VmType::Bool => "i8",
        VmType::I16 | VmType::U16 => "i16",
        VmType::I32 | VmType::U32 | VmType::Char => "i32",
        VmType::I64 | VmType::U64 | VmType::Isize | VmType::Usize => "i64",
        VmType::I128 | VmType::U128 => "i128",
        VmType::F32 => "float",
        VmType::F64 => "double",
        VmType::Reference { .. } | VmType::RawPointer { .. } => "ptr",
        _ => return None,
    })
}
