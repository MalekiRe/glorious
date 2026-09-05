//! Native-layout raw storage for locally compiled unsafe source. These are
//! machine leaves: there is no vector, capacity policy, resident count, or
//! element destructor here. The caller owns initialization and use obligations.

use super::{
    ExecutionBudget, MemoryPrimitive, Safety, VmArtifactError, VmFunction, VmType, VmValue,
    VmNominalCopyDescriptor,
    expect_usize, value_matches_vm_type,
};
use grandiose_runtime::memory::{MemoryError, MemoryLayout, RawAllocation};
use std::{collections::BTreeMap, ptr, sync::Arc};

#[derive(Default)]
pub(super) struct NativeMemory {
    allocations: BTreeMap<usize, RawAllocation>,
    live_bytes: usize,
    descriptors: BTreeMap<super::DefKey, Arc<[VmNominalCopyDescriptor]>>,
    /// Static-address leaves retain the original bytes, never an Array copy.
    /// Source `'static` values live for this execution's module/data domain;
    /// no public runner returns a reference beyond that domain.
    static_data: BTreeMap<usize, Arc<[u8]>>,
}

fn memory_error(error: MemoryError) -> VmArtifactError {
    VmArtifactError::NativeMemory {
        message: match error {
            MemoryError::InvalidLayout { .. } => "invalid raw allocation layout",
            MemoryError::SizeOverflow => "native layout size overflow",
            MemoryError::LimitExceeded { .. } => "native memory budget exceeded",
            MemoryError::AllocationFailed { .. } => "native allocation failed",
        },
    }
}

fn error(message: &'static str) -> VmArtifactError {
    VmArtifactError::NativeMemory { message }
}

impl NativeMemory {
    fn allocate(
        &mut self,
        layout: MemoryLayout,
        block_limit: usize,
        total_limit: usize,
    ) -> Result<*mut u8, VmArtifactError> {
        let available = total_limit.saturating_sub(self.live_bytes).min(block_limit);
        let allocation = match RawAllocation::new(layout, available) {
            Ok(allocation) => allocation,
            Err(MemoryError::AllocationFailed { .. }) => return Ok(ptr::null_mut()),
            Err(failure) => return Err(memory_error(failure)),
        };
        let pointer = allocation.as_ptr().as_ptr();
        // Zero-sized allocations own no bytes and can share an aligned
        // dangling address. Source code still owns every logical resident.
        if layout.size() != 0 {
            self.live_bytes += layout.size();
            self.allocations.insert(pointer.addr(), allocation);
        }
        Ok(pointer)
    }

    fn deallocate(
        &mut self,
        pointer: *mut u8,
        layout: MemoryLayout,
    ) -> Result<(), VmArtifactError> {
        if layout.size() == 0 {
            if pointer.is_null() || pointer.addr() % layout.alignment() != 0 {
                return Err(error("invalid zero-sized allocation pointer"));
            }
            return Ok(());
        }
        let allocation = self
            .allocations
            .get(&pointer.addr())
            .ok_or_else(|| error("raw release does not name a live allocation in this domain"))?;
        if allocation.layout() != layout {
            return Err(error("raw release layout does not match allocation"));
        }
        self.live_bytes -= layout.size();
        self.allocations.remove(&pointer.addr());
        Ok(())
    }

    /// # Safety
    /// The source caller has ended all loans and discharged residents that
    /// relocation or truncation would invalidate. No resident drop is implied.
    unsafe fn reallocate(
        &mut self,
        pointer: *mut u8,
        old: MemoryLayout,
        size: usize,
        block_limit: usize,
        total_limit: usize,
    ) -> Result<*mut u8, VmArtifactError> {
        let mut allocation = if old.size() == 0 {
            if pointer.is_null() || pointer.addr() % old.alignment() != 0 {
                return Err(error("invalid zero-sized reallocation pointer"));
            }
            RawAllocation::new(old, 0).map_err(memory_error)?
        } else {
            let allocation = self.allocations.get(&pointer.addr()).ok_or_else(|| {
                error("raw resize does not name a live allocation in this domain")
            })?;
            if allocation.layout() != old {
                return Err(error("raw resize layout does not match allocation"));
            }
            self.allocations.remove(&pointer.addr()).unwrap()
        };
        let available = total_limit
            .saturating_sub(self.live_bytes - old.size())
            .min(block_limit);
        // SAFETY: forwarded source/embedding obligation; this owner retains
        // the exact allocator identity and allocation provenance.
        let result = unsafe { allocation.resize(size, available) };
        let output = allocation.as_ptr().as_ptr();
        if allocation.layout().size() != 0 {
            self.allocations.insert(output.addr(), allocation);
        }
        match result {
            Ok(()) => {
                self.live_bytes = self.live_bytes - old.size() + size;
                Ok(output)
            }
            Err(MemoryError::AllocationFailed { .. }) => Ok(ptr::null_mut()),
            Err(failure) => Err(memory_error(failure)),
        }
    }
}

#[derive(Clone, Debug)]
struct NativeField {
    offset: usize,
    layout: NativeLayout,
}

#[derive(Clone, Debug)]
enum NativeShape {
    Scalar,
    /// A checked reference is one genuine referent pointer in storage. Its
    /// pointee layout is resolved lazily so indirection terminates recursive
    /// layouts; the descriptor table is metadata, never resident bytes.
    Reference {
        referent: VmType,
        unique: bool,
        descriptors: Arc<[VmNominalCopyDescriptor]>,
    },
    Product(Vec<NativeField>),
    Enum {
        payload_offset: usize,
        variants: Vec<Vec<NativeField>>,
    },
}

#[derive(Clone, Debug)]
struct NativeLayout {
    ty: VmType,
    memory: MemoryLayout,
    shape: NativeShape,
}

/// Out-of-band layout metadata accompanies a real pointer; this never caches
/// a resident or snapshots its contents. Native references are frame-neutral.
#[derive(Clone, Debug)]
pub(super) struct NativeReference {
    pointer: *mut u8,
    layout: Arc<NativeLayout>,
}

impl NativeReference {
    pub(super) fn ty(&self) -> &VmType {
        &self.layout.ty
    }

    pub(super) fn project(&self, path: &[u32]) -> Result<Self, VmArtifactError> {
        let mut pointer = self.pointer;
        let mut layout = self.layout.as_ref();
        for &index in path {
            let (offset, fields) = match &layout.shape {
                NativeShape::Product(fields) => (0, fields),
                NativeShape::Enum {
                    payload_offset,
                    variants,
                } => {
                    // SAFETY: construction promises a live, initialized resident;
                    // ordinary source loan checks preserve it during projection.
                    let tag = unsafe { pointer.cast::<u32>().read() };
                    (
                        *payload_offset,
                        variants
                            .get(tag as usize)
                            .ok_or_else(|| error("invalid native enum discriminant"))?,
                    )
                }
                _ => {
                    return Err(error(
                        "native reference projection has no structural fields",
                    ));
                }
            };
            let field = fields
                .get(index as usize)
                .ok_or_else(|| error("native reference field is out of range"))?;
            // SAFETY: concrete field layout stays within the referenced resident.
            pointer = unsafe { pointer.add(offset + field.offset) };
            layout = &field.layout;
        }
        Ok(Self {
            pointer,
            layout: if path.is_empty() {
                self.layout.clone()
            } else {
                Arc::new(layout.clone())
            },
        })
    }

    pub(super) fn read(
        &self,
        path: &[u32],
        budget: &mut ExecutionBudget,
    ) -> Result<VmValue, VmArtifactError> {
        let field = self.project(path)?;
        // SAFETY: native reference creation and the source borrow/use contract
        // establish validity. DerefCopy/Move separately retain resident uses.
        unsafe { field.layout.read(field.pointer, budget) }
    }

    pub(super) fn write(&self, path: &[u32], value: VmValue) -> Result<(), VmArtifactError> {
        let field = self.project(path)?;
        // SAFETY: only checked unique references reach this operation; source
        // drops/moves the old resident before replacing it.
        unsafe { field.layout.write(field.pointer, value) }
    }
}

fn product_layout(
    types: &[VmType],
    descriptors: &Arc<[VmNominalCopyDescriptor]>,
    active: &mut Vec<VmType>,
) -> Result<(MemoryLayout, Vec<NativeField>), VmArtifactError> {
    let mut memory = MemoryLayout::of::<()>();
    let mut fields = Vec::with_capacity(types.len());
    for ty in types {
        let layout = native_layout(ty, descriptors, active)?;
        let (next, offset) = memory.extend(layout.memory).map_err(memory_error)?;
        memory = next;
        fields.push(NativeField { offset, layout });
    }
    Ok((memory.pad_to_alignment(), fields))
}

fn native_layout(
    ty: &VmType,
    descriptors: &Arc<[VmNominalCopyDescriptor]>,
    active: &mut Vec<VmType>,
) -> Result<NativeLayout, VmArtifactError> {
    if active.len() >= 96 || active.contains(ty) {
        return Err(error("recursive or excessively nested native value layout"));
    }
    // Existing Stage0 usize/isize are frozen 64-bit values. This first native
    // layout implementation deliberately rejects other host pointer widths.
    if std::mem::size_of::<usize>() != 8 {
        return Err(error(
            "native memory currently requires a 64-bit host target",
        ));
    }
    let memory = match ty {
        VmType::Unit => MemoryLayout::of::<()>(),
        VmType::U8 | VmType::I8 | VmType::Bool => MemoryLayout::of::<u8>(),
        VmType::U16 | VmType::I16 => MemoryLayout::of::<u16>(),
        VmType::U32 | VmType::I32 | VmType::F32 | VmType::Char => MemoryLayout::of::<u32>(),
        VmType::U64 | VmType::I64 | VmType::Usize | VmType::Isize | VmType::F64 => {
            MemoryLayout::of::<u64>()
        }
        VmType::U128 | VmType::I128 => MemoryLayout::of::<u128>(),
        VmType::RawPointer { .. } => MemoryLayout::of::<*mut u8>(),
        VmType::Reference { unique, referent } => {
            return Ok(NativeLayout {
                ty: ty.clone(),
                memory: MemoryLayout::of::<*mut u8>(),
                shape: NativeShape::Reference {
                    referent: (**referent).clone(),
                    unique: *unique,
                    descriptors: descriptors.clone(),
                },
            });
        }
        VmType::Tuple(types) => {
            active.push(ty.clone());
            let (memory, fields) = product_layout(types, descriptors, active)?;
            active.pop();
            return Ok(NativeLayout {
                ty: ty.clone(),
                memory,
                shape: NativeShape::Product(fields),
            });
        }
        VmType::Nominal { definition, arguments } => {
            let descriptor = descriptors.iter().find(|descriptor| {
                descriptor.definition == *definition && descriptor.arguments == *arguments
            }).ok_or_else(|| error("native nominal has no frozen layout descriptor"))?;
            active.push(ty.clone());
            let shape_and_memory = if descriptor.is_enum {
                let mut variants = Vec::with_capacity(descriptor.variants.len());
                let (mut payload_size, mut payload_align) = (0, 1);
                for variant in &descriptor.variants {
                    let (layout, fields) = product_layout(variant, descriptors, active)?;
                    payload_size = payload_size.max(layout.size());
                    payload_align = payload_align.max(layout.alignment());
                    variants.push(fields);
                }
                let payload =
                    MemoryLayout::new(payload_size, payload_align).map_err(memory_error)?;
                let (layout, payload_offset) = MemoryLayout::of::<u32>()
                    .extend(payload)
                    .map_err(memory_error)?;
                (
                    layout.pad_to_alignment(),
                    NativeShape::Enum {
                        payload_offset,
                        variants,
                    },
                )
            } else {
                let [fields] = descriptor.variants.as_slice() else {
                    return Err(error(
                        "record native layout must have exactly one field list",
                    ));
                };
                let (layout, fields) = product_layout(fields, descriptors, active)?;
                (layout, NativeShape::Product(fields))
            };
            active.pop();
            return Ok(NativeLayout {
                ty: ty.clone(),
                memory: shape_and_memory.0,
                shape: shape_and_memory.1,
            });
        }
        // Callable/legacy collection values need the full stable
        // address/call ABI. Never serialize their Rust/VM handles into memory
        // and misrepresent that as a host-compatible Glorious payload.
        _ => return Err(VmArtifactError::UnsupportedNativeLayout { ty: ty.clone() }),
    };
    Ok(NativeLayout {
        ty: ty.clone(),
        memory,
        shape: NativeShape::Scalar,
    })
}

impl NativeLayout {
    /// # Safety
    /// `source` has suitable provenance, alignment, extent and initialized
    /// resident validity for this type. Moving/copying its obligations is the
    /// source caller's responsibility, including for zero-sized residents.
    unsafe fn read(
        &self,
        source: *const u8,
        budget: &mut ExecutionBudget,
    ) -> Result<VmValue, VmArtifactError> {
        macro_rules! scalar {
            ($rust:ty, $variant:ident) => {
                Ok(VmValue::$variant(unsafe { source.cast::<$rust>().read() }))
            };
        }
        match &self.shape {
            NativeShape::Reference { referent, unique, descriptors } => {
                // SAFETY: an initialized reference resident stores a genuine
                // pointer; reading it as a pointer retains its provenance.
                let pointer = unsafe { source.cast::<*mut u8>().read() };
                let layout = native_layout(referent, descriptors, &mut vec![])?;
                if pointer.is_null() || pointer.addr() % layout.memory.alignment() != 0 {
                    return Err(error("native reference resident is null or misaligned"));
                }
                Ok(VmValue::Reference {
                    target: super::ReferenceTarget::Native(NativeReference {
                        pointer, layout: Arc::new(layout),
                    }),
                    fields: Arc::from([]),
                    unique: *unique,
                    referent: referent.clone(),
                })
            }
            NativeShape::Product(fields) => {
                budget.reserve_value("native resident fields", fields.len())?;
                let values = fields
                    .iter()
                    .map(|field| {
                        // SAFETY: concrete field offset/layout within the caller's resident.
                        unsafe { field.layout.read(source.add(field.offset), budget) }
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(match &self.ty {
                    VmType::Tuple(_) => VmValue::Tuple(values.into()),
                    VmType::Nominal { definition, .. } => VmValue::Record {
                        definition: *definition,
                        fields: values.into(),
                        signature: self.ty.clone(),
                    },
                    _ => return Err(error("invalid native product type")),
                })
            }
            NativeShape::Enum {
                payload_offset,
                variants,
            } => {
                // SAFETY: the discriminant is an initialized u32 in this resident.
                let tag = unsafe { source.cast::<u32>().read() };
                let fields = variants
                    .get(tag as usize)
                    .ok_or_else(|| error("invalid native enum discriminant"))?;
                budget.reserve_value("native enum fields", fields.len())?;
                let values = fields
                    .iter()
                    .map(|field| unsafe {
                        field
                            .layout
                            .read(source.add(payload_offset + field.offset), budget)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let VmType::Nominal { definition, .. } = &self.ty else {
                    return Err(error("invalid native enum type"));
                };
                Ok(VmValue::Enum {
                    definition: *definition,
                    variant: tag,
                    fields: values.into(),
                    signature: self.ty.clone(),
                })
            }
            NativeShape::Scalar => match &self.ty {
                VmType::Unit => Ok(VmValue::Unit),
                VmType::U8 => scalar!(u8, U8),
                VmType::I8 => scalar!(i8, I8),
                VmType::U16 => scalar!(u16, U16),
                VmType::I16 => scalar!(i16, I16),
                VmType::U32 => scalar!(u32, U32),
                VmType::I32 => scalar!(i32, I32),
                VmType::U64 => scalar!(u64, U64),
                VmType::I64 => scalar!(i64, I64),
                VmType::U128 => scalar!(u128, U128),
                VmType::I128 => scalar!(i128, I128),
                VmType::Usize => scalar!(u64, Usize),
                VmType::Isize => scalar!(i64, Isize),
                VmType::F32 => scalar!(f32, F32),
                VmType::F64 => scalar!(f64, F64),
                VmType::RawPointer { .. } => Ok(VmValue::RawPointer {
                    pointer: unsafe { source.cast::<*mut u8>().read() },
                    signature: self.ty.clone(),
                }),
                VmType::Bool => match unsafe { source.read() } {
                    0 => Ok(VmValue::Bool(false)),
                    1 => Ok(VmValue::Bool(true)),
                    _ => Err(error("invalid native boolean")),
                },
                VmType::Char => char::from_u32(unsafe { source.cast::<u32>().read() })
                    .map(VmValue::Char)
                    .ok_or_else(|| error("invalid native character")),
                _ => Err(error("invalid native scalar type")),
            },
        }
    }

    /// # Safety
    /// `destination` has the layout's alignment, extent, and writable provenance;
    /// its previous resident obligations have already been discharged. No
    /// overlapping live loan may be invalidated by this typed move.
    unsafe fn write(&self, destination: *mut u8, value: VmValue) -> Result<(), VmArtifactError> {
        if !value_matches_vm_type(&value, &self.ty) {
            return Err(error("native write value does not match concrete type"));
        }
        match (&self.shape, value) {
            (
                NativeShape::Reference { referent, .. },
                VmValue::Reference { target: super::ReferenceTarget::Native(native), fields, .. },
            ) => {
                let native = native.project(&fields)?;
                if native.ty() != referent {
                    return Err(error("native reference resident has a different referent layout"));
                }
                // SAFETY: destination is an aligned reference slot and the
                // checked source reference supplies the actual referent pointer.
                unsafe { destination.cast::<*mut u8>().write(native.pointer); }
            }
            (NativeShape::Reference { .. }, VmValue::Reference { .. }) => {
                return Err(error("frame reference must have native-addressable storage before raw residency"));
            }
            (
                NativeShape::Product(fields),
                VmValue::Tuple(values) | VmValue::Record { fields: values, .. },
            ) => {
                if fields.len() != values.len() {
                    return Err(error("native product field count mismatch"));
                }
                for (field, value) in fields.iter().zip(values.iter()) {
                    // VM containers are private register representations; this
                    // instruction semantically moves each resident into memory.
                    unsafe {
                        field
                            .layout
                            .write(destination.add(field.offset), value.clone())?;
                    }
                }
            }
            (
                NativeShape::Enum {
                    payload_offset,
                    variants,
                },
                VmValue::Enum {
                    variant,
                    fields: values,
                    ..
                },
            ) => {
                let fields = variants
                    .get(variant as usize)
                    .ok_or_else(|| error("native enum variant mismatch"))?;
                if fields.len() != values.len() {
                    return Err(error("native enum field count mismatch"));
                }
                for (field, value) in fields.iter().zip(values.iter()) {
                    unsafe {
                        field.layout.write(
                            destination.add(payload_offset + field.offset),
                            value.clone(),
                        )?;
                    }
                }
                unsafe {
                    destination.cast::<u32>().write(variant);
                }
            }
            (NativeShape::Scalar, value) => {
                macro_rules! write {
                    ($rust:ty, $value:expr) => {
                        unsafe {
                            destination.cast::<$rust>().write($value);
                        }
                    };
                }
                match value {
                    VmValue::Unit => {}
                    VmValue::U8(value) => write!(u8, value),
                    VmValue::I8(value) => write!(i8, value),
                    VmValue::U16(value) => write!(u16, value),
                    VmValue::I16(value) => write!(i16, value),
                    VmValue::U32(value) => write!(u32, value),
                    VmValue::I32(value) => write!(i32, value),
                    VmValue::U64(value) | VmValue::Usize(value) => write!(u64, value),
                    VmValue::I64(value) | VmValue::Isize(value) => write!(i64, value),
                    VmValue::U128(value) => write!(u128, value),
                    VmValue::I128(value) => write!(i128, value),
                    VmValue::F32(value) => write!(f32, value),
                    VmValue::F64(value) => write!(f64, value),
                    VmValue::RawPointer { pointer, .. } => write!(*mut u8, pointer),
                    VmValue::Bool(value) => write!(u8, u8::from(value)),
                    VmValue::Char(value) => write!(u32, u32::from(value)),
                    _ => return Err(error("invalid native scalar value")),
                }
            }
            _ => return Err(error("native value shape mismatch")),
        }
        Ok(())
    }
}

fn pointer(value: &VmValue) -> Result<*mut u8, VmArtifactError> {
    match value {
        VmValue::RawPointer { pointer, .. } => Ok(*pointer),
        _ => Err(error("expected raw pointer operand")),
    }
}

pub(super) fn execute_memory_intrinsic(
    primitive: MemoryPrimitive,
    types: &[VmType],
    arguments: &[u32],
    function: &VmFunction,
    registers: &mut [Option<VmValue>],
    budget: &mut ExecutionBudget,
) -> Result<VmValue, VmArtifactError> {
    if primitive.safety() == Safety::Unsafe && !budget.unsafe_execution {
        return Err(VmArtifactError::UnsafeExecutionRequiresUnsafeApi);
    }
    let arg = |index: usize| {
        let register = *arguments
            .get(index)
            .ok_or_else(|| error("missing raw-memory operand"))?;
        registers
            .get(register as usize)
            .and_then(Option::as_ref)
            .ok_or(VmArtifactError::UseAfterMove { register })
    };
    let count = |index| {
        expect_usize(arg(index)?).and_then(|value| {
            usize::try_from(value).map_err(|_| error("native count does not fit host usize"))
        })
    };
    let ptr_arg = |index| pointer(arg(index)?);
    let block_limit =
        usize::try_from(budget.limits.max_native_allocation_bytes).unwrap_or(usize::MAX);
    let total_limit = usize::try_from(budget.limits.max_native_bytes).unwrap_or(usize::MAX);
    let descriptors = budget.native_memory.descriptors.entry(function.definition)
        .or_insert_with(|| function.nominal_copy_descriptors.clone().into()).clone();
    let layout = |index| native_layout(&types[index], &descriptors, &mut vec![]);
    let (_, signature) = super::memory_intrinsic_signature(primitive, types)?;
    let result_pointer = |pointer| VmValue::RawPointer {
        pointer,
        signature: signature.clone(),
    };
    use MemoryPrimitive::*;
    Ok(match primitive {
        SizeOf => VmValue::Usize(layout(0)?.memory.size() as u64),
        AlignOf => VmValue::Usize(layout(0)?.memory.alignment() as u64),
        Forget => {
            // The unsafe caller has deliberately discharged/transferred the
            // logical obligations. Dropping a VM register is NOT source Drop.
            let register = arguments[0];
            registers[register as usize].take()
                .ok_or(VmArtifactError::UseAfterMove { register })?;
            VmValue::Unit
        }
        StaticBytesLen => {
            let (_, _, length) = super::expect_static_utf8(arg(0)?)?;
            VmValue::Usize(length as u64)
        }
        Null => result_pointer(ptr::null_mut()),
        Dangling => {
            let alignment = layout(0)?.memory.alignment();
            result_pointer(ptr::without_provenance_mut(alignment))
        }
        Allocate => {
            let layout = MemoryLayout::new(count(0)?, count(1)?).map_err(memory_error)?;
            result_pointer(
                budget
                    .native_memory
                    .allocate(layout, block_limit, total_limit)?,
            )
        }
        Deallocate => {
            let (pointer, size, alignment) = (ptr_arg(0)?, count(1)?, count(2)?);
            budget.native_memory.deallocate(
                pointer,
                MemoryLayout::new(size, alignment).map_err(memory_error)?,
            )?;
            VmValue::Unit
        }
        Reallocate => {
            let (pointer, old_size, alignment, size) =
                (ptr_arg(0)?, count(1)?, count(2)?, count(3)?);
            let old = MemoryLayout::new(old_size, alignment).map_err(memory_error)?;
            // SAFETY: unsafe execution is scoped to the embedding call; source
            // invariants are its caller's responsibility, not an artifact flag.
            result_pointer(unsafe {
                budget
                    .native_memory
                    .reallocate(pointer, old, size, block_limit, total_limit)?
            })
        }
        IsNull => VmValue::U32(u32::from(ptr_arg(0)?.is_null())),
        Offset | OffsetConst => {
            let bytes = layout(0)?
                .memory
                .repeat(count(1)?)
                .map_err(memory_error)?
                .size();
            result_pointer(if bytes == 0 {
                ptr_arg(0)?
            } else {
                // SAFETY: source promises that this derivation stays in its allocation.
                unsafe { ptr_arg(0)?.add(bytes) }
            })
        }
        Cast | CastConst | AsConst => result_pointer(ptr_arg(0)?),
        AsRawShared | AsRawUnique => {
            let VmValue::Reference { target: super::ReferenceTarget::Native(native), fields, .. }
                = arg(0)? else {
                    return Err(error("reference needs native-addressable storage before exposing its pointer"));
                };
            result_pointer(native.project(fields)?.pointer)
        }
        StaticUtf8Address | StaticBytesAddress => {
            let (bytes, offset, length) = super::expect_static_utf8(arg(0)?)?;
            let end = offset.checked_add(length).ok_or_else(|| error("static byte window overflow"))?;
            if bytes.get(offset..end).is_none() {
                return Err(error("static byte window exceeds its backing storage"));
            }
            // SAFETY: the checked window is within the retained immutable byte
            // allocation; a zero-length endpoint never dereferences its pointer.
            let pointer = unsafe { bytes.as_ptr().add(offset) };
            budget.native_memory.static_data.entry(bytes.as_ptr().addr()).or_insert(bytes);
            result_pointer(pointer.cast_mut())
        }
        BorrowShared | BorrowUnique => {
            let layout = layout(0)?;
            let pointer = ptr_arg(0)?;
            if pointer.is_null() || pointer.addr() % layout.memory.alignment() != 0 {
                return Err(error(
                    "native reference requires a non-null aligned pointer",
                ));
            }
            VmValue::Reference {
                target: super::ReferenceTarget::Native(NativeReference {
                    pointer,
                    layout: Arc::new(layout.clone()),
                }),
                fields: Arc::from([]),
                unique: primitive == BorrowUnique,
                referent: layout.ty,
            }
        }
        Read => {
            let (layout, source) = (layout(0)?, ptr_arg(0)?);
            // SAFETY: unsafe source promises an initialized, valid resident and
            // transfers its ownership obligations according to the raw-read contract.
            unsafe { layout.read(source, budget)? }
        }
        Write => {
            let (layout, destination) = (layout(0)?, ptr_arg(0)?);
            let register = arguments[1];
            let value = registers
                .get_mut(register as usize)
                .and_then(Option::take)
                .ok_or(VmArtifactError::UseAfterMove { register })?;
            // SAFETY: source promises writable storage and discharges its previous resident.
            unsafe {
                layout.write(destination, value)?;
            }
            VmValue::Unit
        }
        Copy | CopyNonoverlapping => {
            let bytes = layout(0)?
                .memory
                .repeat(count(2)?)
                .map_err(memory_error)?
                .size();
            let (source, destination) = (ptr_arg(0)?, ptr_arg(1)?);
            if bytes != 0 {
                // SAFETY: source owns the source/destination extent, provenance,
                // and overlap obligations. Bytes may include uninitialized padding.
                unsafe {
                    if primitive == Copy {
                        ptr::copy(source, destination, bytes);
                    } else {
                        ptr::copy_nonoverlapping(source, destination, bytes);
                    }
                }
            }
            VmValue::Unit
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn checked_reference_resident_is_one_actual_native_pointer() {
        let descriptors = Arc::from([]);
        let layout = native_layout(&VmType::Reference {
            unique: true, referent: Box::new(VmType::I64),
        }, &descriptors, &mut vec![]).unwrap();
        assert_eq!(layout.memory, MemoryLayout::of::<*mut i64>());
        let mut value = 40i64;
        let pointer = &raw mut value;
        let reference = VmValue::Reference {
            target: super::super::ReferenceTarget::Native(NativeReference {
                pointer: pointer.cast(),
                layout: Arc::new(native_layout(&VmType::I64, &descriptors, &mut vec![]).unwrap()),
            }),
            fields: Arc::from([]), unique: true, referent: VmType::I64,
        };
        let mut resident = std::mem::MaybeUninit::<*mut i64>::uninit();
        // SAFETY: one correctly aligned writable reference slot; its referent
        // is the live local above, exclusively accessed through this pointer.
        unsafe {
            layout.write(resident.as_mut_ptr().cast(), reference).unwrap();
            let stored = resident.assume_init();
            assert_eq!(stored, pointer);
            *stored += 2;
        }
        assert_eq!(value, 42);
    }

    #[test]
    fn rejected_resizes_keep_the_registered_owner_and_initialized_prefix() {
        let mut memory = NativeMemory::default();
        let layout = MemoryLayout::of::<u64>();
        let pointer = memory.allocate(layout, 64, 64).unwrap();
        // SAFETY: one aligned u64 slot, no reference escapes or overlaps resize.
        unsafe {
            pointer.cast::<u64>().write(42);
            assert!(memory.reallocate(pointer, layout, 16, 8, 64).is_err());
            assert!(
                memory
                    .reallocate(pointer, layout, usize::MAX, usize::MAX, usize::MAX)
                    .is_err()
            );
            assert_eq!(pointer.cast::<u64>().read(), 42);
        }
        assert_eq!(memory.live_bytes, 8);
        assert_eq!(memory.allocations.len(), 1);
        memory.deallocate(pointer, layout).unwrap();
        assert_eq!(memory.live_bytes, 0);
        assert!(memory.allocations.is_empty());
    }

    #[test]
    fn resizing_accounts_for_the_old_block_and_other_live_allocations() {
        let mut memory = NativeMemory::default();
        let small = MemoryLayout::new(8, 64).unwrap();
        let first = memory.allocate(small, 64, 24).unwrap();
        let other = memory.allocate(small, 64, 24).unwrap();
        // SAFETY: only initialized bytes are read; the refreshed pointer replaces
        // the original after successful resize, and no references survive it.
        let current = unsafe {
            first.write(42);
            let current = memory.reallocate(first, small, 16, 64, 24).unwrap();
            assert_eq!(current.read(), 42);
            assert_eq!(current.addr() % 64, 0);
            assert!(
                memory
                    .reallocate(current, MemoryLayout::new(16, 64).unwrap(), 24, 64, 24)
                    .is_err()
            );
            assert_eq!(current.read(), 42);
            current
        };
        assert_eq!(memory.live_bytes, 24);
        memory.deallocate(other, small).unwrap();
        memory
            .deallocate(current, MemoryLayout::new(16, 64).unwrap())
            .unwrap();
        assert_eq!(memory.live_bytes, 0);
    }

    #[test]
    fn zero_sized_allocations_share_no_byte_owner_and_resize_explicitly() {
        let mut memory = NativeMemory::default();
        let zero = MemoryLayout::new(0, 64).unwrap();
        let first = memory.allocate(zero, 0, 0).unwrap();
        let second = memory.allocate(zero, 0, 0).unwrap();
        assert_eq!(memory.allocations.len(), 0);
        assert_eq!(memory.live_bytes, 0);
        // SAFETY: these raw blocks contain no initialized residents or loans.
        let current = unsafe { memory.reallocate(first, zero, 64, 64, 64) }.unwrap();
        assert_eq!(memory.live_bytes, 64);
        memory.deallocate(second, zero).unwrap();
        assert_eq!(memory.live_bytes, 64);
        let empty =
            unsafe { memory.reallocate(current, MemoryLayout::new(64, 64).unwrap(), 0, 0, 0) }
                .unwrap();
        memory.deallocate(empty, zero).unwrap();
        assert_eq!(memory.live_bytes, 0);
        assert!(memory.allocations.is_empty());
    }
}
