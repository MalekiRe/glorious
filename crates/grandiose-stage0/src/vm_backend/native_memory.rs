//! Native-layout raw storage for locally compiled unsafe source. These are
//! machine leaves: there is no vector, capacity policy, resident count, or
//! element destructor here. The caller owns initialization and use obligations.

use super::{
    ExecutionBudget, MemoryPrimitive, Safety, VmArtifactError, VmFunction, VmType, VmValue,
    VmNominalCopyDescriptor,
    expect_usize, value_matches_vm_type,
};
use grandiose_runtime::memory::{MemoryError, MemoryLayout, RawAllocation};
use super::native_profile::{AllocationKind, NativeAllocation, NativeMemoryMeasurements};
use std::{cell::{Cell, RefCell}, collections::{BTreeMap, BTreeSet}, ptr, rc::Rc, sync::Arc};

#[derive(Default)]
pub(super) struct NativeMemory {
    allocations: BTreeMap<usize, NativeAllocation>,
    live_bytes: usize,
    pub(super) home_bytes: Rc<Cell<usize>>,
    pub(super) measurements: Option<Rc<NativeMemoryMeasurements>>,
    pub(super) homes: super::native_storage::HomeRegistry,
    pub(super) residents: Rc<super::native_residents::ResidentMetadata>,
    program_descriptors: Option<Arc<[VmNominalCopyDescriptor]>>,
    storage_plans: BTreeMap<super::DefKey, Arc<super::native_storage::NativeFramePlan>>,
    native_return_plans: BTreeMap<super::DefKey, Arc<super::native_storage::NativeFramePlan>>,
    descriptors: BTreeMap<super::DefKey, Arc<[VmNominalCopyDescriptor]>>,
    /// Static-address leaves retain the original bytes, never an Array copy.
    /// Source `'static` values live for this execution's module/data domain;
    /// no public runner returns a reference beyond that domain.
    static_data: BTreeMap<usize, Arc<[u8]>>,
    static_literals: BTreeMap<(super::DefKey, usize), Arc<[u8]>>,
    /// Authority installed by the explicit native runner after exact linking.
    /// It is never obtained from an artifact or an ambient process registry.
    pub(super) imports: Option<Arc<super::native_bridge::BoundNativeImports>>,
    pub(super) callback_depth: u32,
}

pub(super) fn memory_error(error: MemoryError) -> VmArtifactError {
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
    /// Keep a source literal's genuine allocation stable for this execution's
    /// data domain, even after all of its temporary view slots are retired.
    pub(super) fn static_literal(&mut self, function: super::DefKey, pc: usize, bytes: &[u8]) -> StaticBytes {
        let bytes = self.static_literals.entry((function, pc))
            .or_insert_with(|| Arc::from(bytes)).clone();
        self.static_data.entry(bytes.as_ptr().addr()).or_insert_with(|| bytes.clone());
        StaticBytes(StaticBytesBacking::Owned(bytes))
    }
    pub(super) fn profiled() -> Self {
        Self { measurements: Some(Rc::default()), ..Self::default() }
    }

    pub(super) fn live_native_bytes(&self) -> usize { self.live_bytes + self.home_bytes.get() }

    pub(super) fn install_program_layouts(&mut self, program: &super::CandidateVmProgram) {
        if self.program_descriptors.is_some() { return; }
        let mut descriptors = BTreeMap::new();
        for descriptor in program.functions.values().flat_map(|function| &function.nominal_copy_descriptors) {
            descriptors.entry(super::vm_nominal_copy_descriptor_key(descriptor)).or_insert_with(|| descriptor.clone());
        }
        self.program_descriptors = Some(descriptors.into_values().collect::<Vec<_>>().into());
    }

    fn layout_descriptors(&mut self, function: &VmFunction) -> Arc<[VmNominalCopyDescriptor]> {
        self.program_descriptors.clone().unwrap_or_else(|| self.descriptors.entry(function.definition)
            .or_insert_with(|| function.nominal_copy_descriptors.clone().into()).clone())
    }

    pub(super) fn storage_plan(&mut self, function: &VmFunction) -> Arc<super::native_storage::NativeFramePlan> {
        if let Some(plan) = self.storage_plans.get(&function.definition) { return plan.clone(); }
        let descriptors = self.layout_descriptors(function);
        let plan = Arc::new(super::native_storage::NativeFramePlan::with_native_bindings(function, &descriptors, false, self.imports.as_deref()));
        self.storage_plans.insert(function.definition, plan.clone()); plan
    }

    pub(super) fn native_return_plan(&mut self, function: &VmFunction) -> Arc<super::native_storage::NativeFramePlan> {
        if let Some(plan) = self.native_return_plans.get(&function.definition) { return plan.clone(); }
        let descriptors = self.layout_descriptors(function);
        let plan = Arc::new(super::native_storage::NativeFramePlan::with_native_bindings(function, &descriptors, true, self.imports.as_deref()));
        self.native_return_plans.insert(function.definition, plan.clone()); plan
    }

    fn home_reference(&self, pointer: *mut u8, referent: &VmType, unique: bool) -> Result<Option<VmValue>, VmArtifactError> {
        let home = self.homes.borrow().range(..=pointer.addr()).next_back()
            .and_then(|(_, home)| home.upgrade());
        let Some(home) = home else { return Ok(None); };
        let Some(fields) = home.find_path(pointer, referent)? else { return Ok(None); };
        if !home.is_fully_initialized(&fields) { return Err(error("native reference names moved-out source storage")); }
        Ok(Some(VmValue::Reference { target: super::ReferenceTarget::Home(home), fields: fields.into(), unique, referent: referent.clone() }))
    }

    pub(super) unsafe fn raw_reference(&self, pointer: *mut u8, layout: Arc<NativeLayout>, unique: bool)
        -> Result<VmValue, VmArtifactError>
    {
        if pointer.is_null() || pointer.addr() % layout.memory.alignment() != 0 {
            return Err(error("raw reference creation requires a non-null aligned pointer"));
        }
        if let Some(reference) = self.home_reference(pointer, &layout.ty, unique)? { return Ok(reference); }
        Ok(VmValue::Reference { referent: layout.ty.clone(), unique, fields: Arc::from([]),
            target: super::ReferenceTarget::Native(NativeReference::new(pointer, layout)) })
    }
    pub(super) fn allocate(
        &mut self,
        layout: MemoryLayout,
        block_limit: usize,
        total_limit: usize,
    ) -> Result<*mut u8, VmArtifactError> {
        let available = total_limit.saturating_sub(self.live_native_bytes()).min(block_limit);
        let allocation = match RawAllocation::new(layout, available) {
            Ok(allocation) => allocation,
            Err(MemoryError::AllocationFailed { .. }) => return Ok(ptr::null_mut()),
            Err(failure) => return Err(memory_error(failure)),
        };
        let allocation = NativeAllocation::new(allocation, self.measurements.clone(), AllocationKind::Raw);
        let pointer = allocation.as_ptr().as_ptr();
        // Zero-sized allocations own no bytes and can share an aligned
        // dangling address. Source code still owns every logical resident.
        if layout.size() != 0 {
            self.live_bytes += layout.size();
            self.allocations.insert(pointer.addr(), allocation);
        }
        Ok(pointer)
    }

    pub(super) fn deallocate(
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
        self.residents.clear(pointer.addr(), layout.size());
        self.allocations.remove(&pointer.addr());
        Ok(())
    }

    /// # Safety
    /// The source caller has ended all loans and discharged residents that
    /// relocation or truncation would invalidate. No resident drop is implied.
    pub(super) unsafe fn reallocate(
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
            NativeAllocation::new(RawAllocation::new(old, 0).map_err(memory_error)?,
                self.measurements.clone(), AllocationKind::Raw)
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
            .saturating_sub(self.live_native_bytes() - old.size())
            .min(block_limit);
        // SAFETY: forwarded source/embedding obligation; this owner retains
        // the exact allocator identity and allocation provenance.
        let result = unsafe { allocation.resize_raw(size, available) };
        let output = allocation.as_ptr().as_ptr();
        if allocation.layout().size() != 0 {
            self.allocations.insert(output.addr(), allocation);
        }
        match result {
            Ok(()) => {
                self.residents.relocate(pointer.addr(), old.size(), output.addr(), size);
                self.live_bytes = self.live_bytes - old.size() + size;
                Ok(output)
            }
            Err(MemoryError::AllocationFailed { .. }) => Ok(ptr::null_mut()),
            Err(failure) => Err(memory_error(failure)),
        }
    }
}

/// Private interpreter view of immutable data, never the native payload. A
/// native slot is exactly the pointer and extent below, with no Rust handle.
#[derive(Clone, Debug)]
pub(super) struct StaticBytes(StaticBytesBacking);

#[derive(Clone, Debug)]
enum StaticBytesBacking {
    Owned(Arc<[u8]>),
    Native { pointer: *const u8, length: usize },
}

impl StaticBytes {
    /// # Safety
    /// These bytes are immutable, valid and pinned for the execution's entire
    /// data domain. Generated libraries are pinned by the active module/import
    /// owners; an external unsafe binding must provide the same static lifetime.
    unsafe fn native(pointer: *const u8, length: usize) -> Result<Self, VmArtifactError> {
        if pointer.is_null() || length > isize::MAX as usize
            || pointer.addr().checked_add(length).is_none() {
            return Err(error("native static-data view has an invalid pointer or extent"));
        }
        Ok(Self(StaticBytesBacking::Native { pointer, length }))
    }
}

impl std::ops::Deref for StaticBytes {
    type Target = [u8];
    fn deref(&self) -> &[u8] {
        match &self.0 {
            StaticBytesBacking::Owned(bytes) => bytes,
            // SAFETY: only `native` constructs this arm under the data-domain
            // obligation above. No public runner exports this private view.
            StaticBytesBacking::Native { pointer, length } => unsafe { std::slice::from_raw_parts(*pointer, *length) },
        }
    }
}

#[derive(Clone, Debug)]
pub(super) struct NativeField {
    pub(super) offset: usize,
    pub(super) layout: Arc<NativeLayout>,
}

/// Product fields are either explicitly heterogeneous or a compact repeated
/// layout. Iteration is reserved for resident operations; metadata queries use
/// `distinct` so a huge array never expands into tuple-shaped layout metadata.
#[derive(Clone, Debug)]
pub(super) enum NativeFields {
    Explicit(Vec<NativeField>),
    Repeated { element: Arc<NativeLayout>, count: usize, stride: usize },
}

impl NativeFields {
    pub(super) fn len(&self) -> usize {
        match self { Self::Explicit(fields) => fields.len(), Self::Repeated { count, .. } => *count }
    }
    pub(super) fn get(&self, index: usize) -> Option<NativeField> {
        match self {
            Self::Explicit(fields) => fields.get(index).cloned(),
            Self::Repeated { element, count, stride } if index < *count => Some(NativeField {
                layout: element.clone(), offset: stride.checked_mul(index)?,
            }),
            _ => None,
        }
    }
    pub(super) fn iter(&self) -> NativeFieldIter<'_> {
        NativeFieldIter { fields: self, indices: 0..self.len() }
    }
    pub(super) fn distinct(&self) -> impl Iterator<Item = NativeField> + '_ {
        self.iter().take(match self { Self::Repeated { count, .. } => usize::from(*count != 0), _ => self.len() })
    }
}

pub(super) struct NativeFieldIter<'a> {
    fields: &'a NativeFields,
    indices: std::ops::Range<usize>,
}
impl Iterator for NativeFieldIter<'_> {
    type Item = NativeField;
    fn next(&mut self) -> Option<Self::Item> {
        self.indices.next().map(|index| self.fields.get(index).expect("admitted product field"))
    }
    fn size_hint(&self) -> (usize, Option<usize>) { self.indices.size_hint() }
}
impl ExactSizeIterator for NativeFieldIter<'_> {}

impl<'a> IntoIterator for &'a NativeFields {
    type Item = NativeField;
    type IntoIter = NativeFieldIter<'a>;
    fn into_iter(self) -> Self::IntoIter { self.iter() }
}

#[derive(Clone, Debug)]
pub(super) enum NativeShape {
    Scalar,
    /// Verified callee key (32 bytes) and execution-domain environment token
    /// (u64). Ownership leases are metadata, never Rust objects in the payload.
    Callable,
    /// Two words: a genuine immutable byte pointer, then its usize extent.
    /// The static tag and element alignment are frozen in `NativeLayout::ty`.
    StaticData,
    /// A checked reference is one genuine referent pointer in storage. Its
    /// pointee layout is resolved lazily so indirection terminates recursive
    /// layouts; the descriptor table is metadata, never resident bytes.
    Reference {
        referent: VmType,
        unique: bool,
        descriptors: Arc<[VmNominalCopyDescriptor]>,
    },
    Product(NativeFields),
    Enum {
        payload_offset: usize,
        variants: Vec<NativeFields>,
    },
}

#[derive(Clone, Debug)]
pub(super) struct NativeLayout {
    pub(super) ty: VmType,
    pub(super) memory: MemoryLayout,
    pub(super) shape: NativeShape,
}

#[derive(Clone, Copy)]
pub(super) enum ReferenceRead {
    Resident,
    External,
}

impl NativeLayout {
    pub(super) fn has_resident_metadata(&self) -> bool {
        match &self.shape {
            NativeShape::Callable | NativeShape::Reference { .. } => true,
            NativeShape::Product(fields) => fields.distinct().any(|field| field.layout.has_resident_metadata()),
            NativeShape::Enum { variants, .. } => variants.iter().flat_map(NativeFields::distinct).any(|field| field.layout.has_resident_metadata()),
            _ => false,
        }
    }

    pub(super) fn owns_callable(&self) -> bool {
        match &self.shape {
            NativeShape::Callable => true,
            NativeShape::Product(fields) => fields.distinct().any(|field| field.layout.owns_callable()),
            NativeShape::Enum { variants, .. } => variants.iter().flat_map(NativeFields::distinct).any(|field| field.layout.owns_callable()),
            _ => false,
        }
    }

    /// A native reference needs a representable referent, recursively through
    /// aggregate fields. Keep linking and ordinary storage planning in agreement.
    pub(super) fn supports_resident(&self, descriptors: &Arc<[VmNominalCopyDescriptor]>) -> bool {
        fn visit(layout: &NativeLayout, descriptors: &Arc<[VmNominalCopyDescriptor]>, seen: &mut std::collections::BTreeSet<Vec<u8>>, depth: usize) -> bool {
            let mut key = vec![];
            super::codec::encode_type(&layout.ty, &mut key);
            if !seen.insert(key) { return true; }
            if depth >= 96 { return false; }
            match &layout.shape {
                NativeShape::Scalar | NativeShape::StaticData | NativeShape::Callable => true,
                NativeShape::Reference { referent, .. } => native_layout(referent, descriptors, &mut vec![])
                    .is_ok_and(|layout| visit(&layout, descriptors, seen, depth + 1)),
                NativeShape::Product(fields) => fields.distinct().all(|field| visit(&field.layout, descriptors, seen, depth + 1)),
                NativeShape::Enum { variants, .. } => variants.iter().flat_map(NativeFields::distinct).all(|field| visit(&field.layout, descriptors, seen, depth + 1)),
            }
        }
        visit(self, descriptors, &mut std::collections::BTreeSet::new(), 0)
    }
}

/// Out-of-band layout metadata accompanies a real pointer; this never caches
/// a resident or snapshots its contents. Native references are frame-neutral.
#[derive(Clone, Debug)]
pub(super) struct NativeReference {
    pointer: *mut u8,
    layout: Arc<NativeLayout>,
    // Logical paths, not byte ranges: distinct zero-sized fields can have
    // the same address. Reborrows and projections share this initialization
    // state; constructing a fresh reference from raw storage remains an
    // unsafe promise of initialized source storage.
    path: Vec<u32>,
    initialization: ReferenceInitialization,
}

#[derive(Clone, Debug)]
enum ReferenceInitialization {
    Raw(Rc<RefCell<BTreeSet<Vec<u32>>>>),
    Generated {
        flags: *mut u8,
        paths: Arc<[Vec<u32>]>,
        live: Rc<Cell<bool>>,
    },
}

impl super::ReferenceTarget {
    pub(super) fn native_project(&self, fields: &[u32]) -> Result<(*mut u8, Arc<NativeLayout>), VmArtifactError> {
        match self {
            Self::Home(home) => home.project(fields),
            Self::Native(native) => {
                let projected = native.project(fields)?;
                Ok((projected.pointer, projected.layout))
            }
            _ => Err(error("reference has no native backing storage")),
        }
    }

    pub(super) fn native_initialized(&self, fields: &[u32], complete: bool) -> bool {
        match self {
            Self::Home(home) => if complete { home.is_fully_initialized(fields) } else { home.is_initialized(fields) },
            Self::Native(native) => if complete {
                native.project(fields).is_ok_and(|field| field.is_fully_initialized())
            } else { native.is_initialized(fields) },
            _ => false,
        }
    }

    pub(super) fn replace_native_initialization(&self, fields: &[u32], holes: &BTreeSet<Vec<u32>>)
        -> Result<(), VmArtifactError>
    {
        match self {
            Self::Home(home) => home.replace_initialization(fields, holes),
            Self::Native(native) => native.replace_initialization(fields, holes),
            _ => Err(error("reference has no native backing initialization")),
        }
    }
}

impl ReferenceInitialization {
    fn check_live(&self) -> Result<(), VmArtifactError> {
        if let Self::Generated { live, .. } = self && !live.get() {
            return Err(error("generated reference outlived its backing frame"));
        }
        Ok(())
    }

    fn any_hole(&self, selected: impl Fn(&[u32]) -> bool) -> Result<bool, VmArtifactError> {
        self.check_live()?;
        match self {
            Self::Raw(holes) => Ok(holes.borrow().iter().any(|hole| selected(hole))),
            Self::Generated { flags, paths, .. } => {
                for (index, path) in paths.iter().enumerate() {
                    match unsafe { *flags.add(index) } {
                        0 => { if selected(path) { return Ok(true); } }
                        1 => {}
                        _ => return Err(error("invalid generated reference initialization flag")),
                    }
                }
                Ok(false)
            }
        }
    }

    fn replace(&self, path: &[u32], holes: &BTreeSet<Vec<u32>>) -> Result<(), VmArtifactError> {
        match self {
            Self::Raw(state) => {
                let mut state = state.borrow_mut();
                state.retain(|hole| !hole.starts_with(path));
                state.extend(holes.iter().cloned());
            }
            Self::Generated { flags, paths, live } => {
                if !live.get() { return Err(error("generated reference outlived its backing frame")); }
                for (index, candidate) in paths.iter().enumerate().filter(|(_, p)| p.starts_with(path)) {
                    unsafe { *flags.add(index) = u8::from(!holes.iter().any(|hole| candidate.starts_with(hole))); }
                }
            }
        }
        Ok(())
    }
}

impl NativeReference {
    fn new(pointer: *mut u8, layout: Arc<NativeLayout>) -> Self {
        Self { pointer, layout, path: vec![], initialization: ReferenceInitialization::Raw(Rc::default()) }
    }

    /// The generated frame publishes these exact logical paths. The lease is
    /// revoked synchronously before its flag or payload stack storage expires.
    pub(super) unsafe fn generated(pointer: *mut u8, layout: Arc<NativeLayout>, flags: *mut u8,
        paths: Arc<[Vec<u32>]>, live: Rc<Cell<bool>>,
    ) -> Result<Self, VmArtifactError> {
        if flags.is_null() || paths.first().is_none_or(|path| !path.is_empty()) {
            return Err(error("generated reference lacks its backing initialization contract"));
        }
        let initialization = ReferenceInitialization::Generated { flags, paths, live };
        initialization.any_hole(|_| false)?;
        Ok(Self { pointer, layout, path: vec![], initialization })
    }

    pub(super) fn ty(&self) -> &VmType {
        &self.layout.ty
    }

    pub(super) fn pointer(&self) -> *mut u8 { self.pointer }

    pub(super) fn project(&self, path: &[u32]) -> Result<Self, VmArtifactError> {
        self.initialization.check_live()?;
        let mut pointer = self.pointer;
        let mut layout = self.layout.clone();
        let mut logical_path = self.path.clone();
        for &index in path {
            let (offset, fields) = match &layout.shape {
                NativeShape::Product(fields) => (0, fields),
                NativeShape::Enum {
                    payload_offset,
                    variants,
                } => {
                    if self.initialization.any_hole(|hole| logical_path.starts_with(hole))? {
                        return Err(error("native enum projection names a moved-out resident"));
                    }
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
            layout = field.layout.clone();
            logical_path.push(index);
        }
        Ok(Self {
            pointer,
            layout,
            path: logical_path,
            initialization: self.initialization.clone(),
        })
    }

    pub(super) fn is_initialized(&self, path: &[u32]) -> bool {
        let path = self.path.iter().chain(path).copied().collect::<Vec<_>>();
        self.initialization.any_hole(|hole| path.starts_with(hole)).is_ok_and(|absent| !absent)
    }

    pub(super) fn is_fully_initialized(&self) -> bool {
        self.initialization.any_hole(|hole|
            self.path.starts_with(hole) || hole.starts_with(&self.path)).is_ok_and(|absent| !absent)
    }

    pub(super) fn replace_initialization(&self, path: &[u32], holes: &BTreeSet<Vec<u32>>)
        -> Result<(), VmArtifactError>
    {
        let field = self.project(path)?;
        if self.initialization.any_hole(|hole| hole.len() < field.path.len() && field.path.starts_with(hole))? {
            return Err(error("native field cannot initialize an absent parent"));
        }
        let holes = holes.iter().map(|path| field.path.iter().chain(path).copied().collect()).collect();
        self.initialization.replace(&field.path, &holes)
    }

    pub(super) fn read(
        &self,
        path: &[u32],
        budget: &mut ExecutionBudget,
    ) -> Result<VmValue, VmArtifactError> {
        let field = self.project(path)?;
        if !field.is_initialized(&[]) {
            return Ok(VmValue::Uninitialized(field.layout.ty.clone()));
        }
        // Preserve logical holes in a partial aggregate without reading its
        // moved-out bytes. Cleanup can still inspect the remaining fields.
        if !field.is_fully_initialized() {
            let (fields, variant) = match &field.layout.shape {
                NativeShape::Product(fields) => (fields, None),
                NativeShape::Enum { variants, .. } => {
                    let tag = unsafe { field.pointer.cast::<u32>().read() };
                    (variants.get(tag as usize).ok_or_else(|| error("invalid native enum discriminant"))?, Some(tag))
                }
                _ => return Err(error("native scalar has an invalid projected hole")),
            };
            budget.reserve_value("partial native resident fields", fields.len())?;
            let values = (0..fields.len()).map(|index| field.read(&[index as u32], budget))
                .collect::<Result<Vec<_>, _>>()?.into();
            return Ok(match (&field.layout.ty, variant) {
                (VmType::Tuple(_), None) => VmValue::Tuple(values),
                (VmType::FixedArray { .. }, None) => VmValue::Array { values },
                (VmType::Nominal { definition, .. }, None) => VmValue::Record {
                    definition: *definition, fields: values, signature: field.layout.ty.clone(),
                },
                (VmType::Nominal { definition, .. }, Some(variant)) => VmValue::Enum {
                    definition: *definition, variant, fields: values, signature: field.layout.ty.clone(),
                },
                _ => return Err(error("invalid partial native aggregate type")),
            });
        }
        // SAFETY: native reference creation and the source borrow/use contract
        // establish validity. DerefCopy/Move separately retain resident uses.
        unsafe { field.layout.read_with_reference_admission(field.pointer, budget,
            match field.initialization { ReferenceInitialization::Raw(_) => ReferenceRead::External, _ => ReferenceRead::Resident }) }
    }

    pub(super) fn take(&self, path: &[u32], budget: &mut ExecutionBudget) -> Result<VmValue, VmArtifactError> {
        let field = self.project(path)?;
        if !field.is_initialized(&[]) {
            return Err(error("native reference resident was moved out"));
        }
        let value = field.read(&[], budget)?;
        budget.native_memory.residents.clear(field.pointer.addr(), field.layout.memory.size());
        self.initialization.replace(&field.path, &BTreeSet::from([field.path.clone()]))?;
        Ok(value)
    }

    pub(super) fn write(&self, path: &[u32], value: VmValue, budget: &mut ExecutionBudget) -> Result<(), VmArtifactError> {
        let field = self.project(path)?;
        if self.initialization.any_hole(|hole| hole != field.path && field.path.starts_with(hole))? {
            return Err(error("native field cannot initialize an absent parent"));
        }
        // Native byte storage can carry a partially moved aggregate, but the
        // uninitialized children must remain holes rather than fresh owners.
        fn write_partial(layout: &NativeLayout, pointer: *mut u8, value: VmValue,
            path: &mut Vec<u32>, holes: &mut BTreeSet<Vec<u32>>, budget: &mut ExecutionBudget,
        ) -> Result<(), VmArtifactError> {
            let value = match value {
                VmValue::Resident(home) => home.load(&[], budget)?,
                value => value,
            };
            if let VmValue::Uninitialized(ty) = &value {
                if &layout.ty != ty { return Err(error("native hole has a different concrete type")); }
                holes.insert(path.clone());
                return Ok(());
            }
            let (offset, fields, values, tag) = match (&layout.shape, &value) {
                (NativeShape::Product(fields), VmValue::Tuple(values) | VmValue::Array { values } | VmValue::Record { fields: values, .. }) => (0, fields, values, None),
                (NativeShape::Enum { payload_offset, variants }, VmValue::Enum { variant, fields: values, .. }) =>
                    (*payload_offset, variants.get(*variant as usize).ok_or_else(|| error("invalid native enum discriminant"))?, values, Some(*variant)),
                _ => return unsafe { layout.write(pointer, value, budget) },
            };
            if fields.len() != values.len() { return Err(error("native product field count mismatch")); }
            for (index, (field, value)) in fields.iter().zip(values.iter()).enumerate() {
                path.push(index as u32);
                write_partial(&field.layout, unsafe { pointer.add(offset + field.offset) }, value.clone(), path, holes, budget)?;
                path.pop();
            }
            if let Some(tag) = tag { unsafe { pointer.cast::<u32>().write(tag); } }
            Ok(())
        }
        let mut replacement_holes = BTreeSet::new();
        let value = match value { VmValue::Resident(home) => home.load(&[], budget)?, value => value };
        budget.native_memory.residents.clear(field.pointer.addr(), field.layout.memory.size());
        // SAFETY: only checked unique references reach this operation; source
        // drops/moves the old resident before replacing it.
        write_partial(&field.layout, field.pointer, value, &mut field.path.clone(), &mut replacement_holes, budget)?;
        self.initialization.replace(&field.path, &replacement_holes)?;
        Ok(())
    }
}

fn product_layout(
    types: &[VmType],
    descriptors: &Arc<[VmNominalCopyDescriptor]>,
    active: &mut Vec<VmType>,
) -> Result<(MemoryLayout, NativeFields), VmArtifactError> {
    let mut memory = MemoryLayout::of::<()>();
    let mut fields = Vec::with_capacity(types.len());
    for ty in types {
        let layout = native_layout(ty, descriptors, active)?;
        let (next, offset) = memory.extend(layout.memory).map_err(memory_error)?;
        memory = next;
        fields.push(NativeField { offset, layout: Arc::new(layout) });
    }
    Ok((memory.pad_to_alignment(), NativeFields::Explicit(fields)))
}

pub(super) fn native_layout(
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
        VmType::Callable { .. } => {
            return Ok(NativeLayout { ty: ty.clone(),
                memory: MemoryLayout::of::<[u64; 5]>(), shape: NativeShape::Callable });
        }
        VmType::StaticData { element, tag, alignment: 1 }
            if element.as_ref() == &VmType::U8
                && matches!(*tag, crate::STATIC_UTF8_DATA_TAG | crate::STATIC_RAW_U8_DATA_TAG) => {
            return Ok(NativeLayout { ty: ty.clone(),
                memory: MemoryLayout::of::<[*const u8; 2]>(), shape: NativeShape::StaticData });
        }
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
        VmType::FixedArray { element, length } => {
            active.push(ty.clone());
            let element = Arc::new(native_layout(element, descriptors, active)?);
            active.pop();
            let count = usize::try_from(*length).map_err(|_| error("fixed array count exceeds target indexing width"))?;
            let stride = element.memory.pad_to_alignment().size();
            let memory = element.memory.repeat(count).map_err(memory_error)?;
            return Ok(NativeLayout { ty: ty.clone(), memory,
                shape: NativeShape::Product(NativeFields::Repeated { element, count, stride }) });
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
        // Legacy collection and control-capability values do not have a raw
        // resident ABI. Never serialize their interpreter representations.
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
    pub(super) unsafe fn read(
        &self,
        source: *const u8,
        budget: &mut ExecutionBudget,
    ) -> Result<VmValue, VmArtifactError> {
        unsafe { self.read_with_reference_admission(source, budget, ReferenceRead::Resident) }
    }

    /// Only an explicit unsafe raw/native boundary may introduce a reference
    /// origin from external pointer bytes. Ambient unsafe execution is not this
    /// authority; generated slots and ordinary home reads always require leases.
    pub(super) unsafe fn read_with_reference_admission(&self, source: *const u8,
        budget: &mut ExecutionBudget, admission: ReferenceRead,
    ) -> Result<VmValue, VmArtifactError> {
        macro_rules! scalar {
            ($rust:ty, $variant:ident) => {
                Ok(VmValue::$variant(unsafe { source.cast::<$rust>().read() }))
            };
        }
        match &self.shape {
            NativeShape::Callable => unsafe {
                budget.native_memory.residents.read(source, &self.ty)
            },
            NativeShape::StaticData => {
                let pointer = unsafe { source.cast::<*const u8>().read() };
                let length = unsafe { source.add(std::mem::size_of::<usize>()).cast::<usize>().read() };
                let bytes = unsafe { StaticBytes::native(pointer, length)? };
                let VmType::StaticData { tag, alignment, .. } = &self.ty else { unreachable!() };
                Ok(VmValue::StaticData { tag: *tag, alignment: *alignment, bytes, offset: 0, length })
            }
            NativeShape::Reference { referent, unique, descriptors } => {
                if let Some(reference) = unsafe { budget.native_memory.residents.read_reference(source, referent, *unique)? } {
                    return Ok(reference);
                }
                if matches!(admission, ReferenceRead::Resident) {
                    return Err(error("native storage reference has no checked origin"));
                }
                // SAFETY: an initialized reference resident stores a genuine
                // pointer; reading it as a pointer retains its provenance.
                let pointer = unsafe { source.cast::<*mut u8>().read() };
                let layout = native_layout(referent, descriptors, &mut vec![])?;
                if pointer.is_null() || pointer.addr() % layout.memory.alignment() != 0 {
                    return Err(error("native reference resident is null or misaligned"));
                }
                unsafe { budget.native_memory.raw_reference(pointer, Arc::new(layout), *unique) }
            }
            NativeShape::Product(fields) => {
                budget.reserve_value("native resident fields", fields.len())?;
                let values = fields
                    .iter()
                    .map(|field| {
                        // SAFETY: concrete field offset/layout within the caller's resident.
                        unsafe { field.layout.read_with_reference_admission(source.add(field.offset), budget, admission) }
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(match &self.ty {
                    VmType::Tuple(_) => VmValue::Tuple(values.into()),
                    VmType::FixedArray { .. } => VmValue::Array { values: values.into() },
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
                            .read_with_reference_admission(source.add(payload_offset + field.offset), budget, admission)
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
    pub(super) unsafe fn write(&self, destination: *mut u8, value: VmValue, budget: &mut ExecutionBudget) -> Result<(), VmArtifactError> {
        if !value_matches_vm_type(&value, &self.ty) {
            return Err(error("native write value does not match concrete type"));
        }
        if !matches!(&value, VmValue::Resident(_)) {
            budget.native_memory.residents.clear(destination.addr(), self.memory.size());
        }
        match (&self.shape, value) {
            (_, VmValue::Resident(home)) => unsafe { home.write_bytes(destination)?; },
            (NativeShape::Callable, value) => {
                budget.reserve_value("native callable resident lease", 1)?;
                unsafe { budget.native_memory.residents.write(destination, value)?; }
            }
            (NativeShape::StaticData, VmValue::StaticData { bytes, offset, length, .. }) => {
                let end = offset.checked_add(length).ok_or_else(|| error("static byte window overflow"))?;
                if bytes.get(offset..end).is_none() { return Err(error("static byte window exceeds its backing storage")); }
                unsafe {
                    destination.cast::<*const u8>().write(bytes.as_ptr().add(offset));
                    destination.add(std::mem::size_of::<usize>()).cast::<usize>().write(length);
                }
            }
            (NativeShape::Reference { .. }, value @ VmValue::Reference { .. }) => {
                unsafe { budget.native_memory.residents.write_reference(destination, &value, true, true)?; }
            }
            (
                NativeShape::Product(fields),
                VmValue::Tuple(values) | VmValue::Array { values } | VmValue::Record { fields: values, .. },
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
                            .write(destination.add(field.offset), value.clone(), budget)?;
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
                            budget,
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
        VmValue::Resident(home) => pointer(&home.scalar_value()?),
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
    let descriptors = budget.native_memory.layout_descriptors(function);
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
            if let VmValue::Resident(home) = registers[register as usize].take()
                .ok_or(VmArtifactError::UseAfterMove { register })? {
                home.clear(&[]);
            }
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
        // Compare/inspect the address only: do not load a resident, validate
        // an allocation, or expose provenance for reconstructing a pointer.
        PointerEq => VmValue::U32(u32::from(ptr_arg(0)?.addr() == ptr_arg(1)?.addr())),
        PointerAddress => VmValue::Usize(ptr_arg(0)?.addr() as u64),
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
            let carrier = match arg(0)? {
                VmValue::Resident(home) => home.load(&[], budget)?,
                value => value.clone(),
            };
            let VmValue::Reference { target, fields, .. }
                = &carrier else {
                    return Err(error("reference needs native-addressable storage before exposing its pointer"));
                };
            let pointer = match target {
                super::ReferenceTarget::Home(home) => { home.expose_address(); home.project(fields)?.0 },
                super::ReferenceTarget::Native(native) => native.project(fields)?.pointer,
                _ => return Err(error("reference needs native-addressable storage before exposing its pointer")),
            };
            result_pointer(pointer)
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
            if let StaticBytesBacking::Owned(bytes) = bytes.0 {
                budget.native_memory.static_data.entry(bytes.as_ptr().addr()).or_insert(bytes);
            }
            result_pointer(pointer.cast_mut())
        }
        BorrowShared | BorrowUnique => {
            let layout = layout(0)?;
            let pointer = ptr_arg(0)?;
            unsafe { budget.native_memory.raw_reference(pointer, Arc::new(layout), primitive == BorrowUnique)? }
        }
        Read => {
            let (layout, source) = (layout(0)?, ptr_arg(0)?);
            // SAFETY: unsafe source promises an initialized, valid resident and
            // transfers its ownership obligations according to the raw-read contract.
            let value = unsafe { layout.read_with_reference_admission(source, budget, ReferenceRead::External)? };
            budget.native_memory.residents.clear(source.addr(), layout.memory.size());
            value
        }
        Write => {
            let (layout, destination) = (layout(0)?, ptr_arg(0)?);
            let register = arguments[1];
            let value = registers
                .get_mut(register as usize)
                .and_then(Option::take)
                .ok_or(VmArtifactError::UseAfterMove { register })?;
            // SAFETY: source promises writable storage and discharges its previous resident.
            let consumed_home = match &value { VmValue::Resident(home) => Some(home.clone()), _ => None };
            unsafe {
                layout.write(destination, value, budget)?;
            }
            if let Some(home) = consumed_home { home.clear(&[]); }
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
                budget.native_memory.residents.copy(source.addr(), destination.addr(), bytes);
                // SAFETY: source owns the source/destination extent, provenance,
                // and overlap obligations. Bytes may include uninitialized padding.
                unsafe {
                    if primitive == Copy {
                        ptr::copy(source, destination, bytes);
                    } else {
                        ptr::copy_nonoverlapping(source, destination, bytes);
                    }
                }
                if let Some(measurements) = &budget.native_memory.measurements {
                    measurements.copied(AllocationKind::Raw, bytes);
                }
            }
            VmValue::Unit
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn budget() -> ExecutionBudget {
        ExecutionBudget { native_memory: NativeMemory::default(), unsafe_execution: true,
            limits: Default::default(), instructions: 0, allocated_elements: 0 }
    }

    #[test]
    fn generated_reference_views_share_actual_flags_and_expire_before_stack_access() {
        let mut budget = budget();
        let layout = Arc::new(native_layout(&VmType::Tuple(vec![VmType::Unit, VmType::Unit]), &Arc::from([]), &mut vec![]).unwrap());
        let pointer = std::ptr::NonNull::<u8>::dangling().as_ptr();
        let mut flags = [1u8; 3];
        let live = Rc::new(Cell::new(true));
        let reference = unsafe { NativeReference::generated(pointer, layout, flags.as_mut_ptr(),
            Arc::from([vec![], vec![0], vec![1]]), live.clone()).unwrap() };
        let first = reference.project(&[0]).unwrap();
        let second = reference.project(&[1]).unwrap();
        assert_eq!(first.pointer(), second.pointer());
        assert!(matches!(first.take(&[], &mut budget).unwrap(), VmValue::Unit));
        assert_eq!(flags, [1, 0, 1]);
        assert!(!reference.is_fully_initialized());
        assert!(second.is_fully_initialized());
        flags[1] = 1;
        assert!(first.is_fully_initialized(), "a generated store must be visible without a shadow mask refresh");
        first.take(&[], &mut budget).unwrap();
        first.write(&[], VmValue::Unit, &mut budget).unwrap();
        assert_eq!(flags, [1, 1, 1]);
        flags[0] = 0;
        assert_eq!(flags[0], 0);
        assert!(first.write(&[], VmValue::Unit, &mut budget).is_err(), "a child cannot restore an absent parent");
        live.set(false);
        assert!(reference.project(&[]).is_err());
        assert!(reference.read(&[], &mut budget).is_err());
        assert!(second.write(&[], VmValue::Unit, &mut budget).is_err());
    }

    #[test]
    fn static_data_slots_keep_the_original_allocation_and_site_lifetime() {
        #[repr(C)]
        struct Slot { pointer: *const u8, length: usize }
        let ty = VmType::StaticData { element: Box::new(VmType::U8), tag: crate::STATIC_RAW_U8_DATA_TAG, alignment: 1 };
        let layout = native_layout(&ty, &Arc::from([]), &mut vec![]).unwrap();
        assert_eq!((layout.memory.size(), layout.memory.alignment()), (16,8));
        let mut budget = budget();
        let key = super::super::DefKey(super::super::Digest::of_bytes(b"static-site"));
        let bytes = budget.native_memory.static_literal(key, 7, &[20,22]);
        let pointer = bytes.as_ptr();
        let value = VmValue::StaticData { tag: crate::STATIC_RAW_U8_DATA_TAG, alignment: 1, bytes, offset: 1, length: 1 };
        let mut slot = Slot { pointer: ptr::null(), length: 0 };
        unsafe { layout.write((&mut slot as *mut Slot).cast(), value, &mut budget) }.unwrap();
        assert_eq!(slot.pointer, unsafe { pointer.add(1) });
        assert_eq!(slot.length, 1);
        assert_eq!(unsafe { slot.pointer.read() }, 22);
        let view = unsafe { layout.read((&slot as *const Slot).cast(), &mut budget) }.unwrap();
        let VmValue::StaticData { bytes, .. } = view else { panic!() };
        assert_eq!(bytes.as_ptr(), slot.pointer, "native return must not allocate or marshal bytes");
        assert_eq!(&*bytes, &[22]);
        assert_eq!(budget.native_memory.static_literal(key, 7, &[20,22]).as_ptr(), pointer);
        assert!(budget.native_memory.allocations.is_empty(), "static data is not a raw owned allocation");
    }

    #[test]
    fn malformed_static_extents_and_layout_tags_fail_before_access() {
        for (pointer, length) in [
            (ptr::null(),0), (ptr::null(),1),
            (ptr::without_provenance(1),usize::MAX),
            (ptr::without_provenance(usize::MAX),1),
        ] {
            assert!(unsafe { StaticBytes::native(pointer, length) }.is_err());
        }
        for (element, tag, alignment) in [
            (VmType::U16, crate::STATIC_RAW_U8_DATA_TAG, 1),
            (VmType::U8, crate::STATIC_RAW_U8_DATA_TAG, 2),
            (VmType::U8, 7, 1),
        ] {
            let ty = VmType::StaticData { element: Box::new(element), tag, alignment };
            assert!(native_layout(&ty, &Arc::from([]), &mut vec![]).is_err());
        }
    }

    #[test]
    fn fixed_array_layout_is_compact_contiguous_and_checked() {
        let ty = VmType::FixedArray { element: Box::new(VmType::U16), length: 1_000_000_000 };
        let layout = native_layout(&ty, &Arc::from([]), &mut vec![]).unwrap();
        assert_eq!((layout.memory.size(), layout.memory.alignment()), (2_000_000_000, 2));
        let NativeShape::Product(NativeFields::Repeated { count, stride, .. }) = layout.shape else { panic!() };
        assert_eq!((count, stride), (1_000_000_000, 2));
        let overflow = VmType::FixedArray { element: Box::new(VmType::U128), length: u64::MAX };
        assert!(native_layout(&overflow, &Arc::from([]), &mut vec![]).is_err());
        let empty = VmType::FixedArray { element: Box::new(VmType::U128), length: 0 };
        let empty = native_layout(&empty, &Arc::from([]), &mut vec![]).unwrap();
        assert_eq!((empty.memory.size(), empty.memory.alignment()), (0, 16));
    }

    #[test]
    fn fixed_array_zero_sized_residents_keep_distinct_move_holes() {
        let ty = VmType::FixedArray { element: Box::new(VmType::Unit), length: 2 };
        let layout = Arc::new(native_layout(&ty, &Arc::from([]), &mut vec![]).unwrap());
        let allocation = RawAllocation::new(layout.memory, 0).unwrap();
        let native = NativeReference::new(allocation.as_ptr().as_ptr(), layout);
        let left = native.project(&[0]).unwrap();
        let right = native.project(&[1]).unwrap();
        assert_eq!(left.pointer, right.pointer);
        let mut budget = budget();
        assert!(matches!(left.take(&[], &mut budget).unwrap(), VmValue::Unit));
        assert!(left.take(&[], &mut budget).is_err());
        assert!(right.is_initialized(&[]));
        let VmValue::Array { values } = native.read(&[], &mut budget).unwrap() else { panic!() };
        assert!(matches!(values[0], VmValue::Uninitialized(VmType::Unit)));
        assert!(matches!(values[1], VmValue::Unit));
        left.write(&[], VmValue::Unit, &mut budget).unwrap();
        assert!(native.is_fully_initialized());
    }

    #[test]
    fn safe_address_inspection_does_not_read_storage_or_grant_unsafe_authority() {
        let raw = VmType::RawPointer { mutability: crate::PointerMutability::Const, pointee: Box::new(VmType::I64) };
        let function = VmFunction {
            definition: crate::DefKey(crate::Digest::of_bytes(b"address-only-memory")),
            safety: Safety::Safe, unsafe_execution: false, nominal_copy_descriptors: vec![],
            captures: 0, parameters: 2, registers: vec![raw.clone(), raw.clone()], instructions: vec![],
        };
        let mut budget = budget();
        budget.unsafe_execution = false;
        // Deliberately no allocation/provenance exists for these addresses.
        for (left, right) in [(0, 0), (8, 8), (8, 16), (usize::MAX, 0)] {
            let mut registers = [left, right].map(|address| Some(VmValue::RawPointer {
                pointer: ptr::without_provenance_mut(address), signature: raw.clone(),
            }));
            assert!(matches!(execute_memory_intrinsic(MemoryPrimitive::PointerEq,
                &[VmType::I64], &[0, 1], &function, &mut registers, &mut budget).unwrap(),
                VmValue::U32(value) if value == u32::from(left == right)));
            assert!(matches!(execute_memory_intrinsic(MemoryPrimitive::PointerAddress,
                &[VmType::I64], &[0], &function, &mut registers, &mut budget).unwrap(),
                VmValue::Usize(value) if value == left as u64));
            assert!(!budget.unsafe_execution);
            assert!(budget.native_memory.allocations.is_empty());
            assert!(matches!(execute_memory_intrinsic(MemoryPrimitive::Read,
                &[VmType::I64], &[0], &function, &mut registers, &mut budget),
                Err(VmArtifactError::UnsafeExecutionRequiresUnsafeApi)));
        }
    }

    #[test]
    fn native_profile_tracks_raw_resize_failures_zero_sizes_and_release() {
        let mut memory = NativeMemory::profiled();
        let measurements = memory.measurements.clone().unwrap();
        let empty = MemoryLayout::new(0, 8).unwrap();
        let zero = memory.allocate(empty, 64, 64).unwrap();
        memory.deallocate(zero, empty).unwrap();
        assert_eq!(measurements.snapshot(), Default::default());

        let first = MemoryLayout::new(8, 8).unwrap();
        let pointer = memory.allocate(first, 64, 64).unwrap();
        unsafe { pointer.write_bytes(7, 8); }
        let admitted = measurements.snapshot();
        assert_eq!((admitted.raw_live_bytes, admitted.raw_allocations), (8, 1));
        assert!(memory.allocate(MemoryLayout::new(80, 8).unwrap(), 64, 64).is_err());
        assert_eq!(measurements.snapshot(), admitted);

        let pointer = unsafe { memory.reallocate(pointer, first, 24, 64, 64) }.unwrap();
        let grown = measurements.snapshot();
        assert_eq!((grown.raw_live_bytes, grown.raw_peak_bytes, grown.raw_reallocations), (24, 24, 1));
        let layout = MemoryLayout::new(24, 8).unwrap();
        assert!(unsafe { memory.reallocate(pointer, layout, 128, 64, 64) }.is_err());
        assert_eq!(measurements.snapshot(), grown);
        assert_eq!(unsafe { std::slice::from_raw_parts(pointer, 8) }, &[7; 8]);
        let pointer = unsafe { memory.reallocate(pointer, layout, 24, 64, 64) }.unwrap();
        assert_eq!(measurements.snapshot(), grown, "same-size resize does not invoke the allocator");
        let pointer = unsafe { memory.reallocate(pointer, layout, 4, 64, 64) }.unwrap();
        assert_eq!(unsafe { std::slice::from_raw_parts(pointer, 4) }, &[7; 4]);
        let pointer = unsafe { memory.reallocate(pointer, MemoryLayout::new(4, 8).unwrap(), 0, 64, 64) }.unwrap();
        assert_eq!(measurements.snapshot().raw_live_bytes, 0);
        let pointer = unsafe { memory.reallocate(pointer, empty, 16, 64, 64) }.unwrap();
        let final_layout = MemoryLayout::new(16, 8).unwrap();
        let live = measurements.snapshot();
        assert!(memory.deallocate(pointer, first).is_err());
        assert_eq!(measurements.snapshot(), live, "rejected release cannot alter measurements");
        memory.deallocate(pointer, final_layout).unwrap();
        let result = measurements.snapshot();
        assert_eq!((result.raw_live_bytes, result.raw_peak_bytes, result.peak_live_bytes), (0, 24, 24));
        assert_eq!((result.raw_allocations, result.raw_reallocations, result.raw_deallocations), (2, 2, 2));
        assert!(!result.counters_saturated);
    }

    #[test]
    fn native_profile_observes_combined_peaks_between_instruction_ticks() {
        use super::super::native_storage::NativeHome;
        let mut budget = budget();
        budget.native_memory = NativeMemory::profiled();
        let measurements = budget.native_memory.measurements.clone().unwrap();
        let raw_layout = MemoryLayout::new(32, 8).unwrap();
        let raw = budget.native_memory.allocate(raw_layout, 256, 256).unwrap();
        let scalar = Arc::new(native_layout(&VmType::I64, &Arc::from([]), &mut vec![]).unwrap());
        let small = NativeHome::new(scalar, &mut budget).unwrap();
        assert_eq!(measurements.snapshot().peak_live_bytes, 40);
        budget.native_memory.deallocate(raw, raw_layout).unwrap();
        let tuple = Arc::new(native_layout(&VmType::Tuple(vec![VmType::I64; 16]), &Arc::from([]), &mut vec![]).unwrap());
        let large = NativeHome::new(tuple, &mut budget).unwrap();
        drop(large);
        drop(small);
        let result = measurements.snapshot();
        assert_eq!(budget.instructions, 0, "this peak occurs without an instruction tick");
        assert_eq!(result.peak_live_bytes, 136);
        assert_eq!((result.raw_peak_bytes, result.home_peak_bytes), (32, 136));
        assert!(result.peak_live_bytes < result.raw_peak_bytes + result.home_peak_bytes);
        assert_eq!((result.raw_live_bytes, result.home_live_bytes), (0, 0));
        assert_eq!((result.home_allocations, result.home_deallocations), (2, 2));
        assert_eq!(budget.native_memory.live_native_bytes(), 0);
    }

    #[test]
    fn native_projected_holes_are_shared_and_distinguish_zero_sized_fields() {
        let layout = Arc::new(native_layout(&VmType::Tuple(vec![VmType::Unit, VmType::Unit]),
            &Arc::from([]), &mut vec![]).unwrap());
        let allocation = RawAllocation::new(layout.memory, 0).unwrap();
        let native = NativeReference::new(allocation.as_ptr().as_ptr(), layout);
        let alias = native.clone();
        let left = native.project(&[0]).unwrap();
        let right = native.project(&[1]).unwrap();
        assert_eq!(left.pointer, right.pointer);
        let mut budget = budget();
        assert!(matches!(left.take(&[], &mut budget).unwrap(), VmValue::Unit));
        assert!(!alias.is_initialized(&[0]));
        assert!(right.is_initialized(&[]));
        assert!(native.is_initialized(&[]));
        assert!(!native.is_fully_initialized());
        assert!(left.take(&[], &mut budget).is_err());
        let VmValue::Tuple(fields) = native.read(&[], &mut budget).unwrap() else { panic!() };
        assert!(matches!(fields[0], VmValue::Uninitialized(VmType::Unit)));
        assert!(matches!(fields[1], VmValue::Unit));
        left.write(&[], VmValue::Unit, &mut budget).unwrap();
        assert!(alias.is_fully_initialized());
    }

    #[test]
    fn native_partial_moves_preserve_holes_when_stored_and_restored() {
        let layout = Arc::new(native_layout(&VmType::Tuple(vec![
            VmType::Tuple(vec![VmType::I64, VmType::I64]), VmType::I64,
        ]), &Arc::from([]), &mut vec![]).unwrap());
        let first = RawAllocation::new(layout.memory, 24).unwrap();
        let second = RawAllocation::new(layout.memory, 24).unwrap();
        let native = NativeReference::new(first.as_ptr().as_ptr(), layout.clone());
        let destination = NativeReference::new(second.as_ptr().as_ptr(), layout.clone());
        let mut budget = budget();
        native.write(&[], VmValue::Tuple(vec![
            VmValue::Tuple(vec![VmValue::I64(19), VmValue::I64(42)].into()), VmValue::I64(23),
        ].into()), &mut budget).unwrap();
        let field = native.project(&[0, 1]).unwrap();
        assert!(matches!(field.take(&[], &mut budget).unwrap(), VmValue::I64(42)));
        let alias = VmValue::Reference { target: super::super::ReferenceTarget::Native(native.clone()),
            fields: vec![0, 1].into(), unique: true, referent: VmType::I64 };
        assert!(!super::super::referent_is_initialized(&[], &[], &alias).unwrap());
        let snapshot = native.take(&[], &mut budget).unwrap();
        assert!(!native.is_initialized(&[]));
        assert!(field.write(&[], VmValue::I64(0), &mut budget).is_err());
        destination.write(&[], snapshot, &mut budget).unwrap();
        assert!(!destination.is_initialized(&[0, 1]));
        assert!(matches!(destination.read(&[0, 0], &mut budget).unwrap(), VmValue::I64(19)));
        assert!(matches!(destination.read(&[1], &mut budget).unwrap(), VmValue::I64(23)));
        let reference_layout = native_layout(&VmType::Reference { unique: true, referent: Box::new(layout.ty.clone()) },
            &Arc::from([]), &mut vec![]).unwrap();
        let mut pointer_slot = std::mem::MaybeUninit::<*mut u8>::uninit();
        let reference = VmValue::Reference { target: super::super::ReferenceTarget::Native(destination.clone()),
            fields: Arc::from([]), unique: true, referent: layout.ty.clone() };
        // A partially moved resident cannot be exported as a complete native reference.
        assert!(unsafe { reference_layout.write(pointer_slot.as_mut_ptr().cast(), reference, &mut budget) }.is_err());
        destination.write(&[0, 1], VmValue::I64(42), &mut budget).unwrap();
        assert!(destination.is_fully_initialized());
        native.write(&[], destination.take(&[], &mut budget).unwrap(), &mut budget).unwrap();
        assert!(super::super::referent_is_initialized(&[], &[], &alias).unwrap());
        assert!(matches!(field.read(&[], &mut budget).unwrap(), VmValue::I64(42)));
    }

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
            target: super::super::ReferenceTarget::Native(NativeReference::new(
                pointer.cast(), Arc::new(native_layout(&VmType::I64, &descriptors, &mut vec![]).unwrap()),
            )),
            fields: Arc::from([]), unique: true, referent: VmType::I64,
        };
        let mut resident = std::mem::MaybeUninit::<*mut i64>::uninit();
        // SAFETY: one correctly aligned writable reference slot; its referent
        // is the live local above, exclusively accessed through this pointer.
        unsafe {
            layout.write(resident.as_mut_ptr().cast(), reference, &mut budget()).unwrap();
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
