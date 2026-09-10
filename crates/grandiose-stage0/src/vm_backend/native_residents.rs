//! Shared execution-domain resident metadata. Callable bytes contain a definition key
//! and an opaque identity; reference bytes contain a genuine machine pointer.
//! One byte-transport protocol preserves their respective environment leases and
//! backing-storage identities. Byte moves never create source owners.

use super::{DefKey, RuntimeCaptureEnvironment, VmArtifactError, VmType, VmValue};
use std::{cell::{Cell, RefCell}, collections::BTreeMap, rc::Rc, sync::{Arc, Weak, atomic::{AtomicU64, Ordering}}};

pub(super) const BYTES: usize = 40;

fn error(message: &'static str) -> VmArtifactError {
    VmArtifactError::NativeMemory { message }
}

struct Identity {
    callee: DefKey,
    signature: VmType,
    environment: Weak<RuntimeCaptureEnvironment>,
}

#[derive(Clone)]
struct Lease {
    token: u64,
    environment: Arc<RuntimeCaptureEnvironment>,
}

#[derive(Clone, Debug)]
enum ReferenceOrigin {
    Home(Weak<super::native_storage::NativeHome>),
    Native(super::native_memory::NativeReference),
}

#[derive(Clone, Debug)]
struct ReferenceLease {
    pointer: *mut u8,
    origin: ReferenceOrigin,
    fields: Arc<[u32]>,
    unique: bool,
    referent: VmType,
}

#[derive(Clone)]
enum ResidentLease {
    Callable(Lease),
    Reference(ReferenceLease),
}

impl ResidentLease {
    fn bytes(&self) -> usize {
        match self {
            Self::Callable(_) => BYTES,
            Self::Reference(_) => std::mem::size_of::<*mut u8>(),
        }
    }
}

#[derive(Default)]
struct ResidentState {
    identities: BTreeMap<u64, Identity>,
    leases: BTreeMap<usize, ResidentLease>,
}

#[derive(Default)]
pub(super) struct ResidentMetadata { state: RefCell<ResidentState> }

/// Compiler-owned temporary storage has a synchronous lifetime. Revocation
/// neither reads its bytes nor performs source destruction.
pub(super) struct ResidentScope {
    residents: Rc<ResidentMetadata>,
    regions: Vec<(usize, usize)>,
    live: Option<Rc<Cell<bool>>>,
}

impl ResidentScope {
    pub(super) fn track(&mut self, address: usize, bytes: usize) { self.regions.push((address, bytes)); }
    pub(super) fn lifetime(&mut self) -> Rc<Cell<bool>> {
        self.live.get_or_insert_with(|| Rc::new(Cell::new(true))).clone()
    }
}

impl Drop for ResidentScope {
    fn drop(&mut self) {
        if let Some(live) = &self.live { live.set(false); }
        for (address, bytes) in &self.regions { self.residents.clear(*address, *bytes); }
    }
}

impl std::fmt::Debug for ResidentMetadata {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let state = self.state.borrow();
        f.debug_struct("ResidentMetadata").field("identities", &state.identities.len())
            .field("leases", &state.leases.len()).finish()
    }
}

impl ResidentMetadata {
    pub(super) fn scope(self: &Rc<Self>) -> ResidentScope {
        ResidentScope { residents: self.clone(), regions: vec![], live: None }
    }
    fn prune(&self) {
        self.state.borrow_mut().identities.retain(|_, identity| identity.environment.strong_count() != 0);
    }

    pub(super) fn clear(&self, address: usize, bytes: usize) {
        if bytes == 0 { return; }
        let end = address.saturating_add(bytes);
        let removed = {
            let mut state = self.state.borrow_mut();
            let keys = state.leases.iter().filter(|(slot, lease)|
                **slot < end && slot.saturating_add(lease.bytes()) > address)
                .map(|(slot, _)| *slot).collect::<Vec<_>>();
            keys.into_iter().filter_map(|slot| state.leases.remove(&slot)).collect::<Vec<_>>()
        };
        // Releasing the final environment can retire captured native homes,
        // which in turn clear their own leases. Never hold a registry borrow.
        drop(removed);
        self.prune();
    }

    /// Preserve only complete typed residents. Partial byte overwrites
    /// invalidate the destination's lease and cannot synthesize authority.
    pub(super) fn copy(&self, source: usize, destination: usize, bytes: usize) {
        if source == destination || bytes == 0 { return; }
        let end = source.saturating_add(bytes);
        let copied = self.state.borrow().leases.range(source..end)
            .filter(|(slot, lease)| slot.saturating_add(lease.bytes()) <= end)
            .map(|(slot, lease)| (destination + (slot - source), lease.clone()))
            .collect::<Vec<_>>();
        self.clear(destination, bytes);
        self.state.borrow_mut().leases.extend(copied);
    }

    pub(super) fn relocate(&self, source: usize, old_bytes: usize, destination: usize, bytes: usize) {
        let retained = old_bytes.min(bytes);
        let end = source.saturating_add(retained);
        let moved = self.state.borrow().leases.range(source..end)
            .filter(|(slot, lease)| slot.saturating_add(lease.bytes()) <= end)
            .map(|(slot, lease)| (destination + (slot - source), lease.clone()))
            .collect::<Vec<_>>();
        self.clear(source, old_bytes);
        self.clear(destination, bytes);
        self.state.borrow_mut().leases.extend(moved);
    }

    pub(super) fn expose_references(&self, source: usize, bytes: usize) -> Result<(), VmArtifactError> {
        let end = source.saturating_add(bytes);
        for (slot, lease) in self.state.borrow().leases.range(source..end) {
            if slot.saturating_add(lease.bytes()) > end { continue; }
            if let ResidentLease::Reference(ReferenceLease { origin: ReferenceOrigin::Home(home), .. }) = lease {
                home.upgrade().ok_or_else(|| error("stored reference outlived its native home"))?.expose_address();
            }
        }
        Ok(())
    }

    pub(super) unsafe fn write(&self, destination: *mut u8, value: VmValue) -> Result<(), VmArtifactError> {
        let VmValue::Callable { callee, captures, signature } = value else {
            return Err(error("native callable resident requires a source callable environment"));
        };
        if !captures.live.get() { return Err(error("native callable environment has been destroyed")); }
        self.prune();
        let token = self.state.borrow().identities.iter().find_map(|(token, identity)| {
            (identity.callee == callee && identity.signature == signature
                && identity.environment.ptr_eq(&Arc::downgrade(&captures))).then_some(*token)
        });
        let token = match token {
            Some(token) => token,
            None => {
                // Tokens are never reused, including across execution domains.
                static NEXT: AtomicU64 = AtomicU64::new(1);
                let token = NEXT.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| next.checked_add(1))
                    .map_err(|_| error("native callable identity space exhausted"))?;
                self.state.borrow_mut().identities.insert(token, Identity {
                    callee, signature, environment: Arc::downgrade(&captures),
                });
                token
            }
        };
        self.clear(destination.addr(), BYTES);
        unsafe {
            std::ptr::copy_nonoverlapping(callee.0.as_bytes().as_ptr(), destination, 32);
            destination.add(32).cast::<u64>().write(token);
        }
        self.state.borrow_mut().leases.insert(destination.addr(), ResidentLease::Callable(Lease { token, environment: captures }));
        Ok(())
    }

    pub(super) unsafe fn read(&self, source: *const u8, expected: &VmType) -> Result<VmValue, VmArtifactError> {
        let token = unsafe { source.add(32).cast::<u64>().read() };
        let state = self.state.borrow();
        let identity = state.identities.get(&token)
            .ok_or_else(|| error("native callable identity is unknown in this execution domain"))?;
        let lease = state.leases.get(&source.addr())
            .and_then(|lease| match lease { ResidentLease::Callable(lease) => Some(lease), _ => None })
            .filter(|lease| lease.token == token)
            .ok_or_else(|| error("native callable bytes have no resident ownership lease"))?;
        let callee = unsafe { std::slice::from_raw_parts(source, 32) };
        if callee != identity.callee.0.as_bytes()
            || !super::vm_type_matches(&identity.signature, expected)
            || !identity.environment.ptr_eq(&Arc::downgrade(&lease.environment)) {
            return Err(error("native callable identity has a different target or signature"));
        }
        if !lease.environment.live.get() {
            return Err(error("native callable environment has been destroyed"));
        }
        Ok(VmValue::Callable { callee: identity.callee, signature: identity.signature.clone(),
            captures: lease.environment.clone() })
    }

    /// Store the checked handle identity, including a unique restoration loan.
    /// It is not a fresh promise that every referent field is initialized.
    pub(super) unsafe fn write_reference(&self, destination: *mut u8, value: &VmValue,
        expose: bool, require_initialized: bool,
    ) -> Result<(), VmArtifactError> {
        let VmValue::Reference { target, fields, unique, referent } = value else {
            return Err(error("native reference metadata requires a reference"));
        };
        let (pointer, origin) = match target {
            super::ReferenceTarget::Home(home) => {
                let (pointer, layout) = home.project(fields)?;
                if layout.ty != *referent
                    || (require_initialized && !home.is_fully_initialized(fields))
                    || (!unique && !home.is_initialized(fields)) {
                    return Err(error("native storage reference has an invalid checked origin"));
                }
                if expose { home.expose_address(); }
                (pointer, ReferenceOrigin::Home(Arc::downgrade(home)))
            }
            super::ReferenceTarget::Native(native) => {
                let projected = native.project(fields)?;
                if projected.ty() != referent
                    || (require_initialized && !projected.is_fully_initialized())
                    || (!unique && !projected.is_initialized(&[])) {
                    return Err(error("native reference resident has a different or absent referent"));
                }
                (projected.pointer(), ReferenceOrigin::Native(native.clone()))
            }
            _ => return Err(error("native storage reference lacks an addressable origin")),
        };
        self.clear(destination.addr(), std::mem::size_of::<*mut u8>());
        unsafe { destination.cast::<*mut u8>().write(pointer); }
        self.state.borrow_mut().leases.insert(destination.addr(), ResidentLease::Reference(ReferenceLease {
            pointer, origin, fields: fields.clone(), unique: *unique, referent: referent.clone(),
        }));
        Ok(())
    }

    /// A handle's address selects its exact logical projection, not the numeric
    /// referent address (distinct zero-byte fields may share that address).
    pub(super) unsafe fn read_reference(&self, source: *const u8, referent: &VmType, unique: bool)
        -> Result<Option<VmValue>, VmArtifactError>
    {
        let stored = match self.state.borrow().leases.get(&source.addr()) {
            Some(ResidentLease::Reference(reference)) => reference.clone(),
            Some(_) => return Err(error("native reference slot contains different resident metadata")),
            None => return Ok(None),
        };
        if unsafe { source.cast::<*mut u8>().read() } != stored.pointer
            || &stored.referent != referent || (unique && !stored.unique) {
            return Err(error("native reference bytes have a different origin or authority"));
        }
        let target = match stored.origin {
            ReferenceOrigin::Home(home) => {
                let home = home.upgrade().ok_or_else(|| error("stored reference outlived its native home"))?;
                let (pointer, layout) = home.project(&stored.fields)?;
                if pointer != stored.pointer || &layout.ty != referent {
                    return Err(error("stored reference no longer names its checked projection"));
                }
                super::ReferenceTarget::Home(home)
            }
            ReferenceOrigin::Native(native) => {
                let projected = native.project(&stored.fields)?;
                if projected.pointer() != stored.pointer || projected.ty() != referent {
                    return Err(error("stored native reference no longer names its checked projection"));
                }
                super::ReferenceTarget::Native(native)
            }
        };
        Ok(Some(VmValue::Reference { target, fields: stored.fields, unique, referent: stored.referent }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vm_backend::{ExecutionBudget, Safety, native_memory::{NativeMemory, native_layout}, native_storage::NativeHome};

    fn budget() -> ExecutionBudget {
        ExecutionBudget { native_memory: NativeMemory::default(), unsafe_execution: true,
            limits: Default::default(), instructions: 0, allocated_elements: 0 }
    }
    fn signature() -> VmType {
        VmType::Callable { shared_receiver: true, unique_receiver: true, safety: Safety::Safe,
            parameters: vec![], result: Box::new(VmType::I64), effects: Box::default() }
    }
    fn callable(environment: Arc<RuntimeCaptureEnvironment>) -> VmValue {
        VmValue::Callable { callee: DefKey(crate::Digest::of_bytes(b"callable-resident-test")),
            captures: environment, signature: signature() }
    }
    fn environment(value: VmValue) -> Arc<RuntimeCaptureEnvironment> {
        RuntimeCaptureEnvironment::new(vec![value])
    }
    fn captures(value: VmValue) -> Arc<RuntimeCaptureEnvironment> {
        let VmValue::Callable { captures, .. } = value else { panic!("callable expected") };
        captures
    }

    #[test]
    fn reference_byte_transport_preserves_logical_zero_sized_origins_and_revokes_partial_writes() {
        use crate::vm_backend::ReferenceTarget;
        let mut budget = budget();
        budget.unsafe_execution = false;
        let owner_layout = Arc::new(native_layout(&VmType::Tuple(vec![VmType::Unit, VmType::Unit]), &Arc::from([]), &mut vec![]).unwrap());
        let owner = NativeHome::new(owner_layout, &mut budget).unwrap();
        owner.store(&[], &VmValue::Tuple(vec![VmValue::Unit, VmValue::Unit].into()), &mut budget).unwrap();
        let reference_type = VmType::Reference { unique: true, referent: Box::new(VmType::Unit) };
        let layout = native_layout(&reference_type, &Arc::from([]), &mut vec![]).unwrap();
        let mut source = [0usize; 2];
        let mut destination = [0usize; 2];
        for index in 0..2 {
            let value = VmValue::Reference { target: ReferenceTarget::Home(owner.clone()), fields: Arc::from([index as u32]),
                unique: true, referent: VmType::Unit };
            unsafe { layout.write(source.as_mut_ptr().add(index).cast(), value, &mut budget).unwrap(); }
        }
        assert_eq!(source[0], source[1], "equal addresses do not identify a logical zero-byte field");
        budget.native_memory.residents.copy(source.as_ptr().addr(), destination.as_ptr().addr(), 2 * std::mem::size_of::<usize>());
        destination.copy_from_slice(&source);
        budget.native_memory.residents.clear(source.as_ptr().addr(), 2 * std::mem::size_of::<usize>());
        owner.clear(&[0]);
        for index in 0..2 {
            let value = unsafe { layout.read(destination.as_ptr().add(index).cast(), &mut budget).unwrap() };
            let VmValue::Reference { target, fields, .. } = value else { panic!() };
            assert_eq!(fields.as_ref(), &[index as u32]);
            assert_eq!(target.native_initialized(&fields, true), index == 1);
        }
        let byte = native_layout(&VmType::U8, &Arc::from([]), &mut vec![]).unwrap();
        let pointer = destination.as_mut_ptr().cast::<u8>();
        let unchanged = unsafe { *pointer };
        unsafe { byte.write(pointer, VmValue::U8(unchanged), &mut budget).unwrap(); }
        assert!(unsafe { layout.read(pointer, &mut budget) }.is_err(), "matching overwritten bits do not retain a checked loan");
        assert!(unsafe { layout.read(destination.as_ptr().add(1).cast(), &mut budget) }.is_ok());
        owner.retire();
        assert!(unsafe { layout.read(destination.as_ptr().add(1).cast(), &mut budget) }.is_err());
        budget.native_memory.residents.clear(destination.as_ptr().addr(), 2 * std::mem::size_of::<usize>());
    }

    #[test]
    fn scoped_reference_transport_retires_handles_and_cannot_extend_a_backing_frame() {
        use crate::vm_backend::{ReferenceTarget, native_memory::NativeReference};
        let mut budget = budget();
        let target_layout = Arc::new(native_layout(&VmType::I64, &Arc::from([]), &mut vec![]).unwrap());
        let ty = VmType::Reference { unique: false, referent: Box::new(VmType::I64) };
        let layout = native_layout(&ty, &Arc::from([]), &mut vec![]).unwrap();
        let mut payload = 42i64;
        let mut flags = [1u8];
        let mut slots = [0usize; 2];
        let mut scope = budget.native_memory.residents.scope();
        scope.track(slots.as_ptr().addr(), std::mem::size_of::<usize>());
        let native = unsafe { NativeReference::generated((&raw mut payload).cast(), target_layout,
            flags.as_mut_ptr(), Arc::from([vec![]]), scope.lifetime()).unwrap() };
        let value = VmValue::Reference { target: ReferenceTarget::Native(native), fields: Arc::from([]), unique: false, referent: VmType::I64 };
        unsafe { layout.write(slots.as_mut_ptr().cast(), value, &mut budget).unwrap(); }
        budget.native_memory.residents.copy(slots.as_ptr().addr(), unsafe { slots.as_ptr().add(1) }.addr(), std::mem::size_of::<usize>());
        slots[1] = slots[0];
        assert!(unsafe { layout.read(slots.as_ptr().add(1).cast(), &mut budget) }.is_ok());
        drop(scope);
        assert!(unsafe { layout.read(slots.as_ptr().cast(), &mut budget) }.is_err());
        assert!(unsafe { layout.read(slots.as_ptr().add(1).cast(), &mut budget) }.is_err(), "a copied handle cannot extend the frame behind its pointer");
        assert_eq!(payload, 42, "runtime lease retirement does not destroy source storage");
        budget.native_memory.residents.clear(slots.as_ptr().addr(), std::mem::size_of_val(&slots));
        assert!(budget.native_memory.residents.state.borrow().leases.is_empty());
    }

    #[test]
    fn concrete_callable_layout_and_move_keep_the_exact_environment() {
        let mut budget = budget();
        let layout = native_layout(&signature(), &Arc::from([]), &mut vec![]).unwrap();
        assert_eq!((layout.memory.size(), layout.memory.alignment()), (40, 8));
        let environment = environment(VmValue::I64(42));
        let mut slots = [[0u64; 5]; 2];
        let source = slots[0].as_mut_ptr().cast::<u8>();
        let destination = slots[1].as_mut_ptr().cast::<u8>();
        unsafe { layout.write(source, callable(environment.clone()), &mut budget).unwrap(); }
        let value = unsafe { layout.read(source, &mut budget).unwrap() };
        assert!(Arc::ptr_eq(&captures(value), &environment));
        budget.native_memory.residents.copy(source.addr(), destination.addr(), BYTES);
        unsafe { std::ptr::copy_nonoverlapping(source, destination, BYTES); }
        budget.native_memory.residents.clear(source.addr(), BYTES);
        assert!(unsafe { layout.read(source, &mut budget) }.is_err());
        assert!(Arc::ptr_eq(&captures(unsafe { layout.read(destination, &mut budget).unwrap() }), &environment));
        budget.native_memory.residents.clear(destination.addr(), BYTES);
        assert_eq!(Arc::strong_count(&environment), 1);
    }

    #[test]
    fn forged_cross_domain_destroyed_and_overwritten_callable_bytes_fail() {
        let mut budget = budget();
        let layout = native_layout(&signature(), &Arc::from([]), &mut vec![]).unwrap();
        let environment = environment(VmValue::I64(42));
        let mut slot = [0u64; 5];
        let pointer = slot.as_mut_ptr().cast::<u8>();
        unsafe { layout.write(pointer, callable(environment.clone()), &mut budget).unwrap(); }
        let mut other = self::budget();
        assert!(unsafe { layout.read(pointer, &mut other) }.is_err());
        let mut forged = slot;
        assert!(unsafe { layout.read(forged.as_mut_ptr().cast(), &mut budget) }.is_err());
        slot[0] ^= 1;
        assert!(unsafe { layout.read(pointer, &mut budget) }.is_err());
        slot[0] ^= 1;
        slot[4] ^= 1 << 63;
        assert!(unsafe { layout.read(pointer, &mut budget) }.is_err());
        slot[4] ^= 1 << 63;
        let mut different = signature();
        if let VmType::Callable { result, .. } = &mut different { *result = Box::new(VmType::Bool); }
        let different = native_layout(&different, &Arc::from([]), &mut vec![]).unwrap();
        assert!(unsafe { different.read(pointer, &mut budget) }.is_err());
        environment.live.set(false);
        assert!(unsafe { layout.read(pointer, &mut budget) }.is_err());
        environment.live.set(true);
        let scalar = native_layout(&VmType::U64, &Arc::from([]), &mut vec![]).unwrap();
        unsafe { scalar.write(pointer.add(32), VmValue::U64(slot[4]), &mut budget).unwrap(); }
        assert!(unsafe { layout.read(pointer, &mut budget) }.is_err(), "even matching partial raw writes cannot manufacture a lease");
        assert_eq!(Arc::strong_count(&environment), 1);
    }

    #[test]
    fn raw_callable_reads_cannot_upgrade_receiver_authority() {
        let mut budget = budget();
        let mut restricted = signature();
        if let VmType::Callable { shared_receiver, unique_receiver, .. } = &mut restricted {
            *shared_receiver = false;
            *unique_receiver = false;
        }
        let restricted_layout = native_layout(&restricted, &Arc::from([]), &mut vec![]).unwrap();
        let shared_layout = native_layout(&signature(), &Arc::from([]), &mut vec![]).unwrap();
        let mut slot = [0u64; 5];
        let pointer = slot.as_mut_ptr().cast();
        let value = VmValue::Callable {
            callee: DefKey(crate::Digest::of_bytes(b"restricted-callable-resident")),
            captures: environment(VmValue::I64(42)),
            signature: restricted,
        };
        unsafe { restricted_layout.write(pointer, value, &mut budget).unwrap(); }
        assert!(unsafe { restricted_layout.read(pointer, &mut budget) }.is_ok());
        assert!(unsafe { shared_layout.read(pointer, &mut budget) }.is_err(),
            "a raw callable view cannot manufacture shared or unique invocation permission");
        budget.native_memory.residents.clear(pointer.addr(), BYTES);
    }

    #[test]
    fn allocation_resize_and_release_preserve_then_release_capture_leases() {
        let mut budget = budget();
        let layout = native_layout(&signature(), &Arc::from([]), &mut vec![]).unwrap();
        let environment = environment(VmValue::I64(42));
        let pointer = budget.native_memory.allocate(layout.memory, 1024, 1024).unwrap();
        unsafe { layout.write(pointer, callable(environment.clone()), &mut budget).unwrap(); }
        let resized = unsafe { budget.native_memory.reallocate(pointer, layout.memory, 80, 1024, 1024).unwrap() };
        assert!(Arc::ptr_eq(&captures(unsafe { layout.read(resized, &mut budget).unwrap() }), &environment));
        budget.native_memory.deallocate(resized, grandiose_runtime::memory::MemoryLayout::new(80, 8).unwrap()).unwrap();
        assert_eq!(Arc::strong_count(&environment), 1);
        assert!(budget.native_memory.residents.state.borrow().leases.is_empty());
        for _ in 0..256 {
            let environment = self::environment(VmValue::I64(42));
            let weak = Arc::downgrade(&environment);
            let mut slot = [0u64; 5];
            let pointer = slot.as_mut_ptr().cast();
            unsafe { layout.write(pointer, callable(environment), &mut budget).unwrap(); }
            budget.native_memory.residents.clear(pointer.addr(), BYTES);
            assert!(weak.upgrade().is_none(), "popped or overwritten callbacks must be reclaimable");
        }
    }

    #[test]
    fn source_copy_duplicates_captures_but_native_home_moves_do_not() {
        let mut budget = budget();
        let layout = Arc::new(native_layout(&signature(), &Arc::from([]), &mut vec![]).unwrap());
        let environment = environment(VmValue::I64(42));
        let home = NativeHome::new(layout.clone(), &mut budget).unwrap();
        home.store(&[], &callable(environment.clone()), &mut budget).unwrap();
        let copied = crate::vm_backend::copy_owned_value(&VmValue::Resident(home.clone()), &mut budget).unwrap();
        let VmValue::Resident(copied) = copied else { panic!() };
        assert!(!Arc::ptr_eq(&captures(copied.load(&[], &mut budget).unwrap()), &environment));
        let moved = NativeHome::new(layout, &mut budget).unwrap();
        moved.store(&[], &VmValue::Resident(home.clone()), &mut budget).unwrap();
        home.clear(&[]);
        assert!(Arc::ptr_eq(&captures(moved.load(&[], &mut budget).unwrap()), &environment));
        moved.clear(&[]);
        assert_eq!(Arc::strong_count(&environment), 1);
    }

    #[test]
    fn execution_shutdown_has_no_registry_environment_home_cycle() {
        let mut budget = budget();
        let layout = Arc::new(native_layout(&VmType::I64, &Arc::from([]), &mut vec![]).unwrap());
        let home = NativeHome::new(layout, &mut budget).unwrap();
        home.store(&[], &VmValue::I64(42), &mut budget).unwrap();
        let weak_home = Arc::downgrade(&home);
        let environment = environment(VmValue::Resident(home));
        let weak_environment = Arc::downgrade(&environment);
        let layout = native_layout(&signature(), &Arc::from([]), &mut vec![]).unwrap();
        let pointer = budget.native_memory.allocate(layout.memory, 1024, 1024).unwrap();
        unsafe { layout.write(pointer, callable(environment), &mut budget).unwrap(); }
        let registry = std::rc::Rc::downgrade(&budget.native_memory.residents);
        drop(budget);
        assert!(registry.upgrade().is_none());
        assert!(weak_environment.upgrade().is_none());
        assert!(weak_home.upgrade().is_none());
    }

    #[test]
    fn lease_release_can_recursively_retire_a_captured_callable_home() {
        let mut budget = budget();
        let layout = Arc::new(native_layout(&signature(), &Arc::from([]), &mut vec![]).unwrap());
        let inner = environment(VmValue::I64(42));
        let weak_inner = Arc::downgrade(&inner);
        let home = NativeHome::new(layout.clone(), &mut budget).unwrap();
        home.store(&[], &callable(inner), &mut budget).unwrap();
        let weak_home = Arc::downgrade(&home);
        let outer = environment(VmValue::Resident(home));
        let weak_outer = Arc::downgrade(&outer);
        let mut slot = [0u64; 5];
        let pointer = slot.as_mut_ptr().cast();
        unsafe { layout.write(pointer, callable(outer), &mut budget).unwrap(); }
        budget.native_memory.residents.clear(pointer.addr(), BYTES);
        assert!(weak_outer.upgrade().is_none());
        assert!(weak_home.upgrade().is_none());
        assert!(weak_inner.upgrade().is_none());
        assert!(budget.native_memory.residents.state.borrow().identities.is_empty());
    }
}
