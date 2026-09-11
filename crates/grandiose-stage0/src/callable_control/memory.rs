//! Manifest-bound machine memory in the shared ordered control relation.
//! This models possible source-storage changes, not allocation validity,
//! initialization, byte layout, or unsafe permission; those remain separate.
use super::*;
use crate::MemoryPrimitive;

fn target(value: &ControlValue) -> ControlMemoryTarget {
    match &value.shape {
        ControlValueShape::RawPointer { target, .. } => (**target).clone(),
        ControlValueShape::Borrow(value) => value.storage.clone()
            .map(ControlMemoryTarget::Storage).unwrap_or(ControlMemoryTarget::Unknown),
        _ => ControlMemoryTarget::Unknown,
    }
}

/// A byte offset, cast, bulk write or release can reach beyond the typed
/// subfield at the original address. Keep its containing storage owner, not
/// a falsely precise field identity. An unresolved owner stays unresolved.
fn containing(target: ControlMemoryTarget) -> ControlMemoryTarget {
    match target {
        ControlMemoryTarget::Storage(mut storage) => {
            while let ControlStorage::Field { base, .. } = storage { storage = *base; }
            ControlMemoryTarget::Storage(storage)
        }
        target => target,
    }
}

pub(super) fn invoke(frame: &Frame, id: CoreId, owner: DefKey, primitive: MemoryPrimitive,
    generics: Option<&[GenericArgument]>, arguments: &[ControlValue], result_ty: Type,
    mut state: State) -> Vec<State> {
    let Some(generics) = generics else {
        return vec![state.stop(ControlUnknown::Unsupported("open memory primitive ABI"))];
    };
    if !primitive.matches_invocation(generics,
        &arguments.iter().map(|value| value.ty.clone()).collect::<Vec<_>>(), &result_ty) {
        return vec![state.stop(ControlUnknown::InvalidContract(owner))];
    }
    let mutations = primitive.mutated_pointer_arguments().iter().map(|index| {
        let address = target(&arguments[*index]);
        if matches!(primitive, MemoryPrimitive::Read | MemoryPrimitive::Write) { address }
        else { containing(address) }
    }).collect();
    state.events.push(ControlEvent::Memory { site: frame.site(id), primitive, mutations });
    let mut result = unknown(frame, id, result_ty);
    if matches!(result.ty, Type::RawPointer { .. }) {
        let (address, input) = match primitive {
            MemoryPrimitive::Null | MemoryPrimitive::Dangling | MemoryPrimitive::Allocate
            | MemoryPrimitive::StaticUtf8Address | MemoryPrimitive::StaticBytesAddress =>
                (ControlMemoryTarget::External, None),
            MemoryPrimitive::AsRawShared | MemoryPrimitive::AsRawUnique | MemoryPrimitive::AsConst =>
                (target(&arguments[0]), Some(Box::new(arguments[0].clone()))),
            MemoryPrimitive::Offset | MemoryPrimitive::OffsetConst | MemoryPrimitive::Cast
            | MemoryPrimitive::CastConst | MemoryPrimitive::Reallocate =>
                (containing(target(&arguments[0])), Some(Box::new(arguments[0].clone()))),
            // A loaded pointer is not the address of its containing storage.
            // Without a content proof, it may alias any source storage.
            _ => (ControlMemoryTarget::Unknown, None),
        };
        result.shape = ControlValueShape::RawPointer { target: Box::new(address), input };
    }
    state.outcome = ControlOutcome::Return(result);
    // Keep checked faults distinct from normal return and source cleanup.
    // No machine memory operation invokes an algebraic handler or destructor.
    let mut trapped = state.clone();
    trapped.outcome = ControlOutcome::RuntimeTrap;
    vec![state, trapped]
}

pub(super) fn invalidate(value: &mut ControlValue, target: &ControlMemoryTarget, site: &ControlSite,
    interface: &ElaboratedInterface, steps: &mut usize, limit: usize) -> Result<(), ControlUnknown> {
    *steps = steps.saturating_add(1);
    if *steps > limit { return Err(ControlUnknown::Limit); }
    let Some(storage) = value.storage.clone() else { return Ok(()); };
    let (whole, partial) = match target {
        ControlMemoryTarget::Unknown => (true, false),
        ControlMemoryTarget::External => (storage.external_resident(), false),
        ControlMemoryTarget::Storage(destination) if !destination.strong_destination() =>
            (storage.external_resident(), false),
        ControlMemoryTarget::Storage(destination) =>
            (storage.path_from(destination).is_some(), destination.path_from(&storage).is_some()),
    };
    if !whole && !partial { return Ok(()); }
    if whole {
        value.shape = ControlValueShape::Unknown;
    } else {
        open_product(value, interface, steps, limit)?;
        match &mut value.shape {
            ControlValueShape::Tuple(fields) | ControlValueShape::Array(fields)
            | ControlValueShape::Record { fields, .. } | ControlValueShape::Enum { fields, .. } => {
                for field in fields { invalidate(field, target, site, interface, steps, limit)?; }
            }
            _ => return Err(ControlUnknown::Unsupported("unresolved memory mutation product")),
        }
    }
    value.origin = ControlOrigin::Invalidated { site: Box::new(site.clone()), previous: Box::new(value.origin.clone()) };
    Ok(())
}
