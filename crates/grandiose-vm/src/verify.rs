use std::{collections::VecDeque, error::Error, fmt, ops::Range, sync::Arc};

use crate::bytecode::{
    Artifact, Constant, DROP_HOOK, EXPORTED, Function, HandlerClause, Instruction, NO_RETURN,
    Primitive, Signature, Type, TypeId, U32, UNIT, construction_field_types, primitive_signature,
    projection_field_type,
};

/// Immutable, verifier-produced indexes used by the interpreter.
///
/// Keeping this separate from [`Artifact`] is intentional: `Artifact` remains
/// the convenient, mutable assembly/decoding format, while execution only
/// consumes ranges that were checked once at the trust boundary.
#[derive(Clone, Debug)]
struct RuntimeLayout {
    functions: Box<[FunctionLayout]>,
    captures: Box<[CapturePlan]>,
}

#[derive(Clone, Debug)]
struct FunctionLayout {
    code: Range<u32>,
    cleanups: Range<u32>,
    captures: Range<u32>,
}

#[derive(Clone, Debug)]
struct CapturePlan {
    pc: u32,
    registers: Box<[u32]>,
}

/// A function-local instruction offset whose bounds were checked against the
/// verified function body.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct VerifiedPc {
    function: u32,
    offset: u32,
}

/// A checked view of one function in a verified artifact.
#[derive(Clone, Copy, Debug)]
pub(crate) struct VerifiedFunction<'a> {
    function: u32,
    descriptor: &'a Function,
    code: &'a [Instruction],
    cleanups: &'a [crate::bytecode::CleanupPlan],
    captures: &'a [CapturePlan],
}

impl<'a> VerifiedFunction<'a> {
    pub(crate) fn descriptor(&self) -> &'a Function {
        self.descriptor
    }

    pub(crate) fn checked_pc(&self, pc: u32) -> Option<VerifiedPc> {
        ((pc as usize) < self.code.len()).then_some(VerifiedPc {
            function: self.function,
            offset: pc,
        })
    }

    pub(crate) fn instruction(&self, pc: VerifiedPc) -> &'a Instruction {
        assert_eq!(
            pc.function, self.function,
            "verified PC used with wrong function"
        );
        &self.code[pc.offset as usize]
    }

    pub(crate) fn cleanup_registers(&self, pc: VerifiedPc) -> &'a [u32] {
        assert_eq!(
            pc.function, self.function,
            "verified PC used with wrong function"
        );
        let at = self
            .cleanups
            .partition_point(|plan| plan.end_instruction <= pc.offset);
        self.cleanups
            .get(at)
            .filter(|plan| plan.first_instruction <= pc.offset)
            .map(|plan| plan.registers.as_slice())
            .expect("verified function PC has cleanup metadata")
    }

    pub(crate) fn continuation_registers(&self, pc: VerifiedPc) -> &'a [u32] {
        assert_eq!(
            pc.function, self.function,
            "verified PC used with wrong function"
        );
        let at = self.captures.partition_point(|plan| plan.pc < pc.offset);
        self.captures
            .get(at)
            .filter(|plan| plan.pc == pc.offset)
            .map_or(&[], |plan| plan.registers.as_ref())
    }
}

#[derive(Clone, Debug)]
pub struct VerifiedArtifact {
    artifact: Arc<Artifact>,
    layout: Arc<RuntimeLayout>,
}

impl VerifiedArtifact {
    pub fn artifact(&self) -> &Artifact {
        &self.artifact
    }
    pub fn into_inner(self) -> Arc<Artifact> {
        self.artifact
    }

    pub(crate) fn function(&self, function: u32) -> Option<VerifiedFunction<'_>> {
        let index = usize::try_from(function).ok()?;
        let descriptor = self.artifact.functions.get(index)?;
        let layout = self.layout.functions.get(index)?;
        Some(VerifiedFunction {
            function,
            descriptor,
            code: &self.artifact.code[layout.code.start as usize..layout.code.end as usize],
            cleanups: &self.artifact.cleanups
                [layout.cleanups.start as usize..layout.cleanups.end as usize],
            captures: &self.layout.captures
                [layout.captures.start as usize..layout.captures.end as usize],
        })
    }
}

impl RuntimeLayout {
    fn from_verified(artifact: &Artifact) -> Self {
        let mut cleanup_start = 0usize;
        let mut captures = Vec::new();
        let functions = artifact
            .functions
            .iter()
            .enumerate()
            .map(|(function_id, function)| {
                let code_start = function.code_start;
                let code_end = code_start + function.code_len;
                let start = cleanup_start as u32;
                let capture_start = captures.len() as u32;
                while cleanup_start < artifact.cleanups.len()
                    && artifact.cleanups[cleanup_start].function as usize == function_id
                {
                    cleanup_start += 1;
                }
                let labels = verify_labels(artifact, function_id as u32, function)
                    .expect("verified function labels remain valid");
                for (pc, live) in continuation_live_registers(artifact, function, &labels)
                    .expect("verified function CFG remains valid")
                    .into_iter()
                    .enumerate()
                {
                    if is_continuation_boundary_pc(artifact, function, pc as u32) {
                        captures.push(CapturePlan {
                            pc: pc as u32,
                            registers: live
                                .into_iter()
                                .enumerate()
                                .filter_map(|(register, live)| live.then_some(register as u32))
                                .collect::<Vec<_>>()
                                .into_boxed_slice(),
                        });
                    }
                }
                FunctionLayout {
                    code: code_start..code_end,
                    cleanups: start..cleanup_start as u32,
                    captures: capture_start..captures.len() as u32,
                }
            })
            .collect::<Vec<_>>()
            .into_boxed_slice();
        debug_assert_eq!(cleanup_start, artifact.cleanups.len());
        Self {
            functions,
            captures: captures.into_boxed_slice(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifyError {
    InvalidFeatures(u64),
    InvalidType(TypeId),
    CyclicOwnedType(TypeId),
    InvalidFunction(u32),
    InvalidConstant(u32),
    InvalidRegister {
        function: u32,
        instruction: u32,
        register: u32,
    },
    InvalidTarget {
        function: u32,
        instruction: u32,
        target: u32,
    },
    TypeMismatch {
        function: u32,
        instruction: u32,
        expected: TypeId,
        actual: TypeId,
    },
    UseOfEmpty {
        function: u32,
        instruction: u32,
        register: u32,
    },
    Overwrite {
        function: u32,
        instruction: u32,
        register: u32,
    },
    IllegalCopy {
        function: u32,
        instruction: u32,
        ty: TypeId,
    },
    InvalidAggregate {
        function: u32,
        instruction: u32,
    },
    InvalidPrimitive {
        function: u32,
        instruction: u32,
    },
    StateMismatch {
        function: u32,
        instruction: u32,
    },
    LiveValueAtExit {
        function: u32,
        instruction: u32,
        register: u32,
    },
    Fallthrough {
        function: u32,
    },
    BorrowConflict {
        function: u32,
        instruction: u32,
        register: u32,
    },
}

impl fmt::Display for VerifyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use VerifyError::*;
        match self {
            InvalidFeatures(features) => write!(f, "invalid required feature bits {features:#x}"),
            InvalidType(x) => write!(f, "invalid type index {x}"),
            CyclicOwnedType(x) => write!(f, "owned type {x} is cyclic"),
            InvalidFunction(x) => write!(f, "invalid function {x}"),
            InvalidConstant(x) => write!(f, "invalid constant {x}"),
            InvalidRegister {
                function,
                instruction,
                register,
            } => write!(
                f,
                "function {function}, instruction {instruction}: invalid register r{register}"
            ),
            InvalidTarget {
                function,
                instruction,
                target,
            } => write!(
                f,
                "function {function}, instruction {instruction}: invalid branch target {target}"
            ),
            TypeMismatch {
                function,
                instruction,
                expected,
                actual,
            } => write!(
                f,
                "function {function}, instruction {instruction}: expected type {expected}, got {actual}"
            ),
            UseOfEmpty {
                function,
                instruction,
                register,
            } => write!(
                f,
                "function {function}, instruction {instruction}: use of empty r{register}"
            ),
            Overwrite {
                function,
                instruction,
                register,
            } => write!(
                f,
                "function {function}, instruction {instruction}: overwrite of live r{register}"
            ),
            IllegalCopy {
                function,
                instruction,
                ty,
            } => write!(
                f,
                "function {function}, instruction {instruction}: type {ty} is not copyable"
            ),
            InvalidAggregate {
                function,
                instruction,
            } => write!(
                f,
                "function {function}, instruction {instruction}: invalid aggregate operation"
            ),
            InvalidPrimitive {
                function,
                instruction,
            } => write!(
                f,
                "function {function}, instruction {instruction}: invalid primitive operation"
            ),
            StateMismatch {
                function,
                instruction,
            } => write!(
                f,
                "function {function}, instruction {instruction}: move states disagree at CFG join"
            ),
            LiveValueAtExit {
                function,
                instruction,
                register,
            } => write!(
                f,
                "function {function}, instruction {instruction}: r{register} remains live at exit"
            ),
            Fallthrough { function } => write!(f, "function {function} can fall off the end"),
            BorrowConflict {
                function,
                instruction,
                register,
            } => write!(
                f,
                "function {function}, instruction {instruction}: incompatible access to borrowed r{register}"
            ),
        }
    }
}
impl Error for VerifyError {}

pub fn verify(mut artifact: Artifact) -> Result<VerifiedArtifact, VerifyError> {
    verify_artifact(&artifact, true, false)?;
    // The decoded/assembled form is deliberately mutable and often has spare
    // construction capacity. Verification is the freeze boundary: compact the
    // large top-level instruction and descriptor arrays before sharing them.
    artifact.types.shrink_to_fit();
    artifact.constants.shrink_to_fit();
    artifact.imports.shrink_to_fit();
    artifact.protocols.shrink_to_fit();
    artifact.handler_defs.shrink_to_fit();
    artifact.cleanups.shrink_to_fit();
    artifact.exports.shrink_to_fit();
    artifact.drop_glue.shrink_to_fit();
    artifact.functions.shrink_to_fit();
    artifact.code.shrink_to_fit();
    let layout = Arc::new(RuntimeLayout::from_verified(&artifact));
    Ok(VerifiedArtifact {
        artifact: Arc::new(artifact),
        layout,
    })
}

/// Populate canonical per-PC cleanup metadata for a freshly assembled
/// in-memory artifact. This deliberately does not support `LEAVE`: nonlocal
/// cleanup boundaries must be emitted explicitly by the compiler.
pub fn with_generated_cleanup_plans(mut artifact: Artifact) -> Result<Artifact, VerifyError> {
    artifact.cleanups.clear();
    artifact.cleanups = verify_artifact(&artifact, false, false)?;
    verify_artifact(&artifact, true, false)?;
    Ok(artifact)
}

/// Complete cleanup metadata for compiler-emitted nonlocal label control.
///
/// Unlike [`with_generated_cleanup_plans`], the input must already contain
/// exact one-instruction cleanup anchors for every `Leave` source and its
/// `LabelPush` destination. Those anchors come from the compiler's MIR
/// ownership analysis; the bytecode oracle consumes them to validate each
/// nonlocal cleanup suffix while deriving the remaining edge-transfer and
/// synthetic-block PCs. A final ordinary verification pass then requires the
/// completed table to be exact everywhere.
pub fn with_compiler_seeded_cleanup_plans(mut artifact: Artifact) -> Result<Artifact, VerifyError> {
    if artifact.cleanups.is_empty()
        || artifact
            .code
            .iter()
            .all(|instruction| !matches!(instruction, Instruction::Leave { .. }))
    {
        return Err(VerifyError::InvalidFunction(u32::MAX));
    }
    artifact.cleanups = verify_artifact(&artifact, false, true)?;
    verify_artifact(&artifact, true, false)?;
    Ok(artifact)
}

fn verify_artifact(
    artifact: &Artifact,
    require_cleanup_metadata: bool,
    allow_seeded_leave_generation: bool,
) -> Result<Vec<crate::bytecode::CleanupPlan>, VerifyError> {
    let used_features = crate::bytecode::used_features(
        &artifact.types,
        &artifact.code,
        !artifact.protocols.is_empty(),
        !artifact.imports.is_empty(),
    );
    if artifact.required_features & !Artifact::SUPPORTED_FEATURES != 0
        || artifact.required_features | 1 != used_features
    {
        return Err(VerifyError::InvalidFeatures(artifact.required_features));
    }
    if let Some(entry) = artifact.entry_function {
        let f = artifact
            .functions
            .get(entry as usize)
            .ok_or(VerifyError::InvalidFunction(entry))?;
        if !f.params.is_empty()
            || f.return_type != crate::bytecode::UNIT
            || f.receiver_mode.is_some()
            || !f.outward_protocols.is_empty()
        {
            return Err(VerifyError::InvalidFunction(entry));
        }
    }
    verify_types(artifact)?;
    verify_function_metadata(artifact)?;
    if require_cleanup_metadata {
        verify_cleanup_tables(artifact)?;
    } else if !allow_seeded_leave_generation
        && artifact
            .code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::Leave { .. }))
    {
        return Err(VerifyError::InvalidFunction(u32::MAX));
    }
    let mut cleanups = Vec::new();
    for (i, f) in artifact.functions.iter().enumerate() {
        cleanups.extend(verify_function(
            artifact,
            i as u32,
            f,
            require_cleanup_metadata,
            allow_seeded_leave_generation,
        )?);
    }
    verify_handler_parameter_quantity_dispositions(artifact)?;
    Ok(cleanups)
}

fn verify_function_metadata(a: &Artifact) -> Result<(), VerifyError> {
    let valid_flags = EXPORTED | DROP_HOOK | NO_RETURN;
    for (id, function) in a.functions.iter().enumerate() {
        let id = id as u32;
        if function.flags & !valid_flags != 0 {
            return Err(VerifyError::InvalidFunction(id));
        }
        let exported = a.exports.iter().any(|export| export.function == id);
        if (function.flags & EXPORTED != 0) != exported {
            return Err(VerifyError::InvalidFunction(id));
        }
        let is_drop_hook = a.drop_glue.iter().any(|glue| glue.function == id);
        if (function.flags & DROP_HOOK != 0) != is_drop_hook {
            return Err(VerifyError::InvalidFunction(id));
        }
        if function.flags & NO_RETURN != 0
            && function_code(a, function)?
                .iter()
                .any(|instruction| matches!(instruction, Instruction::Return { .. }))
        {
            return Err(VerifyError::InvalidFunction(id));
        }
    }

    let mut previous_type = None;
    for glue in &a.drop_glue {
        if previous_type.is_some_and(|previous| previous >= glue.ty)
            || glue.ty as usize >= a.types.len()
            || a.types[glue.ty as usize].is_predefined()
        {
            return Err(VerifyError::InvalidType(glue.ty));
        }
        previous_type = Some(glue.ty);
        let hook = a
            .functions
            .get(glue.function as usize)
            .ok_or(VerifyError::InvalidFunction(glue.function))?;
        if hook.receiver_mode.is_some()
            || hook.params.len() != 1
            || hook.return_type != UNIT
            || !hook.outward_protocols.is_empty()
            || !matches!(type_at(a, hook.params[0])?, Type::RefUnique { referent } if *referent == glue.ty)
        {
            return Err(VerifyError::InvalidFunction(glue.function));
        }
        verify_drop_hook_reachable(a, glue.function, &mut std::collections::BTreeSet::new())?;
        verify_drop_hook_move_restrictions(a, glue.function)?;
    }

    for (caller_id, caller) in a.functions.iter().enumerate() {
        for instruction in function_code(a, caller)? {
            let target = match instruction {
                Instruction::Call { function, .. } | Instruction::TailCall { function, .. } => {
                    Some(*function)
                }
                _ => None,
            };
            if target.is_some_and(|target| {
                a.functions
                    .get(target as usize)
                    .is_some_and(|function| function.flags & DROP_HOOK != 0)
            }) {
                return Err(VerifyError::InvalidFunction(caller_id as u32));
            }
        }
    }
    Ok(())
}

fn verify_drop_hook_move_restrictions(a: &Artifact, hook: u32) -> Result<(), VerifyError> {
    let mut pending = vec![(hook, std::collections::BTreeSet::from([1u32]))];
    let mut seen = std::collections::BTreeMap::<u32, std::collections::BTreeSet<u32>>::new();
    while let Some((function_id, incoming)) = pending.pop() {
        let known = seen.entry(function_id).or_default();
        let old_len = known.len();
        known.extend(incoming);
        if known.len() == old_len {
            continue;
        }
        let mut tainted = known.clone();
        let function = &a.functions[function_id as usize];
        // This is deliberately a fixed point over register provenance rather
        // than a linear-path check: joins may only increase the set of places
        // derived from the hook's unique self reference.
        loop {
            let before = tainted.len();
            for instruction in function_code(a, function)? {
                match instruction {
                    Instruction::Move { dst, src }
                    | Instruction::Copy { dst, src }
                    | Instruction::ReborrowShared { dst, src }
                    | Instruction::ReborrowUnique { dst, src }
                    | Instruction::ProjectBorrowShared { dst, src, .. }
                    | Instruction::ProjectBorrowUnique { dst, src, .. }
                        if tainted.contains(src) =>
                    {
                        tainted.insert(*dst);
                    }
                    Instruction::ProjectMove { src, .. } if tainted.contains(src) => {
                        return Err(VerifyError::InvalidFunction(function_id));
                    }
                    Instruction::Primitive { op, args, .. }
                        if matches!(op, Primitive::ArrayGetMove | Primitive::ArrayPopMove)
                            && args
                                .first()
                                .is_some_and(|register| tainted.contains(register)) =>
                    {
                        return Err(VerifyError::InvalidFunction(function_id));
                    }
                    _ => {}
                }
            }
            if tainted.len() == before {
                break;
            }
        }
        for instruction in function_code(a, function)? {
            if let Instruction::Call {
                function: callee,
                args,
                ..
            }
            | Instruction::TailCall {
                function: callee,
                args,
            } = instruction
            {
                let incoming = args
                    .iter()
                    .enumerate()
                    .filter_map(|(index, register)| {
                        tainted.contains(register).then_some(index as u32 + 1)
                    })
                    .collect();
                pending.push((*callee, incoming));
            }
        }
    }
    Ok(())
}

fn function_code<'a>(
    a: &'a Artifact,
    function: &Function,
) -> Result<&'a [Instruction], VerifyError> {
    let start = function.code_start as usize;
    let end = start
        .checked_add(function.code_len as usize)
        .ok_or(VerifyError::InvalidFunction(u32::MAX))?;
    a.code
        .get(start..end)
        .ok_or(VerifyError::InvalidFunction(u32::MAX))
}

fn verify_drop_hook_reachable(
    a: &Artifact,
    function_id: u32,
    visited: &mut std::collections::BTreeSet<u32>,
) -> Result<(), VerifyError> {
    if !visited.insert(function_id) {
        return Ok(());
    }
    let function = a
        .functions
        .get(function_id as usize)
        .ok_or(VerifyError::InvalidFunction(function_id))?;
    if !function.outward_protocols.is_empty() || function.label_slot_count != 0 {
        return Err(VerifyError::InvalidFunction(function_id));
    }
    for instruction in function_code(a, function)? {
        match instruction {
            Instruction::Call { function, .. } | Instruction::TailCall { function, .. } => {
                verify_drop_hook_reachable(a, *function, visited)?;
            }
            Instruction::LabelPush { .. }
            | Instruction::LabelPop { .. }
            | Instruction::Leave { .. }
            | Instruction::MakeHandler { .. }
            | Instruction::MakeHandlerShared { .. }
            | Instruction::Handle { .. }
            | Instruction::Perform { .. }
            | Instruction::Resume { .. }
            | Instruction::TailResume { .. }
            | Instruction::Cancel { .. }
            | Instruction::HostCall { .. }
            | Instruction::CallIndirect { .. }
            | Instruction::TailCallIndirect { .. } => {
                return Err(VerifyError::InvalidFunction(function_id));
            }
            _ => {}
        }
    }
    Ok(())
}

fn verify_cleanup_tables(a: &Artifact) -> Result<(), VerifyError> {
    let mut at = 0usize;
    for (fid, function) in a.functions.iter().enumerate() {
        let mut next = 0u32;
        while let Some(plan) = a.cleanups.get(at) {
            if plan.function != fid as u32 {
                break;
            }
            if plan.first_instruction != next
                || plan.end_instruction <= plan.first_instruction
                || plan.end_instruction > function.code_len
            {
                return Err(VerifyError::InvalidFunction(fid as u32));
            }
            let mut seen = std::collections::BTreeSet::new();
            if plan.registers.iter().any(|register| {
                *register as usize >= function.register_types.len() || !seen.insert(*register)
            }) {
                return Err(VerifyError::InvalidFunction(fid as u32));
            }
            next = plan.end_instruction;
            at += 1;
        }
        if next != function.code_len {
            return Err(VerifyError::InvalidFunction(fid as u32));
        }
    }
    if at != a.cleanups.len() {
        return Err(VerifyError::InvalidFunction(a.cleanups[at].function));
    }
    Ok(())
}

fn verify_types(a: &Artifact) -> Result<(), VerifyError> {
    fn valid_outward_row(a: &Artifact, signature: &Signature) -> bool {
        signature
            .outward_protocols
            .iter()
            .all(|protocol| (*protocol as usize) < a.protocols.len())
            && signature
                .outward_protocols
                .windows(2)
                .all(|pair| pair[0] < pair[1])
    }

    for import in &a.imports {
        if !valid_outward_row(a, &import.signature) {
            return Err(VerifyError::InvalidType(import.signature.result));
        }
        for &parameter in &import.signature.params {
            runtime_type_at(a, parameter)?;
        }
        runtime_type_at(a, import.signature.result)?;
    }

    if !a.protocols.windows(2).all(|pair| {
        (&pair[0].display_name, &pair[0].type_arguments)
            < (&pair[1].display_name, &pair[1].type_arguments)
    }) {
        return Err(VerifyError::InvalidType(u32::MAX));
    }
    for protocol in &a.protocols {
        for &argument in &protocol.type_arguments {
            runtime_type_at(a, argument)?;
        }
        for operation in &protocol.operations {
            if !valid_outward_row(a, &operation.payload_signature) {
                return Err(VerifyError::InvalidType(operation.result_type));
            }
            for &parameter in &operation.payload_signature.params {
                runtime_type_at(a, parameter)?;
            }
            runtime_type_at(a, operation.payload_signature.result)?;
            runtime_type_at(a, operation.result_type)?;
            if operation.terminal {
                if operation.result_type != crate::bytecode::NEVER
                    || operation.resumption_lower != 0
                    || operation.resumption_upper != Some(0)
                {
                    return Err(VerifyError::InvalidType(operation.result_type));
                }
            } else if operation
                .resumption_upper
                .is_some_and(|upper| operation.resumption_lower > upper)
            {
                return Err(VerifyError::InvalidType(operation.result_type));
            }
        }
    }
    let mut clause_resumption_identities = std::collections::BTreeSet::new();
    for definition in &a.handler_defs {
        runtime_type_at(a, definition.result_type)?;
        let mut seen = std::collections::BTreeSet::new();
        for clause in &definition.clauses {
            if !valid_outward_row(a, &clause.callable_signature) {
                return Err(VerifyError::InvalidType(definition.result_type));
            }
            if !seen.insert((clause.protocol, clause.operation)) {
                return Err(VerifyError::InvalidType(definition.result_type));
            }
            let operation = a
                .protocols
                .get(clause.protocol as usize)
                .and_then(|protocol| protocol.operations.get(clause.operation as usize))
                .ok_or(VerifyError::InvalidType(definition.result_type))?;
            let mut expected_params = operation.payload_signature.params.clone();
            if operation.terminal {
                if clause.resumption_type.is_some() {
                    return Err(VerifyError::InvalidType(definition.result_type));
                }
            } else {
                let resumption = clause
                    .resumption_type
                    .ok_or(VerifyError::InvalidType(definition.result_type))?;
                let descriptor = type_at(a, resumption)?;
                if !matches!(descriptor, Type::Resumption {
                    input_type,
                    output_type,
                    effect_signature,
                    lower_uses,
                    upper_uses,
                    ..
                } if *input_type == operation.result_type
                    && *output_type == definition.result_type
                    && effect_signature.params.is_empty()
                    && effect_signature.result == definition.result_type
                    && *lower_uses == operation.resumption_lower
                    && *upper_uses == operation.resumption_upper)
                {
                    return Err(VerifyError::InvalidType(definition.result_type));
                }
                if !clause_resumption_identities.insert(resumption) {
                    return Err(VerifyError::InvalidType(resumption));
                }
                expected_params.push(resumption);
            }
            if clause.callable_signature.params != expected_params
                || clause.callable_signature.result != definition.result_type
            {
                return Err(VerifyError::InvalidType(definition.result_type));
            }
        }
        if !definition.partial {
            for protocol in definition
                .clauses
                .iter()
                .map(|clause| clause.protocol)
                .collect::<std::collections::BTreeSet<_>>()
            {
                let operation_count = a.protocols[protocol as usize].operations.len();
                if (0..operation_count as u32)
                    .any(|operation| !seen.contains(&(protocol, operation)))
                {
                    return Err(VerifyError::InvalidType(definition.result_type));
                }
            }
        }
    }
    for declared_type in &a.types {
        let ty = declared_type.representation();
        match ty {
            Type::Tuple { fields, .. } => {
                for &field in fields {
                    type_at(a, field)?;
                }
            }
            Type::Struct { fields, .. } => {
                for field in fields {
                    type_at(a, field.ty)?;
                }
            }
            Type::Enum { variants, .. } => {
                for variant in variants {
                    for field in &variant.fields {
                        type_at(a, field.ty)?;
                    }
                }
            }
            Type::Callable {
                signature,
                capture_type,
                receiver_mode,
                ..
            } => {
                if *receiver_mode > 2 || !valid_outward_row(a, signature) {
                    return Err(VerifyError::InvalidType(*capture_type));
                }
                runtime_type_at(a, *capture_type)?;
                for &parameter in &signature.params {
                    runtime_type_at(a, parameter)?;
                }
                runtime_type_at(a, signature.result)?;
            }
            Type::Handler {
                handler_def,
                capture_type,
                ..
            } => {
                let definition = a
                    .handler_defs
                    .get(*handler_def as usize)
                    .ok_or(VerifyError::InvalidType(*capture_type))?;
                runtime_type_at(a, *capture_type)?;
                let clause_types =
                    callable_capture_fields(a, *capture_type, definition.clauses.len())?;
                for (callable_type, clause) in clause_types.into_iter().zip(&definition.clauses) {
                    let Type::Callable { signature, .. } = type_at(a, callable_type)? else {
                        return Err(VerifyError::InvalidType(callable_type));
                    };
                    if signature != &clause.callable_signature {
                        return Err(VerifyError::InvalidType(callable_type));
                    }
                }
            }
            Type::Resumption {
                input_type,
                output_type,
                effect_signature,
                lower_uses,
                upper_uses,
                copy,
                ..
            } => {
                if !valid_outward_row(a, effect_signature) {
                    return Err(VerifyError::InvalidType(*input_type));
                }
                runtime_type_at(a, *input_type)?;
                runtime_type_at(a, *output_type)?;
                for &parameter in &effect_signature.params {
                    runtime_type_at(a, parameter)?;
                }
                runtime_type_at(a, effect_signature.result)?;
                if upper_uses.is_some_and(|upper| *lower_uses > upper)
                    || *copy != upper_uses.is_none_or(|upper| upper > 1)
                {
                    return Err(VerifyError::InvalidType(*input_type));
                }
            }
            Type::BindingPack { payload_type, .. } => {
                runtime_type_at(a, *payload_type)?;
            }
            Type::Available { .. } => {}
            Type::Array { element }
            | Type::RefShared { referent: element }
            | Type::RefUnique { referent: element } => {
                runtime_type_at(a, *element)?;
            }
            _ => {}
        }
    }
    fn visit(a: &Artifact, id: TypeId, marks: &mut [u8]) -> Result<(), VerifyError> {
        match marks[id as usize] {
            1 => return Err(VerifyError::CyclicOwnedType(id)),
            2 => return Ok(()),
            _ => {}
        }
        marks[id as usize] = 1;
        match a.types[id as usize].representation() {
            Type::Tuple { fields, .. } => {
                for &x in fields {
                    visit(a, x, marks)?;
                }
            }
            Type::Struct { fields, .. } => {
                for field in fields {
                    visit(a, field.ty, marks)?;
                }
            }
            Type::Enum { variants, .. } => {
                for variant in variants {
                    for field in &variant.fields {
                        visit(a, field.ty, marks)?;
                    }
                }
            }
            Type::Array { element } => visit(a, *element, marks)?,
            // Reference edges do not participate in owned-layout cycles.
            Type::RefShared { .. }
            | Type::RefUnique { .. }
            | Type::Callable { .. }
            | Type::Handler { .. } => {}
            Type::Resumption { .. } => {}
            Type::BindingPack { payload_type, .. } => visit(a, *payload_type, marks)?,
            Type::Available { .. } => {}
            _ => {}
        }
        marks[id as usize] = 2;
        Ok(())
    }
    let mut marks = vec![0; a.types.len()];
    for id in 0..a.types.len() {
        visit(a, id as u32, &mut marks)?;
    }
    for (id, ty) in a.types.iter().enumerate() {
        if ty.claimed_duplicable() && !supports_copy(a, id as TypeId) {
            return Err(VerifyError::InvalidType(id as TypeId));
        }
        if ty.claimed_zero_use_allowed() && !supports_zero_use(a, id as TypeId) {
            return Err(VerifyError::InvalidType(id as TypeId));
        }
    }
    Ok(())
}

fn verify_function(
    a: &Artifact,
    fid: u32,
    f: &Function,
    require_cleanup_metadata: bool,
    allow_seeded_leave_generation: bool,
) -> Result<Vec<crate::bytecode::CleanupPlan>, VerifyError> {
    if f.outward_protocols
        .iter()
        .any(|protocol| *protocol as usize >= a.protocols.len())
        || !f.outward_protocols.windows(2).all(|pair| pair[0] < pair[1])
    {
        return Err(VerifyError::InvalidFunction(fid));
    }
    if f.params.len() + 1 > f.register_types.len()
        || f.params != f.register_types[1..1 + f.params.len()]
    {
        return Err(VerifyError::InvalidFunction(fid));
    }
    let receiver = f.register_types[0];
    match (f.receiver_mode, type_at(a, receiver)?) {
        (None, Type::Unit)
        | (Some(0), Type::RefShared { .. })
        | (Some(1), Type::RefUnique { .. })
        | (Some(2), _) => {}
        _ => return Err(VerifyError::InvalidFunction(fid)),
    }
    for &ty in f
        .register_types
        .iter()
        .chain(std::iter::once(&f.return_type))
    {
        type_at(a, ty)?;
        if matches!(type_at(a, ty)?, Type::Available { .. }) {
            return Err(VerifyError::InvalidFunction(fid));
        }
    }
    let start = f.code_start as usize;
    let end = start
        .checked_add(f.code_len as usize)
        .ok_or(VerifyError::InvalidFunction(fid))?;
    if f.code_len == 0 || end > a.code.len() {
        return Err(VerifyError::InvalidFunction(fid));
    }
    for (local, ins) in a.code[start..end].iter().enumerate() {
        shape(a, fid, local as u32, f, ins)?;
    }
    let label_states = verify_labels(a, fid, f)?;
    let continuation_live = continuation_live_registers(a, f, &label_states)?;
    let callable_targets = callable_targets_at_pcs(a, fid, f, &label_states)?;
    verify_resumption_quantities(a, fid, f, &label_states).map_err(|error| {
        eprintln!("quantity verification failed for {fid}: {error:?}");
        error
    })?;
    let enum_facts = verify_enum_dominance(a, fid, f, &label_states)?;
    let move_path_states = verify_move_paths(a, fid, f, &enum_facts, &label_states)?;
    let result_leaves = reference_leaves(a, f.return_type);
    let single_result_leaf = single_reference_leaf(a, f.return_type);
    let direct_reference_result = matches!(
        type_at(a, f.return_type)?.representation(),
        Type::RefShared { .. } | Type::RefUnique { .. }
    );
    if result_leaves.len() > 1
        || (single_result_leaf.is_some()
            && ((!direct_reference_result && !result_leaves.is_empty())
                || f.params.iter().any(|ty| reference_leaves(a, *ty).len() > 1)))
    {
        aggregate_reference_return_origins(a, fid, &mut Vec::new())?;
    } else if single_result_leaf.is_some() {
        reference_return_parameter(a, fid, &mut Vec::new())?;
    }
    let loan_states = verify_loans(a, fid, f, &label_states)?;
    let mut entry = vec![false; f.register_types.len()];
    entry[0] = f.receiver_mode.is_some();
    entry[1..1 + f.params.len()].fill(true);
    let mut states: Vec<Option<Vec<bool>>> = vec![None; f.code_len as usize];
    let mut order_entry = (0..=f.params.len())
        .filter(|&register| entry[register])
        .map(|register| register as u32)
        .collect::<Vec<_>>();
    let mut order_states: Vec<Option<Vec<u32>>> = vec![None; f.code_len as usize];
    // A deconstructed shell may be reconstructed into the same storage place
    // by compiler-generated observational pattern tests. Remember its owner
    // age so reconstruction cannot perturb observable reverse-cleanup order.
    let mut shell_age_states: Vec<Option<Vec<Option<usize>>>> = vec![None; f.code_len as usize];
    states[0] = Some(entry);
    order_states[0] = Some(std::mem::take(&mut order_entry));
    shell_age_states[0] = Some(vec![None; f.register_types.len()]);
    let mut expected_cleanup = vec![None; f.code_len as usize];
    let mut work = VecDeque::from([0u32]);
    while let Some(pc) = work.pop_front() {
        let mut state = states[pc as usize].clone().unwrap();
        let mut order = order_states[pc as usize].clone().unwrap();
        let mut shell_ages = shell_age_states[pc as usize].clone().unwrap();
        let expected = order.iter().rev().copied().collect::<Vec<_>>();
        let seeded = allow_seeded_leave_generation
            .then(|| cleanup_registers(a, fid, pc))
            .filter(|registers| !registers.is_empty());
        if let Some(seed) = seeded
            && !expected.iter().all(|register| seed.contains(register))
        {
            return Err(VerifyError::StateMismatch {
                function: fid,
                instruction: pc,
            });
        }
        // Compiler-provided LEAVE anchors may include the still-empty label
        // result slot. Preserve that exact suffix in the generated table;
        // ordinary liveness alone cannot reconstruct the protected-value
        // substitution performed by LEAVE.
        expected_cleanup[pc as usize] = Some(
            seeded
                .map(<[u32]>::to_vec)
                .unwrap_or_else(|| expected.clone()),
        );
        if require_cleanup_metadata {
            let plan = cleanup_registers(a, fid, pc);
            let exact = if f.label_slot_count == 0 {
                plan == expected
            } else {
                // Label result slots may be listed before `LEAVE` initializes
                // them so source and destination cleanup lists can have the
                // required suffix relationship. Runtime skips that empty slot.
                expected.iter().all(|register| plan.contains(register))
            };
            if !exact {
                return Err(VerifyError::StateMismatch {
                    function: fid,
                    instruction: pc,
                });
            }
        }
        let ins = &a.code[start + pc as usize];
        let before = state.clone();
        if let Instruction::Deconstruct { src } = ins {
            shell_ages[*src as usize] = order.iter().position(|register| register == src);
        }
        let successors = transfer(
            TransferContext {
                artifact: a,
                function_id: fid,
                pc,
                function: f,
                enum_variants: &enum_facts[pc as usize],
                move_paths: &move_path_states[pc as usize],
                loans: &loan_states[pc as usize],
                labels: &label_states[pc as usize],
                continuation_live: continuation_live
                    .get(pc as usize + 1)
                    .map_or(&[], Vec::as_slice),
                callable_targets: &callable_targets[pc as usize],
            },
            ins,
            &mut state,
        )?;
        if let Instruction::Move { dst, src } = ins {
            let position = order.iter().position(|register| register == src).ok_or(
                VerifyError::StateMismatch {
                    function: fid,
                    instruction: pc,
                },
            )?;
            order[position] = *dst;
        }
        order.retain(|register| state[*register as usize]);
        for register in 0..state.len() {
            if state[register] && !before[register] && !order.contains(&(register as u32)) {
                if matches!(ins, Instruction::Construct { dst, .. } if *dst as usize == register)
                    && let Some(position) = shell_ages[register].take()
                {
                    order.insert(position.min(order.len()), register as u32);
                } else {
                    shell_ages[register] = None;
                    order.push(register as u32);
                }
            }
        }
        for target in successors {
            if target >= f.code_len {
                return Err(VerifyError::InvalidTarget {
                    function: fid,
                    instruction: pc,
                    target,
                });
            }
            match &states[target as usize] {
                Some(old) if old != &state => {
                    return Err(VerifyError::StateMismatch {
                        function: fid,
                        instruction: target,
                    });
                }
                Some(_) => {}
                None => {
                    states[target as usize] = Some(state.clone());
                    order_states[target as usize] = Some(order.clone());
                    shell_age_states[target as usize] = Some(shell_ages.clone());
                    work.push_back(target);
                }
            }
            if let Some(previous) = &order_states[target as usize]
                && previous != &order
            {
                return Err(VerifyError::StateMismatch {
                    function: fid,
                    instruction: target,
                });
            }
            if let Some(previous) = &mut shell_age_states[target as usize] {
                let mut changed = false;
                for (existing, incoming) in previous.iter_mut().zip(&shell_ages) {
                    if existing.is_some() && existing != incoming {
                        *existing = None;
                        changed = true;
                    }
                }
                if changed && !work.contains(&target) {
                    work.push_back(target);
                }
            }
        }
    }
    let mut plans = Vec::new();
    let mut pc = 0u32;
    while pc < f.code_len {
        let registers = expected_cleanup[pc as usize].clone().unwrap_or_default();
        let first = pc;
        pc += 1;
        while pc < f.code_len
            && expected_cleanup[pc as usize]
                .as_ref()
                .is_some_and(|next| next == &registers)
        {
            pc += 1;
        }
        plans.push(crate::bytecode::CleanupPlan {
            function: fid,
            first_instruction: first,
            end_instruction: pc,
            registers,
        });
    }
    Ok(plans)
}

fn quantity_leaf_types(a: &Artifact, ty: TypeId) -> Vec<TypeId> {
    fn collect(a: &Artifact, ty: TypeId, visiting: &mut [bool], leaves: &mut Vec<TypeId>) {
        let Some(descriptor) = a.types.get(ty as usize) else {
            return;
        };
        if visiting[ty as usize] {
            // Callable/handler descriptors are nominal, pointer-like runtime
            // identities. Revisiting one describes the same recursive
            // environment shape, not another statically addressable leaf.
            return;
        }
        visiting[ty as usize] = true;
        match descriptor.representation() {
            Type::Resumption { .. } => leaves.push(ty),
            Type::Tuple { fields, .. } => {
                for &field in fields {
                    collect(a, field, visiting, leaves);
                }
            }
            Type::Struct { fields, .. } => {
                for field in fields {
                    collect(a, field.ty, visiting, leaves);
                }
            }
            Type::Callable { capture_type, .. } | Type::Handler { capture_type, .. } => {
                collect(a, *capture_type, visiting, leaves);
            }
            Type::Enum { variants, .. } => {
                for field in variants.iter().flat_map(|variant| &variant.fields) {
                    collect(a, field.ty, visiting, leaves);
                }
            }
            _ => {}
        }
        visiting[ty as usize] = false;
    }

    let mut leaves = Vec::new();
    collect(a, ty, &mut vec![false; a.types.len()], &mut leaves);
    leaves
}

fn quantity_field_leaf_range(
    a: &Artifact,
    ty: TypeId,
    variant: Option<u32>,
    field: u32,
) -> Option<std::ops::Range<usize>> {
    if let Type::RefShared { referent } | Type::RefUnique { referent } =
        a.types[ty as usize].representation()
    {
        return quantity_field_leaf_range(a, *referent, variant, field);
    }
    let (base, fields) = match (a.types[ty as usize].representation(), variant) {
        (Type::Tuple { fields, .. }, None) => (0, fields.clone()),
        (Type::Struct { fields, .. }, None) => (0, fields.iter().map(|field| field.ty).collect()),
        (Type::Enum { variants, .. }, Some(active)) => {
            let active = active as usize;
            let base: usize = variants
                .get(..active)?
                .iter()
                .flat_map(|variant| &variant.fields)
                .map(|field| quantity_leaf_types(a, field.ty).len())
                .sum();
            let fields = variants
                .get(active)?
                .fields
                .iter()
                .map(|field| field.ty)
                .collect();
            (base, fields)
        }
        _ => return None,
    };
    let field = usize::try_from(field).ok()?;
    let start: usize = fields
        .get(..field)?
        .iter()
        .map(|&ty| quantity_leaf_types(a, ty).len())
        .sum();
    let len = quantity_leaf_types(a, *fields.get(field)?).len();
    Some(base + start..base + start + len)
}

fn quantity_variant_leaf_range(
    a: &Artifact,
    ty: TypeId,
    active: u32,
) -> Option<std::ops::Range<usize>> {
    let Type::Enum { variants, .. } = a.types[ty as usize].representation() else {
        return None;
    };
    let active = active as usize;
    let start = variants
        .get(..active)?
        .iter()
        .flat_map(|variant| &variant.fields)
        .map(|field| quantity_leaf_types(a, field.ty).len())
        .sum::<usize>();
    let len = variants
        .get(active)?
        .fields
        .iter()
        .map(|field| quantity_leaf_types(a, field.ty).len())
        .sum::<usize>();
    Some(start..start + len)
}

/// Summaries are permutations from result leaves to receiver/parameter leaves.
/// They deliberately describe transport only: any resumption/cancel/drop in a
/// candidate body prevents certification, so quantity deltas cannot be hidden.
fn quantity_transport_summaries(a: &Artifact) -> Vec<Option<Vec<usize>>> {
    fn analyze_cfg(
        a: &Artifact,
        function: &Function,
        summaries: &[Option<Vec<usize>>],
    ) -> Option<Vec<usize>> {
        #[derive(Clone, Eq, PartialEq)]
        struct State(Vec<Vec<Option<usize>>>);
        let shapes = function
            .register_types
            .iter()
            .map(|&ty| quantity_leaf_types(a, ty).len())
            .collect::<Vec<_>>();
        let mut entry = State(
            shapes
                .iter()
                .map(|&len| vec![None; len])
                .collect::<Vec<_>>(),
        );
        let mut next_origin = 0;
        for register in 0..=function.params.len() {
            for slot in &mut entry.0[register] {
                *slot = Some(next_origin);
                next_origin += 1;
            }
        }
        let code = function_code(a, function).ok()?;
        let mut states = vec![None; code.len()];
        states[0] = Some(entry);
        let mut work = VecDeque::from([0usize]);
        let mut returned = None;
        while let Some(pc) = work.pop_front() {
            let mut state = states[pc].clone()?;
            let instruction = &code[pc];
            match instruction {
                Instruction::Move { dst, src } => {
                    if state.0[*src as usize].iter().any(Option::is_none)
                        || state.0[*dst as usize].iter().any(Option::is_some)
                        || shapes[*src as usize] != shapes[*dst as usize]
                    {
                        return None;
                    }
                    state.0[*dst as usize] = std::mem::take(&mut state.0[*src as usize]);
                    state.0[*src as usize] = vec![None; shapes[*src as usize]];
                }
                Instruction::Construct {
                    dst,
                    fields,
                    variant: None,
                    ..
                } => {
                    let incoming = fields
                        .iter()
                        .flat_map(|field| state.0[*field as usize].iter().copied())
                        .collect::<Vec<_>>();
                    if incoming.len() != shapes[*dst as usize]
                        || incoming.iter().any(Option::is_none)
                    {
                        return None;
                    }
                    state.0[*dst as usize] = incoming;
                    for field in fields {
                        state.0[*field as usize].fill(None);
                    }
                }
                Instruction::ProjectMove { dst, src, field } => {
                    let range = quantity_field_leaf_range(
                        a,
                        function.register_types[*src as usize],
                        None,
                        *field,
                    )?;
                    let projected = state.0[*src as usize][range.clone()].to_vec();
                    if projected.len() != shapes[*dst as usize]
                        || projected.iter().any(Option::is_none)
                    {
                        return None;
                    }
                    state.0[*dst as usize] = projected;
                    state.0[*src as usize][range].fill(None);
                }
                Instruction::Call {
                    dst: Some(dst),
                    function: callee,
                    args,
                } if shapes[*dst as usize] != 0 => {
                    let summary = summaries.get(*callee as usize)?.as_ref()?;
                    let incoming = args
                        .iter()
                        .flat_map(|arg| state.0[*arg as usize].iter().copied())
                        .collect::<Vec<_>>();
                    state.0[*dst as usize] = summary
                        .iter()
                        .map(|&leaf| incoming.get(leaf).copied().flatten())
                        .collect::<Option<Vec<_>>>()?
                        .into_iter()
                        .map(Some)
                        .collect();
                    for arg in args {
                        state.0[*arg as usize].fill(None);
                    }
                }
                Instruction::MakeHandlerShared {
                    dst,
                    functions,
                    captures,
                    ..
                } if shapes[*dst as usize] != 0
                    || captures
                        .iter()
                        .any(|capture| shapes[*capture as usize] != 0) =>
                {
                    let incoming = captures
                        .iter()
                        .flat_map(|capture| state.0[*capture as usize].iter().copied())
                        .collect::<Vec<_>>();
                    if incoming.is_empty()
                        || incoming.iter().any(Option::is_none)
                        || shapes[*dst as usize] != incoming.len().saturating_mul(functions.len())
                    {
                        return None;
                    }
                    state.0[*dst as usize] = (0..functions.len())
                        .flat_map(|_| incoming.iter().copied())
                        .collect();
                    for capture in captures {
                        state.0[*capture as usize].fill(None);
                    }
                }
                Instruction::Return { src: Some(src) } => {
                    let result = state.0[*src as usize]
                        .iter()
                        .copied()
                        .collect::<Option<Vec<_>>>()?;
                    let mut owned = result.clone();
                    owned.sort_unstable();
                    owned.dedup();
                    if owned != (0..next_origin).collect::<Vec<_>>()
                        || returned.as_ref().is_some_and(|known| known != &result)
                    {
                        return None;
                    }
                    returned = Some(result);
                    continue;
                }
                Instruction::Jump { .. } | Instruction::Switch { .. } => {}
                Instruction::Resume { resumption, .. }
                | Instruction::TailResume { resumption, .. }
                | Instruction::Cancel { resumption, .. }
                | Instruction::Drop {
                    register: resumption,
                } if shapes[*resumption as usize] != 0 => return None,
                Instruction::Copy { src, dst } | Instruction::ProjectCopy { src, dst, .. }
                    if shapes[*src as usize] != 0 || shapes[*dst as usize] != 0 =>
                {
                    return None;
                }
                Instruction::Call { dst, args, .. }
                    if dst.is_some_and(|dst| shapes[dst as usize] != 0)
                        || args.iter().any(|arg| shapes[*arg as usize] != 0) =>
                {
                    return None;
                }
                Instruction::CallSelf { .. }
                | Instruction::CallKnownReceiver { .. }
                | Instruction::TailCall { .. }
                | Instruction::TailCallSelf { .. }
                | Instruction::TailCallKnownReceiver { .. }
                | Instruction::CallIndirect { .. }
                | Instruction::TailCallIndirect { .. }
                | Instruction::TailResume { .. }
                | Instruction::Construct {
                    variant: Some(_), ..
                } => return None,
                _ => {}
            }
            let successors = match instruction {
                Instruction::Jump { target } => vec![*target as usize],
                Instruction::Switch {
                    cases, otherwise, ..
                } => cases
                    .iter()
                    .map(|(_, target)| *target as usize)
                    .chain(std::iter::once(*otherwise as usize))
                    .collect(),
                _ if pc + 1 < code.len() => vec![pc + 1],
                _ => vec![],
            };
            for target in successors {
                let slot = states.get_mut(target)?;
                match slot {
                    Some(previous) if previous != &state => return None,
                    Some(_) => {}
                    None => {
                        *slot = Some(state.clone());
                        work.push_back(target);
                    }
                }
            }
        }
        returned
    }

    fn analyze(
        a: &Artifact,
        function: &Function,
        summaries: &[Option<Vec<usize>>],
    ) -> Option<Vec<usize>> {
        if function_code(a, function).ok()?.iter().any(|instruction| {
            matches!(
                instruction,
                Instruction::Jump { .. } | Instruction::Switch { .. }
            )
        }) {
            return analyze_cfg(a, function, summaries);
        }
        let shapes = function
            .register_types
            .iter()
            .map(|&ty| quantity_leaf_types(a, ty).len())
            .collect::<Vec<_>>();
        let mut registers = shapes
            .iter()
            .map(|&len| vec![None; len])
            .collect::<Vec<Vec<Option<usize>>>>();
        let mut next = 0;
        for register in registers.iter_mut().take(function.params.len() + 1) {
            for slot in register {
                *slot = Some(next);
                next += 1;
            }
        }
        let expected_inputs = next;
        for instruction in function_code(a, function).ok()? {
            match instruction {
                Instruction::Move { dst, src } => {
                    if registers[*dst as usize].iter().any(Option::is_some)
                        || registers[*src as usize].iter().any(Option::is_none)
                        || shapes[*dst as usize] != shapes[*src as usize]
                    {
                        return None;
                    }
                    registers[*dst as usize] = std::mem::take(&mut registers[*src as usize]);
                    registers[*src as usize] = vec![None; shapes[*src as usize]];
                }
                Instruction::Construct { dst, fields, .. } => {
                    let incoming = fields
                        .iter()
                        .flat_map(|field| registers[*field as usize].iter().copied())
                        .collect::<Vec<_>>();
                    if incoming.len() != shapes[*dst as usize]
                        || incoming.iter().any(Option::is_none)
                    {
                        return None;
                    }
                    registers[*dst as usize] = incoming;
                    for field in fields {
                        registers[*field as usize].fill(None);
                    }
                }
                Instruction::ProjectMove { dst, src, field } => {
                    let range = quantity_field_leaf_range(
                        a,
                        function.register_types[*src as usize],
                        None,
                        *field,
                    )?;
                    let projected = registers[*src as usize][range.clone()].to_vec();
                    if projected.len() != shapes[*dst as usize]
                        || projected.iter().any(Option::is_none)
                    {
                        return None;
                    }
                    registers[*dst as usize] = projected;
                    registers[*src as usize][range].fill(None);
                }
                Instruction::Call {
                    dst: Some(dst),
                    function: callee,
                    args,
                } if shapes[*dst as usize] != 0 => {
                    let summary = summaries.get(*callee as usize)?.as_ref()?;
                    let incoming = args
                        .iter()
                        .flat_map(|arg| registers[*arg as usize].iter().copied())
                        .collect::<Vec<_>>();
                    let output = summary
                        .iter()
                        .map(|&leaf| *incoming.get(leaf)?)
                        .collect::<Option<Vec<_>>>()?;
                    if output.len() != shapes[*dst as usize] {
                        return None;
                    }
                    for arg in args {
                        registers[*arg as usize].fill(None);
                    }
                    registers[*dst as usize] = output.into_iter().map(Some).collect();
                }
                Instruction::MakeHandlerShared {
                    dst,
                    functions,
                    captures,
                    ..
                } if shapes[*dst as usize] != 0
                    || captures
                        .iter()
                        .any(|capture| shapes[*capture as usize] != 0) =>
                {
                    let incoming = captures
                        .iter()
                        .flat_map(|capture| registers[*capture as usize].iter().copied())
                        .collect::<Vec<_>>();
                    if incoming.is_empty()
                        || incoming.iter().any(Option::is_none)
                        || shapes[*dst as usize] != incoming.len().saturating_mul(functions.len())
                    {
                        return None;
                    }
                    registers[*dst as usize] = (0..functions.len())
                        .flat_map(|_| incoming.iter().copied())
                        .collect();
                    for capture in captures {
                        registers[*capture as usize].fill(None);
                    }
                }
                Instruction::Call { dst, args, .. }
                    if dst.is_some_and(|dst| shapes[dst as usize] != 0)
                        || args.iter().any(|arg| shapes[*arg as usize] != 0) =>
                {
                    return None;
                }
                Instruction::Return { src: Some(src) } => {
                    let result = registers[*src as usize]
                        .iter()
                        .copied()
                        .collect::<Option<Vec<_>>>()?;
                    let mut owned = result.clone();
                    owned.sort_unstable();
                    owned.dedup();
                    if owned != (0..expected_inputs).collect::<Vec<_>>() {
                        return None;
                    }
                    return Some(result);
                }
                Instruction::Resume { resumption, .. }
                | Instruction::TailResume { resumption, .. }
                | Instruction::Cancel { resumption, .. }
                | Instruction::Drop {
                    register: resumption,
                } if shapes[*resumption as usize] != 0 => return None,
                Instruction::Copy { src, dst } | Instruction::ProjectCopy { src, dst, .. }
                    if shapes[*src as usize] != 0 || shapes[*dst as usize] != 0 =>
                {
                    return None;
                }
                Instruction::Jump { .. }
                | Instruction::Switch { .. }
                | Instruction::TailCall { .. }
                | Instruction::CallSelf { .. }
                | Instruction::TailCallSelf { .. }
                | Instruction::CallKnownReceiver { .. }
                | Instruction::TailCallKnownReceiver { .. }
                | Instruction::CallIndirect { .. }
                | Instruction::TailCallIndirect { .. }
                | Instruction::TailResume { .. } => return None,
                Instruction::MakeCallable { dst, captures, .. }
                    if shapes[*dst as usize] != 0
                        || captures
                            .iter()
                            .any(|capture| shapes[*capture as usize] != 0) =>
                {
                    return None;
                }
                Instruction::MakeHandler { dst, clauses, .. }
                    if shapes[*dst as usize] != 0
                        || clauses.iter().any(|clause| shapes[*clause as usize] != 0) =>
                {
                    return None;
                }
                Instruction::MakeBindingPack { dst, payloads, .. }
                    if shapes[*dst as usize] != 0
                        || payloads
                            .iter()
                            .any(|payload| shapes[*payload as usize] != 0) =>
                {
                    return None;
                }
                _ => {}
            }
        }
        None
    }

    let mut summaries = a
        .functions
        .iter()
        .map(|function| {
            let inputs = function.register_types[..=function.params.len()]
                .iter()
                .map(|&ty| quantity_leaf_types(a, ty).len())
                .sum::<usize>();
            let outputs = quantity_leaf_types(a, function.return_type).len();
            (inputs == outputs && inputs != 0).then(|| (0..inputs).collect())
        })
        .collect::<Vec<_>>();
    let mut pinned = vec![false; a.functions.len()];
    let mut history = Vec::<Vec<Option<Vec<usize>>>>::new();
    for _ in 0..a
        .functions
        .len()
        .saturating_mul(a.functions.len())
        .saturating_mul(4)
        .max(8)
    {
        history.push(summaries.clone());
        let next = a
            .functions
            .iter()
            .enumerate()
            .map(|(index, function)| {
                (!pinned[index])
                    .then(|| analyze(a, function, &summaries))
                    .flatten()
            })
            .collect::<Vec<_>>();
        eprintln!("relaxed summary iteration: {:?}", next.get(10));
        if next == summaries {
            return next;
        }
        if let Some(cycle_start) = history.iter().position(|previous| previous == &next) {
            let mut eliminated = false;
            for index in 0..a.functions.len() {
                if history[cycle_start..]
                    .iter()
                    .any(|state| state[index] != next[index])
                {
                    pinned[index] = true;
                    eliminated = true;
                }
            }
            if !eliminated {
                return next;
            }
            summaries = next;
            for (index, summary) in summaries.iter_mut().enumerate() {
                if pinned[index] {
                    *summary = None;
                }
            }
            history.clear();
            continue;
        }
        summaries = next;
    }
    summaries
}

fn function_receiver_quantity_leaf_types(a: &Artifact, function: &Function) -> Vec<TypeId> {
    let receiver_type = function.register_types[0];
    match (
        function.receiver_mode,
        a.types[receiver_type as usize].representation(),
    ) {
        (Some(0 | 1), Type::RefShared { referent } | Type::RefUnique { referent }) => {
            quantity_leaf_types(a, *referent)
        }
        _ => quantity_leaf_types(a, receiver_type),
    }
}

fn quantity_deltas_satisfy(a: &Artifact, deltas: &[u64], leaves: &[TypeId]) -> bool {
    deltas.len() == leaves.len()
        && deltas.iter().zip(leaves).all(|(&delta, &leaf_ty)| {
            matches!(
                a.types[leaf_ty as usize].representation(),
                Type::Resumption {
                    lower_uses,
                    upper_uses,
                    ..
                } if delta >= u64::from(*lower_uses)
                    && upper_uses.is_none_or(|upper| delta <= u64::from(upper))
            )
        })
}

fn analyze_borrowed_receiver_resume_deltas(
    a: &Artifact,
    function_id: u32,
    summaries: &[Option<Vec<u64>>],
    relaxed: bool,
) -> Option<Vec<u64>> {
    let function = a.functions.get(function_id as usize)?;
    if !matches!(function.receiver_mode, Some(0 | 1)) {
        return None;
    }
    let referent = match a.types[function.register_types[0] as usize].representation() {
        Type::RefShared { referent } | Type::RefUnique { referent } => *referent,
        _ => return None,
    };
    let count = quantity_leaf_types(a, referent).len();
    let mut entry_origins = function
        .register_types
        .iter()
        .map(|&ty| vec![None; quantity_leaf_types(a, ty).len()])
        .collect::<Vec<_>>();
    entry_origins[0] = (0..count).map(Some).collect();
    let code = function_code(a, function).ok()?;
    let mut states = vec![None; code.len()];
    states[0] = Some((entry_origins, vec![0u64; count]));
    let mut work = VecDeque::from([0usize]);
    let mut returned = None;
    while let Some(pc) = work.pop_front() {
        let (mut origins, mut deltas) = states[pc].clone()?;
        let instruction = &code[pc];
        match instruction {
            Instruction::ProjectCopy { dst, src, field }
            | Instruction::ProjectMove { dst, src, field }
            | Instruction::ProjectBorrowShared { dst, src, field }
            | Instruction::ProjectBorrowUnique { dst, src, field } => {
                let source_type = if *src == 0 {
                    referent
                } else {
                    function.register_types[*src as usize]
                };
                let range = quantity_field_leaf_range(a, source_type, None, *field)?;
                let projected = origins[*src as usize].get(range.clone())?.to_vec();
                if projected.len() != origins[*dst as usize].len() {
                    return None;
                }
                origins[*dst as usize] = projected;
                if matches!(instruction, Instruction::ProjectMove { .. }) {
                    origins[*src as usize][range].fill(None);
                }
            }
            Instruction::Move { dst, src } | Instruction::Copy { dst, src } => {
                if origins[*dst as usize].len() != origins[*src as usize].len() {
                    return None;
                }
                origins[*dst as usize] = origins[*src as usize].clone();
                if matches!(instruction, Instruction::Move { .. }) {
                    origins[*src as usize].fill(None);
                }
            }
            Instruction::Resume { resumption, .. } | Instruction::TailResume { resumption, .. } => {
                match origins[*resumption as usize].as_slice() {
                    [Some(origin)] => deltas[*origin] = deltas[*origin].checked_add(1)?,
                    slots if slots.iter().all(Option::is_none) => {}
                    _ => return None,
                }
            }
            Instruction::Construct { dst, fields, .. } => {
                let incoming = fields
                    .iter()
                    .flat_map(|field| origins[*field as usize].iter().copied())
                    .collect::<Vec<_>>();
                if incoming.len() != origins[*dst as usize].len() {
                    return None;
                }
                origins[*dst as usize] = incoming;
                for field in fields {
                    origins[*field as usize].fill(None);
                }
            }
            Instruction::Drop { register }
            | Instruction::EndBorrow {
                reference: register,
            } => {
                origins[*register as usize].fill(None);
            }
            Instruction::CallSelf { dst, args }
            | Instruction::CallKnownReceiver { dst, args, .. } => {
                let (target, receiver) = match instruction {
                    Instruction::CallSelf { .. } => (function_id, 0),
                    Instruction::CallKnownReceiver {
                        function, receiver, ..
                    } => (*function, *receiver as usize),
                    _ => unreachable!(),
                };
                if args
                    .iter()
                    .any(|argument| origins[*argument as usize].iter().any(Option::is_some))
                    || dst.is_some_and(|dst| origins[dst as usize].iter().any(Option::is_some))
                {
                    return None;
                }
                let target_deltas = summaries.get(target as usize)?.as_ref()?;
                let receiver_origins = origins.get(receiver)?;
                if receiver_origins.len() != target_deltas.len() {
                    return None;
                }
                for (origin, delta) in receiver_origins.iter().zip(target_deltas) {
                    let origin = origin.as_ref().copied()?;
                    deltas[origin] = deltas[origin].checked_add(*delta)?;
                }
            }
            Instruction::TailCallSelf { args }
            | Instruction::TailCallKnownReceiver { args, .. } => {
                let (target, receiver) = match instruction {
                    Instruction::TailCallSelf { .. } => (function_id, 0),
                    Instruction::TailCallKnownReceiver {
                        function, receiver, ..
                    } => (*function, *receiver as usize),
                    _ => unreachable!(),
                };
                if args
                    .iter()
                    .any(|argument| origins[*argument as usize].iter().any(Option::is_some))
                {
                    return None;
                }
                let target_deltas = summaries.get(target as usize)?.as_ref()?;
                let receiver_origins = origins.get(receiver)?;
                if receiver_origins.len() != target_deltas.len() {
                    return None;
                }
                for (origin, delta) in receiver_origins.iter().zip(target_deltas) {
                    let origin = origin.as_ref().copied()?;
                    deltas[origin] = deltas[origin].checked_add(*delta)?;
                }
                merge_borrowed_receiver_deltas(&mut returned, deltas, relaxed)?;
                continue;
            }
            Instruction::Return { src: None } => {
                merge_borrowed_receiver_deltas(&mut returned, deltas, relaxed)?;
                continue;
            }
            Instruction::Return { src: Some(src) }
                if quantity_leaf_types(a, function.register_types[*src as usize]).is_empty() =>
            {
                merge_borrowed_receiver_deltas(&mut returned, deltas, relaxed)?;
                continue;
            }
            Instruction::Const { dst, .. }
            | Instruction::Primitive { dst, .. }
            | Instruction::Cancel { dst, .. } => origins[*dst as usize].fill(None),
            Instruction::Jump { .. } | Instruction::Switch { .. } | Instruction::Nop => {}
            _ => {
                if count != 0 {
                    return None;
                }
            }
        }
        let successors = match instruction {
            Instruction::Jump { target } => vec![*target as usize],
            Instruction::Switch {
                cases, otherwise, ..
            } => cases
                .iter()
                .map(|(_, target)| *target as usize)
                .chain(std::iter::once(*otherwise as usize))
                .collect(),
            Instruction::Return { .. }
            | Instruction::TailCall { .. }
            | Instruction::TailCallSelf { .. }
            | Instruction::TailCallKnownReceiver { .. }
            | Instruction::TailCallIndirect { .. }
            | Instruction::TailResume { .. }
            | Instruction::Perform { dst: None, .. }
            | Instruction::Unreachable
            | Instruction::Abort { .. } => vec![],
            _ if pc + 1 < code.len() => vec![pc + 1],
            _ => vec![],
        };
        for successor in successors {
            let incoming = (origins.clone(), deltas.clone());
            match states.get_mut(successor)? {
                Some(existing) if existing != &incoming => {
                    if !relaxed || existing.0 != incoming.0 || existing.1.len() != incoming.1.len()
                    {
                        return None;
                    }
                    let mut changed = false;
                    for (old, new) in existing.1.iter_mut().zip(incoming.1) {
                        let joined = (*old).max(new);
                        changed |= joined != *old;
                        *old = joined;
                    }
                    if changed {
                        work.push_back(successor);
                    }
                }
                Some(_) => {}
                slot @ None => {
                    *slot = Some(incoming);
                    work.push_back(successor);
                }
            }
        }
    }
    returned
}

fn merge_borrowed_receiver_deltas(
    returned: &mut Option<Vec<u64>>,
    incoming: Vec<u64>,
    relaxed: bool,
) -> Option<()> {
    match returned {
        Some(known) if known != &incoming => {
            if !relaxed || known.len() != incoming.len() {
                return None;
            }
            for (old, new) in known.iter_mut().zip(incoming) {
                *old = (*old).max(new);
            }
        }
        Some(_) => {}
        slot @ None => *slot = Some(incoming),
    }
    Some(())
}

fn borrowed_receiver_resume_delta_summaries(a: &Artifact) -> Vec<Option<Vec<u64>>> {
    let mut summaries = a
        .functions
        .iter()
        .map(|function| {
            matches!(function.receiver_mode, Some(0 | 1)).then(|| {
                let leaves = function_receiver_quantity_leaf_types(a, function);
                (!leaves.is_empty()).then(|| {
                    leaves
                        .iter()
                        .map(|leaf| match a.types[*leaf as usize].representation() {
                            Type::Resumption { lower_uses, .. } => u64::from(*lower_uses),
                            _ => unreachable!(),
                        })
                        .collect()
                })
            })?
        })
        .collect::<Vec<_>>();
    let iterations = summaries
        .len()
        .saturating_mul(summaries.len())
        .saturating_mul(4)
        .max(8);
    for _ in 0..iterations {
        let next = a
            .functions
            .iter()
            .enumerate()
            .map(|(function, _)| {
                analyze_borrowed_receiver_resume_deltas(a, function as u32, &summaries, true)
            })
            .collect::<Vec<_>>();
        eprintln!("exact summary iteration: {:?}", next.get(10));
        if next == summaries {
            summaries = next;
            break;
        }
        summaries = next;
    }
    for _ in 0..iterations {
        let next = a
            .functions
            .iter()
            .enumerate()
            .map(|(function, _)| {
                analyze_borrowed_receiver_resume_deltas(a, function as u32, &summaries, false)
            })
            .collect::<Vec<_>>();
        if next == summaries {
            return next;
        }
        summaries = next;
    }
    vec![None; a.functions.len()]
}

fn borrowed_receiver_resume_deltas(a: &Artifact, function: u32) -> Option<Vec<u64>> {
    borrowed_receiver_resume_delta_summaries(a)
        .get(function as usize)?
        .clone()
}

/// All dynamic alternatives must expose the same receiver-quantity behavior.
/// Merely having a compatible callable type is insufficient: a forged or
/// externally supplied producer has no body-derived proof and therefore has no
/// finite target set to certify here.
fn canonical_borrowed_receiver_resume_deltas(
    a: &Artifact,
    targets: &CallableTargets,
) -> Option<Vec<u64>> {
    let mut alternatives = targets
        .iter()
        .map(|target| borrowed_receiver_resume_deltas(a, *target));
    let first = alternatives.next()??;
    alternatives
        .all(|alternative| alternative.as_ref() == Some(&first))
        .then_some(first)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum QuantityTerminalDisposition {
    Returned,
    Resumed,
    Cancelled,
    Dropped,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct OwnedReceiverQuantitySummary {
    outputs: Vec<usize>,
    resumes: Vec<u64>,
    dispositions: Vec<QuantityTerminalDisposition>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct TerminalEffectPayloadSummary {
    protocol: u32,
    operation: u32,
    payloads: Vec<usize>,
    dropped: Vec<usize>,
}

type InstantiatedQuantityOutcome = (
    Vec<Option<usize>>,
    Vec<(usize, u64, QuantityTerminalDisposition)>,
);

/// Infer the exact input origins moved by an owned callable into one terminal
/// effect. This deliberately accepts only transport operations; quantity use
/// remains visible to the ordinary quantity verifier and cannot be hidden in
/// this summary.
fn terminal_effect_payload_summaries(a: &Artifact) -> Vec<Option<TerminalEffectPayloadSummary>> {
    fn analyze(
        a: &Artifact,
        function_id: u32,
        summaries: &[Option<TerminalEffectPayloadSummary>],
        targets_at_pcs: &[Vec<CallableTargets>],
    ) -> Option<TerminalEffectPayloadSummary> {
        let function = a.functions.get(function_id as usize)?;
        let shapes = function
            .register_types
            .iter()
            .map(|ty| quantity_leaf_types(a, *ty).len())
            .collect::<Vec<_>>();
        let input_count = shapes[..=function.params.len()].iter().sum::<usize>();
        if input_count == 0 {
            return None;
        }
        let mut entry = shapes
            .iter()
            .map(|len| vec![None; *len])
            .collect::<Vec<_>>();
        let mut origin = 0usize;
        for register in entry.iter_mut().take(function.params.len() + 1) {
            for slot in register {
                *slot = Some(origin);
                origin += 1;
            }
        }
        let code = function_code(a, function).ok()?;
        let mut states = vec![None; code.len()];
        states[0] = Some(entry);
        let mut work = VecDeque::from([0usize]);
        let mut effect = None;
        while let Some(pc) = work.pop_front() {
            let mut origins = states[pc].clone()?;
            let instruction = &code[pc];
            match instruction {
                Instruction::Move { dst, src } => {
                    if shapes[*dst as usize] != shapes[*src as usize] {
                        return None;
                    }
                    origins[*dst as usize] = std::mem::take(&mut origins[*src as usize]);
                    origins[*src as usize] = vec![None; shapes[*src as usize]];
                }
                Instruction::Construct { dst, fields, .. } => {
                    let incoming = fields
                        .iter()
                        .flat_map(|field| origins[*field as usize].iter().copied())
                        .collect::<Vec<_>>();
                    if incoming.len() != shapes[*dst as usize] {
                        return None;
                    }
                    origins[*dst as usize] = incoming;
                    for field in fields {
                        origins[*field as usize].fill(None);
                    }
                }
                Instruction::ProjectMove { dst, src, field } => {
                    let range = quantity_field_leaf_range(
                        a,
                        function.register_types[*src as usize],
                        None,
                        *field,
                    )?;
                    let projected = origins[*src as usize].get(range.clone())?.to_vec();
                    if projected.len() != shapes[*dst as usize] {
                        return None;
                    }
                    origins[*dst as usize] = projected;
                    origins[*src as usize][range].fill(None);
                }
                Instruction::MakeCallable { dst, captures, .. } => {
                    let incoming = captures
                        .iter()
                        .flat_map(|capture| origins[*capture as usize].iter().copied())
                        .collect::<Vec<_>>();
                    if incoming.len() != shapes[*dst as usize] {
                        return None;
                    }
                    origins[*dst as usize] = incoming;
                    for capture in captures {
                        origins[*capture as usize].fill(None);
                    }
                }
                Instruction::MakeHandler { dst, clauses, .. } => {
                    let incoming = clauses
                        .iter()
                        .flat_map(|clause| origins[*clause as usize].iter().copied())
                        .collect::<Vec<_>>();
                    if incoming.len() != shapes[*dst as usize] {
                        return None;
                    }
                    origins[*dst as usize] = incoming;
                    for clause in clauses {
                        origins[*clause as usize].fill(None);
                    }
                }
                Instruction::MakeHandlerShared {
                    dst,
                    functions,
                    captures,
                    ..
                } => {
                    let incoming = captures
                        .iter()
                        .flat_map(|capture| origins[*capture as usize].iter().copied())
                        .collect::<Vec<_>>();
                    if shapes[*dst as usize] != incoming.len().saturating_mul(functions.len()) {
                        return None;
                    }
                    origins[*dst as usize] = (0..functions.len())
                        .flat_map(|_| incoming.iter().copied())
                        .collect();
                    for capture in captures {
                        origins[*capture as usize].fill(None);
                    }
                }
                Instruction::Handle {
                    handler,
                    body,
                    args,
                    ..
                } => {
                    let body_targets = targets_at_pcs.get(pc)?.get(*body as usize)?;
                    let body_effect =
                        canonical_terminal_effect_payload_summary(summaries, body_targets)?;
                    let Type::Handler { handler_def, .. } =
                        type_at(a, function.register_types[*handler as usize]).ok()?
                    else {
                        return None;
                    };
                    let definition = a.handler_defs.get(*handler_def as usize)?;
                    if !definition.partial
                        || definition.clauses.iter().any(|clause| {
                            clause.protocol == body_effect.protocol
                                && clause.operation == body_effect.operation
                        })
                    {
                        return None;
                    }
                    let body_inputs = std::iter::once(*body)
                        .chain(args.iter().copied())
                        .flat_map(|operand| origins[operand as usize].iter().copied())
                        .collect::<Vec<_>>();
                    let payloads = body_effect
                        .payloads
                        .iter()
                        .map(|index| body_inputs.get(*index).copied().flatten())
                        .collect::<Option<Vec<_>>>()?;
                    let payload_origins = payloads
                        .iter()
                        .copied()
                        .collect::<std::collections::BTreeSet<_>>();
                    let dropped = origins
                        .iter()
                        .flatten()
                        .copied()
                        .flatten()
                        .filter(|origin| !payload_origins.contains(origin))
                        .collect::<std::collections::BTreeSet<_>>()
                        .into_iter()
                        .collect();
                    let summary = TerminalEffectPayloadSummary {
                        protocol: body_effect.protocol,
                        operation: body_effect.operation,
                        payloads,
                        dropped,
                    };
                    if effect.as_ref().is_some_and(|known| known != &summary) {
                        return None;
                    }
                    effect = Some(summary);
                    continue;
                }
                Instruction::Perform {
                    dst: None,
                    protocol,
                    operation,
                    payloads,
                } => {
                    let payloads = payloads
                        .iter()
                        .flat_map(|payload| origins[*payload as usize].iter().copied())
                        .collect::<Option<Vec<_>>>()?;
                    let payload_origins = payloads
                        .iter()
                        .copied()
                        .collect::<std::collections::BTreeSet<_>>();
                    let dropped = origins
                        .iter()
                        .flatten()
                        .copied()
                        .flatten()
                        .filter(|origin| !payload_origins.contains(origin))
                        .collect::<std::collections::BTreeSet<_>>()
                        .into_iter()
                        .collect();
                    let summary = TerminalEffectPayloadSummary {
                        protocol: *protocol,
                        operation: *operation,
                        payloads,
                        dropped,
                    };
                    if effect.as_ref().is_some_and(|known| known != &summary) {
                        return None;
                    }
                    effect = Some(summary);
                    continue;
                }
                Instruction::Jump { .. } | Instruction::Switch { .. } | Instruction::Nop => {}
                _ if instruction_register_uses(instruction)
                    .iter()
                    .all(|register| shapes[*register as usize] == 0)
                    && instruction_destination(instruction)
                        .is_none_or(|dst| shapes[dst as usize] == 0) => {}
                _ => return None,
            }
            let successors = match instruction {
                Instruction::Jump { target } => vec![*target as usize],
                Instruction::Switch {
                    cases, otherwise, ..
                } => cases
                    .iter()
                    .map(|case| case.1 as usize)
                    .chain(std::iter::once(*otherwise as usize))
                    .collect(),
                Instruction::Perform { dst: None, .. }
                | Instruction::Return { .. }
                | Instruction::Unreachable
                | Instruction::Abort { .. } => vec![],
                _ if pc + 1 < code.len() => vec![pc + 1],
                _ => vec![],
            };
            for successor in successors {
                match states.get_mut(successor)? {
                    Some(existing) if existing != &origins => return None,
                    Some(_) => {}
                    slot @ None => {
                        *slot = Some(origins.clone());
                        work.push_back(successor);
                    }
                }
            }
        }
        effect
    }

    let target_facts = a
        .functions
        .iter()
        .enumerate()
        .map(|(function, descriptor)| {
            let labels = verify_labels(a, function as u32, descriptor).ok()?;
            callable_targets_at_pcs(a, function as u32, descriptor, &labels).ok()
        })
        .collect::<Vec<_>>();
    let mut summaries = vec![None; a.functions.len()];
    let iterations = a
        .functions
        .len()
        .saturating_mul(a.functions.len())
        .saturating_mul(4)
        .max(8);
    for _ in 0..iterations {
        let next = a
            .functions
            .iter()
            .enumerate()
            .map(|(function, _)| {
                target_facts[function]
                    .as_ref()
                    .and_then(|targets| analyze(a, function as u32, &summaries, targets))
            })
            .collect::<Vec<_>>();
        if next == summaries {
            return next;
        }
        summaries = next;
    }
    a.functions
        .iter()
        .enumerate()
        .map(|(function, _)| {
            let next = target_facts[function]
                .as_ref()
                .and_then(|targets| analyze(a, function as u32, &summaries, targets));
            (next == summaries[function]).then(|| summaries[function].clone())?
        })
        .collect()
}

fn canonical_terminal_effect_payload_summary<'a>(
    summaries: &'a [Option<TerminalEffectPayloadSummary>],
    targets: &CallableTargets,
) -> Option<&'a TerminalEffectPayloadSummary> {
    let mut alternatives = targets
        .iter()
        .map(|target| summaries.get(*target as usize)?.as_ref());
    let first = alternatives.next()??;
    alternatives
        .all(|alternative| alternative == Some(first))
        .then_some(first)
}

/// Infer exact quantity behavior for an owned callable environment. Unlike the
/// transport-only summary, this records resumes and the terminal disposition of
/// every receiver leaf. The fixed point is deliberately exact: recursive or
/// dynamic alternatives which do not converge to one mapping are uncertified.
fn owned_receiver_quantity_summaries(a: &Artifact) -> Vec<Option<OwnedReceiverQuantitySummary>> {
    #[derive(Clone, Debug, Eq, PartialEq)]
    struct State {
        origins: Vec<Vec<Option<usize>>>,
        resumes: Vec<u64>,
        terminal: Vec<Option<QuantityTerminalDisposition>>,
    }

    fn analyze(
        a: &Artifact,
        fid: u32,
        summaries: &[Option<OwnedReceiverQuantitySummary>],
        terminal_summaries: &[Option<TerminalEffectPayloadSummary>],
        targets_at_pcs: &[Vec<CallableTargets>],
    ) -> Option<OwnedReceiverQuantitySummary> {
        let function = a.functions.get(fid as usize)?;
        let shapes = function
            .register_types
            .iter()
            .map(|ty| quantity_leaf_types(a, *ty).len())
            .collect::<Vec<_>>();
        let input_count = shapes[..=function.params.len()].iter().sum::<usize>();
        if input_count == 0 {
            return None;
        }
        let mut entry = State {
            origins: shapes.iter().map(|len| vec![None; *len]).collect(),
            resumes: vec![0; input_count],
            terminal: vec![None; input_count],
        };
        let mut next_origin = 0usize;
        for register in entry.origins.iter_mut().take(function.params.len() + 1) {
            for slot in register {
                *slot = Some(next_origin);
                next_origin += 1;
            }
        }
        let code = function_code(a, function).ok()?;
        let mut states = vec![None; code.len()];
        states[0] = Some(entry);
        let mut work = VecDeque::from([0usize]);
        let mut returned = None;

        let consume = |state: &mut State,
                       register: usize,
                       disposition: QuantityTerminalDisposition|
         -> Option<()> {
            let consumed = state
                .origins
                .get_mut(register)?
                .drain(..)
                .collect::<Vec<_>>();
            state.origins[register] = vec![None; shapes[register]];
            for origin in consumed.into_iter().flatten() {
                let still_live = state
                    .origins
                    .iter()
                    .flatten()
                    .any(|candidate| *candidate == Some(origin));
                if !still_live {
                    match state.terminal[origin] {
                        None => state.terminal[origin] = Some(disposition),
                        Some(existing) if existing == disposition => {}
                        Some(_) => return None,
                    }
                }
            }
            Some(())
        };

        while let Some(pc) = work.pop_front() {
            let mut state = states[pc].clone()?;
            let instruction = &code[pc];
            match instruction {
                Instruction::Move { dst, src } | Instruction::Copy { dst, src } => {
                    if shapes[*dst as usize] != shapes[*src as usize] {
                        return None;
                    }
                    state.origins[*dst as usize] = state.origins[*src as usize].clone();
                    if matches!(instruction, Instruction::Move { .. }) {
                        state.origins[*src as usize].fill(None);
                    }
                }
                Instruction::Construct { dst, fields, .. }
                | Instruction::MakeBindingPack {
                    dst,
                    payloads: fields,
                    ..
                } => {
                    let incoming = fields
                        .iter()
                        .flat_map(|field| state.origins[*field as usize].iter().copied())
                        .collect::<Vec<_>>();
                    if incoming.len() != shapes[*dst as usize] {
                        return None;
                    }
                    state.origins[*dst as usize] = incoming;
                    for field in fields {
                        state.origins[*field as usize].fill(None);
                    }
                }
                Instruction::ProjectMove { dst, src, field }
                | Instruction::ProjectCopy { dst, src, field } => {
                    let range = quantity_field_leaf_range(
                        a,
                        function.register_types[*src as usize],
                        None,
                        *field,
                    )?;
                    let projected = state.origins[*src as usize].get(range.clone())?.to_vec();
                    if projected.len() != shapes[*dst as usize] {
                        return None;
                    }
                    state.origins[*dst as usize] = projected;
                    if matches!(instruction, Instruction::ProjectMove { .. }) {
                        state.origins[*src as usize][range].fill(None);
                    }
                }
                Instruction::MakeCallable { dst, captures, .. } => {
                    let incoming = captures
                        .iter()
                        .flat_map(|capture| state.origins[*capture as usize].iter().copied())
                        .collect::<Vec<_>>();
                    if incoming.len() != shapes[*dst as usize] {
                        return None;
                    }
                    state.origins[*dst as usize] = incoming;
                    for capture in captures {
                        state.origins[*capture as usize].fill(None);
                    }
                }
                Instruction::MakeHandler { dst, clauses, .. } => {
                    let incoming = clauses
                        .iter()
                        .flat_map(|clause| state.origins[*clause as usize].iter().copied())
                        .collect::<Vec<_>>();
                    if incoming.len() != shapes[*dst as usize] {
                        return None;
                    }
                    state.origins[*dst as usize] = incoming;
                    for clause in clauses {
                        state.origins[*clause as usize].fill(None);
                    }
                }
                Instruction::MakeHandlerShared {
                    dst,
                    functions,
                    captures,
                    ..
                } => {
                    let incoming = captures
                        .iter()
                        .flat_map(|capture| state.origins[*capture as usize].iter().copied())
                        .collect::<Vec<_>>();
                    if shapes[*dst as usize] != incoming.len().saturating_mul(functions.len()) {
                        return None;
                    }
                    state.origins[*dst as usize] = (0..functions.len())
                        .flat_map(|_| incoming.iter().copied())
                        .collect();
                    for capture in captures {
                        state.origins[*capture as usize].fill(None);
                    }
                }
                Instruction::Deconstruct { src }
                    if state.origins[*src as usize].iter().all(Option::is_none) => {}
                Instruction::Resume {
                    resumption,
                    receiver_mode,
                    ..
                }
                | Instruction::TailResume {
                    resumption,
                    receiver_mode,
                    ..
                } => {
                    let [Some(origin)] = state.origins[*resumption as usize].as_slice() else {
                        return None;
                    };
                    state.resumes[*origin] = state.resumes[*origin].checked_add(1)?;
                    if *receiver_mode == 2 {
                        consume(
                            &mut state,
                            *resumption as usize,
                            QuantityTerminalDisposition::Resumed,
                        )?;
                    }
                    if matches!(instruction, Instruction::TailResume { .. }) {
                        if !quantity_leaf_types(a, function.return_type).is_empty() {
                            return None;
                        }
                        let dispositions =
                            state.terminal.iter().copied().collect::<Option<Vec<_>>>()?;
                        let summary = OwnedReceiverQuantitySummary {
                            outputs: vec![],
                            resumes: state.resumes,
                            dispositions,
                        };
                        if returned.as_ref().is_some_and(|known| known != &summary) {
                            return None;
                        }
                        returned = Some(summary);
                        continue;
                    }
                }
                Instruction::Cancel { resumption, .. } => consume(
                    &mut state,
                    *resumption as usize,
                    QuantityTerminalDisposition::Cancelled,
                )?,
                Instruction::Drop { register } => consume(
                    &mut state,
                    *register as usize,
                    QuantityTerminalDisposition::Dropped,
                )?,
                Instruction::Call {
                    dst,
                    function: callee,
                    args,
                } if args.iter().any(|argument| shapes[*argument as usize] != 0)
                    || dst.is_some_and(|dst| shapes[dst as usize] != 0) =>
                {
                    let summary = summaries.get(*callee as usize)?.as_ref()?;
                    let inputs = args
                        .iter()
                        .flat_map(|argument| state.origins[*argument as usize].iter().copied())
                        .collect::<Vec<_>>();
                    if inputs.len() != summary.resumes.len() {
                        return None;
                    }
                    for (input, delta) in inputs.iter().zip(&summary.resumes) {
                        let origin = input.as_ref().copied()?;
                        state.resumes[origin] = state.resumes[origin].checked_add(*delta)?;
                    }
                    let output = summary
                        .outputs
                        .iter()
                        .map(|index| inputs.get(*index).copied().flatten())
                        .collect::<Option<Vec<_>>>()?;
                    for argument in args {
                        state.origins[*argument as usize].fill(None);
                    }
                    if let Some(dst) = dst {
                        if output.len() != shapes[*dst as usize] {
                            return None;
                        }
                        state.origins[*dst as usize] = output.into_iter().map(Some).collect();
                    } else if !output.is_empty() {
                        return None;
                    }
                    for (index, disposition) in summary.dispositions.iter().enumerate() {
                        if *disposition == QuantityTerminalDisposition::Returned {
                            continue;
                        }
                        let origin = inputs[index]?;
                        if !state
                            .origins
                            .iter()
                            .flatten()
                            .any(|candidate| *candidate == Some(origin))
                        {
                            match state.terminal[origin] {
                                None => state.terminal[origin] = Some(*disposition),
                                Some(existing) if existing == *disposition => {}
                                Some(_) => return None,
                            }
                        }
                    }
                }
                Instruction::CallSelf { dst, args }
                | Instruction::CallKnownReceiver { dst, args, .. }
                    if args.iter().any(|argument| shapes[*argument as usize] != 0)
                        || dst.is_some_and(|dst| shapes[dst as usize] != 0) =>
                {
                    let callee = match instruction {
                        Instruction::CallSelf { .. } => fid,
                        Instruction::CallKnownReceiver { function, .. } => *function,
                        _ => unreachable!(),
                    };
                    let summary = summaries.get(callee as usize)?.as_ref()?;
                    let inputs = args
                        .iter()
                        .flat_map(|argument| state.origins[*argument as usize].iter().copied())
                        .collect::<Vec<_>>();
                    if inputs.len() != summary.resumes.len() {
                        return None;
                    }
                    for (input, delta) in inputs.iter().zip(&summary.resumes) {
                        let origin = input.as_ref().copied()?;
                        state.resumes[origin] = state.resumes[origin].checked_add(*delta)?;
                    }
                    let output = summary
                        .outputs
                        .iter()
                        .map(|index| inputs.get(*index).copied().flatten())
                        .collect::<Option<Vec<_>>>()?;
                    for argument in args {
                        state.origins[*argument as usize].fill(None);
                    }
                    if let Some(dst) = dst {
                        if output.len() != shapes[*dst as usize] {
                            return None;
                        }
                        state.origins[*dst as usize] = output.into_iter().map(Some).collect();
                    } else if !output.is_empty() {
                        return None;
                    }
                    for (index, disposition) in summary.dispositions.iter().enumerate() {
                        if *disposition == QuantityTerminalDisposition::Returned {
                            continue;
                        }
                        let origin = inputs[index]?;
                        if !state
                            .origins
                            .iter()
                            .flatten()
                            .any(|candidate| *candidate == Some(origin))
                        {
                            match state.terminal[origin] {
                                None => state.terminal[origin] = Some(*disposition),
                                Some(existing) if existing == *disposition => {}
                                Some(_) => return None,
                            }
                        }
                    }
                }
                Instruction::TailCall { args, .. }
                | Instruction::TailCallSelf { args }
                | Instruction::TailCallKnownReceiver { args, .. }
                    if args.iter().all(|argument| shapes[*argument as usize] == 0)
                        && quantity_leaf_types(a, function.return_type).is_empty() =>
                {
                    // A quantity-free tail callee cannot transport any of this
                    // frame's quantity origins, but it still terminates the
                    // frame. Preserve already established resume/cancel/drop
                    // dispositions instead of falling through as if another
                    // instruction could complete the summary.
                    let dispositions =
                        state.terminal.iter().copied().collect::<Option<Vec<_>>>()?;
                    let result = OwnedReceiverQuantitySummary {
                        outputs: vec![],
                        resumes: state.resumes,
                        dispositions,
                    };
                    if returned.as_ref().is_some_and(|known| known != &result) {
                        return None;
                    }
                    returned = Some(result);
                    continue;
                }
                Instruction::TailCall {
                    function: callee,
                    args,
                } if args.iter().any(|argument| shapes[*argument as usize] != 0) => {
                    let summary = summaries.get(*callee as usize)?.as_ref()?;
                    let inputs = args
                        .iter()
                        .flat_map(|argument| state.origins[*argument as usize].iter().copied())
                        .collect::<Vec<_>>();
                    if inputs.len() != summary.resumes.len() {
                        return None;
                    }
                    for (input, delta) in inputs.iter().zip(&summary.resumes) {
                        let origin = input.as_ref().copied()?;
                        state.resumes[origin] = state.resumes[origin].checked_add(*delta)?;
                    }
                    let outputs = summary
                        .outputs
                        .iter()
                        .map(|index| inputs.get(*index).copied().flatten())
                        .collect::<Option<Vec<_>>>()?;
                    for (index, disposition) in summary.dispositions.iter().enumerate() {
                        if *disposition != QuantityTerminalDisposition::Returned {
                            let origin = inputs[index]?;
                            match state.terminal[origin] {
                                None => state.terminal[origin] = Some(*disposition),
                                Some(existing) if existing == *disposition => {}
                                Some(_) => return None,
                            }
                        }
                    }
                    let dispositions = (0..input_count)
                        .map(|origin| {
                            outputs
                                .contains(&origin)
                                .then_some(QuantityTerminalDisposition::Returned)
                                .or(state.terminal[origin])
                        })
                        .collect::<Option<Vec<_>>>()?;
                    let result = OwnedReceiverQuantitySummary {
                        outputs,
                        resumes: state.resumes,
                        dispositions,
                    };
                    if returned.as_ref().is_some_and(|known| known != &result) {
                        return None;
                    }
                    returned = Some(result);
                    continue;
                }
                Instruction::TailCallSelf { args }
                | Instruction::TailCallKnownReceiver { args, .. }
                    if args.iter().any(|argument| shapes[*argument as usize] != 0) =>
                {
                    let callee = match instruction {
                        Instruction::TailCallSelf { .. } => fid,
                        Instruction::TailCallKnownReceiver { function, .. } => *function,
                        _ => unreachable!(),
                    };
                    let summary = summaries.get(callee as usize)?.as_ref()?;
                    let inputs = args
                        .iter()
                        .flat_map(|argument| state.origins[*argument as usize].iter().copied())
                        .collect::<Vec<_>>();
                    if inputs.len() != summary.resumes.len() {
                        return None;
                    }
                    for (input, delta) in inputs.iter().zip(&summary.resumes) {
                        let origin = input.as_ref().copied()?;
                        state.resumes[origin] = state.resumes[origin].checked_add(*delta)?;
                    }
                    let outputs = summary
                        .outputs
                        .iter()
                        .map(|index| inputs.get(*index).copied().flatten())
                        .collect::<Option<Vec<_>>>()?;
                    for (index, disposition) in summary.dispositions.iter().enumerate() {
                        if *disposition != QuantityTerminalDisposition::Returned {
                            let origin = inputs[index]?;
                            match state.terminal[origin] {
                                None => state.terminal[origin] = Some(*disposition),
                                Some(existing) if existing == *disposition => {}
                                Some(_) => return None,
                            }
                        }
                    }
                    let dispositions = (0..input_count)
                        .map(|origin| {
                            outputs
                                .contains(&origin)
                                .then_some(QuantityTerminalDisposition::Returned)
                                .or(state.terminal[origin])
                        })
                        .collect::<Option<Vec<_>>>()?;
                    let result = OwnedReceiverQuantitySummary {
                        outputs,
                        resumes: state.resumes,
                        dispositions,
                    };
                    if returned.as_ref().is_some_and(|known| known != &result) {
                        return None;
                    }
                    returned = Some(result);
                    continue;
                }
                Instruction::CallIndirect {
                    dst,
                    callable,
                    receiver_mode: 2,
                    args,
                } if args.iter().all(|argument| shapes[*argument as usize] == 0) => {
                    let targets = targets_at_pcs.get(pc)?.get(*callable as usize)?;
                    let inputs = state.origins[*callable as usize].clone();
                    if let Some(deltas) = canonical_borrowed_receiver_resume_deltas(a, targets) {
                        if inputs.len() != deltas.len()
                            || dst.is_some_and(|dst| shapes[dst as usize] != 0)
                        {
                            return None;
                        }
                        for (input, delta) in inputs.iter().zip(deltas) {
                            let origin = input.as_ref().copied()?;
                            state.resumes[origin] = state.resumes[origin].checked_add(delta)?;
                        }
                        consume(
                            &mut state,
                            *callable as usize,
                            QuantityTerminalDisposition::Dropped,
                        )?;
                    } else {
                        let summary =
                            canonical_owned_receiver_quantity_summary(summaries, targets)?;
                        if inputs.len() != summary.resumes.len() {
                            return None;
                        }
                        for (input, delta) in inputs.iter().zip(&summary.resumes) {
                            let origin = input.as_ref().copied()?;
                            state.resumes[origin] = state.resumes[origin].checked_add(*delta)?;
                        }
                        consume(
                            &mut state,
                            *callable as usize,
                            QuantityTerminalDisposition::Dropped,
                        )?;
                        for (index, disposition) in summary.dispositions.iter().enumerate() {
                            if *disposition != QuantityTerminalDisposition::Returned {
                                let origin = inputs[index]?;
                                state.terminal[origin] = Some(*disposition);
                            }
                        }
                        if let Some(dst) = dst {
                            let output = summary
                                .outputs
                                .iter()
                                .map(|index| inputs.get(*index).copied().flatten())
                                .collect::<Option<Vec<_>>>()?;
                            if output.len() != shapes[*dst as usize] {
                                return None;
                            }
                            state.origins[*dst as usize] = output.into_iter().map(Some).collect();
                        } else if !summary.outputs.is_empty() {
                            return None;
                        }
                    }
                }
                Instruction::CallIndirect {
                    dst,
                    callable,
                    receiver_mode,
                    args,
                } if dst.is_none_or(|dst| shapes[dst as usize] == 0)
                    && args.iter().all(|argument| shapes[*argument as usize] == 0) =>
                {
                    let targets = targets_at_pcs.get(pc)?.get(*callable as usize)?;
                    let deltas = canonical_borrowed_receiver_resume_deltas(a, targets)?;
                    let inputs = state.origins[*callable as usize].clone();
                    if inputs.len() != deltas.len() {
                        return None;
                    }
                    for (input, delta) in inputs.iter().zip(deltas) {
                        let origin = input.as_ref().copied()?;
                        state.resumes[origin] = state.resumes[origin].checked_add(delta)?;
                    }
                    if *receiver_mode == 2 {
                        consume(
                            &mut state,
                            *callable as usize,
                            QuantityTerminalDisposition::Dropped,
                        )?;
                    }
                }
                Instruction::TailCallIndirect {
                    callable,
                    receiver_mode,
                    args,
                } => {
                    let targets = targets_at_pcs.get(pc)?.get(*callable as usize)?;
                    let inputs = std::iter::once(*callable)
                        .chain(args.iter().copied())
                        .flat_map(|operand| state.origins[operand as usize].iter().copied())
                        .collect::<Vec<_>>();
                    if let Some(deltas) = canonical_borrowed_receiver_resume_deltas(a, targets) {
                        if *receiver_mode != 2
                            || args.iter().any(|argument| shapes[*argument as usize] != 0)
                            || inputs.len() != deltas.len()
                            || !quantity_leaf_types(a, function.return_type).is_empty()
                        {
                            return None;
                        }
                        for (input, delta) in inputs.iter().zip(deltas) {
                            let origin = input.as_ref().copied()?;
                            state.resumes[origin] = state.resumes[origin].checked_add(delta)?;
                            state.terminal[origin] = Some(QuantityTerminalDisposition::Dropped);
                        }
                        let dispositions =
                            state.terminal.iter().copied().collect::<Option<Vec<_>>>()?;
                        let result = OwnedReceiverQuantitySummary {
                            outputs: vec![],
                            resumes: state.resumes,
                            dispositions,
                        };
                        if returned.as_ref().is_some_and(|known| known != &result) {
                            return None;
                        }
                        returned = Some(result);
                        continue;
                    }
                    let summary = canonical_owned_receiver_quantity_summary(summaries, targets)?;
                    if inputs.len() != summary.resumes.len() {
                        return None;
                    }
                    for (input, delta) in inputs.iter().zip(&summary.resumes) {
                        let origin = input.as_ref().copied()?;
                        state.resumes[origin] = state.resumes[origin].checked_add(*delta)?;
                    }
                    let outputs = summary
                        .outputs
                        .iter()
                        .map(|index| inputs.get(*index).copied().flatten())
                        .collect::<Option<Vec<_>>>()?;
                    for (index, disposition) in summary.dispositions.iter().enumerate() {
                        if *disposition != QuantityTerminalDisposition::Returned {
                            let origin = inputs[index]?;
                            match state.terminal[origin] {
                                None => state.terminal[origin] = Some(*disposition),
                                Some(existing) if existing == *disposition => {}
                                Some(_) => return None,
                            }
                        }
                    }
                    let dispositions = (0..input_count)
                        .map(|origin| {
                            outputs
                                .contains(&origin)
                                .then_some(QuantityTerminalDisposition::Returned)
                                .or(state.terminal[origin])
                        })
                        .collect::<Option<Vec<_>>>()?;
                    let result = OwnedReceiverQuantitySummary {
                        outputs,
                        resumes: state.resumes,
                        dispositions,
                    };
                    if returned.as_ref().is_some_and(|known| known != &result) {
                        return None;
                    }
                    returned = Some(result);
                    continue;
                }
                Instruction::Handle {
                    dst,
                    handler,
                    body,
                    args,
                } if (shapes[*dst as usize] != 0
                    || shapes[*handler as usize] != 0
                    || shapes[*body as usize] != 0
                    || args.iter().any(|argument| shapes[*argument as usize] != 0))
                    && canonical_owned_receiver_quantity_summary(
                        summaries,
                        targets_at_pcs.get(pc)?.get(*body as usize)?,
                    )
                    .is_none() =>
                {
                    let body_targets = targets_at_pcs.get(pc)?.get(*body as usize)?;
                    let effect = canonical_terminal_effect_payload_summary(
                        terminal_summaries,
                        body_targets,
                    )?;
                    let Type::Handler { handler_def, .. } =
                        type_at(a, function.register_types[*handler as usize]).ok()?
                    else {
                        return None;
                    };
                    let definition = a.handler_defs.get(*handler_def as usize)?;
                    let clause_index = definition.clauses.iter().position(|clause| {
                        clause.protocol == effect.protocol && clause.operation == effect.operation
                    })?;
                    let clause_targets = finite_handler_clause_targets(
                        a,
                        function.register_types[*handler as usize],
                    )?;
                    let targets = clause_targets.get(clause_index)?;
                    let summary = canonical_owned_receiver_quantity_summary(summaries, targets)?;
                    let mut handler_offset = 0usize;
                    let mut selected_receiver_inputs = vec![];
                    let mut unselected_origins = vec![];
                    for (index, targets) in clause_targets.iter().enumerate() {
                        let target = *targets.first()?;
                        let receiver_len = function_receiver_quantity_leaf_types(
                            a,
                            a.functions.get(target as usize)?,
                        )
                        .len();
                        if targets.iter().any(|target| {
                            a.functions.get(*target as usize).is_none_or(|function| {
                                function_receiver_quantity_leaf_types(a, function).len()
                                    != receiver_len
                            })
                        }) {
                            return None;
                        }
                        let end = handler_offset.checked_add(receiver_len)?;
                        let receiver_inputs = state.origins[*handler as usize]
                            .get(handler_offset..end)?
                            .to_vec();
                        if index == clause_index {
                            selected_receiver_inputs = receiver_inputs;
                        } else {
                            unselected_origins.extend(receiver_inputs.into_iter().flatten());
                        }
                        handler_offset = end;
                    }
                    if handler_offset != state.origins[*handler as usize].len() {
                        return None;
                    }
                    let body_inputs = std::iter::once(*body)
                        .chain(args.iter().copied())
                        .flat_map(|operand| state.origins[operand as usize].iter().copied())
                        .collect::<Vec<_>>();
                    let clause_inputs = selected_receiver_inputs
                        .iter()
                        .copied()
                        .chain(
                            effect
                                .payloads
                                .iter()
                                .map(|index| body_inputs.get(*index).copied().flatten()),
                        )
                        .collect::<Option<Vec<_>>>()?;
                    if clause_inputs.len() != summary.resumes.len() {
                        return None;
                    }
                    let output = summary
                        .outputs
                        .iter()
                        .map(|index| clause_inputs.get(*index).copied())
                        .collect::<Option<Vec<_>>>()?;
                    if output.len() != shapes[*dst as usize] {
                        return None;
                    }
                    let effects = clause_inputs
                        .iter()
                        .zip(&summary.resumes)
                        .zip(&summary.dispositions)
                        .map(|((origin, resumes), disposition)| (*origin, *resumes, *disposition))
                        .collect::<Vec<_>>();
                    let forwarded_dropped = effect
                        .dropped
                        .iter()
                        .map(|index| body_inputs.get(*index).copied().flatten())
                        .collect::<Option<Vec<_>>>()?;
                    let mut operands = vec![*handler, *body];
                    operands.extend(args.iter().copied());
                    for operand in operands {
                        state.origins[operand as usize].fill(None);
                    }
                    state.origins[*dst as usize] = output.into_iter().map(Some).collect();
                    let mut combined = std::collections::BTreeMap::new();
                    for (origin, resumes, disposition) in effects {
                        let entry = combined.entry(origin).or_insert((0u64, disposition));
                        if entry.1 != disposition {
                            return None;
                        }
                        entry.0 = entry.0.checked_add(resumes)?;
                    }
                    for origin in forwarded_dropped {
                        if !clause_inputs.contains(&origin) {
                            let entry = combined
                                .entry(origin)
                                .or_insert((0u64, QuantityTerminalDisposition::Dropped));
                            if entry.1 != QuantityTerminalDisposition::Dropped {
                                return None;
                            }
                        }
                    }
                    for origin in unselected_origins {
                        if !clause_inputs.contains(&origin) {
                            let entry = combined
                                .entry(origin)
                                .or_insert((0u64, QuantityTerminalDisposition::Dropped));
                            if entry.1 != QuantityTerminalDisposition::Dropped {
                                return None;
                            }
                        }
                    }
                    for (origin, (resumes, disposition)) in combined {
                        state.resumes[origin] = state.resumes[origin].checked_add(resumes)?;
                        if disposition != QuantityTerminalDisposition::Returned
                            && !state
                                .origins
                                .iter()
                                .flatten()
                                .any(|candidate| *candidate == Some(origin))
                        {
                            match state.terminal[origin] {
                                None => state.terminal[origin] = Some(disposition),
                                Some(existing) if existing == disposition => {}
                                Some(_) => return None,
                            }
                        }
                    }
                }
                Instruction::Handle {
                    dst,
                    handler,
                    body,
                    args,
                } if shapes[*dst as usize] != 0
                    || shapes[*handler as usize] != 0
                    || shapes[*body as usize] != 0
                    || args.iter().any(|argument| shapes[*argument as usize] != 0) =>
                {
                    let body_targets = targets_at_pcs.get(pc)?.get(*body as usize)?;
                    let body_summary =
                        canonical_owned_receiver_quantity_summary(summaries, body_targets)?;
                    let body_inputs = std::iter::once(*body)
                        .chain(args.iter().copied())
                        .flat_map(|operand| state.origins[operand as usize].iter().copied())
                        .collect::<Vec<_>>();
                    if body_inputs.len() != body_summary.resumes.len() {
                        return None;
                    }
                    let expected_output = body_summary
                        .outputs
                        .iter()
                        .map(|index| body_inputs.get(*index).copied().flatten())
                        .collect::<Option<Vec<_>>>()?;
                    let expected_effects = body_inputs
                        .iter()
                        .zip(&body_summary.resumes)
                        .zip(&body_summary.dispositions)
                        .map(|((origin, resumes), disposition)| {
                            Some((origin.as_ref().copied()?, *resumes, *disposition))
                        })
                        .collect::<Option<Vec<_>>>()?;
                    let clause_targets = finite_handler_clause_targets(
                        a,
                        function.register_types[*handler as usize],
                    )?;
                    let mut offset = 0usize;
                    for targets in clause_targets {
                        let summary =
                            canonical_owned_receiver_quantity_summary(summaries, &targets)?;
                        let target = *targets.first()?;
                        let receiver_len = function_receiver_quantity_leaf_types(
                            a,
                            a.functions.get(target as usize)?,
                        )
                        .len();
                        let end = offset.checked_add(receiver_len)?;
                        let receiver_inputs = state.origins[*handler as usize].get(offset..end)?;
                        if summary.resumes.len() < receiver_len
                            || summary.outputs.iter().any(|index| *index >= receiver_len)
                            || summary.dispositions[receiver_len..]
                                .iter()
                                .any(|disposition| {
                                    *disposition == QuantityTerminalDisposition::Returned
                                })
                        {
                            return None;
                        }
                        let output = summary
                            .outputs
                            .iter()
                            .map(|index| receiver_inputs.get(*index).copied().flatten())
                            .collect::<Option<Vec<_>>>()?;
                        let effects = receiver_inputs
                            .iter()
                            .zip(&summary.resumes[..receiver_len])
                            .zip(&summary.dispositions[..receiver_len])
                            .map(|((origin, resumes), disposition)| {
                                Some((origin.as_ref().copied()?, *resumes, *disposition))
                            })
                            .collect::<Option<Vec<_>>>()?;
                        if output != expected_output || effects != expected_effects {
                            return None;
                        }
                        offset = end;
                    }
                    if offset != state.origins[*handler as usize].len()
                        || expected_output.len() != shapes[*dst as usize]
                    {
                        return None;
                    }
                    let mut operands = vec![*handler, *body];
                    operands.extend(args.iter().copied());
                    for operand in operands {
                        state.origins[operand as usize].fill(None);
                    }
                    state.origins[*dst as usize] = expected_output.into_iter().map(Some).collect();
                    let mut effects = std::collections::BTreeMap::new();
                    for (origin, resumes, disposition) in expected_effects {
                        let effect = effects.entry(origin).or_insert((0u64, disposition));
                        if effect.1 != disposition {
                            return None;
                        }
                        effect.0 = effect.0.checked_add(resumes)?;
                    }
                    for (origin, (resumes, disposition)) in effects {
                        state.resumes[origin] = state.resumes[origin].checked_add(resumes)?;
                        if disposition != QuantityTerminalDisposition::Returned
                            && !state
                                .origins
                                .iter()
                                .flatten()
                                .any(|candidate| *candidate == Some(origin))
                        {
                            match state.terminal[origin] {
                                None => state.terminal[origin] = Some(disposition),
                                Some(existing) if existing == disposition => {}
                                Some(_) => return None,
                            }
                        }
                    }
                }
                Instruction::Return { src } => {
                    let outputs = src
                        .map(|src| {
                            state.origins[src as usize]
                                .iter()
                                .copied()
                                .collect::<Option<Vec<_>>>()
                        })
                        .flatten()
                        .unwrap_or_default();
                    let mut dispositions = Vec::with_capacity(input_count);
                    for origin in 0..input_count {
                        if outputs.contains(&origin) {
                            dispositions.push(QuantityTerminalDisposition::Returned);
                        } else {
                            dispositions.push(state.terminal[origin]?);
                        }
                    }
                    let summary = OwnedReceiverQuantitySummary {
                        outputs,
                        resumes: state.resumes,
                        dispositions,
                    };
                    if returned.as_ref().is_some_and(|known| known != &summary) {
                        return None;
                    }
                    returned = Some(summary);
                    continue;
                }
                Instruction::Perform {
                    dst: None,
                    payloads,
                    ..
                } => {
                    if payloads
                        .iter()
                        .any(|payload| shapes[*payload as usize] != 0)
                    {
                        return None;
                    }
                    for origin in state.origins.iter().flatten().copied().flatten() {
                        match state.terminal[origin] {
                            None => {
                                state.terminal[origin] = Some(QuantityTerminalDisposition::Dropped)
                            }
                            Some(QuantityTerminalDisposition::Returned) => return None,
                            Some(_) => {}
                        }
                    }
                    let summary = OwnedReceiverQuantitySummary {
                        outputs: vec![],
                        resumes: state.resumes,
                        dispositions: state.terminal.into_iter().collect::<Option<Vec<_>>>()?,
                    };
                    if returned.as_ref().is_some_and(|known| known != &summary) {
                        return None;
                    }
                    returned = Some(summary);
                    continue;
                }
                Instruction::Const { dst, .. }
                | Instruction::Primitive { dst, .. }
                | Instruction::EnumTag { dst, .. } => {
                    if shapes[*dst as usize] != 0 {
                        return None;
                    }
                }
                Instruction::Jump { .. } | Instruction::Switch { .. } | Instruction::Nop => {}
                _ if instruction_register_uses(instruction)
                    .iter()
                    .all(|register| shapes[*register as usize] == 0)
                    && instruction_destination(instruction)
                        .is_none_or(|dst| shapes[dst as usize] == 0) => {}
                _ => return None,
            }
            let successors = match instruction {
                Instruction::Jump { target } => vec![*target as usize],
                Instruction::Switch {
                    cases, otherwise, ..
                } => cases
                    .iter()
                    .map(|case| case.1 as usize)
                    .chain(std::iter::once(*otherwise as usize))
                    .collect(),
                Instruction::Return { .. }
                | Instruction::Perform { dst: None, .. }
                | Instruction::TailResume { .. }
                | Instruction::TailCallIndirect { .. }
                | Instruction::Unreachable
                | Instruction::Abort { .. } => vec![],
                _ if pc + 1 < code.len() => vec![pc + 1],
                _ => vec![],
            };
            for successor in successors {
                match states.get_mut(successor)? {
                    Some(existing) if existing != &state => return None,
                    Some(_) => {}
                    slot @ None => {
                        *slot = Some(state.clone());
                        work.push_back(successor);
                    }
                }
            }
        }
        returned
    }

    let target_facts = a
        .functions
        .iter()
        .enumerate()
        .map(|(fid, function)| {
            let labels = verify_labels(a, fid as u32, function).ok()?;
            callable_targets_at_pcs(a, fid as u32, function, &labels).ok()
        })
        .collect::<Vec<_>>();
    let terminal_summaries = terminal_effect_payload_summaries(a);
    let mut summaries = a
        .functions
        .iter()
        .map(|function| {
            let inputs = function.register_types[..=function.params.len()]
                .iter()
                .map(|ty| quantity_leaf_types(a, *ty).len())
                .sum::<usize>();
            let outputs = quantity_leaf_types(a, function.return_type).len();
            (inputs != 0 && inputs == outputs).then(|| OwnedReceiverQuantitySummary {
                outputs: (0..inputs).collect(),
                resumes: vec![0; inputs],
                dispositions: vec![QuantityTerminalDisposition::Returned; inputs],
            })
        })
        .collect::<Vec<_>>();
    let mut pinned = vec![false; summaries.len()];
    let mut history = Vec::new();
    for _ in 0..summaries
        .len()
        .saturating_mul(summaries.len())
        .saturating_mul(4)
        .max(8)
    {
        history.push(summaries.clone());
        let next = a
            .functions
            .iter()
            .enumerate()
            .map(|(fid, _)| {
                (!pinned[fid])
                    .then(|| {
                        target_facts[fid].as_ref().and_then(|targets| {
                            analyze(a, fid as u32, &summaries, &terminal_summaries, targets)
                        })
                    })
                    .flatten()
            })
            .collect::<Vec<_>>();
        if next == summaries {
            return next;
        }
        if let Some(cycle) = history.iter().position(|state| state == &next) {
            let mut eliminated = false;
            for fid in 0..summaries.len() {
                if history[cycle..].iter().any(|state| state[fid] != next[fid]) {
                    pinned[fid] = true;
                    eliminated = true;
                }
            }
            if !eliminated {
                return next;
            }
            summaries = next;
            for (fid, summary) in summaries.iter_mut().enumerate() {
                if pinned[fid] {
                    *summary = None;
                }
            }
            history.clear();
        } else {
            summaries = next;
        }
    }
    summaries
}

fn canonical_owned_receiver_quantity_summary<'a>(
    summaries: &'a [Option<OwnedReceiverQuantitySummary>],
    targets: &CallableTargets,
) -> Option<&'a OwnedReceiverQuantitySummary> {
    let mut alternatives = targets
        .iter()
        .map(|target| summaries.get(*target as usize)?.as_ref());
    let first = alternatives.next()??;
    alternatives
        .all(|alternative| alternative == Some(first))
        .then_some(first)
}

fn finite_handler_clause_targets(
    a: &Artifact,
    handler_type: TypeId,
) -> Option<Vec<CallableTargets>> {
    let Type::Handler {
        handler_def,
        capture_type,
        ..
    } = type_at(a, handler_type).ok()?
    else {
        return None;
    };
    let definition = a.handler_defs.get(*handler_def as usize)?;
    callable_capture_fields(a, *capture_type, definition.clauses.len())
        .ok()?
        .into_iter()
        .map(|callable_type| {
            let targets = callable_type_producers(a, callable_type);
            (!targets.is_empty()).then_some(targets)
        })
        .collect()
}

/// Certify the disposition of every quantity-bearing operation payload and
/// fresh resumption supplied to a concrete handler clause. Payload ownership
/// crosses `Perform` without changing logical quantity identity; this exact
/// parameter summary is the receiving half of that transport proof.
fn verify_handler_parameter_quantity_dispositions(a: &Artifact) -> Result<(), VerifyError> {
    let summaries = owned_receiver_quantity_summaries(a);
    for descriptor in &a.types {
        let Type::Handler {
            handler_def,
            capture_type,
            ..
        } = descriptor.representation()
        else {
            continue;
        };
        let definition = a
            .handler_defs
            .get(*handler_def as usize)
            .ok_or(VerifyError::InvalidType(*capture_type))?;
        let callable_types = callable_capture_fields(a, *capture_type, definition.clauses.len())?;
        for (callable_type, clause) in callable_types.into_iter().zip(&definition.clauses) {
            if clause
                .callable_signature
                .params
                .iter()
                .all(|parameter| quantity_leaf_types(a, *parameter).is_empty())
            {
                continue;
            }
            let producers = callable_type_producers(a, callable_type);
            for producer in producers {
                let function = a
                    .functions
                    .get(producer as usize)
                    .ok_or(VerifyError::InvalidFunction(producer))?;
                let summary = summaries
                    .get(producer as usize)
                    .and_then(Option::as_ref)
                    .ok_or(VerifyError::InvalidFunction(producer))?;
                let mut origin = quantity_leaf_types(a, function.register_types[0]).len();
                for (parameter, &parameter_type) in
                    clause.callable_signature.params.iter().enumerate()
                {
                    let fresh_resumption = clause.resumption_type.is_some()
                        && parameter + 1 == clause.callable_signature.params.len();
                    for leaf_type in quantity_leaf_types(a, parameter_type) {
                        let Type::Resumption {
                            lower_uses,
                            upper_uses,
                            ..
                        } = type_at(a, leaf_type)?
                        else {
                            return Err(VerifyError::InvalidType(leaf_type));
                        };
                        let resumes = summary
                            .resumes
                            .get(origin)
                            .copied()
                            .ok_or(VerifyError::InvalidFunction(producer))?;
                        let disposition = summary
                            .dispositions
                            .get(origin)
                            .copied()
                            .ok_or(VerifyError::InvalidFunction(producer))?;
                        if resumes < u64::from(*lower_uses)
                            || upper_uses.is_some_and(|upper| resumes > u64::from(upper))
                            || (fresh_resumption
                                && disposition == QuantityTerminalDisposition::Returned)
                        {
                            return Err(VerifyError::InvalidFunction(producer));
                        }
                        origin += 1;
                    }
                }
            }
        }
    }
    Ok(())
}

fn canonical_quantity_transport_summary<'a>(
    summaries: &'a [Option<Vec<usize>>],
    targets: &CallableTargets,
) -> Option<&'a [usize]> {
    let mut alternatives = targets
        .iter()
        .map(|target| summaries.get(*target as usize)?.as_deref());
    let first = alternatives.next()??;
    alternatives
        .all(|alternative| alternative == Some(first))
        .then_some(first)
}

fn verify_resumption_quantities(
    a: &Artifact,
    fid: u32,
    f: &Function,
    label_states: &[Vec<LabelEntry>],
) -> Result<(), VerifyError> {
    fn visit_variants(
        a: &Artifact,
        fid: u32,
        f: &Function,
        label_states: &[Vec<LabelEntry>],
        register: usize,
        choices: &mut Vec<Option<u32>>,
    ) -> Result<(), VerifyError> {
        if register > f.params.len() {
            return verify_resumption_quantities_for_variants(a, fid, f, label_states, choices);
        }
        if let Type::Enum { variants, .. } =
            a.types[f.register_types[register] as usize].representation()
            && !quantity_leaf_types(a, f.register_types[register]).is_empty()
        {
            for variant in 0..variants.len() as u32 {
                choices[register] = Some(variant);
                visit_variants(a, fid, f, label_states, register + 1, choices)?;
            }
            choices[register] = None;
            Ok(())
        } else {
            visit_variants(a, fid, f, label_states, register + 1, choices)
        }
    }

    let mut choices = vec![None; f.params.len() + 1];
    visit_variants(a, fid, f, label_states, 0, &mut choices)
}

fn verify_resumption_quantities_for_variants(
    a: &Artifact,
    fid: u32,
    f: &Function,
    label_states: &[Vec<LabelEntry>],
    entry_variants: &[Option<u32>],
) -> Result<(), VerifyError> {
    let transport_summaries = quantity_transport_summaries(a);
    let owned_summaries = owned_receiver_quantity_summaries(a);
    let terminal_effect_summaries = terminal_effect_payload_summaries(a);
    let finite_callable_targets = callable_targets_at_pcs(a, fid, f, label_states)?;
    let finite_handler_representatives = |handler_type: TypeId| -> Option<Vec<u32>> {
        finite_handler_clause_targets(a, handler_type)?
            .into_iter()
            .map(|targets| {
                let representative = *targets.first()?;
                let receiver_len = function_receiver_quantity_leaf_types(
                    a,
                    a.functions.get(representative as usize)?,
                )
                .len();
                let same_receiver_shape = targets.iter().all(|target| {
                    a.functions.get(*target as usize).is_some_and(|function| {
                        function_receiver_quantity_leaf_types(a, function).len() == receiver_len
                    })
                });
                (same_receiver_shape
                    && (receiver_len == 0
                        || canonical_owned_receiver_quantity_summary(&owned_summaries, &targets)
                            .is_some()
                        || canonical_borrowed_receiver_resume_deltas(a, &targets).is_some()))
                .then_some(representative)
            })
            .collect()
    };
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct UseInterval {
        min: u64,
        max: u64,
    }

    #[derive(Clone, Debug, Eq, PartialEq)]
    struct QuantityState {
        // A register can hide more than one resumption inside a tuple/struct.
        // Slots follow the aggregate's depth-first field order.
        registers: Vec<Vec<Option<usize>>>,
        counts: Vec<Option<UseInterval>>,
        callable_targets: Vec<CallableTargets>,
        handler_targets: Vec<Option<Vec<u32>>>,
        // MAKE_HANDLER_SHARED materializes several callable views over one
        // runtime capture Rc. Repeated leaf slots in such a handler are aliases
        // of one quantity owner, not independently disposable resumptions.
        shared_handler_environment: Vec<bool>,
        enum_variants: Vec<Option<u32>>,
    }

    let mut leaf_types = f
        .register_types
        .iter()
        .map(|&ty| quantity_leaf_types(a, ty))
        .collect::<Vec<_>>();
    if matches!(f.receiver_mode, Some(0 | 1)) {
        let referent = match a.types[f.register_types[0] as usize].representation() {
            Type::RefShared { referent } | Type::RefUnique { referent } => Some(*referent),
            _ => None,
        };
        if let Some(referent) = referent {
            leaf_types[0] = quantity_leaf_types(a, referent);
        }
    }
    if !leaf_types.iter().any(|leaves| !leaves.is_empty()) {
        return Ok(());
    }
    let mut entry = QuantityState {
        registers: leaf_types
            .iter()
            .map(|leaves| vec![None; leaves.len()])
            .collect(),
        counts: vec![None; leaf_types[..=f.params.len()].iter().map(Vec::len).sum()],
        callable_targets: vec![CallableTargets::new(); leaf_types.len()],
        handler_targets: vec![None; leaf_types.len()],
        shared_handler_environment: vec![false; leaf_types.len()],
        enum_variants: vec![None; leaf_types.len()],
    };
    let mut group_base = 0usize;
    for (register, &entry_variant) in entry_variants.iter().enumerate() {
        let initialized = if let Some(active) = entry_variant {
            entry.enum_variants[register] = Some(active);
            quantity_variant_leaf_range(a, f.register_types[register], active)
                .ok_or(VerifyError::InvalidFunction(fid))?
        } else {
            0..entry.registers[register].len()
        };
        for (index, slot) in entry.registers[register][initialized.clone()]
            .iter_mut()
            .enumerate()
        {
            let group = group_base + initialized.start + index;
            *slot = Some(group);
            entry.counts[group] = Some(UseInterval { min: 0, max: 0 });
        }
        group_base += entry.registers[register].len();
    }
    let mut states = vec![None; f.code_len as usize];
    states[0] = Some(entry);
    let mut work = VecDeque::from([0u32]);
    let start = f.code_start as usize;
    while let Some(pc) = work.pop_front() {
        let mut state = states[pc as usize].clone().unwrap();
        let instruction = &a.code[start + pc as usize];
        let transfer_pristine =
            |state: &mut QuantityState, arguments: &[u32]| -> Result<(), VerifyError> {
                for &register in arguments {
                    for group in state.registers[register as usize].iter().copied() {
                        let Some(group) = group else { continue };
                        let locations = state
                            .registers
                            .iter()
                            .enumerate()
                            .flat_map(|(owner, slots)| {
                                slots
                                    .iter()
                                    .filter(move |candidate| **candidate == Some(group))
                                    .map(move |_| owner)
                            })
                            .collect::<Vec<_>>();
                        let one_shared_environment = !locations.is_empty()
                            && locations.iter().all(|owner| *owner == register as usize)
                            && state.shared_handler_environment[register as usize];
                        if state.counts[group] != Some(UseInterval { min: 0, max: 0 })
                            || (locations.len() != 1 && !one_shared_environment)
                        {
                            return Err(VerifyError::InvalidFunction(fid));
                        }
                    }
                }
                for &register in arguments {
                    for slot in &mut state.registers[register as usize] {
                        if let Some(group) = slot.take() {
                            state.counts[group] = None;
                        }
                    }
                }
                Ok(())
            };
        match instruction {
            Instruction::Resume {
                resumption,
                receiver_mode,
                ..
            }
            | Instruction::TailResume {
                resumption,
                receiver_mode,
                ..
            } if !leaf_types[*resumption as usize].is_empty() => {
                let Type::Resumption {
                    lower_uses,
                    upper_uses,
                    ..
                } = a.types[f.register_types[*resumption as usize] as usize].representation()
                else {
                    unreachable!()
                };
                let [slot] = state.registers[*resumption as usize].as_slice() else {
                    return Err(VerifyError::InvalidFunction(fid));
                };
                let group = slot.ok_or(VerifyError::UseOfEmpty {
                    function: fid,
                    instruction: pc,
                    register: *resumption,
                })?;
                let mut count = state.counts[group].ok_or(VerifyError::InvalidFunction(fid))?;
                let cutoff =
                    upper_uses.map_or(u64::from(*lower_uses), |upper| u64::from(upper) + 1);
                count.min = count.min.saturating_add(1).min(cutoff);
                count.max = count.max.saturating_add(1).min(cutoff);
                if upper_uses.is_some_and(|upper| count.max > u64::from(upper)) {
                    return Err(VerifyError::InvalidFunction(fid));
                }
                state.counts[group] = Some(count);
                if *receiver_mode == 2 {
                    state.registers[*resumption as usize][0] = None;
                    let final_alias = !state
                        .registers
                        .iter()
                        .flatten()
                        .any(|slot| *slot == Some(group));
                    if final_alias && count.min < u64::from(*lower_uses) {
                        return Err(VerifyError::InvalidFunction(fid));
                    }
                    if final_alias {
                        state.counts[group] = None;
                    }
                }
                if let Instruction::TailResume { value, .. } = instruction {
                    transfer_pristine(&mut state, &[*value])?;
                }
            }
            Instruction::Cancel { resumption, .. }
                if !leaf_types[*resumption as usize].is_empty() =>
            {
                let Type::Resumption { lower_uses, .. } =
                    a.types[f.register_types[*resumption as usize] as usize].representation()
                else {
                    unreachable!()
                };
                if *lower_uses != 0 {
                    return Err(VerifyError::InvalidFunction(fid));
                }
                let [slot] = state.registers[*resumption as usize].as_mut_slice() else {
                    return Err(VerifyError::InvalidFunction(fid));
                };
                let group = slot.take().ok_or(VerifyError::UseOfEmpty {
                    function: fid,
                    instruction: pc,
                    register: *resumption,
                })?;
                if !state
                    .registers
                    .iter()
                    .flatten()
                    .any(|slot| *slot == Some(group))
                {
                    state.counts[group] = None;
                }
            }
            Instruction::Drop { register } if !leaf_types[*register as usize].is_empty() => {
                let groups = state.registers[*register as usize]
                    .iter_mut()
                    .enumerate()
                    .filter_map(|(index, slot)| slot.take().map(|group| (group, index)))
                    .collect::<Vec<_>>();
                let mut discharged = std::collections::BTreeSet::new();
                for (group, index) in groups {
                    if !discharged.insert(group) {
                        continue;
                    }
                    let leaf_ty = leaf_types[*register as usize][index];
                    let Type::Resumption { lower_uses, .. } =
                        a.types[leaf_ty as usize].representation()
                    else {
                        unreachable!()
                    };
                    if !state
                        .registers
                        .iter()
                        .flatten()
                        .any(|slot| *slot == Some(group))
                        && state.counts[group]
                            .is_none_or(|count| count.min < u64::from(*lower_uses))
                    {
                        return Err(VerifyError::InvalidFunction(fid));
                    }
                    if !state
                        .registers
                        .iter()
                        .flatten()
                        .any(|slot| *slot == Some(group))
                    {
                        state.counts[group] = None;
                    }
                }
            }
            Instruction::Move { src, dst }
                if !leaf_types[*src as usize].is_empty()
                    || !leaf_types[*dst as usize].is_empty() =>
            {
                if state.registers[*dst as usize].iter().any(Option::is_some)
                    || state.registers[*src as usize].len() != state.registers[*dst as usize].len()
                {
                    return Err(VerifyError::InvalidFunction(fid));
                }
                state.registers[*dst as usize] =
                    std::mem::take(&mut state.registers[*src as usize]);
                state.registers[*src as usize] = vec![None; leaf_types[*src as usize].len()];
                state.callable_targets[*dst as usize] =
                    std::mem::take(&mut state.callable_targets[*src as usize]);
                state.handler_targets[*dst as usize] = state.handler_targets[*src as usize].take();
                state.shared_handler_environment[*dst as usize] =
                    std::mem::take(&mut state.shared_handler_environment[*src as usize]);
                state.enum_variants[*dst as usize] = state.enum_variants[*src as usize].take();
            }
            Instruction::Copy { src, dst }
                if !leaf_types[*src as usize].is_empty()
                    || !leaf_types[*dst as usize].is_empty() =>
            {
                // Runtime copy glue creates an independent continuation
                // snapshot, but both bytecode values originate from the same
                // declared resumption quantity. Keep one shared interval
                // obligation while tracking the two owned aliases separately.
                if state.registers[*dst as usize].iter().any(Option::is_some)
                    || state.registers[*src as usize].len() != state.registers[*dst as usize].len()
                {
                    return Err(VerifyError::InvalidFunction(fid));
                }
                state.registers[*dst as usize] = state.registers[*src as usize].clone();
                state.callable_targets[*dst as usize] =
                    state.callable_targets[*src as usize].clone();
                state.handler_targets[*dst as usize] = state.handler_targets[*src as usize].clone();
                state.shared_handler_environment[*dst as usize] =
                    state.shared_handler_environment[*src as usize];
                state.enum_variants[*dst as usize] = state.enum_variants[*src as usize];
            }
            Instruction::Construct {
                dst,
                fields,
                variant,
                ..
            } if !leaf_types[*dst as usize].is_empty()
                || fields
                    .iter()
                    .any(|&register| !leaf_types[register as usize].is_empty()) =>
            {
                let incoming = fields
                    .iter()
                    .flat_map(|&field| state.registers[field as usize].iter().copied())
                    .collect::<Vec<_>>();
                let destination = if let Some(variant) = variant {
                    quantity_field_leaf_range(a, f.register_types[*dst as usize], Some(*variant), 0)
                        .map(|first| {
                            let Type::Enum { variants, .. } =
                                a.types[f.register_types[*dst as usize] as usize].representation()
                            else {
                                unreachable!()
                            };
                            let len = variants[*variant as usize]
                                .fields
                                .iter()
                                .map(|field| quantity_leaf_types(a, field.ty).len())
                                .sum::<usize>();
                            first.start..first.start + len
                        })
                        .unwrap_or(0..0)
                } else {
                    0..state.registers[*dst as usize].len()
                };
                if incoming.len() != destination.len()
                    || incoming.iter().any(Option::is_none)
                    || state.registers[*dst as usize].iter().any(Option::is_some)
                {
                    return Err(VerifyError::InvalidFunction(fid));
                }
                state.registers[*dst as usize][destination].copy_from_slice(&incoming);
                state.enum_variants[*dst as usize] = *variant;
                state.callable_targets[*dst as usize] = fields
                    .iter()
                    .flat_map(|field| state.callable_targets[*field as usize].iter().copied())
                    .collect();
                for &field in fields {
                    state.registers[field as usize].fill(None);
                    state.callable_targets[field as usize].clear();
                }
            }
            Instruction::ProjectMove { dst, src, field }
            | Instruction::ProjectCopy { dst, src, field }
                if !leaf_types[*dst as usize].is_empty()
                    || !leaf_types[*src as usize].is_empty() =>
            {
                let Some(range) = quantity_field_leaf_range(
                    a,
                    f.register_types[*src as usize],
                    state.enum_variants[*src as usize],
                    *field,
                ) else {
                    return Err(VerifyError::InvalidFunction(fid));
                };
                let projected = state.registers[*src as usize][range.clone()].to_vec();
                if projected.len() != state.registers[*dst as usize].len()
                    || projected.iter().any(Option::is_none)
                    || state.registers[*dst as usize].iter().any(Option::is_some)
                {
                    return Err(VerifyError::InvalidFunction(fid));
                }
                state.registers[*dst as usize] = projected;
                state.callable_targets[*dst as usize] =
                    state.callable_targets[*src as usize].clone();
                if matches!(instruction, Instruction::ProjectMove { .. }) {
                    state.registers[*src as usize][range].fill(None);
                    state.callable_targets[*src as usize].clear();
                }
            }
            Instruction::MakeCallable {
                dst,
                function,
                captures,
                ..
            } if !leaf_types[*dst as usize].is_empty()
                || captures
                    .iter()
                    .any(|&register| !leaf_types[register as usize].is_empty()) =>
            {
                let incoming = captures
                    .iter()
                    .flat_map(|capture| state.registers[*capture as usize].iter().copied())
                    .collect::<Vec<_>>();
                if incoming.len() != state.registers[*dst as usize].len()
                    || incoming.iter().any(Option::is_none)
                    || state.registers[*dst as usize].iter().any(Option::is_some)
                {
                    return Err(VerifyError::InvalidFunction(fid));
                }
                for capture in captures {
                    state.registers[*capture as usize].fill(None);
                }
                state.registers[*dst as usize] = incoming;
                state.callable_targets[*dst as usize] = CallableTargets::from([*function]);
            }
            Instruction::MakeHandler { dst, clauses, .. } => {
                let targets = clauses
                    .iter()
                    .map(|clause| {
                        let targets = if state.callable_targets[*clause as usize].is_empty() {
                            &finite_callable_targets[pc as usize][*clause as usize]
                        } else {
                            &state.callable_targets[*clause as usize]
                        };
                        let representative =
                            *targets.first().ok_or(VerifyError::InvalidFunction(fid))?;
                        let receiver_len = function_receiver_quantity_leaf_types(
                            a,
                            &a.functions[representative as usize],
                        )
                        .len();
                        let canonical = targets.iter().all(|target| {
                            a.functions.get(*target as usize).is_some_and(|function| {
                                function_receiver_quantity_leaf_types(a, function).len()
                                    == receiver_len
                            })
                        }) && (receiver_len == 0
                            || canonical_owned_receiver_quantity_summary(
                                &owned_summaries,
                                targets,
                            )
                            .is_some()
                            || canonical_borrowed_receiver_resume_deltas(a, targets).is_some());
                        canonical
                            .then_some(representative)
                            .ok_or(VerifyError::InvalidFunction(fid))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let incoming = clauses
                    .iter()
                    .flat_map(|clause| state.registers[*clause as usize].iter().copied())
                    .collect::<Vec<_>>();
                if incoming.len() != state.registers[*dst as usize].len()
                    || incoming.iter().any(Option::is_none)
                {
                    return Err(VerifyError::InvalidFunction(fid));
                }
                for clause in clauses {
                    state.registers[*clause as usize].fill(None);
                    state.callable_targets[*clause as usize].clear();
                }
                state.registers[*dst as usize] = incoming;
                state.handler_targets[*dst as usize] = Some(targets);
            }
            Instruction::MakeHandlerShared {
                dst,
                functions,
                captures,
                ..
            } if !leaf_types[*dst as usize].is_empty()
                || captures
                    .iter()
                    .any(|&register| !leaf_types[register as usize].is_empty()) =>
            {
                let incoming = captures
                    .iter()
                    .flat_map(|capture| state.registers[*capture as usize].iter().copied())
                    .collect::<Vec<_>>();
                let destination_len = state.registers[*dst as usize].len();
                if incoming.is_empty()
                    || destination_len != incoming.len().saturating_mul(functions.len())
                    || incoming.iter().any(Option::is_none)
                {
                    return Err(VerifyError::InvalidFunction(fid));
                }
                for capture in captures {
                    state.registers[*capture as usize].fill(None);
                }
                state.registers[*dst as usize] = (0..functions.len())
                    .flat_map(|_| incoming.iter().copied())
                    .collect();
                state.handler_targets[*dst as usize] = Some(functions.clone());
                state.shared_handler_environment[*dst as usize] = true;
            }
            Instruction::MakeBindingPack { dst, payloads, .. }
                if !leaf_types[*dst as usize].is_empty()
                    || payloads
                        .iter()
                        .any(|&register| !leaf_types[register as usize].is_empty()) =>
            {
                return Err(VerifyError::InvalidFunction(fid));
            }
            Instruction::CallSelf { dst, args }
                if !leaf_types[0].is_empty()
                    || dst.is_some_and(|dst| !leaf_types[dst as usize].is_empty())
                    || args
                        .iter()
                        .any(|&register| !leaf_types[register as usize].is_empty()) =>
            {
                if dst.is_some_and(|dst| !leaf_types[dst as usize].is_empty()) {
                    return Err(VerifyError::InvalidFunction(fid));
                }
                let deltas = borrowed_receiver_resume_deltas(a, fid).ok_or_else(|| {
                    eprintln!("missing borrowed recursive delta summary for {fid}");
                    VerifyError::InvalidFunction(fid)
                })?;
                if deltas.len() != state.registers[0].len() {
                    return Err(VerifyError::InvalidFunction(fid));
                }
                let mut terminal_groups = Vec::new();
                for ((slot, &delta), &leaf_ty) in state.registers[0]
                    .iter_mut()
                    .zip(&deltas)
                    .zip(&leaf_types[0])
                {
                    let group = slot.ok_or(VerifyError::UseOfEmpty {
                        function: fid,
                        instruction: pc,
                        register: 0,
                    })?;
                    let count = state.counts[group]
                        .as_mut()
                        .ok_or(VerifyError::InvalidFunction(fid))?;
                    count.min = count.min.saturating_add(delta);
                    count.max = count.max.saturating_add(delta);
                    let Type::Resumption { upper_uses, .. } =
                        a.types[leaf_ty as usize].representation()
                    else {
                        unreachable!()
                    };
                    if upper_uses.is_some_and(|upper| count.max > u64::from(upper)) {
                        return Err(VerifyError::InvalidFunction(fid));
                    }
                    // A returning unique self-call has moved a one-shot leaf
                    // from the same receiver object that the parent frame
                    // observes after the call.
                    if upper_uses == &Some(1) && delta == 1 {
                        *slot = None;
                        terminal_groups.push((group, leaf_ty));
                    }
                }
                for (group, leaf_ty) in terminal_groups {
                    let final_alias = !state
                        .registers
                        .iter()
                        .flatten()
                        .any(|slot| *slot == Some(group));
                    if final_alias {
                        let Type::Resumption { lower_uses, .. } =
                            a.types[leaf_ty as usize].representation()
                        else {
                            unreachable!()
                        };
                        let count = state.counts[group].ok_or(VerifyError::InvalidFunction(fid))?;
                        if count.min < u64::from(*lower_uses) {
                            return Err(VerifyError::InvalidFunction(fid));
                        }
                        state.counts[group] = None;
                    }
                }
                transfer_pristine(&mut state, args)?;
            }
            Instruction::Call { dst, args, .. }
            | Instruction::CallKnownReceiver { dst, args, .. } => {
                if let Some(dst) = dst.filter(|dst| !leaf_types[*dst as usize].is_empty()) {
                    let function = match instruction {
                        Instruction::Call { function, .. }
                        | Instruction::CallKnownReceiver { function, .. } => *function,
                        _ => unreachable!(),
                    };
                    let summary = transport_summaries
                        .get(function as usize)
                        .and_then(Option::as_ref)
                        .cloned()
                        .or_else(|| {
                            owned_summaries
                                .get(function as usize)
                                .and_then(Option::as_ref)
                                .filter(|summary| {
                                    summary.resumes.iter().all(|resumes| *resumes == 0)
                                        && summary.dispositions.iter().all(|disposition| {
                                            *disposition == QuantityTerminalDisposition::Returned
                                        })
                                })
                                .map(|summary| summary.outputs.clone())
                        })
                        .ok_or(VerifyError::InvalidFunction(fid))?;
                    let incoming = args
                        .iter()
                        .flat_map(|arg| state.registers[*arg as usize].iter().copied())
                        .collect::<Vec<_>>();
                    let output = summary
                        .iter()
                        .map(|&leaf| incoming.get(leaf).copied().flatten())
                        .collect::<Vec<_>>();
                    if output.len() != state.registers[dst as usize].len()
                        || state.registers[dst as usize].iter().any(Option::is_some)
                    {
                        return Err(VerifyError::InvalidFunction(fid));
                    }
                    let targets = args
                        .iter()
                        .flat_map(|arg| state.callable_targets[*arg as usize].iter().copied())
                        .collect::<CallableTargets>();
                    for arg in args {
                        state.registers[*arg as usize].fill(None);
                        state.callable_targets[*arg as usize].clear();
                    }
                    state.registers[dst as usize] = output;
                    state.callable_targets[dst as usize] = targets;
                } else {
                    transfer_pristine(&mut state, args)?;
                }
            }
            Instruction::Handle {
                dst,
                handler,
                body,
                args,
            } if !leaf_types[*handler as usize].is_empty()
                || !leaf_types[*body as usize].is_empty()
                || args
                    .iter()
                    .any(|&register| !leaf_types[register as usize].is_empty()) =>
            'handle: {
                let handler_targets = state.handler_targets[*handler as usize]
                    .clone()
                    .or_else(|| finite_handler_representatives(f.register_types[*handler as usize]))
                    .ok_or(VerifyError::InvalidFunction(fid))?;
                let body_targets = if state.callable_targets[*body as usize].is_empty() {
                    &finite_callable_targets[pc as usize][*body as usize]
                } else {
                    &state.callable_targets[*body as usize]
                };
                let has_exact_owned_disposition =
                    canonical_owned_receiver_quantity_summary(&owned_summaries, body_targets)
                        .is_some()
                        && handler_targets.iter().all(|target| {
                            let summary = owned_summaries
                                .get(*target as usize)
                                .and_then(Option::as_ref);
                            summary.is_some_and(|summary| {
                                let receiver_len = function_receiver_quantity_leaf_types(
                                    a,
                                    &a.functions[*target as usize],
                                )
                                .len();
                                summary.resumes.len() >= receiver_len
                                    && summary.outputs.iter().all(|index| *index < receiver_len)
                                    && summary.dispositions[receiver_len..].iter().all(
                                        |disposition| {
                                            *disposition != QuantityTerminalDisposition::Returned
                                        },
                                    )
                            })
                        });
                if !leaf_types[*dst as usize].is_empty()
                    && state.registers[*handler as usize].is_empty()
                    && let Some(effect) = canonical_terminal_effect_payload_summary(
                        &terminal_effect_summaries,
                        body_targets,
                    )
                {
                    let Type::Handler { handler_def, .. } =
                        type_at(a, f.register_types[*handler as usize])?
                    else {
                        return Err(VerifyError::InvalidFunction(fid));
                    };
                    let definition = a
                        .handler_defs
                        .get(*handler_def as usize)
                        .ok_or(VerifyError::InvalidFunction(fid))?;
                    let clause_index = definition
                        .clauses
                        .iter()
                        .position(|clause| {
                            clause.protocol == effect.protocol
                                && clause.operation == effect.operation
                        })
                        .ok_or(VerifyError::InvalidFunction(fid))?;
                    let operation = a
                        .protocols
                        .get(effect.protocol as usize)
                        .and_then(|protocol| protocol.operations.get(effect.operation as usize))
                        .ok_or(VerifyError::InvalidFunction(fid))?;
                    if !operation.terminal {
                        return Err(VerifyError::InvalidFunction(fid));
                    }
                    let target = *handler_targets
                        .get(clause_index)
                        .ok_or(VerifyError::InvalidFunction(fid))?;
                    let clause_summary = owned_summaries
                        .get(target as usize)
                        .and_then(Option::as_ref)
                        .ok_or(VerifyError::InvalidFunction(fid))?;
                    if !function_receiver_quantity_leaf_types(a, &a.functions[target as usize])
                        .is_empty()
                    {
                        return Err(VerifyError::InvalidFunction(fid));
                    }
                    let body_inputs = std::iter::once(*body)
                        .chain(args.iter().copied())
                        .flat_map(|operand| state.registers[operand as usize].iter().copied())
                        .collect::<Vec<_>>();
                    let clause_inputs = effect
                        .payloads
                        .iter()
                        .map(|origin| body_inputs.get(*origin).copied().flatten())
                        .collect::<Option<Vec<_>>>()
                        .ok_or(VerifyError::InvalidFunction(fid))?;
                    if clause_inputs.len() != clause_summary.resumes.len() {
                        return Err(VerifyError::InvalidFunction(fid));
                    }
                    let output = clause_summary
                        .outputs
                        .iter()
                        .map(|origin| clause_inputs.get(*origin).copied())
                        .collect::<Option<Vec<_>>>()
                        .ok_or(VerifyError::InvalidFunction(fid))?;
                    if output.len() != state.registers[*dst as usize].len() {
                        return Err(VerifyError::InvalidFunction(fid));
                    }
                    let effects = clause_inputs
                        .iter()
                        .zip(&clause_summary.resumes)
                        .zip(&clause_summary.dispositions)
                        .map(|((group, resumes), disposition)| {
                            Some((*group, *resumes, *disposition))
                        })
                        .collect::<Option<Vec<_>>>()
                        .ok_or(VerifyError::InvalidFunction(fid))?;
                    let group_types = effects
                        .iter()
                        .map(|(group, _, _)| {
                            state
                                .registers
                                .iter()
                                .zip(&leaf_types)
                                .find_map(|(slots, types)| {
                                    slots
                                        .iter()
                                        .position(|slot| *slot == Some(*group))
                                        .map(|index| types[index])
                                })
                                .map(|ty| (*group, ty))
                                .ok_or(VerifyError::InvalidFunction(fid))
                        })
                        .collect::<Result<std::collections::BTreeMap<_, _>, _>>()?;
                    let mut combined = std::collections::BTreeMap::new();
                    for (group, resumes, disposition) in effects {
                        let entry = combined.entry(group).or_insert((0u64, disposition));
                        if entry.1 != disposition {
                            return Err(VerifyError::InvalidFunction(fid));
                        }
                        entry.0 = entry
                            .0
                            .checked_add(resumes)
                            .ok_or(VerifyError::InvalidFunction(fid))?;
                    }
                    let mut operands = vec![*handler, *body];
                    operands.extend(args.iter().copied());
                    for operand in operands {
                        state.registers[operand as usize].fill(None);
                    }
                    state.registers[*dst as usize] = output.into_iter().map(Some).collect();
                    for (group, (delta, disposition)) in combined {
                        let count = state.counts[group]
                            .as_mut()
                            .ok_or(VerifyError::InvalidFunction(fid))?;
                        count.min = count.min.saturating_add(delta);
                        count.max = count.max.saturating_add(delta);
                        let Type::Resumption {
                            lower_uses,
                            upper_uses,
                            ..
                        } = a.types[group_types[&group] as usize].representation()
                        else {
                            return Err(VerifyError::InvalidFunction(fid));
                        };
                        if upper_uses.is_some_and(|upper| count.max > u64::from(upper)) {
                            return Err(VerifyError::InvalidFunction(fid));
                        }
                        let still_live = state
                            .registers
                            .iter()
                            .flatten()
                            .any(|slot| *slot == Some(group));
                        if disposition != QuantityTerminalDisposition::Returned && !still_live {
                            if count.min < u64::from(*lower_uses) {
                                return Err(VerifyError::InvalidFunction(fid));
                            }
                            state.counts[group] = None;
                        }
                    }
                    state.handler_targets[*handler as usize] = None;
                    state.callable_targets[*body as usize].clear();
                    break 'handle;
                }
                if leaf_types[*dst as usize].is_empty() && !has_exact_owned_disposition {
                    let mut offset = 0usize;
                    for &target in &handler_targets {
                        let target_function = &a.functions[target as usize];
                        let receiver_leaves =
                            function_receiver_quantity_leaf_types(a, target_function);
                        let end = offset + receiver_leaves.len();
                        if end > leaf_types[*handler as usize].len() {
                            return Err(VerifyError::InvalidFunction(fid));
                        }
                        if matches!(target_function.receiver_mode, Some(0 | 1)) {
                            let deltas = borrowed_receiver_resume_deltas(a, target)
                                .ok_or(VerifyError::InvalidFunction(fid))?;
                            if !quantity_deltas_satisfy(a, &deltas, &receiver_leaves) {
                                return Err(VerifyError::InvalidFunction(fid));
                            }
                        }
                        offset = end;
                    }
                    let mut operands = vec![*handler, *body];
                    operands.extend(args.iter().copied());
                    transfer_pristine(&mut state, &operands)?;
                    state.handler_targets[*handler as usize] = None;
                    state.shared_handler_environment[*handler as usize] = false;
                    state.callable_targets[*body as usize].clear();
                    break 'handle;
                }
                if let Some(body_summary) =
                    canonical_owned_receiver_quantity_summary(&owned_summaries, body_targets)
                {
                    let instantiate = |summary: &OwnedReceiverQuantitySummary,
                                       inputs: &[Option<usize>]|
                     -> Option<InstantiatedQuantityOutcome> {
                        if inputs.len() != summary.resumes.len() {
                            return None;
                        }
                        let output = summary
                            .outputs
                            .iter()
                            .map(|index| inputs.get(*index).copied().flatten())
                            .collect::<Vec<_>>();
                        let effects = inputs
                            .iter()
                            .zip(&summary.resumes)
                            .zip(&summary.dispositions)
                            .map(|((group, resumes), disposition)| {
                                Some((group.as_ref().copied()?, *resumes, *disposition))
                            })
                            .collect::<Option<Vec<_>>>()?;
                        Some((output, effects))
                    };
                    let instantiate_handler =
                        |summary: &OwnedReceiverQuantitySummary,
                         inputs: &[Option<usize>]|
                         -> Option<InstantiatedQuantityOutcome> {
                            let receiver_len = inputs.len();
                            if summary.resumes.len() < receiver_len
                                || summary.outputs.iter().any(|index| *index >= receiver_len)
                                || summary.dispositions[receiver_len..]
                                    .iter()
                                    .any(|disposition| {
                                        *disposition == QuantityTerminalDisposition::Returned
                                    })
                            {
                                return None;
                            }
                            let output = summary
                                .outputs
                                .iter()
                                .map(|index| inputs.get(*index).copied().flatten())
                                .collect::<Vec<_>>();
                            let effects = inputs
                                .iter()
                                .zip(&summary.resumes[..receiver_len])
                                .zip(&summary.dispositions[..receiver_len])
                                .map(|((group, resumes), disposition)| {
                                    Some((group.as_ref().copied()?, *resumes, *disposition))
                                })
                                .collect::<Option<Vec<_>>>()?;
                            Some((output, effects))
                        };
                    let body_inputs = std::iter::once(*body)
                        .chain(args.iter().copied())
                        .flat_map(|operand| state.registers[operand as usize].iter().copied())
                        .collect::<Vec<_>>();
                    let expected = instantiate(body_summary, &body_inputs)
                        .ok_or(VerifyError::InvalidFunction(fid))?;
                    let mut offset = 0usize;
                    for target in &handler_targets {
                        let summary = owned_summaries
                            .get(*target as usize)
                            .and_then(Option::as_ref)
                            .ok_or(VerifyError::InvalidFunction(fid))?;
                        let receiver_len = function_receiver_quantity_leaf_types(
                            a,
                            &a.functions[*target as usize],
                        )
                        .len();
                        let end = offset + receiver_len;
                        let inputs = state.registers[*handler as usize]
                            .get(offset..end)
                            .ok_or(VerifyError::InvalidFunction(fid))?;
                        if instantiate_handler(summary, inputs).as_ref() != Some(&expected) {
                            return Err(VerifyError::InvalidFunction(fid));
                        }
                        offset = end;
                    }
                    if offset != state.registers[*handler as usize].len()
                        || expected.0.len() != state.registers[*dst as usize].len()
                    {
                        return Err(VerifyError::InvalidFunction(fid));
                    }
                    let group_types = expected
                        .1
                        .iter()
                        .map(|(group, _, _)| {
                            state
                                .registers
                                .iter()
                                .zip(&leaf_types)
                                .find_map(|(slots, types)| {
                                    slots
                                        .iter()
                                        .position(|slot| *slot == Some(*group))
                                        .map(|index| types[index])
                                })
                                .map(|ty| (*group, ty))
                                .ok_or(VerifyError::InvalidFunction(fid))
                        })
                        .collect::<Result<std::collections::BTreeMap<_, _>, _>>()?;
                    let mut effects = std::collections::BTreeMap::new();
                    for (group, resumes, disposition) in &expected.1 {
                        let entry = effects.entry(*group).or_insert((0u64, *disposition));
                        if entry.1 != *disposition {
                            return Err(VerifyError::InvalidFunction(fid));
                        }
                        entry.0 = entry
                            .0
                            .checked_add(*resumes)
                            .ok_or(VerifyError::InvalidFunction(fid))?;
                    }
                    let mut operands = vec![*handler, *body];
                    operands.extend(args.iter().copied());
                    for operand in operands {
                        state.registers[operand as usize].fill(None);
                    }
                    state.registers[*dst as usize] = expected.0;
                    for (group, (delta, disposition)) in effects {
                        let count = state.counts[group]
                            .as_mut()
                            .ok_or(VerifyError::InvalidFunction(fid))?;
                        count.min = count.min.saturating_add(delta);
                        count.max = count.max.saturating_add(delta);
                        let leaf_ty = group_types[&group];
                        let Type::Resumption {
                            lower_uses,
                            upper_uses,
                            ..
                        } = a.types[leaf_ty as usize].representation()
                        else {
                            return Err(VerifyError::InvalidFunction(fid));
                        };
                        if upper_uses.is_some_and(|upper| count.max > u64::from(upper)) {
                            return Err(VerifyError::InvalidFunction(fid));
                        }
                        let still_live = state
                            .registers
                            .iter()
                            .flatten()
                            .any(|slot| *slot == Some(group));
                        if disposition != QuantityTerminalDisposition::Returned && !still_live {
                            if count.min < u64::from(*lower_uses) {
                                return Err(VerifyError::InvalidFunction(fid));
                            }
                            state.counts[group] = None;
                        }
                    }
                    state.handler_targets[*handler as usize] = None;
                    state.shared_handler_environment[*handler as usize] = false;
                    state.callable_targets[*body as usize].clear();
                    break 'handle;
                }
                let body_summary = canonical_quantity_transport_summary(
                    &transport_summaries,
                    &state.callable_targets[*body as usize],
                )
                .ok_or(VerifyError::InvalidFunction(fid))?;
                let body_inputs = std::iter::once(*body)
                    .chain(args.iter().copied())
                    .flat_map(|operand| state.registers[operand as usize].iter().copied())
                    .collect::<Vec<_>>();
                let expected = body_summary
                    .iter()
                    .map(|&leaf| body_inputs.get(leaf).copied().flatten())
                    .collect::<Vec<_>>();
                let mut offset = 0usize;
                for target in handler_targets {
                    let summary = transport_summaries[target as usize]
                        .as_ref()
                        .ok_or(VerifyError::InvalidFunction(fid))?;
                    let target_function = &a.functions[target as usize];
                    let receiver_len =
                        function_receiver_quantity_leaf_types(a, target_function).len();
                    let end = offset + receiver_len;
                    let inputs = state.registers[*handler as usize]
                        .get(offset..end)
                        .ok_or(VerifyError::InvalidFunction(fid))?;
                    let output = summary
                        .iter()
                        .map(|&leaf| inputs.get(leaf).copied().flatten())
                        .collect::<Vec<_>>();
                    if output != expected {
                        return Err(VerifyError::InvalidFunction(fid));
                    }
                    offset = end;
                }
                if expected.len() != state.registers[*dst as usize].len() {
                    return Err(VerifyError::InvalidFunction(fid));
                }
                let mut operands = vec![*handler, *body];
                operands.extend(args.iter().copied());
                for operand in operands {
                    state.registers[operand as usize].fill(None);
                }
                state.registers[*dst as usize] = expected;
                state.handler_targets[*handler as usize] = None;
                state.shared_handler_environment[*handler as usize] = false;
                state.callable_targets[*body as usize].clear();
            }
            Instruction::Handle {
                dst,
                args,
                body: _,
                handler: _,
                ..
            }
            | Instruction::HostCall {
                dst: Some(dst),
                args,
                ..
            } if !leaf_types[*dst as usize].is_empty()
                || args
                    .iter()
                    .any(|&register| !leaf_types[register as usize].is_empty()) =>
            {
                return Err(VerifyError::InvalidFunction(fid));
            }
            Instruction::Handle { handler, body, .. }
                if !leaf_types[*handler as usize].is_empty()
                    || !leaf_types[*body as usize].is_empty() =>
            {
                return Err(VerifyError::InvalidFunction(fid));
            }
            Instruction::TailCall { args, .. }
            | Instruction::TailCallSelf { args }
            | Instruction::TailCallKnownReceiver { args, .. } => {
                transfer_pristine(&mut state, args)?
            }
            Instruction::HostCall {
                dst: None, args, ..
            }
            | Instruction::Primitive { args, .. }
                if args
                    .iter()
                    .any(|&register| !leaf_types[register as usize].is_empty()) =>
            {
                return Err(VerifyError::InvalidFunction(fid));
            }
            Instruction::Perform { payloads, .. }
                if payloads
                    .iter()
                    .any(|&register| !leaf_types[register as usize].is_empty()) =>
            {
                // The runtime moves these exact values into the selected
                // clause (or preserves them unchanged while forwarding).
                // Requiring a pristine sole owner prevents an alias or prior
                // use count from being laundered into the clause's fresh
                // parameter accounting.
                transfer_pristine(&mut state, payloads)?;
            }
            Instruction::CallIndirect {
                dst,
                callable,
                receiver_mode,
                args,
            } if dst.is_some_and(|dst| !leaf_types[dst as usize].is_empty())
                || !leaf_types[*callable as usize].is_empty()
                || args
                    .iter()
                    .any(|&register| !leaf_types[register as usize].is_empty()) =>
            'indirect: {
                let targets = if state.callable_targets[*callable as usize].is_empty() {
                    &finite_callable_targets[pc as usize][*callable as usize]
                } else {
                    &state.callable_targets[*callable as usize]
                };
                if targets.is_empty() {
                    return Err(VerifyError::InvalidFunction(fid));
                }
                if *receiver_mode != 2 {
                    if dst.is_some_and(|dst| !leaf_types[dst as usize].is_empty()) {
                        return Err(VerifyError::InvalidFunction(fid));
                    }
                    let deltas = canonical_borrowed_receiver_resume_deltas(a, targets)
                        .ok_or(VerifyError::InvalidFunction(fid))?;
                    if deltas.len() != state.registers[*callable as usize].len() {
                        return Err(VerifyError::InvalidFunction(fid));
                    }
                    for ((slot, &delta), &leaf_ty) in state.registers[*callable as usize]
                        .iter()
                        .zip(&deltas)
                        .zip(&leaf_types[*callable as usize])
                    {
                        let group = slot.ok_or(VerifyError::UseOfEmpty {
                            function: fid,
                            instruction: pc,
                            register: *callable,
                        })?;
                        let count = state.counts[group]
                            .as_mut()
                            .ok_or(VerifyError::InvalidFunction(fid))?;
                        count.min = count.min.saturating_add(delta);
                        count.max = count.max.saturating_add(delta);
                        let Type::Resumption { upper_uses, .. } =
                            a.types[leaf_ty as usize].representation()
                        else {
                            unreachable!()
                        };
                        if upper_uses.is_some_and(|upper| count.max > u64::from(upper)) {
                            return Err(VerifyError::InvalidFunction(fid));
                        }
                    }
                    transfer_pristine(&mut state, args)?;
                    break 'indirect;
                }
                let mut operands = vec![*callable];
                operands.extend(args.iter().copied());
                if let Some(dst) = dst.filter(|dst| !leaf_types[*dst as usize].is_empty()) {
                    let summary =
                        canonical_quantity_transport_summary(&transport_summaries, targets)
                            .ok_or(VerifyError::InvalidFunction(fid))?;
                    let incoming = operands
                        .iter()
                        .flat_map(|operand| state.registers[*operand as usize].iter().copied())
                        .collect::<Vec<_>>();
                    let output = summary
                        .iter()
                        .map(|&leaf| incoming.get(leaf).copied().flatten())
                        .collect::<Vec<_>>();
                    if output.len() != state.registers[dst as usize].len() {
                        return Err(VerifyError::InvalidFunction(fid));
                    }
                    for operand in operands {
                        state.registers[operand as usize].fill(None);
                    }
                    state.callable_targets[*callable as usize].clear();
                    state.registers[dst as usize] = output;
                } else {
                    if let Some(deltas) = canonical_borrowed_receiver_resume_deltas(a, targets) {
                        if deltas.len() != state.registers[*callable as usize].len() {
                            return Err(VerifyError::InvalidFunction(fid));
                        }
                        for ((slot, &delta), &leaf_ty) in state.registers[*callable as usize]
                            .iter()
                            .zip(&deltas)
                            .zip(&leaf_types[*callable as usize])
                        {
                            let group = slot.ok_or(VerifyError::UseOfEmpty {
                                function: fid,
                                instruction: pc,
                                register: *callable,
                            })?;
                            let count = state.counts[group]
                                .as_mut()
                                .ok_or(VerifyError::InvalidFunction(fid))?;
                            count.min = count.min.saturating_add(delta);
                            count.max = count.max.saturating_add(delta);
                            let Type::Resumption {
                                lower_uses,
                                upper_uses,
                                ..
                            } = a.types[leaf_ty as usize].representation()
                            else {
                                unreachable!()
                            };
                            if upper_uses.is_some_and(|upper| count.max > u64::from(upper)) {
                                return Err(VerifyError::InvalidFunction(fid));
                            }
                            let final_alias =
                                !state.registers.iter().enumerate().any(|(register, slots)| {
                                    register != *callable as usize && slots.contains(&Some(group))
                                });
                            if final_alias && count.min < u64::from(*lower_uses) {
                                return Err(VerifyError::InvalidFunction(fid));
                            }
                        }
                        let groups = state.registers[*callable as usize]
                            .iter()
                            .copied()
                            .flatten()
                            .collect::<Vec<_>>();
                        state.registers[*callable as usize].fill(None);
                        for group in groups {
                            if !state
                                .registers
                                .iter()
                                .flatten()
                                .any(|slot| *slot == Some(group))
                            {
                                state.counts[group] = None;
                            }
                        }
                        transfer_pristine(&mut state, args)?;
                    } else {
                        transfer_pristine(&mut state, &operands)?;
                    }
                    state.callable_targets[*callable as usize].clear();
                }
            }
            Instruction::TailCallIndirect { callable, args, .. }
                if !leaf_types[*callable as usize].is_empty()
                    || args
                        .iter()
                        .any(|&register| !leaf_types[register as usize].is_empty()) =>
            {
                let targets = if state.callable_targets[*callable as usize].is_empty() {
                    &finite_callable_targets[pc as usize][*callable as usize]
                } else {
                    &state.callable_targets[*callable as usize]
                };
                if targets.is_empty()
                    || (canonical_owned_receiver_quantity_summary(&owned_summaries, targets)
                        .is_none()
                        && canonical_borrowed_receiver_resume_deltas(a, targets).is_none())
                {
                    return Err(VerifyError::InvalidFunction(fid));
                }
                let mut operands = vec![*callable];
                operands.extend(args.iter().copied());
                transfer_pristine(&mut state, &operands)?;
            }
            Instruction::Return { src: Some(src) } if !leaf_types[*src as usize].is_empty() => {
                let actual = state.registers[*src as usize].clone();
                let exact_transport = transport_summaries[fid as usize].as_ref().map(|summary| {
                    summary
                        .iter()
                        .map(|group| state.counts[*group].map(|_| *group))
                        .collect::<Vec<_>>()
                });
                let body_derived_input = actual
                    .iter()
                    .all(|group| group.is_some_and(|group| group < group_base));
                let sole_return_owners = actual.iter().flatten().all(|group| {
                    let live = state
                        .registers
                        .iter()
                        .flatten()
                        .filter(|slot| **slot == Some(*group))
                        .count();
                    let returned = actual.iter().filter(|slot| **slot == Some(*group)).count();
                    live == returned
                });
                if exact_transport
                    .as_ref()
                    .is_some_and(|expected| actual != *expected)
                    || (exact_transport.is_none() && !body_derived_input)
                    || !sole_return_owners
                    || actual
                        .iter()
                        .flatten()
                        .any(|group| state.counts[*group] != Some(UseInterval { min: 0, max: 0 }))
                {
                    return Err(VerifyError::InvalidFunction(fid));
                }
            }
            Instruction::Leave { value: src, .. } if !leaf_types[*src as usize].is_empty() => {
                return Err(VerifyError::InvalidFunction(fid));
            }
            _ => {}
        }
        let successors = label_successors(instruction, pc, &label_states[pc as usize])
            .map_err(|_| VerifyError::InvalidFunction(fid))?;
        for (target, _) in successors {
            if target >= f.code_len {
                continue;
            }
            match &mut states[target as usize] {
                Some(previous) => {
                    if previous.handler_targets != state.handler_targets
                        || previous.shared_handler_environment != state.shared_handler_environment
                    {
                        return Err(VerifyError::StateMismatch {
                            function: fid,
                            instruction: target,
                        });
                    }
                    for register in 0..previous.registers.len() {
                        let differing_enum_variant = previous.enum_variants[register]
                            != state.enum_variants[register]
                            && matches!(type_at(a, f.register_types[register])?, Type::Enum { .. });
                        if differing_enum_variant {
                            previous.enum_variants[register] = None;
                            for (old, incoming) in previous.registers[register]
                                .iter_mut()
                                .zip(&state.registers[register])
                            {
                                match (*old, *incoming) {
                                    (left, right) if left == right => {}
                                    (Some(group), None) => {
                                        state.counts[group]
                                            .get_or_insert(UseInterval { min: 0, max: 0 });
                                    }
                                    (None, Some(group)) => {
                                        *old = Some(group);
                                        previous.counts[group]
                                            .get_or_insert(UseInterval { min: 0, max: 0 });
                                    }
                                    _ => {
                                        return Err(VerifyError::StateMismatch {
                                            function: fid,
                                            instruction: target,
                                        });
                                    }
                                }
                            }
                        } else if previous.registers[register] != state.registers[register]
                            || previous.enum_variants[register] != state.enum_variants[register]
                        {
                            return Err(VerifyError::StateMismatch {
                                function: fid,
                                instruction: target,
                            });
                        }
                    }
                    let mut changed = false;
                    for (old, incoming) in previous
                        .callable_targets
                        .iter_mut()
                        .zip(&state.callable_targets)
                    {
                        let old_len = old.len();
                        old.extend(incoming.iter().copied());
                        changed |= old.len() != old_len;
                    }
                    for (old, incoming) in previous.counts.iter_mut().zip(&state.counts) {
                        match (old.as_mut(), incoming) {
                            (Some(old), Some(incoming)) => {
                                let joined = UseInterval {
                                    min: old.min.min(incoming.min),
                                    max: old.max.max(incoming.max),
                                };
                                changed |= *old != joined;
                                *old = joined;
                            }
                            (None, None) => {}
                            _ => {
                                return Err(VerifyError::StateMismatch {
                                    function: fid,
                                    instruction: target,
                                });
                            }
                        }
                    }
                    if changed {
                        work.push_back(target);
                    }
                }
                slot @ None => {
                    *slot = Some(state.clone());
                    work.push_back(target);
                }
            }
        }
    }
    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct LabelEntry {
    slot: u32,
    result_register: u32,
    target: u32,
}

fn cleanup_registers(a: &Artifact, fid: u32, pc: u32) -> &[u32] {
    a.cleanups
        .iter()
        .find(|plan| {
            plan.function == fid && plan.first_instruction <= pc && pc < plan.end_instruction
        })
        .map_or(&[], |plan| plan.registers.as_slice())
}

fn cleanup_prefix(a: &Artifact, fid: u32, pc: u32, target: u32) -> Result<&[u32], VerifyError> {
    let source = cleanup_registers(a, fid, pc);
    let destination = cleanup_registers(a, fid, target);
    if source.len() < destination.len()
        || source[source.len() - destination.len()..] != *destination
    {
        return Err(VerifyError::StateMismatch {
            function: fid,
            instruction: pc,
        });
    }
    Ok(&source[..source.len() - destination.len()])
}

fn label_successors(
    instruction: &Instruction,
    pc: u32,
    labels: &[LabelEntry],
) -> Result<Vec<(u32, Vec<LabelEntry>)>, ()> {
    let mut next = labels.to_vec();
    Ok(match instruction {
        Instruction::LabelPush {
            slot,
            result_register,
            target,
        } => {
            next.push(LabelEntry {
                slot: *slot,
                result_register: *result_register,
                target: *target,
            });
            vec![(pc + 1, next)]
        }
        Instruction::LabelPop { slot } => {
            if next.last().map(|entry| entry.slot) != Some(*slot) {
                return Err(());
            }
            next.pop();
            vec![(pc + 1, next)]
        }
        Instruction::Leave { slot, .. } => {
            let Some(index) = next.iter().rposition(|entry| entry.slot == *slot) else {
                return Err(());
            };
            let target = next[index].target;
            next.truncate(index);
            vec![(target, next)]
        }
        Instruction::Jump { target } => vec![(*target, next)],
        Instruction::Switch {
            cases, otherwise, ..
        } => {
            let mut successors = cases
                .iter()
                .map(|case| (case.1, next.clone()))
                .collect::<Vec<_>>();
            successors.push((*otherwise, next));
            successors
        }
        Instruction::Return { .. }
        | Instruction::TailCall { .. }
        | Instruction::TailCallSelf { .. }
        | Instruction::TailCallKnownReceiver { .. }
        | Instruction::TailCallIndirect { .. }
        | Instruction::TailResume { .. }
        | Instruction::Perform { dst: None, .. }
        | Instruction::Unreachable
        | Instruction::Abort { .. } => {
            if !labels.is_empty()
                && matches!(
                    instruction,
                    Instruction::Return { .. }
                        | Instruction::TailCall { .. }
                        | Instruction::TailCallSelf { .. }
                        | Instruction::TailCallKnownReceiver { .. }
                        | Instruction::TailCallIndirect { .. }
                        | Instruction::TailResume { .. }
                )
            {
                return Err(());
            }
            vec![]
        }
        _ => vec![(pc + 1, next)],
    })
}

fn verify_labels(
    a: &Artifact,
    fid: u32,
    f: &Function,
) -> Result<Vec<Vec<LabelEntry>>, VerifyError> {
    let start = f.code_start as usize;
    let mut states: Vec<Option<Vec<LabelEntry>>> = vec![None; f.code_len as usize];
    states[0] = Some(vec![]);
    let mut work = VecDeque::from([0u32]);
    while let Some(pc) = work.pop_front() {
        let labels = states[pc as usize].clone().unwrap();
        let instruction = &a.code[start + pc as usize];
        let successors = label_successors(instruction, pc, &labels)
            .map_err(|_| VerifyError::InvalidFunction(fid))?;
        for (target, incoming) in successors {
            if target >= f.code_len {
                return Err(VerifyError::InvalidTarget {
                    function: fid,
                    instruction: pc,
                    target,
                });
            }
            match &states[target as usize] {
                Some(existing) if existing != &incoming => {
                    return Err(VerifyError::StateMismatch {
                        function: fid,
                        instruction: target,
                    });
                }
                Some(_) => {}
                None => {
                    states[target as usize] = Some(incoming);
                    work.push_back(target);
                }
            }
        }
    }
    Ok(states.into_iter().map(Option::unwrap_or_default).collect())
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct EnumFacts {
    tag_origins: Vec<Option<u32>>,
    variants: Vec<Option<u32>>,
}

fn verify_enum_dominance(
    a: &Artifact,
    fid: u32,
    f: &Function,
    label_states: &[Vec<LabelEntry>],
) -> Result<Vec<Vec<Option<u32>>>, VerifyError> {
    let start = f.code_start as usize;
    let empty = EnumFacts {
        tag_origins: vec![None; f.register_types.len()],
        variants: vec![None; f.register_types.len()],
    };
    let mut states: Vec<Option<EnumFacts>> = vec![None; f.code_len as usize];
    states[0] = Some(empty);
    let mut work = VecDeque::from([0u32]);
    while let Some(pc) = work.pop_front() {
        let mut state = states[pc as usize].clone().unwrap();
        let instruction = &a.code[start + pc as usize];
        match instruction {
            Instruction::Construct { dst, variant, .. } => state.variants[*dst as usize] = *variant,
            Instruction::Move { dst, src } => {
                state.variants[*dst as usize] = state.variants[*src as usize].take();
                state.tag_origins[*dst as usize] = state.tag_origins[*src as usize].take();
                for origin in state.tag_origins.iter_mut().flatten() {
                    if *origin == *src {
                        *origin = *dst;
                    }
                }
            }
            Instruction::Copy { dst, src } => {
                state.variants[*dst as usize] = state.variants[*src as usize];
                state.tag_origins[*dst as usize] = state.tag_origins[*src as usize];
            }
            Instruction::EnumTag { dst, src } => state.tag_origins[*dst as usize] = Some(*src),
            Instruction::Drop { register }
            | Instruction::Deconstruct { src: register }
            | Instruction::Return {
                src: Some(register),
            } => {
                state.variants[*register as usize] = None;
                state.tag_origins[*register as usize] = None;
            }
            Instruction::Leave { slot, value } => {
                let entry = label_states[pc as usize]
                    .iter()
                    .rfind(|entry| entry.slot == *slot)
                    .ok_or(VerifyError::InvalidFunction(fid))?;
                state.variants[entry.result_register as usize] =
                    state.variants[*value as usize].take();
                state.tag_origins[entry.result_register as usize] =
                    state.tag_origins[*value as usize].take();
                for register in cleanup_prefix(a, fid, pc, entry.target)? {
                    state.variants[*register as usize] = None;
                    state.tag_origins[*register as usize] = None;
                }
            }
            Instruction::Call { dst: Some(dst), .. }
            | Instruction::CallSelf { dst: Some(dst), .. }
            | Instruction::CallIndirect { dst: Some(dst), .. }
            | Instruction::Primitive { dst, .. }
            | Instruction::Const { dst, .. }
            | Instruction::MakeCallable { dst, .. }
            | Instruction::MakeHandler { dst, .. }
            | Instruction::MakeHandlerShared { dst, .. }
            | Instruction::MakeBindingPack { dst, .. }
            | Instruction::BorrowShared { dst, .. }
            | Instruction::BorrowUnique { dst, .. }
            | Instruction::ReborrowShared { dst, .. }
            | Instruction::ReborrowUnique { dst, .. }
            | Instruction::DerefCopy { dst, .. }
            | Instruction::DerefMove { dst, .. }
            | Instruction::ProjectMove { dst, .. }
            | Instruction::ProjectCopy { dst, .. }
            | Instruction::ProjectBorrowShared { dst, .. }
            | Instruction::ProjectBorrowUnique { dst, .. } => {
                state.variants[*dst as usize] = None;
                state.tag_origins[*dst as usize] = None;
            }
            Instruction::DerefStore { src, .. } => {
                state.variants[*src as usize] = None;
                state.tag_origins[*src as usize] = None;
            }
            Instruction::Handle { dst, .. } => {
                state.variants[*dst as usize] = None;
                state.tag_origins[*dst as usize] = None;
            }
            Instruction::Perform { dst: Some(dst), .. } => {
                state.variants[*dst as usize] = None;
                state.tag_origins[*dst as usize] = None;
            }
            Instruction::HostCall { dst: Some(dst), .. } => {
                state.variants[*dst as usize] = None;
                state.tag_origins[*dst as usize] = None;
            }
            _ => {}
        }
        let mut successors = Vec::new();
        match instruction {
            Instruction::Switch {
                discr,
                cases,
                otherwise,
            } => {
                let origin = state.tag_origins[*discr as usize];
                if origin.is_none() {
                    successors.extend(cases.iter().map(|case| (case.1, state.clone())));
                    successors.push((*otherwise, state));
                    continue_enum_successors(&mut states, &mut work, successors);
                    continue;
                }
                let mut seen = std::collections::BTreeSet::new();
                for &(constant, target) in cases {
                    let variant = match a.constants.get(constant as usize) {
                        Some(Constant::U32(variant)) if seen.insert(*variant) => *variant,
                        _ => {
                            return Err(VerifyError::InvalidAggregate {
                                function: fid,
                                instruction: pc,
                            });
                        }
                    };
                    let mut edge = state.clone();
                    if let Some(origin) = origin {
                        let Type::Enum { variants, .. } =
                            type_at(a, f.register_types[origin as usize])?
                        else {
                            return Err(VerifyError::InvalidAggregate {
                                function: fid,
                                instruction: pc,
                            });
                        };
                        if variant as usize >= variants.len() {
                            return Err(VerifyError::InvalidAggregate {
                                function: fid,
                                instruction: pc,
                            });
                        }
                        edge.variants[origin as usize] = Some(variant);
                    }
                    successors.push((target, edge));
                }
                let mut default = state.clone();
                if let Some(origin) = origin
                    && let Type::Enum { variants, .. } =
                        type_at(a, f.register_types[origin as usize])?
                {
                    let remaining = (0..variants.len() as u32)
                        .filter(|variant| !seen.contains(variant))
                        .collect::<Vec<_>>();
                    default.variants[origin as usize] =
                        (remaining.len() == 1).then(|| remaining[0]);
                }
                successors.push((*otherwise, default));
            }
            Instruction::Jump { target } => successors.push((*target, state)),
            Instruction::Leave { slot, .. } => {
                let entry = label_states[pc as usize]
                    .iter()
                    .rfind(|entry| entry.slot == *slot)
                    .ok_or(VerifyError::InvalidFunction(fid))?;
                successors.push((entry.target, state));
            }
            Instruction::Return { .. }
            | Instruction::TailCall { .. }
            | Instruction::TailCallSelf { .. }
            | Instruction::TailCallKnownReceiver { .. }
            | Instruction::TailCallIndirect { .. }
            | Instruction::TailResume { .. }
            | Instruction::Perform { dst: None, .. }
            | Instruction::Unreachable
            | Instruction::Abort { .. } => {}
            _ => successors.push((pc + 1, state)),
        }
        continue_enum_successors(&mut states, &mut work, successors);
    }
    Ok(states
        .into_iter()
        .map(|state| {
            state
                .unwrap_or_else(|| EnumFacts {
                    tag_origins: vec![None; f.register_types.len()],
                    variants: vec![None; f.register_types.len()],
                })
                .variants
        })
        .collect())
}

fn continue_enum_successors(
    states: &mut [Option<EnumFacts>],
    work: &mut VecDeque<u32>,
    successors: Vec<(u32, EnumFacts)>,
) {
    for (target, incoming) in successors {
        match &mut states[target as usize] {
            Some(existing) => {
                let mut changed = false;
                for (old, new) in existing.variants.iter_mut().zip(&incoming.variants) {
                    if *old != *new && old.take().is_some() {
                        changed = true;
                    }
                }
                for (old, new) in existing.tag_origins.iter_mut().zip(&incoming.tag_origins) {
                    if *old != *new && old.take().is_some() {
                        changed = true;
                    }
                }
                if changed {
                    work.push_back(target);
                }
            }
            slot @ None => {
                *slot = Some(incoming);
                work.push_back(target);
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum FieldInit {
    Whole,
    Partial(Vec<bool>),
}

fn verify_move_paths(
    a: &Artifact,
    fid: u32,
    f: &Function,
    enum_facts: &[Vec<Option<u32>>],
    label_states: &[Vec<LabelEntry>],
) -> Result<Vec<Vec<Option<FieldInit>>>, VerifyError> {
    let is_aggregate = |ty: TypeId| {
        matches!(
            a.types.get(ty as usize).map(Type::representation),
            Some(Type::Tuple { .. } | Type::Struct { .. } | Type::Enum { .. })
                | Some(Type::BindingPack { .. })
        )
    };
    let mut entry = vec![None; f.register_types.len()];
    if f.receiver_mode == Some(2) && is_aggregate(f.register_types[0]) {
        entry[0] = Some(FieldInit::Whole);
    }
    for (register, slot) in entry.iter_mut().enumerate().take(f.params.len() + 1) {
        if is_aggregate(f.register_types[register]) {
            *slot = Some(FieldInit::Whole);
        }
    }
    let mut states: Vec<Option<Vec<Option<FieldInit>>>> = vec![None; f.code_len as usize];
    states[0] = Some(entry);
    let mut work = VecDeque::from([0u32]);
    let start = f.code_start as usize;
    while let Some(pc) = work.pop_front() {
        let mut state = states[pc as usize].clone().unwrap();
        let instruction = &a.code[start + pc as usize];
        let invalid = || VerifyError::InvalidAggregate {
            function: fid,
            instruction: pc,
        };
        let complete = |state: &[Option<FieldInit>], register: u32| {
            !is_aggregate(f.register_types[register as usize])
                || matches!(state[register as usize], Some(FieldInit::Whole))
        };
        let ensure_complete = |state: &[Option<FieldInit>], register: u32| {
            if complete(state, register) {
                Ok(())
            } else {
                Err(invalid())
            }
        };
        match instruction {
            Instruction::Construct { dst, fields, .. } => {
                for field in fields {
                    state[*field as usize] = None;
                }
                state[*dst as usize] = Some(FieldInit::Whole);
            }
            Instruction::Move { dst, src } => {
                state[*dst as usize] = state[*src as usize].take();
            }
            Instruction::Copy { dst, src } => {
                ensure_complete(&state, *src)?;
                state[*dst as usize] = state[*src as usize].clone();
            }
            Instruction::DerefCopy { dst, .. } => {
                if is_aggregate(f.register_types[*dst as usize]) {
                    state[*dst as usize] = Some(FieldInit::Whole);
                }
            }
            Instruction::CallKnownReceiver { dst, args, .. } => {
                for &register in args {
                    ensure_complete(&state, register)?;
                    state[register as usize] = None;
                }
                if let Some(dst) = dst
                    && is_aggregate(f.register_types[*dst as usize])
                {
                    state[*dst as usize] = Some(FieldInit::Whole);
                }
            }
            Instruction::DerefMove { dst, .. } => {
                if is_aggregate(f.register_types[*dst as usize]) {
                    state[*dst as usize] = Some(FieldInit::Whole);
                }
            }
            Instruction::DerefStore { src, .. } => {
                ensure_complete(&state, *src)?;
                state[*src as usize] = None;
            }
            Instruction::ProjectMove { dst, src, field } => {
                if !is_aggregate(f.register_types[*src as usize]) {
                    if is_aggregate(f.register_types[*dst as usize]) {
                        state[*dst as usize] = Some(FieldInit::Whole);
                    }
                    continue_move_path_successors(
                        instruction,
                        fid,
                        pc,
                        &state,
                        &mut states,
                        &mut work,
                        &label_states[pc as usize],
                    )?;
                    continue;
                }
                let source_ty = f.register_types[*src as usize];
                if has_custom_drop(a, source_ty) {
                    return Err(invalid());
                }
                let variant = enum_facts[pc as usize][*src as usize];
                let field_types = construction_field_types(&a.types[source_ty as usize], variant)
                    .ok_or_else(invalid)?;
                if matches!(state[*src as usize], Some(FieldInit::Whole)) {
                    state[*src as usize] = Some(FieldInit::Partial(
                        field_types
                            .iter()
                            .map(|&ty| !matches!(type_at(a, ty), Ok(Type::Available { .. })))
                            .collect(),
                    ));
                }
                let Some(FieldInit::Partial(fields)) = &mut state[*src as usize] else {
                    return Err(invalid());
                };
                let initialized = fields.get_mut(*field as usize).ok_or_else(invalid)?;
                if !*initialized {
                    return Err(invalid());
                }
                *initialized = false;
                if is_aggregate(f.register_types[*dst as usize]) {
                    state[*dst as usize] = Some(FieldInit::Whole);
                }
            }
            Instruction::Deconstruct { src } => {
                let source_ty = f.register_types[*src as usize];
                if !matches!(
                    type_at(a, source_ty),
                    Ok(Type::Tuple { .. } | Type::Struct { .. } | Type::Enum { .. })
                ) || a.drop_glue.iter().any(|glue| glue.ty == source_ty)
                {
                    return Err(invalid());
                }
                let variant = enum_facts[pc as usize][*src as usize];
                let field_types = construction_field_types(&a.types[source_ty as usize], variant)
                    .ok_or_else(invalid)?;
                let empty_whole = field_types
                    .iter()
                    .all(|&ty| matches!(type_at(a, ty), Ok(Type::Available { .. })));
                let empty = match &state[*src as usize] {
                    Some(FieldInit::Whole) => empty_whole,
                    Some(FieldInit::Partial(fields)) => fields.iter().all(|field| !field),
                    None => false,
                };
                if !empty {
                    return Err(invalid());
                }
                state[*src as usize] = None;
            }
            Instruction::ProjectCopy { dst, src, field } => {
                if !is_aggregate(f.register_types[*src as usize]) {
                    if is_aggregate(f.register_types[*dst as usize]) {
                        state[*dst as usize] = Some(FieldInit::Whole);
                    }
                    continue_move_path_successors(
                        instruction,
                        fid,
                        pc,
                        &state,
                        &mut states,
                        &mut work,
                        &label_states[pc as usize],
                    )?;
                    continue;
                }
                match &state[*src as usize] {
                    Some(FieldInit::Whole) => {}
                    Some(FieldInit::Partial(fields))
                        if fields.get(*field as usize) == Some(&true) => {}
                    _ => return Err(invalid()),
                }
                if is_aggregate(f.register_types[*dst as usize]) {
                    state[*dst as usize] = Some(FieldInit::Whole);
                }
            }
            Instruction::ProjectBorrowShared { src, field, .. }
            | Instruction::ProjectBorrowUnique { src, field, .. } => {
                if !is_aggregate(f.register_types[*src as usize]) {
                    // A projected reference was proven initialized when its parent loan was made.
                    continue_move_path_successors(
                        instruction,
                        fid,
                        pc,
                        &state,
                        &mut states,
                        &mut work,
                        &label_states[pc as usize],
                    )?;
                    continue;
                }
                match &state[*src as usize] {
                    Some(FieldInit::Whole) => {}
                    Some(FieldInit::Partial(fields))
                        if fields.get(*field as usize) == Some(&true) => {}
                    _ => return Err(invalid()),
                }
            }
            Instruction::Drop { register }
            | Instruction::Return {
                src: Some(register),
            } => {
                if matches!(instruction, Instruction::Return { .. })
                    || has_custom_drop(a, f.register_types[*register as usize])
                {
                    ensure_complete(&state, *register)?;
                }
                state[*register as usize] = None;
            }
            Instruction::Call { dst, args, .. } => {
                for &register in args {
                    ensure_complete(&state, register)?;
                    state[register as usize] = None;
                }
                if let Some(dst) = dst
                    && is_aggregate(f.register_types[*dst as usize])
                {
                    state[*dst as usize] = Some(FieldInit::Whole);
                }
            }
            Instruction::MakeCallable { dst, captures, .. } => {
                for &register in captures {
                    ensure_complete(&state, register)?;
                    state[register as usize] = None;
                }
                if is_aggregate(f.register_types[*dst as usize]) {
                    state[*dst as usize] = Some(FieldInit::Whole);
                }
            }
            Instruction::MakeHandler { clauses, .. } => {
                for &register in clauses {
                    ensure_complete(&state, register)?;
                    state[register as usize] = None;
                }
            }
            Instruction::MakeHandlerShared { dst, captures, .. } => {
                for &register in captures {
                    ensure_complete(&state, register)?;
                    state[register as usize] = None;
                }
                if is_aggregate(f.register_types[*dst as usize]) {
                    state[*dst as usize] = Some(FieldInit::Whole);
                }
            }
            Instruction::MakeBindingPack { dst, payloads, .. } => {
                for &register in payloads {
                    ensure_complete(&state, register)?;
                    state[register as usize] = None;
                }
                state[*dst as usize] = Some(FieldInit::Whole);
            }
            Instruction::Handle {
                dst,
                handler,
                body,
                args,
            } => {
                for register in std::iter::once(handler)
                    .chain(std::iter::once(body))
                    .chain(args.iter())
                {
                    ensure_complete(&state, *register)?;
                    state[*register as usize] = None;
                }
                if is_aggregate(f.register_types[*dst as usize]) {
                    state[*dst as usize] = Some(FieldInit::Whole);
                }
            }
            Instruction::Perform { dst, payloads, .. } => {
                for &register in payloads {
                    ensure_complete(&state, register)?;
                    state[register as usize] = None;
                }
                if let Some(dst) = dst
                    && is_aggregate(f.register_types[*dst as usize])
                {
                    state[*dst as usize] = Some(FieldInit::Whole);
                }
            }
            Instruction::HostCall { dst, args, .. } => {
                for &register in args {
                    ensure_complete(&state, register)?;
                    state[register as usize] = None;
                }
                if let Some(dst) = dst
                    && is_aggregate(f.register_types[*dst as usize])
                {
                    state[*dst as usize] = Some(FieldInit::Whole);
                }
            }
            Instruction::Resume {
                dst,
                resumption,
                value,
                receiver_mode,
            } => {
                if *receiver_mode == 2 {
                    ensure_complete(&state, *resumption)?;
                    state[*resumption as usize] = None;
                }
                ensure_complete(&state, *value)?;
                state[*value as usize] = None;
                if is_aggregate(f.register_types[*dst as usize]) {
                    state[*dst as usize] = Some(FieldInit::Whole);
                }
            }
            Instruction::TailResume {
                resumption,
                value,
                receiver_mode,
            } => {
                if *receiver_mode == 2 {
                    ensure_complete(&state, *resumption)?;
                    state[*resumption as usize] = None;
                }
                ensure_complete(&state, *value)?;
                state[*value as usize] = None;
            }
            Instruction::Cancel { dst, resumption } => {
                ensure_complete(&state, *resumption)?;
                state[*resumption as usize] = None;
                if is_aggregate(f.register_types[*dst as usize]) {
                    state[*dst as usize] = Some(FieldInit::Whole);
                }
            }
            Instruction::Leave { slot, value } => {
                let entry = label_states[pc as usize]
                    .iter()
                    .rfind(|entry| entry.slot == *slot)
                    .ok_or(VerifyError::InvalidFunction(fid))?;
                let protected = state[*value as usize].take();
                for register in cleanup_prefix(a, fid, pc, entry.target)? {
                    state[*register as usize] = None;
                }
                state[entry.result_register as usize] = protected;
            }
            Instruction::CallIndirect {
                dst,
                callable,
                receiver_mode,
                args,
            } => {
                if *receiver_mode == 2 {
                    ensure_complete(&state, *callable)?;
                    state[*callable as usize] = None;
                }
                for &register in args {
                    ensure_complete(&state, register)?;
                    state[register as usize] = None;
                }
                if let Some(dst) = dst
                    && is_aggregate(f.register_types[*dst as usize])
                {
                    state[*dst as usize] = Some(FieldInit::Whole);
                }
            }
            Instruction::TailCall { args, .. } => {
                for &register in args {
                    ensure_complete(&state, register)?;
                    state[register as usize] = None;
                }
            }
            Instruction::TailCallSelf { args } => {
                ensure_complete(&state, 0)?;
                state[0] = None;
                for &register in args {
                    ensure_complete(&state, register)?;
                    state[register as usize] = None;
                }
            }
            Instruction::TailCallKnownReceiver { args, .. } => {
                for &register in args {
                    ensure_complete(&state, register)?;
                    state[register as usize] = None;
                }
            }
            Instruction::TailCallIndirect { callable, args, .. } => {
                ensure_complete(&state, *callable)?;
                state[*callable as usize] = None;
                for &register in args {
                    ensure_complete(&state, register)?;
                    state[register as usize] = None;
                }
            }
            Instruction::Primitive { dst, args, .. } => {
                for &register in args {
                    ensure_complete(&state, register)?;
                    state[register as usize] = None;
                }
                if is_aggregate(f.register_types[*dst as usize]) {
                    state[*dst as usize] = Some(FieldInit::Whole);
                }
            }
            _ => {}
        }
        continue_move_path_successors(
            instruction,
            fid,
            pc,
            &state,
            &mut states,
            &mut work,
            &label_states[pc as usize],
        )?;
    }
    Ok(states
        .into_iter()
        .map(|state| state.unwrap_or_else(|| vec![None; f.register_types.len()]))
        .collect())
}

fn continue_move_path_successors(
    instruction: &Instruction,
    fid: u32,
    pc: u32,
    state: &[Option<FieldInit>],
    states: &mut [Option<Vec<Option<FieldInit>>>],
    work: &mut VecDeque<u32>,
    labels: &[LabelEntry],
) -> Result<(), VerifyError> {
    let successors: Vec<u32> = match instruction {
        Instruction::Jump { target } => vec![*target],
        Instruction::Leave { slot, .. } => vec![
            labels
                .iter()
                .rfind(|entry| entry.slot == *slot)
                .ok_or(VerifyError::InvalidFunction(fid))?
                .target,
        ],
        Instruction::Switch {
            cases, otherwise, ..
        } => cases
            .iter()
            .map(|case| case.1)
            .chain(std::iter::once(*otherwise))
            .collect(),
        Instruction::Return { .. }
        | Instruction::TailCall { .. }
        | Instruction::TailCallSelf { .. }
        | Instruction::TailCallKnownReceiver { .. }
        | Instruction::TailCallIndirect { .. }
        | Instruction::TailResume { .. }
        | Instruction::Perform { dst: None, .. }
        | Instruction::Unreachable
        | Instruction::Abort { .. } => {
            vec![]
        }
        _ => vec![pc + 1],
    };
    for successor in successors {
        match &mut states[successor as usize] {
            Some(existing) => {
                let mut changed = false;
                for (old, incoming) in existing.iter_mut().zip(state) {
                    if old == incoming {
                        continue;
                    }
                    let joined = match (&*old, incoming) {
                        (Some(FieldInit::Whole), Some(FieldInit::Partial(fields)))
                        | (Some(FieldInit::Partial(fields)), Some(FieldInit::Whole)) => {
                            Some(FieldInit::Partial(fields.clone()))
                        }
                        (Some(FieldInit::Partial(left)), Some(FieldInit::Partial(right)))
                            if left.len() == right.len() =>
                        {
                            Some(FieldInit::Partial(
                                left.iter()
                                    .zip(right)
                                    .map(|(left, right)| *left && *right)
                                    .collect(),
                            ))
                        }
                        _ => {
                            return Err(VerifyError::StateMismatch {
                                function: fid,
                                instruction: successor,
                            });
                        }
                    };
                    if *old != joined {
                        *old = joined;
                        changed = true;
                    }
                }
                if changed && !work.contains(&successor) {
                    work.push_back(successor);
                }
            }
            None => {
                states[successor as usize] = Some(state.to_vec());
                work.push_back(successor);
            }
        }
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ReferenceOrigin {
    Parameter(usize),
    Receiver,
    Local,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum CarrierOrigin {
    Parameter { parameter: usize, path: Vec<u32> },
    Receiver { path: Vec<u32> },
    Local,
}

type CarrierOrigins = Vec<(Vec<u32>, CarrierOrigin)>;
type CallableTargets = std::collections::BTreeSet<u32>;

/// Compute the finite set of callable producers at every instruction boundary.
/// An empty set means that no body-derived target is known. Branch joins union
/// their alternatives instead of discarding useful information merely because
/// more than one target can reach the call. This small summary is rebuilt while
/// verifying and is not kept in [`VerifiedArtifact`].
fn callable_targets_at_pcs(
    a: &Artifact,
    fid: u32,
    f: &Function,
    label_states: &[Vec<LabelEntry>],
) -> Result<Vec<Vec<CallableTargets>>, VerifyError> {
    let mut entries = vec![None; f.code_len as usize];
    let mut entry = vec![CallableTargets::new(); f.register_types.len()];
    for (register, ty) in f
        .register_types
        .iter()
        .copied()
        .enumerate()
        .take(f.params.len() + 1)
    {
        if matches!(type_at(a, ty)?, Type::Callable { .. }) {
            entry[register] = callable_type_producers(a, ty);
        }
    }
    entries[0] = Some(entry);
    let mut work = VecDeque::from([0u32]);
    while let Some(pc) = work.pop_front() {
        let mut state = entries[pc as usize].clone().unwrap();
        let instruction = &a.code[f.code_start as usize + pc as usize];
        match instruction {
            Instruction::Move { dst, src } => {
                state[*dst as usize] = std::mem::take(&mut state[*src as usize]);
            }
            Instruction::Copy { dst, src } => {
                state[*dst as usize] = state[*src as usize].clone();
            }
            Instruction::Construct { dst, fields, .. }
            | Instruction::MakeBindingPack {
                dst,
                payloads: fields,
                ..
            } => {
                let targets = fields
                    .iter()
                    .flat_map(|field| state[*field as usize].iter().copied())
                    .collect::<std::collections::BTreeSet<_>>();
                state[*dst as usize] = targets;
                for field in fields {
                    state[*field as usize].clear();
                }
            }
            Instruction::ProjectMove { dst, src, .. } => {
                state[*dst as usize] = std::mem::take(&mut state[*src as usize]);
            }
            Instruction::ProjectCopy { dst, src, .. } => {
                state[*dst as usize] = state[*src as usize].clone();
            }
            Instruction::MakeCallable { dst, function, .. } => {
                state[*dst as usize] = CallableTargets::from([*function]);
            }
            Instruction::Drop { register } | Instruction::Deconstruct { src: register } => {
                state[*register as usize].clear();
            }
            _ => {
                if let Some(destination) = instruction_destination(instruction) {
                    state[destination as usize].clear();
                }
            }
        }
        let successors = match instruction {
            Instruction::Jump { target } => vec![*target],
            Instruction::Switch {
                cases, otherwise, ..
            } => cases
                .iter()
                .map(|case| case.1)
                .chain(std::iter::once(*otherwise))
                .collect(),
            Instruction::Leave { slot, .. } => vec![
                label_states[pc as usize]
                    .iter()
                    .rfind(|entry| entry.slot == *slot)
                    .ok_or(VerifyError::InvalidFunction(fid))?
                    .target,
            ],
            Instruction::Return { .. }
            | Instruction::TailCall { .. }
            | Instruction::TailCallSelf { .. }
            | Instruction::TailCallKnownReceiver { .. }
            | Instruction::TailCallIndirect { .. }
            | Instruction::TailResume { .. }
            | Instruction::Perform { dst: None, .. }
            | Instruction::Unreachable
            | Instruction::Abort { .. } => vec![],
            _ => vec![pc + 1],
        };
        for successor in successors {
            let entry = entries
                .get_mut(successor as usize)
                .ok_or(VerifyError::InvalidFunction(fid))?;
            match entry {
                None => {
                    *entry = Some(state.clone());
                    work.push_back(successor);
                }
                Some(existing) => {
                    let mut changed = false;
                    for (old, incoming) in existing.iter_mut().zip(&state) {
                        let old_len = old.len();
                        old.extend(incoming);
                        changed |= old.len() != old_len;
                    }
                    if changed {
                        work.push_back(successor);
                    }
                }
            }
        }
    }
    Ok(entries
        .into_iter()
        .map(|entry| entry.unwrap_or_else(|| vec![CallableTargets::new(); f.register_types.len()]))
        .collect())
}

fn canonical_callable_carrier_contract(
    a: &Artifact,
    targets: &CallableTargets,
    visiting: &mut Vec<u32>,
) -> Result<CarrierOrigins, VerifyError> {
    canonical_callable_carrier_contract_with(
        a,
        targets,
        visiting,
        &mut std::collections::BTreeMap::new(),
    )
}

fn canonical_callable_carrier_contract_with(
    a: &Artifact,
    targets: &CallableTargets,
    visiting: &mut Vec<u32>,
    provisional: &mut std::collections::BTreeMap<u32, CarrierOrigins>,
) -> Result<CarrierOrigins, VerifyError> {
    let mut contracts = targets.iter().map(|target| {
        aggregate_reference_return_origins_with(a, *target, visiting, provisional)
            .map_err(|_| VerifyError::InvalidFunction(*target))
    });
    let first = contracts
        .next()
        .ok_or(VerifyError::InvalidFunction(u32::MAX))??;
    for contract in contracts {
        if contract? != first {
            return Err(VerifyError::InvalidFunction(u32::MAX));
        }
    }
    Ok(first)
}

fn canonical_callable_reference_contract(
    a: &Artifact,
    targets: &CallableTargets,
    visiting: &mut Vec<u32>,
) -> Result<Option<ReferenceOrigin>, VerifyError> {
    let mut contracts = targets
        .iter()
        .map(|target| reference_return_parameter(a, *target, visiting));
    let first = contracts
        .next()
        .ok_or(VerifyError::InvalidFunction(u32::MAX))??;
    for contract in contracts {
        if contract? != first {
            return Err(VerifyError::InvalidFunction(u32::MAX));
        }
    }
    Ok(first)
}

fn instruction_destination(instruction: &Instruction) -> Option<u32> {
    match instruction {
        Instruction::Const { dst, .. }
        | Instruction::Move { dst, .. }
        | Instruction::Copy { dst, .. }
        | Instruction::BorrowShared { dst, .. }
        | Instruction::BorrowUnique { dst, .. }
        | Instruction::DerefCopy { dst, .. }
        | Instruction::DerefMove { dst, .. }
        | Instruction::Construct { dst, .. }
        | Instruction::ProjectMove { dst, .. }
        | Instruction::ProjectCopy { dst, .. }
        | Instruction::ReborrowShared { dst, .. }
        | Instruction::ReborrowUnique { dst, .. }
        | Instruction::ProjectBorrowShared { dst, .. }
        | Instruction::ProjectBorrowUnique { dst, .. }
        | Instruction::EnumTag { dst, .. }
        | Instruction::Primitive { dst, .. }
        | Instruction::MakeCallable { dst, .. }
        | Instruction::MakeHandler { dst, .. }
        | Instruction::MakeHandlerShared { dst, .. }
        | Instruction::MakeBindingPack { dst, .. }
        | Instruction::Resume { dst, .. }
        | Instruction::Cancel { dst, .. } => Some(*dst),
        Instruction::Call { dst, .. }
        | Instruction::CallSelf { dst, .. }
        | Instruction::CallKnownReceiver { dst, .. }
        | Instruction::CallIndirect { dst, .. }
        | Instruction::HostCall { dst, .. }
        | Instruction::Perform { dst, .. } => *dst,
        _ => None,
    }
}

/// Infer a leaf-for-leaf return contract for finite reference-bearing aggregates.
/// This is deliberately body-derived, so no lifetime metadata enters the wire format.
fn aggregate_reference_return_origins(
    a: &Artifact,
    fid: u32,
    visiting: &mut Vec<u32>,
) -> Result<CarrierOrigins, VerifyError> {
    aggregate_reference_return_origins_with(
        a,
        fid,
        visiting,
        &mut std::collections::BTreeMap::new(),
    )
}

fn aggregate_reference_return_origins_with(
    a: &Artifact,
    fid: u32,
    visiting: &mut Vec<u32>,
    provisional: &mut std::collections::BTreeMap<u32, CarrierOrigins>,
) -> Result<CarrierOrigins, VerifyError> {
    if visiting.contains(&fid) {
        return provisional
            .get(&fid)
            .cloned()
            .ok_or(VerifyError::InvalidFunction(fid));
    }
    let function = a
        .functions
        .get(fid as usize)
        .ok_or(VerifyError::InvalidFunction(fid))?;
    let result_leaves = reference_leaves(a, function.return_type);
    if result_leaves.is_empty() {
        return Err(VerifyError::InvalidFunction(fid));
    }
    fn reaches(
        a: &Artifact,
        start: u32,
        current: u32,
        seen: &mut std::collections::BTreeSet<u32>,
    ) -> bool {
        if !seen.insert(current) {
            return false;
        }
        let Some(function) = a.functions.get(current as usize) else {
            return false;
        };
        let Ok(code) = function_code(a, function) else {
            return false;
        };
        code.iter().any(|instruction| {
            let target = match instruction {
                Instruction::Call { function, .. }
                | Instruction::TailCall { function, .. }
                | Instruction::CallKnownReceiver { function, .. }
                | Instruction::TailCallKnownReceiver { function, .. } => Some(*function),
                Instruction::CallSelf { .. } | Instruction::TailCallSelf { .. } => Some(current),
                _ => None,
            };
            target.is_some_and(|target| target == start || reaches(a, start, target, seen))
        })
    }
    let recursive = reaches(a, fid, fid, &mut std::collections::BTreeSet::new());
    let result_count = result_leaves.len();
    let mut sources = Vec::new();
    if function.receiver_mode.is_some() {
        let leaves = reference_leaves(a, function.register_types[0]);
        let whole_carrier = leaves.len() == result_count;
        sources.extend(
            leaves
                .into_iter()
                .map(|(path, unique)| (CarrierOrigin::Receiver { path }, unique, whole_carrier)),
        );
    }
    for (parameter, ty) in function.params.iter().enumerate() {
        let leaves = reference_leaves(a, *ty);
        let whole_carrier = leaves.len() == result_count;
        sources.extend(leaves.into_iter().map(|(path, unique)| {
            (
                CarrierOrigin::Parameter { parameter, path },
                unique,
                whole_carrier,
            )
        }));
        if let Some(element) = array_element_type(a, *ty) {
            let element_leaves = reference_leaves(a, element);
            for (path, unique) in &element_leaves {
                sources.push((
                    CarrierOrigin::Parameter {
                        parameter,
                        path: array_last_slot_path(path.clone()),
                    },
                    *unique,
                    false,
                ));
            }
            for index in a.constants.iter().filter_map(|constant| match constant {
                Constant::U8(value) => Some(u64::from(*value)),
                Constant::U16(value) => Some(u64::from(*value)),
                Constant::U32(value) => Some(u64::from(*value)),
                Constant::U64(value) | Constant::Usize(value) => Some(*value),
                _ => None,
            }) {
                for (path, unique) in &element_leaves {
                    if let Some(path) = array_slot_path(index, path.clone()) {
                        sources.push((
                            CarrierOrigin::Parameter { parameter, path },
                            *unique,
                            false,
                        ));
                    }
                }
            }
        }
    }
    const MAX_PROVISIONAL_CONTRACTS: usize = 256;
    let mut candidates = vec![CarrierOrigins::new()];
    for (result_path, result_unique) in result_leaves {
        let compatible = sources
            .iter()
            .filter(|(origin, source_unique, whole_carrier)| {
                *source_unique == result_unique
                    && (!recursive
                        || !*whole_carrier
                        || match origin {
                            CarrierOrigin::Parameter { path, .. }
                            | CarrierOrigin::Receiver { path } => path == &result_path,
                            CarrierOrigin::Local => false,
                        })
            })
            .map(|(origin, _, _)| origin.clone())
            .collect::<Vec<_>>();
        if compatible.is_empty()
            || candidates
                .len()
                .checked_mul(compatible.len())
                .is_none_or(|count| count > MAX_PROVISIONAL_CONTRACTS)
        {
            return Err(VerifyError::InvalidFunction(fid));
        }
        candidates = candidates
            .into_iter()
            .flat_map(|candidate| {
                let result_path = result_path.clone();
                compatible.iter().cloned().map(move |origin| {
                    let mut candidate = candidate.clone();
                    candidate.push((result_path.clone(), origin));
                    candidate
                })
            })
            .collect();
    }
    let mut fixed_points = Vec::new();
    for candidate in candidates {
        provisional.insert(fid, candidate.clone());
        visiting.push(fid);
        let result = aggregate_reference_return_origins_inner(a, fid, visiting, provisional);
        visiting.pop();
        provisional.remove(&fid);
        if let Ok(result) = result
            && result == candidate
            && !fixed_points.contains(&result)
        {
            fixed_points.push(result);
        }
    }
    if fixed_points.len() == 1 {
        Ok(fixed_points.pop().unwrap())
    } else {
        Err(VerifyError::InvalidFunction(fid))
    }
}

fn aggregate_reference_return_origins_inner(
    a: &Artifact,
    fid: u32,
    visiting: &mut Vec<u32>,
    provisional: &mut std::collections::BTreeMap<u32, CarrierOrigins>,
) -> Result<CarrierOrigins, VerifyError> {
    let f = a
        .functions
        .get(fid as usize)
        .ok_or(VerifyError::InvalidFunction(fid))?;
    let label_states = verify_labels(a, fid, f)?;
    let callable_targets = callable_targets_at_pcs(a, fid, f, &label_states)?;
    let array_roots = array_roots_at_pcs(a, fid, f, &label_states)?;
    let constants = constant_u64_registers_at_pcs(a, fid, f, &label_states)?;
    let mut entry = vec![CarrierOrigins::new(); f.register_types.len()];
    for (parameter, ty) in f.params.iter().enumerate() {
        entry[parameter + 1] = reference_leaves(a, *ty)
            .into_iter()
            .map(|(path, _)| (path.clone(), CarrierOrigin::Parameter { parameter, path }))
            .collect();
    }
    if f.receiver_mode.is_some() {
        entry[0] = reference_leaves(a, f.register_types[0])
            .into_iter()
            .map(|(path, _)| (path.clone(), CarrierOrigin::Receiver { path }))
            .collect();
    }
    let mut states = vec![None; f.code_len as usize];
    states[0] = Some(entry);
    let mut work = VecDeque::from([0u32]);
    let mut returned = None::<CarrierOrigins>;
    let start = f.code_start as usize;
    while let Some(pc) = work.pop_front() {
        let mut state = states[pc as usize].clone().unwrap();
        let instruction = &a.code[start + pc as usize];
        match instruction {
            Instruction::Move { dst, src } => {
                state[*dst as usize] = std::mem::take(&mut state[*src as usize]);
            }
            Instruction::Copy { dst, src } => state[*dst as usize] = state[*src as usize].clone(),
            Instruction::Construct {
                dst,
                ty,
                variant,
                fields,
            } => {
                let field_indices = construction_field_types(&a.types[*ty as usize], *variant)
                    .ok_or(VerifyError::InvalidFunction(fid))?
                    .into_iter()
                    .enumerate()
                    .filter_map(|(field, ty)| {
                        (!matches!(type_at(a, ty), Ok(Type::Available { .. })))
                            .then_some(field as u32)
                    });
                let mut origins = Vec::new();
                for (&field_register, field) in fields.iter().zip(field_indices) {
                    origins.extend(state[field_register as usize].drain(..).map(
                        |(mut path, origin)| {
                            path.insert(0, field);
                            (path, origin)
                        },
                    ));
                }
                origins.sort_by(|left, right| left.0.cmp(&right.0));
                state[*dst as usize] = origins;
            }
            Instruction::MakeCallable { dst, captures, .. }
            | Instruction::MakeHandlerShared { dst, captures, .. } => {
                let sources = captures
                    .iter()
                    .flat_map(|capture| state[*capture as usize].clone())
                    .collect::<CarrierOrigins>();
                state[*dst as usize] =
                    remap_carrier_origins(a, f.register_types[*dst as usize], sources, fid)?;
                for capture in captures {
                    state[*capture as usize].clear();
                }
            }
            Instruction::MakeHandler { dst, clauses, .. } => {
                let sources = clauses
                    .iter()
                    .flat_map(|clause| state[*clause as usize].clone())
                    .collect::<CarrierOrigins>();
                state[*dst as usize] =
                    remap_carrier_origins(a, f.register_types[*dst as usize], sources, fid)?;
                for clause in clauses {
                    state[*clause as usize].clear();
                }
            }
            Instruction::ProjectMove { dst, src, field } => {
                let mut projected = Vec::new();
                state[*src as usize].retain(|(path, origin)| {
                    if path.first() == Some(field) {
                        projected.push((path[1..].to_vec(), origin.clone()));
                        false
                    } else {
                        true
                    }
                });
                state[*dst as usize] = projected;
            }
            Instruction::ProjectCopy { dst, src, field } => {
                let mut projected = state[*src as usize]
                    .iter()
                    .filter(|(path, _)| path.first() == Some(field))
                    .map(|(path, origin)| (path[1..].to_vec(), origin.clone()))
                    .collect::<CarrierOrigins>();
                if projected.is_empty()
                    && *src == 0
                    && matches!(f.receiver_mode, Some(0 | 1))
                    && let [(carrier_path, CarrierOrigin::Receiver { path: root_path })] =
                        state[*src as usize].as_slice()
                    && carrier_path.is_empty()
                {
                    projected = reference_leaves(a, f.register_types[*dst as usize])
                        .into_iter()
                        .map(|(result_path, _)| {
                            let mut source_path = root_path.clone();
                            source_path.push(*field);
                            source_path.extend(result_path.iter().copied());
                            (result_path, CarrierOrigin::Receiver { path: source_path })
                        })
                        .collect();
                }
                state[*dst as usize] = projected;
            }
            Instruction::BorrowShared { dst, .. } | Instruction::BorrowUnique { dst, .. } => {
                state[*dst as usize] = vec![(vec![], CarrierOrigin::Local)];
            }
            Instruction::ReborrowShared { dst, src }
            | Instruction::ReborrowUnique { dst, src }
            | Instruction::ProjectBorrowShared { dst, src, .. }
            | Instruction::ProjectBorrowUnique { dst, src, .. } => {
                state[*dst as usize] = state[*src as usize].clone();
            }
            Instruction::Primitive { dst, op, args } => {
                let root = args
                    .first()
                    .and_then(|register| array_roots[pc as usize][*register as usize]);
                let exact = || {
                    args.get(1)
                        .and_then(|register| constants[pc as usize][*register as usize])
                };
                let source_for = |root: ArrayRoot,
                                  index: Option<u64>,
                                  state: &[CarrierOrigins]|
                 -> Result<CarrierOrigins, VerifyError> {
                    match root {
                        ArrayRoot::Local(owner) => {
                            let mut origins = state[owner as usize]
                                .iter()
                                .filter_map(|(path, origin)| {
                                    let (candidate, element_path) = split_array_slot_path(path)?;
                                    (index == Some(candidate))
                                        .then(|| (element_path.to_vec(), origin.clone()))
                                })
                                .collect::<CarrierOrigins>();
                            origins.sort_by(|left, right| left.0.cmp(&right.0));
                            (!origins.is_empty())
                                .then_some(origins)
                                .ok_or(VerifyError::InvalidFunction(fid))
                        }
                        ArrayRoot::Parameter(parameter) => reference_leaves(
                            a,
                            array_element_type(a, f.params[parameter])
                                .ok_or(VerifyError::InvalidFunction(fid))?,
                        )
                        .into_iter()
                        .map(|(element_path, _)| {
                            let path = match index {
                                Some(index) => array_slot_path(index, element_path.clone())
                                    .ok_or(VerifyError::InvalidFunction(fid))?,
                                None => array_last_slot_path(element_path.clone()),
                            };
                            Ok((element_path, CarrierOrigin::Parameter { parameter, path }))
                        })
                        .collect(),
                    }
                };
                match op {
                    Primitive::ArraySetMove | Primitive::ArrayPushMove => {
                        if let Some(ArrayRoot::Local(owner)) = root {
                            let item = *args
                                .get(if matches!(op, Primitive::ArraySetMove) {
                                    2
                                } else {
                                    1
                                })
                                .ok_or(VerifyError::InvalidFunction(fid))?;
                            let index = if matches!(op, Primitive::ArraySetMove) {
                                exact().ok_or(VerifyError::InvalidFunction(fid))?
                            } else {
                                state[owner as usize]
                                    .iter()
                                    .filter_map(|(path, _)| {
                                        split_array_slot_path(path).map(|slot| slot.0)
                                    })
                                    .max()
                                    .map_or(Some(0), |index| index.checked_add(1))
                                    .ok_or(VerifyError::InvalidFunction(fid))?
                            };
                            let carried = std::mem::take(&mut state[item as usize]);
                            for (path, origin) in carried {
                                state[owner as usize].push((
                                    array_slot_path(index, path)
                                        .ok_or(VerifyError::InvalidFunction(fid))?,
                                    origin,
                                ));
                            }
                        }
                    }
                    Primitive::ArrayGetCopy | Primitive::ArrayGetMove => {
                        if !reference_leaves(a, f.register_types[*dst as usize]).is_empty() {
                            state[*dst as usize] = source_for(
                                root.ok_or(VerifyError::InvalidFunction(fid))?,
                                Some(exact().ok_or(VerifyError::InvalidFunction(fid))?),
                                &state,
                            )?;
                        }
                    }
                    Primitive::ArrayPopMove
                        if !reference_leaves(a, f.register_types[*dst as usize]).is_empty() =>
                    {
                        let root = root.ok_or(VerifyError::InvalidFunction(fid))?;
                        let index = match root {
                            ArrayRoot::Local(owner) => state[owner as usize]
                                .iter()
                                .filter_map(|(path, _)| {
                                    split_array_slot_path(path).map(|slot| slot.0)
                                })
                                .max(),
                            ArrayRoot::Parameter(_) => None,
                        };
                        state[*dst as usize] = source_for(root, index, &state)?;
                    }
                    _ => {}
                }
            }
            Instruction::Call {
                dst: Some(dst),
                function,
                args,
            } if !reference_leaves(a, f.register_types[*dst as usize]).is_empty() => {
                let contract =
                    aggregate_reference_return_origins_with(a, *function, visiting, provisional)?;
                let mut origins = Vec::new();
                for (result_path, origin) in contract {
                    let CarrierOrigin::Parameter { parameter, path } = origin else {
                        return Err(VerifyError::InvalidFunction(*function));
                    };
                    let argument = *args
                        .get(parameter)
                        .ok_or(VerifyError::InvalidFunction(*function))?;
                    let source = state[argument as usize]
                        .iter()
                        .find(|(candidate, _)| candidate == &path)
                        .map(|(_, origin)| origin.clone())
                        .ok_or(VerifyError::InvalidFunction(*function))?;
                    origins.push((result_path, source));
                }
                state[*dst as usize] = origins;
            }
            Instruction::CallIndirect {
                dst: Some(dst),
                callable,
                args,
                ..
            } if !reference_leaves(a, f.register_types[*dst as usize]).is_empty() => {
                let targets = &callable_targets[pc as usize][*callable as usize];
                let contract =
                    canonical_callable_carrier_contract_with(a, targets, visiting, provisional)
                        .map_err(|_| VerifyError::InvalidFunction(fid))?;
                state[*dst as usize] =
                    instantiate_carrier_contract(&contract, Some(*callable), args, &state, fid)?;
            }
            Instruction::Perform {
                dst: Some(dst),
                payloads,
                ..
            } if !reference_leaves(a, f.register_types[*dst as usize]).is_empty() => {
                let source = unique_reference_carrier(&state, payloads)
                    .ok_or(VerifyError::InvalidFunction(fid))?;
                state[*dst as usize] =
                    remap_carrier_origins(a, f.register_types[*dst as usize], source, fid)?;
                for payload in payloads {
                    state[*payload as usize].clear();
                }
            }
            Instruction::Resume {
                dst,
                value,
                resumption,
                receiver_mode,
            } if !reference_leaves(a, f.register_types[*dst as usize]).is_empty() => {
                state[*dst as usize] = remap_carrier_origins(
                    a,
                    f.register_types[*dst as usize],
                    state[*value as usize].clone(),
                    fid,
                )?;
                state[*value as usize].clear();
                if *receiver_mode == 2 {
                    state[*resumption as usize].clear();
                }
            }
            Instruction::TailResume {
                value,
                resumption,
                receiver_mode,
            } => {
                state[*value as usize].clear();
                if *receiver_mode == 2 {
                    state[*resumption as usize].clear();
                }
            }
            Instruction::Handle {
                dst,
                handler,
                body,
                args,
            } if !reference_leaves(a, f.register_types[*dst as usize]).is_empty() => {
                let inputs = std::iter::once(handler)
                    .chain(std::iter::once(body))
                    .chain(args.iter())
                    .copied()
                    .collect::<Vec<_>>();
                let sources = inputs
                    .iter()
                    .flat_map(|input| state[*input as usize].clone())
                    .collect::<CarrierOrigins>();
                state[*dst as usize] =
                    remap_carrier_origins(a, f.register_types[*dst as usize], sources, fid)?;
                for input in inputs {
                    state[input as usize].clear();
                }
            }
            Instruction::TailCall { function, args }
                if !reference_leaves(a, f.return_type).is_empty() =>
            {
                let contract =
                    aggregate_reference_return_origins_with(a, *function, visiting, provisional)?;
                let origins =
                    instantiate_carrier_contract(&contract, None, args, &state, *function)?;
                record_carrier_return(fid, origins, &mut returned)?;
            }
            Instruction::TailCallSelf { args }
                if !reference_leaves(a, f.return_type).is_empty() =>
            {
                let contract =
                    aggregate_reference_return_origins_with(a, fid, visiting, provisional)?;
                let origins = instantiate_carrier_contract(&contract, Some(0), args, &state, fid)?;
                record_carrier_return(fid, origins, &mut returned)?;
            }
            Instruction::TailCallKnownReceiver {
                function,
                receiver,
                args,
            } if !reference_leaves(a, f.return_type).is_empty() => {
                let contract =
                    aggregate_reference_return_origins_with(a, *function, visiting, provisional)?;
                let mut origins = Vec::new();
                for (result_path, origin) in contract {
                    let source = match origin {
                        CarrierOrigin::Parameter { parameter, path } => {
                            let argument = *args
                                .get(parameter)
                                .ok_or(VerifyError::InvalidFunction(*function))?;
                            state[argument as usize]
                                .iter()
                                .find(|(candidate, _)| candidate == &path)
                                .map(|(_, origin)| origin.clone())
                        }
                        CarrierOrigin::Receiver { path } => state[*receiver as usize]
                            .iter()
                            .find(|(candidate, _)| candidate == &path)
                            .map(|(_, origin)| origin.clone()),
                        CarrierOrigin::Local => None,
                    }
                    .ok_or(VerifyError::InvalidFunction(*function))?;
                    origins.push((result_path, source));
                }
                record_carrier_return(fid, origins, &mut returned)?;
            }
            Instruction::TailCallIndirect { callable, args, .. }
                if !reference_leaves(a, f.return_type).is_empty() =>
            {
                let targets = &callable_targets[pc as usize][*callable as usize];
                let contract =
                    canonical_callable_carrier_contract_with(a, targets, visiting, provisional)
                        .map_err(|_| VerifyError::InvalidFunction(fid))?;
                let origins =
                    instantiate_carrier_contract(&contract, Some(*callable), args, &state, fid)?;
                record_carrier_return(fid, origins, &mut returned)?;
            }
            Instruction::Return { src: Some(src) } => {
                let origins = state[*src as usize].clone();
                if origins
                    .iter()
                    .any(|(_, origin)| matches!(origin, CarrierOrigin::Local))
                {
                    return Err(VerifyError::InvalidFunction(fid));
                }
                match &returned {
                    Some(existing) if existing != &origins => {
                        return Err(VerifyError::InvalidFunction(fid));
                    }
                    None => returned = Some(origins),
                    _ => {}
                }
            }
            Instruction::Leave { slot, value } => {
                let entry = label_states[pc as usize]
                    .iter()
                    .rfind(|entry| entry.slot == *slot)
                    .ok_or(VerifyError::InvalidFunction(fid))?;
                state[entry.result_register as usize] = std::mem::take(&mut state[*value as usize]);
            }
            Instruction::Drop { register }
            | Instruction::EndBorrow {
                reference: register,
            }
            | Instruction::Deconstruct { src: register } => state[*register as usize].clear(),
            _ => {}
        }
        let successors = match instruction {
            Instruction::Jump { target } => vec![*target],
            Instruction::Switch {
                cases, otherwise, ..
            } => cases
                .iter()
                .map(|case| case.1)
                .chain(std::iter::once(*otherwise))
                .collect(),
            Instruction::Return { .. }
            | Instruction::TailCall { .. }
            | Instruction::TailCallSelf { .. }
            | Instruction::TailCallKnownReceiver { .. }
            | Instruction::TailCallIndirect { .. }
            | Instruction::TailResume { .. }
            | Instruction::Perform { dst: None, .. }
            | Instruction::Unreachable
            | Instruction::Abort { .. } => vec![],
            Instruction::Leave { slot, .. } => vec![
                label_states[pc as usize]
                    .iter()
                    .rfind(|entry| entry.slot == *slot)
                    .ok_or(VerifyError::InvalidFunction(fid))?
                    .target,
            ],
            _ => vec![pc + 1],
        };
        for successor in successors {
            let slot = states
                .get_mut(successor as usize)
                .ok_or(VerifyError::InvalidFunction(fid))?;
            match slot {
                Some(existing) if existing != &state => {
                    let mut changed = false;
                    for (old, incoming) in existing.iter_mut().zip(&state) {
                        if old == incoming || (!old.is_empty() && incoming.is_empty()) {
                            continue;
                        }
                        if old.is_empty() {
                            *old = incoming.clone();
                            changed = true;
                            continue;
                        }
                        return Err(VerifyError::InvalidFunction(fid));
                    }
                    if changed {
                        work.push_back(successor);
                    }
                }
                Some(_) => {}
                None => {
                    *slot = Some(state.clone());
                    work.push_back(successor);
                }
            }
        }
    }
    returned.ok_or(VerifyError::InvalidFunction(fid))
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum ArrayWritePosition {
    Exact(u64),
    Push,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ArrayWriteEffect {
    owner_parameter: usize,
    position: ArrayWritePosition,
    value_parameter: usize,
    value_path: Vec<u32>,
}

/// Infer the caller-visible reference loans installed by exact array writes.
///
/// This is deliberately an ephemeral, body-derived contract.  It mirrors the
/// source ownership summary without adding lifetime metadata to the artifact.
/// Unsupported control flow, dynamic indices, receiver/local origins, and
/// recursive effect cycles fail closed by producing no usable contract.
fn array_write_effects(a: &Artifact, fid: u32) -> Result<Vec<ArrayWriteEffect>, VerifyError> {
    array_write_effects_with(a, fid, &mut Vec::new())
}

fn array_write_effects_with(
    a: &Artifact,
    fid: u32,
    visiting: &mut Vec<u32>,
) -> Result<Vec<ArrayWriteEffect>, VerifyError> {
    if visiting.contains(&fid) {
        return Err(VerifyError::InvalidFunction(fid));
    }
    let f = a
        .functions
        .get(fid as usize)
        .ok_or(VerifyError::InvalidFunction(fid))?;
    let label_states = verify_labels(a, fid, f)?;
    let array_roots = array_roots_at_pcs(a, fid, f, &label_states)?;
    let constants = constant_u64_registers_at_pcs(a, fid, f, &label_states)?;
    let mut entry = vec![CarrierOrigins::new(); f.register_types.len()];
    for (parameter, ty) in f.params.iter().enumerate() {
        entry[parameter + 1] = reference_leaves(a, *ty)
            .into_iter()
            .map(|(path, _)| (path.clone(), CarrierOrigin::Parameter { parameter, path }))
            .collect();
    }
    let mut states = vec![None; f.code_len as usize];
    states[0] = Some((entry, Vec::<ArrayWriteEffect>::new()));
    let mut work = VecDeque::from([0u32]);
    let mut returned = None::<Vec<ArrayWriteEffect>>;
    visiting.push(fid);
    let result = (|| {
        while let Some(pc) = work.pop_front() {
            let (mut origins, mut effects) = states[pc as usize].clone().unwrap();
            let instruction = &a.code[f.code_start as usize + pc as usize];
            match instruction {
                Instruction::Move { dst, src } => {
                    origins[*dst as usize] = std::mem::take(&mut origins[*src as usize]);
                }
                Instruction::Copy { dst, src } => {
                    origins[*dst as usize] = origins[*src as usize].clone();
                }
                Instruction::Construct {
                    dst,
                    ty,
                    variant,
                    fields,
                } => {
                    let field_indices = construction_field_types(&a.types[*ty as usize], *variant)
                        .ok_or(VerifyError::InvalidFunction(fid))?
                        .into_iter()
                        .enumerate()
                        .filter_map(|(field, ty)| {
                            (!matches!(type_at(a, ty), Ok(Type::Available { .. })))
                                .then_some(field as u32)
                        });
                    let mut carried = Vec::new();
                    for (&register, field) in fields.iter().zip(field_indices) {
                        carried.extend(origins[register as usize].drain(..).map(
                            |(mut path, origin)| {
                                path.insert(0, field);
                                (path, origin)
                            },
                        ));
                    }
                    carried.sort_by(|left, right| left.0.cmp(&right.0));
                    origins[*dst as usize] = carried;
                }
                Instruction::ProjectMove { dst, src, field } => {
                    let mut projected = Vec::new();
                    origins[*src as usize].retain(|(path, origin)| {
                        if path.first() == Some(field) {
                            projected.push((path[1..].to_vec(), origin.clone()));
                            false
                        } else {
                            true
                        }
                    });
                    origins[*dst as usize] = projected;
                }
                Instruction::ProjectCopy { dst, src, field } => {
                    origins[*dst as usize] = origins[*src as usize]
                        .iter()
                        .filter(|(path, _)| path.first() == Some(field))
                        .map(|(path, origin)| (path[1..].to_vec(), origin.clone()))
                        .collect();
                }
                Instruction::ReborrowShared { dst, src }
                | Instruction::ReborrowUnique { dst, src }
                | Instruction::ProjectBorrowShared { dst, src, .. }
                | Instruction::ProjectBorrowUnique { dst, src, .. } => {
                    origins[*dst as usize] = origins[*src as usize].clone();
                }
                Instruction::Primitive { op, args, .. }
                    if matches!(op, Primitive::ArraySetMove | Primitive::ArrayPushMove) =>
                {
                    let root = args
                        .first()
                        .and_then(|register| array_roots[pc as usize][*register as usize]);
                    if let Some(ArrayRoot::Parameter(owner_parameter)) = root {
                        let item = *args
                            .get(if matches!(op, Primitive::ArraySetMove) {
                                2
                            } else {
                                1
                            })
                            .ok_or(VerifyError::InvalidFunction(fid))?;
                        let position = if matches!(op, Primitive::ArraySetMove) {
                            ArrayWritePosition::Exact(
                                args.get(1)
                                    .and_then(|register| constants[pc as usize][*register as usize])
                                    .ok_or(VerifyError::InvalidFunction(fid))?,
                            )
                        } else {
                            ArrayWritePosition::Push
                        };
                        let installed = origins[item as usize].clone();
                        if installed.is_empty() {
                            return Err(VerifyError::InvalidFunction(fid));
                        }
                        for (value_path, origin) in installed {
                            let CarrierOrigin::Parameter {
                                parameter: value_parameter,
                                path: source_path,
                            } = origin
                            else {
                                return Err(VerifyError::InvalidFunction(fid));
                            };
                            if source_path != value_path {
                                return Err(VerifyError::InvalidFunction(fid));
                            }
                            effects.push(ArrayWriteEffect {
                                owner_parameter,
                                position: position.clone(),
                                value_parameter,
                                value_path,
                            });
                        }
                    }
                }
                Instruction::Call {
                    dst,
                    function,
                    args,
                } => {
                    if let Ok(callee_effects) = array_write_effects_with(a, *function, visiting) {
                        for effect in callee_effects {
                            let owner_argument = *args
                                .get(effect.owner_parameter)
                                .ok_or(VerifyError::InvalidFunction(*function))?;
                            let Some(ArrayRoot::Parameter(owner_parameter)) =
                                array_roots[pc as usize][owner_argument as usize]
                            else {
                                continue;
                            };
                            let value_argument = *args
                                .get(effect.value_parameter)
                                .ok_or(VerifyError::InvalidFunction(*function))?;
                            let (_, origin) = origins[value_argument as usize]
                                .iter()
                                .find(|(path, _)| path == &effect.value_path)
                                .ok_or(VerifyError::InvalidFunction(*function))?;
                            let CarrierOrigin::Parameter {
                                parameter: value_parameter,
                                path: source_path,
                            } = origin
                            else {
                                return Err(VerifyError::InvalidFunction(fid));
                            };
                            if source_path != &effect.value_path {
                                return Err(VerifyError::InvalidFunction(fid));
                            }
                            effects.push(ArrayWriteEffect {
                                owner_parameter,
                                position: effect.position,
                                value_parameter: *value_parameter,
                                value_path: effect.value_path,
                            });
                        }
                    }
                    if let Some(dst) = dst
                        && !reference_leaves(a, f.register_types[*dst as usize]).is_empty()
                    {
                        let contract =
                            aggregate_reference_return_origins(a, *function, &mut vec![])?;
                        origins[*dst as usize] = instantiate_carrier_contract(
                            &contract, None, args, &origins, *function,
                        )?;
                    }
                }
                Instruction::Return { .. } => {
                    effects.sort_by(|left, right| {
                        left.owner_parameter
                            .cmp(&right.owner_parameter)
                            .then_with(|| left.value_path.cmp(&right.value_path))
                            .then_with(|| left.value_parameter.cmp(&right.value_parameter))
                    });
                    if returned
                        .as_ref()
                        .is_some_and(|existing| existing != &effects)
                    {
                        return Err(VerifyError::InvalidFunction(fid));
                    }
                    returned.get_or_insert(effects.clone());
                }
                _ => {}
            }
            let successors = match instruction {
                Instruction::Jump { target } => vec![*target],
                Instruction::Switch {
                    cases, otherwise, ..
                } => cases
                    .iter()
                    .map(|case| case.1)
                    .chain(std::iter::once(*otherwise))
                    .collect(),
                Instruction::Return { .. }
                | Instruction::TailCall { .. }
                | Instruction::TailCallSelf { .. }
                | Instruction::TailCallKnownReceiver { .. }
                | Instruction::TailCallIndirect { .. }
                | Instruction::TailResume { .. }
                | Instruction::Perform { dst: None, .. }
                | Instruction::Unreachable
                | Instruction::Abort { .. } => vec![],
                Instruction::Leave { slot, .. } => vec![
                    label_states[pc as usize]
                        .iter()
                        .rfind(|entry| entry.slot == *slot)
                        .ok_or(VerifyError::InvalidFunction(fid))?
                        .target,
                ],
                _ => vec![pc + 1],
            };
            for successor in successors {
                let slot = states
                    .get_mut(successor as usize)
                    .ok_or(VerifyError::InvalidFunction(fid))?;
                let incoming = (origins.clone(), effects.clone());
                match slot {
                    Some(existing) if existing != &incoming => {
                        return Err(VerifyError::InvalidFunction(fid));
                    }
                    Some(_) => {}
                    None => {
                        *slot = Some(incoming);
                        work.push_back(successor);
                    }
                }
            }
        }
        Ok(returned.unwrap_or_default())
    })();
    visiting.pop();
    result
}

fn unique_reference_carrier(state: &[CarrierOrigins], registers: &[u32]) -> Option<CarrierOrigins> {
    let mut carriers = registers
        .iter()
        .filter(|register| !state[**register as usize].is_empty())
        .map(|register| state[*register as usize].clone());
    let carrier = carriers.next()?;
    carriers.next().is_none().then_some(carrier)
}

fn instantiate_carrier_contract(
    contract: &CarrierOrigins,
    receiver: Option<u32>,
    arguments: &[u32],
    state: &[CarrierOrigins],
    callee: u32,
) -> Result<CarrierOrigins, VerifyError> {
    contract
        .iter()
        .map(|(result_path, origin)| {
            let (register, path) = match origin {
                CarrierOrigin::Parameter { parameter, path } => (
                    *arguments
                        .get(*parameter)
                        .ok_or(VerifyError::InvalidFunction(callee))?,
                    path,
                ),
                CarrierOrigin::Receiver { path } => {
                    (receiver.ok_or(VerifyError::InvalidFunction(callee))?, path)
                }
                CarrierOrigin::Local => return Err(VerifyError::InvalidFunction(callee)),
            };
            let source = state[register as usize]
                .iter()
                .find(|(candidate, _)| candidate == path)
                .map(|(_, origin)| origin.clone())
                .ok_or(VerifyError::InvalidFunction(callee))?;
            Ok((result_path.clone(), source))
        })
        .collect()
}

fn record_carrier_return(
    fid: u32,
    origins: CarrierOrigins,
    returned: &mut Option<CarrierOrigins>,
) -> Result<(), VerifyError> {
    if origins
        .iter()
        .any(|(_, origin)| matches!(origin, CarrierOrigin::Local))
        || returned
            .as_ref()
            .is_some_and(|existing| existing != &origins)
    {
        return Err(VerifyError::InvalidFunction(fid));
    }
    if returned.is_none() {
        *returned = Some(origins);
    }
    Ok(())
}

fn remap_carrier_origins(
    a: &Artifact,
    destination: TypeId,
    sources: CarrierOrigins,
    fid: u32,
) -> Result<CarrierOrigins, VerifyError> {
    let leaves = reference_leaves(a, destination);
    if leaves.len() != sources.len() {
        return Err(VerifyError::InvalidFunction(fid));
    }
    Ok(leaves
        .into_iter()
        .zip(sources)
        .map(|((path, _), (_, origin))| (path, origin))
        .collect())
}

/// Prove that every returning path yields a reference rooted in the same
/// reference parameter. Local places and callable captures are intentionally
/// excluded: neither outlives the frame/callable invocation in general.
fn reference_return_parameter(
    a: &Artifact,
    fid: u32,
    visiting: &mut Vec<u32>,
) -> Result<Option<ReferenceOrigin>, VerifyError> {
    if visiting.contains(&fid) {
        // Break a recursive inference cycle only when the signature itself has
        // one unambiguous candidate. This is provisional: every non-cyclic
        // caller on the stack still validates its complete body and rejects a
        // local origin, a different parameter, or inconsistent return paths.
        let function = a
            .functions
            .get(fid as usize)
            .ok_or(VerifyError::InvalidFunction(fid))?;
        let mut candidates = function
            .params
            .iter()
            .enumerate()
            .filter_map(|(index, ty)| {
                single_reference_leaf(a, *ty).map(|_| ReferenceOrigin::Parameter(index))
            })
            .collect::<Vec<_>>();
        if function.receiver_mode.is_some()
            && single_reference_leaf(a, function.register_types[0]).is_some()
        {
            candidates.push(ReferenceOrigin::Receiver);
        }
        return (candidates.len() == 1)
            .then(|| Some(candidates[0]))
            .ok_or(VerifyError::InvalidFunction(fid));
    }
    visiting.push(fid);
    let result = reference_return_parameter_inner(a, fid, visiting);
    visiting.pop();
    result
}

fn indirect_reference_parameter(a: &Artifact, signature: &Signature) -> Option<usize> {
    single_reference_leaf(a, signature.result)?;
    let mut matches = signature
        .params
        .iter()
        .enumerate()
        .filter_map(|(index, ty)| single_reference_leaf(a, *ty).map(|_| index));
    let only = matches.next()?;
    matches.next().is_none().then_some(only)
}

fn reference_return_parameter_inner(
    a: &Artifact,
    fid: u32,
    visiting: &mut Vec<u32>,
) -> Result<Option<ReferenceOrigin>, VerifyError> {
    let f = a
        .functions
        .get(fid as usize)
        .ok_or(VerifyError::InvalidFunction(fid))?;
    let label_states = verify_labels(a, fid, f)?;
    let callable_targets = callable_targets_at_pcs(a, fid, f, &label_states)?;
    let array_roots = array_roots_at_pcs(a, fid, f, &label_states)?;
    let constants = constant_u64_registers_at_pcs(a, fid, f, &label_states)?;
    let mut entry = vec![None; f.register_types.len()];
    // The receiver is tied to callable storage, not a normal argument whose
    // owner is known to the caller, so it is never a permitted escape root.
    for (index, ty) in f.params.iter().enumerate() {
        if single_reference_leaf(a, *ty).is_some() {
            entry[index + 1] = Some(ReferenceOrigin::Parameter(index));
        }
    }
    if f.receiver_mode.is_some() && single_reference_leaf(a, f.register_types[0]).is_some() {
        entry[0] = Some(ReferenceOrigin::Receiver);
    }
    let mut states = vec![None; f.code_len as usize];
    states[0] = Some(entry);
    let mut work = VecDeque::from([0u32]);
    let mut returned = None;
    let mut saw_return = false;
    let start = f.code_start as usize;
    while let Some(pc) = work.pop_front() {
        let mut state = states[pc as usize].clone().unwrap();
        let instruction = a
            .code
            .get(start + pc as usize)
            .ok_or(VerifyError::InvalidFunction(fid))?;
        let carries_reference =
            |register: u32| single_reference_leaf(a, f.register_types[register as usize]).is_some();
        match instruction {
            Instruction::Move { dst, src } => {
                let origin = state[*src as usize].take();
                state[*dst as usize] = origin;
            }
            Instruction::Copy { dst, src } => state[*dst as usize] = state[*src as usize],
            Instruction::Construct { dst, fields, .. } => {
                let mut origins = fields
                    .iter()
                    .filter_map(|field| state[*field as usize])
                    .collect::<Vec<_>>();
                origins.dedup();
                if origins.len() > 1 {
                    return Err(VerifyError::InvalidFunction(fid));
                }
                for field in fields {
                    state[*field as usize] = None;
                }
                state[*dst as usize] = origins.into_iter().next();
            }
            Instruction::MakeCallable { dst, captures, .. }
            | Instruction::MakeHandlerShared { dst, captures, .. } => {
                let mut origins = captures
                    .iter()
                    .filter_map(|capture| state[*capture as usize])
                    .collect::<Vec<_>>();
                origins.dedup();
                if origins.len() > 1 {
                    return Err(VerifyError::InvalidFunction(fid));
                }
                for capture in captures {
                    state[*capture as usize] = None;
                }
                state[*dst as usize] = origins.into_iter().next();
            }
            Instruction::MakeHandler { dst, clauses, .. } => {
                let mut origins = clauses
                    .iter()
                    .filter_map(|clause| state[*clause as usize])
                    .collect::<Vec<_>>();
                origins.dedup();
                if origins.len() > 1 {
                    return Err(VerifyError::InvalidFunction(fid));
                }
                for clause in clauses {
                    state[*clause as usize] = None;
                }
                state[*dst as usize] = origins.into_iter().next();
            }
            Instruction::MakeBindingPack { dst, payloads, .. } => {
                let mut origins = payloads
                    .iter()
                    .filter_map(|payload| state[*payload as usize])
                    .collect::<Vec<_>>();
                origins.dedup();
                if origins.len() > 1 {
                    return Err(VerifyError::InvalidFunction(fid));
                }
                for payload in payloads {
                    state[*payload as usize] = None;
                }
                state[*dst as usize] = origins.into_iter().next();
            }
            Instruction::ProjectMove { dst, src, .. } => {
                if carries_reference(*dst) {
                    state[*dst as usize] = state[*src as usize].take();
                }
            }
            Instruction::ProjectCopy { dst, src, .. } => {
                if carries_reference(*dst) {
                    state[*dst as usize] = state[*src as usize];
                }
            }
            Instruction::BorrowShared { dst, .. } | Instruction::BorrowUnique { dst, .. } => {
                state[*dst as usize] = Some(ReferenceOrigin::Local)
            }
            Instruction::ReborrowShared { dst, src }
            | Instruction::ReborrowUnique { dst, src }
            | Instruction::ProjectBorrowShared { dst, src, .. }
            | Instruction::ProjectBorrowUnique { dst, src, .. } => {
                state[*dst as usize] = state[*src as usize]
            }
            Instruction::Primitive { dst, op, args } if carries_reference(*dst) => {
                let origin = if matches!(
                    op,
                    Primitive::ArrayGetBorrowShared | Primitive::ArrayGetBorrowUnique
                ) {
                    args.first().and_then(|arg| state[*arg as usize])
                } else if matches!(
                    op,
                    Primitive::ArrayGetCopy | Primitive::ArrayGetMove | Primitive::ArrayPopMove
                ) {
                    let exact = !matches!(op, Primitive::ArrayGetCopy | Primitive::ArrayGetMove)
                        || args
                            .get(1)
                            .is_some_and(|index| constants[pc as usize][*index as usize].is_some());
                    exact
                        .then(|| args.first())
                        .flatten()
                        .and_then(|array| array_roots[pc as usize][*array as usize])
                        .and_then(|root| match root {
                            ArrayRoot::Parameter(parameter) => {
                                Some(ReferenceOrigin::Parameter(parameter))
                            }
                            ArrayRoot::Local(_) => None,
                        })
                } else {
                    Some(ReferenceOrigin::Local)
                };
                state[*dst as usize] = origin;
            }
            Instruction::Call {
                dst: Some(dst),
                function,
                args,
            } if carries_reference(*dst) => {
                let parameter = reference_return_parameter(a, *function, visiting)?;
                state[*dst as usize] = match parameter {
                    Some(ReferenceOrigin::Parameter(parameter)) => {
                        args.get(parameter).and_then(|arg| state[*arg as usize])
                    }
                    Some(ReferenceOrigin::Receiver | ReferenceOrigin::Local) => {
                        return Err(VerifyError::InvalidFunction(fid));
                    }
                    None => None,
                };
            }
            Instruction::CallSelf {
                dst: Some(dst),
                args,
            } if carries_reference(*dst) => {
                state[*dst as usize] = match reference_return_parameter(a, fid, visiting)? {
                    Some(ReferenceOrigin::Parameter(parameter)) => {
                        args.get(parameter).and_then(|arg| state[*arg as usize])
                    }
                    Some(ReferenceOrigin::Receiver) => state[0],
                    Some(ReferenceOrigin::Local) => {
                        return Err(VerifyError::InvalidFunction(fid));
                    }
                    None => None,
                };
            }
            Instruction::CallKnownReceiver {
                dst: Some(dst),
                function,
                receiver,
                args,
            } if carries_reference(*dst) => {
                state[*dst as usize] = match reference_return_parameter(a, *function, visiting)? {
                    Some(ReferenceOrigin::Parameter(parameter)) => {
                        args.get(parameter).and_then(|arg| state[*arg as usize])
                    }
                    Some(ReferenceOrigin::Receiver) => state[*receiver as usize],
                    Some(ReferenceOrigin::Local) => {
                        return Err(VerifyError::InvalidFunction(*function));
                    }
                    None => None,
                };
            }
            Instruction::CallIndirect {
                dst: Some(dst),
                callable,
                args,
                ..
            } if carries_reference(*dst) => {
                let targets = &callable_targets[pc as usize][*callable as usize];
                let contract = if targets.is_empty() {
                    let Type::Callable { signature, .. } =
                        type_at(a, f.register_types[*callable as usize])?
                    else {
                        return Err(VerifyError::InvalidFunction(fid));
                    };
                    indirect_reference_parameter(a, signature).map(ReferenceOrigin::Parameter)
                } else {
                    canonical_callable_reference_contract(a, targets, visiting)
                        .map_err(|_| VerifyError::InvalidFunction(fid))?
                };
                state[*dst as usize] = match contract {
                    Some(ReferenceOrigin::Parameter(parameter)) => {
                        args.get(parameter).and_then(|arg| state[*arg as usize])
                    }
                    Some(ReferenceOrigin::Receiver) => state[*callable as usize],
                    Some(ReferenceOrigin::Local) => return Err(VerifyError::InvalidFunction(fid)),
                    None => None,
                };
            }
            Instruction::Perform {
                dst: Some(dst),
                payloads,
                ..
            } if carries_reference(*dst) => {
                let mut origins = payloads
                    .iter()
                    .filter_map(|payload| state[*payload as usize])
                    .collect::<Vec<_>>();
                origins.dedup();
                if origins.len() != 1 {
                    return Err(VerifyError::InvalidFunction(fid));
                }
                state[*dst as usize] = origins.first().copied();
                for payload in payloads {
                    state[*payload as usize] = None;
                }
            }
            Instruction::Resume {
                dst,
                value,
                resumption,
                receiver_mode,
            } if carries_reference(*dst) => {
                state[*dst as usize] = state[*value as usize];
                if state[*dst as usize].is_none() {
                    return Err(VerifyError::InvalidFunction(fid));
                }
                state[*value as usize] = None;
                if *receiver_mode == 2 {
                    state[*resumption as usize] = None;
                }
            }
            Instruction::TailResume {
                value,
                resumption,
                receiver_mode,
            } => {
                state[*value as usize] = None;
                if *receiver_mode == 2 {
                    state[*resumption as usize] = None;
                }
            }
            Instruction::Handle {
                dst,
                handler,
                body,
                args,
            } if carries_reference(*dst) => {
                let mut inputs = vec![*handler, *body];
                inputs.extend(args.iter().copied());
                let mut origins = inputs
                    .iter()
                    .filter_map(|input| state[*input as usize])
                    .collect::<Vec<_>>();
                origins.dedup();
                if origins.len() > 1 {
                    return Err(VerifyError::InvalidFunction(fid));
                }
                for input in inputs {
                    state[input as usize] = None;
                }
                state[*dst as usize] = origins.into_iter().next();
            }
            Instruction::TailCall { function, args } => {
                let parameter = reference_return_parameter(a, *function, visiting)?;
                let origin = match parameter {
                    Some(ReferenceOrigin::Parameter(parameter)) => {
                        args.get(parameter).and_then(|arg| state[*arg as usize])
                    }
                    Some(ReferenceOrigin::Receiver | ReferenceOrigin::Local) => {
                        return Err(VerifyError::InvalidFunction(fid));
                    }
                    None => None,
                };
                record_reference_return(fid, origin, &mut returned, &mut saw_return)?;
            }
            Instruction::TailCallKnownReceiver {
                function,
                receiver,
                args,
            } => {
                let origin = match reference_return_parameter(a, *function, visiting)? {
                    Some(ReferenceOrigin::Parameter(parameter)) => {
                        args.get(parameter).and_then(|arg| state[*arg as usize])
                    }
                    Some(ReferenceOrigin::Receiver) => state[*receiver as usize],
                    Some(ReferenceOrigin::Local) => {
                        return Err(VerifyError::InvalidFunction(*function));
                    }
                    None => None,
                };
                record_reference_return(fid, origin, &mut returned, &mut saw_return)?;
            }
            Instruction::TailCallSelf { args } => {
                let origin = match reference_return_parameter(a, fid, visiting)? {
                    Some(ReferenceOrigin::Parameter(parameter)) => {
                        args.get(parameter).and_then(|arg| state[*arg as usize])
                    }
                    Some(ReferenceOrigin::Receiver) => state[0],
                    Some(ReferenceOrigin::Local) => {
                        return Err(VerifyError::InvalidFunction(fid));
                    }
                    None => None,
                };
                record_reference_return(fid, origin, &mut returned, &mut saw_return)?;
            }
            Instruction::TailCallIndirect { callable, args, .. } => {
                let targets = &callable_targets[pc as usize][*callable as usize];
                let contract = if targets.is_empty() {
                    let Type::Callable { signature, .. } =
                        type_at(a, f.register_types[*callable as usize])?
                    else {
                        return Err(VerifyError::InvalidFunction(fid));
                    };
                    indirect_reference_parameter(a, signature).map(ReferenceOrigin::Parameter)
                } else {
                    canonical_callable_reference_contract(a, targets, visiting)
                        .map_err(|_| VerifyError::InvalidFunction(fid))?
                };
                let origin = match contract {
                    Some(ReferenceOrigin::Parameter(parameter)) => {
                        args.get(parameter).and_then(|arg| state[*arg as usize])
                    }
                    Some(ReferenceOrigin::Receiver) => state[*callable as usize],
                    Some(ReferenceOrigin::Local) => return Err(VerifyError::InvalidFunction(fid)),
                    None => None,
                };
                record_reference_return(fid, origin, &mut returned, &mut saw_return)?;
            }
            Instruction::Perform {
                dst: None,
                payloads,
                ..
            } => {
                let mut origins = payloads
                    .iter()
                    .filter_map(|payload| state[*payload as usize])
                    .collect::<Vec<_>>();
                origins.dedup();
                if origins.len() > 1 {
                    return Err(VerifyError::InvalidFunction(fid));
                }
                record_reference_return(
                    fid,
                    origins.into_iter().next(),
                    &mut returned,
                    &mut saw_return,
                )?;
            }
            Instruction::Return { src: Some(src) } => {
                record_reference_return(fid, state[*src as usize], &mut returned, &mut saw_return)?;
            }
            Instruction::Leave { slot, value } => {
                let entry = label_states[pc as usize]
                    .iter()
                    .rfind(|entry| entry.slot == *slot)
                    .ok_or(VerifyError::InvalidFunction(fid))?;
                state[entry.result_register as usize] = state[*value as usize].take();
            }
            Instruction::Handle { dst, .. } | Instruction::HostCall { dst: Some(dst), .. }
                if carries_reference(*dst) =>
            {
                state[*dst as usize] = Some(ReferenceOrigin::Local)
            }
            _ => {}
        }

        let successors: Vec<u32> = match instruction {
            Instruction::Jump { target } => vec![*target],
            Instruction::Switch {
                cases, otherwise, ..
            } => cases
                .iter()
                .map(|case| case.1)
                .chain(std::iter::once(*otherwise))
                .collect(),
            Instruction::Return { .. }
            | Instruction::TailCall { .. }
            | Instruction::TailCallSelf { .. }
            | Instruction::TailCallKnownReceiver { .. }
            | Instruction::TailCallIndirect { .. }
            | Instruction::TailResume { .. }
            | Instruction::Perform { dst: None, .. }
            | Instruction::Unreachable
            | Instruction::Abort { .. } => vec![],
            Instruction::Leave { slot, .. } => vec![
                label_states[pc as usize]
                    .iter()
                    .rfind(|entry| entry.slot == *slot)
                    .ok_or(VerifyError::InvalidFunction(fid))?
                    .target,
            ],
            _ => vec![pc + 1],
        };
        for successor in successors {
            let Some(slot) = states.get_mut(successor as usize) else {
                return Err(VerifyError::InvalidTarget {
                    function: fid,
                    instruction: pc,
                    target: successor,
                });
            };
            match slot {
                Some(existing) if existing != &state => {
                    let mut changed = false;
                    for (register, (old, new)) in existing.iter_mut().zip(&state).enumerate() {
                        if old == new {
                            continue;
                        }
                        if single_reference_leaf(a, f.register_types[register]).is_some()
                            && (old.is_none() || new.is_none())
                        {
                            if old.is_none() {
                                *old = *new;
                                changed = true;
                            }
                            continue;
                        }
                        return Err(VerifyError::InvalidFunction(fid));
                    }
                    if changed {
                        work.push_back(successor);
                    }
                }
                Some(_) => {}
                None => {
                    *slot = Some(state.clone());
                    work.push_back(successor);
                }
            }
        }
    }
    saw_return
        .then_some(returned)
        .ok_or(VerifyError::InvalidFunction(fid))
}

fn record_reference_return(
    fid: u32,
    origin: Option<ReferenceOrigin>,
    returned: &mut Option<ReferenceOrigin>,
    saw_return: &mut bool,
) -> Result<(), VerifyError> {
    *saw_return = true;
    let Some(origin) = origin else {
        return Ok(());
    };
    if origin == ReferenceOrigin::Local {
        return Err(VerifyError::InvalidFunction(fid));
    }
    match returned {
        Some(existing) if *existing != origin => Err(VerifyError::InvalidFunction(fid)),
        Some(_) => Ok(()),
        None => {
            *returned = Some(origin);
            Ok(())
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct BorrowedPlace {
    owner: u32,
    projections: Vec<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Loan {
    place: BorrowedPlace,
    unique: bool,
    suspended_parent: Option<u32>,
    /// `false` only between DEREF_MOVE and the matching DEREF_STORE through
    /// this unique handle.  Keeping this on the loan makes the transient hole
    /// follow ordinary register moves and participate in CFG join equality.
    referent_initialized: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct CarrierLoan {
    /// Field path inside the register value. Direct references use the empty path.
    path: Vec<u32>,
    loan: Loan,
}

type CarrierLoans = Vec<CarrierLoan>;

// Array indices live in a separate namespace from aggregate field paths.
// No well-formed aggregate can have `u32::MAX` fields, so this marker makes
// exact array slots unambiguous without extending the bytecode ABI.
const ARRAY_SLOT_PATH: u32 = u32::MAX;

fn array_slot_path(index: u64, mut element_path: Vec<u32>) -> Option<Vec<u32>> {
    let index = u32::try_from(index).ok()?;
    let mut path = Vec::with_capacity(element_path.len() + 2);
    path.extend([ARRAY_SLOT_PATH, index]);
    path.append(&mut element_path);
    Some(path)
}

fn array_last_slot_path(mut element_path: Vec<u32>) -> Vec<u32> {
    let mut path = Vec::with_capacity(element_path.len() + 2);
    path.extend([ARRAY_SLOT_PATH, ARRAY_SLOT_PATH]);
    path.append(&mut element_path);
    path
}

fn split_array_slot_path(path: &[u32]) -> Option<(u64, &[u32])> {
    (path.first() == Some(&ARRAY_SLOT_PATH) && path.len() >= 2)
        .then(|| (u64::from(path[1]), &path[2..]))
}

fn instantiate_array_write_loans(
    effects: &[ArrayWriteEffect],
    arguments: &[u32],
    loans: &[CarrierLoans],
    callee: u32,
) -> Result<Vec<(u32, CarrierLoan)>, VerifyError> {
    let mut installed = Vec::new();
    let mut push_slots = std::collections::BTreeMap::<u32, u64>::new();
    for effect in effects {
        let owner_argument = *arguments
            .get(effect.owner_parameter)
            .ok_or(VerifyError::InvalidFunction(callee))?;
        let outer = loans[owner_argument as usize]
            .iter()
            .find(|loan| loan.path.is_empty())
            .ok_or(VerifyError::InvalidFunction(callee))?;
        let owner = outer.loan.place.owner;
        if owner as usize >= loans.len() {
            return Err(VerifyError::InvalidFunction(callee));
        }
        let value_argument = *arguments
            .get(effect.value_parameter)
            .ok_or(VerifyError::InvalidFunction(callee))?;
        let mut loan = loans[value_argument as usize]
            .iter()
            .find(|loan| loan.path == effect.value_path)
            .cloned()
            .ok_or(VerifyError::InvalidFunction(callee))?;
        let index = match effect.position {
            ArrayWritePosition::Exact(index) => index,
            ArrayWritePosition::Push => *push_slots.entry(owner).or_insert_with(|| {
                loans[owner as usize]
                    .iter()
                    .filter_map(|loan| split_array_slot_path(&loan.path).map(|slot| slot.0))
                    .max()
                    .map_or(0, |index| index.saturating_add(1))
            }),
        };
        if loans[owner as usize].iter().any(|loan| {
            split_array_slot_path(&loan.path)
                .is_some_and(|(candidate, path)| candidate == index && path == effect.value_path)
        }) {
            return Err(VerifyError::InvalidFunction(callee));
        }
        loan.path = array_slot_path(index, effect.value_path.clone())
            .ok_or(VerifyError::InvalidFunction(callee))?;
        installed.push((owner, loan));
    }
    Ok(installed)
}

fn array_element_type(a: &Artifact, ty: TypeId) -> Option<TypeId> {
    match a.types.get(ty as usize).map(Type::representation)? {
        Type::Array { element } => Some(*element),
        Type::RefShared { referent } | Type::RefUnique { referent } => {
            match a.types.get(*referent as usize).map(Type::representation)? {
                Type::Array { element } => Some(*element),
                _ => None,
            }
        }
        _ => None,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ArrayRoot {
    Local(u32),
    Parameter(usize),
}

fn array_roots_at_pcs(
    a: &Artifact,
    fid: u32,
    f: &Function,
    label_states: &[Vec<LabelEntry>],
) -> Result<Vec<Vec<Option<ArrayRoot>>>, VerifyError> {
    let mut entries = vec![None; f.code_len as usize];
    let mut entry = vec![None; f.register_types.len()];
    for (parameter, ty) in f.params.iter().enumerate() {
        if array_element_type(a, *ty).is_some() {
            entry[parameter + 1] = Some(ArrayRoot::Parameter(parameter));
        }
    }
    entries[0] = Some(entry);
    let mut work = VecDeque::from([0u32]);
    while let Some(pc) = work.pop_front() {
        let mut state = entries[pc as usize].clone().unwrap();
        let instruction = &a.code[f.code_start as usize + pc as usize];
        match instruction {
            Instruction::Move { dst, src } => {
                state[*dst as usize] = state[*src as usize].take();
            }
            Instruction::Copy { dst, src }
            | Instruction::BorrowShared { dst, src }
            | Instruction::BorrowUnique { dst, src }
            | Instruction::ReborrowShared { dst, src }
            | Instruction::ReborrowUnique { dst, src } => {
                state[*dst as usize] = state[*src as usize].or_else(|| {
                    array_element_type(a, f.register_types[*src as usize])
                        .is_some()
                        .then_some(ArrayRoot::Local(*src))
                });
            }
            Instruction::Primitive {
                dst,
                op: Primitive::ArrayEmpty | Primitive::ArrayNew,
                ..
            } => state[*dst as usize] = Some(ArrayRoot::Local(*dst)),
            _ => {
                if let Some(dst) = instruction_destination(instruction) {
                    state[dst as usize] = None;
                }
            }
        }
        let successors = match instruction {
            Instruction::Jump { target } => vec![*target],
            Instruction::Switch {
                cases, otherwise, ..
            } => cases
                .iter()
                .map(|case| case.1)
                .chain(std::iter::once(*otherwise))
                .collect(),
            Instruction::Leave { slot, .. } => vec![
                label_states[pc as usize]
                    .iter()
                    .rfind(|entry| entry.slot == *slot)
                    .ok_or(VerifyError::InvalidFunction(fid))?
                    .target,
            ],
            Instruction::Return { .. }
            | Instruction::TailCall { .. }
            | Instruction::TailCallSelf { .. }
            | Instruction::TailCallKnownReceiver { .. }
            | Instruction::TailCallIndirect { .. }
            | Instruction::TailResume { .. }
            | Instruction::Perform { dst: None, .. }
            | Instruction::Unreachable
            | Instruction::Abort { .. } => vec![],
            _ => vec![pc + 1],
        };
        for successor in successors {
            let slot = entries
                .get_mut(successor as usize)
                .ok_or(VerifyError::InvalidFunction(fid))?;
            match slot {
                None => {
                    *slot = Some(state.clone());
                    work.push_back(successor);
                }
                Some(existing) => {
                    let mut changed = false;
                    for (old, incoming) in existing.iter_mut().zip(&state) {
                        let joined = if old == incoming { *old } else { None };
                        if *old != joined {
                            *old = joined;
                            changed = true;
                        }
                    }
                    if changed {
                        work.push_back(successor);
                    }
                }
            }
        }
    }
    Ok(entries
        .into_iter()
        .map(|entry| entry.unwrap_or_else(|| vec![None; f.register_types.len()]))
        .collect())
}

fn constant_u64_registers_at_pcs(
    a: &Artifact,
    fid: u32,
    f: &Function,
    label_states: &[Vec<LabelEntry>],
) -> Result<Vec<Vec<Option<u64>>>, VerifyError> {
    let mut entries = vec![None; f.code_len as usize];
    entries[0] = Some(vec![None; f.register_types.len()]);
    let mut work = VecDeque::from([0u32]);
    while let Some(pc) = work.pop_front() {
        let mut state = entries[pc as usize].clone().unwrap();
        let instruction = &a.code[f.code_start as usize + pc as usize];
        match instruction {
            Instruction::Const { dst, constant } => {
                state[*dst as usize] = match a.constants.get(*constant as usize) {
                    Some(Constant::U8(value)) => Some(u64::from(*value)),
                    Some(Constant::U16(value)) => Some(u64::from(*value)),
                    Some(Constant::U32(value)) => Some(u64::from(*value)),
                    Some(Constant::U64(value) | Constant::Usize(value)) => Some(*value),
                    _ => None,
                };
            }
            Instruction::Move { dst, src } => {
                state[*dst as usize] = state[*src as usize].take();
            }
            Instruction::Copy { dst, src } => state[*dst as usize] = state[*src as usize],
            _ => {
                if let Some(dst) = instruction_destination(instruction) {
                    state[dst as usize] = None;
                }
            }
        }
        let successors = match instruction {
            Instruction::Jump { target } => vec![*target],
            Instruction::Switch {
                cases, otherwise, ..
            } => cases
                .iter()
                .map(|case| case.1)
                .chain(std::iter::once(*otherwise))
                .collect(),
            Instruction::Leave { slot, .. } => vec![
                label_states[pc as usize]
                    .iter()
                    .rfind(|entry| entry.slot == *slot)
                    .ok_or(VerifyError::InvalidFunction(fid))?
                    .target,
            ],
            Instruction::Return { .. }
            | Instruction::TailCall { .. }
            | Instruction::TailCallSelf { .. }
            | Instruction::TailCallKnownReceiver { .. }
            | Instruction::TailCallIndirect { .. }
            | Instruction::TailResume { .. }
            | Instruction::Perform { dst: None, .. }
            | Instruction::Unreachable
            | Instruction::Abort { .. } => vec![],
            _ => vec![pc + 1],
        };
        for successor in successors {
            let entry = entries
                .get_mut(successor as usize)
                .ok_or(VerifyError::InvalidFunction(fid))?;
            match entry {
                None => {
                    *entry = Some(state.clone());
                    work.push_back(successor);
                }
                Some(existing) => {
                    let mut changed = false;
                    for (old, incoming) in existing.iter_mut().zip(&state) {
                        let joined = if old == incoming { *old } else { None };
                        if *old != joined {
                            *old = joined;
                            changed = true;
                        }
                    }
                    if changed {
                        work.push_back(successor);
                    }
                }
            }
        }
    }
    Ok(entries
        .into_iter()
        .map(|entry| entry.unwrap_or_else(|| vec![None; f.register_types.len()]))
        .collect())
}

fn remap_carrier_loans(
    a: &Artifact,
    destination: TypeId,
    mut carried: CarrierLoans,
    fid: u32,
) -> Result<CarrierLoans, VerifyError> {
    let leaves = reference_leaves(a, destination);
    if leaves.len() != carried.len() {
        return Err(VerifyError::InvalidFunction(fid));
    }
    for (loan, (path, unique)) in carried.iter_mut().zip(leaves) {
        if loan.loan.unique != unique {
            return Err(VerifyError::InvalidFunction(fid));
        }
        loan.path = path;
    }
    Ok(carried)
}

fn reference_leaves(a: &Artifact, ty: TypeId) -> Vec<(Vec<u32>, bool)> {
    fn collect(
        a: &Artifact,
        ty: TypeId,
        visiting: &mut Vec<TypeId>,
        path: &mut Vec<u32>,
        leaves: &mut Vec<(Vec<u32>, bool)>,
    ) {
        if visiting.contains(&ty) {
            return;
        }
        visiting.push(ty);
        match a.types.get(ty as usize).map(Type::representation) {
            Some(Type::RefShared { .. }) => leaves.push((path.clone(), false)),
            Some(Type::RefUnique { .. }) => leaves.push((path.clone(), true)),
            Some(Type::Tuple { fields, .. }) => {
                for (field, ty) in fields.iter().enumerate() {
                    path.push(field as u32);
                    collect(a, *ty, visiting, path, leaves);
                    path.pop();
                }
            }
            Some(Type::Struct { fields, .. }) => {
                for (field, ty) in fields.iter().enumerate() {
                    path.push(field as u32);
                    collect(a, ty.ty, visiting, path, leaves);
                    path.pop();
                }
            }
            // Variant identity is not part of runtime field projection paths.
            // Keep only paths whose reference kind agrees across all variants.
            Some(Type::Enum { variants, .. }) => {
                let mut alternatives = Vec::new();
                for variant in variants {
                    let mut variant_leaves = Vec::new();
                    for (field, ty) in variant.fields.iter().enumerate() {
                        path.push(field as u32);
                        collect(a, ty.ty, visiting, path, &mut variant_leaves);
                        path.pop();
                    }
                    alternatives.push(variant_leaves);
                }
                if let Some(first) = alternatives.first()
                    && alternatives.iter().all(|candidate| candidate == first)
                {
                    leaves.extend(first.iter().cloned());
                }
            }
            Some(Type::Callable { capture_type, .. }) => {
                collect(a, *capture_type, visiting, path, leaves)
            }
            Some(Type::Handler { capture_type, .. }) => {
                let shared_environment = match a
                    .types
                    .get(*capture_type as usize)
                    .map(Type::representation)
                {
                    Some(Type::Tuple { fields, .. }) => {
                        let environments = fields
                            .iter()
                            .map(|field| {
                                match a.types.get(*field as usize).map(Type::representation) {
                                    Some(Type::Callable {
                                        capture_type,
                                        receiver_mode: 0,
                                        ..
                                    }) => Some(*capture_type),
                                    _ => None,
                                }
                            })
                            .collect::<Option<Vec<_>>>();
                        environments.and_then(|environments| {
                            environments.first().copied().filter(|first| {
                                environments.iter().all(|environment| environment == first)
                            })
                        })
                    }
                    _ => None,
                };
                collect(
                    a,
                    shared_environment.unwrap_or(*capture_type),
                    visiting,
                    path,
                    leaves,
                )
            }
            Some(Type::BindingPack { payload_type, .. }) => {
                collect(a, *payload_type, visiting, path, leaves)
            }
            // Dynamic element identities need a separate summarized model.
            Some(Type::Array { .. }) => {}
            _ => {}
        }
        visiting.pop();
    }

    let mut leaves = Vec::new();
    collect(a, ty, &mut Vec::new(), &mut Vec::new(), &mut leaves);
    leaves.sort_by(|left, right| left.0.cmp(&right.0));
    leaves
}

fn single_reference_leaf(a: &Artifact, ty: TypeId) -> Option<bool> {
    fn collect(a: &Artifact, ty: TypeId, visiting: &mut Vec<TypeId>, leaves: &mut Vec<bool>) {
        if leaves.len() > 1 || visiting.contains(&ty) {
            return;
        }
        visiting.push(ty);
        match a.types.get(ty as usize).map(Type::representation) {
            Some(Type::RefShared { .. }) => leaves.push(false),
            Some(Type::RefUnique { .. }) => leaves.push(true),
            Some(Type::Tuple { fields, .. }) => {
                for field in fields {
                    collect(a, *field, visiting, leaves);
                }
            }
            Some(Type::Struct { fields, .. }) => {
                for field in fields {
                    collect(a, field.ty, visiting, leaves);
                }
            }
            Some(Type::Enum { variants, .. }) => {
                for variant in variants {
                    for field in &variant.fields {
                        collect(a, field.ty, visiting, leaves);
                    }
                }
            }
            Some(Type::Callable { capture_type, .. }) => {
                collect(a, *capture_type, visiting, leaves)
            }
            Some(Type::Handler { capture_type, .. }) => {
                let shared_environment = match a
                    .types
                    .get(*capture_type as usize)
                    .map(Type::representation)
                {
                    Some(Type::Tuple { fields, .. }) => {
                        let environments = fields
                            .iter()
                            .map(|field| {
                                match a.types.get(*field as usize).map(Type::representation) {
                                    Some(Type::Callable {
                                        capture_type,
                                        receiver_mode: 0,
                                        ..
                                    }) => Some(*capture_type),
                                    _ => None,
                                }
                            })
                            .collect::<Option<Vec<_>>>();
                        environments.and_then(|environments| {
                            environments.first().copied().filter(|first| {
                                environments.iter().all(|environment| environment == first)
                            })
                        })
                    }
                    _ => None,
                };
                collect(
                    a,
                    shared_environment.unwrap_or(*capture_type),
                    visiting,
                    leaves,
                )
            }
            Some(Type::BindingPack { payload_type, .. }) => {
                collect(a, *payload_type, visiting, leaves)
            }
            Some(Type::Array { element }) => {
                let before = leaves.len();
                collect(a, *element, visiting, leaves);
                if leaves.len() > before {
                    leaves.push(leaves[before]);
                }
            }
            _ => {}
        }
        visiting.pop();
    }

    let mut leaves = Vec::new();
    collect(a, ty, &mut Vec::new(), &mut leaves);
    (leaves.len() == 1).then(|| leaves[0])
}

fn places_overlap(a: &BorrowedPlace, b: &BorrowedPlace) -> bool {
    a.owner == b.owner
        && a.projections
            .iter()
            .zip(&b.projections)
            .all(|(left, right)| left == right)
}

fn verify_loans(
    a: &Artifact,
    fid: u32,
    f: &Function,
    label_states: &[Vec<LabelEntry>],
) -> Result<Vec<Vec<CarrierLoans>>, VerifyError> {
    let start = f.code_start as usize;
    let callable_targets = callable_targets_at_pcs(a, fid, f, label_states)?;
    let constants = constant_u64_registers_at_pcs(a, fid, f, label_states)?;
    let mut states: Vec<Option<Vec<CarrierLoans>>> = vec![None; f.code_len as usize];
    let mut entry = vec![Vec::new(); f.register_types.len()];
    for (register, slot) in entry.iter_mut().enumerate().take(f.params.len() + 1) {
        *slot = reference_leaves(a, f.register_types[register])
            .into_iter()
            .enumerate()
            .map(|(leaf, (path, unique))| CarrierLoan {
                path,
                loan: Loan {
                    // Every external leaf is an independent verifier root.
                    place: BorrowedPlace {
                        owner: f.register_types.len() as u32
                            + register as u32
                            + (leaf as u32).saturating_mul(f.register_types.len() as u32 + 1),
                        projections: vec![],
                    },
                    unique,
                    suspended_parent: None,
                    referent_initialized: true,
                },
            })
            .collect();
    }
    states[0] = Some(entry);
    let mut work = VecDeque::from([0u32]);
    while let Some(pc) = work.pop_front() {
        let mut loans = states[pc as usize].clone().unwrap();
        let instruction = &a.code[start + pc as usize];
        let conflict = |register| VerifyError::BorrowConflict {
            function: fid,
            instruction: pc,
            register,
        };
        let whole = |owner| BorrowedPlace {
            owner,
            projections: vec![],
        };
        let conflicts = |place: &BorrowedPlace,
                         unique: bool,
                         ignored: Option<u32>,
                         loans: &[CarrierLoans]| {
            loans
                .iter()
                .enumerate()
                .filter(|(register, _)| Some(*register as u32) != ignored)
                .flat_map(|(_, loans)| loans)
                .any(|loan| places_overlap(place, &loan.loan.place) && (unique || loan.loan.unique))
        };
        let is_suspended = |register: u32, loans: &[CarrierLoans]| {
            loans
                .iter()
                .flatten()
                .any(|loan| loan.loan.suspended_parent == Some(register))
        };
        let end_reference = |loans: &mut [CarrierLoans], register: u32| {
            if loans[register as usize]
                .iter()
                .any(|loan| !loan.loan.referent_initialized)
            {
                return Err(conflict(register));
            }
            loans[register as usize].clear();
            Ok(())
        };
        let consume_owner = |loans: &[CarrierLoans], register: u32| {
            if conflicts(&whole(register), true, None, loans) || is_suspended(register, loans) {
                Err(conflict(register))
            } else {
                Ok(())
            }
        };
        match instruction {
            Instruction::BorrowShared { dst, src } => {
                let place = whole(*src);
                if conflicts(&place, false, None, &loans) {
                    return Err(conflict(*src));
                }
                loans[*dst as usize] = vec![CarrierLoan {
                    path: vec![],
                    loan: Loan {
                        place,
                        unique: false,
                        suspended_parent: None,
                        referent_initialized: true,
                    },
                }];
            }
            Instruction::BorrowUnique { dst, src } => {
                let place = whole(*src);
                if conflicts(&place, true, None, &loans) {
                    return Err(conflict(*src));
                }
                loans[*dst as usize] = vec![CarrierLoan {
                    path: vec![],
                    loan: Loan {
                        place,
                        unique: true,
                        suspended_parent: None,
                        referent_initialized: true,
                    },
                }];
            }
            Instruction::DerefCopy { src, .. } => {
                if is_suspended(*src, &loans)
                    || !matches!(loans[*src as usize].as_slice(), [loan] if loan.path.is_empty() && loan.loan.referent_initialized)
                {
                    return Err(conflict(*src));
                }
            }
            Instruction::DerefMove { src, .. } => {
                if is_suspended(*src, &loans) {
                    return Err(conflict(*src));
                }
                if loans[*src as usize].len() != 1 {
                    return Err(conflict(*src));
                }
                let loan = loans[*src as usize]
                    .as_mut_slice()
                    .first_mut()
                    .filter(|loan| {
                        loan.path.is_empty() && loan.loan.unique && loan.loan.referent_initialized
                    })
                    .ok_or_else(|| conflict(*src))?;
                loan.loan.referent_initialized = false;
            }
            Instruction::DerefStore { dst, src } => {
                if is_suspended(*dst, &loans) {
                    return Err(conflict(*dst));
                }
                let loan = loans[*dst as usize]
                    .as_mut_slice()
                    .first_mut()
                    .filter(|loan| {
                        loan.path.is_empty() && loan.loan.unique && !loan.loan.referent_initialized
                    })
                    .ok_or_else(|| conflict(*dst))?;
                loan.loan.referent_initialized = true;
                consume_owner(&loans, *src)?;
                end_reference(&mut loans, *src)?;
            }
            Instruction::ReborrowShared { dst, src } => {
                if is_suspended(*src, &loans) {
                    return Err(conflict(*src));
                }
                let source = loans[*src as usize]
                    .first()
                    .filter(|loan| {
                        loans[*src as usize].len() == 1
                            && loan.path.is_empty()
                            && loan.loan.referent_initialized
                    })
                    .cloned()
                    .ok_or(VerifyError::BorrowConflict {
                        function: fid,
                        instruction: pc,
                        register: *src,
                    })?;
                if conflicts(&source.loan.place, false, Some(*src), &loans) {
                    return Err(conflict(*src));
                }
                loans[*dst as usize] = vec![CarrierLoan {
                    path: vec![],
                    loan: Loan {
                        place: source.loan.place,
                        unique: false,
                        suspended_parent: source.loan.unique.then_some(*src),
                        referent_initialized: true,
                    },
                }];
            }
            Instruction::ReborrowUnique { dst, src } => {
                if is_suspended(*src, &loans) {
                    return Err(conflict(*src));
                }
                let source = loans[*src as usize]
                    .first()
                    .filter(|loan| {
                        loans[*src as usize].len() == 1
                            && loan.path.is_empty()
                            && loan.loan.unique
                            && loan.loan.referent_initialized
                    })
                    .cloned()
                    .ok_or(VerifyError::BorrowConflict {
                        function: fid,
                        instruction: pc,
                        register: *src,
                    })?;
                if conflicts(&source.loan.place, true, Some(*src), &loans) {
                    return Err(conflict(*src));
                }
                loans[*dst as usize] = vec![CarrierLoan {
                    path: vec![],
                    loan: Loan {
                        place: source.loan.place,
                        unique: true,
                        suspended_parent: Some(*src),
                        referent_initialized: true,
                    },
                }];
            }
            Instruction::EndBorrow { reference } => {
                if is_suspended(*reference, &loans) {
                    return Err(conflict(*reference));
                }
                end_reference(&mut loans, *reference)?;
            }
            Instruction::Move { dst, src } => {
                consume_owner(&loans, *src)?;
                loans[*dst as usize] = std::mem::take(&mut loans[*src as usize]);
                for loan in loans.iter_mut().flatten() {
                    if loan.loan.suspended_parent == Some(*src) {
                        loan.loan.suspended_parent = Some(*dst);
                    }
                }
            }
            Instruction::Copy { dst, src } => {
                if conflicts(&whole(*src), false, None, &loans) || is_suspended(*src, &loans) {
                    return Err(conflict(*src));
                }
                loans[*dst as usize] = loans[*src as usize].clone();
            }
            Instruction::Drop { register } => {
                if is_suspended(*register, &loans) {
                    if !matches!(
                        type_at(a, f.register_types[*register as usize])?,
                        Type::RefShared { .. } | Type::RefUnique { .. }
                    ) {
                        return Err(conflict(*register));
                    }
                    // Permanently consuming the parent cannot make it usable
                    // while a child reborrow remains live. The child keeps the
                    // underlying-place loan after the parent handle is retired.
                    for loan in loans.iter_mut().flatten() {
                        if loan.loan.suspended_parent == Some(*register) {
                            loan.loan.suspended_parent = None;
                        }
                    }
                }
                consume_owner(&loans, *register)?;
                end_reference(&mut loans, *register)?;
            }
            Instruction::Deconstruct { src: register }
            | Instruction::Return {
                src: Some(register),
            } => {
                consume_owner(&loans, *register)?;
                end_reference(&mut loans, *register)?;
            }
            Instruction::Construct {
                dst,
                ty,
                variant,
                fields,
            } => {
                let field_indices = construction_field_types(&a.types[*ty as usize], *variant)
                    .ok_or_else(|| conflict(*dst))?
                    .into_iter()
                    .enumerate()
                    .filter_map(|(field, ty)| {
                        (!matches!(type_at(a, ty), Ok(Type::Available { .. })))
                            .then_some(field as u32)
                    });
                let mut carried = Vec::new();
                for (&register, field) in fields.iter().zip(field_indices) {
                    carried.extend(loans[register as usize].iter().cloned().map(|mut loan| {
                        loan.path.insert(0, field);
                        loan
                    }));
                }
                carried.sort_by(|left, right| left.path.cmp(&right.path));
                for &register in fields {
                    consume_owner(&loans, register)?;
                    end_reference(&mut loans, register)?;
                }
                loans[*dst as usize] = carried;
            }
            Instruction::MakeCallable { dst, captures, .. } => {
                let carried = captures
                    .iter()
                    .flat_map(|register| loans[*register as usize].clone())
                    .collect::<Vec<_>>();
                for &register in captures {
                    consume_owner(&loans, register)?;
                    end_reference(&mut loans, register)?;
                }
                loans[*dst as usize] =
                    remap_carrier_loans(a, f.register_types[*dst as usize], carried, fid)?;
            }
            Instruction::TailResume {
                resumption,
                receiver_mode,
                value,
            } => {
                if *receiver_mode == 2 {
                    consume_owner(&loans, *resumption)?;
                    end_reference(&mut loans, *resumption)?;
                }
                consume_owner(&loans, *value)?;
                end_reference(&mut loans, *value)?;
            }
            Instruction::MakeHandler { dst, clauses, .. } => {
                let carried = clauses
                    .iter()
                    .flat_map(|register| loans[*register as usize].clone())
                    .collect::<Vec<_>>();
                for &register in clauses {
                    consume_owner(&loans, register)?;
                    end_reference(&mut loans, register)?;
                }
                loans[*dst as usize] =
                    remap_carrier_loans(a, f.register_types[*dst as usize], carried, fid)?;
            }
            Instruction::MakeHandlerShared { dst, captures, .. } => {
                // Preserve one carrier entry per structural reference leaf.
                // Several leaves may name the same shared loan; their paths in
                // the sealed environment remain distinct even though the
                // referent identity is shared. Unique aliases have already
                // been rejected by the snapshot/capture checks.
                let carried = captures
                    .iter()
                    .enumerate()
                    .flat_map(|(capture, register)| {
                        loans[*register as usize]
                            .clone()
                            .into_iter()
                            .map(move |mut loan| {
                                loan.path.insert(0, capture as u32);
                                loan
                            })
                    })
                    .collect::<Vec<_>>();
                for &register in captures {
                    consume_owner(&loans, register)?;
                    end_reference(&mut loans, register)?;
                }
                // MAKE_HANDLER_SHARED stores one physical environment, not
                // one copy of that environment beneath every clause callable
                // described by the nominal Handler type. Its carrier paths
                // therefore follow the capture tuple directly.
                loans[*dst as usize] = carried;
            }
            Instruction::MakeBindingPack { payloads, .. } => {
                for &register in payloads {
                    consume_owner(&loans, register)?;
                    end_reference(&mut loans, register)?;
                }
            }
            Instruction::Handle {
                dst,
                handler,
                body,
                args,
                ..
            } => {
                let result_has_references =
                    !reference_leaves(a, f.register_types[*dst as usize]).is_empty();
                let carried = if result_has_references {
                    std::iter::once(handler)
                        .chain(std::iter::once(body))
                        .chain(args.iter())
                        .flat_map(|register| loans[*register as usize].clone())
                        .collect::<Vec<_>>()
                } else {
                    Vec::new()
                };
                for register in std::iter::once(handler)
                    .chain(std::iter::once(body))
                    .chain(args.iter())
                {
                    consume_owner(&loans, *register)?;
                    end_reference(&mut loans, *register)?;
                }
                loans[*dst as usize] =
                    remap_carrier_loans(a, f.register_types[*dst as usize], carried, fid)?;
            }
            Instruction::Perform {
                dst,
                protocol,
                operation,
                payloads,
            } => {
                let result_leaves = dst.map_or_else(Vec::new, |dst| {
                    reference_leaves(a, f.register_types[dst as usize])
                });
                let mut carriers = payloads
                    .iter()
                    .filter(|payload| !loans[**payload as usize].is_empty());
                let carried = if result_leaves.is_empty() {
                    Vec::new()
                } else {
                    let payload = carriers.next().ok_or(VerifyError::InvalidFunction(fid))?;
                    if carriers.next().is_some() {
                        return Err(VerifyError::InvalidFunction(fid));
                    }
                    loans[*payload as usize].clone()
                };
                let operation = &a.protocols[*protocol as usize].operations[*operation as usize];
                if operation.resumption_upper.is_none_or(|upper| upper > 1)
                    && payloads
                        .iter()
                        .any(|payload| loans[*payload as usize].iter().any(|loan| loan.loan.unique))
                {
                    return Err(conflict(payloads[0]));
                }
                for &register in payloads {
                    consume_owner(&loans, register)?;
                    end_reference(&mut loans, register)?;
                }
                if let Some(dst) = dst {
                    loans[*dst as usize] =
                        remap_carrier_loans(a, f.register_types[*dst as usize], carried, fid)?;
                }
            }
            Instruction::HostCall { args, .. } => {
                for &register in args {
                    consume_owner(&loans, register)?;
                    end_reference(&mut loans, register)?;
                }
            }
            Instruction::TailCallKnownReceiver { receiver, args, .. } => {
                if is_suspended(*receiver, &loans) {
                    return Err(conflict(*receiver));
                }
                for &register in args {
                    consume_owner(&loans, register)?;
                    end_reference(&mut loans, register)?;
                }
            }
            Instruction::ProjectMove { dst, src, field } => {
                let place = BorrowedPlace {
                    owner: *src,
                    projections: vec![*field],
                };
                if conflicts(&place, true, None, &loans) {
                    return Err(conflict(*src));
                }
                let mut projected = Vec::new();
                loans[*src as usize].retain(|loan| {
                    if loan.path.first() == Some(field) {
                        let mut loan = loan.clone();
                        loan.path.remove(0);
                        projected.push(loan);
                        false
                    } else {
                        true
                    }
                });
                projected.sort_by(|left, right| left.path.cmp(&right.path));
                loans[*dst as usize] = projected;
            }
            Instruction::ProjectCopy { dst, src, field } => {
                let place = BorrowedPlace {
                    owner: *src,
                    projections: vec![*field],
                };
                if conflicts(&place, false, None, &loans) {
                    return Err(conflict(*src));
                }
                let mut projected = loans[*src as usize]
                    .iter()
                    .filter(|loan| loan.path.first() == Some(field))
                    .cloned()
                    .map(|mut loan| {
                        loan.path.remove(0);
                        loan
                    })
                    .collect::<Vec<_>>();
                if projected.is_empty()
                    && *src == 0
                    && matches!(f.receiver_mode, Some(0 | 1))
                    && let [root] = loans[*src as usize].as_slice()
                    && root.path.is_empty()
                {
                    // A borrowed receiver register carries the whole external
                    // environment reference, while PROJECT_COPY addresses a
                    // field inside its referent. Materialize the destination's
                    // structural reference leaves from that authenticated root
                    // instead of losing them merely because the carrier itself
                    // has no aggregate field path.
                    projected = reference_leaves(a, f.register_types[*dst as usize])
                        .into_iter()
                        .map(|(path, unique)| {
                            let mut place = root.loan.place.clone();
                            place.projections.push(*field);
                            place.projections.extend(path.iter().copied());
                            CarrierLoan {
                                path,
                                loan: Loan {
                                    place,
                                    unique,
                                    suspended_parent: root.loan.suspended_parent,
                                    referent_initialized: root.loan.referent_initialized,
                                },
                            }
                        })
                        .collect();
                }
                if projected.iter().any(|loan| loan.loan.unique) {
                    return Err(conflict(*src));
                }
                projected.sort_by(|left, right| left.path.cmp(&right.path));
                loans[*dst as usize] = projected;
            }
            Instruction::Switch { discr: src, .. } => {
                if conflicts(&whole(*src), false, None, &loans) {
                    return Err(conflict(*src));
                }
            }
            Instruction::ProjectBorrowShared { dst, src, field }
            | Instruction::ProjectBorrowUnique { dst, src, field } => {
                let unique = matches!(instruction, Instruction::ProjectBorrowUnique { .. });
                let inherited = loans[*src as usize]
                    .first()
                    .filter(|_| loans[*src as usize].len() == 1)
                    .cloned();
                if inherited
                    .as_ref()
                    .is_some_and(|loan| !loan.loan.referent_initialized)
                {
                    return Err(conflict(*src));
                }
                let mut place = inherited
                    .as_ref()
                    .map_or_else(|| whole(*src), |loan| loan.loan.place.clone());
                place.projections.push(*field);
                // A nested projection through a reference is a descendant
                // access authorized by that reference's whole carrier chain.
                // The source may already be suspended by another child: the
                // exact place comparison below admits a statically disjoint
                // sibling while rejecting an overlapping child. Every carrier
                // in the chain names the same root place and would otherwise
                // conflict with the child it is authorizing. Exempt only those
                // exact carriers; unrelated aliases still conflict.
                let mut authorized = std::collections::BTreeSet::new();
                if inherited.is_some() {
                    let mut carrier = Some(*src);
                    while let Some(register) = carrier {
                        if !authorized.insert(register) {
                            break;
                        }
                        carrier = loans[register as usize]
                            .first()
                            .filter(|_| loans[register as usize].len() == 1)
                            .and_then(|loan| loan.loan.suspended_parent);
                    }
                }
                let has_conflict = loans
                    .iter()
                    .enumerate()
                    .filter(|(register, _)| !authorized.contains(&(*register as u32)))
                    .flat_map(|(_, loans)| loans)
                    .any(|loan| {
                        places_overlap(&place, &loan.loan.place) && (unique || loan.loan.unique)
                    });
                if has_conflict {
                    return Err(conflict(*src));
                }
                loans[*dst as usize] = vec![CarrierLoan {
                    path: vec![],
                    loan: Loan {
                        place,
                        unique,
                        suspended_parent: inherited
                            .as_ref()
                            .is_some_and(|loan| loan.loan.unique)
                            .then_some(*src),
                        referent_initialized: true,
                    },
                }];
            }
            Instruction::EnumTag { src, .. } => {
                if conflicts(&whole(*src), false, None, &loans) {
                    return Err(conflict(*src));
                }
            }
            Instruction::Primitive { dst, op, args } => {
                let exact_index = || {
                    args.get(1)
                        .and_then(|register| constants[pc as usize][*register as usize])
                };
                let array_owner = || {
                    let reference = *args.first()?;
                    let [loan] = loans[reference as usize].as_slice() else {
                        return None;
                    };
                    (loan.path.is_empty()
                        && loan.loan.referent_initialized
                        && (loan.loan.place.owner as usize) < loans.len())
                    .then_some(loan.loan.place.owner)
                };
                let mut transported = None::<CarrierLoans>;
                match op {
                    Primitive::ArraySetMove => {
                        if let Some(owner) = array_owner() {
                            let index = exact_index().ok_or_else(|| conflict(args[0]))?;
                            let item = *args.get(2).ok_or(VerifyError::InvalidFunction(fid))?;
                            let mut carried = loans[item as usize].clone();
                            for loan in &mut carried {
                                loan.path = array_slot_path(index, loan.path.clone())
                                    .ok_or_else(|| conflict(args[0]))?;
                            }
                            if loans[owner as usize].iter().any(|loan| {
                                split_array_slot_path(&loan.path)
                                    .is_some_and(|(candidate, _)| candidate == index)
                            }) {
                                return Err(conflict(args[0]));
                            }
                            loans[owner as usize].extend(carried);
                        }
                    }
                    Primitive::ArrayPushMove => {
                        if let Some(owner) = array_owner() {
                            let item = *args.get(1).ok_or(VerifyError::InvalidFunction(fid))?;
                            let index = loans[owner as usize]
                                .iter()
                                .filter_map(|loan| {
                                    split_array_slot_path(&loan.path).map(|slot| slot.0)
                                })
                                .max()
                                .map_or(Some(0), |index| index.checked_add(1))
                                .ok_or_else(|| conflict(args[0]))?;
                            let mut carried = loans[item as usize].clone();
                            for loan in &mut carried {
                                loan.path = array_slot_path(index, loan.path.clone())
                                    .ok_or_else(|| conflict(args[0]))?;
                            }
                            loans[owner as usize].extend(carried);
                        }
                    }
                    Primitive::ArrayGetCopy | Primitive::ArrayGetMove => {
                        if !reference_leaves(a, f.register_types[*dst as usize]).is_empty() {
                            let index = exact_index().ok_or_else(|| conflict(args[0]))?;
                            let mut carried = Vec::new();
                            if let Some(owner) = array_owner() {
                                loans[owner as usize].retain(|loan| {
                                    let Some((candidate, element_path)) =
                                        split_array_slot_path(&loan.path)
                                    else {
                                        return true;
                                    };
                                    if candidate != index {
                                        return true;
                                    }
                                    let mut loan = loan.clone();
                                    loan.path = element_path.to_vec();
                                    carried.push(loan);
                                    matches!(op, Primitive::ArrayGetCopy)
                                });
                            } else if let Some(reference) = args.first()
                                && let [array_loan] = loans[*reference as usize].as_slice()
                            {
                                carried = reference_leaves(a, f.register_types[*dst as usize])
                                    .into_iter()
                                    .map(|(path, unique)| {
                                        let mut loan = array_loan.clone();
                                        loan.path = path.clone();
                                        loan.loan.place.projections.extend(
                                            array_slot_path(index, path)
                                                .unwrap_or_else(|| vec![ARRAY_SLOT_PATH]),
                                        );
                                        loan.loan.unique = unique;
                                        loan
                                    })
                                    .collect();
                            }
                            if carried.is_empty()
                                || matches!(op, Primitive::ArrayGetCopy)
                                    && carried.iter().any(|loan| loan.loan.unique)
                            {
                                return Err(conflict(args[0]));
                            }
                            transported = Some(remap_carrier_loans(
                                a,
                                f.register_types[*dst as usize],
                                carried,
                                fid,
                            )?);
                        }
                    }
                    Primitive::ArrayPopMove => {
                        if !reference_leaves(a, f.register_types[*dst as usize]).is_empty() {
                            let mut carried = Vec::new();
                            if let Some(owner) = array_owner() {
                                let index = loans[owner as usize]
                                    .iter()
                                    .filter_map(|loan| {
                                        split_array_slot_path(&loan.path).map(|slot| slot.0)
                                    })
                                    .max()
                                    .ok_or_else(|| conflict(args[0]))?;
                                loans[owner as usize].retain(|loan| {
                                    let Some((candidate, element_path)) =
                                        split_array_slot_path(&loan.path)
                                    else {
                                        return true;
                                    };
                                    if candidate != index {
                                        return true;
                                    }
                                    let mut loan = loan.clone();
                                    loan.path = element_path.to_vec();
                                    carried.push(loan);
                                    false
                                });
                            } else if let Some(reference) = args.first()
                                && let [array_loan] = loans[*reference as usize].as_slice()
                            {
                                carried = reference_leaves(a, f.register_types[*dst as usize])
                                    .into_iter()
                                    .map(|(path, unique)| {
                                        let mut loan = array_loan.clone();
                                        loan.path = path.clone();
                                        loan.loan
                                            .place
                                            .projections
                                            .extend(array_last_slot_path(path));
                                        loan.loan.unique = unique;
                                        loan
                                    })
                                    .collect();
                            }
                            transported = Some(remap_carrier_loans(
                                a,
                                f.register_types[*dst as usize],
                                carried,
                                fid,
                            )?);
                        }
                    }
                    Primitive::ArrayFinishDrained => {
                        let owner = *args.first().ok_or(VerifyError::InvalidFunction(fid))?;
                        if loans[owner as usize]
                            .iter()
                            .any(|loan| split_array_slot_path(&loan.path).is_some())
                        {
                            return Err(conflict(owner));
                        }
                    }
                    _ => {}
                }
                let inherited = if matches!(
                    op,
                    Primitive::ArrayGetBorrowShared | Primitive::ArrayGetBorrowUnique
                ) {
                    args.first().and_then(|register| {
                        (loans[*register as usize].len() == 1)
                            .then(|| loans[*register as usize][0].clone())
                    })
                } else {
                    None
                };
                for &register in args {
                    consume_owner(&loans, register)?;
                    end_reference(&mut loans, register)?;
                }
                if let Some(mut loan) = inherited {
                    loan.loan.unique = matches!(op, Primitive::ArrayGetBorrowUnique);
                    loan.loan.place.projections.push(u32::MAX);
                    loan.path.clear();
                    loans[*dst as usize] = vec![loan];
                } else if let Some(transported) = transported {
                    loans[*dst as usize] = transported;
                }
            }
            Instruction::Call {
                dst,
                function,
                args,
            } => {
                let installed_writes = array_write_effects(a, *function)
                    .and_then(|effects| {
                        instantiate_array_write_loans(&effects, args, &loans, *function)
                    })
                    .unwrap_or_default();
                let result_leaves = dst.map_or_else(Vec::new, |dst| {
                    reference_leaves(a, f.register_types[dst as usize])
                });
                let callee_has_multi_leaf_parameter = a.functions[*function as usize]
                    .params
                    .iter()
                    .any(|ty| reference_leaves(a, *ty).len() > 1);
                let array_contract = (!result_leaves.is_empty())
                    .then(|| aggregate_reference_return_origins(a, *function, &mut Vec::new()))
                    .and_then(Result::ok)
                    .filter(|contract| {
                        contract.iter().any(|(_, origin)| {
                            matches!(origin, CarrierOrigin::Parameter { path, .. } if split_array_slot_path(path).is_some())
                        })
                    });
                let mut returned_loans = if let Some(contract) = array_contract {
                    let callee_copies = function_code(a, &a.functions[*function as usize])?
                        .iter()
                        .any(|instruction| {
                            matches!(
                                instruction,
                                Instruction::Primitive {
                                    op: Primitive::ArrayGetCopy,
                                    ..
                                }
                            )
                        });
                    let mut returned = Vec::new();
                    for (result_path, origin) in contract {
                        let CarrierOrigin::Parameter { parameter, path } = origin else {
                            return Err(VerifyError::InvalidFunction(*function));
                        };
                        let argument = *args
                            .get(parameter)
                            .ok_or(VerifyError::InvalidFunction(*function))?;
                        let [array_reference] = loans[argument as usize].as_slice() else {
                            return Err(VerifyError::InvalidFunction(*function));
                        };
                        let owner = array_reference.loan.place.owner;
                        if owner as usize >= loans.len() {
                            let mut loan = array_reference.clone();
                            loan.path = result_path;
                            loan.loan.place.projections.extend(path);
                            loan.loan.unique = result_leaves
                                .iter()
                                .find(|(candidate, _)| candidate == &loan.path)
                                .is_some_and(|(_, unique)| *unique);
                            returned.push(loan);
                            continue;
                        }
                        let (requested, element_path) = split_array_slot_path(&path)
                            .ok_or(VerifyError::InvalidFunction(*function))?;
                        let selected = if requested == u64::from(ARRAY_SLOT_PATH) {
                            loans[owner as usize]
                                .iter()
                                .filter_map(|loan| {
                                    split_array_slot_path(&loan.path).map(|slot| slot.0)
                                })
                                .max()
                                .ok_or(VerifyError::InvalidFunction(*function))?
                        } else {
                            requested
                        };
                        let position = loans[owner as usize]
                            .iter()
                            .position(|loan| {
                                split_array_slot_path(&loan.path).is_some_and(
                                    |(slot, candidate)| {
                                        slot == selected && candidate == element_path
                                    },
                                )
                            })
                            .ok_or(VerifyError::InvalidFunction(*function))?;
                        let mut loan = if callee_copies {
                            loans[owner as usize][position].clone()
                        } else {
                            loans[owner as usize].remove(position)
                        };
                        loan.path = result_path;
                        returned.push(loan);
                    }
                    returned.sort_by(|left, right| left.path.cmp(&right.path));
                    returned
                } else if result_leaves.len() > 1
                    || (!result_leaves.is_empty() && callee_has_multi_leaf_parameter)
                {
                    let contract =
                        aggregate_reference_return_origins(a, *function, &mut Vec::new())?;
                    let mut returned = Vec::new();
                    for (result_path, origin) in contract {
                        let CarrierOrigin::Parameter { parameter, path } = origin else {
                            return Err(VerifyError::InvalidFunction(*function));
                        };
                        let argument = *args
                            .get(parameter)
                            .ok_or(VerifyError::InvalidFunction(*function))?;
                        let mut loan = loans[argument as usize]
                            .iter()
                            .find(|loan| loan.path == path)
                            .cloned()
                            .ok_or(VerifyError::InvalidFunction(*function))?;
                        loan.path = result_path;
                        returned.push(loan);
                    }
                    returned.sort_by(|left, right| left.path.cmp(&right.path));
                    returned
                } else if let Some(dst) = dst
                    && single_reference_leaf(a, f.register_types[*dst as usize]).is_some()
                {
                    let Some(ReferenceOrigin::Parameter(parameter)) =
                        reference_return_parameter(a, *function, &mut Vec::new())?
                    else {
                        return Err(VerifyError::InvalidFunction(*function));
                    };
                    args.get(parameter)
                        .and_then(|argument| {
                            (loans[*argument as usize].len() == 1)
                                .then(|| loans[*argument as usize][0].clone())
                        })
                        .ok_or(VerifyError::InvalidFunction(*function))
                        .map(|loan| vec![loan])?
                } else {
                    Vec::new()
                };
                if let [(path, unique)] = result_leaves.as_slice()
                    && let [loan] = returned_loans.as_mut_slice()
                {
                    loan.path = path.clone();
                    loan.loan.unique = *unique;
                }
                for &register in args {
                    consume_owner(&loans, register)?;
                    end_reference(&mut loans, register)?;
                }
                for (owner, loan) in installed_writes {
                    loans[owner as usize].push(loan);
                    loans[owner as usize].sort_by(|left, right| left.path.cmp(&right.path));
                }
                if let Some(dst) = dst {
                    loans[*dst as usize] = returned_loans;
                }
            }
            Instruction::CallSelf { dst, args } => {
                if is_suspended(0, &loans) {
                    return Err(conflict(0));
                }
                let returned = if let Some(dst) = dst
                    && single_reference_leaf(a, f.register_types[*dst as usize]).is_some()
                {
                    match reference_return_parameter(a, fid, &mut Vec::new())? {
                        Some(ReferenceOrigin::Parameter(parameter)) => args
                            .get(parameter)
                            .and_then(|argument| loans[*argument as usize].first())
                            .cloned()
                            .map(|loan| vec![loan])
                            .ok_or(VerifyError::InvalidFunction(fid))?,
                        Some(ReferenceOrigin::Receiver) => loans[0].clone(),
                        _ => return Err(VerifyError::InvalidFunction(fid)),
                    }
                } else {
                    Vec::new()
                };
                for &register in args {
                    consume_owner(&loans, register)?;
                    end_reference(&mut loans, register)?;
                }
                if let Some(dst) = dst {
                    loans[*dst as usize] = returned;
                }
            }
            Instruction::CallKnownReceiver {
                dst,
                function,
                receiver,
                args,
            } => {
                if is_suspended(*receiver, &loans) {
                    return Err(conflict(*receiver));
                }
                let returned = if let Some(dst) = dst
                    && single_reference_leaf(a, f.register_types[*dst as usize]).is_some()
                {
                    match reference_return_parameter(a, *function, &mut Vec::new())? {
                        Some(ReferenceOrigin::Parameter(parameter)) => args
                            .get(parameter)
                            .and_then(|argument| loans[*argument as usize].first())
                            .cloned()
                            .map(|loan| vec![loan])
                            .ok_or(VerifyError::InvalidFunction(*function))?,
                        Some(ReferenceOrigin::Receiver) => loans[*receiver as usize].clone(),
                        _ => return Err(VerifyError::InvalidFunction(*function)),
                    }
                } else {
                    Vec::new()
                };
                for &register in args {
                    consume_owner(&loans, register)?;
                    end_reference(&mut loans, register)?;
                }
                if let Some(dst) = dst {
                    loans[*dst as usize] = returned;
                }
            }
            Instruction::CallIndirect {
                dst,
                callable,
                receiver_mode,
                args,
            } => {
                let result_leaves = dst.map_or_else(Vec::new, |dst| {
                    reference_leaves(a, f.register_types[dst as usize])
                });
                let mut returned_loans = if result_leaves.len() > 1 {
                    let targets = &callable_targets[pc as usize][*callable as usize];
                    let contract = canonical_callable_carrier_contract(a, targets, &mut Vec::new())
                        .map_err(|_| VerifyError::InvalidFunction(fid))?;
                    let mut returned = Vec::new();
                    for (result_path, origin) in contract {
                        let (source_register, path) = match origin {
                            CarrierOrigin::Parameter { parameter, path } => (
                                *args
                                    .get(parameter)
                                    .ok_or(VerifyError::InvalidFunction(fid))?,
                                path,
                            ),
                            CarrierOrigin::Receiver { path } => (*callable, path),
                            CarrierOrigin::Local => {
                                return Err(VerifyError::InvalidFunction(fid));
                            }
                        };
                        let mut loan = loans[source_register as usize]
                            .iter()
                            .find(|loan| loan.path == path)
                            .cloned()
                            .ok_or(VerifyError::InvalidFunction(fid))?;
                        loan.path = result_path;
                        returned.push(loan);
                    }
                    returned.sort_by(|left, right| left.path.cmp(&right.path));
                    returned
                } else if let Some(dst) = dst
                    && single_reference_leaf(a, f.register_types[*dst as usize]).is_some()
                {
                    let targets = &callable_targets[pc as usize][*callable as usize];
                    if targets.is_empty() {
                        let candidates = args
                            .iter()
                            .filter(|argument| loans[**argument as usize].len() == 1)
                            .map(|argument| loans[*argument as usize][0].clone())
                            .collect::<Vec<_>>();
                        (candidates.len() == 1)
                            .then(|| candidates[0].clone())
                            .ok_or(VerifyError::InvalidFunction(fid))
                            .map(|loan| vec![loan])?
                    } else {
                        match canonical_callable_reference_contract(a, targets, &mut Vec::new())
                            .map_err(|_| VerifyError::InvalidFunction(fid))?
                        {
                            Some(ReferenceOrigin::Parameter(parameter)) => args
                                .get(parameter)
                                .and_then(|argument| loans[*argument as usize].first())
                                .cloned()
                                .map(|loan| vec![loan])
                                .ok_or(VerifyError::InvalidFunction(fid))?,
                            Some(ReferenceOrigin::Receiver) => loans[*callable as usize].clone(),
                            Some(ReferenceOrigin::Local) | None => {
                                return Err(VerifyError::InvalidFunction(fid));
                            }
                        }
                    }
                } else {
                    Vec::new()
                };
                if *receiver_mode == 2 {
                    consume_owner(&loans, *callable)?;
                    end_reference(&mut loans, *callable)?;
                } else {
                    let unique = *receiver_mode == 1;
                    if conflicts(&whole(*callable), unique, None, &loans)
                        || is_suspended(*callable, &loans)
                    {
                        return Err(conflict(*callable));
                    }
                }
                for &register in args {
                    consume_owner(&loans, register)?;
                    end_reference(&mut loans, register)?;
                }
                if let Some(dst) = dst {
                    if let ([(path, unique)], [loan]) =
                        (result_leaves.as_slice(), returned_loans.as_mut_slice())
                    {
                        loan.path = path.clone();
                        loan.loan.unique = *unique;
                    }
                    loans[*dst as usize] = returned_loans;
                }
            }
            Instruction::TailCall { args, .. } => {
                for &register in args {
                    consume_owner(&loans, register)?;
                    end_reference(&mut loans, register)?;
                }
            }
            Instruction::TailCallSelf { args } => {
                if is_suspended(0, &loans) {
                    return Err(conflict(0));
                }
                consume_owner(&loans, 0)?;
                end_reference(&mut loans, 0)?;
                for &register in args {
                    consume_owner(&loans, register)?;
                    end_reference(&mut loans, register)?;
                }
            }
            Instruction::TailCallIndirect { callable, args, .. } => {
                consume_owner(&loans, *callable)?;
                end_reference(&mut loans, *callable)?;
                for &register in args {
                    consume_owner(&loans, register)?;
                    end_reference(&mut loans, register)?;
                }
            }
            Instruction::Resume {
                dst,
                resumption,
                receiver_mode,
                value,
            } => {
                let carried = loans[*value as usize].clone();
                if *receiver_mode == 2 {
                    consume_owner(&loans, *resumption)?;
                    end_reference(&mut loans, *resumption)?;
                }
                consume_owner(&loans, *value)?;
                end_reference(&mut loans, *value)?;
                loans[*dst as usize] =
                    remap_carrier_loans(a, f.register_types[*dst as usize], carried, fid)?;
            }
            Instruction::Cancel { resumption, .. } => {
                consume_owner(&loans, *resumption)?;
                end_reference(&mut loans, *resumption)?;
            }
            Instruction::Leave { slot, value } => {
                let entry = label_states[pc as usize]
                    .iter()
                    .rfind(|entry| entry.slot == *slot)
                    .ok_or(VerifyError::InvalidFunction(fid))?;
                consume_owner(&loans, *value)?;
                let protected = std::mem::take(&mut loans[*value as usize]);
                for register in cleanup_prefix(a, fid, pc, entry.target)? {
                    consume_owner(&loans, *register)?;
                    end_reference(&mut loans, *register)?;
                }
                loans[entry.result_register as usize] = protected;
            }
            Instruction::Nop
            | Instruction::Return { src: None }
            | Instruction::Const { .. }
            | Instruction::Jump { .. }
            | Instruction::LabelPush { .. }
            | Instruction::LabelPop { .. }
            | Instruction::Unreachable
            | Instruction::Abort { .. } => {}
        }
        let successors: Vec<u32> = match instruction {
            Instruction::Jump { target } => vec![*target],
            Instruction::Leave { slot, .. } => vec![
                label_states[pc as usize]
                    .iter()
                    .rfind(|entry| entry.slot == *slot)
                    .ok_or(VerifyError::InvalidFunction(fid))?
                    .target,
            ],
            Instruction::Switch {
                cases, otherwise, ..
            } => cases
                .iter()
                .map(|case| case.1)
                .chain(std::iter::once(*otherwise))
                .collect(),
            Instruction::Return { .. }
            | Instruction::TailCall { .. }
            | Instruction::TailCallSelf { .. }
            | Instruction::TailCallKnownReceiver { .. }
            | Instruction::TailCallIndirect { .. }
            | Instruction::TailResume { .. }
            | Instruction::Perform { dst: None, .. }
            | Instruction::Unreachable
            | Instruction::Abort { .. } => vec![],
            _ => vec![pc + 1],
        };
        for successor in successors {
            match &mut states[successor as usize] {
                Some(old) => {
                    let mut changed = false;
                    for register in 0..old.len() {
                        if old[register] == loans[register] {
                            continue;
                        }
                        if !old[register].is_empty() && loans[register].is_empty() {
                            continue;
                        }
                        if old[register].is_empty() && !loans[register].is_empty() {
                            old[register] = loans[register].clone();
                            changed = true;
                            continue;
                        }
                        return Err(VerifyError::StateMismatch {
                            function: fid,
                            instruction: successor,
                        });
                    }
                    if changed {
                        work.push_back(successor);
                    }
                }
                None => {
                    states[successor as usize] = Some(loans.clone());
                    work.push_back(successor);
                }
            }
        }
    }
    Ok(states
        .into_iter()
        .map(|state| state.unwrap_or_else(|| vec![Vec::new(); f.register_types.len()]))
        .collect())
}

fn shape(
    a: &Artifact,
    fid: u32,
    pc: u32,
    f: &Function,
    i: &Instruction,
) -> Result<(), VerifyError> {
    let reg = |r| {
        if (r as usize) < f.register_types.len() {
            Ok(())
        } else {
            Err(VerifyError::InvalidRegister {
                function: fid,
                instruction: pc,
                register: r,
            })
        }
    };
    let target = |t| {
        if t < f.code_len {
            Ok(())
        } else {
            Err(VerifyError::InvalidTarget {
                function: fid,
                instruction: pc,
                target: t,
            })
        }
    };
    match i {
        Instruction::Nop => {}
        Instruction::Const { dst, constant } => {
            reg(*dst)?;
            if *constant as usize >= a.constants.len() {
                return Err(VerifyError::InvalidConstant(*constant));
            }
        }
        Instruction::Move { dst, src } | Instruction::Copy { dst, src } => {
            reg(*dst)?;
            reg(*src)?;
        }
        Instruction::BorrowShared { dst, src } | Instruction::BorrowUnique { dst, src } => {
            reg(*dst)?;
            reg(*src)?;
        }
        Instruction::ReborrowShared { dst, src }
        | Instruction::ReborrowUnique { dst, src }
        | Instruction::DerefCopy { dst, src }
        | Instruction::DerefMove { dst, src }
        | Instruction::DerefStore { dst, src } => {
            reg(*dst)?;
            reg(*src)?;
        }
        Instruction::EndBorrow { reference } => reg(*reference)?,
        Instruction::Construct {
            dst, ty, fields, ..
        } => {
            reg(*dst)?;
            type_at(a, *ty)?;
            for &r in fields {
                reg(r)?;
            }
        }
        Instruction::ProjectMove { dst, src, .. } | Instruction::ProjectCopy { dst, src, .. } => {
            reg(*dst)?;
            reg(*src)?;
        }
        Instruction::ProjectBorrowShared { dst, src, .. }
        | Instruction::ProjectBorrowUnique { dst, src, .. }
        | Instruction::EnumTag { dst, src } => {
            reg(*dst)?;
            reg(*src)?;
        }
        Instruction::Drop { register } | Instruction::Deconstruct { src: register } => {
            reg(*register)?
        }
        Instruction::Primitive { dst, args, .. } => {
            reg(*dst)?;
            for &r in args {
                reg(r)?;
            }
        }
        Instruction::Jump { target: t } => target(*t)?,
        Instruction::Switch {
            discr,
            cases,
            otherwise,
        } => {
            reg(*discr)?;
            target(*otherwise)?;
            for &(c, t) in cases {
                if c as usize >= a.constants.len() {
                    return Err(VerifyError::InvalidConstant(c));
                }
                target(t)?;
            }
        }
        Instruction::Call {
            dst,
            function,
            args,
        } => {
            if let Some(dst) = dst {
                reg(*dst)?;
            }
            if *function as usize >= a.functions.len() {
                return Err(VerifyError::InvalidFunction(*function));
            }
            if dst.is_none()
                && !matches!(
                    type_at(a, a.functions[*function as usize].return_type)?,
                    Type::Unit | Type::Never
                )
            {
                return Err(VerifyError::InvalidFunction(*function));
            }
            for &r in args {
                reg(r)?;
            }
        }
        Instruction::TailCall { function, args } => {
            if *function as usize >= a.functions.len() {
                return Err(VerifyError::InvalidFunction(*function));
            }
            for &r in args {
                reg(r)?;
            }
        }
        Instruction::CallSelf { dst, args } => {
            if !matches!(f.receiver_mode, Some(0 | 1)) {
                return Err(VerifyError::InvalidFunction(fid));
            }
            if let Some(dst) = dst {
                reg(*dst)?;
            } else if !matches!(type_at(a, f.return_type)?, Type::Unit | Type::Never) {
                return Err(VerifyError::InvalidFunction(fid));
            }
            for &r in args {
                reg(r)?;
            }
        }
        Instruction::CallKnownReceiver {
            dst,
            function,
            receiver,
            args,
        } => {
            if let Some(dst) = dst {
                reg(*dst)?;
            }
            reg(*receiver)?;
            if *function as usize >= a.functions.len() {
                return Err(VerifyError::InvalidFunction(*function));
            }
            if dst.is_none()
                && !matches!(
                    type_at(a, a.functions[*function as usize].return_type)?,
                    Type::Unit | Type::Never
                )
            {
                return Err(VerifyError::InvalidFunction(*function));
            }
            for &r in args {
                reg(r)?;
            }
        }
        Instruction::TailCallKnownReceiver {
            function,
            receiver,
            args,
        } => {
            reg(*receiver)?;
            if *function as usize >= a.functions.len() {
                return Err(VerifyError::InvalidFunction(*function));
            }
            for &r in args {
                reg(r)?;
            }
        }
        Instruction::TailCallSelf { args } => {
            if f.receiver_mode.is_none() {
                return Err(VerifyError::InvalidFunction(fid));
            }
            for &r in args {
                reg(r)?;
            }
        }
        Instruction::MakeCallable {
            dst,
            callable_type,
            function,
            captures,
        } => {
            reg(*dst)?;
            if !matches!(type_at(a, *callable_type)?, Type::Callable { .. }) {
                return Err(VerifyError::InvalidType(*callable_type));
            }
            if *function as usize >= a.functions.len() {
                return Err(VerifyError::InvalidFunction(*function));
            }
            for &capture in captures {
                reg(capture)?;
            }
        }
        Instruction::MakeHandler {
            dst,
            handler_def,
            clauses,
        } => {
            reg(*dst)?;
            if *handler_def as usize >= a.handler_defs.len() {
                return Err(VerifyError::InvalidType(*handler_def));
            }
            for &clause in clauses {
                reg(clause)?;
            }
        }
        Instruction::MakeHandlerShared {
            dst,
            handler_def,
            functions,
            captures,
        } => {
            reg(*dst)?;
            if *handler_def as usize >= a.handler_defs.len() {
                return Err(VerifyError::InvalidType(*handler_def));
            }
            for function in functions {
                if *function as usize >= a.functions.len() {
                    return Err(VerifyError::InvalidFunction(*function));
                }
            }
            for &capture in captures {
                reg(capture)?;
            }
        }
        Instruction::MakeBindingPack {
            dst,
            binding_type,
            payloads,
        } => {
            reg(*dst)?;
            if !matches!(type_at(a, *binding_type)?, Type::BindingPack { .. }) {
                return Err(VerifyError::InvalidType(*binding_type));
            }
            for &payload in payloads {
                reg(payload)?;
            }
        }
        Instruction::CallIndirect {
            dst,
            callable,
            receiver_mode,
            args,
        } => {
            if let Some(dst) = dst {
                reg(*dst)?;
            }
            reg(*callable)?;
            if dst.is_none() {
                let Type::Callable { signature, .. } =
                    type_at(a, f.register_types[*callable as usize])?
                else {
                    return Err(VerifyError::InvalidFunction(fid));
                };
                if !matches!(type_at(a, signature.result)?, Type::Unit | Type::Never) {
                    return Err(VerifyError::InvalidFunction(fid));
                }
            }
            let Type::Callable {
                receiver_mode: described_mode,
                ..
            } = type_at(a, f.register_types[*callable as usize])?
            else {
                return Err(VerifyError::InvalidFunction(fid));
            };
            if *receiver_mode > 2 || *receiver_mode < *described_mode {
                return Err(VerifyError::InvalidFunction(fid));
            }
            for &argument in args {
                reg(argument)?;
            }
        }
        Instruction::TailCallIndirect {
            callable,
            receiver_mode,
            args,
        } => {
            reg(*callable)?;
            let Type::Callable {
                receiver_mode: described_mode,
                ..
            } = type_at(a, f.register_types[*callable as usize])?
            else {
                return Err(VerifyError::InvalidFunction(fid));
            };
            if *receiver_mode != 2 || *receiver_mode < *described_mode {
                return Err(VerifyError::InvalidFunction(fid));
            }
            for &argument in args {
                reg(argument)?;
            }
        }
        Instruction::Handle {
            dst,
            handler,
            body,
            args,
        } => {
            reg(*dst)?;
            reg(*handler)?;
            reg(*body)?;
            for &argument in args {
                reg(argument)?;
            }
        }
        Instruction::Perform {
            dst,
            protocol,
            operation,
            payloads,
        } => {
            if let Some(dst) = dst {
                reg(*dst)?;
            }
            if a.protocols
                .get(*protocol as usize)
                .and_then(|protocol| protocol.operations.get(*operation as usize))
                .is_none()
            {
                return Err(VerifyError::InvalidType(*protocol));
            }
            for &payload in payloads {
                reg(payload)?;
            }
        }
        Instruction::Resume {
            dst,
            resumption,
            receiver_mode,
            value,
        } => {
            reg(*dst)?;
            reg(*resumption)?;
            reg(*value)?;
            if *receiver_mode > 2 {
                return Err(VerifyError::InvalidFunction(fid));
            }
        }
        Instruction::Cancel { dst, resumption } => {
            reg(*dst)?;
            reg(*resumption)?;
        }
        Instruction::HostCall { dst, import, args } => {
            if let Some(dst) = dst {
                reg(*dst)?;
            }
            let signature = &a
                .imports
                .get(*import as usize)
                .ok_or(VerifyError::InvalidFunction(fid))?
                .signature;
            if dst.is_none() && !matches!(type_at(a, signature.result)?, Type::Unit | Type::Never) {
                return Err(VerifyError::InvalidFunction(fid));
            }
            for &argument in args {
                reg(argument)?;
            }
        }
        Instruction::LabelPush {
            slot,
            result_register,
            target: label_target,
        } => {
            if *slot >= f.label_slot_count {
                return Err(VerifyError::InvalidFunction(fid));
            }
            reg(*result_register)?;
            target(*label_target)?;
        }
        Instruction::LabelPop { slot } => {
            if *slot >= f.label_slot_count {
                return Err(VerifyError::InvalidFunction(fid));
            }
        }
        Instruction::Leave { slot, value } => {
            if *slot >= f.label_slot_count {
                return Err(VerifyError::InvalidFunction(fid));
            }
            reg(*value)?;
        }
        Instruction::TailResume {
            resumption, value, ..
        } => {
            reg(*resumption)?;
            reg(*value)?;
        }
        Instruction::Return { src } => {
            if let Some(src) = src {
                reg(*src)?;
            } else if f.return_type != crate::bytecode::UNIT {
                return Err(VerifyError::InvalidFunction(fid));
            }
        }
        Instruction::Unreachable | Instruction::Abort { .. } => {}
    }
    Ok(())
}

struct TransferContext<'a> {
    artifact: &'a Artifact,
    function_id: u32,
    pc: u32,
    function: &'a Function,
    enum_variants: &'a [Option<u32>],
    move_paths: &'a [Option<FieldInit>],
    loans: &'a [CarrierLoans],
    labels: &'a [LabelEntry],
    continuation_live: &'a [bool],
    callable_targets: &'a [CallableTargets],
}

fn transfer(
    context: TransferContext<'_>,
    i: &Instruction,
    s: &mut [bool],
) -> Result<Vec<u32>, VerifyError> {
    let TransferContext {
        artifact: a,
        function_id: fid,
        pc,
        function: f,
        enum_variants,
        move_paths,
        loans,
        labels,
        continuation_live,
        callable_targets,
    } = context;
    let err_empty = |r| VerifyError::UseOfEmpty {
        function: fid,
        instruction: pc,
        register: r,
    };
    let err_over = |r| VerifyError::Overwrite {
        function: fid,
        instruction: pc,
        register: r,
    };
    let read = |s: &[bool], r: u32| {
        if s[r as usize] {
            Ok(())
        } else {
            Err(err_empty(r))
        }
    };
    let write = |s: &mut [bool], r: u32| {
        if s[r as usize] {
            Err(err_over(r))
        } else {
            s[r as usize] = true;
            Ok(())
        }
    };
    let consume = |s: &mut [bool], r: u32| {
        if s[r as usize] {
            s[r as usize] = false;
            Ok(())
        } else {
            Err(err_empty(r))
        }
    };
    let expect = |want, got| {
        if want == got {
            Ok(())
        } else {
            Err(VerifyError::TypeMismatch {
                function: fid,
                instruction: pc,
                expected: want,
                actual: got,
            })
        }
    };
    let next = || {
        if pc + 1 < f.code_len {
            Ok(vec![pc + 1])
        } else {
            Err(VerifyError::Fallthrough { function: fid })
        }
    };

    // The format intentionally carries no explicit continuation capture map.
    // Reconstruct a conservative proof at every instruction that can suspend
    // this frame: all values which remain in the frame must be independently
    // snapshot-cloneable, and no loan may cross the suspension. Arguments and
    // perform payloads are moved before suspension and are therefore excluded.
    let multishot_excluded: Option<Vec<u32>> = match i {
        Instruction::Perform {
            protocol,
            operation,
            payloads,
            ..
        } if operation_is_multishot(a, *protocol, *operation) => Some(payloads.clone()),
        Instruction::Call { function, args, .. } if function_body_may_multishot(a, *function) => {
            Some(args.clone())
        }
        Instruction::CallIndirect { callable, args, .. } => {
            let Type::Callable { signature, .. } =
                type_at(a, f.register_types[*callable as usize])?
            else {
                return Err(VerifyError::InvalidFunction(fid));
            };
            let targets = &callable_targets[*callable as usize];
            let may_multishot = if targets.is_empty() {
                // Parameters and imported/opaque producers still obey their
                // declared callable contract. Locally constructed values use
                // their exact body summaries instead of an unnecessarily wide
                // signature-only approximation.
                signature_may_multishot(a, signature)
            } else {
                targets
                    .iter()
                    .any(|target| function_body_may_multishot(a, *target))
            };
            may_multishot.then(|| {
                let mut excluded = args.clone();
                excluded.push(*callable);
                excluded
            })
        }
        _ => None,
    };
    if let Some(excluded) = multishot_excluded {
        verify_prunable_capture(
            a,
            fid,
            pc,
            f,
            s,
            move_paths,
            enum_variants,
            continuation_live,
            &excluded,
        )?;
        verify_multishot_capture(
            a,
            fid,
            pc,
            f,
            ContinuationState {
                live: s,
                move_paths,
                enum_variants,
                loans,
                excluded: &excluded,
                required: continuation_live,
            },
        )?;
    }
    let cancellation_excluded: Option<Vec<u32>> = match i {
        Instruction::Perform {
            protocol,
            operation,
            payloads,
            ..
        } if operation_is_cancellable(a, *protocol, *operation) => Some(payloads.clone()),
        Instruction::Call { function, args, .. }
            if function_body_may_cancel(a, *function)
                && !call_cancellation_discharged_by_handler(a, fid, *function) =>
        {
            Some(args.clone())
        }
        Instruction::CallIndirect {
            callable,
            receiver_mode,
            args,
            ..
        } => {
            let Type::Callable { signature, .. } =
                type_at(a, f.register_types[*callable as usize])?
            else {
                return Err(VerifyError::InvalidFunction(fid));
            };
            let targets = &callable_targets[*callable as usize];
            let may_cancel = if targets.is_empty() {
                signature_may_cancel(a, signature)
            } else {
                targets
                    .iter()
                    .any(|target| function_body_may_cancel(a, *target))
            };
            may_cancel.then(|| {
                let mut excluded = args.clone();
                if *receiver_mode == 2 {
                    excluded.push(*callable);
                }
                excluded
            })
        }
        _ => None,
    };
    if let Some(excluded) = cancellation_excluded {
        verify_cancellation_capture(
            a,
            fid,
            pc,
            f,
            ContinuationState {
                live: s,
                move_paths,
                enum_variants,
                loans,
                excluded: &excluded,
                required: continuation_live,
            },
        )?;
    }
    if let Instruction::Handle { handler, body, .. } = i
        && let Type::Callable { signature, .. } = type_at(a, f.register_types[*body as usize])?
    {
        let targets = &callable_targets[*body as usize];
        let body_may_multishot = if targets.is_empty() {
            signature_may_multishot(a, signature)
        } else {
            targets
                .iter()
                .any(|target| function_body_may_multishot(a, *target))
        };
        let body_may_cancel = if targets.is_empty() {
            signature_may_cancel(a, signature)
        } else {
            targets
                .iter()
                .any(|target| function_body_may_cancel(a, *target))
        };
        if body_may_multishot && !handler_snapshot_cloneable(a, f.register_types[*handler as usize])
        {
            return Err(VerifyError::IllegalCopy {
                function: fid,
                instruction: pc,
                ty: f.register_types[*handler as usize],
            });
        }
        if body_may_cancel
            && !handler_dependency_zero_use_safe(a, f.register_types[*handler as usize])
        {
            return Err(VerifyError::LiveValueAtExit {
                function: fid,
                instruction: pc,
                register: *handler,
            });
        }
    }
    if let Instruction::Handle { handler, body, .. } = i
        && let Type::Callable { signature, .. } = type_at(a, f.register_types[*body as usize])?
        && handler_may_forward_terminal(a, f.register_types[*handler as usize], signature)
        && !handler_dependency_zero_use_safe(a, f.register_types[*handler as usize])
    {
        return Err(VerifyError::LiveValueAtExit {
            function: fid,
            instruction: pc,
            register: *handler,
        });
    }
    match i {
        Instruction::Nop => next(),
        Instruction::Const { dst, constant } => {
            write(s, *dst)?;
            expect(
                f.register_types[*dst as usize],
                constant_type(a, &a.constants[*constant as usize])?,
            )?;
            next()
        }
        Instruction::Move { dst, src } => {
            if dst == src {
                return Err(err_over(*dst));
            }
            read(s, *src)?;
            expect(
                f.register_types[*dst as usize],
                f.register_types[*src as usize],
            )?;
            consume(s, *src)?;
            write(s, *dst)?;
            next()
        }
        Instruction::Deconstruct { src } => {
            read(s, *src)?;
            let source_ty = f.register_types[*src as usize];
            if a.drop_glue.iter().any(|glue| glue.ty == source_ty)
                || !matches!(
                    type_at(a, source_ty)?,
                    Type::Tuple { .. } | Type::Struct { .. } | Type::Enum { .. }
                )
            {
                return Err(VerifyError::InvalidAggregate {
                    function: fid,
                    instruction: pc,
                });
            }
            consume(s, *src)?;
            next()
        }
        Instruction::HostCall { dst, import, args } => {
            let signature = &a.imports[*import as usize].signature;
            if args.len() != signature.params.len()
                || !signature
                    .outward_protocols
                    .iter()
                    .all(|protocol| f.outward_protocols.contains(protocol))
            {
                return Err(VerifyError::InvalidFunction(fid));
            }
            for (&register, &ty) in args.iter().zip(&signature.params) {
                read(s, register)?;
                expect(ty, f.register_types[register as usize])?;
                consume(s, register)?;
            }
            if let Some(dst) = dst {
                expect(f.register_types[*dst as usize], signature.result)?;
                write(s, *dst)?;
            } else if !matches!(type_at(a, signature.result)?, Type::Unit | Type::Never) {
                return Err(VerifyError::InvalidFunction(fid));
            }
            next()
        }
        Instruction::CallKnownReceiver {
            dst,
            function,
            receiver,
            args,
        } => {
            let callee = &a.functions[*function as usize];
            let actual_outward = actual_function_outward_protocols(a);
            if callee.receiver_mode != Some(0)
                || callee.register_types.first().copied()
                    != Some(f.register_types[*receiver as usize])
                || args.len() != callee.params.len()
                || !actual_outward[*function as usize]
                    .iter()
                    .all(|protocol| f.outward_protocols.contains(protocol))
            {
                return Err(VerifyError::InvalidFunction(*function));
            }
            read(s, *receiver)?;
            for (&r, &ty) in args.iter().zip(&callee.params) {
                read(s, r)?;
                expect(ty, f.register_types[r as usize])?;
                consume(s, r)?;
            }
            if let Some(dst) = dst {
                expect(f.register_types[*dst as usize], callee.return_type)?;
                write(s, *dst)?;
            }
            next()
        }
        Instruction::TailCallKnownReceiver {
            function,
            receiver,
            args,
        } => {
            let callee = &a.functions[*function as usize];
            let actual_outward = actual_function_outward_protocols(a);
            if callee.receiver_mode != Some(0)
                || callee.register_types.first().copied()
                    != Some(f.register_types[*receiver as usize])
                || args.len() != callee.params.len()
                || f.return_type != callee.return_type
                || !actual_outward[*function as usize]
                    .iter()
                    .all(|protocol| f.outward_protocols.contains(protocol))
            {
                return Err(VerifyError::InvalidFunction(*function));
            }
            read(s, *receiver)?;
            for (&r, &ty) in args.iter().zip(&callee.params) {
                read(s, r)?;
                expect(ty, f.register_types[r as usize])?;
                consume(s, r)?;
            }
            ensure_abandonable(a, f, fid, pc, s, move_paths, enum_variants)?;
            Ok(vec![])
        }
        Instruction::MakeBindingPack {
            dst,
            binding_type,
            payloads,
        } => {
            expect(f.register_types[*dst as usize], *binding_type)?;
            let Type::BindingPack { payload_type, .. } = type_at(a, *binding_type)? else {
                return Err(VerifyError::InvalidType(*binding_type));
            };
            let fields = callable_capture_fields(a, *payload_type, payloads.len())?;
            for (&payload, &field_type) in payloads.iter().zip(&fields) {
                read(s, payload)?;
                expect(field_type, f.register_types[payload as usize])?;
                consume(s, payload)?;
            }
            write(s, *dst)?;
            next()
        }
        Instruction::MakeHandler {
            dst,
            handler_def,
            clauses,
        } => {
            let Type::Handler {
                handler_def: described_definition,
                capture_type,
                ..
            } = type_at(a, f.register_types[*dst as usize])?
            else {
                return Err(VerifyError::InvalidType(f.register_types[*dst as usize]));
            };
            let definition = a
                .handler_defs
                .get(*handler_def as usize)
                .ok_or(VerifyError::InvalidType(*handler_def))?;
            if described_definition != handler_def || definition.clauses.len() != clauses.len() {
                return Err(VerifyError::InvalidType(f.register_types[*dst as usize]));
            }
            let fields = callable_capture_fields(a, *capture_type, clauses.len())?;
            for ((&clause, &field_type), definition_clause) in
                clauses.iter().zip(&fields).zip(&definition.clauses)
            {
                read(s, clause)?;
                expect(field_type, f.register_types[clause as usize])?;
                let Type::Callable { signature, .. } = type_at(a, field_type)? else {
                    return Err(VerifyError::InvalidType(field_type));
                };
                if signature != &definition_clause.callable_signature {
                    return Err(VerifyError::InvalidType(field_type));
                }
                if clause_requires_reusable_receiver(a, definition_clause) {
                    let producer_modes = callable_producer_modes(a, field_type)?;
                    if producer_modes.is_empty()
                        || producer_modes
                            .iter()
                            .any(|receiver_mode| !matches!(receiver_mode, 0 | 1))
                    {
                        return Err(VerifyError::InvalidType(field_type));
                    }
                }
                consume(s, clause)?;
            }
            write(s, *dst)?;
            next()
        }
        Instruction::MakeHandlerShared {
            dst,
            handler_def,
            functions,
            captures,
        } => {
            let Type::Handler {
                handler_def: described_definition,
                capture_type,
                ..
            } = type_at(a, f.register_types[*dst as usize])?
            else {
                return Err(VerifyError::InvalidType(f.register_types[*dst as usize]));
            };
            let definition = a
                .handler_defs
                .get(*handler_def as usize)
                .ok_or(VerifyError::InvalidType(*handler_def))?;
            if described_definition != handler_def || definition.clauses.len() != functions.len() {
                return Err(VerifyError::InvalidType(f.register_types[*dst as usize]));
            }
            let callable_types = callable_capture_fields(a, *capture_type, functions.len())?;
            let mut environment_type = None;
            for ((function, callable_type), definition_clause) in functions
                .iter()
                .zip(callable_types)
                .zip(&definition.clauses)
            {
                let callee = &a.functions[*function as usize];
                let Type::Callable {
                    signature,
                    capture_type: described_environment,
                    receiver_mode: described_mode,
                    ..
                } = type_at(a, callable_type)?
                else {
                    return Err(VerifyError::InvalidType(callable_type));
                };
                // The shared environment supports mixed receiver views: a
                // terminal (or one-shot consuming) clause owns it, so
                // operation selection may move the stored value into at most
                // one such clause; a reusable resumptive clause receives a
                // borrowed view of the same stored environment, so the
                // handler survives resumption without cloning or aliasing
                // the captures as two independent owners.
                let reusable = clause_requires_reusable_receiver(a, definition_clause);
                let receiver_matches = match (reusable, callee.receiver_mode) {
                    (false, Some(2)) => callee.register_types[0] == *described_environment,
                    (true, Some(0)) => matches!(
                        type_at(a, callee.register_types[0])?,
                        Type::RefShared { referent } if *referent == *described_environment
                    ),
                    (true, Some(1)) => matches!(
                        type_at(a, callee.register_types[0])?,
                        Type::RefUnique { referent } if *referent == *described_environment
                    ),
                    _ => false,
                };
                if !receiver_matches
                    || callee.receiver_mode != Some(*described_mode)
                    || signature != &definition_clause.callable_signature
                    || environment_type
                        .replace(*described_environment)
                        .is_some_and(|existing| existing != *described_environment)
                {
                    return Err(VerifyError::InvalidFunction(*function));
                }
            }
            let environment_type =
                environment_type.ok_or(VerifyError::InvalidType(*capture_type))?;
            let fields = callable_capture_fields(a, environment_type, captures.len())?;
            for (&capture, &field_type) in captures.iter().zip(&fields) {
                read(s, capture)?;
                expect(field_type, f.register_types[capture as usize])?;
                consume(s, capture)?;
            }
            write(s, *dst)?;
            next()
        }
        Instruction::Copy { dst, src } => {
            read(s, *src)?;
            let ty = f.register_types[*src as usize];
            expect(f.register_types[*dst as usize], ty)?;
            if !is_copy(a, ty) {
                return Err(VerifyError::IllegalCopy {
                    function: fid,
                    instruction: pc,
                    ty,
                });
            }
            write(s, *dst)?;
            next()
        }
        Instruction::BorrowShared { dst, src } => {
            read(s, *src)?;
            let referent = f.register_types[*src as usize];
            if !matches!(type_at(a, f.register_types[*dst as usize])?, Type::RefShared { referent: actual } if *actual == referent)
            {
                return Err(VerifyError::TypeMismatch {
                    function: fid,
                    instruction: pc,
                    expected: referent,
                    actual: f.register_types[*dst as usize],
                });
            }
            write(s, *dst)?;
            next()
        }
        Instruction::BorrowUnique { dst, src } => {
            read(s, *src)?;
            let referent = f.register_types[*src as usize];
            if !matches!(type_at(a, f.register_types[*dst as usize])?, Type::RefUnique { referent: actual } if *actual == referent)
            {
                return Err(VerifyError::TypeMismatch {
                    function: fid,
                    instruction: pc,
                    expected: referent,
                    actual: f.register_types[*dst as usize],
                });
            }
            write(s, *dst)?;
            next()
        }
        Instruction::ReborrowShared { dst, src } => {
            read(s, *src)?;
            let referent = match type_at(a, f.register_types[*src as usize])? {
                Type::RefShared { referent } | Type::RefUnique { referent } => *referent,
                _ => {
                    return Err(VerifyError::InvalidAggregate {
                        function: fid,
                        instruction: pc,
                    });
                }
            };
            if !matches!(type_at(a, f.register_types[*dst as usize])?, Type::RefShared { referent: actual } if *actual == referent)
            {
                return Err(VerifyError::TypeMismatch {
                    function: fid,
                    instruction: pc,
                    expected: referent,
                    actual: f.register_types[*dst as usize],
                });
            }
            write(s, *dst)?;
            next()
        }
        Instruction::ReborrowUnique { dst, src } => {
            read(s, *src)?;
            let Type::RefUnique { referent } = type_at(a, f.register_types[*src as usize])? else {
                return Err(VerifyError::InvalidAggregate {
                    function: fid,
                    instruction: pc,
                });
            };
            if !matches!(type_at(a, f.register_types[*dst as usize])?, Type::RefUnique { referent: actual } if actual == referent)
            {
                return Err(VerifyError::TypeMismatch {
                    function: fid,
                    instruction: pc,
                    expected: *referent,
                    actual: f.register_types[*dst as usize],
                });
            }
            write(s, *dst)?;
            next()
        }
        Instruction::EndBorrow { reference } => {
            if !matches!(
                type_at(a, f.register_types[*reference as usize])?,
                Type::RefShared { .. } | Type::RefUnique { .. }
            ) {
                return Err(VerifyError::InvalidPrimitive {
                    function: fid,
                    instruction: pc,
                });
            }
            consume(s, *reference)?;
            next()
        }
        Instruction::DerefCopy { dst, src } => {
            read(s, *src)?;
            let referent = match type_at(a, f.register_types[*src as usize])? {
                Type::RefShared { referent } | Type::RefUnique { referent } => *referent,
                _ => {
                    return Err(VerifyError::InvalidAggregate {
                        function: fid,
                        instruction: pc,
                    });
                }
            };
            if !is_copy(a, referent) {
                return Err(VerifyError::IllegalCopy {
                    function: fid,
                    instruction: pc,
                    ty: referent,
                });
            }
            expect(referent, f.register_types[*dst as usize])?;
            write(s, *dst)?;
            next()
        }
        Instruction::DerefMove { dst, src } => {
            read(s, *src)?;
            let Type::RefUnique { referent } = type_at(a, f.register_types[*src as usize])? else {
                return Err(VerifyError::InvalidAggregate {
                    function: fid,
                    instruction: pc,
                });
            };
            expect(*referent, f.register_types[*dst as usize])?;
            write(s, *dst)?;
            next()
        }
        Instruction::DerefStore { dst, src } => {
            read(s, *dst)?;
            read(s, *src)?;
            let Type::RefUnique { referent } = type_at(a, f.register_types[*dst as usize])? else {
                return Err(VerifyError::InvalidAggregate {
                    function: fid,
                    instruction: pc,
                });
            };
            expect(*referent, f.register_types[*src as usize])?;
            consume(s, *src)?;
            next()
        }
        Instruction::Construct {
            dst,
            ty,
            variant,
            fields,
        } => {
            expect(f.register_types[*dst as usize], *ty)?;
            let wanted = construction_field_types(type_at(a, *ty)?, *variant).ok_or(
                VerifyError::InvalidAggregate {
                    function: fid,
                    instruction: pc,
                },
            )?;
            let wanted = wanted
                .into_iter()
                .filter(|&field| !matches!(type_at(a, field), Ok(Type::Available { .. })))
                .collect::<Vec<_>>();
            if wanted.len() != fields.len() {
                return Err(VerifyError::InvalidAggregate {
                    function: fid,
                    instruction: pc,
                });
            }
            for (&r, &want) in fields.iter().zip(&wanted) {
                read(s, r)?;
                expect(want, f.register_types[r as usize])?;
                consume(s, r)?;
            }
            write(s, *dst)?;
            next()
        }
        Instruction::ProjectMove { dst, src, field } => {
            read(s, *src)?;
            let source_ty = f.register_types[*src as usize];
            let projection_owner = match type_at(a, source_ty)? {
                Type::RefShared { .. } => {
                    return Err(VerifyError::BorrowConflict {
                        function: fid,
                        instruction: pc,
                        register: *src,
                    });
                }
                Type::RefUnique { referent } => *referent,
                _ => source_ty,
            };
            if has_custom_drop(a, projection_owner) {
                return Err(VerifyError::InvalidAggregate {
                    function: fid,
                    instruction: pc,
                });
            }
            let ty = projected_type_at(a, f, *src, *field, enum_variants, loans).ok_or(
                VerifyError::InvalidAggregate {
                    function: fid,
                    instruction: pc,
                },
            )?;
            expect(f.register_types[*dst as usize], ty)?;
            write(s, *dst)?;
            next()
        }
        Instruction::ProjectCopy { dst, src, field } => {
            read(s, *src)?;
            let ty = projected_type_at(a, f, *src, *field, enum_variants, loans).ok_or(
                VerifyError::InvalidAggregate {
                    function: fid,
                    instruction: pc,
                },
            )?;
            if !is_copy(a, ty) {
                return Err(VerifyError::IllegalCopy {
                    function: fid,
                    instruction: pc,
                    ty,
                });
            }
            expect(f.register_types[*dst as usize], ty)?;
            write(s, *dst)?;
            next()
        }
        Instruction::ProjectBorrowShared { dst, src, field }
        | Instruction::ProjectBorrowUnique { dst, src, field } => {
            read(s, *src)?;
            let unique = matches!(i, Instruction::ProjectBorrowUnique { .. });
            let source_ty = f.register_types[*src as usize];
            let _base_ty = match type_at(a, source_ty)? {
                Type::RefShared { referent } if !unique => *referent,
                Type::RefUnique { referent } => *referent,
                Type::RefShared { .. } => {
                    return Err(VerifyError::BorrowConflict {
                        function: fid,
                        instruction: pc,
                        register: *src,
                    });
                }
                _ => source_ty,
            };
            let projected = projected_type_at(a, f, *src, *field, enum_variants, loans).ok_or(
                VerifyError::InvalidAggregate {
                    function: fid,
                    instruction: pc,
                },
            )?;
            let valid = match type_at(a, f.register_types[*dst as usize])? {
                Type::RefShared { referent } => !unique && *referent == projected,
                Type::RefUnique { referent } => unique && *referent == projected,
                _ => false,
            };
            if !valid {
                return Err(VerifyError::InvalidAggregate {
                    function: fid,
                    instruction: pc,
                });
            }
            write(s, *dst)?;
            next()
        }
        Instruction::EnumTag { dst, src } => {
            read(s, *src)?;
            if !matches!(
                type_at(a, f.register_types[*src as usize])?,
                Type::Enum { .. }
            ) {
                return Err(VerifyError::InvalidAggregate {
                    function: fid,
                    instruction: pc,
                });
            }
            expect(U32, f.register_types[*dst as usize])?;
            write(s, *dst)?;
            next()
        }
        Instruction::Drop { register } => {
            let ty = f.register_types[*register as usize];
            if !residual_quantity_drop_allowed(
                a,
                ty,
                move_paths[*register as usize].as_ref(),
                enum_variants[*register as usize],
            ) {
                return Err(VerifyError::LiveValueAtExit {
                    function: fid,
                    instruction: pc,
                    register: *register,
                });
            }
            consume(s, *register)?;
            next()
        }
        Instruction::Primitive { dst, op, args } => {
            let arg_types = args
                .iter()
                .map(|&r| f.register_types[r as usize])
                .collect::<Vec<_>>();
            let result = f.register_types[*dst as usize];
            if !primitive_signature(&a.types, *op, &arg_types, result) {
                return Err(VerifyError::InvalidPrimitive {
                    function: fid,
                    instruction: pc,
                });
            }
            let element = match (*op, arg_types.as_slice()) {
                (Primitive::ArrayNew, [_, element]) => Some(*element),
                (Primitive::ArrayGetCopy, [reference, _]) => {
                    let referent = match type_at(a, *reference)? {
                        Type::RefShared { referent } => *referent,
                        _ => unreachable!("primitive signature already checked"),
                    };
                    match type_at(a, referent)? {
                        Type::Array { element } => Some(*element),
                        _ => unreachable!("primitive signature already checked"),
                    }
                }
                _ => None,
            };
            if matches!(*op, Primitive::ArrayNew | Primitive::ArrayGetCopy)
                && element.is_some_and(|element| !is_copy(a, element))
            {
                return Err(VerifyError::IllegalCopy {
                    function: fid,
                    instruction: pc,
                    ty: element.unwrap(),
                });
            }
            for &r in args {
                read(s, r)?;
                consume(s, r)?;
            }
            write(s, *dst)?;
            next()
        }
        Instruction::Jump { target } => Ok(vec![*target]),
        Instruction::Switch {
            discr,
            cases,
            otherwise,
        } => {
            read(s, *discr)?;
            let ty = f.register_types[*discr as usize];
            if !matches!(type_at(a, ty)?, Type::U32 | Type::I64 | Type::U64) {
                return Err(VerifyError::InvalidPrimitive {
                    function: fid,
                    instruction: pc,
                });
            }
            for &(c, _) in cases {
                expect(ty, constant_type(a, &a.constants[c as usize])?)?;
            }
            let mut v: Vec<u32> = cases.iter().map(|x| x.1).collect();
            v.push(*otherwise);
            Ok(v)
        }
        Instruction::Call {
            dst,
            function,
            args,
        } => {
            let callee = &a.functions[*function as usize];
            let actual_outward = actual_function_outward_protocols(a);
            if callee.receiver_mode.is_some()
                || args.len() != callee.params.len()
                || !actual_outward[*function as usize]
                    .iter()
                    .all(|protocol| f.outward_protocols.contains(protocol))
            {
                return Err(VerifyError::InvalidFunction(*function));
            }
            for (&r, &ty) in args.iter().zip(&callee.params) {
                read(s, r)?;
                expect(ty, f.register_types[r as usize])?;
                consume(s, r)?;
            }
            if let Some(dst) = dst {
                expect(f.register_types[*dst as usize], callee.return_type)?;
                write(s, *dst)?;
            } else if !matches!(type_at(a, callee.return_type)?, Type::Unit | Type::Never) {
                return Err(VerifyError::InvalidFunction(*function));
            }
            next()
        }
        Instruction::TailCall { function, args } => {
            let callee = &a.functions[*function as usize];
            let actual_outward = actual_function_outward_protocols(a);
            if callee.receiver_mode.is_some()
                || args.len() != callee.params.len()
                || !actual_outward[*function as usize]
                    .iter()
                    .all(|protocol| f.outward_protocols.contains(protocol))
            {
                return Err(VerifyError::InvalidFunction(*function));
            }
            for (&r, &ty) in args.iter().zip(&callee.params) {
                read(s, r)?;
                expect(ty, f.register_types[r as usize])?;
                consume(s, r)?;
            }
            expect(f.return_type, callee.return_type)?;
            ensure_abandonable(a, f, fid, pc, s, move_paths, enum_variants)?;
            Ok(vec![])
        }
        Instruction::CallSelf { dst, args } => {
            if !matches!(f.receiver_mode, Some(0 | 1)) || args.len() != f.params.len() {
                return Err(VerifyError::InvalidFunction(fid));
            }
            read(s, 0)?;
            for (&r, &ty) in args.iter().zip(&f.params) {
                read(s, r)?;
                expect(ty, f.register_types[r as usize])?;
                consume(s, r)?;
            }
            if let Some(dst) = dst {
                expect(f.register_types[*dst as usize], f.return_type)?;
                write(s, *dst)?;
            }
            next()
        }
        Instruction::TailCallSelf { args } => {
            if f.receiver_mode.is_none() || args.len() != f.params.len() {
                return Err(VerifyError::InvalidFunction(fid));
            }
            read(s, 0)?;
            consume(s, 0)?;
            for (&r, &ty) in args.iter().zip(&f.params) {
                read(s, r)?;
                expect(ty, f.register_types[r as usize])?;
                consume(s, r)?;
            }
            ensure_abandonable(a, f, fid, pc, s, move_paths, enum_variants)?;
            Ok(vec![])
        }
        Instruction::Resume {
            dst,
            resumption,
            receiver_mode,
            value,
        } => {
            let Type::Resumption {
                input_type,
                output_type,
                effect_signature,
                upper_uses,
                ..
            } = type_at(a, f.register_types[*resumption as usize])?
            else {
                return Err(VerifyError::InvalidType(
                    f.register_types[*resumption as usize],
                ));
            };
            if upper_uses == &Some(0)
                || (upper_uses == &Some(1) && *receiver_mode != 2)
                || (upper_uses.is_none_or(|upper| upper > 1) && *receiver_mode > 2)
                || !effect_signature
                    .outward_protocols
                    .iter()
                    .all(|protocol| f.outward_protocols.contains(protocol))
            {
                return Err(VerifyError::InvalidFunction(fid));
            }
            read(s, *resumption)?;
            if *receiver_mode == 2 {
                consume(s, *resumption)?;
            }
            read(s, *value)?;
            expect(*input_type, f.register_types[*value as usize])?;
            consume(s, *value)?;
            expect(*output_type, f.register_types[*dst as usize])?;
            write(s, *dst)?;
            next()
        }
        Instruction::TailResume {
            resumption,
            receiver_mode,
            value,
        } => {
            let Type::Resumption {
                input_type,
                output_type,
                effect_signature,
                upper_uses,
                ..
            } = type_at(a, f.register_types[*resumption as usize])?
            else {
                return Err(VerifyError::InvalidType(
                    f.register_types[*resumption as usize],
                ));
            };
            if upper_uses == &Some(0)
                || (upper_uses == &Some(1) && *receiver_mode != 2)
                || (upper_uses.is_none_or(|upper| upper > 1) && *receiver_mode > 2)
                || *output_type != f.return_type
                || !effect_signature
                    .outward_protocols
                    .iter()
                    .all(|protocol| f.outward_protocols.contains(protocol))
            {
                return Err(VerifyError::InvalidFunction(fid));
            }
            read(s, *resumption)?;
            if *receiver_mode == 2 {
                consume(s, *resumption)?;
            }
            read(s, *value)?;
            expect(*input_type, f.register_types[*value as usize])?;
            consume(s, *value)?;
            ensure_abandonable(a, f, fid, pc, s, move_paths, enum_variants)?;
            Ok(vec![])
        }
        Instruction::Cancel { dst, resumption } => {
            let Type::Resumption { lower_uses, .. } =
                type_at(a, f.register_types[*resumption as usize])?
            else {
                return Err(VerifyError::InvalidType(
                    f.register_types[*resumption as usize],
                ));
            };
            if *lower_uses != 0 {
                return Err(VerifyError::InvalidFunction(fid));
            }
            read(s, *resumption)?;
            consume(s, *resumption)?;
            expect(crate::bytecode::UNIT, f.register_types[*dst as usize])?;
            write(s, *dst)?;
            next()
        }
        Instruction::Handle {
            dst,
            handler,
            body,
            args,
        } => {
            let Type::Handler { handler_def, .. } =
                type_at(a, f.register_types[*handler as usize])?
            else {
                return Err(VerifyError::InvalidType(
                    f.register_types[*handler as usize],
                ));
            };
            let definition = &a.handler_defs[*handler_def as usize];
            let Type::Callable { signature, .. } = type_at(a, f.register_types[*body as usize])?
            else {
                return Err(VerifyError::InvalidType(f.register_types[*body as usize]));
            };
            if signature.result != definition.result_type || args.len() != signature.params.len() {
                return Err(VerifyError::InvalidFunction(fid));
            }
            let handled = definition
                .clauses
                .iter()
                .map(|clause| clause.protocol)
                .collect::<std::collections::BTreeSet<_>>();
            if !signature.outward_protocols.iter().all(|protocol| {
                handled.contains(protocol) || f.outward_protocols.contains(protocol)
            }) {
                return Err(VerifyError::InvalidFunction(fid));
            }
            read(s, *handler)?;
            consume(s, *handler)?;
            read(s, *body)?;
            consume(s, *body)?;
            for (&argument, &argument_type) in args.iter().zip(&signature.params) {
                read(s, argument)?;
                expect(argument_type, f.register_types[argument as usize])?;
                consume(s, argument)?;
            }
            expect(definition.result_type, f.register_types[*dst as usize])?;
            write(s, *dst)?;
            next()
        }
        Instruction::Perform {
            dst,
            protocol,
            operation,
            payloads,
        } => {
            let operation = &a.protocols[*protocol as usize].operations[*operation as usize];
            if !f.outward_protocols.contains(protocol) {
                return Err(VerifyError::InvalidFunction(fid));
            }
            if payloads.len() != operation.payload_signature.params.len()
                || operation.terminal != dst.is_none()
            {
                return Err(VerifyError::InvalidFunction(fid));
            }
            for (&payload, &payload_type) in
                payloads.iter().zip(&operation.payload_signature.params)
            {
                read(s, payload)?;
                expect(payload_type, f.register_types[payload as usize])?;
                consume(s, payload)?;
            }
            if let Some(dst) = dst {
                expect(operation.result_type, f.register_types[*dst as usize])?;
                write(s, *dst)?;
                next()
            } else {
                ensure_abandonable(a, f, fid, pc, s, move_paths, enum_variants)?;
                Ok(vec![])
            }
        }
        Instruction::MakeCallable {
            dst,
            callable_type,
            function,
            captures,
        } => {
            let callee = &a.functions[*function as usize];
            let Some(receiver_mode) = callee.receiver_mode else {
                return Err(VerifyError::InvalidFunction(*function));
            };
            let capture_type = receiver_capture_type(a, receiver_mode, callee.register_types[0])?;
            let Type::Callable {
                signature,
                capture_type: described_capture,
                receiver_mode: described_mode,
                ..
            } = type_at(a, *callable_type)?
            else {
                return Err(VerifyError::InvalidFunction(*function));
            };
            if f.register_types[*dst as usize] != *callable_type
                || *described_mode != receiver_mode
                || *described_capture != capture_type
                || signature.params != callee.params
                || signature.result != callee.return_type
                || signature.outward_protocols != callee.outward_protocols
            {
                return Err(VerifyError::InvalidFunction(*function));
            }
            let fields = callable_capture_fields(a, capture_type, captures.len())?;
            for (&capture, &field_type) in captures.iter().zip(&fields) {
                read(s, capture)?;
                expect(field_type, f.register_types[capture as usize])?;
                consume(s, capture)?;
            }
            write(s, *dst)?;
            next()
        }
        Instruction::CallIndirect {
            dst,
            callable,
            receiver_mode,
            args,
        } => {
            let Type::Callable {
                signature,
                receiver_mode: described_mode,
                ..
            } = type_at(a, f.register_types[*callable as usize])?
            else {
                return Err(VerifyError::InvalidFunction(fid));
            };
            if *receiver_mode > 2
                || *receiver_mode < *described_mode
                || args.len() != signature.params.len()
            {
                return Err(VerifyError::InvalidFunction(fid));
            }
            if !signature
                .outward_protocols
                .iter()
                .all(|protocol| f.outward_protocols.contains(protocol))
            {
                return Err(VerifyError::InvalidFunction(fid));
            }
            read(s, *callable)?;
            if *receiver_mode == 2 {
                consume(s, *callable)?;
            }
            for (&argument, &argument_type) in args.iter().zip(&signature.params) {
                read(s, argument)?;
                expect(argument_type, f.register_types[argument as usize])?;
                consume(s, argument)?;
            }
            if let Some(dst) = dst {
                expect(signature.result, f.register_types[*dst as usize])?;
                write(s, *dst)?;
            } else if !matches!(type_at(a, signature.result)?, Type::Unit | Type::Never) {
                return Err(VerifyError::InvalidFunction(fid));
            }
            next()
        }
        Instruction::TailCallIndirect {
            callable,
            receiver_mode,
            args,
        } => {
            if *receiver_mode != 2 {
                return Err(VerifyError::InvalidFunction(fid));
            }
            let Type::Callable {
                signature,
                receiver_mode: described_mode,
                ..
            } = type_at(a, f.register_types[*callable as usize])?
            else {
                return Err(VerifyError::InvalidFunction(fid));
            };
            if *receiver_mode < *described_mode || args.len() != signature.params.len() {
                return Err(VerifyError::InvalidFunction(fid));
            }
            if !signature
                .outward_protocols
                .iter()
                .all(|protocol| f.outward_protocols.contains(protocol))
            {
                return Err(VerifyError::InvalidFunction(fid));
            }
            read(s, *callable)?;
            consume(s, *callable)?;
            for (&argument, &argument_type) in args.iter().zip(&signature.params) {
                read(s, argument)?;
                expect(argument_type, f.register_types[argument as usize])?;
                consume(s, argument)?;
            }
            expect(f.return_type, signature.result)?;
            ensure_abandonable(a, f, fid, pc, s, move_paths, enum_variants)?;
            Ok(vec![])
        }
        Instruction::Return { src } => {
            if let Some(src) = src {
                read(s, *src)?;
                expect(f.return_type, f.register_types[*src as usize])?;
                consume(s, *src)?;
            } else if f.return_type != crate::bytecode::UNIT {
                return Err(VerifyError::InvalidFunction(fid));
            }
            ensure_abandonable(a, f, fid, pc, s, move_paths, enum_variants)?;
            Ok(vec![])
        }
        Instruction::LabelPush {
            result_register, ..
        } => {
            if s[*result_register as usize] {
                return Err(err_over(*result_register));
            }
            next()
        }
        Instruction::LabelPop { .. } => next(),
        Instruction::Leave { slot, value } => {
            let entry = labels
                .iter()
                .rfind(|entry| entry.slot == *slot)
                .ok_or(VerifyError::InvalidFunction(fid))?;
            read(s, *value)?;
            expect(
                f.register_types[entry.result_register as usize],
                f.register_types[*value as usize],
            )?;
            consume(s, *value)?;
            for register in cleanup_prefix(a, fid, pc, entry.target)? {
                if !residual_zero_use_allowed(
                    a,
                    f.register_types[*register as usize],
                    move_paths[*register as usize].as_ref(),
                    enum_variants[*register as usize],
                ) {
                    return Err(VerifyError::LiveValueAtExit {
                        function: fid,
                        instruction: pc,
                        register: *register,
                    });
                }
                s[*register as usize] = false;
            }
            write(s, entry.result_register)?;
            Ok(vec![entry.target])
        }
        Instruction::Unreachable | Instruction::Abort { .. } => Ok(vec![]),
    }
}

fn ensure_abandonable(
    a: &Artifact,
    f: &Function,
    fid: u32,
    pc: u32,
    s: &[bool],
    move_paths: &[Option<FieldInit>],
    enum_variants: &[Option<u32>],
) -> Result<(), VerifyError> {
    if let Some((r, _)) = s.iter().enumerate().find(|(register, live)| {
        **live
            && !residual_zero_use_allowed(
                a,
                f.register_types[*register],
                move_paths[*register].as_ref(),
                enum_variants[*register],
            )
    }) {
        Err(VerifyError::LiveValueAtExit {
            function: fid,
            instruction: pc,
            register: r as u32,
        })
    } else {
        Ok(())
    }
}
fn type_at(a: &Artifact, id: TypeId) -> Result<&Type, VerifyError> {
    a.types
        .get(id as usize)
        .map(Type::representation)
        .ok_or(VerifyError::InvalidType(id))
}

fn has_custom_drop(a: &Artifact, id: TypeId) -> bool {
    a.drop_glue.iter().any(|glue| glue.ty == id)
}

fn declared_type_at(a: &Artifact, id: TypeId) -> Result<&Type, VerifyError> {
    a.types.get(id as usize).ok_or(VerifyError::InvalidType(id))
}

fn runtime_type_at(a: &Artifact, id: TypeId) -> Result<&Type, VerifyError> {
    let ty = type_at(a, id)?;
    if matches!(ty, Type::Available { .. }) {
        Err(VerifyError::InvalidType(id))
    } else {
        Ok(ty)
    }
}

fn receiver_capture_type(
    a: &Artifact,
    receiver_mode: u32,
    receiver_type: TypeId,
) -> Result<TypeId, VerifyError> {
    match (receiver_mode, type_at(a, receiver_type)?) {
        (0, Type::RefShared { referent }) | (1, Type::RefUnique { referent }) => Ok(*referent),
        (2, _) => Ok(receiver_type),
        _ => Err(VerifyError::InvalidType(receiver_type)),
    }
}

fn callable_capture_fields(
    a: &Artifact,
    capture_type: TypeId,
    count: usize,
) -> Result<Vec<TypeId>, VerifyError> {
    if capture_type == crate::bytecode::UNIT && count == 0 {
        return Ok(Vec::new());
    }
    let fields = construction_field_types(type_at(a, capture_type)?, None)
        .ok_or(VerifyError::InvalidType(capture_type))?;
    let fields = fields
        .into_iter()
        .filter(|&field| !matches!(type_at(a, field), Ok(Type::Available { .. })))
        .collect::<Vec<_>>();
    (fields.len() == count)
        .then_some(fields)
        .ok_or(VerifyError::InvalidType(capture_type))
}

fn clause_requires_reusable_receiver(a: &Artifact, clause: &HandlerClause) -> bool {
    let Some(resumption_type) = clause.resumption_type else {
        return false;
    };
    !matches!(
        type_at(a, resumption_type).ok(),
        Some(Type::Resumption {
            upper_uses: Some(0),
            ..
        })
    )
}

fn callable_producer_modes(a: &Artifact, callable_type: TypeId) -> Result<Vec<u32>, VerifyError> {
    let mut modes = Vec::new();
    for function in &a.functions {
        for instruction in &a.code
            [function.code_start as usize..(function.code_start + function.code_len) as usize]
        {
            let Instruction::MakeCallable {
                dst,
                function: target,
                ..
            } = instruction
            else {
                continue;
            };
            if function.register_types[*dst as usize] != callable_type {
                continue;
            }
            modes.push(
                a.functions
                    .get(*target as usize)
                    .and_then(|target| target.receiver_mode)
                    .ok_or(VerifyError::InvalidFunction(*target))?,
            );
        }
    }
    Ok(modes)
}
fn projected_type_at(
    a: &Artifact,
    f: &Function,
    source: u32,
    field: u32,
    enum_variants: &[Option<u32>],
    loans: &[CarrierLoans],
) -> Option<TypeId> {
    let source_ty = f.register_types[source as usize];
    let (base_ty, variant_register) = match a.types.get(source_ty as usize)?.representation() {
        Type::RefShared { referent } | Type::RefUnique { referent } => (
            *referent,
            loans.get(source as usize)?.first()?.loan.place.owner,
        ),
        _ => (source_ty, source),
    };
    let variant = matches!(
        a.types.get(base_ty as usize)?.representation(),
        Type::Enum { .. }
    )
    .then(|| {
        enum_variants
            .get(variant_register as usize)
            .copied()
            .flatten()
    })
    .flatten();
    let projected = projection_field_type(a.types.get(base_ty as usize)?, variant, field)?;
    (!matches!(
        a.types.get(projected as usize)?.representation(),
        Type::Available { .. }
    ))
    .then_some(projected)
}

fn operation_is_multishot(a: &Artifact, protocol: u32, operation: u32) -> bool {
    a.protocols
        .get(protocol as usize)
        .and_then(|protocol| protocol.operations.get(operation as usize))
        .is_some_and(|operation| operation.resumption_upper.is_none_or(|upper| upper > 1))
}

fn operation_is_cancellable(a: &Artifact, protocol: u32, operation: u32) -> bool {
    a.protocols
        .get(protocol as usize)
        .and_then(|protocol| protocol.operations.get(operation as usize))
        .is_some_and(|operation| !operation.terminal && operation.resumption_lower == 0)
}

/// Infer the protocols each direct bytecode body can actually emit. Declared
/// rows remain conservative contracts, but a direct caller need not expose an
/// effect that the callee demonstrably consumes with a complete local handler.
fn actual_function_outward_protocols(a: &Artifact) -> Vec<std::collections::BTreeSet<u32>> {
    let mut actual = vec![std::collections::BTreeSet::new(); a.functions.len()];
    let mut direct_calls = vec![Vec::<u32>::new(); a.functions.len()];
    for (fid, function) in a.functions.iter().enumerate() {
        let Ok(code) = function_code(a, function) else {
            continue;
        };
        for instruction in code {
            match instruction {
                Instruction::Perform { protocol, .. } => {
                    actual[fid].insert(*protocol);
                }
                Instruction::Call {
                    function: target, ..
                }
                | Instruction::TailCall {
                    function: target, ..
                } => direct_calls[fid].push(*target),
                Instruction::CallIndirect { callable, .. }
                | Instruction::TailCallIndirect { callable, .. } => {
                    if let Ok(Type::Callable { signature, .. }) =
                        type_at(a, function.register_types[*callable as usize])
                    {
                        actual[fid].extend(&signature.outward_protocols);
                    }
                }
                Instruction::Resume { resumption, .. } => {
                    if let Ok(Type::Resumption {
                        effect_signature, ..
                    }) = type_at(a, function.register_types[*resumption as usize])
                    {
                        actual[fid].extend(&effect_signature.outward_protocols);
                    }
                }
                Instruction::Handle { handler, body, .. } => {
                    let Ok(Type::Callable { signature, .. }) =
                        type_at(a, function.register_types[*body as usize])
                    else {
                        continue;
                    };
                    let Ok(Type::Handler { handler_def, .. }) =
                        type_at(a, function.register_types[*handler as usize])
                    else {
                        continue;
                    };
                    let Some(definition) = a.handler_defs.get(*handler_def as usize) else {
                        continue;
                    };
                    for &protocol in &signature.outward_protocols {
                        let completely_handled =
                            a.protocols
                                .get(protocol as usize)
                                .is_some_and(|descriptor| {
                                    (0..descriptor.operations.len() as u32).all(|operation| {
                                        definition.clauses.iter().any(|clause| {
                                            clause.protocol == protocol
                                                && clause.operation == operation
                                        })
                                    })
                                });
                        if !completely_handled {
                            actual[fid].insert(protocol);
                        }
                    }
                    for clause in &definition.clauses {
                        actual[fid].extend(&clause.callable_signature.outward_protocols);
                    }
                }
                _ => {}
            }
        }
    }
    loop {
        let mut changed = false;
        for fid in 0..a.functions.len() {
            for target in direct_calls[fid].clone() {
                let Some(target_effects) = actual.get(target as usize).cloned() else {
                    continue;
                };
                let old_len = actual[fid].len();
                actual[fid].extend(target_effects);
                changed |= actual[fid].len() != old_len;
            }
        }
        if !changed {
            return actual;
        }
    }
}

fn signature_may_cancel(a: &Artifact, signature: &Signature) -> bool {
    signature.outward_protocols.iter().any(|&protocol_id| {
        a.protocols
            .get(protocol_id as usize)
            .is_some_and(|protocol| {
                protocol
                    .operations
                    .iter()
                    .enumerate()
                    .any(|(operation, _)| {
                        operation_is_cancellable(a, protocol_id, operation as u32)
                    })
            })
    })
}

fn callable_type_producers(a: &Artifact, callable_type: TypeId) -> std::collections::BTreeSet<u32> {
    let mut producers = std::collections::BTreeSet::new();
    for instruction in &a.code {
        if let Instruction::MakeCallable {
            callable_type: produced,
            function,
            ..
        } = instruction
            && *produced == callable_type
        {
            producers.insert(*function);
        }
    }
    for owner in &a.functions {
        let Ok(code) = function_code(a, owner) else {
            continue;
        };
        for instruction in code {
            let Instruction::MakeHandlerShared { dst, functions, .. } = instruction else {
                continue;
            };
            let Some(&handler_type) = owner.register_types.get(*dst as usize) else {
                continue;
            };
            let Ok(Type::Handler { capture_type, .. }) = type_at(a, handler_type) else {
                continue;
            };
            let Ok(fields) = callable_capture_fields(a, *capture_type, functions.len()) else {
                continue;
            };
            for (&target, field) in functions.iter().zip(fields) {
                if field == callable_type {
                    producers.insert(target);
                }
            }
        }
    }
    producers
}

fn clause_resumes_parameter_exactly_once(a: &Artifact, function_id: u32, parameter: usize) -> bool {
    let Some(function) = a.functions.get(function_id as usize) else {
        return false;
    };
    let Some(code) = function_code(a, function).ok() else {
        return false;
    };
    let register = parameter + 1;
    if register >= function.register_types.len() || code.is_empty() {
        return false;
    }
    let mut entry = (vec![false; function.register_types.len()], 0u8);
    entry.0[register] = true;
    let mut states = vec![None; code.len()];
    states[0] = Some(entry);
    let mut work = VecDeque::from([0usize]);
    let mut returned = false;
    while let Some(pc) = work.pop_front() {
        let (mut origins, mut resumes) = states[pc].clone().unwrap();
        let instruction = &code[pc];
        match instruction {
            Instruction::Move { dst, src } => {
                origins[*dst as usize] = origins[*src as usize];
                origins[*src as usize] = false;
            }
            Instruction::Copy { dst, src } => origins[*dst as usize] = origins[*src as usize],
            Instruction::Resume {
                resumption,
                receiver_mode,
                ..
            } if origins[*resumption as usize] => {
                resumes = resumes.saturating_add(1);
                if resumes > 1 {
                    return false;
                }
                if *receiver_mode == 2 {
                    origins[*resumption as usize] = false;
                }
            }
            Instruction::Cancel { resumption, .. } if origins[*resumption as usize] => {
                return false;
            }
            Instruction::Drop { register } if origins[*register as usize] => return false,
            Instruction::Return { .. } => {
                if resumes != 1 || origins.iter().any(|origin| *origin) {
                    return false;
                }
                returned = true;
                continue;
            }
            _ => {}
        }
        let successors = match instruction {
            Instruction::Jump { target } => vec![*target as usize],
            Instruction::Switch {
                cases, otherwise, ..
            } => cases
                .iter()
                .map(|(_, target)| *target as usize)
                .chain(std::iter::once(*otherwise as usize))
                .collect(),
            Instruction::Return { .. }
            | Instruction::TailCall { .. }
            | Instruction::TailCallSelf { .. }
            | Instruction::TailCallKnownReceiver { .. }
            | Instruction::TailCallIndirect { .. }
            | Instruction::TailResume { .. }
            | Instruction::Perform { dst: None, .. }
            | Instruction::Unreachable
            | Instruction::Abort { .. } => vec![],
            _ if pc + 1 < code.len() => vec![pc + 1],
            _ => vec![],
        };
        for successor in successors {
            let incoming = (origins.clone(), resumes);
            match states.get_mut(successor) {
                Some(Some(existing)) if existing != &incoming => return false,
                Some(Some(_)) => {}
                Some(slot @ None) => {
                    *slot = Some(incoming);
                    work.push_back(successor);
                }
                None => return false,
            }
        }
    }
    returned
}

fn call_cancellation_discharged_by_handler(a: &Artifact, body_function: u32, callee: u32) -> bool {
    let actual = actual_function_outward_protocols(a);
    let cancellable = actual
        .get(callee as usize)
        .into_iter()
        .flatten()
        .flat_map(|protocol| {
            a.protocols[*protocol as usize]
                .operations
                .iter()
                .enumerate()
                .filter_map(move |(operation, descriptor)| {
                    (!descriptor.terminal && descriptor.resumption_lower == 0)
                        .then_some((*protocol, operation as u32))
                })
        })
        .collect::<Vec<_>>();
    if cancellable.is_empty() {
        return false;
    }
    let mut saw_context = false;
    for caller in &a.functions {
        let Ok(code) = function_code(a, caller) else {
            return false;
        };
        for instruction in code {
            let Instruction::Handle { handler, body, .. } = instruction else {
                continue;
            };
            let body_type = caller.register_types[*body as usize];
            if callable_type_producers(a, body_type)
                != std::collections::BTreeSet::from([body_function])
            {
                continue;
            }
            saw_context = true;
            let Ok(Type::Handler {
                handler_def,
                capture_type,
                ..
            }) = type_at(a, caller.register_types[*handler as usize])
            else {
                return false;
            };
            let Some(definition) = a.handler_defs.get(*handler_def as usize) else {
                return false;
            };
            let Ok(callable_types) =
                callable_capture_fields(a, *capture_type, definition.clauses.len())
            else {
                return false;
            };
            for protocol in cancellable
                .iter()
                .map(|(protocol, _)| *protocol)
                .collect::<std::collections::BTreeSet<_>>()
            {
                let Some(descriptor) = a.protocols.get(protocol as usize) else {
                    return false;
                };
                if (0..descriptor.operations.len() as u32).any(|operation| {
                    !definition
                        .clauses
                        .iter()
                        .any(|clause| clause.protocol == protocol && clause.operation == operation)
                }) {
                    return false;
                }
            }
            for &(protocol, operation) in &cancellable {
                let Some(index) = definition.clauses.iter().position(|clause| {
                    clause.protocol == protocol && clause.operation == operation
                }) else {
                    return false;
                };
                let clause = &definition.clauses[index];
                let Some(resumption_type) = clause.resumption_type else {
                    return false;
                };
                let parameter = clause.callable_signature.params.len().saturating_sub(1);
                if clause.callable_signature.params.get(parameter) != Some(&resumption_type) {
                    return false;
                }
                let producers = callable_type_producers(a, callable_types[index]);
                if producers.is_empty()
                    || !producers.iter().all(|producer| {
                        clause_resumes_parameter_exactly_once(a, *producer, parameter)
                    })
                {
                    return false;
                }
            }
        }
    }
    saw_context
}

fn function_body_may_cancel(a: &Artifact, function: u32) -> bool {
    function_body_has_effect(
        a,
        function,
        &mut Vec::new(),
        operation_is_cancellable,
        signature_may_cancel,
    )
}

fn verify_cancellation_capture(
    a: &Artifact,
    fid: u32,
    pc: u32,
    f: &Function,
    state: ContinuationState<'_>,
) -> Result<(), VerifyError> {
    let ContinuationState {
        live: state,
        move_paths,
        enum_variants,
        excluded,
        ..
    } = state;
    if let Some((register, _)) = state.iter().copied().enumerate().find(|(register, live)| {
        *live
            && !excluded.contains(&(*register as u32))
            && !residual_zero_use_allowed(
                a,
                f.register_types[*register],
                move_paths[*register].as_ref(),
                enum_variants[*register],
            )
    }) {
        return Err(VerifyError::LiveValueAtExit {
            function: fid,
            instruction: pc,
            register: register as u32,
        });
    }
    Ok(())
}

fn handler_dependency_zero_use_safe(a: &Artifact, id: TypeId) -> bool {
    let Ok(Type::Handler { capture_type, .. }) = type_at(a, id) else {
        return false;
    };
    if *capture_type == UNIT {
        return true;
    }
    let Some(callable_types) = a
        .types
        .get(*capture_type as usize)
        .and_then(|ty| crate::bytecode::construction_field_types(ty, None))
    else {
        return false;
    };
    callable_types.into_iter().all(|callable_type| {
        matches!(
            type_at(a, callable_type),
            Ok(Type::Callable {
                capture_type: environment,
                ..
            }) if zero_use_dependency(a, *environment)
        )
    })
}

fn handler_may_forward_terminal(a: &Artifact, id: TypeId, signature: &Signature) -> bool {
    let Ok(Type::Handler { handler_def, .. }) = type_at(a, id) else {
        return false;
    };
    let Some(definition) = a.handler_defs.get(*handler_def as usize) else {
        return false;
    };
    signature.outward_protocols.iter().any(|&protocol_id| {
        a.protocols
            .get(protocol_id as usize)
            .is_some_and(|protocol| {
                protocol
                    .operations
                    .iter()
                    .enumerate()
                    .any(|(operation_id, operation)| {
                        operation.terminal
                            && !definition.clauses.iter().any(|clause| {
                                clause.protocol == protocol_id
                                    && clause.operation == operation_id as u32
                            })
                    })
            })
    })
}

fn signature_may_multishot(a: &Artifact, signature: &Signature) -> bool {
    signature.outward_protocols.iter().any(|&protocol_id| {
        a.protocols
            .get(protocol_id as usize)
            .is_some_and(|protocol| {
                protocol
                    .operations
                    .iter()
                    .enumerate()
                    .any(|(operation, _)| operation_is_multishot(a, protocol_id, operation as u32))
            })
    })
}

fn function_body_may_multishot(a: &Artifact, function: u32) -> bool {
    function_body_has_effect(
        a,
        function,
        &mut Vec::new(),
        operation_is_multishot,
        signature_may_multishot,
    )
}

fn function_body_has_effect(
    a: &Artifact,
    function: u32,
    _visiting: &mut Vec<u32>,
    operation_has_effect: fn(&Artifact, u32, u32) -> bool,
    signature_has_effect: fn(&Artifact, &Signature) -> bool,
) -> bool {
    let dynamic_targets = a
        .functions
        .iter()
        .enumerate()
        .map(|(fid, descriptor)| {
            let labels = verify_labels(a, fid as u32, descriptor).ok()?;
            callable_targets_at_pcs(a, fid as u32, descriptor, &labels).ok()
        })
        .collect::<Vec<_>>();
    let mut summaries = vec![false; a.functions.len()];
    loop {
        let mut changed = false;
        for (fid, descriptor) in a.functions.iter().enumerate() {
            if summaries[fid] {
                continue;
            }
            let effect = function_code(a, descriptor).is_err()
                || function_code(a, descriptor).is_ok_and(|code| {
                    code.iter()
                        .enumerate()
                        .any(|(pc, instruction)| match instruction {
                            Instruction::Perform {
                                protocol: protocol_id,
                                operation,
                                ..
                            } => operation_has_effect(a, *protocol_id, *operation),
                            Instruction::Call { function, .. }
                            | Instruction::TailCall { function, .. }
                            | Instruction::CallKnownReceiver { function, .. }
                            | Instruction::TailCallKnownReceiver { function, .. } => {
                                summaries.get(*function as usize).copied().unwrap_or(true)
                            }
                            Instruction::CallIndirect { callable, .. }
                            | Instruction::TailCallIndirect { callable, .. } => dynamic_targets
                                [fid]
                                .as_ref()
                                .and_then(|at_pcs| at_pcs.get(pc))
                                .and_then(|registers| registers.get(*callable as usize))
                                .filter(|targets| !targets.is_empty())
                                .map_or_else(
                                    || {
                                        descriptor
                                            .register_types
                                            .get(*callable as usize)
                                            .and_then(|ty| type_at(a, *ty).ok())
                                            .is_none_or(|ty| {
                                                let Type::Callable { signature, .. } = ty else {
                                                    return true;
                                                };
                                                // An externally supplied callable may inhabit the
                                                // same type, so its declared signature remains the
                                                // conservative upper bound.
                                                signature_has_effect(a, signature)
                                            })
                                    },
                                    |targets| {
                                        targets.iter().any(|target| {
                                            summaries.get(*target as usize).copied().unwrap_or(true)
                                        })
                                    },
                                ),
                            Instruction::Handle { body, .. } => descriptor
                                .register_types
                                .get(*body as usize)
                                .and_then(|ty| type_at(a, *ty).ok())
                                .is_none_or(|ty| {
                                    let Type::Callable { signature, .. } = ty else {
                                        return true;
                                    };
                                    signature_has_effect(a, signature)
                                }),
                            Instruction::Resume { resumption, .. }
                            | Instruction::TailResume { resumption, .. } => descriptor
                                .register_types
                                .get(*resumption as usize)
                                .and_then(|ty| type_at(a, *ty).ok())
                                .is_none_or(|ty| {
                                    let Type::Resumption {
                                        effect_signature, ..
                                    } = ty
                                    else {
                                        return true;
                                    };
                                    signature_has_effect(a, effect_signature)
                                }),
                            _ => false,
                        })
                });
            if effect {
                summaries[fid] = true;
                changed = true;
            }
        }
        if !changed {
            return summaries.get(function as usize).copied().unwrap_or(true);
        }
    }
}

fn is_continuation_boundary_pc(a: &Artifact, function: &Function, pc: u32) -> bool {
    let Some(previous) = pc
        .checked_sub(1)
        .and_then(|previous| a.code.get(function.code_start as usize + previous as usize))
    else {
        return false;
    };
    matches!(
        previous,
        Instruction::Perform { dst: Some(_), .. }
            | Instruction::Call { .. }
            | Instruction::CallSelf { .. }
            | Instruction::CallKnownReceiver { .. }
            | Instruction::CallIndirect { .. }
            | Instruction::Handle { .. }
            | Instruction::Resume { .. }
    )
}

fn continuation_live_registers(
    a: &Artifact,
    function: &Function,
    label_states: &[Vec<LabelEntry>],
) -> Result<Vec<Vec<bool>>, VerifyError> {
    let len = function.code_len as usize;
    let registers = function.register_types.len();
    let mut live_in = vec![vec![false; registers]; len];
    loop {
        let mut changed = false;
        for pc in (0..len).rev() {
            let instruction = &a.code[function.code_start as usize + pc];
            let successors = match instruction {
                Instruction::Jump { target } => vec![*target],
                Instruction::Switch {
                    cases, otherwise, ..
                } => cases
                    .iter()
                    .map(|case| case.1)
                    .chain(std::iter::once(*otherwise))
                    .collect(),
                Instruction::Leave { slot, .. } => vec![
                    label_states[pc]
                        .iter()
                        .rfind(|entry| entry.slot == *slot)
                        .ok_or(VerifyError::InvalidFunction(u32::MAX))?
                        .target,
                ],
                Instruction::Return { .. }
                | Instruction::TailCall { .. }
                | Instruction::TailCallSelf { .. }
                | Instruction::TailCallKnownReceiver { .. }
                | Instruction::TailCallIndirect { .. }
                | Instruction::TailResume { .. }
                | Instruction::Perform { dst: None, .. }
                | Instruction::Unreachable
                | Instruction::Abort { .. } => vec![],
                _ if pc + 1 < len => vec![pc as u32 + 1],
                _ => vec![],
            };
            let mut next = vec![false; registers];
            for successor in successors {
                let successor = live_in
                    .get(successor as usize)
                    .ok_or(VerifyError::InvalidFunction(u32::MAX))?;
                for (slot, incoming) in next.iter_mut().zip(successor) {
                    *slot |= *incoming;
                }
            }
            if let Some(destination) = instruction_destination(instruction) {
                next[destination as usize] = false;
            }
            if let Instruction::Leave { slot, .. } = instruction {
                let result = label_states[pc]
                    .iter()
                    .rfind(|entry| entry.slot == *slot)
                    .ok_or(VerifyError::InvalidFunction(u32::MAX))?
                    .result_register;
                next[result as usize] = false;
            }
            for used in instruction_register_uses(instruction) {
                next[used as usize] = true;
            }
            if live_in[pc] != next {
                live_in[pc] = next;
                changed = true;
            }
        }
        if !changed {
            return Ok(live_in);
        }
    }
}

fn instruction_register_uses(instruction: &Instruction) -> Vec<u32> {
    match instruction {
        Instruction::Move { src, .. }
        | Instruction::Copy { src, .. }
        | Instruction::BorrowShared { src, .. }
        | Instruction::BorrowUnique { src, .. }
        | Instruction::DerefCopy { src, .. }
        | Instruction::DerefMove { src, .. }
        | Instruction::ProjectMove { src, .. }
        | Instruction::ProjectCopy { src, .. }
        | Instruction::ReborrowShared { src, .. }
        | Instruction::ReborrowUnique { src, .. }
        | Instruction::ProjectBorrowShared { src, .. }
        | Instruction::ProjectBorrowUnique { src, .. }
        | Instruction::EnumTag { src, .. }
        | Instruction::Deconstruct { src }
        | Instruction::Return { src: Some(src) }
        | Instruction::Leave { value: src, .. } => vec![*src],
        Instruction::DerefStore { dst, src } => vec![*dst, *src],
        Instruction::EndBorrow { reference } => vec![*reference],
        Instruction::Drop { register } => vec![*register],
        Instruction::Construct { fields, .. } => fields.clone(),
        Instruction::Primitive { args, .. }
        | Instruction::Call { args, .. }
        | Instruction::TailCall { args, .. }
        | Instruction::CallSelf { args, .. }
        | Instruction::TailCallSelf { args }
        | Instruction::MakeBindingPack { payloads: args, .. }
        | Instruction::Perform { payloads: args, .. }
        | Instruction::HostCall { args, .. } => args.clone(),
        Instruction::Switch { discr, .. } => vec![*discr],
        Instruction::CallKnownReceiver { receiver, args, .. }
        | Instruction::TailCallKnownReceiver { receiver, args, .. } => std::iter::once(*receiver)
            .chain(args.iter().copied())
            .collect(),
        Instruction::MakeCallable { captures, .. }
        | Instruction::MakeHandlerShared { captures, .. } => captures.clone(),
        Instruction::MakeHandler { clauses, .. } => clauses.clone(),
        Instruction::CallIndirect { callable, args, .. }
        | Instruction::TailCallIndirect { callable, args, .. } => std::iter::once(*callable)
            .chain(args.iter().copied())
            .collect(),
        Instruction::Handle {
            handler,
            body,
            args,
            ..
        } => std::iter::once(*handler)
            .chain(std::iter::once(*body))
            .chain(args.iter().copied())
            .collect(),
        Instruction::Resume {
            resumption, value, ..
        }
        | Instruction::TailResume {
            resumption, value, ..
        } => vec![*resumption, *value],
        Instruction::Cancel { resumption, .. } => vec![*resumption],
        _ => vec![],
    }
}

struct ContinuationState<'a> {
    live: &'a [bool],
    move_paths: &'a [Option<FieldInit>],
    enum_variants: &'a [Option<u32>],
    loans: &'a [CarrierLoans],
    excluded: &'a [u32],
    required: &'a [bool],
}

#[allow(clippy::too_many_arguments)]
fn verify_prunable_capture(
    a: &Artifact,
    fid: u32,
    pc: u32,
    f: &Function,
    live: &[bool],
    move_paths: &[Option<FieldInit>],
    enum_variants: &[Option<u32>],
    required: &[bool],
    excluded: &[u32],
) -> Result<(), VerifyError> {
    for (register, is_live) in live.iter().copied().enumerate() {
        if is_live
            && !excluded.contains(&(register as u32))
            && !required.get(register).copied().unwrap_or(false)
        {
            let ty = f.register_types[register];
            if residual_contains_custom_drop(
                a,
                ty,
                move_paths[register].as_ref(),
                enum_variants[register],
                &mut Vec::new(),
            ) || !residual_zero_use_allowed(
                a,
                ty,
                move_paths[register].as_ref(),
                enum_variants[register],
            ) {
                return Err(VerifyError::LiveValueAtExit {
                    function: fid,
                    instruction: pc,
                    register: register as u32,
                });
            }
        }
    }
    Ok(())
}

fn residual_contains_custom_drop(
    a: &Artifact,
    id: TypeId,
    fields: Option<&FieldInit>,
    variant: Option<u32>,
    visiting: &mut Vec<TypeId>,
) -> bool {
    if has_custom_drop(a, id) || visiting.contains(&id) {
        return has_custom_drop(a, id);
    }
    visiting.push(id);
    let contains = match fields {
        Some(fields @ FieldInit::Partial(_)) => residual_field_types(a, id, fields, variant)
            .is_none_or(|fields| {
                fields
                    .filter(|(initialized, _)| *initialized)
                    .any(|(_, ty)| residual_contains_custom_drop(a, ty, None, None, visiting))
            }),
        Some(FieldInit::Whole) | None => match type_at(a, id) {
            Ok(Type::Tuple { fields, .. }) => fields
                .iter()
                .any(|ty| residual_contains_custom_drop(a, *ty, None, None, visiting)),
            Ok(Type::Struct { fields, .. }) => fields
                .iter()
                .any(|field| residual_contains_custom_drop(a, field.ty, None, None, visiting)),
            Ok(Type::Enum { variants, .. }) => {
                if let Some(active) = variant.and_then(|variant| variants.get(variant as usize)) {
                    active.fields.iter().any(|field| {
                        residual_contains_custom_drop(a, field.ty, None, None, visiting)
                    })
                } else {
                    variants
                        .iter()
                        .flat_map(|variant| &variant.fields)
                        .any(|field| {
                            residual_contains_custom_drop(a, field.ty, None, None, visiting)
                        })
                }
            }
            Ok(Type::Callable { capture_type, .. }) | Ok(Type::Handler { capture_type, .. }) => {
                residual_contains_custom_drop(a, *capture_type, None, None, visiting)
            }
            Ok(Type::BindingPack { payload_type, .. }) => {
                residual_contains_custom_drop(a, *payload_type, None, None, visiting)
            }
            Ok(Type::Array { element }) => {
                residual_contains_custom_drop(a, *element, None, None, visiting)
            }
            _ => false,
        },
    };
    visiting.pop();
    contains
}

fn verify_multishot_capture(
    a: &Artifact,
    fid: u32,
    pc: u32,
    f: &Function,
    state: ContinuationState<'_>,
) -> Result<(), VerifyError> {
    let ContinuationState {
        live: state,
        move_paths,
        enum_variants,
        loans,
        excluded,
        required,
    } = state;
    // A multi-shot snapshot may retain an external shared target or remap an
    // internal shared target into the cloned owner graph. Unique loans cannot
    // be duplicated. An internal owner must itself remain in the snapshot.
    if let Some((register, _)) = loans.iter().enumerate().find(|(register, loans)| {
        required.get(*register).copied().unwrap_or(false)
            && loans.iter().any(|loan| loan.loan.unique)
    }) {
        return Err(VerifyError::BorrowConflict {
            function: fid,
            instruction: pc,
            register: register as u32,
        });
    }
    for (register, loan) in loans
        .iter()
        .enumerate()
        .flat_map(|(register, loans)| loans.iter().map(move |loan| (register, &loan.loan)))
    {
        if !required.get(register).copied().unwrap_or(false) {
            continue;
        }
        let owner = loan.place.owner as usize;
        if owner < f.register_types.len()
            && (!state[owner]
                || excluded.contains(&(owner as u32))
                || !required.get(owner).copied().unwrap_or(false))
        {
            return Err(VerifyError::BorrowConflict {
                function: fid,
                instruction: pc,
                register: register as u32,
            });
        }
    }
    for (register, live) in state.iter().copied().enumerate() {
        if live
            && required.get(register).copied().unwrap_or(false)
            && !excluded.contains(&(register as u32))
        {
            let ty = f.register_types[register];
            if !residual_snapshot_cloneable(
                a,
                ty,
                move_paths[register].as_ref(),
                enum_variants[register],
                &mut Vec::new(),
            ) {
                return Err(VerifyError::IllegalCopy {
                    function: fid,
                    instruction: pc,
                    ty,
                });
            }
        }
    }
    Ok(())
}

fn residual_field_types<'a>(
    a: &'a Artifact,
    id: TypeId,
    fields: &FieldInit,
    variant: Option<u32>,
) -> Option<impl Iterator<Item = (bool, TypeId)> + 'a> {
    let FieldInit::Partial(initialized) = fields else {
        return None;
    };
    let field_types = construction_field_types(&a.types[id as usize], variant)?;
    (field_types.len() == initialized.len()).then(|| {
        initialized
            .iter()
            .copied()
            .zip(field_types)
            .collect::<Vec<_>>()
            .into_iter()
    })
}

fn residual_zero_use_allowed(
    a: &Artifact,
    id: TypeId,
    fields: Option<&FieldInit>,
    variant: Option<u32>,
) -> bool {
    match fields {
        Some(FieldInit::Whole) | None => is_zero_use_allowed(a, id),
        Some(fields @ FieldInit::Partial(_)) => residual_field_types(a, id, fields, variant)
            .is_some_and(|mut fields| {
                fields.all(|(initialized, ty)| !initialized || is_zero_use_allowed(a, ty))
            }),
    }
}

/// Quantity-bearing leaves have their positive-lower obligation checked by
/// `verify_resumption_quantities`, which runs before the ordinary ownership
/// verifier and tracks Copy aliases as one logical group. Structural Drop may
/// therefore retire one such view even when its nominal type does not admit
/// zero use. Every initialized non-quantity field must still independently
/// admit zero use, and custom Drop remains governed by its declared type.
fn residual_quantity_drop_allowed(
    a: &Artifact,
    id: TypeId,
    fields: Option<&FieldInit>,
    variant: Option<u32>,
) -> bool {
    fn structural(a: &Artifact, id: TypeId, variant: Option<u32>, visiting: &mut [bool]) -> bool {
        if quantity_leaf_types(a, id).is_empty() {
            return is_zero_use_allowed(a, id);
        }
        if a.drop_glue.iter().any(|glue| glue.ty == id) || visiting[id as usize] {
            return false;
        }
        visiting[id as usize] = true;
        let allowed = match a.types[id as usize].representation() {
            Type::Resumption { .. } => true,
            Type::Tuple { fields, .. } => fields
                .iter()
                .all(|field| structural(a, *field, None, visiting)),
            Type::Struct { fields, .. } => fields
                .iter()
                .all(|field| structural(a, field.ty, None, visiting)),
            Type::Enum { variants, .. } => {
                if let Some(active) = variant.and_then(|active| variants.get(active as usize)) {
                    active
                        .fields
                        .iter()
                        .all(|field| structural(a, field.ty, None, visiting))
                } else {
                    variants
                        .iter()
                        .flat_map(|variant| &variant.fields)
                        .all(|field| structural(a, field.ty, None, visiting))
                }
            }
            Type::Callable { capture_type, .. } | Type::Handler { capture_type, .. } => {
                structural(a, *capture_type, None, visiting)
            }
            Type::BindingPack { payload_type, .. } => structural(a, *payload_type, None, visiting),
            _ => is_zero_use_allowed(a, id),
        };
        visiting[id as usize] = false;
        allowed
    }

    match fields {
        Some(FieldInit::Whole) | None => {
            structural(a, id, variant, &mut vec![false; a.types.len()])
        }
        Some(fields @ FieldInit::Partial(_)) => {
            !a.drop_glue.iter().any(|glue| glue.ty == id)
                && residual_field_types(a, id, fields, variant).is_some_and(|mut fields| {
                    fields.all(|(initialized, ty)| {
                        !initialized || structural(a, ty, None, &mut vec![false; a.types.len()])
                    })
                })
        }
    }
}

fn residual_snapshot_cloneable(
    a: &Artifact,
    id: TypeId,
    fields: Option<&FieldInit>,
    variant: Option<u32>,
    stack: &mut Vec<TypeId>,
) -> bool {
    match fields {
        Some(FieldInit::Whole) | None => snapshot_cloneable(a, id, stack),
        Some(fields @ FieldInit::Partial(_)) => {
            !a.drop_glue.iter().any(|glue| glue.ty == id)
                && residual_field_types(a, id, fields, variant).is_some_and(|mut fields| {
                    fields.all(|(initialized, ty)| !initialized || snapshot_cloneable(a, ty, stack))
                })
        }
    }
}

/// Stronger than ordinary `COPY` for arrays (which the VM can snapshot
/// structurally) and deliberately stricter for references and custom drop.
/// Owned layout cycles are rejected earlier, so the stack is only a guard for
/// opaque recursive dependencies.
fn snapshot_cloneable(a: &Artifact, id: TypeId, stack: &mut Vec<TypeId>) -> bool {
    if a.drop_glue.iter().any(|glue| glue.ty == id) {
        return false;
    }
    if stack.contains(&id) {
        return false;
    }
    stack.push(id);
    let result = match a.types[id as usize].representation() {
        Type::Unit
        | Type::U8
        | Type::U16
        | Type::U32
        | Type::U64
        | Type::U128
        | Type::I8
        | Type::I16
        | Type::I32
        | Type::I64
        | Type::I128
        | Type::Usize
        | Type::Isize
        | Type::F32
        | Type::F64
        | Type::Char
        | Type::Text
        | Type::Bytes
        | Type::Available { .. } => true,
        Type::RefShared { .. } => true,
        Type::Never | Type::RefUnique { .. } => false,
        Type::Array { element } => snapshot_cloneable(a, *element, stack),
        Type::Tuple { fields, .. } => fields
            .iter()
            .all(|&field| snapshot_cloneable(a, field, stack)),
        Type::Struct { fields, .. } => fields
            .iter()
            .all(|field| snapshot_cloneable(a, field.ty, stack)),
        Type::Enum { variants, .. } => variants
            .iter()
            .flat_map(|variant| &variant.fields)
            .all(|field| snapshot_cloneable(a, field.ty, stack)),
        Type::Callable {
            copy, capture_type, ..
        } => *copy && snapshot_cloneable(a, *capture_type, stack),
        // Handler values remain non-COPY in the language. The VM may clone an
        // active delimiter internally when every hidden clause capture is safe.
        Type::Handler { capture_type, .. } => snapshot_cloneable(a, *capture_type, stack),
        Type::Resumption { copy, .. } => *copy,
        Type::BindingPack {
            copy, payload_type, ..
        } => *copy && snapshot_cloneable(a, *payload_type, stack),
        Type::Restricted { .. } => unreachable!("representation peels restrictions"),
    };
    stack.pop();
    result
}

/// Handler delimiters are cloned as VM-owned graphs rather than through the
/// language-level `COPY` operation. Clause callable `copy` bits therefore do
/// not reject terminal alternatives, but every runtime node that is actually
/// duplicated must be free of custom Drop and each hidden environment must be
/// structurally snapshot-cloneable. The VM clone context preserves shared
/// callable-capture identity within a replay.
fn handler_snapshot_cloneable(a: &Artifact, id: TypeId) -> bool {
    if has_custom_drop(a, id) {
        return false;
    }
    let Type::Handler { capture_type, .. } = a.types[id as usize].representation() else {
        return false;
    };
    let Type::Tuple { fields, .. } = a.types[*capture_type as usize].representation() else {
        return false;
    };
    fields.iter().all(|field| {
        if has_custom_drop(a, *field) {
            return false;
        }
        let Type::Callable {
            capture_type: environment,
            ..
        } = a.types[*field as usize].representation()
        else {
            return false;
        };
        snapshot_cloneable(a, *environment, &mut Vec::new())
    })
}

fn is_copy(a: &Artifact, id: TypeId) -> bool {
    declared_type_at(a, id).is_ok_and(Type::claimed_duplicable) && supports_copy(a, id)
}

fn supports_copy(a: &Artifact, id: TypeId) -> bool {
    fn dependency(a: &Artifact, id: TypeId, visiting: &mut [bool]) -> bool {
        matches!(type_at(a, id), Ok(Type::Available { .. }))
            || (declared_type_at(a, id).is_ok_and(Type::claimed_duplicable)
                && supports(a, id, visiting))
    }

    fn supports(a: &Artifact, id: TypeId, visiting: &mut [bool]) -> bool {
        let Some(ty) = a.types.get(id as usize) else {
            return false;
        };
        if visiting[id as usize] {
            // Callable environment recursion is a nominal identity cycle. Its
            // capability is the greatest fixed point of the declared flags;
            // any concrete noncopy dependency encountered on the way still
            // makes the cycle false.
            return true;
        }
        visiting[id as usize] = true;
        let result = match ty.representation() {
            Type::Unit
            | Type::U8
            | Type::U16
            | Type::U32
            | Type::U64
            | Type::U128
            | Type::I8
            | Type::I16
            | Type::I32
            | Type::I64
            | Type::I128
            | Type::Usize
            | Type::Isize
            | Type::F32
            | Type::F64
            | Type::Char
            | Type::Text
            | Type::Bytes
            | Type::RefShared { .. } => true,
            Type::Never => false,
            Type::Array { .. } | Type::RefUnique { .. } => false,
            Type::Callable { capture_type, .. } => dependency(a, *capture_type, visiting),
            Type::Handler { .. } => false,
            Type::Resumption { upper_uses, .. } => upper_uses.is_none_or(|upper| upper > 1),
            Type::BindingPack { payload_type, .. } => dependency(a, *payload_type, visiting),
            // AVAILABLE has no runtime state, so an erased field never prevents its
            // containing nominal value from being structurally duplicable.
            Type::Available { .. } => true,
            Type::Tuple { fields, .. } => {
                fields.iter().all(|&field| dependency(a, field, visiting))
            }
            Type::Struct { fields, .. } => {
                fields.iter().all(|field| dependency(a, field.ty, visiting))
            }
            Type::Enum { variants, .. } => variants
                .iter()
                .flat_map(|variant| &variant.fields)
                .all(|field| dependency(a, field.ty, visiting)),
            Type::Restricted { .. } => unreachable!("representation peels restrictions"),
        };
        visiting[id as usize] = false;
        result
    }

    supports(a, id, &mut vec![false; a.types.len()])
}

fn is_zero_use_allowed(a: &Artifact, id: TypeId) -> bool {
    declared_type_at(a, id).is_ok_and(Type::claimed_zero_use_allowed) && supports_zero_use(a, id)
}

fn zero_use_dependency(a: &Artifact, id: TypeId) -> bool {
    matches!(type_at(a, id), Ok(Type::Available { .. })) || is_zero_use_allowed(a, id)
}

fn supports_zero_use(a: &Artifact, id: TypeId) -> bool {
    fn dependency(a: &Artifact, id: TypeId, visiting: &mut [bool]) -> bool {
        matches!(type_at(a, id), Ok(Type::Available { .. }))
            || (declared_type_at(a, id).is_ok_and(Type::claimed_zero_use_allowed)
                && supports(a, id, visiting))
    }

    fn supports(a: &Artifact, id: TypeId, visiting: &mut [bool]) -> bool {
        let Some(ty) = a.types.get(id as usize) else {
            return false;
        };
        if visiting[id as usize] {
            return true;
        }
        visiting[id as usize] = true;
        let result = match ty.representation() {
            Type::Unit
            | Type::U8
            | Type::U16
            | Type::U32
            | Type::U64
            | Type::U128
            | Type::I8
            | Type::I16
            | Type::I32
            | Type::I64
            | Type::I128
            | Type::Usize
            | Type::Isize
            | Type::F32
            | Type::F64
            | Type::Char
            | Type::Text
            | Type::Bytes
            | Type::RefShared { .. }
            | Type::RefUnique { .. } => true,
            Type::Never => false,
            Type::Available { .. } => true,
            Type::Array { element } => dependency(a, *element, visiting),
            Type::Tuple { fields, .. } => {
                fields.iter().all(|&field| dependency(a, field, visiting))
            }
            Type::Struct { fields, .. } => {
                fields.iter().all(|field| dependency(a, field.ty, visiting))
            }
            Type::Enum { variants, .. } => variants
                .iter()
                .flat_map(|variant| &variant.fields)
                .all(|field| dependency(a, field.ty, visiting)),
            Type::Callable { capture_type, .. } | Type::Handler { capture_type, .. } => {
                dependency(a, *capture_type, visiting)
            }
            Type::Resumption {
                input_type,
                output_type,
                lower_uses,
                ..
            } => {
                *lower_uses == 0
                    && dependency(a, *input_type, visiting)
                    && dependency(a, *output_type, visiting)
            }
            Type::BindingPack { payload_type, .. } => dependency(a, *payload_type, visiting),
            Type::Restricted { .. } => unreachable!("representation peels restrictions"),
        };
        visiting[id as usize] = false;
        result
    }

    supports(a, id, &mut vec![false; a.types.len()])
}
fn constant_type(a: &Artifact, c: &Constant) -> Result<TypeId, VerifyError> {
    let predicate: fn(&Type) -> bool = match c {
        Constant::Unit => |x| matches!(x, Type::Unit),
        Constant::U8(_) => |x| matches!(x, Type::U8),
        Constant::U16(_) => |x| matches!(x, Type::U16),
        Constant::U32(_) => |x| matches!(x, Type::U32),
        Constant::U64(_) => |x| matches!(x, Type::U64),
        Constant::U128(_) => |x| matches!(x, Type::U128),
        Constant::I8(_) => |x| matches!(x, Type::I8),
        Constant::I16(_) => |x| matches!(x, Type::I16),
        Constant::I32(_) => |x| matches!(x, Type::I32),
        Constant::I64(_) => |x| matches!(x, Type::I64),
        Constant::I128(_) => |x| matches!(x, Type::I128),
        Constant::Usize(_) => |x| matches!(x, Type::Usize),
        Constant::Isize(_) => |x| matches!(x, Type::Isize),
        Constant::F32(_) => |x| matches!(x, Type::F32),
        Constant::F64(_) => |x| matches!(x, Type::F64),
        Constant::Char(_) => |x| matches!(x, Type::Char),
        Constant::Text(_) => |x| matches!(x, Type::Text),
        Constant::Bytes(_) => |x| matches!(x, Type::Bytes),
    };
    a.types
        .iter()
        .position(|ty| predicate(ty.representation()))
        .map(|x| x as u32)
        .ok_or(VerifyError::InvalidType(u32::MAX))
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode::*;
    fn verify(artifact: Artifact) -> Result<VerifiedArtifact, VerifyError> {
        if artifact.cleanups.is_empty() && !artifact.functions.is_empty() {
            return with_generated_cleanup_plans(artifact).and_then(super::verify);
        }
        super::verify(artifact)
    }
    fn base(code: Vec<Instruction>, regs: Vec<TypeId>) -> Artifact {
        Artifact {
            types: Type::predefined(),
            constants: vec![Constant::I64(2)],
            imports: vec![],
            protocols: vec![],
            handler_defs: vec![],
            cleanups: vec![],
            exports: vec![],
            drop_glue: vec![],
            functions: vec![Function {
                flags: 0,
                name: "main".into(),
                params: vec![],
                return_type: I64,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: regs,
                code_start: 0,
                code_len: code.len() as u32,
                label_slot_count: 0,
            }],
            code,
            required_features: 1,
            entry_function: None,
        }
    }

    #[test]
    fn verified_runtime_boundary_checks_function_pc_and_cleanup_ranges() {
        let verified = verify(base(
            vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::Return { src: Some(1) },
            ],
            vec![UNIT, I64],
        ))
        .unwrap();

        assert!(verified.function(u32::MAX).is_none());
        let function = verified.function(0).unwrap();
        assert!(function.checked_pc(2).is_none());
        let entry = function.checked_pc(0).unwrap();
        let exit = function.checked_pc(1).unwrap();
        assert!(matches!(
            function.instruction(entry),
            Instruction::Const { .. }
        ));
        assert_eq!(function.cleanup_registers(entry), &[]);
        assert_eq!(function.cleanup_registers(exit), &[1]);
    }

    #[test]
    #[should_panic(expected = "verified PC used with wrong function")]
    fn forged_cross_function_pc_cannot_cross_the_runtime_boundary() {
        let verified = verify(base(vec![Instruction::Unreachable], vec![UNIT])).unwrap();
        let function = verified.function(0).unwrap();
        let forged = VerifiedPc {
            function: 1,
            offset: 0,
        };
        let _ = function.instruction(forged);
    }

    #[test]
    fn verified_runtime_indexes_are_compact_and_freeze_spare_code_capacity() {
        assert_eq!(
            std::mem::size_of::<VerifiedPc>(),
            2 * std::mem::size_of::<u32>()
        );
        assert_eq!(
            std::mem::size_of::<FunctionLayout>(),
            6 * std::mem::size_of::<u32>()
        );

        let mut artifact = base(vec![Instruction::Unreachable], vec![UNIT]);
        artifact.code.reserve(1024);
        artifact.functions.reserve(1024);
        assert!(artifact.code.capacity() > artifact.code.len());
        let verified = verify(artifact).unwrap();
        assert_eq!(
            verified.artifact().code.capacity(),
            verified.artifact().code.len()
        );
        assert_eq!(
            verified.artifact().functions.capacity(),
            verified.artifact().functions.len()
        );
    }

    fn reference_effect_transport_artifact(
        payload_type: TypeId,
        result_type: TypeId,
        upper: u32,
    ) -> Artifact {
        let mut types = Type::predefined();
        types.extend([
            Type::RefShared { referent: I64 },
            Type::RefUnique { referent: I64 },
        ]);
        Artifact {
            types,
            constants: vec![],
            imports: vec![],
            protocols: vec![Protocol {
                display_name: "Echo".into(),
                type_arguments: vec![],
                operations: vec![Operation {
                    name: "echo".into(),
                    payload_signature: Signature {
                        params: vec![payload_type],
                        result: UNIT,
                        outward_protocols: vec![],
                    },
                    result_type,
                    resumption_lower: 1,
                    resumption_upper: Some(upper),
                    terminal: false,
                }],
            }],
            handler_defs: vec![],
            cleanups: vec![],
            exports: vec![],
            drop_glue: vec![],
            functions: vec![Function {
                flags: 0,
                name: "reference_echo".into(),
                params: vec![payload_type],
                return_type: result_type,
                outward_protocols: vec![0],
                receiver_mode: None,
                register_types: vec![UNIT, payload_type, result_type],
                code_start: 0,
                code_len: 2,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Perform {
                    dst: Some(2),
                    protocol: 0,
                    operation: 0,
                    payloads: vec![1],
                },
                Instruction::Return { src: Some(2) },
            ],
            required_features: 1 | (1 << 1) | (1 << 3),
            entry_function: None,
        }
    }

    fn self_recursive_callable_artifact(mode: u32) -> Artifact {
        let mut types = Type::predefined();
        types.push(Type::Restricted {
            base: Box::new(Type::Tuple {
                fields: vec![I64],
                copy: true,
            }),
            duplicable: true,
            zero_use_allowed: true,
        });
        types.push(Type::Callable {
            signature: Signature {
                params: vec![I64],
                result: I64,
                outward_protocols: vec![],
            },
            capture_type: 19,
            receiver_mode: mode,
            identity_name: format!("recursive mode {mode}"),
            copy: true,
            zero_use_allowed: true,
        });
        types.extend([
            Type::RefShared { referent: 19 },
            Type::RefUnique { referent: 19 },
        ]);
        let mut wrapper = vec![
            Instruction::Const {
                dst: 1,
                constant: 4,
            },
            Instruction::MakeCallable {
                dst: 2,
                callable_type: 20,
                function: 1,
                captures: vec![1],
            },
            Instruction::Const {
                dst: 3,
                constant: 2,
            },
            Instruction::CallIndirect {
                dst: Some(4),
                callable: 2,
                receiver_mode: 2,
                args: vec![3],
            },
        ];
        wrapper.push(Instruction::Return { src: Some(4) });
        let recursive_start = wrapper.len() as u32;
        let recurse = if mode == 2 {
            Instruction::TailCallSelf { args: vec![4] }
        } else {
            Instruction::CallSelf {
                dst: Some(2),
                args: vec![4],
            }
        };
        let recursive = vec![
            Instruction::Switch {
                discr: 1,
                cases: vec![(0, 7)],
                otherwise: 1,
            },
            Instruction::Const {
                dst: 3,
                constant: 1,
            },
            Instruction::Primitive {
                dst: 4,
                op: Primitive::IntCheckedSub,
                args: vec![1, 3],
            },
            recurse,
            Instruction::Drop { register: 0 },
            Instruction::Return { src: Some(2) },
            Instruction::Unreachable,
            Instruction::Drop { register: 0 },
            Instruction::Const {
                dst: 2,
                constant: 3,
            },
            Instruction::Return { src: Some(2) },
        ];
        let wrapper_len = wrapper.len() as u32;
        let recursive_len = recursive.len() as u32;
        wrapper.extend(recursive);
        Artifact {
            types,
            constants: vec![
                Constant::I64(0),
                Constant::I64(1),
                Constant::I64(3),
                Constant::I64(42),
                Constant::I64(99),
            ],
            functions: vec![
                Function {
                    flags: 0,
                    name: "wrapper".into(),
                    params: vec![],
                    return_type: I64,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, I64, 20, I64, I64],
                    code_start: 0,
                    code_len: wrapper_len,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "recursive".into(),
                    params: vec![I64],
                    return_type: I64,
                    outward_protocols: vec![],
                    receiver_mode: Some(mode),
                    register_types: vec![
                        if mode == 0 {
                            21
                        } else if mode == 1 {
                            22
                        } else {
                            19
                        },
                        I64,
                        I64,
                        I64,
                        I64,
                    ],
                    code_start: recursive_start,
                    code_len: recursive_len,
                    label_slot_count: 0,
                },
            ],
            code: wrapper,
            required_features: 1 | (1 << 1),
            ..Artifact::default()
        }
    }

    #[test]
    fn borrowed_and_owned_receivers_execute_self_recursion() {
        for mode in 0..=2 {
            let artifact = verify(self_recursive_callable_artifact(mode))
                .unwrap_or_else(|error| panic!("receiver mode {mode}: {error:?}"));
            assert_eq!(
                crate::Vm::new(artifact).run(0, vec![]).unwrap(),
                crate::Value::I64(42),
                "receiver mode {mode}"
            );
        }
    }

    #[test]
    fn owned_receiver_rejects_non_tail_self_recursion() {
        let mut artifact = self_recursive_callable_artifact(2);
        let pc = artifact.functions[1].code_start as usize + 3;
        artifact.code[pc] = Instruction::CallSelf {
            dst: Some(2),
            args: vec![4],
        };
        assert_eq!(
            verify(artifact).unwrap_err(),
            VerifyError::InvalidFunction(1)
        );
    }

    #[test]
    fn unique_receiver_rejects_self_call_during_an_active_reborrow() {
        let mut artifact = self_recursive_callable_artifact(1);
        artifact.functions[1].register_types.push(22);
        let start = artifact.functions[1].code_start as usize;
        artifact
            .code
            .insert(start + 3, Instruction::ReborrowUnique { dst: 5, src: 0 });
        artifact.functions[1].code_len += 1;
        let Instruction::Switch { cases, .. } = &mut artifact.code[start] else {
            unreachable!()
        };
        cases[0].1 += 1;
        assert!(matches!(
            verify(artifact),
            Err(VerifyError::BorrowConflict {
                function: 1,
                register: 0,
                ..
            })
        ));
    }

    #[test]
    fn perform_transports_a_hand_built_shared_reference_origin() {
        let result = verify(reference_effect_transport_artifact(19, 19, 1));
        assert!(result.is_ok(), "{result:?}");
    }

    #[test]
    fn perform_rejects_missing_and_multishot_unique_reference_origins() {
        let missing = verify(reference_effect_transport_artifact(I64, 19, 1));
        assert!(
            matches!(&missing, Err(VerifyError::InvalidFunction(0))),
            "{missing:?}"
        );
        let multishot = verify(reference_effect_transport_artifact(20, 20, 2));
        assert!(
            matches!(
                &multishot,
                Err(VerifyError::BorrowConflict { function: 0, .. })
            ),
            "{multishot:?}"
        );
    }

    #[test]
    fn handler_snapshot_rejects_custom_drop_on_every_cloned_graph_node() {
        let mut types = Type::predefined();
        types.extend([
            Type::Struct {
                name: "Environment".into(),
                fields: vec![Field {
                    name: "value".into(),
                    ty: I64,
                }],
                copy: false,
            },
            Type::Callable {
                signature: Signature {
                    params: vec![],
                    result: UNIT,
                    outward_protocols: vec![],
                },
                capture_type: 19,
                receiver_mode: 2,
                identity_name: "terminal clause".into(),
                copy: false,
                zero_use_allowed: true,
            },
            Type::Tuple {
                fields: vec![20],
                copy: false,
            },
            Type::Handler {
                handler_def: 0,
                capture_type: 21,
                identity_name: "handler".into(),
            },
        ]);
        let artifact = Artifact {
            types,
            ..Artifact::default()
        };
        assert!(handler_snapshot_cloneable(&artifact, 22));

        for ty in [19, 20, 22] {
            let mut hostile = artifact.clone();
            hostile.drop_glue.push(DropGlue { ty, function: 0 });
            assert!(
                !handler_snapshot_cloneable(&hostile, 22),
                "custom Drop on graph node type {ty} must reject snapshot cloning"
            );
        }
    }

    #[test]
    fn shared_handler_clause_views_keep_one_optional_resumption_identity() {
        let mut types = Type::predefined();
        types.extend([
            Type::Resumption {
                identity_name: "optional captured resumption".into(),
                input_type: I64,
                output_type: I64,
                effect_signature: Signature {
                    params: vec![],
                    result: I64,
                    outward_protocols: vec![],
                },
                lower_uses: 0,
                upper_uses: Some(1),
                copy: false,
            },
            Type::Tuple {
                fields: vec![19],
                copy: false,
            }
            .restricted(false, true),
            Type::Callable {
                signature: Signature {
                    params: vec![],
                    result: I64,
                    outward_protocols: vec![],
                },
                capture_type: 20,
                receiver_mode: 2,
                identity_name: "left terminal clause".into(),
                copy: false,
                zero_use_allowed: true,
            },
            Type::Callable {
                signature: Signature {
                    params: vec![],
                    result: I64,
                    outward_protocols: vec![],
                },
                capture_type: 20,
                receiver_mode: 2,
                identity_name: "right terminal clause".into(),
                copy: false,
                zero_use_allowed: true,
            },
            Type::Tuple {
                fields: vec![21, 22],
                copy: false,
            },
            Type::Handler {
                handler_def: 0,
                capture_type: 23,
                identity_name: "shared optional handler".into(),
            },
            Type::Callable {
                signature: Signature {
                    params: vec![],
                    result: I64,
                    outward_protocols: vec![0],
                },
                capture_type: UNIT,
                receiver_mode: 2,
                identity_name: "handled body".into(),
                copy: false,
                zero_use_allowed: true,
            },
        ]);
        let terminal = |name: &str| Operation {
            name: name.into(),
            payload_signature: Signature {
                params: vec![],
                result: UNIT,
                outward_protocols: vec![],
            },
            result_type: NEVER,
            resumption_lower: 0,
            resumption_upper: Some(0),
            terminal: true,
        };
        let clause = |operation| HandlerClause {
            protocol: 0,
            operation,
            resumption_type: None,
            callable_signature: Signature {
                params: vec![],
                result: I64,
                outward_protocols: vec![],
            },
        };
        let artifact = Artifact {
            required_features: 1 | (1 << 3),
            types,
            constants: vec![Constant::I64(7)],
            protocols: vec![Protocol {
                display_name: "Gate".into(),
                type_arguments: vec![],
                operations: vec![terminal("left"), terminal("right")],
            }],
            handler_defs: vec![HandlerDef {
                result_type: I64,
                clauses: vec![clause(0), clause(1)],
                partial: false,
            }],
            functions: vec![
                Function {
                    flags: 0,
                    name: "run".into(),
                    params: vec![19],
                    return_type: I64,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, 19, 24, 25, I64],
                    code_start: 0,
                    code_len: 4,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "left".into(),
                    params: vec![],
                    return_type: I64,
                    outward_protocols: vec![],
                    receiver_mode: Some(2),
                    register_types: vec![20, I64],
                    code_start: 4,
                    code_len: 3,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "right".into(),
                    params: vec![],
                    return_type: I64,
                    outward_protocols: vec![],
                    receiver_mode: Some(2),
                    register_types: vec![20, I64],
                    code_start: 7,
                    code_len: 3,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "body".into(),
                    params: vec![],
                    return_type: I64,
                    outward_protocols: vec![0],
                    receiver_mode: Some(2),
                    register_types: vec![UNIT],
                    code_start: 10,
                    code_len: 1,
                    label_slot_count: 0,
                },
            ],
            code: vec![
                Instruction::MakeHandlerShared {
                    dst: 2,
                    handler_def: 0,
                    functions: vec![1, 2],
                    captures: vec![1],
                },
                Instruction::MakeCallable {
                    dst: 3,
                    callable_type: 25,
                    function: 3,
                    captures: vec![],
                },
                Instruction::Handle {
                    dst: 4,
                    handler: 2,
                    body: 3,
                    args: vec![],
                },
                Instruction::Return { src: Some(4) },
                Instruction::Drop { register: 0 },
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::Return { src: Some(1) },
                Instruction::Drop { register: 0 },
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::Return { src: Some(1) },
                Instruction::Perform {
                    dst: None,
                    protocol: 0,
                    operation: 0,
                    payloads: vec![],
                },
            ],
            ..Artifact::default()
        };

        verify(artifact).expect("shared clause aliases must discharge one quantity owner");
    }

    #[test]
    fn shared_handler_borrowed_alternative_rejects_wrong_resume_delta() {
        let mut artifact = Artifact::default();
        artifact.types.push(Type::Resumption {
            identity_name: "exact twice".into(),
            input_type: I64,
            output_type: I64,
            effect_signature: Signature {
                params: vec![],
                result: I64,
                outward_protocols: vec![],
            },
            lower_uses: 2,
            upper_uses: Some(2),
            copy: true,
        });
        assert!(!quantity_deltas_satisfy(&artifact, &[1], &[19]));
        assert!(quantity_deltas_satisfy(&artifact, &[2], &[19]));
        assert!(!quantity_deltas_satisfy(&artifact, &[3], &[19]));
    }

    #[test]
    fn exact_outward_inference_removes_a_locally_handled_protocol() {
        let mut types = Type::predefined();
        types.extend([
            Type::Callable {
                signature: Signature {
                    params: vec![],
                    result: UNIT,
                    outward_protocols: vec![0, 1],
                },
                capture_type: UNIT,
                receiver_mode: 2,
                identity_name: "handled body".into(),
                copy: false,
                zero_use_allowed: true,
            },
            Type::Callable {
                signature: Signature {
                    params: vec![],
                    result: UNIT,
                    outward_protocols: vec![],
                },
                capture_type: UNIT,
                receiver_mode: 2,
                identity_name: "terminal clause".into(),
                copy: false,
                zero_use_allowed: true,
            },
            Type::Tuple {
                fields: vec![20],
                copy: false,
            },
            Type::Handler {
                handler_def: 0,
                capture_type: 21,
                identity_name: "local handler".into(),
            },
        ]);
        let terminal = |name: &str| Operation {
            name: name.into(),
            payload_signature: Signature {
                params: vec![],
                result: UNIT,
                outward_protocols: vec![],
            },
            result_type: NEVER,
            resumption_lower: 0,
            resumption_upper: Some(0),
            terminal: true,
        };
        let artifact = Artifact {
            types,
            protocols: vec![
                Protocol {
                    display_name: "Hidden".into(),
                    type_arguments: vec![],
                    operations: vec![terminal("hidden")],
                },
                Protocol {
                    display_name: "Visible".into(),
                    type_arguments: vec![],
                    operations: vec![terminal("visible")],
                },
            ],
            handler_defs: vec![HandlerDef {
                result_type: UNIT,
                clauses: vec![HandlerClause {
                    protocol: 0,
                    operation: 0,
                    resumption_type: None,
                    callable_signature: Signature {
                        params: vec![],
                        result: UNIT,
                        outward_protocols: vec![],
                    },
                }],
                partial: false,
            }],
            functions: vec![Function {
                flags: 0,
                name: "conservative".into(),
                params: vec![22, 19],
                return_type: UNIT,
                outward_protocols: vec![0, 1],
                receiver_mode: None,
                register_types: vec![UNIT, 22, 19, UNIT],
                code_start: 0,
                code_len: 2,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Handle {
                    dst: 3,
                    handler: 1,
                    body: 2,
                    args: vec![],
                },
                Instruction::Return { src: Some(3) },
            ],
            ..Artifact::default()
        };

        assert_eq!(
            actual_function_outward_protocols(&artifact)[0]
                .iter()
                .copied()
                .collect::<Vec<_>>(),
            vec![1]
        );
    }

    #[test]
    fn optional_clause_disposition_requires_one_resume_and_forbids_cancel() {
        let mut types = Type::predefined();
        types.push(Type::Resumption {
            identity_name: "optional".into(),
            input_type: I64,
            output_type: I64,
            effect_signature: Signature {
                params: vec![],
                result: I64,
                outward_protocols: vec![],
            },
            lower_uses: 0,
            upper_uses: Some(1),
            copy: false,
        });
        let artifact = Artifact {
            types,
            constants: vec![Constant::I64(2)],
            functions: vec![Function {
                flags: 0,
                name: "resume_once".into(),
                params: vec![19],
                return_type: I64,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 19, I64, I64],
                code_start: 0,
                code_len: 3,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Const {
                    dst: 2,
                    constant: 0,
                },
                Instruction::Resume {
                    dst: 3,
                    resumption: 1,
                    receiver_mode: 2,
                    value: 2,
                },
                Instruction::Return { src: Some(3) },
            ],
            ..Artifact::default()
        };
        assert!(clause_resumes_parameter_exactly_once(&artifact, 0, 0));

        let mut cancelling = artifact;
        cancelling.code[1] = Instruction::Cancel {
            dst: 3,
            resumption: 1,
        };
        assert!(!clause_resumes_parameter_exactly_once(&cancelling, 0, 0));
    }

    #[test]
    fn rejects_use_after_move() {
        let a = base(
            vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::Move { dst: 2, src: 1 },
                Instruction::Drop { register: 2 },
                Instruction::Return { src: Some(1) },
            ],
            vec![UNIT, I64, I64],
        );
        assert!(matches!(verify(a), Err(VerifyError::UseOfEmpty { .. })));
    }

    #[test]
    fn deref_copy_preserves_a_live_loan_and_requires_a_duplicable_referent() {
        let mut valid = base(
            vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::BorrowShared { dst: 2, src: 1 },
                Instruction::DerefCopy { dst: 3, src: 2 },
                Instruction::DerefCopy { dst: 4, src: 2 },
                Instruction::EndBorrow { reference: 2 },
                Instruction::Drop { register: 1 },
                Instruction::Drop { register: 3 },
                Instruction::Return { src: Some(4) },
            ],
            vec![UNIT, I64, 19, I64, I64],
        );
        valid.types.push(Type::RefShared { referent: I64 });
        valid.required_features |= 1 << 1;
        verify(valid).expect("DEREF_COPY must leave its source reference and loan live");

        let mut noncopy = base(
            vec![
                Instruction::Construct {
                    dst: 1,
                    ty: 19,
                    variant: None,
                    fields: vec![],
                },
                Instruction::BorrowShared { dst: 2, src: 1 },
                Instruction::DerefCopy { dst: 3, src: 2 },
                Instruction::Abort { message: None },
            ],
            vec![UNIT, 19, 20, 19],
        );
        noncopy.types.push(Type::Struct {
            name: "Linear".into(),
            fields: vec![],
            copy: false,
        });
        noncopy.types.push(Type::RefShared { referent: 19 });
        noncopy.required_features |= 1 << 1;
        assert!(matches!(
            verify(noncopy),
            Err(VerifyError::IllegalCopy {
                function: 0,
                instruction: 2,
                ty: 19,
            })
        ));
    }

    #[test]
    fn deref_copy_rejects_nonreferences_wrong_destinations_and_suspended_parents() {
        let mut nonreference = base(
            vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::DerefCopy { dst: 2, src: 1 },
                Instruction::Return { src: Some(2) },
            ],
            vec![UNIT, I64, I64],
        );
        nonreference.required_features |= 1 << 1;
        let nonreference_error = verify(nonreference).unwrap_err();
        assert!(
            matches!(
                &nonreference_error,
                VerifyError::BorrowConflict {
                    function: 0,
                    instruction: 1,
                    register: 1,
                }
            ),
            "{nonreference_error:?}"
        );

        let mut wrong_destination = base(
            vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::BorrowShared { dst: 2, src: 1 },
                Instruction::DerefCopy { dst: 3, src: 2 },
                Instruction::Abort { message: None },
            ],
            vec![UNIT, I64, 19, U64],
        );
        wrong_destination
            .types
            .push(Type::RefShared { referent: I64 });
        wrong_destination.required_features |= 1 << 1;
        let wrong_destination_error = verify(wrong_destination).unwrap_err();
        assert!(
            matches!(
                &wrong_destination_error,
                VerifyError::TypeMismatch {
                    function: 0,
                    instruction: 2,
                    expected: I64,
                    actual: U64,
                }
            ),
            "{wrong_destination_error:?}"
        );

        let mut suspended = base(
            vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::BorrowUnique { dst: 2, src: 1 },
                Instruction::ReborrowShared { dst: 3, src: 2 },
                Instruction::DerefCopy { dst: 4, src: 2 },
                Instruction::Abort { message: None },
            ],
            vec![UNIT, I64, 19, 20, I64],
        );
        suspended.types.push(Type::RefUnique { referent: I64 });
        suspended.types.push(Type::RefShared { referent: I64 });
        suspended.required_features |= 1 << 1;
        assert!(matches!(
            verify(suspended),
            Err(VerifyError::BorrowConflict {
                function: 0,
                instruction: 3,
                register: 2,
            })
        ));
    }

    fn deref_move_artifact(code: Vec<Instruction>, regs: Vec<TypeId>) -> Artifact {
        let mut artifact = base(code, regs);
        artifact.types.push(Type::RefUnique { referent: I64 });
        artifact.required_features |= 1 << 1;
        artifact
    }

    #[test]
    fn deref_move_store_preserves_the_unique_loan_and_restores_the_place() {
        let artifact = deref_move_artifact(
            vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::BorrowUnique { dst: 2, src: 1 },
                Instruction::DerefMove { dst: 3, src: 2 },
                Instruction::Const {
                    dst: 4,
                    constant: 0,
                },
                Instruction::DerefStore { dst: 2, src: 4 },
                Instruction::EndBorrow { reference: 2 },
                Instruction::Drop { register: 1 },
                Instruction::Return { src: Some(3) },
            ],
            vec![UNIT, I64, 19, I64, I64],
        );
        verify(artifact).expect("a restored unique referent must verify");
    }

    #[test]
    fn deref_holes_reject_early_end_double_move_and_overwrite() {
        let early_end = deref_move_artifact(
            vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::BorrowUnique { dst: 2, src: 1 },
                Instruction::DerefMove { dst: 3, src: 2 },
                Instruction::EndBorrow { reference: 2 },
                Instruction::Abort { message: None },
            ],
            vec![UNIT, I64, 19, I64],
        );
        assert!(matches!(
            verify(early_end),
            Err(VerifyError::BorrowConflict {
                instruction: 3,
                register: 2,
                ..
            })
        ));

        let double_move = deref_move_artifact(
            vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::BorrowUnique { dst: 2, src: 1 },
                Instruction::DerefMove { dst: 3, src: 2 },
                Instruction::DerefMove { dst: 4, src: 2 },
                Instruction::Abort { message: None },
            ],
            vec![UNIT, I64, 19, I64, I64],
        );
        assert!(matches!(
            verify(double_move),
            Err(VerifyError::BorrowConflict {
                instruction: 3,
                register: 2,
                ..
            })
        ));

        let overwrite = deref_move_artifact(
            vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::BorrowUnique { dst: 2, src: 1 },
                Instruction::Const {
                    dst: 3,
                    constant: 0,
                },
                Instruction::DerefStore { dst: 2, src: 3 },
                Instruction::Abort { message: None },
            ],
            vec![UNIT, I64, 19, I64],
        );
        assert!(matches!(
            verify(overwrite),
            Err(VerifyError::BorrowConflict {
                instruction: 3,
                register: 2,
                ..
            })
        ));

        let mut shared = base(
            vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::BorrowShared { dst: 2, src: 1 },
                Instruction::DerefMove { dst: 3, src: 2 },
                Instruction::Abort { message: None },
            ],
            vec![UNIT, I64, 19, I64],
        );
        shared.types.push(Type::RefShared { referent: I64 });
        shared.required_features |= 1 << 1;
        assert!(matches!(
            verify(shared),
            Err(VerifyError::BorrowConflict {
                instruction: 2,
                register: 2,
                ..
            })
        ));

        let mut suspended = deref_move_artifact(
            vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::BorrowUnique { dst: 2, src: 1 },
                Instruction::ReborrowShared { dst: 3, src: 2 },
                Instruction::DerefMove { dst: 4, src: 2 },
                Instruction::Abort { message: None },
            ],
            vec![UNIT, I64, 19, 20, I64],
        );
        suspended.types.push(Type::RefShared { referent: I64 });
        assert!(matches!(
            verify(suspended),
            Err(VerifyError::BorrowConflict {
                instruction: 3,
                register: 2,
                ..
            })
        ));
    }

    #[test]
    fn deref_hole_state_must_match_at_cfg_joins_but_abort_needs_no_restore() {
        let mut joined = deref_move_artifact(
            vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::BorrowUnique { dst: 2, src: 1 },
                Instruction::Const {
                    dst: 3,
                    constant: 1,
                },
                Instruction::Switch {
                    discr: 3,
                    cases: vec![(1, 4)],
                    otherwise: 7,
                },
                Instruction::DerefMove { dst: 4, src: 2 },
                Instruction::Drop { register: 4 },
                Instruction::Jump { target: 8 },
                Instruction::Jump { target: 8 },
                Instruction::EndBorrow { reference: 2 },
                Instruction::Drop { register: 1 },
                Instruction::Const {
                    dst: 5,
                    constant: 0,
                },
                Instruction::Return { src: Some(5) },
            ],
            vec![UNIT, I64, 19, U32, I64, I64],
        );
        joined.constants.push(Constant::U32(0));
        assert!(matches!(
            verify(joined),
            Err(VerifyError::StateMismatch { instruction: 8, .. })
        ));

        let aborting = deref_move_artifact(
            vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::BorrowUnique { dst: 2, src: 1 },
                Instruction::DerefMove { dst: 3, src: 2 },
                Instruction::Abort { message: None },
            ],
            vec![UNIT, I64, 19, I64],
        );
        verify(aborting).expect("an abort edge performs no cleanup and may retain a hole");
    }

    #[test]
    fn copy_consults_the_claimed_duplicable_capability() {
        let mut a = base(
            vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::Copy { dst: 2, src: 1 },
                Instruction::Drop { register: 1 },
                Instruction::Return { src: Some(2) },
            ],
            vec![UNIT, I64, I64],
        );
        a.types[I64 as usize] = Type::I64.restricted(false, true);
        assert!(matches!(verify(a), Err(VerifyError::IllegalCopy { .. })));
    }

    #[test]
    fn drop_rejects_exact_linear_scalar_and_aggregate_wrappers() {
        let mut scalar = base(
            vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::Drop { register: 1 },
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::Return { src: Some(1) },
            ],
            vec![UNIT, I64],
        );
        scalar.types[I64 as usize] = Type::I64.restricted(true, false);
        assert!(matches!(
            with_generated_cleanup_plans(scalar),
            Err(VerifyError::LiveValueAtExit {
                function: 0,
                instruction: 1,
                register: 1,
            })
        ));

        let mut aggregate = base(
            vec![
                Instruction::Const {
                    dst: 2,
                    constant: 0,
                },
                Instruction::Construct {
                    dst: 1,
                    ty: 19,
                    variant: None,
                    fields: vec![2],
                },
                Instruction::Drop { register: 1 },
                Instruction::Const {
                    dst: 2,
                    constant: 0,
                },
                Instruction::Return { src: Some(2) },
            ],
            vec![UNIT, 19, I64],
        );
        aggregate.types.push(
            Type::Struct {
                name: "ExactBox".into(),
                fields: vec![Field {
                    name: "value".into(),
                    ty: I64,
                }],
                copy: false,
            }
            .restricted(false, false),
        );
        assert!(matches!(
            verify(aggregate),
            Err(VerifyError::LiveValueAtExit {
                function: 0,
                instruction: 2,
                register: 1,
            })
        ));
    }

    #[test]
    fn drop_accepts_unrestricted_scalar_and_affine_aggregate() {
        let scalar = base(
            vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::Drop { register: 1 },
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::Return { src: Some(1) },
            ],
            vec![UNIT, I64],
        );
        verify(scalar).expect("unrestricted scalars allow zero-use disposal");

        let mut aggregate = base(
            vec![
                Instruction::Const {
                    dst: 2,
                    constant: 0,
                },
                Instruction::Construct {
                    dst: 1,
                    ty: 19,
                    variant: None,
                    fields: vec![2],
                },
                Instruction::Drop { register: 1 },
                Instruction::Const {
                    dst: 2,
                    constant: 0,
                },
                Instruction::Return { src: Some(2) },
            ],
            vec![UNIT, 19, I64],
        );
        aggregate.types.push(
            Type::Struct {
                name: "AffineBox".into(),
                fields: vec![Field {
                    name: "value".into(),
                    ty: I64,
                }],
                copy: false,
            }
            .restricted(false, true),
        );
        verify(aggregate).expect("affine aggregate allows recursive zero-use disposal");
    }

    #[test]
    fn rejects_zero_use_overclaim_over_restricted_child() {
        let mut a = base(
            vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::Return { src: Some(1) },
            ],
            vec![UNIT, I64],
        );
        a.types[I64 as usize] = Type::I64.restricted(true, false);
        a.types.push(
            Type::Struct {
                name: "ExactChild".into(),
                fields: vec![Field {
                    name: "value".into(),
                    ty: I64,
                }],
                copy: false,
            }
            .restricted(false, true),
        );
        assert!(matches!(verify(a), Err(VerifyError::InvalidType(19))));
    }

    #[test]
    fn deconstruct_accepts_restricted_struct_after_exhaustive_project_move() {
        let mut a = base(
            vec![
                Instruction::Const {
                    dst: 2,
                    constant: 0,
                },
                Instruction::Construct {
                    dst: 1,
                    ty: 19,
                    variant: None,
                    fields: vec![2],
                },
                Instruction::ProjectMove {
                    dst: 2,
                    src: 1,
                    field: 0,
                },
                Instruction::Deconstruct { src: 1 },
                Instruction::Return { src: Some(2) },
            ],
            vec![UNIT, 19, I64],
        );
        a.types.push(
            Type::Struct {
                name: "ExactBox".into(),
                fields: vec![Field {
                    name: "value".into(),
                    ty: I64,
                }],
                copy: false,
            }
            .restricted(false, false),
        );

        verify(a).expect("an exhaustively moved restricted aggregate is an empty shell");
    }

    #[test]
    fn deconstruct_rejects_an_initialized_remainder() {
        let mut a = base(
            vec![
                Instruction::Const {
                    dst: 2,
                    constant: 0,
                },
                Instruction::Construct {
                    dst: 1,
                    ty: 19,
                    variant: None,
                    fields: vec![2],
                },
                Instruction::Deconstruct { src: 1 },
                Instruction::Return { src: Some(2) },
            ],
            vec![UNIT, 19, I64],
        );
        a.types.push(Type::Struct {
            name: "StillFull".into(),
            fields: vec![Field {
                name: "value".into(),
                ty: I64,
            }],
            copy: false,
        });

        assert!(matches!(
            verify(a),
            Err(VerifyError::InvalidAggregate {
                function: 0,
                instruction: 2,
            })
        ));
    }

    #[test]
    fn deconstruct_accepts_fieldless_struct_and_active_enum_variant() {
        for aggregate in [
            Type::Struct {
                name: "Empty".into(),
                fields: vec![],
                copy: false,
            },
            Type::Enum {
                name: "Choice".into(),
                variants: vec![EnumVariant {
                    name: "Empty".into(),
                    fields: vec![],
                }],
                copy: false,
            },
        ] {
            let variant = matches!(aggregate, Type::Enum { .. }).then_some(0);
            let mut a = base(
                vec![
                    Instruction::Construct {
                        dst: 1,
                        ty: 19,
                        variant,
                        fields: vec![],
                    },
                    Instruction::Deconstruct { src: 1 },
                    Instruction::Const {
                        dst: 2,
                        constant: 0,
                    },
                    Instruction::Return { src: Some(2) },
                ],
                vec![UNIT, 19, I64],
            );
            a.types.push(aggregate);

            verify(a).expect("a fieldless active aggregate is already an empty shell");
        }
    }

    #[test]
    fn deconstruct_requires_whole_place_exclusivity() {
        let mut a = base(
            vec![
                Instruction::Construct {
                    dst: 1,
                    ty: 19,
                    variant: None,
                    fields: vec![],
                },
                Instruction::BorrowShared { dst: 2, src: 1 },
                Instruction::Deconstruct { src: 1 },
                Instruction::EndBorrow { reference: 2 },
                Instruction::Const {
                    dst: 3,
                    constant: 0,
                },
                Instruction::Return { src: Some(3) },
            ],
            vec![UNIT, 19, 20, I64],
        );
        a.types.push(Type::Struct {
            name: "Empty".into(),
            fields: vec![],
            copy: false,
        });
        a.types.push(Type::RefShared { referent: 19 });
        a.required_features |= 1 << 1;

        assert!(matches!(
            verify(a),
            Err(VerifyError::BorrowConflict {
                function: 0,
                instruction: 2,
                register: 1,
            })
        ));
    }

    #[test]
    fn deconstruct_cannot_bypass_custom_drop_on_empty_shells() {
        fn hostile(
            aggregate: Type,
            attacker: Vec<Instruction>,
            registers: Vec<TypeId>,
            return_type: TypeId,
        ) -> Artifact {
            let mut types = Type::predefined();
            types.push(aggregate.restricted(false, true));
            types.push(Type::RefUnique { referent: 19 });
            let hook_len = 2;
            Artifact {
                types,
                constants: vec![Constant::I64(2)],
                drop_glue: vec![DropGlue {
                    ty: 19,
                    function: 0,
                }],
                functions: vec![
                    Function {
                        flags: DROP_HOOK,
                        name: "drop_resource".into(),
                        params: vec![20],
                        return_type: UNIT,
                        outward_protocols: vec![],
                        receiver_mode: None,
                        register_types: vec![UNIT, 20],
                        code_start: 0,
                        code_len: hook_len,
                        label_slot_count: 0,
                    },
                    Function {
                        flags: 0,
                        name: "bypass".into(),
                        params: vec![],
                        return_type,
                        outward_protocols: vec![],
                        receiver_mode: None,
                        register_types: registers,
                        code_start: hook_len,
                        code_len: attacker.len() as u32,
                        label_slot_count: 0,
                    },
                ],
                code: [
                    vec![
                        Instruction::EndBorrow { reference: 1 },
                        Instruction::Return { src: None },
                    ],
                    attacker,
                ]
                .concat(),
                required_features: 1 | (1 << 1),
                ..Artifact::default()
            }
        }

        for (aggregate, variant) in [
            (
                Type::Struct {
                    name: "EmptyResource".into(),
                    fields: vec![],
                    copy: false,
                },
                None,
            ),
            (
                Type::Enum {
                    name: "ResourceState".into(),
                    variants: vec![EnumVariant {
                        name: "Empty".into(),
                        fields: vec![],
                    }],
                    copy: false,
                },
                Some(0),
            ),
        ] {
            let artifact = hostile(
                aggregate,
                vec![
                    Instruction::Construct {
                        dst: 1,
                        ty: 19,
                        variant,
                        fields: vec![],
                    },
                    Instruction::Deconstruct { src: 1 },
                    Instruction::Return { src: None },
                ],
                vec![UNIT, 19],
                UNIT,
            );
            assert!(matches!(
                verify(artifact),
                Err(VerifyError::InvalidAggregate {
                    function: 1,
                    instruction: 1,
                })
            ));
        }

        let partial = hostile(
            Type::Struct {
                name: "PayloadResource".into(),
                fields: vec![Field {
                    name: "payload".into(),
                    ty: I64,
                }],
                copy: false,
            },
            vec![
                Instruction::Const {
                    dst: 2,
                    constant: 0,
                },
                Instruction::Construct {
                    dst: 1,
                    ty: 19,
                    variant: None,
                    fields: vec![2],
                },
                Instruction::ProjectMove {
                    dst: 2,
                    src: 1,
                    field: 0,
                },
                Instruction::Deconstruct { src: 1 },
                Instruction::Return { src: Some(2) },
            ],
            vec![UNIT, 19, I64],
            I64,
        );
        assert!(matches!(
            verify(partial),
            Err(VerifyError::InvalidAggregate {
                function: 1,
                instruction: 2,
            })
        ));

        for (aggregate, variant) in [
            (
                Type::Struct {
                    name: "StructResource".into(),
                    fields: vec![Field {
                        name: "payload".into(),
                        ty: I64,
                    }],
                    copy: false,
                },
                None,
            ),
            (
                Type::Enum {
                    name: "EnumResource".into(),
                    variants: vec![EnumVariant {
                        name: "Payload".into(),
                        fields: vec![Field {
                            name: "0".into(),
                            ty: I64,
                        }],
                    }],
                    copy: false,
                },
                Some(0),
            ),
        ] {
            let artifact = hostile(
                aggregate,
                vec![
                    Instruction::Const {
                        dst: 2,
                        constant: 0,
                    },
                    Instruction::Construct {
                        dst: 1,
                        ty: 19,
                        variant,
                        fields: vec![2],
                    },
                    Instruction::ProjectMove {
                        dst: 2,
                        src: 1,
                        field: 0,
                    },
                    Instruction::Drop { register: 1 },
                    Instruction::Return { src: Some(2) },
                ],
                vec![UNIT, 19, I64],
                I64,
            );
            assert!(matches!(
                verify(artifact),
                Err(VerifyError::InvalidAggregate {
                    function: 1,
                    instruction: 2,
                })
            ));
        }
    }

    #[test]
    fn custom_drop_preserves_copy_whole_move_and_complete_zero_use_drop() {
        for (aggregate, variant) in [
            (
                Type::Struct {
                    name: "CopyStructResource".into(),
                    fields: vec![Field {
                        name: "payload".into(),
                        ty: I64,
                    }],
                    copy: true,
                },
                None,
            ),
            (
                Type::Enum {
                    name: "CopyEnumResource".into(),
                    variants: vec![EnumVariant {
                        name: "Payload".into(),
                        fields: vec![Field {
                            name: "0".into(),
                            ty: I64,
                        }],
                    }],
                    copy: true,
                },
                Some(0),
            ),
        ] {
            let mut types = Type::predefined();
            types.push(aggregate.restricted(true, true));
            types.push(Type::RefUnique { referent: 19 });
            let body = vec![
                Instruction::Const {
                    dst: 3,
                    constant: 0,
                },
                Instruction::Construct {
                    dst: 1,
                    ty: 19,
                    variant,
                    fields: vec![3],
                },
                Instruction::Copy { dst: 2, src: 1 },
                Instruction::Drop { register: 2 },
                Instruction::Move { dst: 2, src: 1 },
                Instruction::Drop { register: 2 },
                Instruction::Return { src: None },
            ];
            let hook_len = 2;
            let artifact = Artifact {
                types,
                constants: vec![Constant::I64(2)],
                drop_glue: vec![DropGlue {
                    ty: 19,
                    function: 0,
                }],
                functions: vec![
                    Function {
                        flags: DROP_HOOK,
                        name: "drop_resource".into(),
                        params: vec![20],
                        return_type: UNIT,
                        outward_protocols: vec![],
                        receiver_mode: None,
                        register_types: vec![UNIT, 20],
                        code_start: 0,
                        code_len: hook_len,
                        label_slot_count: 0,
                    },
                    Function {
                        flags: 0,
                        name: "legal".into(),
                        params: vec![],
                        return_type: UNIT,
                        outward_protocols: vec![],
                        receiver_mode: None,
                        register_types: vec![UNIT, 19, 19, I64],
                        code_start: hook_len,
                        code_len: body.len() as u32,
                        label_slot_count: 0,
                    },
                ],
                code: [
                    vec![
                        Instruction::EndBorrow { reference: 1 },
                        Instruction::Return { src: None },
                    ],
                    body,
                ]
                .concat(),
                required_features: 1 | (1 << 1),
                ..Artifact::default()
            };

            verify(artifact)
                .expect("copying and whole-moving a complete custom-Drop value must remain legal");
        }
    }
    #[test]
    fn rejects_leak_at_return() {
        let mut a = base(
            vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::Const {
                    dst: 2,
                    constant: 0,
                },
                Instruction::Return { src: Some(1) },
            ],
            vec![UNIT, I64, I64],
        );
        a.types[I64 as usize] = Type::I64.restricted(true, false);
        assert!(matches!(
            verify(a),
            Err(VerifyError::LiveValueAtExit { register: 2, .. })
        ));
    }

    #[test]
    fn permits_implicit_cleanup_for_zero_use_owner_at_return() {
        let a = base(
            vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::Const {
                    dst: 2,
                    constant: 0,
                },
                Instruction::Return { src: Some(1) },
            ],
            vec![UNIT, I64, I64],
        );
        assert!(verify(a).is_ok());
    }

    #[test]
    fn none32_return_is_valid_only_for_unit() {
        let artifact = base(vec![Instruction::Return { src: None }], vec![UNIT]);
        let error = verify(artifact).unwrap_err();
        assert!(
            matches!(error, VerifyError::InvalidFunction(0)),
            "{error:?}"
        );
    }

    #[test]
    fn none32_call_destination_rejects_a_value_result() {
        let artifact = Artifact {
            types: Type::predefined(),
            constants: vec![Constant::I64(1)],
            functions: vec![
                Function {
                    flags: 0,
                    name: "caller".into(),
                    params: vec![],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT],
                    code_start: 0,
                    code_len: 2,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "value".into(),
                    params: vec![],
                    return_type: I64,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, I64],
                    code_start: 2,
                    code_len: 2,
                    label_slot_count: 0,
                },
            ],
            code: vec![
                Instruction::Call {
                    dst: None,
                    function: 1,
                    args: vec![],
                },
                Instruction::Return { src: None },
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::Return { src: Some(1) },
            ],
            ..Artifact::default()
        };
        assert!(matches!(
            verify(artifact),
            Err(VerifyError::InvalidFunction(1))
        ));
    }

    #[test]
    fn none32_indirect_call_destination_rejects_a_value_result() {
        let mut types = Type::predefined();
        types.push(Type::Callable {
            signature: Signature {
                params: vec![],
                result: I64,
                outward_protocols: vec![],
            },
            capture_type: UNIT,
            receiver_mode: 2,
            identity_name: "value thunk".into(),
            copy: true,
            zero_use_allowed: true,
        });
        let artifact = Artifact {
            types,
            constants: vec![Constant::I64(1)],
            functions: vec![
                Function {
                    flags: 0,
                    name: "caller".into(),
                    params: vec![],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, 19],
                    code_start: 0,
                    code_len: 3,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "value".into(),
                    params: vec![],
                    return_type: I64,
                    outward_protocols: vec![],
                    receiver_mode: Some(2),
                    register_types: vec![UNIT, I64],
                    code_start: 3,
                    code_len: 3,
                    label_slot_count: 0,
                },
            ],
            code: vec![
                Instruction::MakeCallable {
                    dst: 1,
                    callable_type: 19,
                    function: 1,
                    captures: vec![],
                },
                Instruction::CallIndirect {
                    dst: None,
                    callable: 1,
                    receiver_mode: 2,
                    args: vec![],
                },
                Instruction::Return { src: None },
                Instruction::Drop { register: 0 },
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::Return { src: Some(1) },
            ],
            ..Artifact::default()
        };
        assert!(matches!(
            verify(artifact),
            Err(VerifyError::InvalidFunction(0))
        ));
    }

    #[test]
    fn none32_call_destination_accepts_a_never_result() {
        let artifact = Artifact {
            functions: vec![
                Function {
                    flags: 0,
                    name: "caller".into(),
                    params: vec![],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT],
                    code_start: 0,
                    code_len: 2,
                    label_slot_count: 0,
                },
                Function {
                    flags: NO_RETURN,
                    name: "diverge".into(),
                    params: vec![],
                    return_type: NEVER,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT],
                    code_start: 2,
                    code_len: 1,
                    label_slot_count: 0,
                },
            ],
            code: vec![
                Instruction::Call {
                    dst: None,
                    function: 1,
                    args: vec![],
                },
                Instruction::Return { src: None },
                Instruction::Unreachable,
            ],
            ..Artifact::default()
        };
        assert!(verify(artifact).is_ok());
    }

    #[test]
    fn rejects_a_primitive_with_the_wrong_result_type() {
        let a = Artifact {
            types: Type::predefined(),
            constants: vec![Constant::Text("a".into()), Constant::Text("b".into())],
            imports: vec![],
            protocols: vec![],
            handler_defs: vec![],
            cleanups: vec![],
            exports: vec![],
            drop_glue: vec![],
            functions: vec![Function {
                flags: 0,
                name: "main".into(),
                params: vec![],
                return_type: TEXT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, TEXT, TEXT, TEXT],
                code_start: 0,
                code_len: 4,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::Const {
                    dst: 2,
                    constant: 1,
                },
                Instruction::Primitive {
                    dst: 3,
                    op: Primitive::TextEq,
                    args: vec![1, 2],
                },
                Instruction::Return { src: Some(3) },
            ],
            required_features: 1,
            entry_function: None,
        };
        assert!(matches!(
            verify(a),
            Err(VerifyError::InvalidPrimitive { .. })
        ));
    }

    #[test]
    fn finish_drained_consumes_an_exact_linear_array_shell_with_exact_types() {
        let mut types = Type::predefined();
        types[U64 as usize] = Type::U64.restricted(false, false);
        types.push(Type::Array { element: U64 });
        let artifact = Artifact {
            required_features: 1 | (1 << 7),
            types,
            constants: vec![],
            imports: vec![],
            protocols: vec![],
            handler_defs: vec![],
            cleanups: vec![],
            exports: vec![],
            drop_glue: vec![],
            functions: vec![Function {
                flags: 0,
                name: "finish".into(),
                params: vec![19],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 19, UNIT],
                code_start: 0,
                code_len: 2,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Primitive {
                    dst: 2,
                    op: Primitive::ArrayFinishDrained,
                    args: vec![1],
                },
                Instruction::Return { src: Some(2) },
            ],
            entry_function: None,
        };
        verify(artifact.clone()).expect("drained-shell consumption is an owned transition");

        let mut ordinary_drop = artifact.clone();
        ordinary_drop.required_features = 1;
        ordinary_drop.code[0] = Instruction::Drop { register: 1 };
        assert!(matches!(
            verify(ordinary_drop),
            Err(VerifyError::LiveValueAtExit { register: 1, .. })
        ));

        let mut wrong_argument = artifact;
        wrong_argument.functions[0].params[0] = U64;
        wrong_argument.functions[0].register_types[1] = U64;
        assert!(matches!(
            verify(wrong_argument),
            Err(VerifyError::InvalidPrimitive { .. })
        ));
    }

    #[test]
    fn rejects_moving_an_array_while_uniquely_borrowed() {
        let mut types = Type::predefined();
        types.push(Type::Array { element: U64 });
        types.push(Type::RefUnique { referent: 19 });
        let a = Artifact {
            types,
            constants: vec![Constant::Unit],
            imports: vec![],
            protocols: vec![],
            handler_defs: vec![],
            cleanups: vec![],
            exports: vec![],
            drop_glue: vec![],
            functions: vec![Function {
                flags: 0,
                name: "main".into(),
                params: vec![],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 19, 20, UNIT],
                code_start: 0,
                code_len: 6,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Primitive {
                    dst: 1,
                    op: Primitive::ArrayEmpty,
                    args: vec![],
                },
                Instruction::BorrowUnique { dst: 2, src: 1 },
                Instruction::Drop { register: 1 },
                Instruction::EndBorrow { reference: 2 },
                Instruction::Const {
                    dst: 3,
                    constant: 0,
                },
                Instruction::Return { src: Some(3) },
            ],
            required_features: 1 | (1 << 1),
            entry_function: None,
        };
        assert!(matches!(
            verify(a),
            Err(VerifyError::BorrowConflict { register: 1, .. })
        ));
    }

    #[test]
    fn rejects_a_unique_borrow_while_a_shared_loan_is_live() {
        let mut types = Type::predefined();
        types.push(Type::Array { element: U64 });
        types.push(Type::RefShared { referent: 19 });
        types.push(Type::RefUnique { referent: 19 });
        let a = Artifact {
            types,
            constants: vec![Constant::Unit],
            imports: vec![],
            protocols: vec![],
            handler_defs: vec![],
            cleanups: vec![],
            exports: vec![],
            drop_glue: vec![],
            functions: vec![Function {
                flags: 0,
                name: "main".into(),
                params: vec![],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 19, 20, 21, UNIT],
                code_start: 0,
                code_len: 8,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Primitive {
                    dst: 1,
                    op: Primitive::ArrayEmpty,
                    args: vec![],
                },
                Instruction::BorrowShared { dst: 2, src: 1 },
                Instruction::BorrowUnique { dst: 3, src: 1 },
                Instruction::EndBorrow { reference: 3 },
                Instruction::EndBorrow { reference: 2 },
                Instruction::Drop { register: 1 },
                Instruction::Const {
                    dst: 4,
                    constant: 0,
                },
                Instruction::Return { src: Some(4) },
            ],
            required_features: 1 | (1 << 1),
            entry_function: None,
        };
        assert!(matches!(
            verify(a),
            Err(VerifyError::BorrowConflict { register: 1, .. })
        ));
    }

    #[test]
    fn rejects_enum_payload_projection_without_a_variant_fact() {
        let mut types = Type::predefined();
        types.push(Type::Enum {
            name: "Choice".into(),
            variants: vec![
                EnumVariant {
                    name: "Signed".into(),
                    fields: vec![Field {
                        name: "value".into(),
                        ty: I64,
                    }],
                },
                EnumVariant {
                    name: "Unsigned".into(),
                    fields: vec![Field {
                        name: "value".into(),
                        ty: U64,
                    }],
                },
            ],
            copy: false,
        });
        let a = Artifact {
            types,
            cleanups: vec![],
            exports: vec![],
            drop_glue: vec![],
            functions: vec![Function {
                flags: 0,
                name: "bad".into(),
                params: vec![19],
                return_type: I64,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 19, I64],
                code_start: 0,
                code_len: 3,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::ProjectMove {
                    dst: 2,
                    src: 1,
                    field: 0,
                },
                Instruction::Drop { register: 1 },
                Instruction::Return { src: Some(2) },
            ],
            required_features: 1,
            entry_function: None,
            ..Artifact::default()
        };
        assert!(matches!(
            verify(a),
            Err(VerifyError::InvalidAggregate { instruction: 0, .. })
        ));
    }

    #[test]
    fn enum_payload_borrow_requires_exact_variant_and_projection_bounds() {
        let mut types = Type::predefined();
        types.push(Type::Enum {
            name: "Choice".into(),
            variants: vec![
                EnumVariant {
                    name: "Value".into(),
                    fields: vec![Field {
                        name: "value".into(),
                        ty: I64,
                    }],
                },
                EnumVariant {
                    name: "Empty".into(),
                    fields: vec![],
                },
            ],
            copy: false,
        });
        types.push(Type::RefShared { referent: I64 });
        let artifact = |variant, field| Artifact {
            types: types.clone(),
            constants: vec![Constant::I64(42)],
            functions: vec![Function {
                flags: 0,
                name: "project".into(),
                params: vec![],
                return_type: 19,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, I64, 19, 20],
                code_start: 0,
                code_len: 5,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::Construct {
                    dst: 2,
                    ty: 19,
                    variant: Some(variant),
                    fields: (variant == 0).then_some(vec![1]).unwrap_or_default(),
                },
                Instruction::ProjectBorrowShared {
                    dst: 3,
                    src: 2,
                    field,
                },
                Instruction::EndBorrow { reference: 3 },
                Instruction::Return { src: Some(2) },
            ],
            required_features: 1 | (1 << 1),
            ..Artifact::default()
        };

        verify(artifact(0, 0)).expect("the constructed variant proves its payload bounds");
        for invalid in [artifact(0, 1), artifact(1, 0)] {
            assert!(matches!(
                verify(invalid),
                Err(VerifyError::InvalidAggregate { instruction: 2, .. })
            ));
        }

        let mut unproven = artifact(0, 0);
        unproven.functions[0].params = vec![19];
        unproven.functions[0].register_types = vec![UNIT, 19, 20];
        unproven.functions[0].code_len = 3;
        unproven.code = vec![
            Instruction::ProjectBorrowShared {
                dst: 2,
                src: 1,
                field: 0,
            },
            Instruction::EndBorrow { reference: 2 },
            Instruction::Return { src: Some(1) },
        ];
        assert!(matches!(
            verify(unproven),
            Err(VerifyError::InvalidAggregate { instruction: 0, .. })
        ));
    }

    #[test]
    fn rejects_parent_unique_reference_use_while_a_reborrow_is_live() {
        let mut types = Type::predefined();
        types.push(Type::Struct {
            name: "Pair".into(),
            fields: vec![Field {
                name: "value".into(),
                ty: I64,
            }],
            copy: false,
        });
        types.push(Type::RefUnique { referent: 19 });
        types.push(Type::RefShared { referent: 19 });
        types.push(Type::RefUnique { referent: I64 });
        let a = Artifact {
            types,
            constants: vec![Constant::Unit],
            imports: vec![],
            protocols: vec![],
            handler_defs: vec![],
            cleanups: vec![],
            exports: vec![],
            drop_glue: vec![],
            functions: vec![Function {
                flags: 0,
                name: "bad".into(),
                params: vec![19],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 19, 20, 21, 22, UNIT],
                code_start: 0,
                code_len: 9,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::BorrowUnique { dst: 2, src: 1 },
                Instruction::ReborrowShared { dst: 3, src: 2 },
                Instruction::ProjectBorrowUnique {
                    dst: 4,
                    src: 2,
                    field: 0,
                },
                Instruction::EndBorrow { reference: 4 },
                Instruction::EndBorrow { reference: 3 },
                Instruction::EndBorrow { reference: 2 },
                Instruction::Drop { register: 1 },
                Instruction::Const {
                    dst: 5,
                    constant: 0,
                },
                Instruction::Return { src: Some(5) },
            ],
            required_features: 1 | (1 << 1),
            entry_function: None,
        };
        assert!(matches!(
            verify(a),
            Err(VerifyError::BorrowConflict { register: 2, .. })
        ));
    }

    fn nested_split_borrow_artifact(second_field: u32) -> Artifact {
        let mut types = Type::predefined();
        types.push(Type::Struct {
            name: "Pair".into(),
            fields: vec![
                Field {
                    name: "left".into(),
                    ty: I64,
                },
                Field {
                    name: "right".into(),
                    ty: I64,
                },
            ],
            copy: false,
        });
        types.push(Type::RefUnique { referent: 19 });
        types.push(Type::RefUnique { referent: I64 });
        Artifact {
            types,
            constants: vec![Constant::Unit],
            functions: vec![Function {
                flags: 0,
                name: "split".into(),
                params: vec![19],
                return_type: 19,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 19, 20, 21, 21],
                code_start: 0,
                code_len: 7,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::BorrowUnique { dst: 2, src: 1 },
                Instruction::ProjectBorrowUnique {
                    dst: 3,
                    src: 2,
                    field: 0,
                },
                Instruction::ProjectBorrowUnique {
                    dst: 4,
                    src: 2,
                    field: second_field,
                },
                Instruction::EndBorrow { reference: 4 },
                Instruction::EndBorrow { reference: 3 },
                Instruction::EndBorrow { reference: 2 },
                Instruction::Return { src: Some(1) },
            ],
            required_features: 1 | (1 << 1),
            ..Artifact::default()
        }
    }

    #[test]
    fn unique_carrier_may_split_into_simultaneous_disjoint_children() {
        verify(nested_split_borrow_artifact(1)).expect("sibling fields are disjoint");
    }

    #[test]
    fn unique_carrier_cannot_split_into_overlapping_children() {
        assert!(matches!(
            verify(nested_split_borrow_artifact(0)),
            Err(VerifyError::BorrowConflict { register: 2, .. })
        ));
    }

    #[test]
    fn rejects_reading_a_field_after_it_was_moved() {
        let mut types = Type::predefined();
        types.push(Type::Struct {
            name: "Pair".into(),
            fields: vec![
                Field {
                    name: "left".into(),
                    ty: I64,
                },
                Field {
                    name: "right".into(),
                    ty: I64,
                },
            ],
            copy: false,
        });
        let a = Artifact {
            types,
            cleanups: vec![],
            exports: vec![],
            drop_glue: vec![],
            functions: vec![Function {
                flags: 0,
                name: "bad".into(),
                params: vec![19],
                return_type: I64,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 19, I64, I64],
                code_start: 0,
                code_len: 5,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::ProjectMove {
                    dst: 2,
                    src: 1,
                    field: 0,
                },
                Instruction::Drop { register: 2 },
                Instruction::ProjectCopy {
                    dst: 3,
                    src: 1,
                    field: 0,
                },
                Instruction::Drop { register: 1 },
                Instruction::Return { src: Some(3) },
            ],
            required_features: 1,
            entry_function: None,
            ..Artifact::default()
        };
        assert!(matches!(
            verify(a),
            Err(VerifyError::InvalidAggregate { instruction: 2, .. })
        ));
    }

    #[test]
    fn reference_parameters_have_external_provenance_for_reborrowing() {
        let mut types = Type::predefined();
        types.push(Type::Struct {
            name: "Cell".into(),
            fields: vec![Field {
                name: "value".into(),
                ty: I64,
            }],
            copy: false,
        });
        types.push(Type::RefUnique { referent: 19 });
        types.push(Type::RefShared { referent: 19 });
        let a = Artifact {
            types,
            constants: vec![Constant::Unit],
            imports: vec![],
            protocols: vec![],
            handler_defs: vec![],
            cleanups: vec![],
            exports: vec![],
            drop_glue: vec![],
            functions: vec![Function {
                flags: 0,
                name: "observe".into(),
                params: vec![20],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 20, 21, UNIT],
                code_start: 0,
                code_len: 5,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::ReborrowShared { dst: 2, src: 1 },
                Instruction::EndBorrow { reference: 2 },
                Instruction::EndBorrow { reference: 1 },
                Instruction::Const {
                    dst: 3,
                    constant: 0,
                },
                Instruction::Return { src: Some(3) },
            ],
            required_features: 1 | (1 << 1),
            entry_function: None,
        };
        assert!(verify(a).is_ok());
    }

    #[test]
    fn recursive_reference_relation_cannot_be_forged_from_a_local_borrow() {
        let mut types = Type::predefined();
        types.push(Type::RefShared { referent: I64 });
        let artifact = Artifact {
            types,
            constants: vec![Constant::I64(1)],
            functions: vec![Function {
                flags: 0,
                name: "bad_recursive_relay".into(),
                params: vec![19],
                return_type: 19,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 19, I64, 19],
                code_start: 0,
                code_len: 3,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Const {
                    dst: 2,
                    constant: 0,
                },
                Instruction::BorrowShared { dst: 3, src: 2 },
                Instruction::TailCall {
                    function: 0,
                    args: vec![3],
                },
            ],
            required_features: 1 | (1 << 1),
            ..Artifact::default()
        };
        assert!(matches!(
            verify(artifact),
            Err(VerifyError::InvalidFunction(0))
        ));
    }

    #[test]
    fn direct_call_uses_callee_reference_provenance_with_multiple_reference_arguments() {
        let mut types = Type::predefined();
        types.push(Type::RefShared { referent: I64 });
        let artifact = Artifact {
            types,
            functions: vec![
                Function {
                    flags: 0,
                    name: "relay".into(),
                    params: vec![19, 19],
                    return_type: 19,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, 19, 19, 19],
                    code_start: 0,
                    code_len: 2,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "select_left".into(),
                    params: vec![19, 19],
                    return_type: 19,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, 19, 19, 19],
                    code_start: 2,
                    code_len: 4,
                    label_slot_count: 0,
                },
            ],
            code: vec![
                Instruction::Call {
                    dst: Some(3),
                    function: 1,
                    args: vec![1, 2],
                },
                Instruction::Return { src: Some(3) },
                Instruction::Copy { dst: 3, src: 1 },
                Instruction::Drop { register: 2 },
                Instruction::Drop { register: 1 },
                Instruction::Return { src: Some(3) },
            ],
            required_features: 1 | (1 << 1),
            ..Artifact::default()
        };
        verify(artifact).expect("the returned loan follows the callee-selected first parameter");
    }

    #[test]
    fn aggregate_reference_return_must_remain_rooted_in_a_parameter() {
        let mut types = Type::predefined();
        types.push(Type::RefShared { referent: I64 });
        types.push(Type::Enum {
            name: "MaybeRef".into(),
            variants: vec![
                EnumVariant {
                    name: "None".into(),
                    fields: vec![],
                },
                EnumVariant {
                    name: "Some".into(),
                    fields: vec![Field {
                        name: "value".into(),
                        ty: 19,
                    }],
                },
            ],
            copy: false,
        });
        let valid = Artifact {
            types: types.clone(),
            functions: vec![Function {
                flags: 0,
                name: "wrap_parameter".into(),
                params: vec![19],
                return_type: 20,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 19, 20],
                code_start: 0,
                code_len: 2,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Construct {
                    dst: 2,
                    ty: 20,
                    variant: Some(1),
                    fields: vec![1],
                },
                Instruction::Return { src: Some(2) },
            ],
            required_features: 1 | (1 << 1),
            ..Artifact::default()
        };
        verify(valid).expect("a wrapped parameter borrow may escape");

        let hostile = Artifact {
            types,
            constants: vec![Constant::I64(1)],
            functions: vec![Function {
                flags: 0,
                name: "wrap_local".into(),
                params: vec![],
                return_type: 20,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, I64, 19, 20],
                code_start: 0,
                code_len: 4,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::BorrowShared { dst: 2, src: 1 },
                Instruction::Construct {
                    dst: 3,
                    ty: 20,
                    variant: Some(1),
                    fields: vec![2],
                },
                Instruction::Return { src: Some(3) },
            ],
            required_features: 1 | (1 << 1),
            ..Artifact::default()
        };
        assert!(matches!(
            verify(hostile),
            Err(VerifyError::InvalidFunction(0))
        ));
    }

    #[test]
    fn rejects_a_copy_descriptor_with_noncopy_fields() {
        let mut types = Type::predefined();
        types.push(Type::Array { element: U64 });
        types.push(Type::Struct {
            name: "Invalid".into(),
            fields: vec![Field {
                name: "items".into(),
                ty: 19,
            }],
            copy: true,
        });
        let a = Artifact {
            types,
            ..Artifact::default()
        };
        assert!(matches!(verify(a), Err(VerifyError::InvalidType(20))));
    }

    fn terminal_operation(name: &str, outward_protocols: Vec<u32>) -> Operation {
        Operation {
            name: name.into(),
            payload_signature: Signature {
                params: vec![],
                result: UNIT,
                outward_protocols,
            },
            result_type: NEVER,
            resumption_lower: 0,
            resumption_upper: Some(0),
            terminal: true,
        }
    }

    #[test]
    fn rejects_feature_bits_that_do_not_exactly_describe_raw_artifact() {
        let mut artifact = Artifact::default();
        artifact.code.push(Instruction::LabelPop { slot: 0 });
        assert_eq!(
            verify(artifact).unwrap_err(),
            VerifyError::InvalidFeatures(1)
        );
    }

    #[test]
    fn rejects_unsorted_outward_protocol_rows() {
        let mut artifact = base(
            vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::Return { src: Some(1) },
            ],
            vec![UNIT, I64],
        );
        artifact.protocols = vec![
            Protocol {
                display_name: "A".into(),
                type_arguments: vec![],
                operations: vec![],
            },
            Protocol {
                display_name: "B".into(),
                type_arguments: vec![],
                operations: vec![],
            },
        ];
        artifact.functions[0].outward_protocols = vec![1, 0];
        artifact.required_features |= 1 << 3;
        assert_eq!(
            verify(artifact).unwrap_err(),
            VerifyError::InvalidFunction(0)
        );
    }

    #[test]
    fn rejects_duplicate_protocol_identity_keys() {
        let protocol = Protocol {
            display_name: "Duplicate".into(),
            type_arguments: vec![I64],
            operations: vec![],
        };
        let artifact = Artifact {
            required_features: 1 | (1 << 3),
            protocols: vec![protocol.clone(), protocol],
            ..Artifact::default()
        };
        assert!(matches!(verify(artifact), Err(VerifyError::InvalidType(_))));
    }

    fn instantiated_protocol_artifact() -> Artifact {
        let mut types = Type::predefined();
        types.push(Type::Resumption {
            identity_name: "Generic<i64>::operation".into(),
            input_type: I64,
            output_type: UNIT,
            effect_signature: Signature {
                params: vec![],
                result: UNIT,
                outward_protocols: vec![],
            },
            lower_uses: 1,
            upper_uses: Some(1),
            copy: false,
        });
        types.push(Type::Resumption {
            identity_name: "Generic<Text>::operation".into(),
            input_type: TEXT,
            output_type: UNIT,
            effect_signature: Signature {
                params: vec![],
                result: UNIT,
                outward_protocols: vec![],
            },
            lower_uses: 0,
            upper_uses: Some(1),
            copy: false,
        });
        let operation = |payload, result, lower| Operation {
            name: "operation".into(),
            payload_signature: Signature {
                params: vec![payload],
                result: UNIT,
                outward_protocols: vec![],
            },
            result_type: result,
            resumption_lower: lower,
            resumption_upper: Some(1),
            terminal: false,
        };
        Artifact {
            required_features: 1 | (1 << 3),
            types,
            protocols: vec![
                Protocol {
                    display_name: "Generic".into(),
                    type_arguments: vec![I64],
                    operations: vec![operation(I64, I64, 1)],
                },
                Protocol {
                    display_name: "Generic".into(),
                    type_arguments: vec![TEXT],
                    operations: vec![operation(TEXT, TEXT, 0)],
                },
            ],
            handler_defs: vec![HandlerDef {
                result_type: UNIT,
                clauses: vec![HandlerClause {
                    protocol: 0,
                    operation: 0,
                    resumption_type: Some(19),
                    callable_signature: Signature {
                        params: vec![I64, 19],
                        result: UNIT,
                        outward_protocols: vec![],
                    },
                }],
                partial: false,
            }],
            ..Artifact::default()
        }
    }

    #[test]
    fn generic_protocol_type_arguments_must_be_valid_runtime_types() {
        let mut artifact = instantiated_protocol_artifact();
        artifact.protocols[0].type_arguments[0] = u32::MAX;
        assert_eq!(
            verify(artifact).unwrap_err(),
            VerifyError::InvalidType(u32::MAX)
        );
    }

    #[test]
    fn protocol_identity_table_must_be_canonically_ordered() {
        let mut artifact = instantiated_protocol_artifact();
        artifact.protocols.swap(0, 1);
        assert_eq!(
            verify(artifact).unwrap_err(),
            VerifyError::InvalidType(u32::MAX)
        );
    }

    #[test]
    fn handler_clause_cannot_be_swapped_to_an_incompatible_sibling_instance() {
        let mut artifact = instantiated_protocol_artifact();
        assert!(verify(artifact.clone()).is_ok());
        artifact.handler_defs[0].clauses[0].protocol = 1;
        assert_eq!(
            verify(artifact).unwrap_err(),
            VerifyError::InvalidType(UNIT)
        );
    }

    #[test]
    fn perform_requires_the_exact_instantiated_protocol_in_its_outward_row() {
        let mut artifact = instantiated_protocol_artifact();
        artifact.handler_defs.clear();
        artifact.functions.push(Function {
            flags: 0,
            name: "wrong_instance".into(),
            params: vec![TEXT],
            return_type: UNIT,
            outward_protocols: vec![0],
            receiver_mode: None,
            register_types: vec![UNIT, TEXT, TEXT],
            code_start: 0,
            code_len: 3,
            label_slot_count: 0,
        });
        artifact.code = vec![
            Instruction::Perform {
                dst: Some(2),
                protocol: 1,
                operation: 0,
                payloads: vec![1],
            },
            Instruction::Drop { register: 2 },
            Instruction::Return { src: None },
        ];
        assert_eq!(
            verify(artifact).unwrap_err(),
            VerifyError::InvalidFunction(0)
        );
    }

    #[test]
    fn rejects_incomplete_nonpartial_handler_for_a_mentioned_protocol() {
        let artifact = Artifact {
            required_features: 1 | (1 << 3),
            protocols: vec![Protocol {
                display_name: "Effects".into(),
                type_arguments: vec![],
                operations: vec![
                    terminal_operation("first", vec![]),
                    terminal_operation("second", vec![]),
                ],
            }],
            handler_defs: vec![HandlerDef {
                result_type: UNIT,
                clauses: vec![HandlerClause {
                    protocol: 0,
                    operation: 0,
                    resumption_type: None,
                    callable_signature: Signature {
                        params: vec![],
                        result: UNIT,
                        outward_protocols: vec![],
                    },
                }],
                partial: false,
            }],
            ..Artifact::default()
        };
        assert_eq!(
            verify(artifact).unwrap_err(),
            VerifyError::InvalidType(UNIT)
        );
    }

    #[test]
    fn cancel_accepts_any_upper_bound_when_zero_uses_are_allowed() {
        let mut types = Type::predefined();
        types.push(Type::Resumption {
            identity_name: "NeverUsable".into(),
            input_type: UNIT,
            output_type: UNIT,
            effect_signature: Signature {
                params: vec![],
                result: UNIT,
                outward_protocols: vec![],
            },
            lower_uses: 0,
            upper_uses: Some(0),
            copy: false,
        });
        let artifact = Artifact {
            required_features: 1 | (1 << 3),
            types,
            constants: vec![],
            functions: vec![Function {
                flags: 0,
                name: "cancel".into(),
                params: vec![19],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 19, UNIT],
                code_start: 0,
                code_len: 2,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Cancel {
                    dst: 2,
                    resumption: 1,
                },
                Instruction::Return { src: Some(2) },
            ],
            ..Artifact::default()
        };
        assert!(verify(artifact).is_ok());
    }

    fn optional_protocol(_resumption_type: TypeId) -> Protocol {
        Protocol {
            display_name: "Optional".into(),
            type_arguments: vec![],
            operations: vec![Operation {
                name: "stop".into(),
                payload_signature: Signature {
                    params: vec![],
                    result: UNIT,
                    outward_protocols: vec![],
                },
                result_type: UNIT,
                resumption_lower: 0,
                resumption_upper: Some(1),
                terminal: false,
            }],
        }
    }

    fn optional_types() -> Vec<Type> {
        let mut types = Type::predefined();
        types[I64 as usize] = Type::I64.restricted(false, false);
        types.push(Type::Resumption {
            identity_name: "optional continuation".into(),
            input_type: UNIT,
            output_type: UNIT,
            effect_signature: Signature {
                params: vec![],
                result: UNIT,
                outward_protocols: vec![],
            },
            lower_uses: 0,
            upper_uses: Some(1),
            copy: false,
        });
        types
    }

    #[test]
    fn optional_perform_rejects_a_live_must_move_continuation_capture() {
        let artifact = Artifact {
            required_features: 1 | (1 << 3),
            types: optional_types(),
            protocols: vec![optional_protocol(19)],
            functions: vec![Function {
                flags: 0,
                name: "suspend".into(),
                params: vec![I64],
                return_type: I64,
                outward_protocols: vec![0],
                receiver_mode: None,
                register_types: vec![UNIT, I64, UNIT],
                code_start: 0,
                code_len: 3,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Perform {
                    dst: Some(2),
                    protocol: 0,
                    operation: 0,
                    payloads: vec![],
                },
                Instruction::Drop { register: 2 },
                Instruction::Return { src: Some(1) },
            ],
            ..Artifact::default()
        };
        assert_eq!(
            verify(artifact).unwrap_err(),
            VerifyError::LiveValueAtExit {
                function: 0,
                instruction: 0,
                register: 1,
            }
        );
    }

    #[test]
    fn optional_outward_direct_call_rejects_a_live_must_move_caller_capture() {
        let artifact = Artifact {
            required_features: 1 | (1 << 3),
            types: optional_types(),
            protocols: vec![optional_protocol(19)],
            functions: vec![
                Function {
                    flags: 0,
                    name: "caller".into(),
                    params: vec![I64],
                    return_type: I64,
                    outward_protocols: vec![0],
                    receiver_mode: None,
                    register_types: vec![UNIT, I64, UNIT],
                    code_start: 0,
                    code_len: 3,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "callee".into(),
                    params: vec![],
                    return_type: UNIT,
                    outward_protocols: vec![0],
                    receiver_mode: None,
                    register_types: vec![UNIT, UNIT],
                    code_start: 3,
                    code_len: 2,
                    label_slot_count: 0,
                },
            ],
            code: vec![
                Instruction::Call {
                    dst: Some(2),
                    function: 1,
                    args: vec![],
                },
                Instruction::Drop { register: 2 },
                Instruction::Return { src: Some(1) },
                Instruction::Perform {
                    dst: Some(1),
                    protocol: 0,
                    operation: 0,
                    payloads: vec![],
                },
                Instruction::Return { src: Some(1) },
            ],
            ..Artifact::default()
        };
        assert_eq!(
            verify(artifact).unwrap_err(),
            VerifyError::LiveValueAtExit {
                function: 0,
                instruction: 0,
                register: 1,
            }
        );
    }

    #[test]
    fn optional_outward_indirect_call_rejects_a_live_must_move_caller_capture() {
        let mut types = optional_types();
        types.push(Type::Callable {
            signature: Signature {
                params: vec![],
                result: UNIT,
                outward_protocols: vec![0],
            },
            capture_type: UNIT,
            receiver_mode: 2,
            identity_name: "optional callable".into(),
            copy: false,
            zero_use_allowed: true,
        });
        let artifact = Artifact {
            required_features: 1 | (1 << 3),
            types,
            protocols: vec![optional_protocol(19)],
            functions: vec![
                Function {
                    flags: 0,
                    name: "caller".into(),
                    params: vec![I64],
                    return_type: I64,
                    outward_protocols: vec![0],
                    receiver_mode: None,
                    register_types: vec![UNIT, I64, 20, UNIT],
                    code_start: 0,
                    code_len: 4,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "callee".into(),
                    params: vec![],
                    return_type: UNIT,
                    outward_protocols: vec![0],
                    receiver_mode: Some(2),
                    register_types: vec![UNIT, UNIT],
                    code_start: 4,
                    code_len: 2,
                    label_slot_count: 0,
                },
            ],
            code: vec![
                Instruction::MakeCallable {
                    dst: 2,
                    callable_type: 20,
                    function: 1,
                    captures: vec![],
                },
                Instruction::CallIndirect {
                    dst: Some(3),
                    callable: 2,
                    receiver_mode: 2,
                    args: vec![],
                },
                Instruction::Drop { register: 3 },
                Instruction::Return { src: Some(1) },
                Instruction::Perform {
                    dst: Some(1),
                    protocol: 0,
                    operation: 0,
                    payloads: vec![],
                },
                Instruction::Return { src: Some(1) },
            ],
            ..Artifact::default()
        };
        assert_eq!(
            verify(artifact).unwrap_err(),
            VerifyError::LiveValueAtExit {
                function: 0,
                instruction: 1,
                register: 1,
            }
        );
    }

    fn finite_dynamic_effect_artifact(
        multishot: bool,
        second_performs: bool,
        recursive_safe_cycle: bool,
    ) -> Artifact {
        let mut types = optional_types();
        types.push(Type::Callable {
            signature: Signature {
                params: vec![],
                result: UNIT,
                outward_protocols: vec![0],
            },
            capture_type: UNIT,
            receiver_mode: 2,
            identity_name: "finite dynamic effect callable".into(),
            copy: false,
            zero_use_allowed: true,
        });
        let protocol = if multishot {
            Protocol {
                display_name: "Multi".into(),
                type_arguments: vec![],
                operations: vec![Operation {
                    name: "fork".into(),
                    payload_signature: Signature {
                        params: vec![],
                        result: UNIT,
                        outward_protocols: vec![],
                    },
                    result_type: UNIT,
                    resumption_lower: 0,
                    resumption_upper: Some(2),
                    terminal: false,
                }],
            }
        } else {
            optional_protocol(19)
        };
        let mut code = vec![
            Instruction::Switch {
                discr: 2,
                cases: vec![(1, 1)],
                otherwise: 3,
            },
            Instruction::MakeCallable {
                dst: 3,
                callable_type: 20,
                function: 1,
                captures: vec![],
            },
            Instruction::Jump { target: 4 },
            Instruction::MakeCallable {
                dst: 3,
                callable_type: 20,
                function: 2,
                captures: vec![],
            },
            Instruction::CallIndirect {
                dst: Some(4),
                callable: 3,
                receiver_mode: 2,
                args: vec![],
            },
            Instruction::Drop { register: 4 },
            Instruction::Return { src: Some(1) },
        ];
        let caller_len = code.len() as u32;
        let append_safe = |code: &mut Vec<Instruction>, other: u32| {
            if recursive_safe_cycle {
                code.extend([
                    Instruction::MakeCallable {
                        dst: 1,
                        callable_type: 20,
                        function: other,
                        captures: vec![],
                    },
                    Instruction::CallIndirect {
                        dst: Some(2),
                        callable: 1,
                        receiver_mode: 2,
                        args: vec![],
                    },
                    Instruction::Return { src: Some(2) },
                ]);
            } else {
                code.extend([
                    Instruction::Const {
                        dst: 1,
                        constant: 0,
                    },
                    Instruction::Return { src: Some(1) },
                ]);
            }
        };
        append_safe(&mut code, 2);
        let second_start = code.len() as u32;
        if second_performs {
            code.extend([
                Instruction::Perform {
                    dst: Some(1),
                    protocol: 0,
                    operation: 0,
                    payloads: vec![],
                },
                Instruction::Return { src: Some(1) },
            ]);
        } else {
            append_safe(&mut code, 1);
        }
        let end = code.len() as u32;
        let mut artifact = Artifact {
            types,
            constants: vec![Constant::Unit, Constant::U32(0)],
            protocols: vec![protocol],
            functions: vec![
                Function {
                    flags: 0,
                    name: "finite_dynamic_effect_caller".into(),
                    params: vec![I64, U32],
                    return_type: I64,
                    outward_protocols: vec![0],
                    receiver_mode: None,
                    register_types: vec![UNIT, I64, U32, 20, UNIT],
                    code_start: 0,
                    code_len: caller_len,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "finite_dynamic_safe_a".into(),
                    params: vec![],
                    return_type: UNIT,
                    outward_protocols: vec![0],
                    receiver_mode: Some(2),
                    register_types: if recursive_safe_cycle {
                        vec![UNIT, 20, UNIT]
                    } else {
                        vec![UNIT, UNIT]
                    },
                    code_start: caller_len,
                    code_len: second_start - caller_len,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "finite_dynamic_b".into(),
                    params: vec![],
                    return_type: UNIT,
                    outward_protocols: vec![0],
                    receiver_mode: Some(2),
                    register_types: if recursive_safe_cycle {
                        vec![UNIT, 20, UNIT]
                    } else {
                        vec![UNIT, UNIT]
                    },
                    code_start: second_start,
                    code_len: end - second_start,
                    label_slot_count: 0,
                },
            ],
            code,
            ..Artifact::default()
        };
        artifact.required_features =
            crate::bytecode::used_features(&artifact.types, &artifact.code, true, false);
        artifact
    }

    #[test]
    fn finite_dynamic_targets_use_exact_cancellation_and_multishot_summaries() {
        verify(finite_dynamic_effect_artifact(false, false, false))
            .expect("two cancellation-free alternatives preserve the caller continuation");
        verify(finite_dynamic_effect_artifact(true, false, false))
            .expect("two one-shot alternatives need no multishot snapshot");

        assert!(matches!(
            verify(finite_dynamic_effect_artifact(false, true, false)),
            Err(VerifyError::LiveValueAtExit {
                function: 0,
                instruction: 4,
                register: 1,
            })
        ));
        assert!(verify(finite_dynamic_effect_artifact(true, true, false)).is_err());
    }

    #[test]
    fn finite_dynamic_effect_summaries_converge_across_recursive_alternatives() {
        verify(finite_dynamic_effect_artifact(false, false, true))
            .expect("a cancellation-free recursive SCC reaches the safe fixed point");
        verify(finite_dynamic_effect_artifact(true, false, true))
            .expect("a multishot-free recursive SCC reaches the safe fixed point");
    }

    #[test]
    fn opaque_dynamic_effect_producers_keep_the_conservative_declared_contract() {
        for multishot in [false, true] {
            let mut artifact = finite_dynamic_effect_artifact(multishot, false, false);
            artifact.code = vec![
                Instruction::CallIndirect {
                    dst: Some(3),
                    callable: 2,
                    receiver_mode: 2,
                    args: vec![],
                },
                Instruction::Drop { register: 3 },
                Instruction::Return { src: Some(1) },
            ];
            artifact.functions = vec![Function {
                flags: 0,
                name: "opaque_dynamic_effect_caller".into(),
                params: vec![I64, 20],
                return_type: I64,
                outward_protocols: vec![0],
                receiver_mode: None,
                register_types: vec![UNIT, I64, 20, UNIT],
                code_start: 0,
                code_len: 3,
                label_slot_count: 0,
            }];
            artifact.required_features =
                crate::bytecode::used_features(&artifact.types, &artifact.code, true, false);
            assert!(verify(artifact).is_err());
        }
    }

    #[test]
    fn optional_handler_rejects_a_must_move_hidden_clause_dependency() {
        let mut types = optional_types();
        types.extend([
            Type::Tuple {
                fields: vec![I64],
                copy: false,
            }
            .restricted(false, false),
            Type::RefShared { referent: 20 },
            Type::Callable {
                signature: Signature {
                    params: vec![19],
                    result: UNIT,
                    outward_protocols: vec![],
                },
                capture_type: 20,
                receiver_mode: 0,
                identity_name: "optional clause".into(),
                copy: false,
                zero_use_allowed: false,
            },
            Type::Tuple {
                fields: vec![22],
                copy: false,
            },
            Type::Handler {
                handler_def: 0,
                capture_type: 23,
                identity_name: "optional handler".into(),
            },
            Type::Callable {
                signature: Signature {
                    params: vec![],
                    result: UNIT,
                    outward_protocols: vec![0],
                },
                capture_type: UNIT,
                receiver_mode: 2,
                identity_name: "optional body".into(),
                copy: false,
                zero_use_allowed: true,
            },
        ]);
        let artifact = Artifact {
            required_features: 1 | (1 << 1) | (1 << 3),
            types,
            constants: vec![Constant::Unit],
            protocols: vec![optional_protocol(19)],
            handler_defs: vec![HandlerDef {
                result_type: UNIT,
                clauses: vec![HandlerClause {
                    protocol: 0,
                    operation: 0,
                    resumption_type: Some(19),
                    callable_signature: Signature {
                        params: vec![19],
                        result: UNIT,
                        outward_protocols: vec![],
                    },
                }],
                partial: false,
            }],
            functions: vec![
                Function {
                    flags: 0,
                    name: "run".into(),
                    params: vec![24],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, 24, 25, UNIT],
                    code_start: 0,
                    code_len: 3,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "clause".into(),
                    params: vec![19],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: Some(0),
                    register_types: vec![21, 19, UNIT, UNIT],
                    code_start: 3,
                    code_len: 3,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "body".into(),
                    params: vec![],
                    return_type: UNIT,
                    outward_protocols: vec![0],
                    receiver_mode: Some(2),
                    register_types: vec![UNIT, UNIT],
                    code_start: 6,
                    code_len: 2,
                    label_slot_count: 0,
                },
            ],
            code: vec![
                Instruction::MakeCallable {
                    dst: 2,
                    callable_type: 25,
                    function: 2,
                    captures: vec![],
                },
                Instruction::Handle {
                    dst: 3,
                    handler: 1,
                    body: 2,
                    args: vec![],
                },
                Instruction::Return { src: Some(3) },
                Instruction::Const {
                    dst: 3,
                    constant: 0,
                },
                Instruction::Resume {
                    dst: 2,
                    resumption: 1,
                    receiver_mode: 2,
                    value: 3,
                },
                Instruction::Return { src: Some(2) },
                Instruction::Perform {
                    dst: Some(1),
                    protocol: 0,
                    operation: 0,
                    payloads: vec![],
                },
                Instruction::Return { src: Some(1) },
            ],
            ..Artifact::default()
        };
        assert_eq!(
            verify(artifact).unwrap_err(),
            VerifyError::LiveValueAtExit {
                function: 0,
                instruction: 1,
                register: 1,
            }
        );
    }

    #[test]
    fn partial_handler_rejects_a_must_move_dependency_before_forwarding_terminal_effect() {
        let mut types = Type::predefined();
        types[I64 as usize] = Type::I64.restricted(false, false);
        types.extend([
            Type::Tuple {
                fields: vec![I64],
                copy: false,
            }
            .restricted(false, false),
            Type::Callable {
                signature: Signature {
                    params: vec![],
                    result: UNIT,
                    outward_protocols: vec![],
                },
                capture_type: 19,
                receiver_mode: 2,
                identity_name: "terminal clause".into(),
                copy: false,
                zero_use_allowed: false,
            },
            Type::Tuple {
                fields: vec![20],
                copy: false,
            },
            Type::Handler {
                handler_def: 0,
                capture_type: 21,
                identity_name: "partial terminal handler".into(),
            },
            Type::Callable {
                signature: Signature {
                    params: vec![],
                    result: UNIT,
                    outward_protocols: vec![0],
                },
                capture_type: UNIT,
                receiver_mode: 2,
                identity_name: "terminal body".into(),
                copy: false,
                zero_use_allowed: true,
            },
        ]);
        let artifact = Artifact {
            required_features: 1 | (1 << 3),
            types,
            protocols: vec![Protocol {
                display_name: "Terminal".into(),
                type_arguments: vec![],
                operations: vec![
                    terminal_operation("handled", vec![]),
                    terminal_operation("forwarded", vec![]),
                ],
            }],
            handler_defs: vec![HandlerDef {
                result_type: UNIT,
                clauses: vec![HandlerClause {
                    protocol: 0,
                    operation: 0,
                    resumption_type: None,
                    callable_signature: Signature {
                        params: vec![],
                        result: UNIT,
                        outward_protocols: vec![],
                    },
                }],
                partial: true,
            }],
            functions: vec![
                Function {
                    flags: 0,
                    name: "run".into(),
                    params: vec![22],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, 22, 23, UNIT],
                    code_start: 0,
                    code_len: 3,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "clause".into(),
                    params: vec![],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: Some(2),
                    register_types: vec![19],
                    code_start: 3,
                    code_len: 1,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "body".into(),
                    params: vec![],
                    return_type: UNIT,
                    outward_protocols: vec![0],
                    receiver_mode: Some(2),
                    register_types: vec![UNIT],
                    code_start: 4,
                    code_len: 1,
                    label_slot_count: 0,
                },
            ],
            code: vec![
                Instruction::MakeCallable {
                    dst: 2,
                    callable_type: 23,
                    function: 2,
                    captures: vec![],
                },
                Instruction::Handle {
                    dst: 3,
                    handler: 1,
                    body: 2,
                    args: vec![],
                },
                Instruction::Return { src: Some(3) },
                Instruction::Abort { message: None },
                Instruction::Perform {
                    dst: None,
                    protocol: 0,
                    operation: 1,
                    payloads: vec![],
                },
            ],
            ..Artifact::default()
        };
        assert_eq!(
            verify(artifact).unwrap_err(),
            VerifyError::LiveValueAtExit {
                function: 0,
                instruction: 1,
                register: 1,
            }
        );
    }

    #[test]
    fn rejects_an_ordinary_jump_that_bypasses_a_label_push() {
        let mut artifact = base(
            vec![
                Instruction::Jump { target: 2 },
                Instruction::LabelPush {
                    slot: 0,
                    result_register: 1,
                    target: 4,
                },
                Instruction::LabelPop { slot: 0 },
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::Return { src: Some(1) },
            ],
            vec![UNIT, I64],
        );
        artifact.functions[0].label_slot_count = 1;
        artifact.required_features |= 1 << 2;

        assert!(matches!(
            verify(artifact),
            Err(VerifyError::InvalidFunction(0))
        ));
    }

    #[test]
    fn rejects_leave_when_the_target_cleanup_is_not_a_source_suffix() {
        let mut artifact = base(
            vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::Const {
                    dst: 2,
                    constant: 0,
                },
                Instruction::LabelPush {
                    slot: 0,
                    result_register: 3,
                    target: 5,
                },
                Instruction::Leave { slot: 0, value: 1 },
                Instruction::LabelPop { slot: 0 },
                Instruction::Return { src: Some(3) },
            ],
            vec![UNIT, I64, I64, I64],
        );
        artifact.functions[0].label_slot_count = 1;
        artifact.required_features |= 1 << 2;
        artifact.cleanups = vec![
            CleanupPlan {
                function: 0,
                first_instruction: 0,
                end_instruction: 3,
                registers: vec![],
            },
            CleanupPlan {
                function: 0,
                first_instruction: 3,
                end_instruction: 4,
                registers: vec![1],
            },
            CleanupPlan {
                function: 0,
                first_instruction: 4,
                end_instruction: 5,
                registers: vec![],
            },
            CleanupPlan {
                function: 0,
                first_instruction: 5,
                end_instruction: 6,
                registers: vec![2],
            },
        ];

        assert!(matches!(
            verify(artifact),
            Err(VerifyError::StateMismatch {
                function: 0,
                instruction: 3,
            })
        ));
    }

    #[test]
    fn seeded_leave_preserves_the_empty_result_suffix_and_reference_origin() {
        let mut types = Type::predefined();
        types.push(Type::RefShared { referent: I64 });
        let artifact = Artifact {
            types,
            functions: vec![Function {
                flags: 0,
                name: "select".into(),
                params: vec![19],
                return_type: 19,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 19, 19],
                code_start: 0,
                code_len: 3,
                label_slot_count: 1,
            }],
            code: vec![
                Instruction::LabelPush {
                    slot: 0,
                    result_register: 2,
                    target: 2,
                },
                Instruction::Leave { slot: 0, value: 1 },
                Instruction::Return { src: Some(2) },
            ],
            cleanups: vec![
                CleanupPlan {
                    function: 0,
                    first_instruction: 1,
                    end_instruction: 2,
                    registers: vec![1, 2],
                },
                CleanupPlan {
                    function: 0,
                    first_instruction: 2,
                    end_instruction: 3,
                    registers: vec![2],
                },
            ],
            required_features: 1 | (1 << 1) | (1 << 2),
            ..Artifact::default()
        };

        let completed = with_compiler_seeded_cleanup_plans(artifact).unwrap();
        assert_eq!(cleanup_registers(&completed, 0, 1), &[1, 2]);
        assert!(super::verify(completed).is_ok());
    }

    #[test]
    fn verifies_drop_hook_metadata_and_rejects_bad_signature() {
        let mut artifact = Artifact::default();
        artifact.required_features |= 1 << 1;
        artifact.types.push(
            Type::Struct {
                name: "Resource".into(),
                fields: vec![],
                copy: false,
            }
            .restricted(false, true),
        );
        artifact.types.push(Type::RefUnique { referent: 19 });
        artifact.constants.push(Constant::Unit);
        artifact.functions.push(Function {
            flags: DROP_HOOK,
            name: "drop_resource".into(),
            params: vec![20],
            return_type: UNIT,
            outward_protocols: vec![],
            receiver_mode: None,
            register_types: vec![UNIT, 20, UNIT],
            code_start: 0,
            code_len: 3,
            label_slot_count: 0,
        });
        artifact.code = vec![
            Instruction::Drop { register: 1 },
            Instruction::Const {
                dst: 2,
                constant: 0,
            },
            Instruction::Return { src: Some(2) },
        ];
        artifact.drop_glue.push(DropGlue {
            ty: 19,
            function: 0,
        });
        assert!(verify(artifact.clone()).is_ok());

        let mut forged_call = artifact.clone();
        forged_call.functions.push(Function {
            flags: 0,
            name: "forged_caller".into(),
            params: vec![],
            return_type: UNIT,
            outward_protocols: vec![],
            receiver_mode: None,
            register_types: vec![UNIT, UNIT],
            code_start: 3,
            code_len: 2,
            label_slot_count: 0,
        });
        forged_call.code.extend([
            Instruction::Call {
                dst: Some(1),
                function: 0,
                args: vec![],
            },
            Instruction::Return { src: Some(1) },
        ]);
        assert!(matches!(
            verify(forged_call),
            Err(VerifyError::InvalidFunction(1))
        ));

        let mut wrong_referent = artifact.clone();
        wrong_referent.drop_glue[0].ty = I64;
        assert!(matches!(
            verify(wrong_referent),
            Err(VerifyError::InvalidType(I64))
        ));

        let mut moving_through_self = artifact.clone();
        moving_through_self.code[0] = Instruction::ProjectMove {
            dst: 2,
            src: 1,
            field: 0,
        };
        assert!(matches!(
            verify(moving_through_self),
            Err(VerifyError::InvalidFunction(0))
        ));

        let mut popping_through_self = artifact.clone();
        popping_through_self.code[0] = Instruction::Primitive {
            dst: 2,
            op: Primitive::ArrayPopMove,
            args: vec![1],
        };
        assert!(matches!(
            verify(popping_through_self),
            Err(VerifyError::InvalidFunction(0))
        ));

        let mut reachable_forbidden = artifact.clone();
        reachable_forbidden.required_features |= 1 << 2;
        reachable_forbidden.functions[0].code_len = 3;
        reachable_forbidden.functions.push(Function {
            flags: 0,
            name: "forbidden_helper".into(),
            params: vec![],
            return_type: UNIT,
            outward_protocols: vec![],
            receiver_mode: None,
            register_types: vec![UNIT, UNIT],
            code_start: 3,
            code_len: 3,
            label_slot_count: 1,
        });
        reachable_forbidden.code = vec![
            Instruction::Drop { register: 1 },
            Instruction::Call {
                dst: Some(2),
                function: 1,
                args: vec![],
            },
            Instruction::Return { src: Some(2) },
            Instruction::LabelPop { slot: 0 },
            Instruction::Const {
                dst: 1,
                constant: 0,
            },
            Instruction::Return { src: Some(1) },
        ];
        assert!(matches!(
            verify(reachable_forbidden),
            Err(VerifyError::InvalidFunction(1))
        ));

        artifact.functions[0].params[0] = U32;
        artifact.functions[0].register_types[1] = U32;
        assert!(matches!(
            verify(artifact),
            Err(VerifyError::InvalidFunction(0))
        ));
    }

    #[test]
    fn no_return_function_rejects_normal_return() {
        let mut artifact = base(
            vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::Return { src: Some(1) },
            ],
            vec![UNIT, I64],
        );
        artifact.functions[0].flags = NO_RETURN;
        assert!(matches!(
            verify(artifact),
            Err(VerifyError::InvalidFunction(0))
        ));
    }

    fn finite_multishot(resumes: usize, lower: u32, upper: u32, mode: u32) -> Artifact {
        let mut types = Type::predefined();
        types.push(Type::Resumption {
            input_type: I64,
            output_type: I64,
            effect_signature: Signature {
                params: vec![],
                result: UNIT,
                outward_protocols: vec![],
            },
            lower_uses: lower,
            upper_uses: Some(upper),
            identity_name: "finite multi".into(),
            copy: true,
        });
        let mut register_types = vec![UNIT, 19];
        register_types.extend(std::iter::repeat_n(I64, resumes));
        register_types.push(I64);
        register_types.push(UNIT);
        let result = (2 + resumes) as u32;
        let unit = result + 1;
        let mut code = Vec::new();
        let final_resume_consumes = resumes != 0 && resumes == upper as usize;
        for index in 0..resumes {
            code.push(Instruction::Resume {
                dst: result,
                resumption: 1,
                receiver_mode: if final_resume_consumes && index + 1 == resumes {
                    2
                } else {
                    mode
                },
                value: (2 + index) as u32,
            });
            code.push(Instruction::Drop { register: result });
        }
        if !final_resume_consumes {
            code.push(Instruction::Drop { register: 1 });
        }
        code.push(Instruction::Const {
            dst: unit,
            constant: 0,
        });
        code.push(Instruction::Return { src: Some(unit) });
        Artifact {
            types,
            constants: vec![Constant::Unit],
            functions: vec![Function {
                flags: 0,
                name: "finite_multishot".into(),
                params: std::iter::once(19)
                    .chain(std::iter::repeat_n(I64, resumes))
                    .collect(),
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types,
                code_start: 0,
                code_len: code.len() as u32,
                label_slot_count: 0,
            }],
            code,
            required_features: 1 | (1 << 3) | (1 << 4),
            ..Artifact::default()
        }
    }

    #[test]
    fn finite_multishot_quantity_is_proved_exactly_for_the_accepted_register_shape() {
        assert!(verify(finite_multishot(2, 2, 2, 0)).is_ok());
        assert!(verify(finite_multishot(2, 2, 2, 1)).is_ok());
        assert!(matches!(
            verify(finite_multishot(3, 0, 2, 0)),
            Err(VerifyError::InvalidFunction(0))
        ));
        assert!(matches!(
            verify(finite_multishot(1, 2, 2, 2)),
            Err(VerifyError::InvalidFunction(0))
        ));
    }

    #[test]
    fn copied_resumption_alias_drop_defers_to_shared_quantity_proof() {
        let mut valid = finite_multishot(1, 1, 2, 0);
        valid.functions[0].register_types.push(19);
        let alias = valid.functions[0].register_types.len() as u32 - 1;
        valid
            .code
            .insert(0, Instruction::Copy { dst: alias, src: 1 });
        let Instruction::Resume { resumption, .. } = &mut valid.code[1] else {
            unreachable!()
        };
        *resumption = alias;
        valid.code.insert(3, Instruction::Drop { register: alias });
        valid.functions[0].code_len = valid.code.len() as u32;
        assert!(verify(valid.clone()).is_ok());

        // Both aliases are explicitly retired, but no view discharges the
        // positive lower bound. The dedicated quantity proof must still make
        // the malformed artifact fail.
        valid.code.drain(1..3);
        valid.functions[0].code_len = valid.code.len() as u32;
        let malformed = verify(valid);
        assert!(malformed.is_err(), "{malformed:?}");
    }

    fn moved_resumption(lower: u32, upper: u32, uses_before_move: usize) -> Artifact {
        let mut artifact = finite_multishot(uses_before_move, lower, upper, 0);
        let old_result = (2 + uses_before_move) as u32;
        let old_unit = old_result + 1;
        let moved = old_unit + 1;
        artifact.functions[0].register_types.push(19);
        let tail = artifact.code.split_off(uses_before_move * 2);
        artifact.code.push(Instruction::Move { dst: moved, src: 1 });
        artifact
            .code
            .extend(tail.into_iter().map(|instruction| match instruction {
                Instruction::Drop { register: 1 } => Instruction::Drop { register: moved },
                other => other,
            }));
        artifact.functions[0].code_len = artifact.code.len() as u32;
        artifact.required_features =
            crate::bytecode::used_features(&artifact.types, &artifact.code, false, false);
        artifact
    }

    #[test]
    fn move_transfers_a_resumption_quantity_obligation() {
        let quantity_verify = |artifact: &Artifact| {
            let labels = verify_labels(artifact, 0, &artifact.functions[0]).unwrap();
            verify_resumption_quantities(artifact, 0, &artifact.functions[0], &labels)
        };
        let zero_lower = moved_resumption(0, 1, 0);
        let zero_lower = quantity_verify(&zero_lower);
        assert!(zero_lower.is_ok(), "{zero_lower:?}");
        assert!(matches!(
            quantity_verify(&moved_resumption(1, 1, 0)),
            Err(VerifyError::InvalidFunction(0))
        ));
        assert!(matches!(
            quantity_verify(&moved_resumption(2, 2, 1)),
            Err(VerifyError::InvalidFunction(0))
        ));

        let mut completed = moved_resumption(2, 2, 1);
        let moved = completed.functions[0].register_types.len() as u32 - 1;
        let result = 3;
        let value = 2;
        let insertion = completed.code.len() - 3;
        completed.code.insert(
            insertion,
            Instruction::Resume {
                dst: result,
                resumption: moved,
                receiver_mode: 2,
                value,
            },
        );
        completed
            .code
            .insert(insertion + 1, Instruction::Drop { register: result });
        completed.code.remove(insertion + 2);
        completed.functions[0].code_len = completed.code.len() as u32;
        assert!(quantity_verify(&completed).is_ok());
    }

    #[test]
    fn restricted_resumption_move_is_still_quantity_checked() {
        let mut artifact = moved_resumption(1, 1, 0);
        artifact.types[19] = artifact.types[19].clone().restricted(false, false);
        let labels = verify_labels(&artifact, 0, &artifact.functions[0]).unwrap();
        let error = verify_resumption_quantities(&artifact, 0, &artifact.functions[0], &labels)
            .unwrap_err();
        assert!(
            matches!(error, VerifyError::InvalidFunction(0)),
            "{error:?}"
        );
    }

    fn aggregate_resumptions(resume_fields: usize) -> Artifact {
        let mut types = Type::predefined();
        types.push(Type::Resumption {
            input_type: I64,
            output_type: I64,
            effect_signature: Signature {
                params: vec![],
                result: UNIT,
                outward_protocols: vec![],
            },
            lower_uses: 1,
            upper_uses: Some(1),
            identity_name: "aggregate leaf".into(),
            copy: false,
        });
        types.push(Type::Tuple {
            fields: vec![19, 19, I64],
            copy: false,
        });
        let mut code = vec![Instruction::Construct {
            dst: 4,
            ty: 20,
            variant: None,
            fields: vec![1, 2, 3],
        }];
        for field in 0..resume_fields {
            let projected = 5 + field as u32;
            code.push(Instruction::ProjectMove {
                dst: projected,
                src: 4,
                field: field as u32,
            });
            code.push(Instruction::Resume {
                dst: 7,
                resumption: projected,
                receiver_mode: 2,
                value: 3,
            });
            code.push(Instruction::Drop { register: 7 });
        }
        code.push(Instruction::Drop { register: 4 });
        code.push(Instruction::Const {
            dst: 8,
            constant: 0,
        });
        code.push(Instruction::Return { src: Some(8) });
        Artifact {
            types,
            constants: vec![Constant::Unit],
            functions: vec![Function {
                flags: 0,
                name: "aggregate_resumptions".into(),
                params: vec![19, 19, I64],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 19, 19, I64, 20, 19, 19, I64, UNIT],
                code_start: 0,
                code_len: code.len() as u32,
                label_slot_count: 0,
            }],
            code,
            required_features: 1 | (1 << 3) | (1 << 4),
            ..Artifact::default()
        }
    }

    #[test]
    fn aggregate_leaf_origins_remain_distinct_through_construct_and_projection() {
        let quantity_verify = |artifact: &Artifact| {
            let labels = verify_labels(artifact, 0, &artifact.functions[0]).unwrap();
            verify_resumption_quantities(artifact, 0, &artifact.functions[0], &labels)
        };
        assert!(quantity_verify(&aggregate_resumptions(2)).is_ok());
        assert!(matches!(
            quantity_verify(&aggregate_resumptions(1)),
            Err(VerifyError::InvalidFunction(0))
        ));
    }

    #[test]
    fn whole_aggregate_move_preserves_each_leaf_obligation() {
        let mut artifact = aggregate_resumptions(2);
        artifact.functions[0].register_types.push(20);
        artifact
            .code
            .insert(1, Instruction::Move { dst: 9, src: 4 });
        for instruction in &mut artifact.code[2..] {
            if let Instruction::ProjectMove { src, .. } = instruction {
                *src = 9;
            }
        }
        artifact.functions[0].code_len = artifact.code.len() as u32;
        let labels = verify_labels(&artifact, 0, &artifact.functions[0]).unwrap();
        assert!(
            verify_resumption_quantities(&artifact, 0, &artifact.functions[0], &labels).is_ok()
        );
    }

    fn aggregate_transport_call(launder: bool) -> Artifact {
        let mut artifact = aggregate_resumptions(0);
        let Type::Resumption { lower_uses, .. } = &mut artifact.types[19] else {
            unreachable!()
        };
        *lower_uses = 0;
        artifact.functions.clear();
        artifact.code.clear();
        // Caller forwards one aggregate and receives the same leaf origin.
        artifact.code.extend([
            Instruction::Call {
                dst: Some(if launder { 3 } else { 2 }),
                function: 1,
                args: if launder { vec![1, 3] } else { vec![1] },
            },
            Instruction::Drop {
                register: if launder { 3 } else { 2 },
            },
            Instruction::Const {
                dst: 4,
                constant: 0,
            },
            Instruction::Return { src: Some(4) },
        ]);
        let callee_start = artifact.code.len() as u32;
        if launder {
            // Returning only the second of two same-typed parameters must not
            // be mistaken for identity transport of the first obligation.
            artifact.code.push(Instruction::Return { src: Some(2) });
        } else {
            artifact.code.extend([
                Instruction::Move { dst: 2, src: 1 },
                Instruction::Return { src: Some(2) },
            ]);
        }
        artifact.functions = vec![
            Function {
                flags: 0,
                name: "transport_caller".into(),
                params: if launder { vec![20, 20] } else { vec![20] },
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 20, 20, 20, UNIT],
                code_start: 0,
                code_len: callee_start,
                label_slot_count: 0,
            },
            Function {
                flags: 0,
                name: "transport_helper".into(),
                params: if launder { vec![20, 20] } else { vec![20] },
                return_type: 20,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 20, 20],
                code_start: callee_start,
                code_len: artifact.code.len() as u32 - callee_start,
                label_slot_count: 0,
            },
        ];
        artifact
    }

    #[test]
    fn verified_direct_call_summary_preserves_an_aggregate_leaf_origin() {
        let artifact = aggregate_transport_call(false);
        for (fid, function) in artifact.functions.iter().enumerate() {
            let labels = verify_labels(&artifact, fid as u32, function).unwrap();
            let result = verify_resumption_quantities(&artifact, fid as u32, function, &labels);
            assert!(result.is_ok(), "fid {fid}: {result:?}");
        }
    }

    #[test]
    fn direct_call_summary_rejects_same_typed_origin_laundering() {
        let artifact = aggregate_transport_call(true);
        let labels = verify_labels(&artifact, 0, &artifact.functions[0]).unwrap();
        assert!(matches!(
            verify_resumption_quantities(&artifact, 0, &artifact.functions[0], &labels),
            Err(VerifyError::InvalidFunction(0))
        ));
    }

    fn callable_transport(target_is_identity: bool) -> Artifact {
        let mut types = Type::predefined();
        types.push(Type::Resumption {
            input_type: I64,
            output_type: I64,
            effect_signature: Signature {
                params: vec![],
                result: UNIT,
                outward_protocols: vec![],
            },
            lower_uses: 0,
            upper_uses: Some(1),
            identity_name: "callable leaf".into(),
            copy: false,
        });
        types.push(Type::Tuple {
            fields: vec![19],
            copy: false,
        });
        types.push(Type::Callable {
            signature: Signature {
                params: vec![],
                result: 20,
                outward_protocols: vec![],
            },
            capture_type: 20,
            receiver_mode: 2,
            identity_name: "transport closure".into(),
            copy: false,
            zero_use_allowed: true,
        });
        let mut code = vec![
            Instruction::MakeCallable {
                dst: 2,
                callable_type: 21,
                function: 1,
                captures: vec![1],
            },
            Instruction::CallIndirect {
                dst: Some(3),
                callable: 2,
                receiver_mode: 2,
                args: vec![],
            },
            Instruction::Drop { register: 3 },
            Instruction::Const {
                dst: 4,
                constant: 0,
            },
            Instruction::Return { src: Some(4) },
        ];
        let callee_start = code.len() as u32;
        if target_is_identity {
            code.extend([
                Instruction::Move { dst: 1, src: 0 },
                Instruction::Return { src: Some(1) },
            ]);
        } else {
            code.extend([
                Instruction::ProjectCopy {
                    dst: 1,
                    src: 0,
                    field: 0,
                },
                Instruction::Construct {
                    dst: 2,
                    ty: 20,
                    variant: None,
                    fields: vec![1],
                },
                Instruction::Return { src: Some(2) },
            ]);
        }
        Artifact {
            types,
            constants: vec![Constant::Unit],
            functions: vec![
                Function {
                    flags: 0,
                    name: "callable_caller".into(),
                    params: vec![19],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, 19, 21, 20, UNIT],
                    code_start: 0,
                    code_len: callee_start,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "callable_target".into(),
                    params: vec![],
                    return_type: 20,
                    outward_protocols: vec![],
                    receiver_mode: Some(2),
                    register_types: if target_is_identity {
                        vec![20, 20]
                    } else {
                        vec![20, 19, 20]
                    },
                    code_start: callee_start,
                    code_len: code.len() as u32 - callee_start,
                    label_slot_count: 0,
                },
            ],
            code,
            required_features: 1 | (1 << 3) | (1 << 4),
            ..Artifact::default()
        }
    }

    fn externally_supplied_callable_artifact() -> Artifact {
        let mut artifact = callable_transport(true);
        artifact.types[20] = Type::Tuple {
            fields: vec![19],
            copy: false,
        }
        .restricted(false, true);
        artifact.code = vec![
            Instruction::CallIndirect {
                dst: Some(2),
                callable: 1,
                receiver_mode: 2,
                args: vec![],
            },
            Instruction::Drop { register: 2 },
            Instruction::Return { src: None },
            Instruction::Move { dst: 1, src: 0 },
            Instruction::Return { src: Some(1) },
            Instruction::MakeCallable {
                dst: 2,
                callable_type: 21,
                function: 1,
                captures: vec![1],
            },
            Instruction::Return { src: Some(2) },
        ];
        artifact.functions = vec![
            Function {
                flags: 0,
                name: "externally_supplied_callable_consumer".into(),
                params: vec![21],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 21, 20],
                code_start: 0,
                code_len: 3,
                label_slot_count: 0,
            },
            Function {
                flags: 0,
                name: "externally_supplied_callable_target".into(),
                params: vec![],
                return_type: 20,
                outward_protocols: vec![],
                receiver_mode: Some(2),
                register_types: vec![20, 20],
                code_start: 3,
                code_len: 2,
                label_slot_count: 0,
            },
            Function {
                flags: 0,
                name: "externally_supplied_callable_factory".into(),
                params: vec![19],
                return_type: 21,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 19, 21],
                code_start: 5,
                code_len: 2,
                label_slot_count: 0,
            },
        ];
        artifact.required_features =
            crate::bytecode::used_features(&artifact.types, &artifact.code, false, false);
        artifact
    }

    #[test]
    fn external_callable_parameters_use_closed_world_canonical_producer_summaries() {
        let artifact = externally_supplied_callable_artifact();
        let labels = verify_labels(&artifact, 0, &artifact.functions[0]).unwrap();
        let targets = callable_targets_at_pcs(&artifact, 0, &artifact.functions[0], &labels)
            .expect("closed-world callable target facts");
        assert_eq!(targets[0][1], CallableTargets::from([1]));
        assert_eq!(
            owned_receiver_quantity_summaries(&artifact)[0],
            Some(OwnedReceiverQuantitySummary {
                outputs: vec![],
                resumes: vec![0],
                dispositions: vec![QuantityTerminalDisposition::Dropped],
            })
        );
        verify(artifact).expect("the authenticated finite producer set is exact");
    }

    #[test]
    fn external_callable_parameters_without_a_valid_producer_fail_closed() {
        let mut absent = externally_supplied_callable_artifact();
        absent.code[5] = Instruction::Drop { register: 1 };
        absent.code[6] = Instruction::Return { src: None };
        absent.functions[2].return_type = UNIT;
        absent.functions[2].register_types = vec![UNIT, 19, UNIT];
        assert!(callable_type_producers(&absent, 21).is_empty());
        assert_eq!(owned_receiver_quantity_summaries(&absent)[0], None);
        assert!(matches!(
            verify(absent),
            Err(VerifyError::InvalidFunction(0))
        ));

        let mut forged = externally_supplied_callable_artifact();
        let Instruction::MakeCallable { function, .. } = &mut forged.code[5] else {
            unreachable!()
        };
        *function = 0;
        assert!(matches!(
            verify(forged),
            Err(VerifyError::InvalidFunction(0))
        ));
    }

    #[test]
    fn exact_callable_target_transports_captured_resumption_origin() {
        let artifact = callable_transport(true);
        for (fid, function) in artifact.functions.iter().enumerate() {
            let labels = verify_labels(&artifact, fid as u32, function).unwrap();
            assert!(verify_resumption_quantities(&artifact, fid as u32, function, &labels).is_ok());
        }
    }

    #[test]
    fn indirect_call_rejects_signature_compatible_uncertified_target() {
        let artifact = callable_transport(false);
        let labels = verify_labels(&artifact, 0, &artifact.functions[0]).unwrap();
        assert!(matches!(
            verify_resumption_quantities(&artifact, 0, &artifact.functions[0], &labels),
            Err(VerifyError::InvalidFunction(0))
        ));
    }

    fn stored_callable_transport() -> Artifact {
        let mut artifact = callable_transport(true);
        artifact.types.push(Type::Tuple {
            fields: vec![21],
            copy: false,
        });
        artifact.functions[0].register_types.extend([22, 21]);
        artifact.code.insert(
            1,
            Instruction::Construct {
                dst: 5,
                ty: 22,
                variant: None,
                fields: vec![2],
            },
        );
        artifact.code.insert(
            2,
            Instruction::ProjectMove {
                dst: 6,
                src: 5,
                field: 0,
            },
        );
        artifact.code.insert(3, Instruction::Drop { register: 5 });
        let Instruction::CallIndirect { callable, .. } = &mut artifact.code[4] else {
            unreachable!()
        };
        *callable = 6;
        artifact.functions[0].code_len += 3;
        artifact.functions[1].code_start += 3;
        artifact
    }

    #[test]
    fn one_shot_callable_survives_aggregate_storage_and_single_invocation() {
        let artifact = stored_callable_transport();
        for (fid, function) in artifact.functions.iter().enumerate() {
            let labels = verify_labels(&artifact, fid as u32, function).unwrap();
            assert!(verify_resumption_quantities(&artifact, fid as u32, function, &labels).is_ok());
        }
    }

    #[test]
    fn optional_callable_capture_may_be_abandoned_without_invocation() {
        let mut artifact = callable_transport(true);
        artifact.code.splice(
            1..5,
            [
                Instruction::Drop { register: 2 },
                Instruction::Const {
                    dst: 4,
                    constant: 0,
                },
                Instruction::Return { src: Some(4) },
            ],
        );
        artifact.functions[0].code_len = 4;
        artifact.functions[1].code_start = 4;
        let labels = verify_labels(&artifact, 0, &artifact.functions[0]).unwrap();
        assert!(
            verify_resumption_quantities(&artifact, 0, &artifact.functions[0], &labels).is_ok()
        );
    }

    #[test]
    fn callable_target_survives_retain_summary_and_aggregate_roundtrip() {
        let mut artifact = stored_callable_transport();
        artifact.functions[0].register_types.push(21);
        artifact.code.insert(
            4,
            Instruction::Call {
                dst: Some(7),
                function: 2,
                args: vec![6],
            },
        );
        let Instruction::CallIndirect { callable, .. } = &mut artifact.code[5] else {
            unreachable!()
        };
        *callable = 7;
        artifact.functions[0].code_len += 1;
        artifact.functions[1].code_start += 1;
        let retain_start = artifact.code.len() as u32;
        artifact.code.extend([
            Instruction::Move { dst: 2, src: 1 },
            Instruction::Return { src: Some(2) },
        ]);
        artifact.functions.push(Function {
            flags: 0,
            name: "retain_stored_callable".into(),
            params: vec![21],
            return_type: 21,
            outward_protocols: vec![],
            receiver_mode: None,
            register_types: vec![UNIT, 21, 21],
            code_start: retain_start,
            code_len: 2,
            label_slot_count: 0,
        });
        let labels = verify_labels(&artifact, 0, &artifact.functions[0]).unwrap();
        assert!(
            verify_resumption_quantities(&artifact, 0, &artifact.functions[0], &labels).is_ok()
        );
    }

    fn handler_capture(forged_clause: bool) -> Artifact {
        let mut artifact = callable_transport(true);
        artifact.types.push(Type::Tuple {
            fields: vec![21],
            copy: false,
        });
        artifact.types.push(Type::Handler {
            handler_def: 0,
            capture_type: 22,
            identity_name: "quantity handler".into(),
        });
        artifact.functions.truncate(1);
        artifact.code = if forged_clause {
            vec![
                Instruction::MakeHandler {
                    dst: 2,
                    handler_def: 0,
                    clauses: vec![1],
                },
                Instruction::Drop { register: 2 },
                Instruction::Const {
                    dst: 3,
                    constant: 0,
                },
                Instruction::Return { src: Some(3) },
            ]
        } else {
            vec![
                Instruction::MakeCallable {
                    dst: 2,
                    callable_type: 21,
                    function: 0,
                    captures: vec![1],
                },
                Instruction::MakeHandler {
                    dst: 3,
                    handler_def: 0,
                    clauses: vec![2],
                },
                Instruction::Drop { register: 3 },
                Instruction::Const {
                    dst: 4,
                    constant: 0,
                },
                Instruction::Return { src: Some(4) },
            ]
        };
        artifact.functions[0] = Function {
            flags: 0,
            name: "handler_capture".into(),
            params: if forged_clause { vec![21] } else { vec![19] },
            return_type: UNIT,
            outward_protocols: vec![],
            receiver_mode: None,
            register_types: if forged_clause {
                vec![UNIT, 21, 23, UNIT]
            } else {
                vec![UNIT, 19, 21, 23, UNIT]
            },
            code_start: 0,
            code_len: artifact.code.len() as u32,
            label_slot_count: 0,
        };
        artifact
    }

    #[test]
    fn handler_pack_preserves_hidden_clause_capture_origins() {
        let artifact = handler_capture(false);
        let labels = verify_labels(&artifact, 0, &artifact.functions[0]).unwrap();
        assert!(
            verify_resumption_quantities(&artifact, 0, &artifact.functions[0], &labels).is_ok()
        );
    }

    #[test]
    fn handler_pack_rejects_a_clause_without_exact_producer_identity() {
        let artifact = handler_capture(true);
        let labels = verify_labels(&artifact, 0, &artifact.functions[0]).unwrap();
        assert!(matches!(
            verify_resumption_quantities(&artifact, 0, &artifact.functions[0], &labels),
            Err(VerifyError::InvalidFunction(0))
        ));
    }

    fn variant_quantity_flow(active_variant: u32) -> Artifact {
        let mut artifact = callable_transport(true);
        artifact.types.truncate(20);
        artifact.types.push(Type::Enum {
            name: "QuantityChoice".into(),
            variants: vec![
                EnumVariant {
                    name: "Empty".into(),
                    fields: vec![],
                },
                EnumVariant {
                    name: "Present".into(),
                    fields: vec![Field {
                        name: "value".into(),
                        ty: 19,
                    }],
                },
            ],
            copy: false,
        });
        artifact.code = vec![
            Instruction::Construct {
                dst: 2,
                ty: 20,
                variant: Some(active_variant),
                fields: vec![1],
            },
            Instruction::ProjectMove {
                dst: 3,
                src: 2,
                field: 0,
            },
            Instruction::Drop { register: 3 },
            Instruction::Drop { register: 2 },
            Instruction::Const {
                dst: 4,
                constant: 0,
            },
            Instruction::Return { src: Some(4) },
        ];
        artifact.functions = vec![Function {
            flags: 0,
            name: "variant_quantity".into(),
            params: vec![19],
            return_type: UNIT,
            outward_protocols: vec![],
            receiver_mode: None,
            register_types: vec![UNIT, 19, 20, 19, UNIT],
            code_start: 0,
            code_len: artifact.code.len() as u32,
            label_slot_count: 0,
        }];
        artifact
    }

    #[test]
    fn known_enum_variant_tracks_only_its_initialized_quantity_leaves() {
        let artifact = variant_quantity_flow(1);
        let labels = verify_labels(&artifact, 0, &artifact.functions[0]).unwrap();
        assert!(
            verify_resumption_quantities(&artifact, 0, &artifact.functions[0], &labels).is_ok()
        );
    }

    #[test]
    fn enum_variant_cannot_launder_a_leaf_through_an_empty_alternative() {
        let artifact = variant_quantity_flow(0);
        let labels = verify_labels(&artifact, 0, &artifact.functions[0]).unwrap();
        assert!(matches!(
            verify_resumption_quantities(&artifact, 0, &artifact.functions[0], &labels),
            Err(VerifyError::InvalidFunction(0))
        ));
    }

    fn enum_parameter_drop(lower: u32) -> Artifact {
        let mut artifact = variant_quantity_flow(1);
        let Type::Resumption { lower_uses, .. } = &mut artifact.types[19] else {
            unreachable!()
        };
        *lower_uses = lower;
        artifact.functions[0].params = vec![20];
        artifact.functions[0].register_types = vec![UNIT, 20, UNIT];
        artifact.code = vec![
            Instruction::Drop { register: 1 },
            Instruction::Const {
                dst: 2,
                constant: 0,
            },
            Instruction::Return { src: Some(2) },
        ];
        artifact.functions[0].code_len = artifact.code.len() as u32;
        artifact
    }

    #[test]
    fn enum_parameter_is_verified_for_each_discriminant_alternative() {
        let artifact = enum_parameter_drop(0);
        let labels = verify_labels(&artifact, 0, &artifact.functions[0]).unwrap();
        assert!(
            verify_resumption_quantities(&artifact, 0, &artifact.functions[0], &labels).is_ok()
        );
    }

    #[test]
    fn enum_parameter_cannot_hide_required_use_in_one_alternative() {
        let artifact = enum_parameter_drop(1);
        let labels = verify_labels(&artifact, 0, &artifact.functions[0]).unwrap();
        assert!(matches!(
            verify_resumption_quantities(&artifact, 0, &artifact.functions[0], &labels),
            Err(VerifyError::InvalidFunction(0))
        ));
    }

    #[test]
    fn enum_parameter_roundtrips_through_certified_direct_summary() {
        let mut artifact = enum_parameter_drop(0);
        artifact.code = vec![
            Instruction::Call {
                dst: Some(2),
                function: 1,
                args: vec![1],
            },
            Instruction::Drop { register: 2 },
            Instruction::Const {
                dst: 3,
                constant: 0,
            },
            Instruction::Return { src: Some(3) },
            Instruction::Move { dst: 2, src: 1 },
            Instruction::Return { src: Some(2) },
        ];
        artifact.functions = vec![
            Function {
                flags: 0,
                name: "enum_retain_caller".into(),
                params: vec![20],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 20, 20, UNIT],
                code_start: 0,
                code_len: 4,
                label_slot_count: 0,
            },
            Function {
                flags: 0,
                name: "enum_retain".into(),
                params: vec![20],
                return_type: 20,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 20, 20],
                code_start: 4,
                code_len: 2,
                label_slot_count: 0,
            },
        ];
        for (fid, function) in artifact.functions.iter().enumerate() {
            let labels = verify_labels(&artifact, fid as u32, function).unwrap();
            let result = verify_resumption_quantities(&artifact, fid as u32, function, &labels);
            assert!(result.is_ok(), "fid {fid}: {result:?}");
        }
    }

    fn branch_transport(swap: bool, loop_back: bool) -> Artifact {
        let mut types = Type::predefined();
        types.push(Type::Resumption {
            input_type: I64,
            output_type: I64,
            effect_signature: Signature {
                params: vec![],
                result: UNIT,
                outward_protocols: vec![],
            },
            lower_uses: 0,
            upper_uses: Some(1),
            identity_name: "branch leaf".into(),
            copy: false,
        });
        types.push(Type::Tuple {
            fields: vec![19, 19],
            copy: false,
        });
        let (params, registers, return_type, code) = if swap {
            (
                vec![19, 19, U32],
                vec![UNIT, 19, 19, U32, 20],
                20,
                vec![
                    Instruction::Switch {
                        discr: 3,
                        cases: vec![(1, 1)],
                        otherwise: 3,
                    },
                    Instruction::Construct {
                        dst: 4,
                        ty: 20,
                        variant: None,
                        fields: vec![1, 2],
                    },
                    Instruction::Jump { target: 4 },
                    Instruction::Construct {
                        dst: 4,
                        ty: 20,
                        variant: None,
                        fields: vec![2, 1],
                    },
                    Instruction::Return { src: Some(4) },
                ],
            )
        } else {
            let branch_target = if loop_back { 0 } else { 3 };
            (
                vec![19, U32],
                vec![UNIT, 19, U32, 19],
                19,
                vec![
                    Instruction::Switch {
                        discr: 2,
                        cases: vec![(1, 1)],
                        otherwise: 3,
                    },
                    Instruction::Jump {
                        target: branch_target,
                    },
                    Instruction::Jump { target: 3 },
                    Instruction::Move { dst: 3, src: 1 },
                    Instruction::Return { src: Some(3) },
                ],
            )
        };
        Artifact {
            types,
            functions: vec![Function {
                flags: 0,
                name: "branch_transport".into(),
                params,
                return_type,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: registers,
                code_start: 0,
                code_len: code.len() as u32,
                label_slot_count: 0,
            }],
            code,
            required_features: 1 | (1 << 3) | (1 << 4),
            ..Artifact::default()
        }
    }

    #[test]
    fn cfg_summary_accepts_equal_branch_and_stable_loop_provenance() {
        assert_eq!(
            quantity_transport_summaries(&branch_transport(false, false))[0],
            Some(vec![0])
        );
        assert_eq!(
            quantity_transport_summaries(&branch_transport(false, true))[0],
            Some(vec![0])
        );
    }

    #[test]
    fn cfg_summary_rejects_branch_origin_laundering() {
        assert_eq!(
            quantity_transport_summaries(&branch_transport(true, false))[0],
            None
        );
    }

    #[test]
    fn cfg_summary_rejects_loop_backedge_origin_laundering() {
        let mut artifact = branch_transport(true, false);
        artifact.code = vec![
            Instruction::Switch {
                discr: 3,
                cases: vec![(1, 1)],
                otherwise: 7,
            },
            Instruction::Construct {
                dst: 4,
                ty: 20,
                variant: None,
                fields: vec![1, 2],
            },
            Instruction::ProjectMove {
                dst: 1,
                src: 4,
                field: 1,
            },
            Instruction::ProjectMove {
                dst: 2,
                src: 4,
                field: 0,
            },
            Instruction::Deconstruct { src: 4 },
            Instruction::Jump { target: 0 },
            Instruction::Jump { target: 7 },
            Instruction::Construct {
                dst: 4,
                ty: 20,
                variant: None,
                fields: vec![1, 2],
            },
            Instruction::Return { src: Some(4) },
        ];
        artifact.functions[0].code_len = artifact.code.len() as u32;
        assert_eq!(quantity_transport_summaries(&artifact)[0], None);
    }

    #[test]
    fn oscillating_recursive_component_does_not_erase_independent_summary() {
        let mut artifact = branch_transport(true, false);
        artifact.code = vec![
            Instruction::Call {
                dst: Some(3),
                function: 0,
                args: vec![2, 1],
            },
            Instruction::Return { src: Some(3) },
            Instruction::Move { dst: 2, src: 1 },
            Instruction::Return { src: Some(2) },
        ];
        artifact.functions = vec![
            Function {
                flags: 0,
                name: "oscillating_swap".into(),
                params: vec![19, 19],
                return_type: 20,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 19, 19, 20],
                code_start: 0,
                code_len: 2,
                label_slot_count: 0,
            },
            Function {
                flags: 0,
                name: "independent_identity".into(),
                params: vec![19],
                return_type: 19,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 19, 19],
                code_start: 2,
                code_len: 2,
                label_slot_count: 0,
            },
        ];
        let summaries = quantity_transport_summaries(&artifact);
        assert_eq!(summaries[0], None);
        assert_eq!(summaries[1], Some(vec![0]));
    }

    #[test]
    fn recursive_identity_component_keeps_its_safe_fixed_point() {
        let mut artifact = branch_transport(true, false);
        artifact.code = vec![
            Instruction::Call {
                dst: Some(3),
                function: 0,
                args: vec![1, 2],
            },
            Instruction::Return { src: Some(3) },
        ];
        artifact.functions[0] = Function {
            flags: 0,
            name: "recursive_identity".into(),
            params: vec![19, 19],
            return_type: 20,
            outward_protocols: vec![],
            receiver_mode: None,
            register_types: vec![UNIT, 19, 19, 20],
            code_start: 0,
            code_len: 2,
            label_slot_count: 0,
        };
        assert_eq!(quantity_transport_summaries(&artifact)[0], Some(vec![0, 1]));
    }

    fn borrowed_callable_resumes(calls: usize) -> Artifact {
        let mut types = Type::predefined();
        types.push(Type::Resumption {
            input_type: I64,
            output_type: I64,
            effect_signature: Signature {
                params: vec![],
                result: UNIT,
                outward_protocols: vec![],
            },
            lower_uses: 2,
            upper_uses: Some(2),
            identity_name: "borrowed callable leaf".into(),
            copy: true,
        });
        types.push(Type::Tuple {
            fields: vec![19],
            copy: true,
        });
        types.push(Type::Callable {
            signature: Signature {
                params: vec![I64],
                result: UNIT,
                outward_protocols: vec![],
            },
            capture_type: 20,
            receiver_mode: 0,
            identity_name: "borrowed quantity closure".into(),
            copy: true,
            zero_use_allowed: false,
        });
        types.push(Type::RefShared { referent: 20 });
        let mut code = vec![Instruction::MakeCallable {
            dst: 4,
            callable_type: 21,
            function: 1,
            captures: vec![1],
        }];
        for index in 0..calls {
            code.push(Instruction::CallIndirect {
                dst: None,
                callable: 4,
                receiver_mode: 0,
                args: vec![2 + index as u32],
            });
        }
        code.extend([
            Instruction::Drop { register: 4 },
            Instruction::Const {
                dst: 5,
                constant: 0,
            },
            Instruction::Return { src: Some(5) },
        ]);
        let caller_len = code.len() as u32;
        code.extend([
            Instruction::ProjectCopy {
                dst: 2,
                src: 0,
                field: 0,
            },
            Instruction::Resume {
                dst: 3,
                resumption: 2,
                receiver_mode: 0,
                value: 1,
            },
            Instruction::Drop { register: 3 },
            Instruction::Const {
                dst: 4,
                constant: 0,
            },
            Instruction::Return { src: Some(4) },
        ]);
        Artifact {
            types,
            constants: vec![Constant::Unit],
            functions: vec![
                Function {
                    flags: 0,
                    name: "borrowed_caller".into(),
                    params: vec![19, I64, I64],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, 19, I64, I64, 21, UNIT],
                    code_start: 0,
                    code_len: caller_len,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "borrowed_target".into(),
                    params: vec![I64],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: Some(0),
                    register_types: vec![22, I64, 19, I64, UNIT],
                    code_start: caller_len,
                    code_len: 5,
                    label_slot_count: 0,
                },
            ],
            code,
            required_features: 1 | (1 << 3) | (1 << 4),
            ..Artifact::default()
        }
    }

    #[test]
    fn borrowed_callable_calls_accumulate_exact_capture_quantity() {
        let artifact = borrowed_callable_resumes(2);
        let labels = verify_labels(&artifact, 0, &artifact.functions[0]).unwrap();
        assert!(
            verify_resumption_quantities(&artifact, 0, &artifact.functions[0], &labels).is_ok()
        );
    }

    fn branched_borrowed_callable(disagree: bool) -> Artifact {
        let mut artifact = borrowed_callable_resumes(2);
        artifact.constants.push(Constant::U32(0));
        artifact.functions.clear();
        artifact.code.clear();
        artifact.code.extend([
            Instruction::Switch {
                discr: 2,
                cases: vec![(1, 1)],
                otherwise: 3,
            },
            Instruction::MakeCallable {
                dst: 5,
                callable_type: 21,
                function: 1,
                captures: vec![1],
            },
            Instruction::Jump { target: 4 },
            Instruction::MakeCallable {
                dst: 5,
                callable_type: 21,
                function: 2,
                captures: vec![1],
            },
            Instruction::CallIndirect {
                dst: None,
                callable: 5,
                receiver_mode: 0,
                args: vec![3],
            },
            Instruction::CallIndirect {
                dst: None,
                callable: 5,
                receiver_mode: 0,
                args: vec![4],
            },
            Instruction::Drop { register: 5 },
            Instruction::Const {
                dst: 6,
                constant: 0,
            },
            Instruction::Return { src: Some(6) },
        ]);
        let caller_len = artifact.code.len() as u32;
        let append_target = |code: &mut Vec<Instruction>, resumes: usize| {
            code.push(Instruction::ProjectCopy {
                dst: 2,
                src: 0,
                field: 0,
            });
            for _ in 0..resumes {
                code.extend([
                    Instruction::Resume {
                        dst: 3,
                        resumption: 2,
                        receiver_mode: 0,
                        value: 1,
                    },
                    Instruction::Drop { register: 3 },
                ]);
            }
            code.extend([
                Instruction::Drop { register: 2 },
                Instruction::Const {
                    dst: 4,
                    constant: 0,
                },
                Instruction::Return { src: Some(4) },
            ]);
        };
        append_target(&mut artifact.code, 1);
        let second_start = artifact.code.len() as u32;
        append_target(&mut artifact.code, usize::from(disagree) + 1);
        artifact.functions = vec![
            Function {
                flags: 0,
                name: "branched_borrowed_caller".into(),
                params: vec![19, U32, I64, I64],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 19, U32, I64, I64, 21, UNIT],
                code_start: 0,
                code_len: caller_len,
                label_slot_count: 0,
            },
            Function {
                flags: 0,
                name: "branched_borrowed_once_a".into(),
                params: vec![I64],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: Some(0),
                register_types: vec![22, I64, 19, I64, UNIT],
                code_start: caller_len,
                code_len: second_start - caller_len,
                label_slot_count: 0,
            },
            Function {
                flags: 0,
                name: "branched_borrowed_once_b".into(),
                params: vec![I64],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: Some(0),
                register_types: vec![22, I64, 19, I64, UNIT],
                code_start: second_start,
                code_len: artifact.code.len() as u32 - second_start,
                label_slot_count: 0,
            },
        ];
        artifact.required_features = crate::bytecode::used_features(
            &artifact.types,
            &artifact.code,
            !artifact.protocols.is_empty(),
            !artifact.imports.is_empty(),
        );
        artifact
    }

    #[test]
    fn branched_dynamic_targets_join_agreeing_receiver_quantity_summaries() {
        let result = verify(branched_borrowed_callable(false));
        assert!(result.is_ok(), "{result:?}");
    }

    #[test]
    fn branched_dynamic_targets_reject_disagreeing_receiver_quantity_summaries() {
        let result = verify(branched_borrowed_callable(true));
        assert!(
            matches!(result, Err(VerifyError::InvalidFunction(0))),
            "{result:?}"
        );
    }

    #[test]
    fn borrowed_callable_calls_cannot_exceed_capture_upper_bound() {
        let mut artifact = borrowed_callable_resumes(2);
        artifact.code.insert(
            3,
            Instruction::CallIndirect {
                dst: None,
                callable: 4,
                receiver_mode: 0,
                args: vec![3],
            },
        );
        artifact.functions[0].code_len += 1;
        artifact.functions[1].code_start += 1;
        let labels = verify_labels(&artifact, 0, &artifact.functions[0]).unwrap();
        assert!(matches!(
            verify_resumption_quantities(&artifact, 0, &artifact.functions[0], &labels),
            Err(VerifyError::InvalidFunction(0))
        ));
    }

    #[test]
    fn borrowed_callable_can_finish_with_an_owned_final_call() {
        let mut artifact = borrowed_callable_resumes(2);
        let Instruction::CallIndirect { receiver_mode, .. } = &mut artifact.code[2] else {
            unreachable!()
        };
        *receiver_mode = 2;
        artifact.code.remove(3);
        artifact.functions[0].code_len -= 1;
        artifact.functions[1].code_start -= 1;
        let labels = verify_labels(&artifact, 0, &artifact.functions[0]).unwrap();
        assert!(
            verify_resumption_quantities(&artifact, 0, &artifact.functions[0], &labels).is_ok()
        );
    }

    #[test]
    fn duplicated_callable_aliases_cannot_launder_capture_quantity() {
        let mut artifact = borrowed_callable_resumes(2);
        let Type::Resumption {
            lower_uses,
            upper_uses,
            ..
        } = &mut artifact.types[19]
        else {
            unreachable!()
        };
        *lower_uses = 0;
        *upper_uses = Some(1);
        artifact.functions[0].register_types.push(21);
        artifact
            .code
            .insert(1, Instruction::Copy { dst: 6, src: 4 });
        let Instruction::CallIndirect { callable, .. } = &mut artifact.code[3] else {
            unreachable!()
        };
        *callable = 6;
        artifact.code.insert(4, Instruction::Drop { register: 6 });
        artifact.functions[0].code_len += 2;
        artifact.functions[1].code_start += 2;
        let labels = verify_labels(&artifact, 0, &artifact.functions[0]).unwrap();
        assert!(matches!(
            verify_resumption_quantities(&artifact, 0, &artifact.functions[0], &labels),
            Err(VerifyError::InvalidFunction(0))
        ));
    }

    #[test]
    fn callable_target_survives_certified_direct_retain_summary() {
        let mut artifact = callable_transport(true);
        artifact.functions[0].register_types.push(21);
        artifact.code.insert(
            1,
            Instruction::Call {
                dst: Some(5),
                function: 2,
                args: vec![2],
            },
        );
        let Instruction::CallIndirect { callable, .. } = &mut artifact.code[2] else {
            unreachable!()
        };
        *callable = 5;
        artifact.functions[0].code_len += 1;
        artifact.functions[1].code_start += 1;
        let retain_start = artifact.code.len() as u32;
        artifact.code.extend([
            Instruction::Move { dst: 2, src: 1 },
            Instruction::Return { src: Some(2) },
        ]);
        artifact.functions.push(Function {
            flags: 0,
            name: "retain_callable".into(),
            params: vec![21],
            return_type: 21,
            outward_protocols: vec![],
            receiver_mode: None,
            register_types: vec![UNIT, 21, 21],
            code_start: retain_start,
            code_len: 2,
            label_slot_count: 0,
        });
        let labels = verify_labels(&artifact, 0, &artifact.functions[0]).unwrap();
        assert!(
            verify_resumption_quantities(&artifact, 0, &artifact.functions[0], &labels).is_ok()
        );
    }

    fn handler_result_transport(ambiguous: bool) -> Artifact {
        let mut artifact = handler_capture(false);
        let Type::Resumption {
            upper_uses, copy, ..
        } = &mut artifact.types[19]
        else {
            unreachable!()
        };
        *upper_uses = Some(2);
        *copy = true;
        artifact.code = vec![
            Instruction::Copy { dst: 2, src: 1 },
            Instruction::Copy { dst: 3, src: 1 },
            Instruction::MakeCallable {
                dst: 4,
                callable_type: 21,
                function: 1,
                captures: vec![2],
            },
            Instruction::MakeCallable {
                dst: 5,
                callable_type: 21,
                function: 2,
                captures: vec![3],
            },
            Instruction::MakeHandler {
                dst: 6,
                handler_def: 0,
                clauses: vec![4],
            },
            Instruction::Handle {
                dst: 7,
                handler: 6,
                body: 5,
                args: vec![],
            },
            Instruction::Drop { register: 1 },
            Instruction::Drop { register: 7 },
            Instruction::Const {
                dst: 8,
                constant: 0,
            },
            Instruction::Return { src: Some(8) },
        ];
        let main_len = artifact.code.len() as u32;
        artifact.code.extend([
            Instruction::Move { dst: 1, src: 0 },
            Instruction::Return { src: Some(1) },
        ]);
        let second_start = artifact.code.len() as u32;
        if ambiguous {
            artifact.constants.push(Constant::I64(0));
            artifact.code.extend([
                Instruction::ProjectCopy {
                    dst: 1,
                    src: 0,
                    field: 0,
                },
                Instruction::Const {
                    dst: 3,
                    constant: 1,
                },
                Instruction::Resume {
                    dst: 4,
                    resumption: 1,
                    receiver_mode: 0,
                    value: 3,
                },
                Instruction::Drop { register: 4 },
                Instruction::Drop { register: 1 },
                Instruction::Move { dst: 2, src: 0 },
                Instruction::Return { src: Some(2) },
            ]);
        } else {
            artifact.code.extend([
                Instruction::Move { dst: 1, src: 0 },
                Instruction::Return { src: Some(1) },
            ]);
        }
        artifact.functions = vec![
            Function {
                flags: 0,
                name: "handler_result_main".into(),
                params: vec![19],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 19, 19, 19, 21, 21, 23, 20, UNIT],
                code_start: 0,
                code_len: main_len,
                label_slot_count: 0,
            },
            Function {
                flags: 0,
                name: "handler_clause_result".into(),
                params: vec![],
                return_type: 20,
                outward_protocols: vec![],
                receiver_mode: Some(2),
                register_types: vec![20, 20],
                code_start: main_len,
                code_len: 2,
                label_slot_count: 0,
            },
            Function {
                flags: 0,
                name: "handler_body_result".into(),
                params: vec![],
                return_type: 20,
                outward_protocols: vec![],
                receiver_mode: Some(2),
                register_types: if ambiguous {
                    vec![20, 19, 20, I64, I64]
                } else {
                    vec![20, 20]
                },
                code_start: second_start,
                code_len: artifact.code.len() as u32 - second_start,
                label_slot_count: 0,
            },
        ];
        artifact
    }

    #[test]
    fn handle_result_relays_one_exact_origin_from_body_and_clause_targets() {
        let artifact = handler_result_transport(false);
        let labels = verify_labels(&artifact, 0, &artifact.functions[0]).unwrap();
        assert!(
            verify_resumption_quantities(&artifact, 0, &artifact.functions[0], &labels).is_ok()
        );
    }

    #[test]
    fn handle_result_rejects_an_uncertified_candidate_target() {
        let artifact = handler_result_transport(true);
        let labels = verify_labels(&artifact, 0, &artifact.functions[0]).unwrap();
        assert!(matches!(
            verify_resumption_quantities(&artifact, 0, &artifact.functions[0], &labels),
            Err(VerifyError::InvalidFunction(0))
        ));
    }

    fn handler_disposition_artifact(disagree: bool) -> Artifact {
        let mut types = Type::predefined();
        types.extend([
            Type::Resumption {
                identity_name: "handler disposition quantity".into(),
                input_type: UNIT,
                output_type: UNIT,
                effect_signature: Signature {
                    params: vec![],
                    result: UNIT,
                    outward_protocols: vec![],
                },
                lower_uses: 0,
                upper_uses: Some(2),
                copy: true,
            },
            Type::Tuple {
                fields: vec![19],
                copy: true,
            }
            .restricted(true, true),
            Type::Callable {
                signature: Signature {
                    params: vec![],
                    result: UNIT,
                    outward_protocols: vec![],
                },
                capture_type: 20,
                receiver_mode: 2,
                identity_name: "disposition callable".into(),
                copy: false,
                zero_use_allowed: true,
            },
            Type::Tuple {
                fields: vec![21],
                copy: false,
            },
            Type::Handler {
                handler_def: 0,
                capture_type: 22,
                identity_name: "disposition handler".into(),
            },
        ]);
        let mut code = vec![
            Instruction::Copy { dst: 2, src: 1 },
            Instruction::MakeCallable {
                dst: 3,
                callable_type: 21,
                function: 1,
                captures: vec![1],
            },
            Instruction::MakeCallable {
                dst: 4,
                callable_type: 21,
                function: 2,
                captures: vec![2],
            },
            Instruction::MakeHandler {
                dst: 5,
                handler_def: 0,
                clauses: vec![4],
            },
            Instruction::Handle {
                dst: 6,
                handler: 5,
                body: 3,
                args: vec![],
            },
            Instruction::Return { src: Some(6) },
        ];
        let caller_len = code.len() as u32;
        code.extend([
            Instruction::ProjectMove {
                dst: 2,
                src: 0,
                field: 0,
            },
            Instruction::Drop { register: 0 },
            Instruction::Cancel {
                dst: 1,
                resumption: 2,
            },
            Instruction::Return { src: Some(1) },
        ]);
        let clause_start = code.len() as u32;
        if disagree {
            code.extend([
                Instruction::ProjectMove {
                    dst: 2,
                    src: 0,
                    field: 0,
                },
                Instruction::Drop { register: 0 },
                Instruction::Drop { register: 2 },
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::Return { src: Some(1) },
            ]);
        } else {
            code.extend([
                Instruction::ProjectMove {
                    dst: 2,
                    src: 0,
                    field: 0,
                },
                Instruction::Drop { register: 0 },
                Instruction::Cancel {
                    dst: 1,
                    resumption: 2,
                },
                Instruction::Return { src: Some(1) },
            ]);
        }
        let operation = Operation {
            name: "terminal".into(),
            payload_signature: Signature {
                params: vec![],
                result: UNIT,
                outward_protocols: vec![],
            },
            result_type: NEVER,
            resumption_lower: 0,
            resumption_upper: Some(0),
            terminal: true,
        };
        let mut artifact = Artifact {
            types,
            constants: vec![Constant::Unit],
            protocols: vec![Protocol {
                display_name: "Disposition".into(),
                type_arguments: vec![],
                operations: vec![operation],
            }],
            handler_defs: vec![HandlerDef {
                result_type: UNIT,
                clauses: vec![HandlerClause {
                    protocol: 0,
                    operation: 0,
                    resumption_type: None,
                    callable_signature: Signature {
                        params: vec![],
                        result: UNIT,
                        outward_protocols: vec![],
                    },
                }],
                partial: false,
            }],
            functions: vec![
                Function {
                    flags: 0,
                    name: "handler_disposition_caller".into(),
                    params: vec![19],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, 19, 19, 21, 21, 23, UNIT],
                    code_start: 0,
                    code_len: caller_len,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "handler_disposition_body".into(),
                    params: vec![],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: Some(2),
                    register_types: vec![20, UNIT, 19],
                    code_start: caller_len,
                    code_len: clause_start - caller_len,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "handler_disposition_clause".into(),
                    params: vec![],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: Some(2),
                    register_types: vec![20, UNIT, 19],
                    code_start: clause_start,
                    code_len: code.len() as u32 - clause_start,
                    label_slot_count: 0,
                },
            ],
            code,
            ..Artifact::default()
        };
        artifact.required_features =
            crate::bytecode::used_features(&artifact.types, &artifact.code, true, false);
        artifact
    }

    #[test]
    fn dynamic_handler_alternatives_require_one_exact_terminal_disposition() {
        verify(handler_disposition_artifact(false))
            .expect("body and clause both cancel the shared logical quantity");
        assert!(matches!(
            verify(handler_disposition_artifact(true)),
            Err(VerifyError::InvalidFunction(0))
        ));
    }

    #[test]
    fn owned_quantity_disposition_summaries_converge_through_recursive_indirect_calls() {
        let mut artifact = callable_transport(true);
        artifact.functions.clear();
        artifact.code.clear();
        let append = |code: &mut Vec<Instruction>, target: u32| {
            code.extend([
                Instruction::ProjectMove {
                    dst: 1,
                    src: 0,
                    field: 0,
                },
                Instruction::Drop { register: 0 },
                Instruction::MakeCallable {
                    dst: 2,
                    callable_type: 21,
                    function: target,
                    captures: vec![1],
                },
                Instruction::CallIndirect {
                    dst: Some(3),
                    callable: 2,
                    receiver_mode: 2,
                    args: vec![],
                },
                Instruction::Return { src: Some(3) },
            ]);
        };
        append(&mut artifact.code, 1);
        let second_start = artifact.code.len() as u32;
        append(&mut artifact.code, 0);
        artifact.functions = vec![
            Function {
                flags: 0,
                name: "recursive_quantity_a".into(),
                params: vec![],
                return_type: 20,
                outward_protocols: vec![],
                receiver_mode: Some(2),
                register_types: vec![20, 19, 21, 20],
                code_start: 0,
                code_len: second_start,
                label_slot_count: 0,
            },
            Function {
                flags: 0,
                name: "recursive_quantity_b".into(),
                params: vec![],
                return_type: 20,
                outward_protocols: vec![],
                receiver_mode: Some(2),
                register_types: vec![20, 19, 21, 20],
                code_start: second_start,
                code_len: artifact.code.len() as u32 - second_start,
                label_slot_count: 0,
            },
        ];
        let expected = OwnedReceiverQuantitySummary {
            outputs: vec![0],
            resumes: vec![0],
            dispositions: vec![QuantityTerminalDisposition::Returned],
        };
        assert_eq!(
            owned_receiver_quantity_summaries(&artifact),
            vec![Some(expected.clone()), Some(expected)]
        );
    }

    #[test]
    fn finite_tail_indirect_quantity_targets_converge_and_opaque_targets_fail_closed() {
        let mut artifact = callable_transport(true);
        artifact.functions.clear();
        artifact.code.clear();
        let append = |code: &mut Vec<Instruction>, target: u32| {
            code.extend([
                Instruction::ProjectMove {
                    dst: 1,
                    src: 0,
                    field: 0,
                },
                Instruction::Drop { register: 0 },
                Instruction::MakeCallable {
                    dst: 2,
                    callable_type: 21,
                    function: target,
                    captures: vec![1],
                },
                Instruction::TailCallIndirect {
                    callable: 2,
                    receiver_mode: 2,
                    args: vec![],
                },
            ]);
        };
        append(&mut artifact.code, 1);
        let second_start = artifact.code.len() as u32;
        append(&mut artifact.code, 0);
        artifact.functions = vec![
            Function {
                flags: 0,
                name: "tail_indirect_quantity_a".into(),
                params: vec![],
                return_type: 20,
                outward_protocols: vec![],
                receiver_mode: Some(2),
                register_types: vec![20, 19, 21],
                code_start: 0,
                code_len: second_start,
                label_slot_count: 0,
            },
            Function {
                flags: 0,
                name: "tail_indirect_quantity_b".into(),
                params: vec![],
                return_type: 20,
                outward_protocols: vec![],
                receiver_mode: Some(2),
                register_types: vec![20, 19, 21],
                code_start: second_start,
                code_len: artifact.code.len() as u32 - second_start,
                label_slot_count: 0,
            },
        ];
        let identity = OwnedReceiverQuantitySummary {
            outputs: vec![0],
            resumes: vec![0],
            dispositions: vec![QuantityTerminalDisposition::Returned],
        };
        assert_eq!(
            owned_receiver_quantity_summaries(&artifact),
            vec![Some(identity.clone()), Some(identity)]
        );
        artifact.required_features =
            crate::bytecode::used_features(&artifact.types, &artifact.code, false, false);
        for (fid, function) in artifact.functions.iter().enumerate() {
            let labels = verify_labels(&artifact, fid as u32, function).unwrap();
            assert!(
                verify_resumption_quantities(&artifact, fid as u32, function, &labels).is_ok(),
                "finite tail-indirect target {fid} retains one exact origin"
            );
        }

        artifact.code = vec![Instruction::TailCallIndirect {
            callable: 1,
            receiver_mode: 2,
            args: vec![],
        }];
        artifact.functions = vec![Function {
            flags: 0,
            name: "opaque_tail_indirect_quantity".into(),
            params: vec![21],
            return_type: 20,
            outward_protocols: vec![],
            receiver_mode: None,
            register_types: vec![UNIT, 21],
            code_start: 0,
            code_len: 1,
            label_slot_count: 0,
        }];
        let labels = verify_labels(&artifact, 0, &artifact.functions[0]).unwrap();
        assert!(matches!(
            verify_resumption_quantities(&artifact, 0, &artifact.functions[0], &labels),
            Err(VerifyError::InvalidFunction(0))
        ));
    }

    #[test]
    fn parameter_quantity_dispositions_converge_through_mutual_direct_tail_calls() {
        let mut artifact = branch_transport(true, false);
        artifact.code = vec![
            Instruction::TailCall {
                function: 1,
                args: vec![1],
            },
            Instruction::TailCall {
                function: 0,
                args: vec![1],
            },
        ];
        artifact.functions = vec![
            Function {
                flags: 0,
                name: "direct_quantity_a".into(),
                params: vec![19],
                return_type: 19,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 19],
                code_start: 0,
                code_len: 1,
                label_slot_count: 0,
            },
            Function {
                flags: 0,
                name: "direct_quantity_b".into(),
                params: vec![19],
                return_type: 19,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 19],
                code_start: 1,
                code_len: 1,
                label_slot_count: 0,
            },
        ];
        artifact.required_features =
            crate::bytecode::used_features(&artifact.types, &artifact.code, false, false);
        let identity = OwnedReceiverQuantitySummary {
            outputs: vec![0],
            resumes: vec![0],
            dispositions: vec![QuantityTerminalDisposition::Returned],
        };
        assert_eq!(
            owned_receiver_quantity_summaries(&artifact),
            vec![Some(identity.clone()), Some(identity)]
        );
        verify(artifact).expect("the mutually recursive direct identity SCC is exact");
    }

    #[test]
    fn terminal_disposition_propagates_through_a_direct_tail_call() {
        let mut artifact = branch_transport(true, false);
        artifact.code = vec![
            Instruction::TailCall {
                function: 1,
                args: vec![1],
            },
            Instruction::Cancel {
                dst: 2,
                resumption: 1,
            },
            Instruction::Return { src: Some(2) },
        ];
        artifact.functions = vec![
            Function {
                flags: 0,
                name: "direct_quantity_cancel_forwarder".into(),
                params: vec![19],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 19],
                code_start: 0,
                code_len: 1,
                label_slot_count: 0,
            },
            Function {
                flags: 0,
                name: "direct_quantity_canceller".into(),
                params: vec![19],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 19, UNIT],
                code_start: 1,
                code_len: 2,
                label_slot_count: 0,
            },
        ];
        artifact.required_features =
            crate::bytecode::used_features(&artifact.types, &artifact.code, false, false);
        let cancelled = OwnedReceiverQuantitySummary {
            outputs: vec![],
            resumes: vec![0],
            dispositions: vec![QuantityTerminalDisposition::Cancelled],
        };
        assert_eq!(
            owned_receiver_quantity_summaries(&artifact),
            vec![Some(cancelled.clone()), Some(cancelled)]
        );
        verify(artifact).expect("the caller inherits the callee's exact cancellation");
    }

    fn borrowed_receiver_parameter_types() -> Vec<Type> {
        let mut types = Type::predefined();
        types.extend([
            Type::Resumption {
                identity_name: "borrowed receiver parameter".into(),
                input_type: UNIT,
                output_type: UNIT,
                effect_signature: Signature {
                    params: vec![],
                    result: UNIT,
                    outward_protocols: vec![],
                },
                lower_uses: 0,
                upper_uses: Some(1),
                copy: false,
            },
            Type::RefShared { referent: UNIT },
        ]);
        types
    }

    #[test]
    fn borrowed_self_tail_recursion_preserves_parameter_quantity_identity() {
        let mut artifact = Artifact {
            types: borrowed_receiver_parameter_types(),
            functions: vec![Function {
                flags: 0,
                name: "borrowed_quantity_self".into(),
                params: vec![19],
                return_type: 19,
                outward_protocols: vec![],
                receiver_mode: Some(0),
                register_types: vec![20, 19],
                code_start: 0,
                code_len: 1,
                label_slot_count: 0,
            }],
            code: vec![Instruction::TailCallSelf { args: vec![1] }],
            ..Artifact::default()
        };
        artifact.required_features =
            crate::bytecode::used_features(&artifact.types, &artifact.code, false, false);
        let identity = OwnedReceiverQuantitySummary {
            outputs: vec![0],
            resumes: vec![0],
            dispositions: vec![QuantityTerminalDisposition::Returned],
        };
        assert_eq!(
            owned_receiver_quantity_summaries(&artifact),
            vec![Some(identity)]
        );
        verify(artifact).expect("borrowed self recursion retains the exact parameter owner");
    }

    #[test]
    fn known_borrowed_receiver_propagates_terminal_parameter_cancellation() {
        let mut artifact = Artifact {
            types: borrowed_receiver_parameter_types(),
            functions: vec![
                Function {
                    flags: 0,
                    name: "known_receiver_cancel_forwarder".into(),
                    params: vec![19],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: Some(0),
                    register_types: vec![20, 19, UNIT],
                    code_start: 0,
                    code_len: 2,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "known_receiver_canceller".into(),
                    params: vec![19],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: Some(0),
                    register_types: vec![20, 19, UNIT],
                    code_start: 2,
                    code_len: 2,
                    label_slot_count: 0,
                },
            ],
            code: vec![
                Instruction::CallKnownReceiver {
                    dst: Some(2),
                    function: 1,
                    receiver: 0,
                    args: vec![1],
                },
                Instruction::Return { src: Some(2) },
                Instruction::Cancel {
                    dst: 2,
                    resumption: 1,
                },
                Instruction::Return { src: Some(2) },
            ],
            ..Artifact::default()
        };
        artifact.required_features =
            crate::bytecode::used_features(&artifact.types, &artifact.code, false, false);
        let cancelled = OwnedReceiverQuantitySummary {
            outputs: vec![],
            resumes: vec![0],
            dispositions: vec![QuantityTerminalDisposition::Cancelled],
        };
        assert_eq!(
            owned_receiver_quantity_summaries(&artifact),
            vec![Some(cancelled.clone()), Some(cancelled)]
        );
        verify(artifact).expect("known borrowed receiver preserves terminal cancellation");
    }

    #[test]
    fn borrowed_receiver_delta_fixed_point_handles_known_calls_and_rejects_growth() {
        let mut artifact = borrowed_callable_resumes(2);
        let caller_len = artifact.functions[0].code_len as usize;
        let target = artifact.code[caller_len..].to_vec();
        artifact.code.truncate(caller_len);
        artifact.code.extend([
            Instruction::CallKnownReceiver {
                dst: Some(2),
                function: 2,
                receiver: 0,
                args: vec![1],
            },
            Instruction::Return { src: Some(2) },
        ]);
        let target_start = artifact.code.len() as u32;
        artifact.code.extend(target);
        artifact.functions[1].register_types = vec![22, I64, UNIT];
        artifact.functions[1].code_start = caller_len as u32;
        artifact.functions[1].code_len = 2;
        let mut target_function = artifact.functions[1].clone();
        target_function.name = "known_receiver_resume_target".into();
        target_function.register_types = vec![22, I64, 19, I64, UNIT];
        target_function.code_start = target_start;
        target_function.code_len = artifact.code.len() as u32 - target_start;
        artifact.functions.push(target_function);
        artifact.required_features =
            crate::bytecode::used_features(&artifact.types, &artifact.code, false, false);
        let deltas = borrowed_receiver_resume_delta_summaries(&artifact);
        assert_eq!(deltas[1], Some(vec![1]));
        assert_eq!(deltas[2], Some(vec![1]));
        let labels = verify_labels(&artifact, 0, &artifact.functions[0]).unwrap();
        assert!(
            verify_resumption_quantities(&artifact, 0, &artifact.functions[0], &labels).is_ok(),
            "two delegated borrowed calls satisfy the exact caller quantity"
        );

        let start = artifact.functions[1].code_start as usize;
        artifact.code.splice(
            start..start + 2,
            [
                Instruction::ProjectCopy {
                    dst: 2,
                    src: 0,
                    field: 0,
                },
                Instruction::Resume {
                    dst: 3,
                    resumption: 2,
                    receiver_mode: 0,
                    value: 1,
                },
                Instruction::Drop { register: 3 },
                Instruction::TailCallSelf { args: vec![1] },
            ],
        );
        artifact.functions[1].register_types = vec![22, I64, 19, I64];
        artifact.functions[1].code_len = 4;
        artifact.functions[2].code_start += 2;
        assert_eq!(borrowed_receiver_resume_delta_summaries(&artifact)[1], None);
    }

    #[test]
    fn oscillating_direct_quantity_scc_is_pinned_without_erasing_independent_facts() {
        let mut artifact = branch_transport(true, false);
        artifact.code = vec![
            Instruction::TailCall {
                function: 1,
                args: vec![1, 2],
            },
            Instruction::TailCall {
                function: 0,
                args: vec![2, 1],
            },
            Instruction::Move { dst: 2, src: 1 },
            Instruction::Return { src: Some(2) },
        ];
        artifact.functions = vec![
            Function {
                flags: 0,
                name: "direct_quantity_swap_a".into(),
                params: vec![19, 19],
                return_type: 20,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 19, 19],
                code_start: 0,
                code_len: 1,
                label_slot_count: 0,
            },
            Function {
                flags: 0,
                name: "direct_quantity_swap_b".into(),
                params: vec![19, 19],
                return_type: 20,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 19, 19],
                code_start: 1,
                code_len: 1,
                label_slot_count: 0,
            },
            Function {
                flags: 0,
                name: "independent_direct_quantity".into(),
                params: vec![19],
                return_type: 19,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 19, 19],
                code_start: 2,
                code_len: 2,
                label_slot_count: 0,
            },
        ];
        let identity = OwnedReceiverQuantitySummary {
            outputs: vec![0],
            resumes: vec![0],
            dispositions: vec![QuantityTerminalDisposition::Returned],
        };
        assert_eq!(
            owned_receiver_quantity_summaries(&artifact),
            vec![None, None, Some(identity)]
        );
    }

    fn handler_parameter_disposition_artifact(disagree: bool) -> Artifact {
        let mut types = Type::predefined();
        types.extend([
            Type::Resumption {
                identity_name: "handler parameter quantity".into(),
                input_type: UNIT,
                output_type: UNIT,
                effect_signature: Signature {
                    params: vec![],
                    result: UNIT,
                    outward_protocols: vec![],
                },
                lower_uses: 0,
                upper_uses: Some(2),
                copy: true,
            },
            Type::Tuple {
                fields: vec![19],
                copy: true,
            }
            .restricted(true, true),
            Type::Callable {
                signature: Signature {
                    params: vec![],
                    result: UNIT,
                    outward_protocols: vec![],
                },
                capture_type: 20,
                receiver_mode: 2,
                identity_name: "parameter clause".into(),
                copy: false,
                zero_use_allowed: true,
            },
            Type::Tuple {
                fields: vec![21],
                copy: false,
            },
            Type::Handler {
                handler_def: 0,
                capture_type: 22,
                identity_name: "parameter handler".into(),
            },
            Type::Callable {
                signature: Signature {
                    params: vec![19],
                    result: UNIT,
                    outward_protocols: vec![0],
                },
                capture_type: UNIT,
                receiver_mode: 2,
                identity_name: "parameter body".into(),
                copy: false,
                zero_use_allowed: true,
            },
        ]);
        let mut code = vec![
            Instruction::Copy { dst: 2, src: 1 },
            Instruction::MakeCallable {
                dst: 3,
                callable_type: 21,
                function: 1,
                captures: vec![1],
            },
            Instruction::MakeHandler {
                dst: 4,
                handler_def: 0,
                clauses: vec![3],
            },
            Instruction::MakeCallable {
                dst: 5,
                callable_type: 24,
                function: 2,
                captures: vec![],
            },
            Instruction::Handle {
                dst: 6,
                handler: 4,
                body: 5,
                args: vec![2],
            },
            Instruction::Return { src: Some(6) },
        ];
        let caller_len = code.len() as u32;
        code.extend([
            Instruction::ProjectMove {
                dst: 2,
                src: 0,
                field: 0,
            },
            Instruction::Drop { register: 0 },
            Instruction::Cancel {
                dst: 1,
                resumption: 2,
            },
            Instruction::Return { src: Some(1) },
        ]);
        let body_start = code.len() as u32;
        if disagree {
            code.extend([
                Instruction::Drop { register: 1 },
                Instruction::Const {
                    dst: 2,
                    constant: 0,
                },
                Instruction::Return { src: Some(2) },
            ]);
        } else {
            code.extend([
                Instruction::Cancel {
                    dst: 2,
                    resumption: 1,
                },
                Instruction::Return { src: Some(2) },
            ]);
        }
        let terminal = Operation {
            name: "terminal".into(),
            payload_signature: Signature {
                params: vec![],
                result: UNIT,
                outward_protocols: vec![],
            },
            result_type: NEVER,
            resumption_lower: 0,
            resumption_upper: Some(0),
            terminal: true,
        };
        let mut artifact = Artifact {
            types,
            constants: vec![Constant::Unit],
            protocols: vec![Protocol {
                display_name: "ParameterDisposition".into(),
                type_arguments: vec![],
                operations: vec![terminal],
            }],
            handler_defs: vec![HandlerDef {
                result_type: UNIT,
                clauses: vec![HandlerClause {
                    protocol: 0,
                    operation: 0,
                    resumption_type: None,
                    callable_signature: Signature {
                        params: vec![],
                        result: UNIT,
                        outward_protocols: vec![],
                    },
                }],
                partial: false,
            }],
            functions: vec![
                Function {
                    flags: 0,
                    name: "handler_parameter_caller".into(),
                    params: vec![19],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, 19, 19, 21, 23, 24, UNIT],
                    code_start: 0,
                    code_len: caller_len,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "handler_parameter_clause".into(),
                    params: vec![],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: Some(2),
                    register_types: vec![20, UNIT, 19],
                    code_start: caller_len,
                    code_len: body_start - caller_len,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "handler_parameter_body".into(),
                    params: vec![19],
                    return_type: UNIT,
                    outward_protocols: vec![0],
                    receiver_mode: Some(2),
                    register_types: vec![UNIT, 19, UNIT],
                    code_start: body_start,
                    code_len: code.len() as u32 - body_start,
                    label_slot_count: 0,
                },
            ],
            code,
            ..Artifact::default()
        };
        artifact.required_features =
            crate::bytecode::used_features(&artifact.types, &artifact.code, true, false);
        artifact
    }

    #[test]
    fn dynamic_handler_body_parameters_keep_exact_quantity_dispositions() {
        let accepted = handler_parameter_disposition_artifact(false);
        let summaries = owned_receiver_quantity_summaries(&accepted);
        let labels0 = verify_labels(&accepted, 0, &accepted.functions[0]).unwrap();
        let target_facts =
            callable_targets_at_pcs(&accepted, 0, &accepted.functions[0], &labels0).unwrap();
        assert_eq!(target_facts[4][5], CallableTargets::from([2]));
        assert_eq!(
            finite_handler_clause_targets(&accepted, 23),
            Some(vec![CallableTargets::from([1])])
        );
        assert_eq!(
            summaries[0],
            Some(OwnedReceiverQuantitySummary {
                outputs: vec![],
                resumes: vec![0],
                dispositions: vec![QuantityTerminalDisposition::Cancelled],
            })
        );
        assert!(summaries[1].is_some(), "clause summary: {summaries:?}");
        assert!(summaries[2].is_some(), "body summary: {summaries:?}");
        let labels = verify_labels(&accepted, 0, &accepted.functions[0]).unwrap();
        let quantity = verify_resumption_quantities(&accepted, 0, &accepted.functions[0], &labels);
        assert!(
            quantity.is_ok(),
            "quantity: {quantity:?}; summaries: {summaries:?}"
        );
        verify(accepted)
            .expect("the body parameter and clause capture cancel one logical quantity");
        assert!(matches!(
            verify(handler_parameter_disposition_artifact(true)),
            Err(VerifyError::InvalidFunction(0))
        ));
    }

    #[test]
    fn nested_partial_handle_identity_scc_converges_and_opaque_body_fails_closed() {
        let mut artifact = callable_transport(true);
        artifact.types.push(Type::Handler {
            handler_def: 0,
            capture_type: UNIT,
            identity_name: "recursive partial identity".into(),
        });
        artifact.handler_defs = vec![HandlerDef {
            result_type: 20,
            clauses: vec![],
            partial: true,
        }];
        artifact.code.clear();
        let append = |code: &mut Vec<Instruction>, target: u32| {
            code.extend([
                Instruction::ProjectMove {
                    dst: 1,
                    src: 0,
                    field: 0,
                },
                Instruction::Drop { register: 0 },
                Instruction::MakeHandler {
                    dst: 2,
                    handler_def: 0,
                    clauses: vec![],
                },
                Instruction::MakeCallable {
                    dst: 3,
                    callable_type: 21,
                    function: target,
                    captures: vec![1],
                },
                Instruction::Handle {
                    dst: 4,
                    handler: 2,
                    body: 3,
                    args: vec![],
                },
                Instruction::Return { src: Some(4) },
            ]);
        };
        append(&mut artifact.code, 1);
        let second_start = artifact.code.len() as u32;
        append(&mut artifact.code, 0);
        artifact.functions = vec![
            Function {
                flags: 0,
                name: "nested_handle_identity_a".into(),
                params: vec![],
                return_type: 20,
                outward_protocols: vec![],
                receiver_mode: Some(2),
                register_types: vec![20, 19, 22, 21, 20],
                code_start: 0,
                code_len: second_start,
                label_slot_count: 0,
            },
            Function {
                flags: 0,
                name: "nested_handle_identity_b".into(),
                params: vec![],
                return_type: 20,
                outward_protocols: vec![],
                receiver_mode: Some(2),
                register_types: vec![20, 19, 22, 21, 20],
                code_start: second_start,
                code_len: artifact.code.len() as u32 - second_start,
                label_slot_count: 0,
            },
        ];
        let identity = OwnedReceiverQuantitySummary {
            outputs: vec![0],
            resumes: vec![0],
            dispositions: vec![QuantityTerminalDisposition::Returned],
        };
        assert_eq!(
            owned_receiver_quantity_summaries(&artifact),
            vec![Some(identity.clone()), Some(identity)]
        );

        artifact.code = vec![
            Instruction::Handle {
                dst: 3,
                handler: 1,
                body: 2,
                args: vec![],
            },
            Instruction::Return { src: Some(3) },
        ];
        artifact.functions = vec![Function {
            flags: 0,
            name: "opaque_nested_handle_body".into(),
            params: vec![22, 21],
            return_type: 20,
            outward_protocols: vec![],
            receiver_mode: None,
            register_types: vec![UNIT, 22, 21, 20],
            code_start: 0,
            code_len: 2,
            label_slot_count: 0,
        }];
        assert_eq!(owned_receiver_quantity_summaries(&artifact), vec![None]);
    }

    #[test]
    fn nested_partial_handle_permutation_scc_is_pinned_opaque() {
        let mut artifact = branch_transport(true, false);
        artifact.types.extend([
            Type::Callable {
                signature: Signature {
                    params: vec![],
                    result: 20,
                    outward_protocols: vec![],
                },
                capture_type: 20,
                receiver_mode: 2,
                identity_name: "recursive partial permutation body".into(),
                copy: false,
                zero_use_allowed: true,
            },
            Type::Handler {
                handler_def: 0,
                capture_type: UNIT,
                identity_name: "recursive partial permutation handler".into(),
            },
        ]);
        artifact.handler_defs = vec![HandlerDef {
            result_type: 20,
            clauses: vec![],
            partial: true,
        }];
        artifact.code.clear();
        let append = |code: &mut Vec<Instruction>, target: u32, captures: [u32; 2]| {
            code.extend([
                Instruction::ProjectMove {
                    dst: 1,
                    src: 0,
                    field: 0,
                },
                Instruction::ProjectMove {
                    dst: 2,
                    src: 0,
                    field: 1,
                },
                Instruction::Deconstruct { src: 0 },
                Instruction::MakeHandler {
                    dst: 3,
                    handler_def: 0,
                    clauses: vec![],
                },
                Instruction::MakeCallable {
                    dst: 4,
                    callable_type: 21,
                    function: target,
                    captures: captures.into(),
                },
                Instruction::Handle {
                    dst: 5,
                    handler: 3,
                    body: 4,
                    args: vec![],
                },
                Instruction::Return { src: Some(5) },
            ]);
        };
        append(&mut artifact.code, 1, [1, 2]);
        let second_start = artifact.code.len() as u32;
        append(&mut artifact.code, 0, [2, 1]);
        artifact.functions = vec![
            Function {
                flags: 0,
                name: "nested_handle_permutation_a".into(),
                params: vec![],
                return_type: 20,
                outward_protocols: vec![],
                receiver_mode: Some(2),
                register_types: vec![20, 19, 19, 22, 21, 20],
                code_start: 0,
                code_len: second_start,
                label_slot_count: 0,
            },
            Function {
                flags: 0,
                name: "nested_handle_permutation_b".into(),
                params: vec![],
                return_type: 20,
                outward_protocols: vec![],
                receiver_mode: Some(2),
                register_types: vec![20, 19, 19, 22, 21, 20],
                code_start: second_start,
                code_len: artifact.code.len() as u32 - second_start,
                label_slot_count: 0,
            },
        ];

        assert_eq!(
            owned_receiver_quantity_summaries(&artifact),
            vec![None, None]
        );
    }

    fn fresh_handler_resumption_artifact(forge_live_fresh: bool) -> Artifact {
        let mut types = Type::predefined();
        types.extend([
            Type::Resumption {
                identity_name: "fresh handler resumption".into(),
                input_type: UNIT,
                output_type: UNIT,
                effect_signature: Signature {
                    params: vec![],
                    result: UNIT,
                    outward_protocols: vec![],
                },
                lower_uses: 0,
                upper_uses: Some(2),
                copy: true,
            },
            Type::RefShared { referent: UNIT },
            Type::Callable {
                signature: Signature {
                    params: vec![19],
                    result: UNIT,
                    outward_protocols: vec![],
                },
                capture_type: UNIT,
                receiver_mode: 0,
                identity_name: "fresh resumption clause".into(),
                copy: false,
                zero_use_allowed: true,
            },
            Type::Tuple {
                fields: vec![21],
                copy: false,
            },
            Type::Handler {
                handler_def: 0,
                capture_type: 22,
                identity_name: "fresh resumption handler".into(),
            },
            Type::Callable {
                signature: Signature {
                    params: vec![],
                    result: UNIT,
                    outward_protocols: vec![0],
                },
                capture_type: UNIT,
                receiver_mode: 2,
                identity_name: "fresh resumption body".into(),
                copy: false,
                zero_use_allowed: true,
            },
        ]);
        let mut code = vec![
            Instruction::MakeCallable {
                dst: 1,
                callable_type: 21,
                function: 1,
                captures: vec![],
            },
            Instruction::MakeHandler {
                dst: 2,
                handler_def: 0,
                clauses: vec![1],
            },
            Instruction::MakeCallable {
                dst: 3,
                callable_type: 24,
                function: 2,
                captures: vec![],
            },
            Instruction::Handle {
                dst: 4,
                handler: 2,
                body: 3,
                args: vec![],
            },
            Instruction::Return { src: Some(4) },
        ];
        let caller_len = code.len() as u32;
        if forge_live_fresh {
            code.extend([
                Instruction::Const {
                    dst: 2,
                    constant: 0,
                },
                Instruction::Return { src: Some(2) },
            ]);
        } else {
            code.extend([
                Instruction::Cancel {
                    dst: 2,
                    resumption: 1,
                },
                Instruction::Return { src: Some(2) },
            ]);
        }
        let body_start = code.len() as u32;
        code.extend([
            Instruction::Perform {
                dst: Some(1),
                protocol: 0,
                operation: 0,
                payloads: vec![],
            },
            Instruction::Return { src: Some(1) },
        ]);
        let mut artifact = Artifact {
            types,
            constants: vec![Constant::Unit],
            protocols: vec![Protocol {
                display_name: "FreshDisposition".into(),
                type_arguments: vec![],
                operations: vec![Operation {
                    name: "optional".into(),
                    payload_signature: Signature {
                        params: vec![],
                        result: UNIT,
                        outward_protocols: vec![],
                    },
                    result_type: UNIT,
                    resumption_lower: 0,
                    resumption_upper: Some(2),
                    terminal: false,
                }],
            }],
            handler_defs: vec![HandlerDef {
                result_type: UNIT,
                clauses: vec![HandlerClause {
                    protocol: 0,
                    operation: 0,
                    resumption_type: Some(19),
                    callable_signature: Signature {
                        params: vec![19],
                        result: UNIT,
                        outward_protocols: vec![],
                    },
                }],
                partial: false,
            }],
            functions: vec![
                Function {
                    flags: 0,
                    name: "fresh_resumption_caller".into(),
                    params: vec![],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, 21, 23, 24, UNIT],
                    code_start: 0,
                    code_len: caller_len,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "fresh_resumption_clause".into(),
                    params: vec![19],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: Some(0),
                    register_types: vec![20, 19, UNIT],
                    code_start: caller_len,
                    code_len: body_start - caller_len,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "fresh_resumption_body".into(),
                    params: vec![],
                    return_type: UNIT,
                    outward_protocols: vec![0],
                    receiver_mode: Some(2),
                    register_types: vec![UNIT, UNIT],
                    code_start: body_start,
                    code_len: code.len() as u32 - body_start,
                    label_slot_count: 0,
                },
            ],
            code,
            ..Artifact::default()
        };
        artifact.required_features =
            crate::bytecode::used_features(&artifact.types, &artifact.code, true, false);
        artifact
    }

    #[test]
    fn fresh_handler_resumptions_are_terminally_discharged_and_cannot_be_forged_live() {
        let accepted = fresh_handler_resumption_artifact(false);
        verify(accepted).expect("the clause cancels its fresh optional resumption");
        assert!(matches!(
            verify(fresh_handler_resumption_artifact(true)),
            Err(VerifyError::InvalidFunction(1))
        ));
    }

    fn handler_quantity_payload_artifact(forge_alias: bool) -> Artifact {
        let mut types = Type::predefined();
        types.extend([
            Type::Resumption {
                identity_name: "effect payload quantity".into(),
                input_type: UNIT,
                output_type: UNIT,
                effect_signature: Signature {
                    params: vec![],
                    result: UNIT,
                    outward_protocols: vec![],
                },
                lower_uses: 0,
                upper_uses: Some(2),
                copy: true,
            },
            Type::Callable {
                signature: Signature {
                    params: vec![19],
                    result: UNIT,
                    outward_protocols: vec![],
                },
                capture_type: UNIT,
                receiver_mode: 2,
                identity_name: "quantity payload clause".into(),
                copy: false,
                zero_use_allowed: true,
            },
            Type::Tuple {
                fields: vec![20],
                copy: false,
            },
            Type::Handler {
                handler_def: 0,
                capture_type: 21,
                identity_name: "quantity payload handler".into(),
            },
            Type::Callable {
                signature: Signature {
                    params: vec![19],
                    result: UNIT,
                    outward_protocols: vec![0],
                },
                capture_type: UNIT,
                receiver_mode: 2,
                identity_name: "quantity payload body".into(),
                copy: false,
                zero_use_allowed: true,
            },
        ]);
        let mut code = vec![
            Instruction::MakeCallable {
                dst: 2,
                callable_type: 20,
                function: 1,
                captures: vec![],
            },
            Instruction::MakeHandler {
                dst: 3,
                handler_def: 0,
                clauses: vec![2],
            },
            Instruction::MakeCallable {
                dst: 4,
                callable_type: 23,
                function: 2,
                captures: vec![],
            },
            Instruction::Handle {
                dst: 5,
                handler: 3,
                body: 4,
                args: vec![1],
            },
            Instruction::Return { src: Some(5) },
            Instruction::Cancel {
                dst: 2,
                resumption: 1,
            },
            Instruction::Return { src: Some(2) },
        ];
        let body_start = code.len() as u32;
        if forge_alias {
            code.push(Instruction::Copy { dst: 2, src: 1 });
        }
        code.push(Instruction::Perform {
            dst: None,
            protocol: 0,
            operation: 0,
            payloads: vec![1],
        });
        let mut artifact = Artifact {
            types,
            constants: vec![],
            protocols: vec![Protocol {
                display_name: "QuantityPayload".into(),
                type_arguments: vec![],
                operations: vec![Operation {
                    name: "send".into(),
                    payload_signature: Signature {
                        params: vec![19],
                        result: UNIT,
                        outward_protocols: vec![],
                    },
                    result_type: NEVER,
                    resumption_lower: 0,
                    resumption_upper: Some(0),
                    terminal: true,
                }],
            }],
            handler_defs: vec![HandlerDef {
                result_type: UNIT,
                clauses: vec![HandlerClause {
                    protocol: 0,
                    operation: 0,
                    resumption_type: None,
                    callable_signature: Signature {
                        params: vec![19],
                        result: UNIT,
                        outward_protocols: vec![],
                    },
                }],
                partial: false,
            }],
            functions: vec![
                Function {
                    flags: 0,
                    name: "quantity_payload_caller".into(),
                    params: vec![19],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, 19, 20, 22, 23, UNIT],
                    code_start: 0,
                    code_len: 5,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "quantity_payload_clause".into(),
                    params: vec![19],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: Some(2),
                    register_types: vec![UNIT, 19, UNIT],
                    code_start: 5,
                    code_len: 2,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "quantity_payload_body".into(),
                    params: vec![19],
                    return_type: UNIT,
                    outward_protocols: vec![0],
                    receiver_mode: Some(2),
                    register_types: vec![UNIT, 19, 19],
                    code_start: body_start,
                    code_len: code.len() as u32 - body_start,
                    label_slot_count: 0,
                },
            ],
            code,
            ..Artifact::default()
        };
        artifact.required_features =
            crate::bytecode::used_features(&artifact.types, &artifact.code, true, false);
        artifact
    }

    #[test]
    fn effect_payload_keeps_one_pristine_quantity_identity_through_the_handler_clause() {
        let accepted = handler_quantity_payload_artifact(false);
        assert_eq!(
            owned_receiver_quantity_summaries(&accepted)[0],
            Some(OwnedReceiverQuantitySummary {
                outputs: vec![],
                resumes: vec![0],
                dispositions: vec![QuantityTerminalDisposition::Cancelled],
            })
        );
        let labels = verify_labels(&accepted, 0, &accepted.functions[0]).unwrap();
        let quantity = verify_resumption_quantities(&accepted, 0, &accepted.functions[0], &labels);
        assert!(quantity.is_ok(), "caller quantity: {quantity:?}");
        verify(accepted)
            .expect("the sole payload owner transfers into the cancelling clause parameter");
        assert!(matches!(
            verify(handler_quantity_payload_artifact(true)),
            Err(VerifyError::InvalidFunction(2))
        ));
    }

    #[test]
    fn terminal_clause_composes_quantity_capture_and_payload_dispositions() {
        let mut artifact = handler_quantity_payload_artifact(false);
        artifact.types.push(
            Type::Tuple {
                fields: vec![19],
                copy: true,
            }
            .restricted(true, true),
        );
        let Type::Callable { capture_type, .. } = &mut artifact.types[20] else {
            unreachable!()
        };
        *capture_type = 24;
        artifact.code = vec![
            Instruction::MakeCallable {
                dst: 3,
                callable_type: 20,
                function: 1,
                captures: vec![1],
            },
            Instruction::MakeHandler {
                dst: 4,
                handler_def: 0,
                clauses: vec![3],
            },
            Instruction::MakeCallable {
                dst: 5,
                callable_type: 23,
                function: 2,
                captures: vec![],
            },
            Instruction::Handle {
                dst: 6,
                handler: 4,
                body: 5,
                args: vec![2],
            },
            Instruction::Return { src: Some(6) },
            Instruction::ProjectMove {
                dst: 2,
                src: 0,
                field: 0,
            },
            Instruction::Deconstruct { src: 0 },
            Instruction::Cancel {
                dst: 3,
                resumption: 1,
            },
            Instruction::Cancel {
                dst: 4,
                resumption: 2,
            },
            Instruction::Return { src: Some(4) },
            Instruction::Perform {
                dst: None,
                protocol: 0,
                operation: 0,
                payloads: vec![1],
            },
        ];
        artifact.functions[0].params = vec![19, 19];
        artifact.functions[0].register_types = vec![UNIT, 19, 19, 20, 22, 23, UNIT];
        artifact.functions[0].code_len = 5;
        artifact.functions[1].register_types = vec![24, 19, 19, UNIT, UNIT];
        artifact.functions[1].code_start = 5;
        artifact.functions[1].code_len = 5;
        artifact.functions[2].code_start = 10;
        artifact.functions[2].code_len = 1;
        artifact.required_features =
            crate::bytecode::used_features(&artifact.types, &artifact.code, true, false);

        let cancelled = OwnedReceiverQuantitySummary {
            outputs: vec![],
            resumes: vec![0, 0],
            dispositions: vec![
                QuantityTerminalDisposition::Cancelled,
                QuantityTerminalDisposition::Cancelled,
            ],
        };
        assert_eq!(
            owned_receiver_quantity_summaries(&artifact)[0],
            Some(cancelled)
        );
        verify(artifact).expect("the selected clause composes its capture and payload quantities");
    }

    fn nested_forwarded_quantity_payload_artifact() -> Artifact {
        let mut artifact = handler_quantity_payload_artifact(false);
        artifact.types.extend([
            Type::Handler {
                handler_def: 1,
                capture_type: UNIT,
                identity_name: "partial forwarding handler".into(),
            },
            Type::Callable {
                signature: Signature {
                    params: vec![19],
                    result: UNIT,
                    outward_protocols: vec![0],
                },
                capture_type: UNIT,
                receiver_mode: 2,
                identity_name: "forwarded quantity payload body".into(),
                copy: false,
                zero_use_allowed: true,
            },
        ]);
        artifact.handler_defs.push(HandlerDef {
            result_type: UNIT,
            clauses: vec![],
            partial: true,
        });
        artifact.code.truncate(7);
        artifact.code.extend([
            Instruction::MakeHandler {
                dst: 2,
                handler_def: 1,
                clauses: vec![],
            },
            Instruction::MakeCallable {
                dst: 3,
                callable_type: 25,
                function: 3,
                captures: vec![],
            },
            Instruction::Handle {
                dst: 4,
                handler: 2,
                body: 3,
                args: vec![1],
            },
            Instruction::Return { src: Some(4) },
            Instruction::Perform {
                dst: None,
                protocol: 0,
                operation: 0,
                payloads: vec![1],
            },
        ]);
        artifact.functions[2].name = "quantity_payload_forwarder".into();
        artifact.functions[2].register_types = vec![UNIT, 19, 24, 25, UNIT];
        artifact.functions[2].code_start = 7;
        artifact.functions[2].code_len = 4;
        artifact.functions.push(Function {
            flags: 0,
            name: "forwarded_quantity_payload_body".into(),
            params: vec![19],
            return_type: UNIT,
            outward_protocols: vec![0],
            receiver_mode: Some(2),
            register_types: vec![UNIT, 19],
            code_start: 11,
            code_len: 1,
            label_slot_count: 0,
        });
        artifact.required_features =
            crate::bytecode::used_features(&artifact.types, &artifact.code, true, false);
        artifact
    }

    #[test]
    fn partial_nested_handler_forwards_the_same_quantity_payload_to_the_outer_clause() {
        let artifact = nested_forwarded_quantity_payload_artifact();
        assert_eq!(
            terminal_effect_payload_summaries(&artifact)[2],
            Some(TerminalEffectPayloadSummary {
                protocol: 0,
                operation: 0,
                payloads: vec![0],
                dropped: vec![],
            })
        );
        assert_eq!(
            owned_receiver_quantity_summaries(&artifact)[0],
            Some(OwnedReceiverQuantitySummary {
                outputs: vec![],
                resumes: vec![0],
                dispositions: vec![QuantityTerminalDisposition::Cancelled],
            })
        );
        verify(artifact).expect("partial forwarding preserves the sole payload quantity owner");
    }

    fn noncopy_forwarding_handler_environment_artifact(shared: bool) -> Artifact {
        let mut artifact = nested_forwarded_quantity_payload_artifact();
        artifact.types.extend([
            Type::Tuple {
                fields: vec![19],
                copy: true,
            }
            .restricted(true, true),
            Type::Callable {
                signature: Signature {
                    params: vec![],
                    result: UNIT,
                    outward_protocols: vec![],
                },
                capture_type: 26,
                receiver_mode: 2,
                identity_name: "noncopy forwarding clause".into(),
                copy: false,
                zero_use_allowed: true,
            },
            Type::Tuple {
                fields: vec![27],
                copy: false,
            },
        ]);
        let Type::Handler { capture_type, .. } = &mut artifact.types[24] else {
            unreachable!()
        };
        *capture_type = 28;
        let Type::Callable { signature, .. } = &mut artifact.types[23] else {
            unreachable!()
        };
        signature.params = vec![19, 19];
        let mut ignored = artifact.protocols[0].operations[0].clone();
        ignored.name = "handled_elsewhere".into();
        ignored.payload_signature.params.clear();
        artifact.protocols.push(Protocol {
            display_name: "ZHandledElsewhere".into(),
            type_arguments: vec![],
            operations: vec![ignored],
        });
        artifact.handler_defs[1].clauses = vec![HandlerClause {
            protocol: 1,
            operation: 0,
            resumption_type: None,
            callable_signature: Signature {
                params: vec![],
                result: UNIT,
                outward_protocols: vec![],
            },
        }];
        artifact.code = vec![
            Instruction::MakeCallable {
                dst: 3,
                callable_type: 20,
                function: 1,
                captures: vec![],
            },
            Instruction::MakeHandler {
                dst: 4,
                handler_def: 0,
                clauses: vec![3],
            },
            Instruction::MakeCallable {
                dst: 5,
                callable_type: 23,
                function: 2,
                captures: vec![],
            },
            Instruction::Handle {
                dst: 6,
                handler: 4,
                body: 5,
                args: vec![1, 2],
            },
            Instruction::Return { src: Some(6) },
            Instruction::Cancel {
                dst: 2,
                resumption: 1,
            },
            Instruction::Return { src: Some(2) },
        ];
        if shared {
            artifact.code.push(Instruction::MakeHandlerShared {
                dst: 4,
                handler_def: 1,
                functions: vec![4],
                captures: vec![1],
            });
        } else {
            artifact.code.extend([
                Instruction::MakeCallable {
                    dst: 3,
                    callable_type: 27,
                    function: 4,
                    captures: vec![1],
                },
                Instruction::MakeHandler {
                    dst: 4,
                    handler_def: 1,
                    clauses: vec![3],
                },
            ]);
        }
        artifact.code.extend([
            Instruction::MakeCallable {
                dst: 5,
                callable_type: 25,
                function: 3,
                captures: vec![],
            },
            Instruction::Handle {
                dst: 6,
                handler: 4,
                body: 5,
                args: vec![2],
            },
            Instruction::Return { src: Some(6) },
        ]);
        let body_start = artifact.code.len() as u32;
        artifact.code.push(Instruction::Perform {
            dst: None,
            protocol: 0,
            operation: 0,
            payloads: vec![1],
        });
        let clause_start = artifact.code.len() as u32;
        artifact.code.extend([
            Instruction::ProjectMove {
                dst: 1,
                src: 0,
                field: 0,
            },
            Instruction::Deconstruct { src: 0 },
            Instruction::Drop { register: 1 },
            Instruction::Return { src: None },
        ]);
        artifact.functions[0].params = vec![19, 19];
        artifact.functions[0].register_types = vec![UNIT, 19, 19, 20, 22, 23, UNIT];
        artifact.functions[0].code_start = 0;
        artifact.functions[0].code_len = 5;
        artifact.functions[1].code_start = 5;
        artifact.functions[1].code_len = 2;
        artifact.functions[2].params = vec![19, 19];
        artifact.functions[2].register_types = vec![UNIT, 19, 19, 27, 24, 25, UNIT];
        artifact.functions[2].code_start = 7;
        artifact.functions[2].code_len = body_start - 7;
        artifact.functions[3].code_start = body_start;
        artifact.functions[3].code_len = 1;
        artifact.functions.push(Function {
            flags: 0,
            name: "noncopy_forwarding_clause".into(),
            params: vec![],
            return_type: UNIT,
            outward_protocols: vec![],
            receiver_mode: Some(2),
            register_types: vec![26, 19],
            code_start: clause_start,
            code_len: 4,
            label_slot_count: 0,
        });
        artifact.required_features =
            crate::bytecode::used_features(&artifact.types, &artifact.code, true, false);
        artifact
    }

    #[test]
    fn partial_forwarding_cleans_noncopy_quantity_handler_environments_once() {
        for shared in [false, true] {
            let artifact = noncopy_forwarding_handler_environment_artifact(shared);
            assert_eq!(
                terminal_effect_payload_summaries(&artifact)[2],
                Some(TerminalEffectPayloadSummary {
                    protocol: 0,
                    operation: 0,
                    payloads: vec![1],
                    dropped: vec![0],
                })
            );
            assert_eq!(
                owned_receiver_quantity_summaries(&artifact)[0],
                Some(OwnedReceiverQuantitySummary {
                    outputs: vec![],
                    resumes: vec![0, 0],
                    dispositions: vec![
                        QuantityTerminalDisposition::Dropped,
                        QuantityTerminalDisposition::Cancelled,
                    ],
                })
            );
            verify(artifact).expect("forwarding drops one logical handler environment owner");
        }
    }

    #[test]
    fn partial_forwarding_rejects_forged_shared_aliases_and_opaque_bodies() {
        let mut forged = noncopy_forwarding_handler_environment_artifact(true);
        let Instruction::MakeHandlerShared { captures, .. } = &mut forged.code[7] else {
            unreachable!()
        };
        *captures = vec![1, 1];
        assert_eq!(terminal_effect_payload_summaries(&forged)[2], None);
        assert!(matches!(
            verify(forged),
            Err(VerifyError::InvalidFunction(2))
        ));

        let mut opaque = noncopy_forwarding_handler_environment_artifact(false);
        opaque.code.splice(
            7..12,
            [
                Instruction::MakeCallable {
                    dst: 4,
                    callable_type: 27,
                    function: 4,
                    captures: vec![1],
                },
                Instruction::MakeHandler {
                    dst: 5,
                    handler_def: 1,
                    clauses: vec![4],
                },
                Instruction::Move { dst: 6, src: 3 },
                Instruction::Handle {
                    dst: 7,
                    handler: 5,
                    body: 6,
                    args: vec![2],
                },
                Instruction::Return { src: Some(7) },
            ],
        );
        opaque.functions[2].params = vec![19, 19, 25];
        opaque.functions[2].register_types = vec![UNIT, 19, 19, 25, 27, 24, 25, UNIT];
        opaque.required_features =
            crate::bytecode::used_features(&opaque.types, &opaque.code, true, false);
        assert_eq!(terminal_effect_payload_summaries(&opaque)[2], None);
        assert_eq!(owned_receiver_quantity_summaries(&opaque)[0], None);
        assert!(matches!(
            verify(opaque),
            Err(VerifyError::InvalidFunction(2))
        ));
    }

    fn dynamically_supplied_handler_artifact() -> Artifact {
        let mut artifact = noncopy_forwarding_handler_environment_artifact(false);
        artifact.code[0..5].clone_from_slice(&[
            Instruction::MakeCallable {
                dst: 4,
                callable_type: 23,
                function: 2,
                captures: vec![],
            },
            Instruction::Handle {
                dst: 5,
                handler: 1,
                body: 4,
                args: vec![2, 3],
            },
            Instruction::Return { src: Some(5) },
            Instruction::Nop,
            Instruction::Nop,
        ]);
        artifact.functions[0].params = vec![22, 19, 19];
        artifact.functions[0].register_types = vec![UNIT, 22, 19, 19, 23, UNIT];
        let factory_start = artifact.code.len() as u32;
        artifact.code.extend([
            Instruction::MakeCallable {
                dst: 1,
                callable_type: 20,
                function: 1,
                captures: vec![],
            },
            Instruction::MakeHandler {
                dst: 2,
                handler_def: 0,
                clauses: vec![1],
            },
            Instruction::Return { src: Some(2) },
        ]);
        artifact.functions.push(Function {
            flags: 0,
            name: "dynamic_handler_factory".into(),
            params: vec![],
            return_type: 22,
            outward_protocols: vec![],
            receiver_mode: None,
            register_types: vec![UNIT, 20, 22],
            code_start: factory_start,
            code_len: 3,
            label_slot_count: 0,
        });
        artifact.required_features =
            crate::bytecode::used_features(&artifact.types, &artifact.code, true, false);
        artifact
    }

    #[test]
    fn dynamic_handler_parameters_use_closed_world_clause_summaries() {
        let artifact = dynamically_supplied_handler_artifact();
        assert_eq!(
            owned_receiver_quantity_summaries(&artifact)[0],
            Some(OwnedReceiverQuantitySummary {
                outputs: vec![],
                resumes: vec![0, 0],
                dispositions: vec![
                    QuantityTerminalDisposition::Dropped,
                    QuantityTerminalDisposition::Cancelled,
                ],
            })
        );
        verify(artifact).expect("dynamic handler clause producers are finite and canonical");
    }

    #[test]
    fn dynamic_handler_parameters_without_clause_producers_fail_closed() {
        let mut artifact = dynamically_supplied_handler_artifact();
        let factory = artifact.functions.pop().unwrap();
        artifact.code.truncate(factory.code_start as usize);
        artifact.required_features =
            crate::bytecode::used_features(&artifact.types, &artifact.code, true, false);
        assert!(callable_type_producers(&artifact, 20).is_empty());
        assert_eq!(owned_receiver_quantity_summaries(&artifact)[0], None);
        assert!(matches!(
            verify(artifact),
            Err(VerifyError::InvalidFunction(0))
        ));
    }

    fn returned_quantity_payload_artifact() -> Artifact {
        let mut artifact = handler_quantity_payload_artifact(false);
        artifact.handler_defs[0].result_type = 19;
        artifact.handler_defs[0].clauses[0]
            .callable_signature
            .result = 19;
        let Type::Callable { signature, .. } = &mut artifact.types[20] else {
            unreachable!()
        };
        signature.result = 19;
        let Type::Callable { signature, .. } = &mut artifact.types[23] else {
            unreachable!()
        };
        signature.result = 19;
        artifact.code.truncate(5);
        artifact.code.extend([
            Instruction::Return { src: Some(1) },
            Instruction::Perform {
                dst: None,
                protocol: 0,
                operation: 0,
                payloads: vec![1],
            },
        ]);
        artifact.functions[0].return_type = 19;
        artifact.functions[0].register_types[5] = 19;
        artifact.functions[1].return_type = 19;
        artifact.functions[1].code_start = 5;
        artifact.functions[1].code_len = 1;
        artifact.functions[2].return_type = 19;
        artifact.functions[2].code_start = 6;
        artifact.functions[2].code_len = 1;
        artifact.required_features =
            crate::bytecode::used_features(&artifact.types, &artifact.code, true, false);
        artifact
    }

    #[test]
    fn terminal_clause_can_return_the_exact_effect_payload_quantity_onward() {
        let artifact = returned_quantity_payload_artifact();
        assert_eq!(
            terminal_effect_payload_summaries(&artifact)[2],
            Some(TerminalEffectPayloadSummary {
                protocol: 0,
                operation: 0,
                payloads: vec![0],
                dropped: vec![],
            })
        );
        assert!(owned_receiver_quantity_summaries(&artifact)[1].is_some());
        assert_eq!(
            owned_receiver_quantity_summaries(&artifact)[0],
            Some(OwnedReceiverQuantitySummary {
                outputs: vec![0],
                resumes: vec![0],
                dispositions: vec![QuantityTerminalDisposition::Returned],
            })
        );
        let labels = verify_labels(&artifact, 0, &artifact.functions[0]).unwrap();
        let quantity = verify_resumption_quantities(&artifact, 0, &artifact.functions[0], &labels);
        assert!(quantity.is_ok(), "caller quantity: {quantity:?}");
        verify(artifact).expect("the handler result preserves the payload's exact quantity origin");
    }

    #[test]
    fn handler_clause_uses_a_converged_mutually_recursive_parameter_scc() {
        let mut artifact = returned_quantity_payload_artifact();
        artifact.code.truncate(5);
        artifact.code.extend([
            Instruction::Call {
                dst: Some(2),
                function: 3,
                args: vec![1],
            },
            Instruction::Return { src: Some(2) },
            Instruction::Perform {
                dst: None,
                protocol: 0,
                operation: 0,
                payloads: vec![1],
            },
            Instruction::TailCall {
                function: 4,
                args: vec![1],
            },
            Instruction::TailCall {
                function: 3,
                args: vec![1],
            },
        ]);
        artifact.functions[1].register_types = vec![UNIT, 19, 19];
        artifact.functions[1].code_start = 5;
        artifact.functions[1].code_len = 2;
        artifact.functions[2].code_start = 7;
        artifact.functions[2].code_len = 1;
        artifact.functions.extend([
            Function {
                flags: 0,
                name: "handler_quantity_helper_a".into(),
                params: vec![19],
                return_type: 19,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 19],
                code_start: 8,
                code_len: 1,
                label_slot_count: 0,
            },
            Function {
                flags: 0,
                name: "handler_quantity_helper_b".into(),
                params: vec![19],
                return_type: 19,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 19],
                code_start: 9,
                code_len: 1,
                label_slot_count: 0,
            },
        ]);
        artifact.required_features =
            crate::bytecode::used_features(&artifact.types, &artifact.code, true, false);
        let summaries = owned_receiver_quantity_summaries(&artifact);
        assert!(summaries[1].is_some());
        assert_eq!(summaries[3], summaries[4]);
        let labels = verify_labels(&artifact, 1, &artifact.functions[1]).unwrap();
        let quantity = verify_resumption_quantities(&artifact, 1, &artifact.functions[1], &labels);
        assert!(quantity.is_ok(), "clause quantity: {quantity:?}");
        verify(artifact).expect("the handler clause uses one converged recursive identity proof");
    }

    #[test]
    fn resumption_copy_shares_the_upper_bound_across_aliases() {
        let mut artifact = finite_multishot(2, 0, 2, 0);
        let result = 4;
        let copied = 6;
        artifact.functions[0].register_types.push(19);
        artifact.code.insert(
            0,
            Instruction::Copy {
                dst: copied,
                src: 1,
            },
        );
        artifact.code.insert(
            5,
            Instruction::Resume {
                dst: result,
                resumption: copied,
                receiver_mode: 0,
                value: 2,
            },
        );
        artifact
            .code
            .insert(6, Instruction::Drop { register: result });
        artifact
            .code
            .insert(7, Instruction::Drop { register: copied });
        artifact.functions[0].code_len = artifact.code.len() as u32;
        artifact.required_features =
            crate::bytecode::used_features(&artifact.types, &artifact.code, false, false);
        assert!(matches!(
            verify(artifact),
            Err(VerifyError::InvalidFunction(0))
        ));
    }

    #[test]
    fn copied_aliases_may_jointly_satisfy_one_lower_bound() {
        let mut artifact = finite_multishot(0, 2, 2, 0);
        artifact.functions[0].params.extend([I64, I64]);
        artifact.functions[0].register_types = vec![UNIT, 19, I64, I64, 19, I64, UNIT];
        artifact.code = vec![
            Instruction::Copy { dst: 4, src: 1 },
            Instruction::Resume {
                dst: 5,
                resumption: 1,
                receiver_mode: 2,
                value: 2,
            },
            Instruction::Drop { register: 5 },
            Instruction::Resume {
                dst: 5,
                resumption: 4,
                receiver_mode: 2,
                value: 3,
            },
            Instruction::Drop { register: 5 },
            Instruction::Const {
                dst: 6,
                constant: 0,
            },
            Instruction::Return { src: Some(6) },
        ];
        artifact.functions[0].code_len = artifact.code.len() as u32;
        assert!(verify(artifact).is_ok());
    }

    #[test]
    fn final_copied_alias_cannot_abandon_the_shared_lower_bound() {
        let mut artifact = finite_multishot(0, 1, 2, 0);
        artifact.functions[0].register_types = vec![UNIT, 19, 19, UNIT];
        artifact.code = vec![
            Instruction::Copy { dst: 2, src: 1 },
            Instruction::Drop { register: 1 },
            Instruction::Drop { register: 2 },
            Instruction::Const {
                dst: 3,
                constant: 0,
            },
            Instruction::Return { src: Some(3) },
        ];
        artifact.functions[0].code_len = artifact.code.len() as u32;
        artifact.required_features =
            crate::bytecode::used_features(&artifact.types, &artifact.code, false, false);
        let error = verify(artifact).unwrap_err();
        assert!(
            matches!(error, VerifyError::InvalidFunction(0)),
            "{error:?}"
        );
    }

    fn branched_resumption(lower: u32, upper: u32, post_join_resumes: usize) -> Artifact {
        let mut types = Type::predefined();
        types.push(Type::Resumption {
            input_type: I64,
            output_type: I64,
            effect_signature: Signature {
                params: vec![],
                result: UNIT,
                outward_protocols: vec![],
            },
            lower_uses: lower,
            upper_uses: Some(upper),
            identity_name: "branched multi".into(),
            copy: true,
        });
        let mut code = vec![
            Instruction::Switch {
                discr: 2,
                cases: vec![(1, 1)],
                otherwise: 5,
            },
            Instruction::Copy { dst: 6, src: 3 },
            Instruction::Resume {
                dst: 4,
                resumption: 1,
                receiver_mode: 0,
                value: 6,
            },
            Instruction::Drop { register: 4 },
            Instruction::Jump { target: 5 },
        ];
        for _ in 0..post_join_resumes {
            code.push(Instruction::Copy { dst: 6, src: 3 });
            code.push(Instruction::Resume {
                dst: 4,
                resumption: 1,
                receiver_mode: 0,
                value: 6,
            });
            code.push(Instruction::Drop { register: 4 });
        }
        code.extend([
            Instruction::Drop { register: 1 },
            Instruction::Const {
                dst: 5,
                constant: 0,
            },
            Instruction::Return { src: Some(5) },
        ]);
        Artifact {
            types,
            constants: vec![Constant::Unit, Constant::U32(0)],
            functions: vec![Function {
                flags: 0,
                name: "branched_resumption".into(),
                params: vec![19, U32, I64],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 19, U32, I64, I64, UNIT, I64],
                code_start: 0,
                code_len: code.len() as u32,
                label_slot_count: 0,
            }],
            code,
            required_features: 1 | (1 << 3) | (1 << 4),
            ..Artifact::default()
        }
    }

    #[test]
    fn resumption_quantity_joins_use_the_branch_hull() {
        let accepted_artifact = branched_resumption(0, 2, 0);
        let labels = verify_labels(&accepted_artifact, 0, &accepted_artifact.functions[0]).unwrap();
        let quantity = verify_resumption_quantities(
            &accepted_artifact,
            0,
            &accepted_artifact.functions[0],
            &labels,
        );
        assert!(quantity.is_ok(), "quantity: {quantity:?}");
        let accepted = verify(accepted_artifact);
        assert!(accepted.is_ok(), "{accepted:?}");
        assert!(matches!(
            verify(branched_resumption(1, 2, 0)),
            Err(VerifyError::InvalidFunction(0))
        ));
        assert!(matches!(
            verify(branched_resumption(0, 2, 2)),
            Err(VerifyError::InvalidFunction(0))
        ));
    }

    fn resumption_helper_call(preuse: bool, retain_alias: bool) -> Artifact {
        let mut types = Type::predefined();
        types.push(Type::Resumption {
            input_type: I64,
            output_type: I64,
            effect_signature: Signature {
                params: vec![],
                result: UNIT,
                outward_protocols: vec![],
            },
            lower_uses: 1,
            upper_uses: Some(2),
            identity_name: "helper-owned continuation".into(),
            copy: true,
        });
        let mut caller = Vec::new();
        if preuse {
            caller.extend([
                Instruction::Resume {
                    dst: 3,
                    resumption: 1,
                    receiver_mode: 0,
                    value: 2,
                },
                Instruction::Drop { register: 3 },
            ]);
        }
        if retain_alias {
            caller.push(Instruction::Copy { dst: 4, src: 1 });
        }
        caller.push(Instruction::Call {
            dst: None,
            function: 1,
            args: vec![1, 2],
        });
        if retain_alias {
            caller.push(Instruction::Drop { register: 4 });
        }
        caller.extend([
            Instruction::Const {
                dst: 5,
                constant: 0,
            },
            Instruction::Return { src: Some(5) },
        ]);
        let caller_len = caller.len() as u32;
        let callee = vec![
            Instruction::Resume {
                dst: 3,
                resumption: 1,
                receiver_mode: 2,
                value: 2,
            },
            Instruction::Drop { register: 3 },
            Instruction::Const {
                dst: 4,
                constant: 0,
            },
            Instruction::Return { src: Some(4) },
        ];
        let mut code = caller;
        code.extend(callee);
        Artifact {
            types,
            constants: vec![Constant::Unit],
            functions: vec![
                Function {
                    flags: 0,
                    name: "caller".into(),
                    params: vec![19, I64],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, 19, I64, I64, 19, UNIT],
                    code_start: 0,
                    code_len: caller_len,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "consume_in_helper".into(),
                    params: vec![19, I64],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, 19, I64, I64, UNIT],
                    code_start: caller_len,
                    code_len: 4,
                    label_slot_count: 0,
                },
            ],
            code,
            required_features: 1 | (1 << 3) | (1 << 4),
            ..Artifact::default()
        }
    }

    #[test]
    fn direct_call_may_take_a_pristine_sole_resumption_obligation() {
        assert!(verify(resumption_helper_call(false, false)).is_ok());
        assert!(matches!(
            verify(resumption_helper_call(true, false)),
            Err(VerifyError::InvalidFunction(0))
        ));
        assert!(matches!(
            verify(resumption_helper_call(false, true)),
            Err(VerifyError::InvalidFunction(0))
        ));
    }

    #[test]
    fn multishot_capture_rejects_a_crossing_unique_loan() {
        let mut types = Type::predefined();
        types.push(Type::RefUnique { referent: I64 });
        types.push(Type::Resumption {
            input_type: I64,
            output_type: I64,
            effect_signature: Signature {
                params: vec![],
                result: I64,
                outward_protocols: vec![],
            },
            lower_uses: 0,
            upper_uses: Some(2),
            identity_name: "loan rejecting multi".into(),
            copy: true,
        });
        let artifact = Artifact {
            types,
            protocols: vec![crate::bytecode::Protocol {
                display_name: "Loan".into(),
                type_arguments: vec![],
                operations: vec![crate::bytecode::Operation {
                    name: "suspend".into(),
                    payload_signature: Signature {
                        params: vec![],
                        result: UNIT,
                        outward_protocols: vec![],
                    },
                    result_type: I64,
                    terminal: false,
                    resumption_lower: 0,
                    resumption_upper: Some(2),
                }],
            }],
            functions: vec![Function {
                flags: 0,
                name: "bad_capture".into(),
                params: vec![19],
                return_type: I64,
                outward_protocols: vec![0],
                receiver_mode: None,
                register_types: vec![UNIT, 19, I64],
                code_start: 0,
                code_len: 3,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Perform {
                    dst: Some(2),
                    protocol: 0,
                    operation: 0,
                    payloads: vec![],
                },
                Instruction::EndBorrow { reference: 1 },
                Instruction::Return { src: Some(2) },
            ],
            required_features: 1 | (1 << 1) | (1 << 3) | (1 << 4),
            ..Artifact::default()
        };
        let mut irrelevant = artifact.clone();
        irrelevant.code.remove(1);
        irrelevant.functions[0].code_len -= 1;
        let verified = verify(irrelevant)
            .expect("a future-dead zero-use unique loan is pruned before the multishot snapshot");
        let function = verified.function(0).unwrap();
        let resume_pc = function.checked_pc(1).unwrap();
        assert_eq!(function.continuation_registers(resume_pc), &[2]);
        assert!(matches!(
            verify(artifact),
            Err(VerifyError::BorrowConflict { instruction: 0, .. })
        ));
    }

    #[test]
    fn multishot_capture_accepts_a_crossing_external_shared_loan() {
        let mut types = Type::predefined();
        types.push(Type::RefShared { referent: I64 });
        types.push(Type::Resumption {
            input_type: I64,
            output_type: I64,
            effect_signature: Signature {
                params: vec![],
                result: I64,
                outward_protocols: vec![],
            },
            lower_uses: 0,
            upper_uses: Some(2),
            identity_name: "shared-loan multi".into(),
            copy: true,
        });
        let artifact = Artifact {
            types,
            protocols: vec![crate::bytecode::Protocol {
                display_name: "Loan".into(),
                type_arguments: vec![],
                operations: vec![crate::bytecode::Operation {
                    name: "suspend".into(),
                    payload_signature: Signature {
                        params: vec![],
                        result: UNIT,
                        outward_protocols: vec![],
                    },
                    result_type: I64,
                    terminal: false,
                    resumption_lower: 0,
                    resumption_upper: Some(2),
                }],
            }],
            functions: vec![Function {
                flags: 0,
                name: "shared_capture".into(),
                params: vec![19],
                return_type: I64,
                outward_protocols: vec![0],
                receiver_mode: None,
                register_types: vec![UNIT, 19, I64],
                code_start: 0,
                code_len: 3,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Perform {
                    dst: Some(2),
                    protocol: 0,
                    operation: 0,
                    payloads: vec![],
                },
                Instruction::EndBorrow { reference: 1 },
                Instruction::Return { src: Some(2) },
            ],
            required_features: 1 | (1 << 1) | (1 << 3) | (1 << 4),
            ..Artifact::default()
        };
        assert!(verify(artifact).is_ok());
    }

    #[test]
    fn multishot_capture_accepts_an_empty_unsafe_field_in_a_residual_aggregate() {
        let mut types = Type::predefined();
        types.push(Type::RefUnique { referent: I64 });
        types.push(Type::Tuple {
            fields: vec![19, I64],
            copy: false,
        });
        types.push(Type::Resumption {
            input_type: I64,
            output_type: I64,
            effect_signature: Signature {
                params: vec![],
                result: I64,
                outward_protocols: vec![],
            },
            lower_uses: 2,
            upper_uses: Some(2),
            identity_name: "residual multi".into(),
            copy: true,
        });
        let artifact = Artifact {
            types,
            constants: vec![Constant::I64(40)],
            protocols: vec![crate::bytecode::Protocol {
                display_name: "Residual".into(),
                type_arguments: vec![],
                operations: vec![crate::bytecode::Operation {
                    name: "suspend".into(),
                    payload_signature: Signature {
                        params: vec![],
                        result: UNIT,
                        outward_protocols: vec![],
                    },
                    result_type: I64,
                    terminal: false,
                    resumption_lower: 2,
                    resumption_upper: Some(2),
                }],
            }],
            functions: vec![Function {
                flags: 0,
                name: "residual_capture".into(),
                params: vec![I64],
                return_type: I64,
                outward_protocols: vec![0],
                receiver_mode: None,
                register_types: vec![UNIT, I64, 19, I64, 20, 19, I64, I64],
                code_start: 0,
                code_len: 9,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::BorrowUnique { dst: 2, src: 1 },
                Instruction::Const {
                    dst: 3,
                    constant: 0,
                },
                Instruction::Construct {
                    dst: 4,
                    ty: 20,
                    variant: None,
                    fields: vec![2, 3],
                },
                Instruction::ProjectMove {
                    dst: 5,
                    src: 4,
                    field: 0,
                },
                Instruction::EndBorrow { reference: 5 },
                Instruction::Perform {
                    dst: Some(6),
                    protocol: 0,
                    operation: 0,
                    payloads: vec![],
                },
                Instruction::Drop { register: 6 },
                Instruction::ProjectMove {
                    dst: 7,
                    src: 4,
                    field: 1,
                },
                Instruction::Return { src: Some(7) },
            ],
            required_features: 1 | (1 << 1) | (1 << 3) | (1 << 4),
            ..Artifact::default()
        };
        let artifact = with_generated_cleanup_plans(artifact).unwrap();
        assert!(verify(artifact).is_ok());
    }

    #[test]
    fn multishot_capture_accepts_only_initialized_fields_of_a_known_enum_variant() {
        let mut types = Type::predefined();
        types.push(Type::RefUnique { referent: I64 });
        types.push(Type::Enum {
            name: "ResidualChoice".into(),
            variants: vec![EnumVariant {
                name: "Payload".into(),
                fields: vec![
                    Field {
                        name: "unsafe".into(),
                        ty: 19,
                    },
                    Field {
                        name: "safe".into(),
                        ty: I64,
                    },
                ],
            }],
            copy: false,
        });
        types.push(Type::Resumption {
            input_type: I64,
            output_type: I64,
            effect_signature: Signature {
                params: vec![],
                result: I64,
                outward_protocols: vec![],
            },
            lower_uses: 2,
            upper_uses: Some(2),
            identity_name: "enum residual multi".into(),
            copy: true,
        });
        let artifact = Artifact {
            types,
            constants: vec![Constant::I64(40)],
            protocols: vec![crate::bytecode::Protocol {
                display_name: "Residual".into(),
                type_arguments: vec![],
                operations: vec![crate::bytecode::Operation {
                    name: "suspend".into(),
                    payload_signature: Signature {
                        params: vec![],
                        result: UNIT,
                        outward_protocols: vec![],
                    },
                    result_type: I64,
                    terminal: false,
                    resumption_lower: 2,
                    resumption_upper: Some(2),
                }],
            }],
            functions: vec![Function {
                flags: 0,
                name: "enum_residual_capture".into(),
                params: vec![I64],
                return_type: I64,
                outward_protocols: vec![0],
                receiver_mode: None,
                register_types: vec![UNIT, I64, 19, I64, 20, 19, I64, I64],
                code_start: 0,
                code_len: 9,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::BorrowUnique { dst: 2, src: 1 },
                Instruction::Const {
                    dst: 3,
                    constant: 0,
                },
                Instruction::Construct {
                    dst: 4,
                    ty: 20,
                    variant: Some(0),
                    fields: vec![2, 3],
                },
                Instruction::ProjectMove {
                    dst: 5,
                    src: 4,
                    field: 0,
                },
                Instruction::EndBorrow { reference: 5 },
                Instruction::Perform {
                    dst: Some(6),
                    protocol: 0,
                    operation: 0,
                    payloads: vec![],
                },
                Instruction::Drop { register: 6 },
                Instruction::ProjectMove {
                    dst: 7,
                    src: 4,
                    field: 1,
                },
                Instruction::Return { src: Some(7) },
            ],
            required_features: 1 | (1 << 1) | (1 << 3) | (1 << 4),
            ..Artifact::default()
        };
        let artifact = with_generated_cleanup_plans(artifact).unwrap();
        assert!(verify(artifact).is_ok());
    }

    #[test]
    fn multishot_capture_rejects_an_array_without_safe_slot_residual_evidence() {
        let mut types = Type::predefined();
        types.push(Type::RefUnique { referent: I64 });
        types.push(Type::Array { element: 19 });
        types.push(Type::Resumption {
            input_type: I64,
            output_type: I64,
            effect_signature: Signature {
                params: vec![],
                result: I64,
                outward_protocols: vec![],
            },
            lower_uses: 2,
            upper_uses: Some(2),
            identity_name: "array residual multi".into(),
            copy: true,
        });
        let artifact = Artifact {
            types,
            protocols: vec![crate::bytecode::Protocol {
                display_name: "Residual".into(),
                type_arguments: vec![],
                operations: vec![crate::bytecode::Operation {
                    name: "suspend".into(),
                    payload_signature: Signature {
                        params: vec![],
                        result: UNIT,
                        outward_protocols: vec![],
                    },
                    result_type: I64,
                    terminal: false,
                    resumption_lower: 2,
                    resumption_upper: Some(2),
                }],
            }],
            functions: vec![Function {
                flags: 0,
                name: "unproved_array_residual".into(),
                params: vec![20],
                return_type: I64,
                outward_protocols: vec![0],
                receiver_mode: None,
                register_types: vec![UNIT, 20, I64],
                code_start: 0,
                code_len: 3,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Perform {
                    dst: Some(2),
                    protocol: 0,
                    operation: 0,
                    payloads: vec![],
                },
                Instruction::Drop { register: 1 },
                Instruction::Return { src: Some(2) },
            ],
            required_features: 1 | (1 << 1) | (1 << 3) | (1 << 4),
            ..Artifact::default()
        };
        assert!(matches!(
            with_generated_cleanup_plans(artifact),
            Err(VerifyError::IllegalCopy {
                function: 0,
                instruction: 0,
                ty: 20,
            })
        ));
    }

    #[test]
    fn cleanup_metadata_is_mandatory_complete_and_exact() {
        let artifact = base(
            vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::Return { src: Some(1) },
            ],
            vec![UNIT, I64],
        );
        assert!(matches!(
            super::verify(artifact.clone()),
            Err(VerifyError::InvalidFunction(0))
        ));

        let canonical = with_generated_cleanup_plans(artifact).unwrap();
        assert!(super::verify(canonical.clone()).is_ok());

        let mut missing = canonical.clone();
        missing.cleanups.pop();
        assert!(matches!(
            super::verify(missing),
            Err(VerifyError::InvalidFunction(0))
        ));

        let mut wrong_membership = canonical;
        wrong_membership.cleanups[1].registers.clear();
        assert!(matches!(
            super::verify(wrong_membership),
            Err(VerifyError::StateMismatch {
                function: 0,
                instruction: 1
            })
        ));
    }

    #[test]
    fn cleanup_order_follows_newest_owner_first_for_custom_drop_values() {
        let mut types = Type::predefined();
        types.push(
            Type::Struct {
                name: "ObservedDrop".into(),
                fields: vec![],
                copy: false,
            }
            .restricted(false, true),
        );
        types.push(Type::RefUnique { referent: 19 });
        let artifact = Artifact {
            required_features: 1 | (1 << 1),
            types,
            drop_glue: vec![crate::bytecode::DropGlue {
                ty: 19,
                function: 0,
            }],
            functions: vec![
                Function {
                    flags: DROP_HOOK,
                    name: "observe_drop".into(),
                    params: vec![20],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, 20],
                    code_start: 0,
                    code_len: 2,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "drop_two".into(),
                    params: vec![19, 19],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, 19, 19],
                    code_start: 2,
                    code_len: 3,
                    label_slot_count: 0,
                },
            ],
            code: vec![
                Instruction::EndBorrow { reference: 1 },
                Instruction::Return { src: None },
                Instruction::Drop { register: 2 },
                Instruction::Drop { register: 1 },
                Instruction::Return { src: None },
            ],
            ..Artifact::default()
        };
        let mut artifact = with_generated_cleanup_plans(artifact).unwrap();
        let plan = artifact
            .cleanups
            .iter_mut()
            .find(|plan| plan.function == 1 && plan.first_instruction == 0)
            .unwrap();
        assert_eq!(plan.registers, [2, 1]);
        plan.registers.swap(0, 1);
        assert!(matches!(
            super::verify(artifact),
            Err(VerifyError::StateMismatch {
                function: 1,
                instruction: 0
            })
        ));
    }

    fn shell_age_artifact(
        register_types: Vec<TypeId>,
        params: Vec<TypeId>,
        constants: Vec<Constant>,
        code: Vec<Instruction>,
    ) -> Artifact {
        let mut types = Type::predefined();
        types.push(
            Type::Tuple {
                fields: vec![I64],
                copy: false,
            }
            .restricted(false, true),
        );
        types.push(
            Type::Tuple {
                fields: vec![],
                copy: false,
            }
            .restricted(false, true),
        );
        Artifact {
            types,
            constants,
            functions: vec![Function {
                flags: 0,
                name: "shell_age".into(),
                params,
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types,
                code_start: 0,
                code_len: code.len() as u32,
                label_slot_count: 0,
            }],
            code,
            required_features: 1,
            ..Artifact::default()
        }
    }

    #[test]
    fn reconstructing_the_same_shell_restores_its_cleanup_position() {
        let artifact = shell_age_artifact(
            vec![UNIT, 19, 19, I64],
            vec![19, 19],
            vec![],
            vec![
                Instruction::ProjectMove {
                    dst: 3,
                    src: 1,
                    field: 0,
                },
                Instruction::Deconstruct { src: 1 },
                Instruction::Construct {
                    dst: 1,
                    ty: 19,
                    variant: None,
                    fields: vec![3],
                },
                Instruction::Nop,
                Instruction::Drop { register: 2 },
                Instruction::Drop { register: 1 },
                Instruction::Return { src: None },
            ],
        );

        let canonical = with_generated_cleanup_plans(artifact).unwrap();
        assert_eq!(cleanup_registers(&canonical, 0, 3), [2, 1]);
        assert!(super::verify(canonical).is_ok());
    }

    #[test]
    fn reconstructing_into_a_different_register_creates_a_newest_owner() {
        let artifact = shell_age_artifact(
            vec![UNIT, 19, 19, I64, 19],
            vec![19, 19],
            vec![],
            vec![
                Instruction::ProjectMove {
                    dst: 3,
                    src: 1,
                    field: 0,
                },
                Instruction::Deconstruct { src: 1 },
                Instruction::Construct {
                    dst: 4,
                    ty: 19,
                    variant: None,
                    fields: vec![3],
                },
                Instruction::Nop,
                Instruction::Drop { register: 4 },
                Instruction::Drop { register: 2 },
                Instruction::Return { src: None },
            ],
        );

        let canonical = with_generated_cleanup_plans(artifact).unwrap();
        assert_eq!(cleanup_registers(&canonical, 0, 3), [4, 2]);
        assert!(super::verify(canonical).is_ok());
    }

    #[test]
    fn conflicting_shell_age_hints_meet_to_unknown_without_forging_age() {
        let artifact = shell_age_artifact(
            vec![UNIT, 20, 20, U32, 20],
            vec![20, 20, U32],
            vec![Constant::U32(0)],
            vec![
                Instruction::Switch {
                    discr: 3,
                    cases: vec![(0, 1)],
                    otherwise: 3,
                },
                Instruction::Deconstruct { src: 1 },
                Instruction::Jump { target: 5 },
                Instruction::Move { dst: 4, src: 1 },
                Instruction::Drop { register: 4 },
                Instruction::Construct {
                    dst: 1,
                    ty: 20,
                    variant: None,
                    fields: vec![],
                },
                Instruction::Nop,
                Instruction::Drop { register: 1 },
                Instruction::Drop { register: 3 },
                Instruction::Drop { register: 2 },
                Instruction::Return { src: None },
            ],
        );

        let canonical = with_generated_cleanup_plans(artifact).unwrap();
        // The conflicting Some(old position) / None hints meet to unknown, so
        // the reconstructed owner is newest rather than regaining r1's age.
        assert_eq!(cleanup_registers(&canonical, 0, 6), [1, 3, 2]);
        assert!(super::verify(canonical).is_ok());
    }

    fn two_shared_reference_types() -> Vec<Type> {
        let mut types = Type::predefined();
        types.push(Type::RefShared { referent: I64 });
        types.push(Type::Tuple {
            fields: vec![19, 19],
            copy: true,
        });
        types.push(Type::RefUnique { referent: I64 });
        types
    }

    #[test]
    fn two_shared_origins_survive_construct_projection_and_deconstruction() {
        let code = vec![
            Instruction::BorrowShared { dst: 3, src: 1 },
            Instruction::BorrowShared { dst: 4, src: 2 },
            Instruction::Construct {
                dst: 5,
                ty: 20,
                variant: None,
                fields: vec![3, 4],
            },
            Instruction::ProjectMove {
                dst: 6,
                src: 5,
                field: 0,
            },
            Instruction::ProjectMove {
                dst: 7,
                src: 5,
                field: 1,
            },
            Instruction::Deconstruct { src: 5 },
            Instruction::EndBorrow { reference: 7 },
            Instruction::EndBorrow { reference: 6 },
            Instruction::Return { src: None },
        ];
        let artifact = Artifact {
            types: two_shared_reference_types(),
            functions: vec![Function {
                flags: 0,
                name: "two_shared_local".into(),
                params: vec![I64, I64],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, I64, I64, 19, 19, 20, 19, 19],
                code_start: 0,
                code_len: code.len() as u32,
                label_slot_count: 0,
            }],
            code,
            required_features: 1 | (1 << 1),
            ..Artifact::default()
        };
        verify(artifact).expect("two independent shared leaves remain individually tracked");
    }

    #[test]
    fn dropping_both_projected_leaves_ends_both_carried_loans() {
        let code = vec![
            Instruction::BorrowShared { dst: 3, src: 1 },
            Instruction::BorrowShared { dst: 4, src: 2 },
            Instruction::Construct {
                dst: 5,
                ty: 20,
                variant: None,
                fields: vec![3, 4],
            },
            Instruction::ProjectMove {
                dst: 6,
                src: 5,
                field: 0,
            },
            Instruction::ProjectMove {
                dst: 7,
                src: 5,
                field: 1,
            },
            Instruction::Deconstruct { src: 5 },
            Instruction::Drop { register: 6 },
            Instruction::Drop { register: 7 },
            Instruction::BorrowUnique { dst: 8, src: 1 },
            Instruction::EndBorrow { reference: 8 },
            Instruction::BorrowUnique { dst: 9, src: 2 },
            Instruction::EndBorrow { reference: 9 },
            Instruction::Return { src: None },
        ];
        let artifact = Artifact {
            types: two_shared_reference_types(),
            functions: vec![Function {
                flags: 0,
                name: "drop_two_shared".into(),
                params: vec![I64, I64],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, I64, I64, 19, 19, 20, 19, 19, 21, 21],
                code_start: 0,
                code_len: code.len() as u32,
                label_slot_count: 0,
            }],
            code,
            required_features: 1 | (1 << 1),
            ..Artifact::default()
        };
        verify(artifact).expect("dropping projected leaves releases every stored shared loan");
    }

    #[test]
    fn direct_call_transports_two_shared_result_origins_by_leaf() {
        let caller = vec![
            Instruction::BorrowShared { dst: 3, src: 1 },
            Instruction::BorrowShared { dst: 4, src: 2 },
            Instruction::Call {
                dst: Some(5),
                function: 1,
                args: vec![3, 4],
            },
            Instruction::ProjectMove {
                dst: 6,
                src: 5,
                field: 0,
            },
            Instruction::ProjectMove {
                dst: 7,
                src: 5,
                field: 1,
            },
            Instruction::Deconstruct { src: 5 },
            Instruction::EndBorrow { reference: 7 },
            Instruction::EndBorrow { reference: 6 },
            Instruction::Return { src: None },
        ];
        let callee = vec![
            Instruction::Construct {
                dst: 3,
                ty: 20,
                variant: None,
                fields: vec![1, 2],
            },
            Instruction::Return { src: Some(3) },
        ];
        let mut code = caller.clone();
        code.extend(callee.clone());
        let artifact = Artifact {
            types: two_shared_reference_types(),
            functions: vec![
                Function {
                    flags: 0,
                    name: "caller".into(),
                    params: vec![I64, I64],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, I64, I64, 19, 19, 20, 19, 19],
                    code_start: 0,
                    code_len: caller.len() as u32,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "pair_refs".into(),
                    params: vec![19, 19],
                    return_type: 20,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, 19, 19, 20],
                    code_start: caller.len() as u32,
                    code_len: callee.len() as u32,
                    label_slot_count: 0,
                },
            ],
            code,
            required_features: 1 | (1 << 1),
            ..Artifact::default()
        };
        verify(artifact)
            .expect("direct return provenance maps every result leaf to its argument leaf");
    }

    fn indirect_two_reference_artifact() -> Artifact {
        let mut types = two_shared_reference_types();
        types.push(Type::Callable {
            signature: Signature {
                params: vec![19, 19],
                result: 20,
                outward_protocols: vec![],
            },
            capture_type: UNIT,
            receiver_mode: 2,
            identity_name: "pair reference callable".into(),
            copy: true,
            zero_use_allowed: true,
        });
        let caller = vec![
            Instruction::BorrowShared { dst: 3, src: 1 },
            Instruction::BorrowShared { dst: 4, src: 2 },
            Instruction::MakeCallable {
                dst: 5,
                callable_type: 22,
                function: 1,
                captures: vec![],
            },
            Instruction::CallIndirect {
                dst: Some(6),
                callable: 5,
                receiver_mode: 2,
                args: vec![3, 4],
            },
            Instruction::ProjectMove {
                dst: 7,
                src: 6,
                field: 0,
            },
            Instruction::ProjectMove {
                dst: 8,
                src: 6,
                field: 1,
            },
            Instruction::Deconstruct { src: 6 },
            Instruction::EndBorrow { reference: 8 },
            Instruction::EndBorrow { reference: 7 },
            Instruction::BorrowUnique { dst: 9, src: 1 },
            Instruction::EndBorrow { reference: 9 },
            Instruction::BorrowUnique { dst: 10, src: 2 },
            Instruction::EndBorrow { reference: 10 },
            Instruction::Return { src: None },
        ];
        let callee = vec![
            Instruction::Construct {
                dst: 3,
                ty: 20,
                variant: None,
                fields: vec![1, 2],
            },
            Instruction::Drop { register: 0 },
            Instruction::Return { src: Some(3) },
        ];
        let mut code = caller.clone();
        code.extend(callee.clone());
        Artifact {
            types,
            functions: vec![
                Function {
                    flags: 0,
                    name: "indirect_pair_caller".into(),
                    params: vec![I64, I64],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, I64, I64, 19, 19, 22, 20, 19, 19, 21, 21],
                    code_start: 0,
                    code_len: caller.len() as u32,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "indirect_pair_target".into(),
                    params: vec![19, 19],
                    return_type: 20,
                    outward_protocols: vec![],
                    receiver_mode: Some(2),
                    register_types: vec![UNIT, 19, 19, 20],
                    code_start: caller.len() as u32,
                    code_len: callee.len() as u32,
                    label_slot_count: 0,
                },
            ],
            code,
            required_features: 1 | (1 << 1),
            ..Artifact::default()
        }
    }

    #[test]
    fn exact_indirect_target_transports_two_reference_origins_by_leaf() {
        let artifact = verify(indirect_two_reference_artifact())
            .expect("an exact callable producer supplies a body-checked leaf contract");
        assert_eq!(
            crate::vm::Vm::new(artifact)
                .run(0, vec![crate::Value::I64(11), crate::Value::I64(22)])
                .unwrap(),
            crate::Value::Unit
        );
    }

    #[test]
    fn indirect_multi_origin_result_rejects_a_forged_or_unknown_callable_target() {
        let mut artifact = indirect_two_reference_artifact();
        artifact.code = vec![
            Instruction::CallIndirect {
                dst: Some(4),
                callable: 1,
                receiver_mode: 2,
                args: vec![2, 3],
            },
            Instruction::Return { src: Some(4) },
            Instruction::Construct {
                dst: 3,
                ty: 20,
                variant: None,
                fields: vec![1, 2],
            },
            Instruction::Drop { register: 0 },
            Instruction::Return { src: Some(3) },
        ];
        artifact.functions[0] = Function {
            flags: 0,
            name: "unknown_indirect_pair".into(),
            params: vec![22, 19, 19],
            return_type: 20,
            outward_protocols: vec![],
            receiver_mode: None,
            register_types: vec![UNIT, 22, 19, 19, 20],
            code_start: 0,
            code_len: 2,
            label_slot_count: 0,
        };
        artifact.functions[1].code_start = 2;
        assert_eq!(
            verify(artifact).expect_err("a callable signature alone cannot forge a leaf contract"),
            VerifyError::InvalidFunction(0)
        );
    }

    fn externally_supplied_multi_reference_artifact(disagree: bool) -> Artifact {
        let mut artifact = indirect_two_reference_artifact();
        artifact.code = vec![
            Instruction::CallIndirect {
                dst: Some(4),
                callable: 1,
                receiver_mode: 2,
                args: vec![2, 3],
            },
            Instruction::Return { src: Some(4) },
            Instruction::Construct {
                dst: 3,
                ty: 20,
                variant: None,
                fields: vec![1, 2],
            },
            Instruction::Drop { register: 0 },
            Instruction::Return { src: Some(3) },
        ];
        artifact.functions[0] = Function {
            flags: 0,
            name: "external_indirect_pair".into(),
            params: vec![22, 19, 19],
            return_type: 20,
            outward_protocols: vec![],
            receiver_mode: None,
            register_types: vec![UNIT, 22, 19, 19, 20],
            code_start: 0,
            code_len: 2,
            label_slot_count: 0,
        };
        artifact.functions[1].code_start = 2;
        if disagree {
            artifact.code.extend([
                Instruction::Construct {
                    dst: 3,
                    ty: 20,
                    variant: None,
                    fields: vec![2, 1],
                },
                Instruction::Drop { register: 0 },
                Instruction::Return { src: Some(3) },
            ]);
            artifact.functions.push(Function {
                flags: 0,
                name: "external_indirect_pair_swapped".into(),
                params: vec![19, 19],
                return_type: 20,
                outward_protocols: vec![],
                receiver_mode: Some(2),
                register_types: vec![UNIT, 19, 19, 20],
                code_start: 5,
                code_len: 3,
                label_slot_count: 0,
            });
        }
        let targets = if disagree { vec![1, 2] } else { vec![1] };
        for target in targets {
            let start = artifact.code.len() as u32;
            artifact.code.extend([
                Instruction::MakeCallable {
                    dst: 1,
                    callable_type: 22,
                    function: target,
                    captures: vec![],
                },
                Instruction::Return { src: Some(1) },
            ]);
            artifact.functions.push(Function {
                flags: 0,
                name: format!("external_pair_factory_{target}"),
                params: vec![],
                return_type: 22,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 22],
                code_start: start,
                code_len: 2,
                label_slot_count: 0,
            });
        }
        artifact.required_features =
            crate::bytecode::used_features(&artifact.types, &artifact.code, false, false);
        artifact
    }

    #[test]
    fn external_indirect_multi_leaf_results_use_canonical_finite_producers() {
        verify(externally_supplied_multi_reference_artifact(false))
            .expect("a dynamic callable parameter uses its sealed producer leaf contract");
    }

    #[test]
    fn external_indirect_multi_leaf_results_reject_divergent_producers() {
        assert_eq!(
            verify(externally_supplied_multi_reference_artifact(true))
                .expect_err("finite producers must agree on every returned leaf"),
            VerifyError::InvalidFunction(0)
        );
    }

    #[test]
    fn indirect_multi_leaf_results_preserve_callable_capture_origins() {
        let mut types = two_shared_reference_types();
        types.push(Type::Callable {
            signature: Signature {
                params: vec![],
                result: 20,
                outward_protocols: vec![],
            },
            capture_type: 20,
            receiver_mode: 2,
            identity_name: "captured reference pair".into(),
            copy: true,
            zero_use_allowed: false,
        });
        let artifact = Artifact {
            types,
            functions: vec![
                Function {
                    flags: 0,
                    name: "external_capture_consumer".into(),
                    params: vec![22],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, 22, 20, 19, 19],
                    code_start: 0,
                    code_len: 7,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "capture_pair_target".into(),
                    params: vec![],
                    return_type: 20,
                    outward_protocols: vec![],
                    receiver_mode: Some(2),
                    register_types: vec![20, 20],
                    code_start: 7,
                    code_len: 2,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "capture_pair_factory".into(),
                    params: vec![19, 19],
                    return_type: 22,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, 19, 19, 22],
                    code_start: 9,
                    code_len: 2,
                    label_slot_count: 0,
                },
            ],
            code: vec![
                Instruction::CallIndirect {
                    dst: Some(2),
                    callable: 1,
                    receiver_mode: 2,
                    args: vec![],
                },
                Instruction::ProjectMove {
                    dst: 3,
                    src: 2,
                    field: 0,
                },
                Instruction::ProjectMove {
                    dst: 4,
                    src: 2,
                    field: 1,
                },
                Instruction::Deconstruct { src: 2 },
                Instruction::EndBorrow { reference: 4 },
                Instruction::EndBorrow { reference: 3 },
                Instruction::Return { src: None },
                Instruction::Move { dst: 1, src: 0 },
                Instruction::Return { src: Some(1) },
                Instruction::MakeCallable {
                    dst: 3,
                    callable_type: 22,
                    function: 1,
                    captures: vec![1, 2],
                },
                Instruction::Return { src: Some(3) },
            ],
            required_features: 1 | (1 << 1),
            ..Artifact::default()
        };
        assert_eq!(
            aggregate_reference_return_origins(&artifact, 1, &mut vec![]).unwrap(),
            vec![
                (vec![0], CarrierOrigin::Receiver { path: vec![0] },),
                (vec![1], CarrierOrigin::Receiver { path: vec![1] },),
            ]
        );
        verify(artifact).expect("indirect results remain rooted in callable capture leaves");
    }

    fn branched_indirect_reference_artifact(disagree: bool) -> Artifact {
        let mut types = two_shared_reference_types();
        types.push(Type::Callable {
            signature: Signature {
                params: vec![19, 19],
                result: 20,
                outward_protocols: vec![],
            },
            capture_type: UNIT,
            receiver_mode: 2,
            identity_name: "branched pair reference callable".into(),
            copy: true,
            zero_use_allowed: true,
        });
        let caller = vec![
            Instruction::BorrowShared { dst: 4, src: 1 },
            Instruction::BorrowShared { dst: 5, src: 2 },
            Instruction::Switch {
                discr: 3,
                cases: vec![(0, 3)],
                otherwise: 5,
            },
            Instruction::MakeCallable {
                dst: 6,
                callable_type: 22,
                function: 1,
                captures: vec![],
            },
            Instruction::Jump { target: 6 },
            Instruction::MakeCallable {
                dst: 6,
                callable_type: 22,
                function: 2,
                captures: vec![],
            },
            Instruction::CallIndirect {
                dst: Some(7),
                callable: 6,
                receiver_mode: 2,
                args: vec![4, 5],
            },
            Instruction::ProjectMove {
                dst: 8,
                src: 7,
                field: 0,
            },
            Instruction::ProjectMove {
                dst: 9,
                src: 7,
                field: 1,
            },
            Instruction::Deconstruct { src: 7 },
            Instruction::EndBorrow { reference: 9 },
            Instruction::EndBorrow { reference: 8 },
            Instruction::Return { src: None },
        ];
        let target = |swapped| {
            vec![
                Instruction::Construct {
                    dst: 3,
                    ty: 20,
                    variant: None,
                    fields: if swapped { vec![2, 1] } else { vec![1, 2] },
                },
                Instruction::Drop { register: 0 },
                Instruction::Return { src: Some(3) },
            ]
        };
        let first = target(false);
        let second = target(disagree);
        let mut code = caller.clone();
        code.extend(first.clone());
        code.extend(second.clone());
        Artifact {
            types,
            constants: vec![Constant::U32(0)],
            functions: vec![
                Function {
                    flags: 0,
                    name: "branched_indirect_caller".into(),
                    params: vec![I64, I64, U32],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, I64, I64, U32, 19, 19, 22, 20, 19, 19],
                    code_start: 0,
                    code_len: caller.len() as u32,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "first_pair_target".into(),
                    params: vec![19, 19],
                    return_type: 20,
                    outward_protocols: vec![],
                    receiver_mode: Some(2),
                    register_types: vec![UNIT, 19, 19, 20],
                    code_start: caller.len() as u32,
                    code_len: first.len() as u32,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "second_pair_target".into(),
                    params: vec![19, 19],
                    return_type: 20,
                    outward_protocols: vec![],
                    receiver_mode: Some(2),
                    register_types: vec![UNIT, 19, 19, 20],
                    code_start: (caller.len() + first.len()) as u32,
                    code_len: second.len() as u32,
                    label_slot_count: 0,
                },
            ],
            code,
            required_features: 1 | (1 << 1),
            ..Artifact::default()
        }
    }

    #[test]
    fn branched_indirect_targets_share_one_canonical_reference_contract() {
        verify(branched_indirect_reference_artifact(false))
            .expect("all dynamic alternatives transport the same reference leaves");
    }

    #[test]
    fn branched_indirect_targets_reject_disagreeing_reference_contracts() {
        assert_eq!(
            verify(branched_indirect_reference_artifact(true))
                .expect_err("dynamic alternatives cannot disagree about reference provenance"),
            VerifyError::InvalidFunction(0)
        );
    }

    #[test]
    fn recursive_effect_summaries_converge_across_a_cycle() {
        let artifact = Artifact {
            types: Type::predefined(),
            protocols: vec![Protocol {
                display_name: "Optional".into(),
                type_arguments: vec![],
                operations: vec![Operation {
                    name: "maybe".into(),
                    payload_signature: Signature {
                        params: vec![],
                        result: UNIT,
                        outward_protocols: vec![],
                    },
                    result_type: UNIT,
                    resumption_lower: 0,
                    resumption_upper: Some(1),
                    terminal: false,
                }],
            }],
            functions: vec![
                Function {
                    flags: 0,
                    name: "cycle_entry".into(),
                    params: vec![],
                    return_type: UNIT,
                    outward_protocols: vec![0],
                    receiver_mode: None,
                    register_types: vec![UNIT],
                    code_start: 0,
                    code_len: 1,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "cycle_effect".into(),
                    params: vec![],
                    return_type: UNIT,
                    outward_protocols: vec![0],
                    receiver_mode: None,
                    register_types: vec![UNIT],
                    code_start: 1,
                    code_len: 2,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "pure_cycle".into(),
                    params: vec![],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT],
                    code_start: 3,
                    code_len: 1,
                    label_slot_count: 0,
                },
            ],
            code: vec![
                Instruction::TailCall {
                    function: 1,
                    args: vec![],
                },
                Instruction::Call {
                    dst: None,
                    function: 0,
                    args: vec![],
                },
                Instruction::Perform {
                    dst: None,
                    protocol: 0,
                    operation: 0,
                    payloads: vec![],
                },
                Instruction::TailCall {
                    function: 2,
                    args: vec![],
                },
            ],
            ..Artifact::default()
        };
        assert!(function_body_may_cancel(&artifact, 0));
        assert!(function_body_may_cancel(&artifact, 1));
        assert!(!function_body_may_cancel(&artifact, 2));
    }

    fn recursive_pair_artifact(swapped_base: bool) -> Artifact {
        let mut code = vec![Instruction::Switch {
            discr: 2,
            cases: vec![(0, 1)],
            otherwise: if swapped_base { 7 } else { 2 },
        }];
        if swapped_base {
            code.extend([
                Instruction::ProjectMove {
                    dst: 3,
                    src: 1,
                    field: 0,
                },
                Instruction::ProjectMove {
                    dst: 4,
                    src: 1,
                    field: 1,
                },
                Instruction::Deconstruct { src: 1 },
                Instruction::Construct {
                    dst: 5,
                    ty: 20,
                    variant: None,
                    fields: vec![4, 3],
                },
                Instruction::Drop { register: 2 },
                Instruction::Return { src: Some(5) },
            ]);
        } else {
            code.push(Instruction::Return { src: Some(1) });
        }
        let recursive = code.len() as u32;
        if swapped_base {
            let Instruction::Switch { otherwise, .. } = &mut code[0] else {
                unreachable!()
            };
            *otherwise = recursive;
        }
        code.extend([
            Instruction::Call {
                dst: Some(6),
                function: 0,
                args: vec![1, 2],
            },
            Instruction::Return { src: Some(6) },
        ]);
        Artifact {
            types: two_shared_reference_types(),
            constants: vec![Constant::U32(0)],
            functions: vec![Function {
                flags: 0,
                name: "recursive_pair".into(),
                params: vec![20, U32],
                return_type: 20,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 20, U32, 19, 19, 20, 20],
                code_start: 0,
                code_len: code.len() as u32,
                label_slot_count: 0,
            }],
            code,
            required_features: 1 | (1 << 1),
            ..Artifact::default()
        }
    }

    #[test]
    fn recursive_aggregate_reference_summary_uses_its_unique_structural_contract() {
        verify(recursive_pair_artifact(false))
            .expect("recursive aggregate identity keeps both parameter leaf origins");
    }

    #[test]
    fn recursive_aggregate_reference_summary_rejects_a_swapped_base_contract() {
        assert!(matches!(
            verify(recursive_pair_artifact(true)),
            Err(VerifyError::InvalidFunction(0))
        ));
    }

    fn mutually_recursive_multi_reference_artifact(diverge: bool) -> Artifact {
        let code = vec![
            Instruction::Switch {
                discr: 3,
                cases: vec![(0, 1)],
                otherwise: 3,
            },
            Instruction::Construct {
                dst: 4,
                ty: 20,
                variant: None,
                fields: vec![1, 2],
            },
            Instruction::Return { src: Some(4) },
            Instruction::Call {
                dst: Some(5),
                function: 1,
                args: vec![1, 2, 3],
            },
            Instruction::Return { src: Some(5) },
            Instruction::TailCall {
                function: 0,
                args: if diverge {
                    vec![2, 1, 3]
                } else {
                    vec![1, 2, 3]
                },
            },
        ];
        Artifact {
            types: two_shared_reference_types(),
            constants: vec![Constant::U32(0)],
            functions: vec![
                Function {
                    flags: 0,
                    name: "mutual_reference_a".into(),
                    params: vec![19, 19, U32],
                    return_type: 20,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, 19, 19, U32, 20, 20],
                    code_start: 0,
                    code_len: 5,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "mutual_reference_b".into(),
                    params: vec![19, 19, U32],
                    return_type: 20,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, 19, 19, U32],
                    code_start: 5,
                    code_len: 1,
                    label_slot_count: 0,
                },
            ],
            code,
            required_features: 1 | (1 << 1),
            ..Artifact::default()
        }
    }

    #[test]
    fn mutually_recursive_reference_scc_converges_on_multiple_leaf_mappings() {
        let artifact = mutually_recursive_multi_reference_artifact(false);
        assert_eq!(
            aggregate_reference_return_origins(&artifact, 0, &mut vec![]).unwrap(),
            vec![
                (
                    vec![0],
                    CarrierOrigin::Parameter {
                        parameter: 0,
                        path: vec![],
                    },
                ),
                (
                    vec![1],
                    CarrierOrigin::Parameter {
                        parameter: 1,
                        path: vec![],
                    },
                ),
            ]
        );
        verify(artifact).expect("the mutual SCC has one exact multi-leaf fixed point");
    }

    #[test]
    fn mutually_recursive_reference_scc_rejects_divergent_leaf_mappings() {
        assert!(matches!(
            verify(mutually_recursive_multi_reference_artifact(true)),
            Err(VerifyError::InvalidFunction(0)) | Err(VerifyError::InvalidFunction(1))
        ));
    }

    #[test]
    fn direct_call_transports_one_selected_leaf_from_an_aggregate_argument() {
        let caller = vec![
            Instruction::BorrowShared { dst: 3, src: 1 },
            Instruction::BorrowShared { dst: 4, src: 2 },
            Instruction::Construct {
                dst: 5,
                ty: 20,
                variant: None,
                fields: vec![3, 4],
            },
            Instruction::Call {
                dst: Some(6),
                function: 1,
                args: vec![5],
            },
            Instruction::EndBorrow { reference: 6 },
            Instruction::BorrowUnique { dst: 7, src: 1 },
            Instruction::EndBorrow { reference: 7 },
            Instruction::BorrowUnique { dst: 8, src: 2 },
            Instruction::EndBorrow { reference: 8 },
            Instruction::Return { src: None },
        ];
        let callee = vec![
            Instruction::ProjectMove {
                dst: 2,
                src: 1,
                field: 0,
            },
            Instruction::Drop { register: 1 },
            Instruction::Return { src: Some(2) },
        ];
        let mut code = caller.clone();
        code.extend(callee.clone());
        let artifact = Artifact {
            types: two_shared_reference_types(),
            functions: vec![
                Function {
                    flags: 0,
                    name: "selected_leaf_caller".into(),
                    params: vec![I64, I64],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, I64, I64, 19, 19, 20, 19, 21, 21],
                    code_start: 0,
                    code_len: caller.len() as u32,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "select_first_leaf".into(),
                    params: vec![20],
                    return_type: 19,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, 20, 19],
                    code_start: caller.len() as u32,
                    code_len: callee.len() as u32,
                    label_slot_count: 0,
                },
            ],
            code,
            required_features: 1 | (1 << 1),
            ..Artifact::default()
        };
        verify(artifact).expect("the returned scalar loan follows the selected aggregate leaf");
    }

    #[test]
    fn control_dependent_aggregate_leaf_selection_is_rejected() {
        let artifact = Artifact {
            types: two_shared_reference_types(),
            constants: vec![Constant::U32(0)],
            functions: vec![Function {
                flags: 0,
                name: "choose_leaf".into(),
                params: vec![U32, 20],
                return_type: 19,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, U32, 20, 19, 19],
                code_start: 0,
                code_len: 7,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Switch {
                    discr: 1,
                    cases: vec![(0, 1)],
                    otherwise: 4,
                },
                Instruction::ProjectMove {
                    dst: 3,
                    src: 2,
                    field: 0,
                },
                Instruction::Drop { register: 2 },
                Instruction::Return { src: Some(3) },
                Instruction::ProjectMove {
                    dst: 4,
                    src: 2,
                    field: 1,
                },
                Instruction::Drop { register: 2 },
                Instruction::Return { src: Some(4) },
            ],
            required_features: 1 | (1 << 1),
            ..Artifact::default()
        };
        assert_eq!(
            verify(artifact).expect_err("different returned leaves must be rejected"),
            VerifyError::InvalidFunction(0)
        );
    }

    fn reference_array_transport_artifact(dynamic_index: bool) -> Artifact {
        let mut types = Type::predefined();
        types.push(Type::RefShared { referent: I64 });
        types.push(Type::Array { element: 19 });
        types.push(Type::RefUnique { referent: 20 });
        let register_types = vec![UNIT, I64, USIZE, 20, 19, 21, UNIT, 21, 19];
        let mut code = vec![
            Instruction::Primitive {
                dst: 3,
                op: Primitive::ArrayEmpty,
                args: vec![],
            },
            Instruction::BorrowShared { dst: 4, src: 1 },
            Instruction::BorrowUnique { dst: 5, src: 3 },
            Instruction::Primitive {
                dst: 6,
                op: Primitive::ArrayPushMove,
                args: vec![5, 4],
            },
            Instruction::Drop { register: 6 },
            Instruction::BorrowUnique { dst: 7, src: 3 },
        ];
        code.push(Instruction::Primitive {
            dst: 8,
            op: if dynamic_index {
                Primitive::ArrayGetMove
            } else {
                Primitive::ArrayPopMove
            },
            args: if dynamic_index { vec![7, 2] } else { vec![7] },
        });
        code.extend([
            Instruction::EndBorrow { reference: 8 },
            Instruction::Primitive {
                dst: 6,
                op: Primitive::ArrayFinishDrained,
                args: vec![3],
            },
            Instruction::Return { src: Some(6) },
        ]);
        Artifact {
            types,
            functions: vec![Function {
                flags: 0,
                name: "reference_array_transport".into(),
                params: vec![I64, USIZE],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types,
                code_start: 0,
                code_len: code.len() as u32,
                label_slot_count: 0,
            }],
            code,
            required_features: 1 | (1 << 1) | (1 << 7),
            ..Artifact::default()
        }
    }

    #[test]
    fn array_push_and_pop_preserve_a_reference_loan() {
        verify(reference_array_transport_artifact(false))
            .expect("an exact pushed reference origin must survive a matching pop");
    }

    #[test]
    fn dynamic_array_reference_move_fails_closed() {
        let error = verify(reference_array_transport_artifact(true)).unwrap_err();
        assert!(
            matches!(error, VerifyError::BorrowConflict { function: 0, .. }),
            "{error:?}"
        );
    }

    #[test]
    fn exact_array_wrapper_exports_reference_slot_provenance() {
        let mut types = Type::predefined();
        types.push(Type::RefShared { referent: I64 });
        types.push(Type::Array { element: 19 });
        types.push(Type::RefUnique { referent: 20 });
        let artifact = Artifact {
            types,
            constants: vec![Constant::Usize(0)],
            functions: vec![Function {
                flags: 0,
                name: "take_zero_reference".into(),
                params: vec![21],
                return_type: 19,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, 21, 21, 19],
                code_start: 0,
                code_len: 3,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Move { dst: 2, src: 1 },
                Instruction::Primitive {
                    dst: 3,
                    op: Primitive::ArrayPopMove,
                    args: vec![2],
                },
                Instruction::Return { src: Some(3) },
            ],
            required_features: 1 | (1 << 1),
            ..Artifact::default()
        };
        assert_eq!(
            aggregate_reference_return_origins(&artifact, 0, &mut vec![]).unwrap(),
            vec![(
                vec![],
                CarrierOrigin::Parameter {
                    parameter: 0,
                    path: vec![ARRAY_SLOT_PATH, ARRAY_SLOT_PATH],
                },
            )]
        );
        verify(artifact).expect("the exact trusted wrapper contract must verify");
    }

    #[test]
    fn cross_call_push_then_read_wrapper_preserves_the_installed_reference_loan() {
        let mut types = Type::predefined();
        types.push(Type::RefShared { referent: I64 });
        types.push(Type::Array { element: 19 });
        types.push(Type::RefUnique { referent: 20 });
        types.push(Type::RefUnique { referent: I64 });
        let caller = vec![
            Instruction::Primitive {
                dst: 2,
                op: Primitive::ArrayEmpty,
                args: vec![],
            },
            Instruction::BorrowShared { dst: 3, src: 1 },
            Instruction::BorrowUnique { dst: 4, src: 2 },
            Instruction::Call {
                dst: Some(5),
                function: 1,
                args: vec![4, 3],
            },
            Instruction::BorrowUnique { dst: 6, src: 2 },
            Instruction::Call {
                dst: Some(7),
                function: 2,
                args: vec![6],
            },
            Instruction::EndBorrow { reference: 7 },
            Instruction::BorrowUnique { dst: 8, src: 1 },
            Instruction::EndBorrow { reference: 8 },
            Instruction::Primitive {
                dst: 9,
                op: Primitive::ArrayFinishDrained,
                args: vec![2],
            },
            Instruction::Return { src: Some(9) },
        ];
        let writer = vec![
            Instruction::Primitive {
                dst: 3,
                op: Primitive::ArrayPushMove,
                args: vec![1, 2],
            },
            Instruction::Return { src: Some(3) },
        ];
        let reader = vec![
            Instruction::Primitive {
                dst: 2,
                op: Primitive::ArrayPopMove,
                args: vec![1],
            },
            Instruction::Return { src: Some(2) },
        ];
        let writer_start = caller.len() as u32;
        let reader_start = writer_start + writer.len() as u32;
        let mut code = caller;
        code.extend(writer);
        code.extend(reader);
        let artifact = Artifact {
            types,
            functions: vec![
                Function {
                    flags: 0,
                    name: "caller".into(),
                    params: vec![I64],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, I64, 20, 19, 21, UNIT, 21, 19, 22, UNIT],
                    code_start: 0,
                    code_len: writer_start,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "push_reference".into(),
                    params: vec![21, 19],
                    return_type: UNIT,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, 21, 19, UNIT],
                    code_start: writer_start,
                    code_len: 2,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "pop_reference".into(),
                    params: vec![21],
                    return_type: 19,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, 21, 19],
                    code_start: reader_start,
                    code_len: 2,
                    label_slot_count: 0,
                },
            ],
            code,
            required_features: 1 | (1 << 1) | (1 << 7),
            ..Artifact::default()
        };
        verify(artifact).expect("the write summary must feed the exact read summary");
    }

    #[test]
    fn resumed_quantity_is_finalized_before_a_quantity_free_direct_tail_call() {
        let mut types = Type::predefined();
        types.push(Type::Resumption {
            input_type: I64,
            output_type: I64,
            effect_signature: Signature {
                params: vec![],
                result: I64,
                outward_protocols: vec![],
            },
            lower_uses: 1,
            upper_uses: Some(1),
            identity_name: "tail-after-resume".into(),
            copy: false,
        });
        let artifact = Artifact {
            types,
            constants: vec![Constant::I64(40)],
            functions: vec![
                Function {
                    flags: 0,
                    name: "clause".into(),
                    params: vec![19],
                    return_type: I64,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, 19, 19, I64, I64],
                    code_start: 0,
                    code_len: 4,
                    label_slot_count: 0,
                },
                Function {
                    flags: 0,
                    name: "sink".into(),
                    params: vec![I64],
                    return_type: I64,
                    outward_protocols: vec![],
                    receiver_mode: None,
                    register_types: vec![UNIT, I64],
                    code_start: 4,
                    code_len: 1,
                    label_slot_count: 0,
                },
            ],
            code: vec![
                Instruction::Move { dst: 2, src: 1 },
                Instruction::Const {
                    dst: 3,
                    constant: 0,
                },
                Instruction::Resume {
                    dst: 4,
                    resumption: 2,
                    receiver_mode: 2,
                    value: 3,
                },
                Instruction::TailCall {
                    function: 1,
                    args: vec![4],
                },
                Instruction::Return { src: Some(1) },
            ],
            required_features: 1 | (1 << 3),
            ..Artifact::default()
        };
        assert_eq!(
            owned_receiver_quantity_summaries(&artifact)[0],
            Some(OwnedReceiverQuantitySummary {
                outputs: vec![],
                resumes: vec![1],
                dispositions: vec![QuantityTerminalDisposition::Resumed],
            })
        );
        verify(artifact).expect("a quantity-free tail call must preserve the completed resume");
    }
}
