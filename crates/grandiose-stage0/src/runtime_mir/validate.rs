use super::control::*;
use super::*;
use crate::mir::{
    validate_instruction_semantic_types, validate_mir_type, validate_nominal_copy_descriptors,
};
impl RuntimeMir {
    pub fn validate(&self) -> Result<(), String> {
        self.validate_with_specialized_lifted_targets(&BTreeSet::new())
    }

    /// Validate a function that belongs to a whole-program product. Only
    /// `MirProgram` can admit a non-source lifted target, after deriving it
    /// from a registered concrete instance.
    pub(crate) fn validate_with_specialized_lifted_targets(
        &self,
        specialized_lifted_targets: &BTreeSet<DefKey>,
    ) -> Result<(), String> {
        if self.entry.0 as usize >= self.blocks.len() {
            return Err(format!("MIR entry block {} is absent", self.entry.0));
        }
        if self.control.tombstoned_blocks.contains(&self.entry) {
            return Err("MIR entry block is tombstoned".into());
        }
        for &block_id in &self.control.tombstoned_blocks {
            let block = self
                .blocks
                .get(block_id.0 as usize)
                .ok_or_else(|| format!("MIR tombstoned block {} is absent", block_id.0))?;
            if !block.parameters.is_empty()
                || !block.instructions.is_empty()
                || !matches!(block.terminator, RuntimeTerminator::Unreachable)
            {
                return Err(format!(
                    "MIR tombstoned block {} remains executable",
                    block_id.0
                ));
            }
        }
        validate_nominal_copy_descriptors(&self.nominal_copy_descriptors)
            .map_err(|message| format!("nominal copy descriptors: {message}"))?;
        self.validate_move_path_tables()?;
        self.control
            .source_storage
            .validate(&self.control.move_paths)?;
        self.control
            .source_storage
            .validate_local_mapping(&self.control.move_paths, self.locals.len())?;
        if let Some(owners) = &self.control.cleanup_owners {
            let captures = self
                .parameters
                .iter()
                .take(self.captures as usize)
                .collect::<BTreeSet<_>>();
            let mut seen = BTreeSet::new();
            for owner in owners {
                self.local_type(*owner)?;
                if captures.contains(owner) || !seen.insert(*owner) {
                    return Err("cleanup owner inventory duplicates an owner or includes an environment capture".into());
                }
            }
        }
        let ordered = self.control.cleanup_owners.clone().unwrap_or_else(|| {
            self.parameters
                .iter()
                .skip(self.captures as usize)
                .rev()
                .copied()
                .collect()
        });
        let mut remaining = ordered.into_iter();
        for action in &self.control.frame_cleanup {
            self.local_type(action.owner)?;
            if !remaining.any(|owner| owner == action.owner) {
                return Err("frame cleanup is not an ordered subset of its owning bindings".into());
            }
        }
        validate_mir_type(&self.result, &mut vec![])
            .map_err(|message| format!("result {:?}: {message}", self.result))?;
        crate::specialized_mir::closed_type(&self.result).map_err(|error| error.0)?;
        for (index, local) in self.locals.iter().enumerate() {
            crate::specialized_mir::closed_type(&local.ty).map_err(|error| error.0)?;
            validate_mir_type(&local.ty, &mut vec![])
                .map_err(|message| format!("local {index} ({:?}): {message}", local.ty))?;
        }
        for (index, block) in self.blocks.iter().enumerate() {
            self.validate_scope(block.scope)?;
            for &parameter in &block.parameters {
                self.local_type(parameter)?;
            }
            for instruction in &block.instructions {
                for local in references(instruction) {
                    self.local_type(local)?;
                }
                self.validate_instruction(instruction, specialized_lifted_targets)?;
                validate_instruction_semantic_types(&instruction.to_backend()).map_err(
                    |message| format!("block {index} instruction {instruction:?}: {message}"),
                )?;
            }
            self.validate_terminator(index, &block.terminator)?;
        }
        self.validate_label_contracts()?;
        self.validate_control_tables()?;
        self.validate_local_storage_liveness()?;
        if self.frame != self.derive_frame()? {
            return Err("Runtime frame ABI or transfer inventory is not exact".into());
        }
        Ok(())
    }
    /// Validate the explicit compact-MIR storage state before any VM emission.
    /// Parameters and block parameters enter initialized; every other local
    /// starts dead and becomes readable only after a defining instruction on
    /// every reachable predecessor. This is the register representation of
    /// source `StorageLive` plus initialization, and rejects forged local
    /// reads even when no PlaceFlow sidecar was supplied.
    fn validate_local_storage_liveness(&self) -> Result<(), String> {
        // Locals and storage bindings are validated as dense body-local IDs
        // before this pass.  Bit vectors therefore encode the same must-live
        // sets as BTreeSet while making predecessor intersection, worklist
        // cloning, and membership checks linear over compact dense storage.
        let local_count = self.locals.len();
        let binding_count = self.control.source_storage.binding_locals.len();
        let mut entries = vec![None::<Vec<bool>>; self.blocks.len()];
        let mut storage_entries = vec![None::<Vec<bool>>; self.blocks.len()];
        let mut entry_live = vec![false; local_count];
        for parameter in &self.parameters {
            entry_live[parameter.0 as usize] = true;
        }
        entries[self.entry.0 as usize] = Some(entry_live);
        storage_entries[self.entry.0 as usize] = Some(vec![false; binding_count]);
        let mut binding_by_local = vec![None; local_count];
        for (binding, local) in self
            .control
            .source_storage
            .binding_locals
            .iter()
            .enumerate()
        {
            if let Some(local) = local {
                binding_by_local[local.0 as usize] = Some(binding);
            }
        }
        let intersect_liveness = |current: &mut Vec<bool>, incoming: &[bool]| {
            let mut changed = false;
            for (current, incoming) in current.iter_mut().zip(incoming) {
                let next = *current && *incoming;
                changed |= *current != next;
                *current = next;
            }
            changed
        };
        let mut worklist = VecDeque::from([self.entry.0 as usize]);
        while let Some(index) = worklist.pop_front() {
            let Some(mut live) = entries[index].clone() else {
                continue;
            };
            let Some(mut storage_live) = storage_entries[index].clone() else {
                continue;
            };
            let block = &self.blocks[index];
            for parameter in &block.parameters {
                live[parameter.0 as usize] = true;
            }
            let mut unique_loans = BTreeMap::<MirLocal, MirLocal>::new();
            let mut aborts = false;
            let mut dynamic_entries = Vec::new();
            for instruction in &block.instructions {
                let destination = destination(instruction);
                let mut inputs = references(instruction);
                // A label instruction names a destination block parameter;
                // that payload local is defined on the nonlocal target, not
                // read while the label capability is installed. Likewise
                // handler payload destinations are definitions supplied by
                // dynamic dispatch, never eager reads at installation.
                match instruction {
                    RuntimeOperation::MakeLabel { destination, .. } => {
                        inputs.retain(|local| local != destination);
                    }
                    RuntimeOperation::InstallHandler { .. } => inputs.clear(),
                    RuntimeOperation::StorageLive { .. } => inputs.clear(),
                    RuntimeOperation::StorageDead { .. } => inputs.clear(),
                    RuntimeOperation::SetDropFlag { flag, .. } => {
                        inputs.retain(|local| local != flag);
                    }
                    RuntimeOperation::DestroyIf { local, .. } => {
                        inputs.retain(|candidate| candidate != local);
                    }
                    RuntimeOperation::IsInitialized { .. } => inputs.clear(),
                    _ => {}
                }
                for local in inputs {
                    if Some(local) != destination && !live[local.0 as usize] {
                        return Err(format!(
                            "MIR reads dead/uninitialized local {} before source-storage initialization",
                            local.0
                        ));
                    }
                }
                // Dynamic clauses and lexical label targets are executable
                // entries too, even when no ordinary CFG edge reaches them.
                // Their lexical environment is captured at installation;
                // dispatch defines the explicit payload destinations.
                match instruction {
                    RuntimeOperation::InstallHandler { target, payload_destinations, clause_owned, .. } => {
                        let mut entry_live = live.clone();
                        for root in clause_owned { entry_live[root.0 as usize] = false; }
                        for payload in payload_destinations {
                            entry_live[payload.0 as usize] = true;
                        }
                        dynamic_entries.push((*target, entry_live, storage_live.clone()));
                    }
                    RuntimeOperation::MakeLabel { target, destination, .. } => {
                        let mut entry_live = live.clone();
                        entry_live[destination.0 as usize] = true;
                        dynamic_entries.push((*target, entry_live, storage_live.clone()));
                    }
                    _ => {}
                }
                if let RuntimeOperation::Store { dst, .. } = instruction {
                    let binding = binding_by_local[dst.0 as usize];
                    // Captures are ABI parameters of a lifted callable. A
                    // unique capture is addressable through that sealed
                    // environment parameter, but it is not a new lexical
                    // source owner in the child body and therefore has no
                    // child-local StorageLive binding to manufacture.
                    let Some(binding) = binding else {
                        if self.parameters.contains(dst) {
                            continue;
                        }
                        return Err(
                            "MIR Store targets a local without frozen addressable source storage"
                                .into(),
                        );
                    };
                    // A lifted capture or invocation argument is an
                    // addressable child binding whose storage is initialized
                    // by the callable ABI. It has an exact mapping but no
                    // child-local `StorageLive`; ordinary lexical owners
                    // still require the explicit transition.
                    if !storage_live[binding] && !self.parameters.contains(dst) {
                        return Err("MIR Store targets source storage before StorageLive".into());
                    }
                    if live[dst.0 as usize] {
                        return Err(
                            "MIR Store replaces initialized source storage without prior zero-use destroy"
                                .into(),
                        );
                    }
                    if unique_loans.values().any(|borrowed| borrowed == dst) {
                        return Err(
                            "MIR replaces addressable source storage while a unique loan is live"
                                .into(),
                        );
                    }
                }
                if let RuntimeOperation::Borrow {
                    dst,
                    src,
                    unique: true,
                    ..
                } = instruction
                {
                    unique_loans.insert(*dst, *src);
                }
                let mut outgoing = BTreeSet::new();
                for argument in protocol::consumed_carriers(instruction) {
                    if Some(*argument) == destination || !outgoing.insert(*argument) {
                        return Err("Runtime transfer aliases a consumed argument carrier".into());
                    }
                    live[argument.0 as usize] = false;
                    unique_loans.remove(argument);
                }
                match instruction {
                    RuntimeOperation::StorageLive { binding, local } => {
                        if storage_live[binding.0 as usize] {
                            return Err(format!(
                                "MIR starts source storage for binding {} more than once on one path",
                                binding.0
                            ));
                        }
                        if live[local.0 as usize] {
                            return Err(format!(
                                "MIR StorageLive local {} is already initialized",
                                local.0
                            ));
                        }
                        storage_live[binding.0 as usize] = true;
                    }
                    RuntimeOperation::StorageDead { binding, local } => {
                        if !std::mem::replace(&mut storage_live[binding.0 as usize], false) {
                            return Err(format!(
                                "MIR ends source storage for inactive binding {}",
                                binding.0
                            ));
                        }
                        if live[local.0 as usize] {
                            return Err(format!(
                                "MIR StorageDead local {} is still initialized",
                                local.0
                            ));
                        }
                        if unique_loans.values().any(|borrowed| borrowed == local) {
                            return Err(
                                "MIR ends addressable source storage while a unique loan is live"
                                    .into(),
                            );
                        }
                    }
                    RuntimeOperation::DestroyIf { local, .. } => {
                        live[local.0 as usize] = false;
                    }
                    RuntimeOperation::Move { src, .. }
                    | RuntimeOperation::DestroyCallable { value: src, .. } => {
                        live[src.0 as usize] = false;
                    }
                    _ => {}
                }
                if let Some(destination) = destination {
                    live[destination.0 as usize] = true;
                }
                // `Abort` terminates the worker immediately.  The compact
                // MIR form deliberately retains the enclosing block
                // terminator for structural compatibility, but that
                // terminator and any following instructions are unreachable
                // at runtime and must not demand an initialized result of
                // the never-returning primitive.
                if matches!(instruction, RuntimeOperation::Abort) {
                    aborts = true;
                    break;
                }
            }
            for (target, edge_live, edge_storage) in dynamic_entries {
                let target_index = target.0 as usize;
                if target_index >= entries.len() {
                    return Err(format!("MIR dynamic edge targets absent block {}", target.0));
                }
                let changed_locals = match &mut entries[target_index] {
                    Some(current) => intersect_liveness(current, &edge_live),
                    slot => { *slot = Some(edge_live); true }
                };
                let changed_storage = match &mut storage_entries[target_index] {
                    Some(current) => intersect_liveness(current, &edge_storage),
                    slot => { *slot = Some(edge_storage); true }
                };
                if changed_locals || changed_storage {
                    worklist.push_back(target_index);
                }
            }
            if aborts {
                continue;
            }
            let mut check_edge = |target: MirBlockId,
                                  arguments: &[MirLocal],
                                  initialized: Option<MirLocal>|
             -> Result<(), String> {
                let mut edge_live = live.clone();
                if let Some(local) = initialized {
                    edge_live[local.0 as usize] = true;
                }
                for local in arguments {
                    if !edge_live[local.0 as usize] {
                        return Err(format!(
                            "MIR edge reads dead/uninitialized local {} before source-storage initialization",
                            local.0
                        ));
                    }
                }
                let target_index = target.0 as usize;
                if target_index >= entries.len() {
                    return Err(format!("MIR edge targets absent block {}", target.0));
                }
                let changed_locals = match &mut entries[target_index] {
                    Some(current) => intersect_liveness(current, &edge_live),
                    slot => {
                        *slot = Some(edge_live.clone());
                        true
                    }
                };
                let changed_storage = match &mut storage_entries[target_index] {
                    Some(current) => intersect_liveness(current, &storage_live),
                    slot => {
                        *slot = Some(storage_live.clone());
                        true
                    }
                };
                if changed_locals || changed_storage {
                    worklist.push_back(target_index);
                }
                Ok(())
            };
            match &block.terminator {
                RuntimeTerminator::Goto { target, arguments }
                | RuntimeTerminator::Leave {
                    target, arguments, ..
                } => check_edge(*target, arguments, None)?,
                RuntimeTerminator::SwitchBool {
                    condition,
                    then_target,
                    then_arguments,
                    else_target,
                    else_arguments,
                } => {
                    if !live[condition.0 as usize] {
                        return Err(format!(
                            "MIR switch reads dead/uninitialized local {} before source-storage initialization",
                            condition.0
                        ));
                    }
                    let initialized = match block.instructions.last() {
                        Some(RuntimeOperation::IsInitialized { dst, base, .. })
                            if dst == condition =>
                        {
                            Some(*base)
                        }
                        _ => None,
                    };
                    check_edge(*then_target, then_arguments, initialized)?;
                    check_edge(*else_target, else_arguments, None)?;
                }
                RuntimeTerminator::Return { value } => {
                    if !live[value.0 as usize] {
                        return Err(format!(
                            "MIR return reads dead/uninitialized local {} before source-storage initialization",
                            value.0
                        ));
                    }
                }
                RuntimeTerminator::TailCall { arguments, .. } => {
                    if arguments.iter().any(|value| !live[value.0 as usize]) {
                        return Err("mandatory tail transfer reads a dead/uninitialized carrier".into());
                    }
                }
                RuntimeTerminator::Unreachable => {}
            }
        }
        Ok(())
    }
    fn validate_move_path_tables(&self) -> Result<(), String> {
        let tables = &self.control.move_paths;
        let mut origins = BTreeSet::new();
        for (index, binding) in tables.bindings.iter().enumerate() {
            if binding.source.0 as usize != index {
                return Err(format!(
                    "MIR move binding {index} has a non-dense PlaceFlow source identity"
                ));
            }
            if binding.spelling.is_empty() {
                return Err(format!("MIR move binding {index} has an empty spelling"));
            }
            if !origins.insert(binding.origin.clone()) {
                return Err("MIR move binding table repeats typed-core provenance".into());
            }
        }
        let mut roots = BTreeSet::new();
        let mut children = BTreeSet::new();
        for (index, path) in tables.paths.iter().enumerate() {
            if path.binding.0 as usize >= tables.bindings.len() {
                return Err(format!(
                    "MIR move path {index} references absent binding {}",
                    path.binding.0
                ));
            }
            match (path.parent, path.field) {
                (None, None) => {
                    if !roots.insert(path.binding) {
                        return Err("MIR move-path table repeats a binding root".into());
                    }
                }
                (Some(parent), Some(field)) => {
                    if parent.0 as usize >= index {
                        return Err(format!(
                            "MIR move path {index} has a non-ancestral parent {}",
                            parent.0
                        ));
                    }
                    let parent = tables.paths.get(parent.0 as usize).ok_or_else(|| {
                        format!(
                            "MIR move path {index} references absent parent {}",
                            parent.0
                        )
                    })?;
                    if parent.binding != path.binding {
                        return Err("MIR move path changes binding across a parent edge".into());
                    }
                    if !children.insert((path.parent, path.binding, field)) {
                        return Err("MIR move-path table repeats a projected child".into());
                    }
                }
                (None, Some(_)) => {
                    return Err(format!("MIR move path {index} is a root with a field"));
                }
                (Some(_), None) => {
                    return Err(format!("MIR move path {index} is a child without a field"));
                }
            }
        }
        Ok(())
    }
    fn validate_scope(&self, scope: MirScopeId) -> Result<(), String> {
        if scope.0 as usize >= self.control.scopes.len() {
            return Err(format!("MIR block references absent scope {}", scope.0));
        }
        Ok(())
    }
    fn validate_control_tables(&self) -> Result<(), String> {
        let Some(root) = self.control.scopes.first() else {
            return Err("MIR control table has no root scope".into());
        };
        if root.parent.is_some() {
            return Err("MIR root scope has a parent".into());
        }
        for (index, scope) in self.control.scopes.iter().enumerate().skip(1) {
            let Some(parent) = scope.parent else {
                return Err(format!("MIR non-root scope {index} has no parent"));
            };
            if parent.0 as usize >= index {
                return Err(format!("MIR scope {index} has a non-ancestral parent"));
            }
            if let Some(label) = scope.entered_label {
                self.control
                    .labels
                    .get(label.0 as usize)
                    .ok_or_else(|| format!("MIR scope {index} enters absent label {}", label.0))?;
            }
            if let Some(handler) = scope.entered_handler {
                self.control
                    .handlers
                    .get(handler.0 as usize)
                    .ok_or_else(|| {
                        format!("MIR scope {index} enters absent handler {}", handler.0)
                    })?;
            }
        }
        for (index, perform) in self.control.performs.iter().enumerate() {
            let mut seen = BTreeSet::new();
            for candidate in &perform.handler_candidates {
                if !seen.insert(*candidate) {
                    return Err(format!(
                        "MIR perform site {index} has non-canonical handler candidates"
                    ));
                }
                // IDs follow block allocation, not lexical nesting. The
                // instruction check below verifies exact innermost-first
                // scope order independently of those incidental numbers.
                let handler = self
                    .control
                    .handlers
                    .get(candidate.0 as usize)
                    .ok_or_else(|| {
                        format!(
                            "MIR perform site {index} references absent handler candidate {}",
                            candidate.0
                        )
                    })?;
                if handler.effect != perform.effect
                    || handler.effect_arguments != perform.effect_arguments
                    || handler.operation != perform.operation
                {
                    return Err(format!(
                        "MIR perform site {index} has an incompatible handler candidate {}",
                        candidate.0
                    ));
                }
            }
        }
        for (index, label) in self.control.labels.iter().enumerate() {
            if self.control.tombstoned_blocks.contains(&label.destination) {
                return Err(format!("MIR label {index} targets a tombstoned block"));
            }
        }
        for (index, handler) in self.control.handlers.iter().enumerate() {
            if self.control.tombstoned_blocks.contains(&handler.block)
                || self.control.tombstoned_blocks.contains(&handler.target)
            {
                return Err(format!("MIR handler {index} targets a tombstoned block"));
            }
        }
        for (index, perform) in self.control.performs.iter().enumerate() {
            if self.control.tombstoned_blocks.contains(&perform.block) {
                return Err(format!("MIR perform {index} is in a tombstoned block"));
            }
        }
        for (index, resumption) in self.control.resumptions.iter().enumerate() {
            if self.control.tombstoned_blocks.contains(&resumption.block) {
                return Err(format!("MIR resumption {index} is in a tombstoned block"));
            }
        }
        for (&block, _) in &self.control.leave_handler_prefixes {
            if self.control.tombstoned_blocks.contains(&block) {
                return Err(format!(
                    "MIR leave-handler depth names tombstoned block {}",
                    block.0
                ));
            }
            let block_data = self
                .blocks
                .get(block.0 as usize)
                .ok_or_else(|| format!("MIR leave-handler depth names absent block {}", block.0))?;
            if !matches!(block_data.terminator, RuntimeTerminator::Leave { .. }) {
                return Err(format!(
                    "MIR leave-handler depth names block {} without a leave terminator",
                    block.0
                ));
            }
        }
        for (index, block) in self.blocks.iter().enumerate() {
            if matches!(block.terminator, RuntimeTerminator::Leave { .. })
                && !self.control.leave_handler_prefixes.contains_key(&MirBlockId(index as u32)) {
                return Err("Runtime leave has no retained-handler contract".into());
            }
        }
        for (index, resumption) in self.control.resumptions.iter().enumerate() {
            let Some(handler) = resumption.originating_handler else {
                continue;
            };
            let handler = self
                .control
                .handlers
                .get(handler.0 as usize)
                .ok_or_else(|| {
                    format!(
                        "MIR resumption site {index} references absent originating handler {}",
                        handler.0
                    )
                })?;
            if handler.target != resumption.block {
                return Err(format!(
                    "MIR resumption site {index} is outside its originating handler body"
                ));
            }
        }
        let mut seen_labels = vec![false; self.control.labels.len()];
        let mut seen_handlers = vec![false; self.control.handlers.len()];
        let mut seen_performs = vec![false; self.control.performs.len()];
        let mut seen_resumptions = vec![false; self.control.resumptions.len()];
        for (block_index, block) in self.blocks.iter().enumerate() {
            let block_id = MirBlockId(block_index as u32);
            let mut scope = block.scope;
            for instruction in &block.instructions {
                match instruction {
                    RuntimeOperation::MakeLabel {
                        label,
                        brand,
                        target,
                        ..
                    } => {
                        let entry = self.control.labels.get(label.0 as usize).ok_or_else(|| {
                            format!("MIR label instruction references absent label {}", label.0)
                        })?;
                        if entry.brand != *brand
                            || entry.destination != *target
                            || !scope_enters_label(&self.control, entry.scope, scope, *label)
                        {
                            return Err(
                                "MIR label instruction disagrees with frozen control table".into(),
                            );
                        }
                        if std::mem::replace(&mut seen_labels[label.0 as usize], true)
                            && !entry.call_destination
                        {
                            return Err("MIR non-call label has multiple materializations".into());
                        }
                        scope = entry.scope;
                    }
                    RuntimeOperation::InstallHandler {
                        site,
                        effect,
                        effect_arguments,
                        operation,
                        target,
                        resume_type,
                        continuation,
                        ..
                    } => {
                        let entry =
                            self.control.handlers.get(site.0 as usize).ok_or_else(|| {
                                format!(
                                    "MIR handler instruction references absent handler {}",
                                    site.0
                                )
                            })?;
                        if entry.block != block_id
                            || !scope_enters_handler(&self.control, entry.scope, scope, *site)
                            || entry.effect != *effect
                            || entry.effect_arguments != *effect_arguments
                            || entry.operation != *operation
                            || entry.target != *target
                            || entry.resume_type != *resume_type
                            || entry.continuation != *continuation
                        {
                            return Err(
                                "MIR handler instruction disagrees with frozen control table"
                                    .into(),
                            );
                        }
                        if std::mem::replace(&mut seen_handlers[site.0 as usize], true) {
                            return Err("MIR handler site is wired more than once".into());
                        }
                        scope = entry.scope;
                    }
                    RuntimeOperation::Perform {
                        site,
                        effect,
                        effect_arguments,
                        operation,
                        ..
                    } => {
                        let entry =
                            self.control.performs.get(site.0 as usize).ok_or_else(|| {
                                format!(
                                    "MIR perform instruction references absent perform {}",
                                    site.0
                                )
                            })?;
                        if entry.block != block_id
                            || entry.scope != scope
                            || entry.effect != *effect
                            || entry.effect_arguments != *effect_arguments
                            || entry.operation != *operation
                        {
                            return Err(
                                "MIR perform instruction disagrees with frozen control table"
                                    .into(),
                            );
                        }
                        if entry.handler_candidates
                            != lexical_handler_candidates(
                                &self.control,
                                scope,
                                *effect,
                                effect_arguments,
                                *operation,
                            )
                        {
                            return Err(
                                "MIR perform site disagrees with lexical handler candidates".into(),
                            );
                        }
                        if std::mem::replace(&mut seen_performs[site.0 as usize], true) {
                            return Err("MIR perform site is wired more than once".into());
                        }
                    }
                    RuntimeOperation::UninstallHandler => {
                        scope = scope_after_uninstall(&self.control, scope).ok_or_else(|| {
                            "MIR uninstall handler escapes the lexical scope tree".to_owned()
                        })?;
                    }
                    instruction @ (RuntimeOperation::CaptureResumption { site, .. }
                    | RuntimeOperation::Resume { site, .. }
                    | RuntimeOperation::ResumeReturn { site, .. }
                    | RuntimeOperation::ResumeSnapshot { site, .. }
                    | RuntimeOperation::Forward { site }
                    | RuntimeOperation::Cancel { site }) => {
                        let entry =
                            self.control
                                .resumptions
                                .get(site.0 as usize)
                                .ok_or_else(|| {
                                    format!(
                                        "MIR resumption instruction references absent site {}",
                                        site.0
                                    )
                                })?;
                        let kind = match instruction {
                            RuntimeOperation::CaptureResumption { .. } => {
                                MirResumptionSiteKind::Capture
                            }
                            RuntimeOperation::Resume { .. } => MirResumptionSiteKind::Resume,
                            RuntimeOperation::ResumeReturn { .. } => {
                                MirResumptionSiteKind::ResumeReturn
                            }
                            RuntimeOperation::ResumeSnapshot { .. } => {
                                MirResumptionSiteKind::ResumeSnapshot
                            }
                            RuntimeOperation::Forward { .. } => MirResumptionSiteKind::Forward,
                            RuntimeOperation::Cancel { .. } => MirResumptionSiteKind::Cancel,
                            _ => unreachable!("resumption match is exhaustive"),
                        };
                        if entry.block != block_id || entry.scope != scope || entry.kind != kind {
                            return Err(
                                "MIR resumption instruction disagrees with frozen control table"
                                    .into(),
                            );
                        }
                        if std::mem::replace(&mut seen_resumptions[site.0 as usize], true) {
                            return Err("MIR resumption site is wired more than once".into());
                        }
                    }
                    _ => {}
                }
            }
            if let RuntimeTerminator::Leave {
                label,
                brand,
                target,
                ..
            } = &block.terminator
            {
                self.control.handler_exit(block_id, scope)?;
                let entry = self
                    .control
                    .labels
                    .get(label.0 as usize)
                    .ok_or_else(|| format!("MIR leave references absent label {}", label.0))?;
                if entry.brand != *brand
                    || entry.destination != *target
                    || !scope_is_ancestor(&self.control, entry.scope, scope)
                {
                    return Err("MIR leave disagrees with frozen control table".into());
                }
                seen_labels[label.0 as usize] = true;
            }
        }
        if seen_labels.iter().any(|seen| !seen)
            || seen_handlers.iter().any(|seen| !seen)
            || seen_performs.iter().any(|seen| !seen)
            || seen_resumptions.iter().any(|seen| !seen)
        {
            return Err("MIR control table contains an unwired site".into());
        }
        Ok(())
    }
    /// A nominal label brand is proof of exactly one lexical destination.
    /// Several source paths may leave the same label, but they must all enter
    /// the same block through that block's one typed parameter layout.  Keep
    /// this check at the frozen MIR boundary as well as the VM boundary: a
    /// hand-built MIR graph must not be able to reuse one brand as a general
    /// purpose nonlocal jump capability.
    fn validate_label_contracts(&self) -> Result<(), String> {
        let mut contracts =
            BTreeMap::<crate::LabelBrand, (MirBlockId, Vec<MirLocal>, Vec<Type>, Vec<MirHandlerSiteId>)>::new();
        for (index, block) in self.blocks.iter().enumerate() {
            let RuntimeTerminator::Leave { brand, target, .. } = &block.terminator else {
                continue;
            };
            let destination = self
                .blocks
                .get(target.0 as usize)
                .ok_or_else(|| format!("MIR label target block {} is absent", target.0))?;
            let destinations = destination.parameters.clone();
            let layout = destinations
                .iter()
                .map(|local| self.local_type(*local).cloned())
                .collect::<Result<Vec<_>, _>>()?;
            let retained = self.control.leave_handler_prefixes.get(&MirBlockId(index as u32))
                .ok_or("missing retained-handler contract")?.clone();
            let contract = (*target, destinations, layout, retained);
            match contracts.get(brand) {
                Some(previous) if previous != &contract => {
                    return Err(
                        "MIR label brand has contradictory destination or payload layout".into(),
                    );
                }
                Some(_) => {}
                None => {
                    contracts.insert(*brand, contract);
                }
            }
        }
        Ok(())
    }
    fn local_type(&self, local: MirLocal) -> Result<&Type, String> {
        self.locals
            .get(local.0 as usize)
            .map(|local| &local.ty)
            .ok_or_else(|| format!("MIR references invalid local {}", local.0))
    }
    fn require_scalar_locals(
        &self,
        locals: &[MirLocal],
        scalar: crate::types::ScalarType,
        instruction: &str,
    ) -> Result<(), String> {
        let expected = Type::Scalar(scalar);
        for local in locals {
            if self.local_type(*local)? != &expected {
                return Err(format!(
                    "MIR {instruction} has an inconsistent scalar operand type"
                ));
            }
        }
        Ok(())
    }
    fn validate_fixed_scalar_instruction(
        &self,
        instruction: &RuntimeOperation,
    ) -> Result<bool, String> {
        use crate::types::ScalarType;
        match instruction {
            RuntimeOperation::ConstI64 { dst, .. } => {
                self.require_scalar_locals(&[*dst], ScalarType::I64, "i64 constant")?;
            }
            RuntimeOperation::ConstBool { dst, .. } => {
                self.require_scalar_locals(&[*dst], ScalarType::Bool, "Bool constant")?;
            }
            RuntimeOperation::AddI64 { dst, left, right }
            | RuntimeOperation::WrappingAddI64 { dst, left, right }
            | RuntimeOperation::WrappingSubI64 { dst, left, right }
            | RuntimeOperation::WrappingMulI64 { dst, left, right }
            | RuntimeOperation::BitAndI64 { dst, left, right }
            | RuntimeOperation::BitXorI64 { dst, left, right }
            | RuntimeOperation::BitOrI64 { dst, left, right }
            | RuntimeOperation::SubI64 { dst, left, right }
            | RuntimeOperation::MulI64 { dst, left, right }
            | RuntimeOperation::DivI64 { dst, left, right }
            | RuntimeOperation::RemI64 { dst, left, right } => {
                self.require_scalar_locals(
                    &[*dst, *left, *right],
                    ScalarType::I64,
                    "i64 operation",
                )?;
            }
            RuntimeOperation::NotBool { dst, value } => {
                self.require_scalar_locals(&[*dst, *value], ScalarType::Bool, "Bool operation")?;
            }
            RuntimeOperation::EqBool { dst, left, right }
            | RuntimeOperation::NeBool { dst, left, right } => {
                self.require_scalar_locals(
                    &[*dst, *left, *right],
                    ScalarType::Bool,
                    "Bool comparison",
                )?;
            }
            RuntimeOperation::AddF64 { dst, left, right }
            | RuntimeOperation::SubF64 { dst, left, right }
            | RuntimeOperation::MulF64 { dst, left, right }
            | RuntimeOperation::DivF64 { dst, left, right }
            | RuntimeOperation::RemF64 { dst, left, right } => {
                self.require_scalar_locals(
                    &[*dst, *left, *right],
                    ScalarType::F64,
                    "f64 operation",
                )?;
            }
            RuntimeOperation::EqI64 { dst, left, right }
            | RuntimeOperation::NeI64 { dst, left, right }
            | RuntimeOperation::LtI64 { dst, left, right }
            | RuntimeOperation::LeI64 { dst, left, right }
            | RuntimeOperation::GtI64 { dst, left, right }
            | RuntimeOperation::GeI64 { dst, left, right } => {
                self.require_scalar_locals(&[*dst], ScalarType::Bool, "i64 comparison result")?;
                self.require_scalar_locals(&[*left, *right], ScalarType::I64, "i64 comparison")?;
            }
            RuntimeOperation::EqF64 { dst, left, right }
            | RuntimeOperation::NeF64 { dst, left, right }
            | RuntimeOperation::LtF64 { dst, left, right }
            | RuntimeOperation::LeF64 { dst, left, right }
            | RuntimeOperation::GtF64 { dst, left, right }
            | RuntimeOperation::GeF64 { dst, left, right } => {
                self.require_scalar_locals(&[*dst], ScalarType::Bool, "f64 comparison result")?;
                self.require_scalar_locals(&[*left, *right], ScalarType::F64, "f64 comparison")?;
            }
            RuntimeOperation::ConstU32 { dst, .. } => {
                self.require_scalar_locals(&[*dst], ScalarType::U32, "u32 constant")?;
            }
            RuntimeOperation::ConstUsize { dst, .. } => {
                self.require_scalar_locals(&[*dst], ScalarType::Usize, "usize constant")?;
            }
            RuntimeOperation::U32CheckedAdd { dst, left, right }
            | RuntimeOperation::U32CheckedSub { dst, left, right }
            | RuntimeOperation::U32CheckedMul { dst, left, right }
            | RuntimeOperation::U32CheckedDiv { dst, left, right }
            | RuntimeOperation::U32CheckedRem { dst, left, right }
            | RuntimeOperation::U32WrappingAdd { dst, left, right }
            | RuntimeOperation::U32WrappingSub { dst, left, right }
            | RuntimeOperation::U32WrappingMul { dst, left, right }
            | RuntimeOperation::U32WrappingShl { dst, left, right }
            | RuntimeOperation::U32WrappingShr { dst, left, right }
            | RuntimeOperation::U32CheckedShl { dst, left, right }
            | RuntimeOperation::U32CheckedShr { dst, left, right }
            | RuntimeOperation::BitAndU32 { dst, left, right } => {
                self.require_scalar_locals(
                    &[*dst, *left, *right],
                    ScalarType::U32,
                    "u32 operation",
                )?;
            }
            RuntimeOperation::U32Eq { dst, left, right }
            | RuntimeOperation::U32Lt { dst, left, right }
            | RuntimeOperation::U32Le { dst, left, right }
            | RuntimeOperation::NeU32 { dst, left, right } => {
                self.require_scalar_locals(&[*dst], ScalarType::Bool, "u32 comparison result")?;
                self.require_scalar_locals(&[*left, *right], ScalarType::U32, "u32 comparison")?;
            }
            RuntimeOperation::U32ToUsize { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::Usize, "u32-to-usize result")?;
                self.require_scalar_locals(&[*value], ScalarType::U32, "u32-to-usize input")?;
            }
            RuntimeOperation::UsizeToU32Checked { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::U32, "usize-to-u32 result")?;
                self.require_scalar_locals(&[*value], ScalarType::Usize, "usize-to-u32 input")?;
            }
            RuntimeOperation::I64ToU32Checked { dst, value }
            | RuntimeOperation::I64ToU32Wrapping { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::U32, "i64-to-u32 result")?;
                self.require_scalar_locals(&[*value], ScalarType::I64, "i64-to-u32 input")?;
            }
            RuntimeOperation::I64ToUsizeChecked { dst, value }
            | RuntimeOperation::I64ToUsizeWrapping { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::Usize, "i64-to-usize result")?;
                self.require_scalar_locals(&[*value], ScalarType::I64, "i64-to-usize input")?;
            }
            RuntimeOperation::I64ToU8Checked { dst, value }
            | RuntimeOperation::I64ToU8Wrapping { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::U8, "i64-to-u8 result")?;
                self.require_scalar_locals(&[*value], ScalarType::I64, "i64-to-u8 input")?;
            }
            RuntimeOperation::I64ToU16Checked { dst, value }
            | RuntimeOperation::I64ToU16Wrapping { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::U16, "i64-to-u16 result")?;
                self.require_scalar_locals(&[*value], ScalarType::I64, "i64-to-u16 input")?;
            }
            RuntimeOperation::I64ToI16Checked { dst, value }
            | RuntimeOperation::I64ToI16Wrapping { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::I16, "i64-to-i16 result")?;
                self.require_scalar_locals(&[*value], ScalarType::I64, "i64-to-i16 input")?;
            }
            RuntimeOperation::I64ToI32Checked { dst, value }
            | RuntimeOperation::I64ToI32Wrapping { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::I32, "i64-to-i32 result")?;
                self.require_scalar_locals(&[*value], ScalarType::I64, "i64-to-i32 input")?;
            }
            RuntimeOperation::I64ToI8Checked { dst, value }
            | RuntimeOperation::I64ToI8Wrapping { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::I8, "i64-to-i8 result")?;
                self.require_scalar_locals(&[*value], ScalarType::I64, "i64-to-i8 input")?;
            }
            RuntimeOperation::I64ToU64Checked { dst, value }
            | RuntimeOperation::I64ToU64Wrapping { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::U64, "i64-to-u64 result")?;
                self.require_scalar_locals(&[*value], ScalarType::I64, "i64-to-u64 input")?;
            }
            RuntimeOperation::I64ToIsizeChecked { dst, value }
            | RuntimeOperation::I64ToIsizeWrapping { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::Isize, "i64-to-isize result")?;
                self.require_scalar_locals(&[*value], ScalarType::I64, "i64-to-isize input")?;
            }
            RuntimeOperation::I64ToU128Checked { dst, value }
            | RuntimeOperation::I64ToU128Wrapping { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::U128, "i64-to-u128 result")?;
                self.require_scalar_locals(&[*value], ScalarType::I64, "i64-to-u128 input")?;
            }
            RuntimeOperation::I64ToI128Checked { dst, value }
            | RuntimeOperation::I64ToI128Wrapping { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::I128, "i64-to-i128 result")?;
                self.require_scalar_locals(&[*value], ScalarType::I64, "i64-to-i128 input")?;
            }
            RuntimeOperation::DestroyCallable { dst, value } => {
                if self.locals[dst.0 as usize].ty != Type::Unit
                    || !matches!(self.locals[value.0 as usize].ty, Type::Callable { .. })
                {
                    return Err(
                        "MIR callable destruction requires a callable and unit result".into(),
                    );
                }
            }
            RuntimeOperation::MemoryIntrinsic {
                dst,
                primitive,
                types,
                arguments,
            } => {
                let Some(mut signature) = primitive.instantiated_signature(types) else {
                    return Err("MIR memory primitive has the wrong type arity".into());
                };
                if signature.safety == crate::Safety::Unsafe && !self.unsafe_execution {
                    return Err(
                        "MIR memory primitive requires an unsafe implementation scope".into(),
                    );
                }
                // Creating a checked reference from raw storage explicitly
                // delegates lifetime validity to the unsafe caller. Retain
                // the selected source lifetime, while still checking the
                // concrete pointee and shared/unique contract exactly.
                if primitive.constructs_reference() {
                    if let (
                        Type::Reference {
                            lifetime: expected, ..
                        },
                        Type::Reference { lifetime, .. },
                    ) = (&mut signature.result, &self.locals[dst.0 as usize].ty)
                    {
                        *expected = *lifetime;
                    }
                }
                if matches!(
                    primitive,
                    crate::MemoryPrimitive::AsRawShared | crate::MemoryPrimitive::AsRawUnique
                ) && let ([parameter], [argument]) =
                    (signature.parameters.as_mut_slice(), arguments.as_slice())
                    && let (
                        Type::Reference {
                            lifetime: expected, ..
                        },
                        Type::Reference { lifetime, .. },
                    ) = (parameter, &self.locals[argument.0 as usize].ty)
                {
                    // Address extraction does not rebind or extend this loan.
                    // Its exact permission/referent remain checked below.
                    *expected = *lifetime;
                }
                if arguments.len() != signature.parameters.len()
                    || self.locals[dst.0 as usize].ty != signature.result
                    || arguments
                        .iter()
                        .zip(&signature.parameters)
                        .any(|(argument, expected)| {
                            &self.locals[argument.0 as usize].ty != expected
                        })
                {
                    return Err("MIR memory primitive ABI does not match its contract".into());
                }
            }
            RuntimeOperation::FloatIntrinsic {
                dst,
                primitive,
                arguments,
            } => {
                let (parameters, result) = primitive.scalar_signature();
                if arguments.len() != parameters.len() {
                    return Err("MIR floating runtime primitive has the wrong arity".into());
                }
                self.require_scalar_locals(&[*dst], result, "floating runtime primitive result")?;
                for (argument, parameter) in arguments.iter().zip(parameters) {
                    self.require_scalar_locals(
                        &[*argument],
                        parameter,
                        "floating runtime primitive operand",
                    )?;
                }
            }
            RuntimeOperation::IntIntrinsic {
                dst,
                primitive,
                scalar,
                arguments,
            } => {
                let Some((parameters, result)) = primitive.integer_scalar_signature(*scalar) else {
                    return Err("MIR integer runtime primitive has an invalid ABI".into());
                };
                if arguments.len() != parameters.len() {
                    return Err("MIR integer runtime primitive has the wrong arity".into());
                }
                self.require_scalar_locals(&[*dst], result, "integer runtime primitive result")?;
                for (argument, parameter) in arguments.iter().zip(parameters) {
                    self.require_scalar_locals(
                        &[*argument],
                        parameter,
                        "integer runtime primitive operand",
                    )?;
                }
            }
            RuntimeOperation::TextByteLen { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::Usize, "Text byte length result")?;
                self.require_scalar_locals(&[*value], ScalarType::Text, "Text byte length input")?;
            }
            RuntimeOperation::StaticLen { dst, value } => {
                let data = Type::StaticData {
                    element: Box::new(Type::Scalar(ScalarType::U8)),
                    tag: 0x4752_414e_4449_4f53_455f_5354_4154_4943,
                    alignment: 1,
                };
                self.validate_local_type(
                    *dst,
                    &Type::Scalar(ScalarType::Usize),
                    "static length",
                    "the result type",
                )?;
                self.validate_local_type(*value, &data, "static length", "the static-data input")?;
            }
            RuntimeOperation::TextConcat { dst, left, right } => {
                self.require_scalar_locals(
                    &[*dst, *left, *right],
                    ScalarType::Text,
                    "Text concatenation",
                )?;
            }
            RuntimeOperation::TextEq { dst, left, right } => {
                self.require_scalar_locals(&[*dst], ScalarType::U32, "Text equality result")?;
                self.require_scalar_locals(
                    &[*left, *right],
                    ScalarType::Text,
                    "Text equality inputs",
                )?;
            }
            RuntimeOperation::TextFromUtf8Checked { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::Text, "UTF-8 decode result")?;
                self.require_scalar_locals(&[*value], ScalarType::Bytes, "UTF-8 decode input")?;
            }
            RuntimeOperation::TextAsBytes { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::Bytes, "Text bytes result")?;
                self.require_scalar_locals(&[*value], ScalarType::Text, "Text bytes input")?;
            }
            RuntimeOperation::CharFromU32Checked { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::Char, "char conversion result")?;
                self.require_scalar_locals(&[*value], ScalarType::U32, "char conversion input")?;
            }
            RuntimeOperation::CharToU32 { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::U32, "char code point result")?;
                self.require_scalar_locals(&[*value], ScalarType::Char, "char code point input")?;
            }
            RuntimeOperation::StoreUsize { dst, value } => {
                self.require_scalar_locals(
                    &[*dst, *value],
                    ScalarType::Usize,
                    "runtime counter assignment",
                )?;
                if self.parameters.contains(dst)
                    || self
                        .control
                        .source_storage
                        .binding_locals
                        .contains(&Some(*dst))
                {
                    return Err(
                        "runtime counter assignment cannot target source storage or parameters"
                            .into(),
                    );
                }
            }
            RuntimeOperation::ArrayLen { dst, value } => {
                if self.local_type(*value)?.array_element().is_none() {
                    return Err("array length requires owned array storage".into());
                }
                self.require_scalar_locals(&[*dst], ScalarType::Usize, "array length")?;
            }
            RuntimeOperation::ArrayElementIsInitialized { dst, value, index }
            | RuntimeOperation::TakeArrayElement { dst, value, index } => {
                let Some(element) = self.local_type(*value)?.array_element() else {
                    return Err("dynamic array projection requires owned array storage".into());
                };
                self.require_scalar_locals(&[*index], ScalarType::Usize, "array index")?;
                if matches!(instruction, RuntimeOperation::TakeArrayElement { .. }) {
                    if dst == value || self.local_type(*dst)? != element {
                        return Err("array move result does not match element type".into());
                    }
                } else {
                    self.require_scalar_locals(
                        &[*dst],
                        ScalarType::Bool,
                        "array initialization probe",
                    )?;
                }
            }
            RuntimeOperation::BytesLen { dst, value }
            | RuntimeOperation::BytesUtf8ValidUpTo { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::Usize, "Bytes length result")?;
                self.require_scalar_locals(&[*value], ScalarType::Bytes, "Bytes length input")?;
            }
            RuntimeOperation::Blake3 { dst, value } => {
                self.require_scalar_locals(&[*dst, *value], ScalarType::Bytes, "BLAKE3")?;
            }
            RuntimeOperation::BytesFromArrayMove { dst, value } => {
                self.require_scalar_locals(&[*dst], ScalarType::Bytes, "Bytes-from-array result")?;
                self.validate_local_type(
                    *value,
                    &Type::Array(Box::new(Type::Scalar(ScalarType::U8))),
                    "Bytes-from-array conversion",
                    "an owned Array<u8> input",
                )?;
            }
            RuntimeOperation::BytesToArray { dst, value } => {
                self.validate_local_type(
                    *dst,
                    &Type::Array(Box::new(Type::Scalar(ScalarType::U8))),
                    "Bytes-to-array conversion",
                    "an Array<u8> result",
                )?;
                self.require_scalar_locals(&[*value], ScalarType::Bytes, "Bytes-to-array input")?;
            }
            RuntimeOperation::BytesConcat { dst, left, right } => {
                self.require_scalar_locals(
                    &[*dst, *left, *right],
                    ScalarType::Bytes,
                    "Bytes concatenation",
                )?;
            }
            RuntimeOperation::BytesGet { dst, bytes, index } => {
                self.require_scalar_locals(&[*dst], ScalarType::U8, "Bytes get result")?;
                self.require_scalar_locals(&[*bytes], ScalarType::Bytes, "Bytes get input")?;
                self.require_scalar_locals(&[*index], ScalarType::Usize, "Bytes get index")?;
            }
            RuntimeOperation::BytesSlice {
                dst,
                bytes,
                start,
                end,
            } => {
                self.require_scalar_locals(
                    &[*dst, *bytes],
                    ScalarType::Bytes,
                    "Bytes slice carrier",
                )?;
                self.require_scalar_locals(
                    &[*start, *end],
                    ScalarType::Usize,
                    "Bytes slice bounds",
                )?;
            }
            _ => return Ok(false),
        }
        Ok(true)
    }
    fn validate_reference(
        &self,
        value: MirLocal,
        mutability: Mutability,
        referent: &Type,
        instruction: &str,
        requirement: &str,
    ) -> Result<(), String> {
        match self.local_type(value)? {
            Type::Reference {
                mutability: actual_mutability,
                referent: actual_referent,
                ..
            } if (*actual_mutability == mutability
                || (mutability == Mutability::Shared
                    && *actual_mutability == Mutability::Unique))
                && actual_referent.as_ref() == referent =>
            {
                Ok(())
            }
            actual => Err(format!(
                "MIR {instruction} requires {requirement}; expected {referent:?}, got {actual:?}"
            )),
        }
    }

    fn validate_array_view(
        &self,
        value: MirLocal,
        element_type: &Type,
        mutability: Mutability,
        instruction: &str,
        requirement: &str,
    ) -> Result<(), String> {
        self.validate_reference(
            value,
            mutability,
            &Type::Array(Box::new(element_type.clone())),
            instruction,
            requirement,
        )
    }

    fn validate_owned_array(
        &self,
        value: MirLocal,
        element_type: &Type,
        instruction: &str,
        requirement: &str,
    ) -> Result<(), String> {
        let expected = Type::Array(Box::new(element_type.clone()));
        if self.local_type(value)? == &expected {
            Ok(())
        } else {
            Err(format!("MIR {instruction} requires {requirement}"))
        }
    }

    fn validate_local_type(
        &self,
        value: MirLocal,
        expected: &Type,
        instruction: &str,
        requirement: &str,
    ) -> Result<(), String> {
        if self.local_type(value)? == expected {
            Ok(())
        } else {
            Err(format!("MIR {instruction} requires {requirement}"))
        }
    }

    fn validate_array_view_instruction(
        &self,
        instruction: &RuntimeOperation,
    ) -> Result<bool, String> {
        match instruction {
            RuntimeOperation::ArrayGetBorrowShared {
                dst,
                value,
                index,
                element_type,
            } => {
                self.validate_reference(
                    *dst,
                    Mutability::Shared,
                    element_type,
                    "array borrow get",
                    "a shared element reference result",
                )?;
                self.validate_array_view(
                    *value,
                    element_type,
                    Mutability::Shared,
                    "array borrow get",
                    "a shared Array view",
                )?;
                self.require_scalar_locals(
                    &[*index],
                    crate::types::ScalarType::Usize,
                    "array borrow get index",
                )?;
                Ok(true)
            }
            RuntimeOperation::ArrayEmpty { dst, element_type } => {
                self.validate_owned_array(*dst, element_type, "array empty", "an Array result")?;
                Ok(true)
            }
            RuntimeOperation::ArrayPushMove {
                value,
                item,
                element_type,
            } => {
                self.validate_array_view(
                    *value,
                    element_type,
                    Mutability::Unique,
                    "array push",
                    "a unique Array view",
                )?;
                self.validate_local_type(*item, element_type, "array push", "an element item")?;
                Ok(true)
            }
            _ => Ok(false),
        }
    }
    fn validate_instruction(
        &self,
        instruction: &RuntimeOperation,
        specialized_lifted_targets: &BTreeSet<DefKey>,
    ) -> Result<(), String> {
        if let RuntimeOperation::CallIndirect { callee, .. } | RuntimeOperation::CallPrepared { callee, .. } = instruction
            && matches!(
                self.local_type(*callee)?,
                Type::Callable {
                    safety: crate::Safety::Unsafe,
                    ..
                }
            )
            && !self.unsafe_execution
        {
            return Err(
                "MIR unsafe indirect call omitted its unsafe implementation requirement".into(),
            );
        }
        match instruction {
            RuntimeOperation::IsInitialized { dst, base, fields }
            | RuntimeOperation::PrepareInvocation { dst, src: base, fields, .. }
            | RuntimeOperation::RetainResumption { dst, src: base, fields }
            | RuntimeOperation::TakeProjection { dst, base, fields } => {
                if dst == base {
                    return Err("MIR storage projection requires a distinct destination".into());
                }
                let taking = matches!(instruction, RuntimeOperation::TakeProjection { .. });
                if taking && fields.is_empty() {
                    return Err("MIR projection move requires a nonempty field path".into());
                }
                let source = self.local_type(*base)?;
                let source = if matches!(instruction, RuntimeOperation::PrepareInvocation { reborrow: true, .. }) {
                    let Type::Reference { referent, .. } = source else { return Err("invocation reborrow requires a reference".into()); };
                    referent.as_ref()
                } else { source };
                let mut candidates = vec![source.clone()];
                for index in fields {
                    let mut projected = Vec::new();
                    for ty in &candidates {
                        match ty {
                            Type::Tuple(fields) => {
                                projected.extend(fields.get(*index as usize).cloned())
                            }
                            Type::Array(element) => projected.push((**element).clone()),
                            Type::FixedArray { element, .. } if ty.fixed_array_length().is_some_and(|n| u64::from(*index) < n) => projected.push((**element).clone()),
                            Type::Nominal {
                                definition,
                                arguments,
                            } => {
                                let descriptor = self
                                    .nominal_copy_descriptors
                                    .iter()
                                    .find(|descriptor| {
                                        descriptor.definition == *definition
                                            && descriptor.arguments == *arguments
                                    })
                                    .ok_or("MIR storage projection has no frozen nominal layout")?;
                                projected.extend(
                                    descriptor
                                        .variants
                                        .iter()
                                        .filter_map(|fields| fields.get(*index as usize).cloned()),
                                );
                            }
                            _ => {}
                        }
                    }
                    if projected.is_empty() {
                        return Err("MIR storage projection is outside its frozen layout".into());
                    }
                    candidates = projected;
                }
                let destination = self.local_type(*dst)?;
                let retaining = matches!(instruction, RuntimeOperation::RetainResumption { .. });
                let preparing = matches!(instruction, RuntimeOperation::PrepareInvocation { .. });
                let mut receiver = destination;
                while let Type::Reference { referent, .. } = receiver { receiver = referent; }
                // A nominal label supplies the same intrinsic Fn authority
                // used by invocation validation. Preparation selects a value;
                // it does not give a proof-only label an address or a loan.
                let label_receiver = crate::types::label::callable(destination).is_some()
                    && matches!(instruction, RuntimeOperation::PrepareInvocation { reborrow: false, .. });
                if preparing && !matches!(receiver, Type::Callable { .. }) && !label_receiver {
                    return Err("invocation preparation requires a callable receiver".into());
                }
                if retaining && !matches!(destination, Type::Callable { .. }) {
                    return Err("MIR resumption transport requires a callable destination".into());
                }
                if if taking || retaining || preparing {
                    !candidates.contains(destination)
                } else {
                    destination != &Type::Scalar(crate::types::ScalarType::Bool)
                } {
                    return Err("MIR storage projection destination type is inconsistent".into());
                }
                return Ok(());
            }
            RuntimeOperation::DerefIsInitialized { dst, reference } => {
                if self.local_type(*dst)? != &Type::Scalar(crate::types::ScalarType::Bool)
                    || !matches!(
                        self.local_type(*reference)?,
                        Type::Reference {
                            mutability: Mutability::Unique,
                            ..
                        }
                    )
                {
                    return Err("MIR referent initialization probe requires a unique reference and Bool destination".into());
                }
                return Ok(());
            }
            RuntimeOperation::StorageLive { binding, local }
            | RuntimeOperation::StorageDead { binding, local } => {
                if self.control.source_storage.binding_local(*binding) != Some(*local) {
                    return Err(
                        "MIR storage statement does not use its frozen binding-local mapping"
                            .into(),
                    );
                }
                return Ok(());
            }
            RuntimeOperation::SetDropFlag { flag, .. } => {
                if self.local_type(*flag)? != &Type::Scalar(crate::types::ScalarType::Bool) {
                    return Err("MIR drop flag local is not Bool".into());
                }
                return Ok(());
            }
            RuntimeOperation::DestroyIf { local, flag } => {
                if self.local_type(*flag)? != &Type::Scalar(crate::types::ScalarType::Bool) {
                    return Err("MIR conditional destroy flag is not Bool".into());
                }
                // A conditional destroy is a source-storage operation, not a
                // general register-clear instruction.  Its owner must have
                // exact frozen binding provenance.
                if !self
                    .control
                    .source_storage
                    .binding_locals
                    .iter()
                    .flatten()
                    .any(|candidate| candidate == local)
                {
                    return Err("MIR conditional destroy targets non-source storage".into());
                }
                return Ok(());
            }
            _ => {}
        }
        if let RuntimeOperation::Copy { dst, src } = instruction {
            if !mir_type_is_duplicable(self.local_type(*src)?, &self.nominal_copy_descriptors) {
                return Err(format!(
                    "MIR copy duplicates an affine capability from local {} ({:?}, source {:?}) into {}",
                    src.0,
                    self.local_type(*src)?,
                    self.locals[src.0 as usize].source,
                    dst.0
                ));
            }
            return Ok(());
        }
        if let RuntimeOperation::ConstF64 { dst, bits } = instruction {
            if self.local_type(*dst)? != &Type::Scalar(crate::types::ScalarType::F64) {
                return Err("MIR f64 constant destination is not f64".into());
            }
            if !is_canonical_f64_bits(*bits) {
                return Err("MIR f64 constant has a non-canonical NaN payload".into());
            }
            return Ok(());
        }
        if let RuntimeOperation::ConstF32 { dst, bits } = instruction {
            if self.local_type(*dst)? != &Type::Scalar(crate::types::ScalarType::F32) {
                return Err("MIR f32 constant destination is not f32".into());
            }
            if !is_canonical_f32_bits(*bits) {
                return Err("MIR f32 constant has a non-canonical NaN payload".into());
            }
            return Ok(());
        }
        if self.validate_fixed_scalar_instruction(instruction)? {
            return Ok(());
        }
        if self.validate_array_view_instruction(instruction)? {
            return Ok(());
        }
        if let RuntimeOperation::MakeCallable {
            callee,
            captures,
            environment,
            ..
        } = instruction
        {
            match environment {
                Some(environment) => {
                    let source = lifted_callable_definition(environment.brand);
                    if *callee != source && !specialized_lifted_targets.contains(callee) {
                        return Err(
                            "MIR callable environment brand does not match its lifted target"
                                .into(),
                        );
                    }
                    if captures.len() != environment.captures.len() {
                        return Err(
                            "MIR callable capture registers do not match their sealed layout"
                                .into(),
                        );
                    }
                    for (&local, capture) in captures.iter().zip(&environment.captures) {
                        if self.local_type(local)? != &capture.ty {
                            return Err(
                                "MIR callable capture type does not match its sealed layout".into(),
                            );
                        }
                    }
                }
                None if !captures.is_empty() => {
                    return Err("MIR callable has captures but no sealed environment".into());
                }
                None => {}
            }
            return Ok(());
        }
        if let RuntimeOperation::MakeLabel {
            dst,
            target,
            destination,
            brand,
            ..
        } = instruction
        {
            if *self.local_type(*dst)? != crate::types::label::new(*brand, self.local_type(*destination)?.clone()) {
                return Err("MIR label value nominal brand or payload disagrees with its destination".into());
            }
            let block = self
                .blocks
                .get(target.0 as usize)
                .ok_or_else(|| "MIR label value target block is absent".to_string())?;
            if self.control.tombstoned_blocks.contains(target) {
                return Err("MIR label value targets a tombstoned block".into());
            }
            if block.parameters.as_slice() != [*destination] {
                return Err("MIR label value target does not accept its exact payload".into());
            }
            return Ok(());
        }
        if let RuntimeOperation::Borrow {
            dst,
            src,
            fields,
            unique,
            reborrow,
        } = instruction
        {
            let Type::Reference {
                mutability,
                referent: destination_referent,
                ..
            } = self.local_type(*dst)?
            else {
                return Err("MIR borrow destination is not a reference".into());
            };
            let expected_mutability = if *unique {
                Mutability::Unique
            } else {
                Mutability::Shared
            };
            if *mutability != expected_mutability {
                return Err(
                    "MIR borrow destination mutability disagrees with its loan mode".into(),
                );
            }
            match (self.local_type(*src)?, *reborrow) {
                (
                    Type::Reference {
                        mutability: parent_mutability,
                        referent: source_referent,
                        ..
                    },
                    true,
                ) => {
                    if *unique && *parent_mutability != Mutability::Unique {
                        return Err("MIR unique reborrow has a shared parent reference".into());
                    }
                    if fields.is_empty() && destination_referent != source_referent {
                        return Err("MIR whole-reference reborrow changes its referent type".into());
                    }
                }
                (source_type, false)
                    if fields.is_empty() && destination_referent.as_ref() != source_type =>
                {
                    return Err(
                        "MIR whole-place borrow referent does not match its source type".into(),
                    );
                }
                (_, true) => {
                    return Err("MIR reborrow source is not a reference".into());
                }
                _ => {}
            }
            return Ok(());
        }
        if let RuntimeOperation::MakeTuple { dst, fields } = instruction {
            let destination = self.local_type(*dst)?;
            if fields.is_empty() && destination == &Type::Unit { return Ok(()); }
            let Type::Tuple(stored) = destination else {
                return Err("MIR tuple destination does not have its tuple type".into());
            };
            if stored.len() != fields.len() { return Err("MIR tuple field count differs from its storage layout".into()); }
            for (stored, field) in stored.iter().zip(fields) {
                if !crate::types::regions::accepts_body_storage(stored, self.local_type(*field)?) {
                    return Err("MIR tuple storage does not accept its constructed field".into());
                }
            }
            return Ok(());
        }
        if let RuntimeOperation::MakeArray {
            dst,
            fields,
            element_type,
        } = instruction
        {
            if self.local_type(*dst)?.array_element() != Some(element_type)
                || !self.local_type(*dst)?.array_accepts_count(fields.len()) {
                return Err("MIR array destination does not have its array type".into());
            }
            for field in fields {
                if !crate::types::regions::accepts_body_storage(element_type, self.local_type(*field)?) {
                    return Err("MIR array field does not match its element type".into());
                }
            }
            return Ok(());
        }
        if let RuntimeOperation::Store { dst, src } = instruction {
            if !crate::types::regions::accepts_body_storage(self.local_type(*dst)?, self.local_type(*src)?) {
                return Err("MIR store value does not match its destination type".into());
            }
            return Ok(());
        }
        if let RuntimeOperation::UpdateRecord {
            dst,
            base,
            index,
            field_count,
            value,
            field_type,
        } = instruction
        {
            if index >= field_count {
                return Err("MIR record update field index is outside its field count".into());
            }
            if self.local_type(*dst)? != self.local_type(*base)? {
                return Err("MIR record update destination does not match its base type".into());
            }
            if self.local_type(*value)? != field_type {
                return Err("MIR record update value does not match its field type".into());
            }
            if !matches!(self.local_type(*base)?, Type::Nominal { .. }) {
                return Err("MIR record update base is not nominal".into());
            }
            return Ok(());
        }
        if let RuntimeOperation::PatternTest {
            dst,
            subject,
            pattern,
        } = instruction
        {
            if self.local_type(*dst)? != &Type::Scalar(crate::types::ScalarType::Bool) {
                return Err("MIR pattern test destination is not Bool".into());
            }
            return validate_pattern(pattern, self.local_type(*subject)?);
        }
        if let RuntimeOperation::InstallHandler {
            payload_destinations,
            continuation,
            target,
            continuation_owned,
            clause_owned,
            ..
        } = instruction
        {
            for roots in [continuation_owned, clause_owned] {
                if roots.windows(2).any(|pair| pair[0] >= pair[1]) {
                    return Err("MIR handler ownership roots are not canonical".into());
                }
                for root in roots { self.local_type(*root)?; }
            }
            if matches!(continuation, MirContinuationPolicy::Replay { uses } if *uses < 2) {
                return Err("MIR replay handler has fewer than two exact uses".into());
            }
            if target.0 as usize >= self.blocks.len() {
                return Err("MIR handler target block is absent".into());
            }
            if self.control.tombstoned_blocks.contains(target) {
                return Err("MIR handler targets a tombstoned block".into());
            }
            let mut destinations = BTreeSet::new();
            for destination in payload_destinations {
                self.local_type(*destination)?;
                if !destinations.insert(*destination) {
                    return Err("MIR handler repeats a payload destination".into());
                }
            }
            return Ok(());
        }
        if let RuntimeOperation::ProjectTuple {
            dst,
            base,
            index,
            field_count,
            field_type,
        } = instruction
        {
            let Type::Tuple(fields) = self.local_type(*base)? else {
                return Err("MIR tuple projection base is not a tuple".into());
            };
            if *field_count != fields.len() as u32 || *index >= *field_count {
                return Err("MIR tuple projection is outside its tuple layout".into());
            }
            if self.local_type(*dst)? != field_type
                || fields.get(*index as usize) != Some(field_type)
            {
                return Err("MIR tuple projection type does not match its layout".into());
            }
            return Ok(());
        }
        if let RuntimeOperation::ProjectArray {
            dst,
            base,
            index,
            field_count,
            element_type,
        } = instruction
        {
            let Some(actual) = self.local_type(*base)?.array_element() else {
                return Err("MIR array projection base is not an array".into());
            };
            if *index >= *field_count || actual != element_type
                || !self.local_type(*base)?.array_accepts_count(*field_count as usize) {
                return Err("MIR array projection has inconsistent structural metadata".into());
            }
            if self.local_type(*dst)? != element_type {
                return Err("MIR array projection result type does not match its element".into());
            }
            return Ok(());
        }
        let (dst, definition, fields, field_types) = match instruction {
            RuntimeOperation::MakeRecord {
                dst,
                definition,
                fields,
                field_types,
            }
            | RuntimeOperation::MakeEnum {
                dst,
                definition,
                fields,
                field_types,
                ..
            } => (dst, definition, fields, field_types),
            _ => return Ok(()),
        };
        if fields.len() != field_types.len() {
            return Err("MIR record construction has mismatched field values and types".into());
        }
        match self.local_type(*dst)? {
            Type::Nominal {
                definition: actual, ..
            } if actual == definition => {}
            _ => return Err("MIR record destination does not have its nominal type".into()),
        }
        for (&field, expected) in fields.iter().zip(field_types) {
            if self.local_type(field)? != expected {
                return Err("MIR record field does not match its declared type".into());
            }
        }
        Ok(())
    }
    fn validate_edge(&self, target: MirBlockId, arguments: &[MirLocal]) -> Result<(), String> {
        if self.control.tombstoned_blocks.contains(&target) {
            return Err(format!("MIR edge targets tombstoned block {}", target.0));
        }
        let target = self
            .blocks
            .get(target.0 as usize)
            .ok_or_else(|| format!("MIR edge targets absent block {}", target.0))?;
        if arguments.len() != target.parameters.len() {
            return Err(format!(
                "MIR edge has {} arguments for {} block parameters",
                arguments.len(),
                target.parameters.len()
            ));
        }
        for (&argument, &parameter) in arguments.iter().zip(&target.parameters) {
            if self.local_type(argument)? != self.local_type(parameter)? {
                return Err("MIR edge argument type does not match block parameter".into());
            }
        }
        Ok(())
    }
    fn validate_terminator(
        &self,
        index: usize,
        terminator: &RuntimeTerminator,
    ) -> Result<(), String> {
        match terminator {
            RuntimeTerminator::Goto { target, arguments } => self.validate_edge(*target, arguments),
            RuntimeTerminator::Leave {
                target,
                arguments,
                cleanup,
                ..
            } => {
                cleanup.validate()?;
                cleanup.validate_with_storage(
                    &self.control.move_paths,
                    &self.control.source_storage,
                )?;
                self.validate_leave_cleanup_payloads(index, arguments, cleanup)?;
                self.validate_edge(*target, arguments)
            }
            RuntimeTerminator::SwitchBool {
                condition,
                then_target,
                then_arguments,
                else_target,
                else_arguments,
            } => {
                if self.local_type(*condition)? != &Type::Scalar(crate::types::ScalarType::Bool) {
                    return Err(format!("MIR switch block {index} condition is not Bool"));
                }
                self.validate_edge(*then_target, then_arguments)?;
                self.validate_edge(*else_target, else_arguments)
            }
            RuntimeTerminator::Return { value } => {
                if self.local_type(*value)? != &self.result {
                    return Err(format!(
                        "MIR return in block {index} does not match function result"
                    ));
                }
                Ok(())
            }
            RuntimeTerminator::TailCall { arguments, .. } => {
                for argument in arguments { self.local_type(*argument)?; }
                if self.captures != 0 {
                    return Err("mandatory tail transfer retains an undischarged capture environment".into());
                }
                Ok(())
            }
            RuntimeTerminator::Unreachable => Ok(()),
        }
    }
    fn validate_leave_cleanup_payloads(
        &self,
        _block: usize,
        arguments: &[MirLocal],
        cleanup: &MirCleanupPlan,
    ) -> Result<(), String> {
        if !self
            .control
            .source_storage
            .exited_bindings(cleanup.source_storage_scope, cleanup.target_storage_scope)?
            .is_empty()
            && cleanup.protected_values != arguments
        {
            return Err("MIR cleanup protected values do not exactly match leave payloads".into());
        }
        // A cleanup path must never consume the value protected by the leave
        // edge. Parameter-origin bindings are the only compact-MIR mapping
        // available before full source-storage lowering, and are exact rather
        // than spelling-based.
        for path in &cleanup.moved_paths {
            let path = &self.control.move_paths.paths[path.0 as usize];
            let binding = &self.control.move_paths.bindings[path.binding.0 as usize];
            if let PlaceBindingOrigin::Parameter { index } = binding.origin
                && self
                    .parameters
                    .get(index as usize)
                    .is_some_and(|local| arguments.contains(local))
            {
                return Err("MIR cleanup disarms a protected leave payload".into());
            }
        }

        Ok(())
    }
}
