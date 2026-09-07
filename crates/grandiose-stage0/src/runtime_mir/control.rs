use super::*;
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) enum MirScopeEntry {
    Label(MirLabelId),
    Handler(MirHandlerSiteId),
}
impl RuntimeMir {
    pub fn with_frozen_control_tables(mut self) -> Self {
        let mut control = MirControlTables {
            leave_handler_depths: self.control.leave_handler_depths.clone(),
            move_paths: self.control.move_paths.clone(),
            tombstoned_blocks: self.control.tombstoned_blocks.clone(),
            source_storage: self.control.source_storage.clone(),
            frame_cleanup: self.control.frame_cleanup.clone(),
            cleanup_owners: self.control.cleanup_owners.clone(),
            ..MirControlTables::default()
        };
        let mut labels = BTreeMap::<crate::LabelBrand, MirLabelId>::new();

        for (block_index, block) in self.blocks.iter_mut().enumerate() {
            let block_id = MirBlockId(block_index as u32);
            for instruction in &mut block.instructions {
                match instruction {
                    RuntimeOperation::MakeLabel {
                        label,
                        brand,
                        target,
                        ..
                    } => {
                        let id = *labels.entry(*brand).or_insert_with(|| {
                            let id = MirLabelId(control.labels.len() as u32);
                            control.labels.push(MirLabelData {
                                brand: *brand,
                                scope: MirScopeId::ROOT,
                                destination: *target,
                                call_destination: true,
                            });
                            id
                        });
                        *label = id;
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
                        let id = MirHandlerSiteId(control.handlers.len() as u32);
                        control.handlers.push(MirHandlerSiteData {
                            block: block_id,
                            scope: MirScopeId::ROOT,
                            effect: *effect,
                            effect_arguments: effect_arguments.clone(),
                            operation: *operation,
                            target: *target,
                            resume_type: resume_type.clone(),
                            continuation: *continuation,
                        });
                        *site = id;
                    }
                    _ => {}
                }
            }
        }

        // `Leave` may be the only executable witness of a label (a label
        // need not be materialized as a first-class value), so allocate its
        // typed identity before deriving the lexical CFG contexts.
        for block in &mut self.blocks {
            if let RuntimeTerminator::Leave {
                label,
                brand,
                target,
                ..
            } = &mut block.terminator
            {
                let id = *labels.entry(*brand).or_insert_with(|| {
                    let id = MirLabelId(control.labels.len() as u32);
                    control.labels.push(MirLabelData {
                        brand: *brand,
                        scope: MirScopeId::ROOT,
                        destination: *target,
                        call_destination: false,
                    });
                    id
                });
                *label = id;
            }
        }

        let contexts = lexical_scope_contexts(&self.blocks, self.entry);
        let handler_bodies = control
            .handlers
            .iter()
            .enumerate()
            .map(|(index, handler)| (handler.target, MirHandlerSiteId(index as u32)))
            .collect::<BTreeMap<_, _>>();
        let mut scope_ids = BTreeMap::<Vec<MirScopeEntry>, MirScopeId>::new();
        scope_ids.insert(vec![], MirScopeId::ROOT);
        for context in contexts.values() {
            intern_lexical_scope_context(context, &mut control.scopes, &mut scope_ids);
        }
        for (block_index, block) in self.blocks.iter_mut().enumerate() {
            let block_id = MirBlockId(block_index as u32);
            let mut context = contexts.get(&block_id).cloned().unwrap_or_default();
            block.scope =
                intern_lexical_scope_context(&context, &mut control.scopes, &mut scope_ids);
            for instruction in &mut block.instructions {
                freeze_control_instruction(
                    instruction,
                    block_id,
                    &mut context,
                    &mut control,
                    &mut scope_ids,
                    handler_bodies.get(&block_id).copied(),
                );
            }
            if let RuntimeTerminator::Leave { label, .. } = &block.terminator {
                let id = *label;
                if let Some(position) = context
                    .iter()
                    .rposition(|entry| *entry == MirScopeEntry::Label(id))
                {
                    control.labels[id.0 as usize].scope = intern_lexical_scope_context(
                        &context[..=position],
                        &mut control.scopes,
                        &mut scope_ids,
                    );
                }
            }
        }
        self.control = control;
        self
    }
}
pub(super) fn lexical_scope_contexts(
    blocks: &[RuntimeBlock],
    entry: MirBlockId,
) -> BTreeMap<MirBlockId, Vec<MirScopeEntry>> {
    let mut contexts = BTreeMap::new();
    let mut pending = VecDeque::new();
    if (entry.0 as usize) < blocks.len() {
        contexts.insert(entry, vec![]);
        pending.push_back(entry);
    }
    while let Some(block_id) = pending.pop_front() {
        let Some(block) = blocks.get(block_id.0 as usize) else {
            continue;
        };
        let mut context = contexts.get(&block_id).cloned().unwrap_or_default();
        for instruction in &block.instructions {
            match instruction {
                RuntimeOperation::MakeLabel { label, target, .. } => {
                    // A first-class invocation re-enters at `target` after
                    // leaving the label's own lexical scope. Preserve the
                    // handler prefix that existed *before* this capability
                    // was minted, so a target nested in an enclosing facade
                    // can later uninstall that facade normally.
                    merge_lexical_context(&mut contexts, &mut pending, *target, &context);
                    context.push(MirScopeEntry::Label(*label));
                }
                RuntimeOperation::InstallHandler { site, target, .. } => {
                    context.push(MirScopeEntry::Handler(*site));
                    merge_lexical_context(&mut contexts, &mut pending, *target, &context);
                }
                RuntimeOperation::UninstallHandler => {
                    if let Some(index) = context
                        .iter()
                        .rposition(|entry| matches!(entry, MirScopeEntry::Handler(_)))
                    {
                        context.truncate(index);
                    }
                }
                _ => {}
            }
        }
        match &block.terminator {
            RuntimeTerminator::Goto { target, .. } => {
                merge_lexical_context(&mut contexts, &mut pending, *target, &context)
            }
            RuntimeTerminator::SwitchBool {
                then_target,
                else_target,
                ..
            } => {
                merge_lexical_context(&mut contexts, &mut pending, *then_target, &context);
                merge_lexical_context(&mut contexts, &mut pending, *else_target, &context);
            }
            RuntimeTerminator::Leave { label, target, .. } => {
                let exit = context
                    .iter()
                    .rposition(|entry| *entry == MirScopeEntry::Label(*label))
                    .map(|index| context[..index].to_vec())
                    // Direct branded leaves need not materialize a
                    // first-class label value. Their explicit cleanups have
                    // already left the lexical target prefix in `context`.
                    .unwrap_or_else(|| context.clone());
                merge_lexical_context(&mut contexts, &mut pending, *target, &exit);
            }
            RuntimeTerminator::Return { .. } | RuntimeTerminator::Unreachable => {}
        }
    }
    contexts
}

pub(super) fn merge_lexical_context(
    contexts: &mut BTreeMap<MirBlockId, Vec<MirScopeEntry>>,
    pending: &mut VecDeque<MirBlockId>,
    block: MirBlockId,
    incoming: &[MirScopeEntry],
) {
    let Some(existing) = contexts.get_mut(&block) else {
        contexts.insert(block, incoming.to_vec());
        pending.push_back(block);
        return;
    };
    let common = existing
        .iter()
        .zip(incoming)
        .take_while(|(left, right)| left == right)
        .count();
    if common < existing.len() {
        existing.truncate(common);
        pending.push_back(block);
    }
}

pub(super) fn intern_lexical_scope_context(
    context: &[MirScopeEntry],
    scopes: &mut Vec<MirScopeData>,
    ids: &mut BTreeMap<Vec<MirScopeEntry>, MirScopeId>,
) -> MirScopeId {
    if let Some(id) = ids.get(context) {
        return *id;
    }
    let (last, parent_context) = context
        .split_last()
        .expect("the root scope context is interned before child scopes");
    let parent = intern_lexical_scope_context(parent_context, scopes, ids);
    let id = MirScopeId(scopes.len() as u32);
    scopes.push(MirScopeData {
        parent: Some(parent),
        entered_label: match last {
            MirScopeEntry::Label(label) => Some(*label),
            MirScopeEntry::Handler(_) => None,
        },
        entered_handler: match last {
            MirScopeEntry::Label(_) => None,
            MirScopeEntry::Handler(handler) => Some(*handler),
        },
    });
    ids.insert(context.to_vec(), id);
    id
}

pub(super) fn lexical_handler_candidates(
    control: &MirControlTables,
    scope: MirScopeId,
    effect: DefKey,
    effect_arguments: &[crate::GenericArgument],
    operation: u32,
) -> Vec<MirHandlerSiteId> {
    let mut candidates = Vec::new();
    let mut current = Some(scope);
    while let Some(scope) = current {
        let Some(data) = control.scopes.get(scope.0 as usize) else {
            break;
        };
        if let Some(site) = data.entered_handler
            && let Some(handler) = control.handlers.get(site.0 as usize)
            && handler.effect == effect
            && handler.effect_arguments == effect_arguments
            && handler.operation == operation
        {
            candidates.push(site);
        }
        current = data.parent;
    }
    candidates
}

pub(super) fn scope_enters_label(
    control: &MirControlTables,
    child: MirScopeId,
    parent: MirScopeId,
    label: MirLabelId,
) -> bool {
    control
        .scopes
        .get(child.0 as usize)
        .is_some_and(|scope| scope.parent == Some(parent) && scope.entered_label == Some(label))
}

pub(super) fn scope_enters_handler(
    control: &MirControlTables,
    child: MirScopeId,
    parent: MirScopeId,
    handler: MirHandlerSiteId,
) -> bool {
    control
        .scopes
        .get(child.0 as usize)
        .is_some_and(|scope| scope.parent == Some(parent) && scope.entered_handler == Some(handler))
}

pub(super) fn scope_after_uninstall(
    control: &MirControlTables,
    scope: MirScopeId,
) -> Option<MirScopeId> {
    let mut current = scope;
    loop {
        let data = control.scopes.get(current.0 as usize)?;
        if data.entered_handler.is_some() {
            return data.parent;
        }
        current = data.parent?;
    }
}

pub(super) fn scope_is_ancestor(
    control: &MirControlTables,
    ancestor: MirScopeId,
    scope: MirScopeId,
) -> bool {
    let mut current = Some(scope);
    while let Some(id) = current {
        if id == ancestor {
            return true;
        }
        current = control
            .scopes
            .get(id.0 as usize)
            .and_then(|data| data.parent);
    }
    false
}

pub(super) fn freeze_control_instruction(
    instruction: &mut RuntimeOperation,
    block: MirBlockId,
    context: &mut Vec<MirScopeEntry>,
    control: &mut MirControlTables,
    scope_ids: &mut BTreeMap<Vec<MirScopeEntry>, MirScopeId>,
    originating_handler: Option<MirHandlerSiteId>,
) {
    match instruction {
        RuntimeOperation::MakeLabel { label, .. } => {
            context.push(MirScopeEntry::Label(*label));
            control.labels[label.0 as usize].scope =
                intern_lexical_scope_context(context, &mut control.scopes, scope_ids);
        }
        RuntimeOperation::InstallHandler { site, .. } => {
            context.push(MirScopeEntry::Handler(*site));
            control.handlers[site.0 as usize].scope =
                intern_lexical_scope_context(context, &mut control.scopes, scope_ids);
        }
        RuntimeOperation::UninstallHandler => {
            if let Some(index) = context
                .iter()
                .rposition(|entry| matches!(entry, MirScopeEntry::Handler(_)))
            {
                context.truncate(index);
            }
        }
        RuntimeOperation::Perform {
            site,
            effect,
            effect_arguments,
            operation,
            ..
        } => {
            let scope = intern_lexical_scope_context(context, &mut control.scopes, scope_ids);
            let id = MirPerformSiteId(control.performs.len() as u32);
            control.performs.push(MirPerformSiteData {
                block,
                scope,
                effect: *effect,
                effect_arguments: effect_arguments.clone(),
                operation: *operation,
                handler_candidates: lexical_handler_candidates(
                    control,
                    scope,
                    *effect,
                    effect_arguments,
                    *operation,
                ),
            });
            *site = id;
        }
        RuntimeOperation::CaptureResumption { site, .. } => freeze_resumption_site(
            site,
            MirResumptionSiteKind::Capture,
            block,
            context,
            control,
            scope_ids,
            originating_handler,
        ),
        RuntimeOperation::Resume { site, .. } => freeze_resumption_site(
            site,
            MirResumptionSiteKind::Resume,
            block,
            context,
            control,
            scope_ids,
            originating_handler,
        ),
        RuntimeOperation::ResumeReturn { site, .. } => freeze_resumption_site(
            site,
            MirResumptionSiteKind::ResumeReturn,
            block,
            context,
            control,
            scope_ids,
            originating_handler,
        ),
        RuntimeOperation::ResumeSnapshot { site, .. } => freeze_resumption_site(
            site,
            MirResumptionSiteKind::ResumeSnapshot,
            block,
            context,
            control,
            scope_ids,
            originating_handler,
        ),
        RuntimeOperation::Forward { site } => freeze_resumption_site(
            site,
            MirResumptionSiteKind::Forward,
            block,
            context,
            control,
            scope_ids,
            originating_handler,
        ),
        RuntimeOperation::Cancel { site } => freeze_resumption_site(
            site,
            MirResumptionSiteKind::Cancel,
            block,
            context,
            control,
            scope_ids,
            originating_handler,
        ),
        _ => {}
    }
}

pub(super) fn freeze_resumption_site(
    site: &mut MirResumptionSiteId,
    kind: MirResumptionSiteKind,
    block: MirBlockId,
    context: &[MirScopeEntry],
    control: &mut MirControlTables,
    scope_ids: &mut BTreeMap<Vec<MirScopeEntry>, MirScopeId>,
    originating_handler: Option<MirHandlerSiteId>,
) {
    let id = MirResumptionSiteId(control.resumptions.len() as u32);
    control.resumptions.push(MirResumptionSiteData {
        block,
        scope: intern_lexical_scope_context(context, &mut control.scopes, scope_ids),
        kind,
        // A resumption belongs to the handler clause CFG entered through its
        // explicit target, not merely to an active protected frame. Nested
        // setup code may execute under several frames before it reaches a
        // clause, so using the nearest lexical frame here would forge a
        // handler-body provenance that the existing verifier rejects.
        originating_handler,
    });
    *site = id;
}
