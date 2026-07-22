//! Deterministic source-module graph and name resolution.
//!
//! Module identities are structured and source-order independent. Backend
//! spellings are derived from those identities only after resolution; the
//! structured tables remain authoritative for diagnostics and tooling.

use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    path::{Component, Path, PathBuf},
    rc::Rc,
};

use crate::{
    ast::{ImportTree, ModuleKind, Program, Visibility},
    diagnostic::Diagnostic,
    source_bundle::{SegmentId, SourceBundle},
    span::Span,
};

const MODULE_CODE: &str = "G1MOD001";

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ModuleId(pub u32);

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Namespace {
    Module,
    Type,
    Value,
    Trait,
    Effect,
    Fixity,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct DefId {
    pub module: ModuleId,
    pub namespace: Namespace,
    pub name: String,
}

#[derive(Clone, Debug)]
pub struct ModuleInfo {
    pub id: ModuleId,
    pub parent: Option<ModuleId>,
    pub name: String,
    pub path: Vec<String>,
    pub declaration: Option<Span>,
    pub segment: Option<SegmentId>,
    pub public: bool,
    physical_dir: PathBuf,
}

#[derive(Clone, Debug, Default)]
pub struct ModuleResolution {
    pub modules: Vec<ModuleInfo>,
    pub definitions: BTreeMap<DefId, Span>,
    pub resolved_paths: BTreeMap<(usize, usize), DefId>,
    segment_modules: BTreeMap<SegmentId, ModuleId>,
    inline_scopes: Vec<(Span, ModuleId)>,
    declaration_defs: BTreeMap<(usize, usize), DefId>,
    definition_public: BTreeMap<DefId, bool>,
    prelude_definitions: BTreeSet<DefId>,
    syntax_path_spans: BTreeMap<(usize, usize), Span>,
}

impl ModuleResolution {
    pub fn module(&self, id: ModuleId) -> &ModuleInfo {
        &self.modules[id.0 as usize]
    }

    pub fn owner(&self, bundle: &SourceBundle, span: Span) -> Option<ModuleId> {
        owner_for_span(span, bundle, &self.segment_modules, &self.inline_scopes)
    }

    pub fn definition_at(&self, declaration: Span) -> Option<&DefId> {
        self.declaration_defs
            .get(&(declaration.start, declaration.end))
    }

    pub fn resolved_path(&self, span: Span) -> Option<&DefId> {
        self.resolved_paths.get(&(span.start, span.end))
    }

    pub fn is_public(&self, definition: &DefId) -> bool {
        self.definition_public
            .get(definition)
            .copied()
            .unwrap_or(false)
    }

    /// An internal symbol that cannot be produced by the source identifier
    /// grammar. Length framing keeps it injective even if display paths are
    /// later extended beyond ordinary identifiers.
    pub fn backend_spelling(&self, definition: &DefId) -> String {
        if definition.module == ModuleId(0) {
            return definition.name.clone();
        }
        let module = self.module(definition.module);
        let mut encoded = String::from("$grandiose$");
        for component in &module.path {
            encoded.push_str(&component.len().to_string());
            encoded.push(':');
            encoded.push_str(component);
        }
        encoded.push('$');
        encoded.push_str(match definition.namespace {
            Namespace::Module => "m",
            Namespace::Type => "t",
            Namespace::Value => "v",
            Namespace::Trait => "r",
            Namespace::Effect => "e",
            Namespace::Fixity => "f",
        });
        encoded.push_str(&definition.name.len().to_string());
        encoded.push(':');
        encoded.push_str(&definition.name);
        encoded
    }
}

#[derive(Clone, Debug)]
pub struct ResolvedProgram {
    pub program: Program,
    pub resolution: ModuleResolution,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Binding {
    definition: DefId,
    public: bool,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ModuleBinding {
    module: ModuleId,
    public: bool,
}

#[derive(Clone, Debug)]
enum ImportLeaf {
    Name {
        path: Vec<String>,
        alias: String,
        span: Span,
    },
    ModuleSelf {
        path: Vec<String>,
        alias: Option<String>,
        span: Span,
    },
    Glob {
        path: Vec<String>,
        span: Span,
    },
}

#[derive(Clone, Debug)]
struct ImportSpec {
    owner: ModuleId,
    public: bool,
    leaf: ImportLeaf,
}

#[derive(Default)]
struct Scopes {
    definitions: BTreeMap<(ModuleId, Namespace, String), BTreeSet<Binding>>,
    modules: BTreeMap<(ModuleId, String), BTreeSet<ModuleBinding>>,
}

fn flatten_import(tree: &ImportTree, prefix: &mut Vec<String>, leaves: &mut Vec<ImportLeaf>) {
    match tree {
        ImportTree::Path { segment, tree } => {
            prefix.push(segment.name.clone());
            flatten_import(tree, prefix, leaves);
            prefix.pop();
        }
        ImportTree::Name { name, alias } => {
            let mut path = prefix.clone();
            path.push(name.name.clone());
            leaves.push(ImportLeaf::Name {
                path,
                alias: alias
                    .as_ref()
                    .map_or_else(|| name.name.clone(), |alias| alias.name.clone()),
                span: name.span,
            });
        }
        ImportTree::SelfValue { span, alias } => leaves.push(ImportLeaf::ModuleSelf {
            path: prefix.clone(),
            alias: alias.as_ref().map(|alias| alias.name.clone()),
            span: *span,
        }),
        ImportTree::Glob { span } => leaves.push(ImportLeaf::Glob {
            path: prefix.clone(),
            span: *span,
        }),
        ImportTree::Group { items, .. } => {
            for item in items {
                flatten_import(item, prefix, leaves);
            }
        }
    }
}

fn is_descendant(resolution: &ModuleResolution, mut module: ModuleId, ancestor: ModuleId) -> bool {
    loop {
        if module == ancestor {
            return true;
        }
        let Some(parent) = resolution.module(module).parent else {
            return false;
        };
        module = parent;
    }
}

fn package_root(resolution: &ModuleResolution, mut module: ModuleId) -> ModuleId {
    while let Some(parent) = resolution.module(module).parent {
        module = parent;
    }
    module
}

fn module_visible_from(resolution: &ModuleResolution, module: ModuleId, from: ModuleId) -> bool {
    let info = resolution.module(module);
    info.public
        || info
            .parent
            .is_some_and(|parent| is_descendant(resolution, from, parent))
}

fn definition_visible_from(
    resolution: &ModuleResolution,
    definition: &DefId,
    from: ModuleId,
) -> bool {
    resolution.is_public(definition) || is_descendant(resolution, from, definition.module)
}

fn child_modules(
    resolution: &ModuleResolution,
    parent: ModuleId,
    name: &str,
) -> BTreeSet<ModuleId> {
    resolution
        .modules
        .iter()
        .filter(|module| module.parent == Some(parent) && module.name == name)
        .map(|module| module.id)
        .collect()
}

fn resolve_module_path(
    resolution: &ModuleResolution,
    scopes: &Scopes,
    current: ModuleId,
    path: &[String],
) -> BTreeSet<ModuleId> {
    if path.is_empty() {
        return BTreeSet::from([current]);
    }
    let mut index = 0;
    let mut modules = match path[0].as_str() {
        "crate" => {
            index = 1;
            BTreeSet::from([package_root(resolution, current)])
        }
        "self" => {
            index = 1;
            BTreeSet::from([current])
        }
        "super" => {
            let mut module = current;
            while path.get(index).is_some_and(|segment| segment == "super") {
                let Some(parent) = resolution.module(module).parent else {
                    return BTreeSet::new();
                };
                module = parent;
                index += 1;
            }
            BTreeSet::from([module])
        }
        name => {
            index = 1;
            let mut found = child_modules(resolution, current, name)
                .into_iter()
                .filter(|module| module_visible_from(resolution, *module, current))
                .collect::<BTreeSet<_>>();
            found.extend(
                scopes
                    .modules
                    .get(&(current, name.to_string()))
                    .into_iter()
                    .flatten()
                    .map(|binding| binding.module),
            );
            found
        }
    };
    for segment in &path[index..] {
        let mut next = BTreeSet::new();
        for module in modules {
            next.extend(
                child_modules(resolution, module, segment)
                    .into_iter()
                    .filter(|child| module_visible_from(resolution, *child, current)),
            );
        }
        modules = next;
    }
    modules
}

fn resolve_definition(
    resolution: &ModuleResolution,
    scopes: &Scopes,
    current: ModuleId,
    namespace: Namespace,
    path: &[String],
    span: Span,
    errors: &mut Vec<Diagnostic>,
) -> Option<DefId> {
    let (name, prefix) = path.split_last()?;
    let modules = if prefix.is_empty() {
        BTreeSet::from([current])
    } else {
        resolve_module_path(resolution, scopes, current, prefix)
    };
    let mut found = BTreeSet::new();
    let mut hidden = false;
    for module in modules {
        for binding in scopes
            .definitions
            .get(&(module, namespace, name.clone()))
            .into_iter()
            .flatten()
        {
            if definition_visible_from(resolution, &binding.definition, current) {
                found.insert(binding.definition.clone());
            } else {
                hidden = true;
            }
        }
    }
    let root = package_root(resolution, current);
    if prefix.is_empty() && current != root && found.is_empty() {
        found.extend(
            scopes
                .definitions
                .get(&(root, namespace, name.clone()))
                .into_iter()
                .flatten()
                .map(|binding| binding.definition.clone()),
        );
    }
    if prefix.is_empty() && root != ModuleId(0) && found.is_empty() {
        found.extend(
            scopes
                .definitions
                .get(&(ModuleId(0), namespace, name.clone()))
                .into_iter()
                .flatten()
                .filter(|binding| resolution.prelude_definitions.contains(&binding.definition))
                .map(|binding| binding.definition.clone()),
        );
    }
    match found.len() {
        0 => {
            if hidden {
                errors.push(error(
                    span,
                    format!("`{}` is private to its defining module", path.join("::")),
                ));
            }
            None
        }
        1 => found.into_iter().next(),
        _ => {
            errors.push(error(
                span,
                format!(
                    "path `{}` is ambiguous in the {namespace:?} namespace",
                    path.join("::")
                ),
            ));
            None
        }
    }
}

fn path_names(path: &[crate::ast::TypePathSegment]) -> Vec<String> {
    path.iter().map(|segment| segment.name.clone()).collect()
}

fn syntax_path_span(path: &[crate::ast::TypePathSegment]) -> Option<Span> {
    Some(path.first()?.span.join(path.last()?.span))
}

fn rewrite_type(
    ty: &mut crate::ast::TypeSyntax,
    current: ModuleId,
    resolution: &mut ModuleResolution,
    scopes: &Scopes,
    errors: &mut Vec<Diagnostic>,
) {
    use crate::ast::TypeSyntaxKind;
    match &mut ty.kind {
        TypeSyntaxKind::Path(path) => {
            let names = path_names(path);
            let path_span = syntax_path_span(path).unwrap_or(ty.span);
            if let Some(definition) = resolve_definition(
                resolution,
                scopes,
                current,
                Namespace::Type,
                &names,
                path_span,
                errors,
            ) {
                let spelling = resolution.backend_spelling(&definition);
                resolution
                    .resolved_paths
                    .insert((path_span.start, path_span.end), definition);
                *path = vec![crate::ast::TypePathSegment {
                    name: spelling,
                    span: ty.span,
                }];
            }
        }
        TypeSyntaxKind::SharedReference(referent) | TypeSyntaxKind::UniqueReference(referent) => {
            rewrite_type(referent, current, resolution, scopes, errors)
        }
        TypeSyntaxKind::Tuple(elements) => {
            for element in elements {
                rewrite_type(element, current, resolution, scopes, errors);
            }
        }
        TypeSyntaxKind::Application {
            constructor,
            arguments,
            ..
        } => {
            rewrite_type(constructor, current, resolution, scopes, errors);
            for argument in arguments {
                rewrite_type(argument, current, resolution, scopes, errors);
            }
        }
        TypeSyntaxKind::Projection {
            subject,
            trait_ref,
            arguments,
            ..
        } => {
            rewrite_type(subject, current, resolution, scopes, errors);
            rewrite_trait_ref(trait_ref, current, resolution, scopes, errors);
            for argument in arguments {
                if let crate::ast::AssociatedArgumentSyntax::Type(argument) = argument {
                    rewrite_type(argument, current, resolution, scopes, errors);
                }
            }
        }
        TypeSyntaxKind::Never => {}
    }
}

fn rewrite_trait_ref(
    relation: &mut crate::ast::TraitRefSyntax,
    current: ModuleId,
    resolution: &mut ModuleResolution,
    scopes: &Scopes,
    errors: &mut Vec<Diagnostic>,
) {
    let names = path_names(&relation.path);
    let path_span = syntax_path_span(&relation.path).unwrap_or(relation.span);
    if let Some(definition) = resolve_definition(
        resolution,
        scopes,
        current,
        Namespace::Trait,
        &names,
        path_span,
        errors,
    ) {
        let spelling = resolution.backend_spelling(&definition);
        resolution
            .resolved_paths
            .insert((path_span.start, path_span.end), definition);
        relation.path = vec![crate::ast::TypePathSegment {
            name: spelling,
            span: relation.span,
        }];
    }
    for argument in &mut relation.arguments {
        if let crate::ast::GoalArgument::Type(argument) = argument {
            rewrite_type(argument, current, resolution, scopes, errors);
        }
    }
    for binding in &mut relation.bindings {
        match &mut binding.value {
            crate::ast::AssociatedBindingValue::Type(value) => {
                rewrite_type(value, current, resolution, scopes, errors)
            }
            crate::ast::AssociatedBindingValue::EffectRow(row) => {
                rewrite_effect_row(row, current, resolution, scopes, errors)
            }
        }
    }
}

fn rewrite_effect_row(
    row: &mut crate::ast::EffectRowSyntax,
    current: ModuleId,
    resolution: &mut ModuleResolution,
    scopes: &Scopes,
    errors: &mut Vec<Diagnostic>,
) {
    for effect in &mut row.effects {
        let names = match &effect.kind {
            crate::ast::TypeSyntaxKind::Path(path) => Some(path_names(path)),
            _ => None,
        };
        let path_span = match &effect.kind {
            crate::ast::TypeSyntaxKind::Path(path) => syntax_path_span(path),
            _ => None,
        }
        .unwrap_or(effect.span);
        if let Some(names) = names
            && let Some(definition) = resolve_definition(
                resolution,
                scopes,
                current,
                Namespace::Effect,
                &names,
                path_span,
                errors,
            )
        {
            let spelling = resolution.backend_spelling(&definition);
            resolution
                .resolved_paths
                .insert((path_span.start, path_span.end), definition);
            effect.kind = crate::ast::TypeSyntaxKind::Path(vec![crate::ast::TypePathSegment {
                name: spelling,
                span: effect.span,
            }]);
        }
    }
}

fn rewrite_value_path(
    path: &[String],
    span: Span,
    current: ModuleId,
    resolution: &mut ModuleResolution,
    scopes: &Scopes,
    errors: &mut Vec<Diagnostic>,
) -> Option<Vec<String>> {
    if let Some(definition) = resolve_definition(
        resolution,
        scopes,
        current,
        Namespace::Value,
        path,
        span,
        errors,
    ) {
        let spelling = resolution.backend_spelling(&definition);
        let exact = resolution
            .syntax_path_spans
            .get(&(span.start, span.end))
            .copied()
            .unwrap_or(span);
        resolution
            .resolved_paths
            .insert((exact.start, exact.end), definition);
        return Some(vec![spelling]);
    }
    let (member, owner) = path.split_last()?;
    for namespace in [Namespace::Type, Namespace::Trait] {
        if let Some(definition) =
            resolve_definition(resolution, scopes, current, namespace, owner, span, errors)
        {
            let spelling = resolution.backend_spelling(&definition);
            let exact = resolution
                .syntax_path_spans
                .get(&(span.start, span.end))
                .copied()
                .unwrap_or(span);
            resolution
                .resolved_paths
                .insert((exact.start, exact.end), definition);
            return Some(vec![spelling, member.clone()]);
        }
    }
    None
}

fn pattern_bindings(pattern: &crate::ast::Pattern, bound: &mut BTreeSet<String>) {
    use crate::ast::PatternKind;
    match &pattern.kind {
        PatternKind::Binding(name) => {
            bound.insert(name.clone());
        }
        PatternKind::Variant { fields, .. } => {
            for field in fields {
                pattern_bindings(field, bound);
            }
        }
        PatternKind::Tuple { elements, .. } => {
            for element in elements {
                pattern_bindings(element, bound);
            }
        }
        PatternKind::Struct { fields, .. } => {
            for field in fields {
                pattern_bindings(&field.pattern, bound);
            }
        }
        PatternKind::Wildcard
        | PatternKind::Unit
        | PatternKind::Int(_)
        | PatternKind::Float(_)
        | PatternKind::String(_)
        | PatternKind::Char(_)
        | PatternKind::Byte(_) => {}
    }
}

fn rewrite_pattern(
    pattern: &mut crate::ast::Pattern,
    current: ModuleId,
    resolution: &mut ModuleResolution,
    scopes: &Scopes,
    errors: &mut Vec<Diagnostic>,
) {
    use crate::ast::PatternKind;
    match &mut pattern.kind {
        PatternKind::Variant { path, fields, .. } => {
            if let Some(rewritten) =
                rewrite_value_path(path, pattern.span, current, resolution, scopes, errors)
            {
                *path = rewritten;
            }
            for field in fields {
                rewrite_pattern(field, current, resolution, scopes, errors);
            }
        }
        PatternKind::Tuple { elements, .. } => {
            for element in elements {
                rewrite_pattern(element, current, resolution, scopes, errors);
            }
        }
        PatternKind::Struct { name, fields, .. } => {
            if let Some(definition) = resolve_definition(
                resolution,
                scopes,
                current,
                Namespace::Type,
                std::slice::from_ref(name),
                pattern.span,
                errors,
            ) {
                *name = resolution.backend_spelling(&definition);
                resolution
                    .resolved_paths
                    .insert((pattern.span.start, pattern.span.end), definition);
            }
            for field in fields {
                rewrite_pattern(&mut field.pattern, current, resolution, scopes, errors);
            }
        }
        PatternKind::Binding(_)
        | PatternKind::Wildcard
        | PatternKind::Unit
        | PatternKind::Int(_)
        | PatternKind::Float(_)
        | PatternKind::String(_)
        | PatternKind::Char(_)
        | PatternKind::Byte(_) => {}
    }
}

fn rewrite_statements(
    statements: &mut Vec<crate::ast::Stmt>,
    current: ModuleId,
    bound: &mut BTreeSet<String>,
    resolution: &mut ModuleResolution,
    scopes: &Scopes,
    effect_sites: &BTreeMap<(usize, usize), String>,
    errors: &mut Vec<Diagnostic>,
) {
    for statement in statements {
        match statement {
            crate::ast::Stmt::Let { name, value, .. } => {
                rewrite_expression(
                    value,
                    current,
                    bound,
                    resolution,
                    scopes,
                    effect_sites,
                    errors,
                );
                bound.insert(name.clone());
            }
            crate::ast::Stmt::Deconstruct {
                ty, fields, value, ..
            } => {
                rewrite_expression(
                    value,
                    current,
                    bound,
                    resolution,
                    scopes,
                    effect_sites,
                    errors,
                );
                if let Some(name) = ty
                    && let Some(definition) = resolve_definition(
                        resolution,
                        scopes,
                        current,
                        Namespace::Type,
                        std::slice::from_ref(name),
                        value.span,
                        errors,
                    )
                {
                    *name = resolution.backend_spelling(&definition);
                }
                bound.extend(fields.iter().filter_map(|field| field.binding.clone()));
            }
            crate::ast::Stmt::Assign {
                destination, value, ..
            } => {
                rewrite_expression(
                    value,
                    current,
                    bound,
                    resolution,
                    scopes,
                    effect_sites,
                    errors,
                );
                if let crate::ast::AssignmentPlaceKind::Dereference { reference, .. } =
                    &mut destination.kind
                {
                    rewrite_expression(
                        Rc::make_mut(reference),
                        current,
                        bound,
                        resolution,
                        scopes,
                        effect_sites,
                        errors,
                    );
                }
            }
            crate::ast::Stmt::Expr(expression) => rewrite_expression(
                expression,
                current,
                bound,
                resolution,
                scopes,
                effect_sites,
                errors,
            ),
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn rewrite_refinement_if(
    callee: &mut crate::ast::Expr,
    arguments: &mut Vec<crate::ast::Expr>,
    current: ModuleId,
    bound: &BTreeSet<String>,
    resolution: &mut ModuleResolution,
    scopes: &Scopes,
    effect_sites: &BTreeMap<(usize, usize), String>,
    errors: &mut Vec<Diagnostic>,
) -> bool {
    use crate::ast::ExprKind;

    let ExprKind::Variable(else_path) = &callee.kind else {
        return false;
    };
    if else_path.len() != 1 || else_path[0].as_ref() != "else" {
        return false;
    }
    let [if_expression, negative] = arguments.as_mut_slice() else {
        return false;
    };
    let ExprKind::Call(if_callee, if_arguments) = &mut if_expression.kind else {
        return false;
    };
    let ExprKind::Variable(if_path) = &if_callee.kind else {
        return false;
    };
    if if_path.len() != 1 || if_path[0].as_ref() != "if" {
        return false;
    }
    let [condition, positive] = Rc::make_mut(if_arguments).as_mut_slice() else {
        return false;
    };
    let ExprKind::Is { subject, pattern } = &mut condition.kind else {
        return false;
    };

    rewrite_expression(
        callee,
        current,
        bound,
        resolution,
        scopes,
        effect_sites,
        errors,
    );
    rewrite_expression(
        Rc::make_mut(if_callee),
        current,
        bound,
        resolution,
        scopes,
        effect_sites,
        errors,
    );
    rewrite_expression(
        Rc::make_mut(subject),
        current,
        bound,
        resolution,
        scopes,
        effect_sites,
        errors,
    );
    rewrite_pattern(Rc::make_mut(pattern), current, resolution, scopes, errors);

    let mut positive_bound = bound.clone();
    pattern_bindings(pattern, &mut positive_bound);
    rewrite_expression(
        positive,
        current,
        &positive_bound,
        resolution,
        scopes,
        effect_sites,
        errors,
    );
    rewrite_expression(
        negative,
        current,
        bound,
        resolution,
        scopes,
        effect_sites,
        errors,
    );
    true
}

#[allow(clippy::too_many_arguments)]
fn rewrite_expression(
    expression: &mut crate::ast::Expr,
    current: ModuleId,
    bound: &BTreeSet<String>,
    resolution: &mut ModuleResolution,
    scopes: &Scopes,
    effect_sites: &BTreeMap<(usize, usize), String>,
    errors: &mut Vec<Diagnostic>,
) {
    use crate::ast::ExprKind;
    match &mut expression.kind {
        ExprKind::Variable(path) => {
            let names = path.iter().map(ToString::to_string).collect::<Vec<_>>();
            if !(names.len() == 1 && bound.contains(&names[0])) {
                if let Some(rewritten) =
                    rewrite_value_path(&names, expression.span, current, resolution, scopes, errors)
                {
                    *path = Rc::from(
                        rewritten
                            .into_iter()
                            .map(Rc::<str>::from)
                            .collect::<Vec<_>>(),
                    );
                } else if package_root(resolution, current) != ModuleId(0) {
                    errors.push(error(
                        expression.span,
                        format!(
                            "unresolved value path `{}` in dependency package",
                            names.join("::")
                        ),
                    ));
                }
            }
        }
        ExprKind::Move(value)
        | ExprKind::Unary { operand: value, .. }
        | ExprKind::Labeled { body: value, .. }
        | ExprKind::LabelDestination { body: value, .. }
        | ExprKind::Cancel { resumption: value }
        | ExprKind::Field(value, _) => rewrite_expression(
            Rc::make_mut(value),
            current,
            bound,
            resolution,
            scopes,
            effect_sites,
            errors,
        ),
        ExprKind::Closure { params, body } => {
            let mut nested = bound.clone();
            nested.extend(params.iter().map(ToString::to_string));
            rewrite_expression(
                Rc::make_mut(body),
                current,
                &nested,
                resolution,
                scopes,
                effect_sites,
                errors,
            );
        }
        ExprKind::TypedClosure {
            params,
            return_type,
            outward_effects,
            body,
            ..
        } => {
            for parameter in Rc::make_mut(params) {
                rewrite_type(&mut parameter.ty, current, resolution, scopes, errors);
            }
            if let Some(result) = return_type {
                rewrite_type(Rc::make_mut(result), current, resolution, scopes, errors);
            }
            if let Some(row) = outward_effects {
                rewrite_effect_row(Rc::make_mut(row), current, resolution, scopes, errors);
            }
            let mut nested = bound.clone();
            nested.extend(params.iter().map(|parameter| parameter.name.clone()));
            rewrite_expression(
                Rc::make_mut(body),
                current,
                &nested,
                resolution,
                scopes,
                effect_sites,
                errors,
            );
        }
        ExprKind::Leave { value, .. }
        | ExprKind::Resume { value, .. }
        | ExprKind::TailResume { value, .. } => {
            if let Some(value) = value {
                rewrite_expression(
                    Rc::make_mut(value),
                    current,
                    bound,
                    resolution,
                    scopes,
                    effect_sites,
                    errors,
                );
            }
            match &mut expression.kind {
                ExprKind::Resume { resumption, .. } | ExprKind::TailResume { resumption, .. } => {
                    rewrite_expression(
                        Rc::make_mut(resumption),
                        current,
                        bound,
                        resolution,
                        scopes,
                        effect_sites,
                        errors,
                    )
                }
                _ => {}
            }
        }
        ExprKind::ContextBlock(statements) | ExprKind::Block(statements) => {
            let mut nested = bound.clone();
            rewrite_statements(
                Rc::make_mut(statements),
                current,
                &mut nested,
                resolution,
                scopes,
                effect_sites,
                errors,
            );
        }
        ExprKind::List(values) | ExprKind::Tuple(values) => {
            for value in Rc::make_mut(values) {
                rewrite_expression(
                    value,
                    current,
                    bound,
                    resolution,
                    scopes,
                    effect_sites,
                    errors,
                );
            }
        }
        ExprKind::Struct { name, fields } => {
            let source_name = name.to_string();
            if let Some(definition) = resolve_definition(
                resolution,
                scopes,
                current,
                Namespace::Type,
                std::slice::from_ref(&source_name),
                expression.span,
                errors,
            ) {
                *name = Rc::from(resolution.backend_spelling(&definition));
            }
            for (_, value) in Rc::make_mut(fields) {
                rewrite_expression(
                    value,
                    current,
                    bound,
                    resolution,
                    scopes,
                    effect_sites,
                    errors,
                );
            }
        }
        ExprKind::Call(callee, arguments) => {
            if rewrite_refinement_if(
                Rc::make_mut(callee),
                Rc::make_mut(arguments),
                current,
                bound,
                resolution,
                scopes,
                effect_sites,
                errors,
            ) {
                return;
            }
            rewrite_expression(
                Rc::make_mut(callee),
                current,
                bound,
                resolution,
                scopes,
                effect_sites,
                errors,
            );
            for argument in Rc::make_mut(arguments) {
                rewrite_expression(
                    argument,
                    current,
                    bound,
                    resolution,
                    scopes,
                    effect_sites,
                    errors,
                );
            }
        }
        ExprKind::Perform { effect, args, .. } => {
            if let Some(spelling) = effect_sites.get(&(expression.span.start, expression.span.end))
            {
                *effect = Rc::from(spelling.as_str());
            } else {
                let name = effect.to_string();
                if let Some(definition) = resolve_definition(
                    resolution,
                    scopes,
                    current,
                    Namespace::Effect,
                    std::slice::from_ref(&name),
                    expression.span,
                    errors,
                ) {
                    *effect = Rc::from(resolution.backend_spelling(&definition));
                }
            }
            for argument in Rc::make_mut(args) {
                rewrite_expression(
                    argument,
                    current,
                    bound,
                    resolution,
                    scopes,
                    effect_sites,
                    errors,
                );
            }
        }
        ExprKind::Handle {
            computation,
            clauses,
        } => {
            rewrite_expression(
                Rc::make_mut(computation),
                current,
                bound,
                resolution,
                scopes,
                effect_sites,
                errors,
            );
            for clause in Rc::make_mut(clauses) {
                let effect = clause.effect.clone();
                if let Some(definition) = resolve_definition(
                    resolution,
                    scopes,
                    current,
                    Namespace::Effect,
                    std::slice::from_ref(&effect),
                    clause.span,
                    errors,
                ) {
                    clause.effect = resolution.backend_spelling(&definition);
                }
                let mut nested = bound.clone();
                for pattern in &mut clause.patterns {
                    rewrite_pattern(pattern, current, resolution, scopes, errors);
                    pattern_bindings(pattern, &mut nested);
                }
                if let Some(resumption) = &clause.resumption {
                    nested.insert(resumption.clone());
                }
                rewrite_expression(
                    &mut clause.body,
                    current,
                    &nested,
                    resolution,
                    scopes,
                    effect_sites,
                    errors,
                );
            }
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            rewrite_expression(
                Rc::make_mut(lhs),
                current,
                bound,
                resolution,
                scopes,
                effect_sites,
                errors,
            );
            rewrite_expression(
                Rc::make_mut(rhs),
                current,
                bound,
                resolution,
                scopes,
                effect_sites,
                errors,
            );
        }
        ExprKind::Is { subject, pattern } => {
            rewrite_expression(
                Rc::make_mut(subject),
                current,
                bound,
                resolution,
                scopes,
                effect_sites,
                errors,
            );
            rewrite_pattern(Rc::make_mut(pattern), current, resolution, scopes, errors);
        }
        ExprKind::Unit
        | ExprKind::Int(_)
        | ExprKind::Float(_)
        | ExprKind::String(_)
        | ExprKind::Char(_)
        | ExprKind::Byte(_)
        | ExprKind::ByteString(_)
        | ExprKind::LabelReference(_) => {}
    }
}

fn rewrite_where_clause(
    clause: Option<&mut crate::ast::WhereClause>,
    current: ModuleId,
    resolution: &mut ModuleResolution,
    scopes: &Scopes,
    errors: &mut Vec<Diagnostic>,
) {
    let Some(clause) = clause else { return };
    for goal in &mut clause.goals {
        rewrite_type(&mut goal.subject, current, resolution, scopes, errors);
        rewrite_trait_ref(&mut goal.relation, current, resolution, scopes, errors);
    }
}

fn rewrite_method(
    method: &mut crate::ast::TraitMethod,
    current: ModuleId,
    resolution: &mut ModuleResolution,
    scopes: &Scopes,
    effect_sites: &BTreeMap<(usize, usize), String>,
    errors: &mut Vec<Diagnostic>,
) {
    for parameter in &mut method.params {
        rewrite_type(&mut parameter.ty, current, resolution, scopes, errors);
    }
    if let Some(result) = &mut method.return_type {
        rewrite_type(result, current, resolution, scopes, errors);
    }
    if let Some(row) = &mut method.outward_effects {
        rewrite_effect_row(row, current, resolution, scopes, errors);
    }
    rewrite_where_clause(
        method.where_clause.as_mut(),
        current,
        resolution,
        scopes,
        errors,
    );
    if let Some(body) = &mut method.body {
        let bound = method
            .params
            .iter()
            .map(|parameter| parameter.name.clone())
            .chain(std::iter::once("self".to_string()))
            .collect();
        rewrite_expression(
            body,
            current,
            &bound,
            resolution,
            scopes,
            effect_sites,
            errors,
        );
    }
}

fn rewrite_program_ast(
    bundle: &SourceBundle,
    program: &mut Program,
    resolution: &mut ModuleResolution,
    scopes: &Scopes,
) -> Vec<Diagnostic> {
    let mut errors = Vec::new();
    resolution.syntax_path_spans.extend(
        program
            .name_paths
            .iter()
            .map(|entry| ((entry.site.start, entry.site.end), entry.path)),
    );
    let mut effect_sites = BTreeMap::new();
    for entry in &mut program.effect_paths {
        let Some(current) = resolution.owner(bundle, entry.site) else {
            continue;
        };
        let names = match &entry.effect.kind {
            crate::ast::TypeSyntaxKind::Path(path) => path_names(path),
            crate::ast::TypeSyntaxKind::Application { constructor, .. } => {
                let crate::ast::TypeSyntaxKind::Path(path) = &constructor.kind else {
                    continue;
                };
                path_names(path)
            }
            _ => continue,
        };
        let effect_path_span = match &entry.effect.kind {
            crate::ast::TypeSyntaxKind::Path(path) => syntax_path_span(path),
            crate::ast::TypeSyntaxKind::Application { constructor, .. } => {
                match &constructor.kind {
                    crate::ast::TypeSyntaxKind::Path(path) => syntax_path_span(path),
                    _ => None,
                }
            }
            _ => None,
        }
        .unwrap_or(entry.effect.span);
        if let Some(definition) = resolve_definition(
            resolution,
            scopes,
            current,
            Namespace::Effect,
            &names,
            effect_path_span,
            &mut errors,
        ) {
            let spelling = resolution.backend_spelling(&definition);
            resolution.resolved_paths.insert(
                (effect_path_span.start, effect_path_span.end),
                definition.clone(),
            );
            effect_sites.insert((entry.site.start, entry.site.end), spelling.clone());
            match &mut entry.effect.kind {
                crate::ast::TypeSyntaxKind::Path(path) => {
                    *path = vec![crate::ast::TypePathSegment {
                        name: spelling,
                        span: entry.effect.span,
                    }]
                }
                crate::ast::TypeSyntaxKind::Application { constructor, .. } => {
                    constructor.kind =
                        crate::ast::TypeSyntaxKind::Path(vec![crate::ast::TypePathSegment {
                            name: spelling,
                            span: constructor.span,
                        }]);
                }
                _ => unreachable!(),
            }
        }
    }

    for declaration in &mut program.type_aliases {
        let current = resolution
            .owner(bundle, declaration.span)
            .unwrap_or(ModuleId(0));
        rewrite_type(
            &mut declaration.target,
            current,
            resolution,
            scopes,
            &mut errors,
        );
    }
    for declaration in &mut program.effect_row_aliases {
        let current = resolution
            .owner(bundle, declaration.span)
            .unwrap_or(ModuleId(0));
        rewrite_effect_row(
            &mut declaration.row,
            current,
            resolution,
            scopes,
            &mut errors,
        );
    }
    for declaration in &mut program.structs {
        let current = resolution
            .owner(bundle, declaration.span)
            .unwrap_or(ModuleId(0));
        for field in &mut declaration.fields {
            rewrite_type(&mut field.ty, current, resolution, scopes, &mut errors);
        }
    }
    for declaration in &mut program.enums {
        let current = resolution
            .owner(bundle, declaration.span)
            .unwrap_or(ModuleId(0));
        for field in declaration
            .variants
            .iter_mut()
            .flat_map(|variant| &mut variant.fields)
        {
            rewrite_type(field, current, resolution, scopes, &mut errors);
        }
    }
    for declaration in &mut program.effects {
        let current = resolution
            .owner(bundle, declaration.span)
            .unwrap_or(ModuleId(0));
        for operation in &mut declaration.operations {
            for parameter in &mut operation.params {
                rewrite_type(&mut parameter.ty, current, resolution, scopes, &mut errors);
            }
            if let Some(result) = &mut operation.return_type {
                rewrite_type(result, current, resolution, scopes, &mut errors);
            }
        }
    }
    for declaration in &mut program.traits {
        let current = resolution
            .owner(bundle, declaration.span)
            .unwrap_or(ModuleId(0));
        for relation in &mut declaration.supertraits {
            rewrite_trait_ref(relation, current, resolution, scopes, &mut errors);
        }
        for method in &mut declaration.methods {
            rewrite_method(
                method,
                current,
                resolution,
                scopes,
                &effect_sites,
                &mut errors,
            );
        }
    }
    for declaration in &mut program.impls {
        let current = resolution
            .owner(bundle, declaration.span)
            .unwrap_or(ModuleId(0));
        rewrite_type(
            &mut declaration.self_ty,
            current,
            resolution,
            scopes,
            &mut errors,
        );
        rewrite_trait_ref(
            &mut declaration.trait_ref,
            current,
            resolution,
            scopes,
            &mut errors,
        );
        rewrite_where_clause(
            declaration.where_clause.as_mut(),
            current,
            resolution,
            scopes,
            &mut errors,
        );
        for associated in &mut declaration.associated_types {
            match &mut associated.value {
                crate::ast::AssociatedBindingValue::Type(value) => {
                    rewrite_type(value, current, resolution, scopes, &mut errors)
                }
                crate::ast::AssociatedBindingValue::EffectRow(row) => {
                    rewrite_effect_row(row, current, resolution, scopes, &mut errors)
                }
            }
        }
        for method in &mut declaration.methods {
            rewrite_method(
                method,
                current,
                resolution,
                scopes,
                &effect_sites,
                &mut errors,
            );
        }
    }
    for declaration in &mut program.uses {
        let current = resolution
            .owner(bundle, declaration.span)
            .unwrap_or(ModuleId(0));
        rewrite_type(
            &mut declaration.target,
            current,
            resolution,
            scopes,
            &mut errors,
        );
        rewrite_where_clause(
            declaration.where_clause.as_mut(),
            current,
            resolution,
            scopes,
            &mut errors,
        );
    }
    for declaration in &mut program.drops {
        let current = resolution
            .owner(bundle, declaration.span)
            .unwrap_or(ModuleId(0));
        rewrite_type(
            &mut declaration.target_type,
            current,
            resolution,
            scopes,
            &mut errors,
        );
        rewrite_where_clause(
            declaration.where_clause.as_mut(),
            current,
            resolution,
            scopes,
            &mut errors,
        );
        rewrite_expression(
            &mut declaration.body,
            current,
            &BTreeSet::from(["self".to_string()]),
            resolution,
            scopes,
            &effect_sites,
            &mut errors,
        );
    }
    for declaration in &mut program.globals {
        let current = resolution
            .owner(bundle, declaration.span)
            .unwrap_or(ModuleId(0));
        rewrite_expression(
            &mut declaration.value,
            current,
            &BTreeSet::new(),
            resolution,
            scopes,
            &effect_sites,
            &mut errors,
        );
    }
    for function in &mut program.functions {
        let current = resolution
            .owner(bundle, function.span)
            .unwrap_or(ModuleId(0));
        for parameter in &mut function.params {
            rewrite_type(&mut parameter.ty, current, resolution, scopes, &mut errors);
        }
        if let Some(result) = &mut function.return_type {
            rewrite_type(result, current, resolution, scopes, &mut errors);
        }
        if let Some(row) = &mut function.outward_effects {
            rewrite_effect_row(row, current, resolution, scopes, &mut errors);
        }
        rewrite_where_clause(
            function.where_clause.as_mut(),
            current,
            resolution,
            scopes,
            &mut errors,
        );
        let bound = function
            .params
            .iter()
            .map(|parameter| parameter.name.clone())
            .collect();
        rewrite_expression(
            &mut function.body,
            current,
            &bound,
            resolution,
            scopes,
            &effect_sites,
            &mut errors,
        );
    }

    // Declarations are renamed last so every lookup above uses source names.
    for declaration in &mut program.type_aliases {
        if let Some(definition) = resolution.definition_at(declaration.span) {
            declaration.name = resolution.backend_spelling(definition);
        }
    }
    for declaration in &mut program.effect_row_aliases {
        if let Some(definition) = resolution.definition_at(declaration.span) {
            declaration.name = resolution.backend_spelling(definition);
        }
    }
    for declaration in &mut program.structs {
        if let Some(definition) = resolution.definition_at(declaration.span) {
            declaration.name = resolution.backend_spelling(definition);
        }
    }
    for declaration in &mut program.enums {
        if let Some(definition) = resolution.definition_at(declaration.span) {
            declaration.name = resolution.backend_spelling(definition);
        }
    }
    for declaration in &mut program.effects {
        if let Some(definition) = resolution.definition_at(declaration.span) {
            declaration.name = resolution.backend_spelling(definition);
        }
    }
    for declaration in &mut program.traits {
        if let Some(definition) = resolution.definition_at(declaration.span) {
            declaration.name = resolution.backend_spelling(definition);
        }
    }
    for declaration in &mut program.functions {
        if let Some(definition) = resolution.definition_at(declaration.span) {
            declaration.name = resolution.backend_spelling(definition);
        }
    }
    for declaration in &mut program.globals {
        if declaration.owner.is_none()
            && let Some(definition) = resolution.definition_at(declaration.span)
        {
            declaration.name = resolution.backend_spelling(definition);
        }
    }
    errors
}

fn local_definitions(resolution: &ModuleResolution, module: ModuleId, name: &str) -> Vec<DefId> {
    resolution
        .definitions
        .keys()
        .filter(|definition| definition.module == module && definition.name == name)
        .cloned()
        .collect()
}

fn import_specs(
    bundle: &SourceBundle,
    program: &Program,
    resolution: &ModuleResolution,
) -> Vec<ImportSpec> {
    let mut specs = Vec::new();
    for import in &program.imports {
        let Some(owner) = resolution.owner(bundle, import.span) else {
            continue;
        };
        let mut leaves = Vec::new();
        flatten_import(&import.tree, &mut Vec::new(), &mut leaves);
        specs.extend(leaves.into_iter().map(|leaf| ImportSpec {
            owner,
            public: import.visibility == Visibility::Public,
            leaf,
        }));
    }
    specs
}

fn build_scopes(
    bundle: &SourceBundle,
    program: &Program,
    resolution: &ModuleResolution,
) -> Result<Scopes, Vec<Diagnostic>> {
    let mut scopes = Scopes::default();
    for definition in resolution.definitions.keys() {
        scopes
            .definitions
            .entry((
                definition.module,
                definition.namespace,
                definition.name.clone(),
            ))
            .or_default()
            .insert(Binding {
                definition: definition.clone(),
                public: resolution.is_public(definition),
            });
    }
    for module in resolution.modules.iter().skip(1) {
        let owner = module.parent.unwrap_or(ModuleId(0));
        scopes
            .modules
            .entry((owner, module.name.clone()))
            .or_default()
            .insert(ModuleBinding {
                module: module.id,
                public: module.public,
            });
    }
    let specs = import_specs(bundle, program, resolution);
    let mut unresolved = BTreeSet::from_iter(0..specs.len());
    loop {
        let mut changed = false;
        let mut resolved_now = Vec::new();
        for &index in &unresolved {
            let spec = &specs[index];
            match &spec.leaf {
                ImportLeaf::Name { path, alias, .. } => {
                    let Some((name, prefix)) = path.split_last() else {
                        continue;
                    };
                    let modules = resolve_module_path(resolution, &scopes, spec.owner, prefix);
                    if modules.len() != 1 {
                        continue;
                    }
                    let target_module = *modules.first().unwrap();
                    let child = child_modules(resolution, target_module, name);
                    let definitions = local_definitions(resolution, target_module, name);
                    if child.is_empty() && definitions.is_empty() {
                        continue;
                    }
                    let mut visible = false;
                    for module in child {
                        if !module_visible_from(resolution, module, spec.owner) {
                            continue;
                        }
                        visible = true;
                        changed |= scopes
                            .modules
                            .entry((spec.owner, alias.clone()))
                            .or_default()
                            .insert(ModuleBinding {
                                module,
                                public: spec.public,
                            });
                    }
                    for definition in definitions {
                        if !definition_visible_from(resolution, &definition, spec.owner) {
                            continue;
                        }
                        visible = true;
                        changed |= scopes
                            .definitions
                            .entry((spec.owner, definition.namespace, alias.clone()))
                            .or_default()
                            .insert(Binding {
                                definition,
                                public: spec.public,
                            });
                    }
                    if visible {
                        resolved_now.push(index);
                    }
                }
                ImportLeaf::ModuleSelf { path, alias, .. } => {
                    let modules = resolve_module_path(resolution, &scopes, spec.owner, path);
                    if modules.len() != 1 {
                        continue;
                    }
                    let module = *modules.first().unwrap();
                    if !module_visible_from(resolution, module, spec.owner) {
                        continue;
                    }
                    let name = alias
                        .clone()
                        .unwrap_or_else(|| resolution.module(module).name.clone());
                    changed |= scopes
                        .modules
                        .entry((spec.owner, name))
                        .or_default()
                        .insert(ModuleBinding {
                            module,
                            public: spec.public,
                        });
                    resolved_now.push(index);
                }
                ImportLeaf::Glob { path, .. } => {
                    let modules = resolve_module_path(resolution, &scopes, spec.owner, path);
                    if modules.len() != 1 {
                        continue;
                    }
                    let module = *modules.first().unwrap();
                    let definition_exports = scopes
                        .definitions
                        .iter()
                        .filter(|((owner, _, _), _)| *owner == module)
                        .flat_map(|((_, namespace, name), bindings)| {
                            bindings
                                .iter()
                                .filter(|binding| binding.public)
                                .map(move |binding| (*namespace, name.clone(), binding.clone()))
                        })
                        .collect::<Vec<_>>();
                    for (namespace, name, binding) in definition_exports {
                        changed |= scopes
                            .definitions
                            .entry((spec.owner, namespace, name))
                            .or_default()
                            .insert(Binding {
                                definition: binding.definition,
                                public: spec.public,
                            });
                    }
                    let module_exports = scopes
                        .modules
                        .iter()
                        .filter(|((owner, _), _)| *owner == module)
                        .flat_map(|((_, name), bindings)| {
                            bindings
                                .iter()
                                .filter(|binding| binding.public)
                                .map(move |binding| (name.clone(), *binding))
                        })
                        .collect::<Vec<_>>();
                    for (name, binding) in module_exports {
                        changed |= scopes
                            .modules
                            .entry((spec.owner, name))
                            .or_default()
                            .insert(ModuleBinding {
                                module: binding.module,
                                public: spec.public,
                            });
                    }
                    resolved_now.push(index);
                }
            }
        }
        for index in resolved_now {
            unresolved.remove(&index);
        }
        if !changed {
            break;
        }
    }
    let mut errors = Vec::new();
    for index in unresolved {
        let (span, path) = match &specs[index].leaf {
            ImportLeaf::Name { path, span, .. }
            | ImportLeaf::ModuleSelf { path, span, .. }
            | ImportLeaf::Glob { path, span } => (*span, path.join("::")),
        };
        errors.push(error(
            span,
            format!("import `{path}` is unresolved, ambiguous, private, or part of an unresolved import cycle"),
        ));
    }
    if errors.is_empty() {
        Ok(scopes)
    } else {
        Err(errors)
    }
}

pub fn fixity_regions(
    bundle: &SourceBundle,
    program: &Program,
) -> Result<Vec<crate::parser::FixityRegion>, Vec<Diagnostic>> {
    if program.modules.is_empty()
        && program.imports.is_empty()
        && !bundle
            .segments()
            .iter()
            .any(|segment| segment.package_root().is_some())
    {
        return Ok(Vec::new());
    }
    let mut resolution = build_graph(bundle, program)?;
    let errors = collect_definitions(bundle, program, &mut resolution);
    if !errors.is_empty() {
        return Err(errors);
    }
    let scopes = build_scopes(bundle, program, &resolution)?;
    let declarations = program
        .fixities
        .iter()
        .map(|fixity| ((fixity.span.start, fixity.span.end), fixity))
        .collect::<BTreeMap<_, _>>();
    let mut maps = BTreeMap::<ModuleId, HashMap<String, crate::parser::ScopedFixity>>::new();
    let mut errors = Vec::new();
    for module in &resolution.modules {
        let root = package_root(&resolution, module.id);
        let mut names = BTreeSet::new();
        names.extend(
            scopes
                .definitions
                .keys()
                .filter(|(owner, namespace, _)| {
                    *namespace == Namespace::Fixity && (*owner == module.id || *owner == root)
                })
                .map(|(_, _, name)| name.clone()),
        );
        names.extend(
            scopes
                .definitions
                .iter()
                .filter(|((owner, namespace, _), bindings)| {
                    *owner == ModuleId(0)
                        && *namespace == Namespace::Fixity
                        && bindings.iter().any(|binding| {
                            resolution.prelude_definitions.contains(&binding.definition)
                        })
                })
                .map(|((_, _, name), _)| name.clone()),
        );
        for name in names {
            let local = scopes
                .definitions
                .get(&(module.id, Namespace::Fixity, name.clone()));
            let root_binding = scopes
                .definitions
                .get(&(root, Namespace::Fixity, name.clone()));
            let prelude_binding = scopes
                .definitions
                .get(&(ModuleId(0), Namespace::Fixity, name.clone()))
                .filter(|bindings| {
                    bindings
                        .iter()
                        .any(|binding| resolution.prelude_definitions.contains(&binding.definition))
                });
            let bindings = local
                .or(root_binding)
                .or(prelude_binding)
                .into_iter()
                .flatten()
                .filter(|binding| {
                    local.is_some()
                        || root_binding.is_some()
                        || resolution.prelude_definitions.contains(&binding.definition)
                })
                .collect::<Vec<_>>();
            let definitions = bindings
                .iter()
                .map(|binding| &binding.definition)
                .collect::<BTreeSet<_>>();
            if definitions.len() != 1 {
                let span = bindings
                    .first()
                    .and_then(|binding| resolution.definitions.get(&binding.definition))
                    .copied()
                    .unwrap_or(Span::new(0, 0));
                errors.push(error(
                    span,
                    format!("operator fixity `{name}` is ambiguous in this module"),
                ));
                continue;
            }
            let definition = definitions.into_iter().next().unwrap();
            let declaration_span = resolution.definitions[definition];
            let Some(declaration) =
                declarations.get(&(declaration_span.start, declaration_span.end))
            else {
                continue;
            };
            maps.entry(module.id).or_default().insert(
                name,
                crate::parser::ScopedFixity {
                    kind: declaration.kind,
                    precedence: declaration.precedence,
                    declaration: Some(declaration.span),
                },
            );
        }
    }
    if !errors.is_empty() {
        return Err(errors);
    }
    let mut regions = Vec::new();
    for segment in bundle.segments() {
        if let Some(module) = resolution.segment_modules.get(&segment.id().unwrap()) {
            regions.push(crate::parser::FixityRegion {
                span: Span::new(segment.global_range().start, segment.global_range().end),
                fixities: maps.get(module).cloned().unwrap_or_default(),
            });
        }
    }
    for (span, module) in &resolution.inline_scopes {
        regions.push(crate::parser::FixityRegion {
            span: *span,
            fixities: maps.get(module).cloned().unwrap_or_default(),
        });
    }
    Ok(regions)
}

pub fn parse_bundle(bundle: &SourceBundle) -> Result<Program, Vec<Diagnostic>> {
    let tokens = crate::lexer::lex(bundle.source()).map_err(|error| vec![error])?;
    let (probe, diagnostics) = crate::parser::parse_recovering(tokens.clone());
    if !diagnostics.is_empty() {
        return Err(diagnostics);
    }
    if probe.modules.is_empty() {
        return Ok(probe);
    }
    let regions = fixity_regions(bundle, &probe)?;
    let (program, diagnostics) =
        crate::parser::parse_recovering_with_fixity_regions(tokens, regions);
    if diagnostics.is_empty() {
        Ok(program)
    } else {
        Err(diagnostics)
    }
}

fn normalized(path: &Path) -> PathBuf {
    let mut result = PathBuf::new();
    for component in path.components() {
        match component {
            Component::CurDir => {}
            Component::ParentDir => {
                result.pop();
            }
            other => result.push(other.as_os_str()),
        }
    }
    result
}

fn contains(container: Span, nested: Span) -> bool {
    container.start <= nested.start && nested.end <= container.end
}

fn owner_for_span(
    span: Span,
    bundle: &SourceBundle,
    segment_owners: &BTreeMap<SegmentId, ModuleId>,
    inline_modules: &[(Span, ModuleId)],
) -> Option<ModuleId> {
    let segment = bundle.segment_at(span.start)?.id()?;
    let base = *segment_owners.get(&segment)?;
    inline_modules
        .iter()
        .filter(|(body, _)| contains(*body, span))
        .min_by_key(|(body, _)| body.end.saturating_sub(body.start))
        .map_or(Some(base), |(_, module)| Some(*module))
}

fn error(span: Span, message: impl Into<String>) -> Diagnostic {
    Diagnostic::error("module resolution failed", message, span).with_code(MODULE_CODE)
}

fn package_alias(name: &str) -> Option<String> {
    let alias = name.replace('-', "_");
    let mut characters = alias.chars();
    let first = characters.next()?;
    (first == '_' || first.is_ascii_alphabetic())
        .then_some(())
        .filter(|_| {
            characters.all(|character| character == '_' || character.is_ascii_alphanumeric())
        })
        .map(|()| alias)
}

/// Builds the physical/logical module graph. Name resolution and AST rewriting
/// are layered on this graph so filesystem layout never becomes symbol identity.
pub fn build_graph(
    bundle: &SourceBundle,
    program: &Program,
) -> Result<ModuleResolution, Vec<Diagnostic>> {
    let user_segments = bundle
        .segments()
        .iter()
        .filter(|segment| segment.id() != bundle.trusted_standard_segment_id())
        .collect::<Vec<_>>();
    let Some(primary) = user_segments.first() else {
        return Ok(ModuleResolution::default());
    };
    let root_dir = Path::new(primary.name())
        .parent()
        .unwrap_or_else(|| Path::new(""))
        .to_path_buf();
    let mut resolution = ModuleResolution {
        modules: vec![ModuleInfo {
            id: ModuleId(0),
            parent: None,
            name: "crate".into(),
            path: Vec::new(),
            declaration: None,
            segment: primary.id(),
            public: true,
            physical_dir: root_dir,
        }],
        ..ModuleResolution::default()
    };
    let mut segment_owners = BTreeMap::new();
    segment_owners.insert(primary.id().expect("assembled segment"), ModuleId(0));
    let mut claimed_segments = BTreeSet::from([primary.id().expect("assembled segment")]);
    let mut errors = Vec::new();
    let mut package_aliases = BTreeMap::<String, (Span, String)>::new();
    for segment in user_segments.iter().skip(1) {
        let Some(package) = segment.package_root() else {
            continue;
        };
        let span = Span::new(segment.global_range().start, segment.global_range().start);
        let Some(alias) = package_alias(package) else {
            errors.push(error(
                span,
                format!(
                    "dependency package name `{package}` does not normalize to a valid identifier"
                ),
            ));
            continue;
        };
        if let Some((previous, previous_name)) = package_aliases.get(&alias) {
            errors.push(
                error(
                    span,
                    format!(
                        "dependency package names `{previous_name}` and `{package}` both normalize to `{alias}`"
                    ),
                )
                .with_related(*previous, "the first dependency root is here"),
            );
            continue;
        }
        package_aliases.insert(alias.clone(), (span, package.to_owned()));
        let id = ModuleId(resolution.modules.len() as u32);
        let physical_dir = Path::new(segment.name())
            .parent()
            .unwrap_or_else(|| Path::new(""))
            .to_path_buf();
        resolution.modules.push(ModuleInfo {
            id,
            parent: None,
            name: alias.clone(),
            path: vec![alias],
            declaration: None,
            segment: segment.id(),
            public: true,
            physical_dir,
        });
        let segment_id = segment.id().expect("assembled segment");
        segment_owners.insert(segment_id, id);
        claimed_segments.insert(segment_id);
    }
    let standard = bundle.trusted_standard_segment_id().and_then(|trusted| {
        bundle
            .segments()
            .iter()
            .find(|segment| segment.id() == Some(trusted))
    });
    if let Some(standard) = standard {
        segment_owners.insert(standard.id().expect("assembled segment"), ModuleId(0));
    }
    if !errors.is_empty() {
        return Err(errors);
    }
    if program.modules.is_empty() {
        for segment in user_segments.iter().skip(1) {
            if segment.package_root().is_none() {
                segment_owners.insert(segment.id().expect("assembled segment"), ModuleId(0));
            }
        }
        resolution.segment_modules = segment_owners;
        return Ok(resolution);
    }

    let paths = user_segments
        .iter()
        .map(|segment| (normalized(Path::new(segment.name())), *segment))
        .collect::<BTreeMap<_, _>>();
    let mut assigned = vec![None; program.modules.len()];
    let mut inline_modules: Vec<(Span, ModuleId)> = Vec::new();
    loop {
        let mut changed = false;
        for (index, declaration) in program.modules.iter().enumerate() {
            if assigned[index].is_some() {
                continue;
            }
            let Some(parent) =
                owner_for_span(declaration.span, bundle, &segment_owners, &inline_modules)
            else {
                continue;
            };
            let parent_info = resolution.module(parent).clone();
            let (segment, physical_dir) = match declaration.kind {
                ModuleKind::Inline { .. } => (
                    parent_info.segment,
                    parent_info.physical_dir.join(&declaration.name),
                ),
                ModuleKind::External => {
                    let directory = parent_info.physical_dir.join(&declaration.name);
                    let expected =
                        normalized(&directory.join(format!("{}.glorious", declaration.name)));
                    let Some(segment) = paths.get(&expected) else {
                        errors.push(error(
                            declaration.name_span,
                            format!(
                                "external module `{}` requires `{}`",
                                declaration.name,
                                expected.display()
                            ),
                        ));
                        assigned[index] = Some(ModuleId(u32::MAX));
                        changed = true;
                        continue;
                    };
                    let segment_id = segment.id().expect("assembled segment");
                    if !claimed_segments.insert(segment_id) {
                        errors.push(error(
                            declaration.name_span,
                            format!(
                                "physical module `{}` is declared more than once",
                                segment.name()
                            ),
                        ));
                    }
                    segment_owners.insert(segment_id, ModuleId(resolution.modules.len() as u32));
                    (Some(segment_id), directory)
                }
            };
            let id = ModuleId(resolution.modules.len() as u32);
            let mut path = parent_info.path;
            path.push(declaration.name.clone());
            resolution.modules.push(ModuleInfo {
                id,
                parent: Some(parent),
                name: declaration.name.clone(),
                path,
                declaration: Some(declaration.span),
                segment,
                public: declaration.visibility == Visibility::Public,
                physical_dir,
            });
            if let ModuleKind::Inline { body } = declaration.kind {
                inline_modules.push((body, id));
            }
            assigned[index] = Some(id);
            changed = true;
        }
        if !changed {
            break;
        }
    }

    for (index, module) in program.modules.iter().enumerate() {
        if assigned[index].is_none() {
            errors.push(error(
                module.span,
                format!(
                    "module `{}` belongs to an unclaimed source file",
                    module.name
                ),
            ));
        }
    }
    let mut sibling_names = BTreeMap::new();
    for module in resolution
        .modules
        .iter()
        .filter(|module| module.parent.is_some())
    {
        let key = (
            module.parent.expect("non-root module"),
            module.name.as_str(),
        );
        if let Some(previous) = sibling_names.insert(key, module.declaration.unwrap()) {
            errors.push(
                error(
                    module.declaration.unwrap(),
                    format!(
                        "module `{}` is declared more than once in this scope",
                        module.name
                    ),
                )
                .with_related(previous, "the first module declaration is here"),
            );
        }
        if module.parent == Some(ModuleId(0))
            && let Some((dependency, package)) = package_aliases.get(&module.name)
        {
            errors.push(
                error(
                    module.declaration.unwrap(),
                    format!(
                        "root module `{}` conflicts with dependency package `{package}` using the same import alias",
                        module.name
                    ),
                )
                .with_related(*dependency, "the dependency root is here"),
            );
        }
    }
    for segment in user_segments.iter().skip(1) {
        let id = segment.id().expect("assembled segment");
        if !claimed_segments.contains(&id) {
            errors.push(error(
                Span::new(segment.global_range().start, segment.global_range().start),
                format!(
                    "source file `{}` is not declared by any `mod` item",
                    segment.name()
                ),
            ));
        }
    }
    if errors.is_empty() {
        resolution.segment_modules = segment_owners;
        resolution.inline_scopes = inline_modules;
        Ok(resolution)
    } else {
        Err(errors)
    }
}

fn insert_definition(
    bundle: &SourceBundle,
    program: &Program,
    resolution: &mut ModuleResolution,
    namespace: Namespace,
    name: &str,
    span: Span,
    errors: &mut Vec<Diagnostic>,
) {
    let Some(module) = resolution.owner(bundle, span) else {
        errors.push(error(span, "declaration belongs to no resolved module"));
        return;
    };
    let definition = DefId {
        module,
        namespace,
        name: name.to_string(),
    };
    if let Some(previous) = resolution.definitions.insert(definition.clone(), span) {
        errors.push(
            error(
                span,
                format!("`{name}` is declared more than once in the same {namespace:?} namespace"),
            )
            .with_related(previous, "the first declaration is here"),
        );
        return;
    }
    let public = module == ModuleId(0) || program.visibility(span) == Visibility::Public;
    resolution
        .definition_public
        .insert(definition.clone(), public);
    resolution
        .declaration_defs
        .insert((span.start, span.end), definition);
}

fn collect_definitions(
    bundle: &SourceBundle,
    program: &Program,
    resolution: &mut ModuleResolution,
) -> Vec<Diagnostic> {
    let mut errors = Vec::new();
    for declaration in &program.type_aliases {
        insert_definition(
            bundle,
            program,
            resolution,
            Namespace::Type,
            &declaration.name,
            declaration.span,
            &mut errors,
        );
    }
    for declaration in &program.effect_row_aliases {
        insert_definition(
            bundle,
            program,
            resolution,
            Namespace::Effect,
            &declaration.name,
            declaration.span,
            &mut errors,
        );
    }
    for declaration in &program.structs {
        insert_definition(
            bundle,
            program,
            resolution,
            Namespace::Type,
            &declaration.name,
            declaration.span,
            &mut errors,
        );
    }
    for declaration in &program.enums {
        insert_definition(
            bundle,
            program,
            resolution,
            Namespace::Type,
            &declaration.name,
            declaration.span,
            &mut errors,
        );
    }
    for declaration in &program.traits {
        insert_definition(
            bundle,
            program,
            resolution,
            Namespace::Trait,
            &declaration.name,
            declaration.span,
            &mut errors,
        );
    }
    for declaration in &program.effects {
        insert_definition(
            bundle,
            program,
            resolution,
            Namespace::Effect,
            &declaration.name,
            declaration.span,
            &mut errors,
        );
    }
    for declaration in &program.functions {
        insert_definition(
            bundle,
            program,
            resolution,
            Namespace::Value,
            &declaration.name,
            declaration.span,
            &mut errors,
        );
    }
    for declaration in &program.globals {
        if declaration.owner.is_none() {
            insert_definition(
                bundle,
                program,
                resolution,
                Namespace::Value,
                &declaration.name,
                declaration.span,
                &mut errors,
            );
        }
    }
    for declaration in &program.fixities {
        insert_definition(
            bundle,
            program,
            resolution,
            Namespace::Fixity,
            &declaration.name,
            declaration.span,
            &mut errors,
        );
    }
    if let Some(trusted) = bundle.trusted_standard_segment_id() {
        resolution.prelude_definitions = resolution
            .definitions
            .iter()
            .filter(|(_, span)| {
                bundle
                    .segment_at(span.start)
                    .is_some_and(|segment| segment.id() == Some(trusted))
            })
            .map(|(definition, _)| definition.clone())
            .collect();
    }
    errors
}

pub fn resolve_program(
    bundle: &SourceBundle,
    program: Program,
) -> Result<ResolvedProgram, Vec<Diagnostic>> {
    resolve_program_impl(bundle, program, false)
}

/// Tooling needs resolved occurrence identities even for the pre-module flat
/// source surface. Normal compilation retains its compatibility fast path;
/// this entry point only asks the same resolver to populate semantic tables.
pub(crate) fn resolve_program_for_interfaces(
    bundle: &SourceBundle,
    program: Program,
) -> Result<ResolvedProgram, Vec<Diagnostic>> {
    resolve_program_impl(bundle, program, true)
}

fn resolve_program_impl(
    bundle: &SourceBundle,
    mut program: Program,
    force_semantic_tables: bool,
) -> Result<ResolvedProgram, Vec<Diagnostic>> {
    if !force_semantic_tables
        && program.modules.is_empty()
        && program.imports.is_empty()
        && !bundle
            .segments()
            .iter()
            .any(|segment| segment.package_root().is_some())
    {
        return Ok(ResolvedProgram {
            resolution: build_graph(bundle, &program)?,
            program,
        });
    }
    let mut resolution = build_graph(bundle, &program)?;
    let mut errors = collect_definitions(bundle, &program, &mut resolution);
    if errors.is_empty() {
        match build_scopes(bundle, &program, &resolution) {
            Ok(scopes) => errors.append(&mut rewrite_program_ast(
                bundle,
                &mut program,
                &mut resolution,
                &scopes,
            )),
            Err(mut import_errors) => errors.append(&mut import_errors),
        }
    }
    if errors.is_empty() {
        Ok(ResolvedProgram {
            program,
            resolution,
        })
    } else {
        Err(errors)
    }
}
