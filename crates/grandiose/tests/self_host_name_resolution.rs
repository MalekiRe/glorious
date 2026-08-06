use std::{
    collections::{BTreeMap, BTreeSet},
    ffi::OsString,
    fs,
    path::{Path, PathBuf},
    process::Command,
};

use grandiose::{
    CompileOptions, LlvmOptions, OptimizationLevel,
    ast::{Expr, ExprKind, Function, PatternKind, Program, Stmt},
    modules::{ModuleId, ModuleResolution},
    source_bundle::{Segment, SourceBundle},
};
use grandiose_vm::{SystemHost, Value, Vm, verify};

fn repository_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_owned()
}

fn self_host_bundle() -> SourceBundle {
    self_host_bundle_for("probe::resolution::application")
}

fn self_host_generic_bundle() -> SourceBundle {
    self_host_bundle_for("probe::resolution::generic_application")
}

fn self_host_module_bundle() -> SourceBundle {
    self_host_bundle_for("probe::resolution::module_application")
}

fn self_host_bundle_for(entry: &str) -> SourceBundle {
    let root = repository_root().join("self-host/src");
    let primary = Segment::new(
        root.join("main.glorious").to_string_lossy(),
        format!(
            "mod frontend;\nmod probe;\n\nmain() {{ run_compiler_host({entry}) }}\n"
        ),
    );
    let paths = [
        root.join("frontend/frontend.glorious"),
        root.join("frontend/lexer/lexer.glorious"),
        root.join("frontend/scanner/scanner.glorious"),
        root.join("frontend/headers/headers.glorious"),
        root.join("frontend/bodies/bodies.glorious"),
        root.join("frontend/resolution/resolution.glorious"),
        root.join("probe/probe.glorious"),
        root.join("probe/resolution/resolution.glorious"),
    ];
    SourceBundle::distributed(
        primary,
        paths.into_iter().map(|path| {
            let mut source = fs::read_to_string(&path)
                .unwrap()
                .replace("pub mod lossless;\n", "")
                .replace("pub mod elaboration;\n", "");
            if path.ends_with("probe/probe.glorious") {
                source = source
                    .replace("pub mod lexer;\n", "")
                    .replace("pub mod scanner;\n", "")
                    .replace("pub mod headers;\n", "")
                    .replace("pub mod bodies;\n", "");
            }
            Segment::new(path.to_string_lossy(), source)
        }),
    )
}

fn encode_rust_generic_resolution(output: &mut Vec<u8>, source: &str) {
    let bundle = raw_source_bundle(source);
    let program = grandiose::modules::parse_bundle(&bundle).unwrap();
    push_u32(output, program.functions.len().try_into().unwrap());
    for function in &program.functions {
        push_string(output, &function.name);
        let generics = function.generics.as_ref();
        push_u32(
            output,
            generics
                .map_or(0, |value| value.params.len())
                .try_into()
                .unwrap(),
        );
        for (ordinal, parameter) in generics
            .into_iter()
            .flat_map(|value| &value.params)
            .enumerate()
        {
            let kind = match parameter.kind {
                grandiose::ast::GenericParamKind::Type => 1,
                grandiose::ast::GenericParamKind::Lifetime => 2,
                grandiose::ast::GenericParamKind::EffectRow => 3,
                grandiose::ast::GenericParamKind::Const(_) => 4,
            };
            output.push(kind);
            push_string(output, &parameter.name);
            push_u32(output, parameter.span.start.try_into().unwrap());
            output.push(match parameter.kind {
                grandiose::ast::GenericParamKind::Type => 1,
                grandiose::ast::GenericParamKind::EffectRow => 2,
                grandiose::ast::GenericParamKind::Lifetime => 0,
                grandiose::ast::GenericParamKind::Const(_) => 0,
            });
            push_u32(output, ordinal.try_into().unwrap());
        }
    }
}

fn push_u32(output: &mut Vec<u8>, value: u32) {
    output.extend(value.to_le_bytes());
}

fn push_string(output: &mut Vec<u8>, value: &str) {
    push_u32(output, value.len().try_into().unwrap());
    output.extend(value.as_bytes());
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct FunctionIdentity {
    module: ModuleId,
    path: Vec<String>,
    name: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Binding {
    kind: u8,
    name: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Target {
    Local(u32),
    Function(FunctionIdentity),
    Struct(u32),
    Variant(u32),
    EffectOperation(FunctionIdentity, u32),
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Occurrence {
    spelling: String,
    target: Target,
}

#[derive(Default)]
struct FunctionResolution {
    bindings: Vec<Binding>,
    occurrences: Vec<Occurrence>,
}

fn raw_source_bundle(source: &str) -> SourceBundle {
    SourceBundle::raw_with_trusted_standard_for_conformance(
        Segment::new("<empty-std>", ""),
        Segment::new("name-resolution-input.glorious", source),
        [],
    )
}

fn function_identity(
    graph: &ModuleResolution,
    bundle: &SourceBundle,
    function: &Function,
) -> Result<FunctionIdentity, ()> {
    let module = graph.owner(bundle, function.span).ok_or(())?;
    Ok(FunctionIdentity {
        module,
        path: graph.module(module).path.clone(),
        name: function.name.clone(),
    })
}

fn function_table(
    graph: &ModuleResolution,
    bundle: &SourceBundle,
    program: &Program,
) -> Result<BTreeMap<(ModuleId, String), FunctionIdentity>, ()> {
    let mut functions = BTreeMap::new();
    for function in &program.functions {
        let identity = function_identity(graph, bundle, function)?;
        if functions
            .insert((identity.module, identity.name.clone()), identity)
            .is_some()
        {
            return Err(());
        }
    }
    Ok(functions)
}

struct Resolver<'a> {
    current_module: ModuleId,
    functions: &'a BTreeMap<(ModuleId, String), FunctionIdentity>,
    structs: &'a BTreeMap<String, u32>,
    variants: &'a BTreeMap<(String, String), u32>,
    effects: &'a BTreeMap<(ModuleId, String), (FunctionIdentity, Vec<String>)>,
    result: FunctionResolution,
}

impl Resolver<'_> {
    fn define(&mut self, kind: u8, name: &str) -> Result<u32, ()> {
        let id = u32::try_from(self.result.bindings.len()).map_err(|_| ())?;
        self.result.bindings.push(Binding {
            kind,
            name: name.to_owned(),
        });
        Ok(id)
    }

    fn function(&self, name: &str) -> Option<FunctionIdentity> {
        self.functions
            .get(&(self.current_module, name.to_owned()))
            .or_else(|| {
                (self.current_module != ModuleId(0))
                    .then(|| self.functions.get(&(ModuleId(0), name.to_owned())))
                    .flatten()
            })
            .cloned()
    }

    fn effect(&self, name: &str) -> Option<(FunctionIdentity, Vec<String>)> {
        self.effects
            .get(&(self.current_module, name.to_owned()))
            .or_else(|| {
                (self.current_module != ModuleId(0))
                    .then(|| self.effects.get(&(ModuleId(0), name.to_owned())))
                    .flatten()
            })
            .cloned()
    }

    fn variable(
        &mut self,
        path: &[std::rc::Rc<str>],
        locals: &BTreeMap<String, u32>,
    ) -> Result<(), ()> {
        let (spelling, target) = match path {
            [name] => {
                let spelling = name.to_string();
                let target = if let Some(local) = locals.get(&spelling) {
                    Target::Local(*local)
                } else {
                    Target::Function(self.function(&spelling).ok_or(())?)
                };
                (spelling, target)
            }
            [nominal, variant] => {
                let target = *self
                    .variants
                    .get(&(nominal.to_string(), variant.to_string()))
                    .ok_or(())?;
                (nominal.to_string(), Target::Variant(target))
            }
            _ => return Err(()),
        };
        self.result
            .occurrences
            .push(Occurrence { spelling, target });
        Ok(())
    }

    fn expression(&mut self, expression: &Expr, locals: &BTreeMap<String, u32>) -> Result<(), ()> {
        match &expression.kind {
            ExprKind::Unit | ExprKind::Int(_) => Ok(()),
            ExprKind::Variable(path) => self.variable(path, locals),
            ExprKind::Call(callee, arguments) => {
                self.expression(callee, locals)?;
                for argument in arguments.iter() {
                    self.expression(argument, locals)?;
                }
                Ok(())
            }
            ExprKind::Block(statements) => {
                let mut nested = locals.clone();
                self.statements(statements, &mut nested)
            }
            ExprKind::Unary { operand, .. } => self.expression(operand, locals),
            ExprKind::Binary { lhs, rhs, .. } => {
                self.expression(lhs, locals)?;
                self.expression(rhs, locals)
            }
            ExprKind::Tuple(elements) => {
                for element in elements.iter() {
                    self.expression(element, locals)?;
                }
                Ok(())
            }
            ExprKind::Struct { name, fields } => {
                let target = *self.structs.get(name.as_ref()).ok_or(())?;
                self.result.occurrences.push(Occurrence {
                    spelling: name.to_string(),
                    target: Target::Struct(target),
                });
                for (_, value) in fields.iter() {
                    self.expression(value, locals)?;
                }
                Ok(())
            }
            ExprKind::Field(subject, _) => self.expression(subject, locals),
            ExprKind::Perform {
                effect,
                operation,
                args,
            } => {
                let (identity, operations) = self.effect(effect).ok_or(())?;
                let ordinal = operations
                    .iter()
                    .position(|candidate| candidate == operation.as_ref())
                    .and_then(|value| u32::try_from(value).ok())
                    .ok_or(())?;
                self.result.occurrences.push(Occurrence {
                    spelling: effect.to_string(),
                    target: Target::EffectOperation(identity, ordinal),
                });
                for argument in args.iter() {
                    self.expression(argument, locals)?;
                }
                Ok(())
            }
            ExprKind::Closure { params, body } => {
                let mut nested = locals.clone();
                for parameter in params.iter() {
                    let id = self.define(2, parameter)?;
                    nested.insert(parameter.to_string(), id);
                }
                self.expression(body, &nested)
            }
            ExprKind::Handle {
                computation,
                clauses,
            } => {
                self.expression(computation, locals)?;
                for clause in clauses.iter() {
                    let (_, operations) = self.effect(&clause.effect).ok_or(())?;
                    if !operations.iter().any(|name| name == &clause.operation) {
                        return Err(());
                    }
                    let mut nested = locals.clone();
                    for pattern in &clause.patterns {
                        match &pattern.kind {
                            PatternKind::Wildcard | PatternKind::Int(_) => {}
                            PatternKind::Binding(name) => {
                                let id = self.define(2, name)?;
                                nested.insert(name.clone(), id);
                            }
                            _ => return Err(()),
                        }
                    }
                    let body = match (&clause.resumption, &clause.body.kind) {
                        (
                            Some(expected),
                            ExprKind::TailResume {
                                resumption,
                                value: Some(value),
                            },
                        ) if matches!(
                            &resumption.kind,
                            ExprKind::Variable(path)
                                if matches!(
                                    path.as_ref(),
                                    [name] if name.as_ref() == expected
                                )
                        ) =>
                        {
                            value.as_ref()
                        }
                        (None, _) => &clause.body,
                        _ => return Err(()),
                    };
                    self.expression(body, &nested)?;
                }
                Ok(())
            }
            _ => Err(()),
        }
    }

    fn statements(
        &mut self,
        statements: &[Stmt],
        locals: &mut BTreeMap<String, u32>,
    ) -> Result<(), ()> {
        for statement in statements {
            match statement {
                Stmt::Let { name, value, .. } => {
                    // Allocate in declaration order, but do not make the new
                    // binding visible to its own initializer.
                    let id = self.define(2, name)?;
                    self.expression(value, locals)?;
                    locals.insert(name.clone(), id);
                }
                Stmt::Expr(expression) => self.expression(expression, locals)?,
                Stmt::Deconstruct { .. } | Stmt::Assign { .. } => return Err(()),
            }
        }
        Ok(())
    }
}

fn resolve_function(
    graph: &ModuleResolution,
    bundle: &SourceBundle,
    functions: &BTreeMap<(ModuleId, String), FunctionIdentity>,
    structs: &BTreeMap<String, u32>,
    variants: &BTreeMap<(String, String), u32>,
    effects: &BTreeMap<(ModuleId, String), (FunctionIdentity, Vec<String>)>,
    function: &Function,
) -> Result<FunctionResolution, ()> {
    let current_module = graph.owner(bundle, function.span).ok_or(())?;
    let mut resolver = Resolver {
        current_module,
        functions,
        structs,
        variants,
        effects,
        result: FunctionResolution::default(),
    };
    let mut locals = BTreeMap::new();
    let mut parameter_names = BTreeSet::new();
    for parameter in &function.params {
        if !parameter_names.insert(parameter.name.clone()) {
            return Err(());
        }
        let id = resolver.define(1, &parameter.name)?;
        locals.insert(parameter.name.clone(), id);
    }
    resolver.expression(&function.body, &locals)?;
    Ok(resolver.result)
}

fn encode_module_path(output: &mut Vec<u8>, path: &[String]) {
    push_u32(output, path.len().try_into().unwrap());
    for component in path {
        push_string(output, component);
    }
}

fn encode_function_identity(output: &mut Vec<u8>, identity: &FunctionIdentity) {
    encode_module_path(output, &identity.path);
    push_string(output, &identity.name);
}

fn encode_rust_resolution(output: &mut Vec<u8>, source: &str) {
    if grandiose::lexer::lex(source).is_err() {
        output.push(1);
        return;
    }
    let bundle = raw_source_bundle(source);
    let Ok(program) = grandiose::modules::parse_bundle(&bundle) else {
        output.push(3);
        return;
    };
    let Ok(graph) = grandiose::modules::build_graph(&bundle, &program) else {
        output.push(3);
        return;
    };
    let Ok(functions) = function_table(&graph, &bundle, &program) else {
        output.push(3);
        return;
    };
    let structs = program
        .structs
        .iter()
        .enumerate()
        .map(|(index, declaration)| (declaration.name.clone(), index as u32))
        .collect::<BTreeMap<_, _>>();
    let mut variants = BTreeMap::new();
    let mut variant_index = 0u32;
    for declaration in &program.enums {
        for variant in &declaration.variants {
            variants.insert(
                (declaration.name.clone(), variant.name.clone()),
                variant_index,
            );
            variant_index += 1;
        }
    }
    let mut effects = BTreeMap::new();
    for declaration in &program.effects {
        let module = match graph.owner(&bundle, declaration.span) {
            Some(value) => value,
            None => {
                output.push(3);
                return;
            }
        };
        let identity = FunctionIdentity {
            module,
            path: graph.module(module).path.clone(),
            name: declaration.name.clone(),
        };
        let operations = declaration
            .operations
            .iter()
            .map(|operation| operation.name.clone())
            .collect();
        if effects
            .insert((module, declaration.name.clone()), (identity, operations))
            .is_some()
        {
            output.push(3);
            return;
        }
    }
    let mut declarations = program.functions.iter().collect::<Vec<_>>();
    declarations.sort_by_key(|function| function.span.start);

    let mut encoded = Vec::new();
    push_u32(&mut encoded, declarations.len().try_into().unwrap());
    for function in declarations {
        let Ok(identity) = function_identity(&graph, &bundle, function) else {
            output.push(3);
            return;
        };
        let Ok(resolved) = resolve_function(
            &graph, &bundle, &functions, &structs, &variants, &effects, function,
        ) else {
            output.push(3);
            return;
        };
        encode_function_identity(&mut encoded, &identity);
        push_u32(&mut encoded, resolved.bindings.len().try_into().unwrap());
        for binding in resolved.bindings {
            encoded.push(binding.kind);
            push_string(&mut encoded, &binding.name);
        }
        push_u32(&mut encoded, resolved.occurrences.len().try_into().unwrap());
        for occurrence in resolved.occurrences {
            push_string(&mut encoded, &occurrence.spelling);
            match occurrence.target {
                Target::Local(id) => {
                    encoded.push(1);
                    push_u32(&mut encoded, id);
                }
                Target::Function(identity) => {
                    encoded.push(2);
                    encode_function_identity(&mut encoded, &identity);
                }
                Target::Struct(index) => {
                    encoded.push(3);
                    push_u32(&mut encoded, index);
                }
                Target::Variant(index) => {
                    encoded.push(4);
                    push_u32(&mut encoded, index);
                }
                Target::EffectOperation(identity, ordinal) => {
                    encoded.push(5);
                    encode_function_identity(&mut encoded, &identity);
                    push_u32(&mut encoded, ordinal);
                }
            }
        }
    }
    output.push(0);
    output.extend(encoded);
}

fn corpus(directory: &Path) -> Vec<PathBuf> {
    let valid = [
        "probe_param(value: u64) { value }",
        "probe_params(left: u64, right: u64) { probe_sink(left, right) } \
         probe_sink(a: u64, b: u64) { a }",
        "probe_forward() { probe_later() } probe_later() { 1 }",
        "probe_earlier() { 1 } probe_backward() { probe_earlier() }",
        "probe_target() { 1 } \
         probe_shadow() { let probe_target = probe_target(); probe_target }",
        "probe_same_block() { let x = 1; let x = x; x }",
        "probe_outer() { let x = 1; { x }; x }",
        "probe_nested_shadow() { let x = 1; { let x = x; x }; x }",
        "probe_initializer_order() { \
         let outer = { let inner = 1; inner }; outer }",
        "probe_target() { 1 } \
         probe_local_call() { let f = probe_target; f() }",
        "probe_pick() { 1 } \
         mod inner { probe_pick() { 2 } probe_local_item() { probe_pick() } }",
        "probe_root() { 1 } \
         mod inner { probe_root_fallback() { probe_root() } }",
        "struct Pair { left: u64, right: u64 } \
         probe_struct(left: u64, right: u64) { \
         Pair { right: right, left: left }.left }",
        "enum Choice { None(), Some(u64) } \
         probe_variant(value: u64) { Choice::Some(value) }",
        "effect Signal { raise(value: u64) -> u64 } \
         probe_effect(value: u64) -> u64 / {Signal} { \
             perform Signal::raise(value) \
         }",
        "effect Signal { raise(value: u64) -> u64 } \
         probe_implicit_effect(value: u64) -> u64 / {Signal} { \
             Signal::raise(value) \
         }",
        "effect RootSignal { raise() -> u64 } \
         mod inner { \
             probe_root_effect() -> u64 / {RootSignal} { \
                 perform RootSignal::raise() \
             } \
         }",
        "effect Signal { root() -> u64 } \
         mod inner { \
             effect Signal { local() -> u64 } \
             probe_local_effect() -> u64 / {Signal} { \
                 perform Signal::local() \
             } \
         }",
        "effect Signal { first() -> u64 second() -> u64 } \
         probe_second() -> u64 / {Signal} { perform Signal::second() }",
        "effect Signal { inspect(value: u64) -> u64 } \
         probe_effect_handle(value: u64) -> u64 { \
             handle perform Signal::inspect(value) { \
                 Signal::inspect(found) => found \
             } \
         }",
        "effect Fail<E> { fail(error: E) -> ! } \
         probe_generic_effect_path() -> i64 { \
             handle perform Fail<i64>::fail(42) { \
                 Fail<Text>::fail(error) => 0 \
             } \
         }",
        "effect Fail<E> { fail(error: E) -> ! } \
         probe_generic_effect_row<E>() -> / {Fail<E>} { () }",
        "effect Stop { stop() -> ! } \
         probe_simple_effect_path() -> i64 { \
             handle perform Stop::stop() { Stop::stop() => 42 } \
         }",
        "effect Fail<E> { fail(error: E) -> ! } \
         invoke<E, F>(error: E, body: F) -> ! / {Fail<E>} \
             where F: Fn<(E), Output=!, Effects={Fail<E>}> { body(error) } \
         probe_effect_path_closure() -> ! / {Fail<i64>} { \
             invoke(42, { error => perform Fail<i64>::fail(error) }) \
         }",
        "effect Outer { inspect(value: u64) -> u64 } \
         effect Inner { inspect(value: u64) -> u64 } \
         probe_nested_effect_binders(value: u64) -> u64 { \
             handle perform Outer::inspect(value) { \
                 Outer::inspect(outer) => \
                     handle perform Inner::inspect(outer) { \
                         Inner::inspect(inner) => inner \
                     } \
             } \
         }",
    ];
    let malformed = [
        "probe_before_let() { x; let x = 1; x }",
        "probe_block_leak() { { let x = 1; x }; x }",
        "probe_unknown_call() { missing() }",
        "mod outer { probe_parent() { 1 } \
         mod child { probe_no_parent_fallback() { probe_parent() } } }",
        "probe_duplicate(x: u64, x: u64) { x }",
        "probe_duplicate_callable() { 1 } \
         probe_duplicate_callable() { 2 } \
         probe_uses_duplicate() { probe_duplicate_callable() }",
        "probe_unknown_struct() { Missing {} }",
        "enum Choice { Some(u64) } \
         probe_unknown_variant(value: u64) { Choice::Missing(value) }",
        "probe_unknown_effect() -> u64 { perform Missing::raise() }",
        "effect Signal { raise() -> u64 } \
         probe_unknown_operation() -> u64 / {Signal} { \
             perform Signal::missing() \
         }",
        "struct Signal {} \
         probe_invalid_effect_owner() -> u64 { perform Signal::raise() }",
        "effect Signal { raise() -> u64 } \
         probe_unknown_handle_operation() -> u64 { \
             handle perform Signal::raise() { Signal::missing() => 1 } \
         }",
        "struct Signal {} \
         probe_invalid_handle_target(value: Signal) -> u64 { \
             handle value { Signal::missing => 1 } \
         }",
        "mod outer { \
             effect Signal { raise() -> u64 } \
             mod child { \
                 probe_no_parent_effect() -> u64 { perform Signal::raise() } \
             } \
         }",
        "effect Fail<E> { fail(error: E) -> ! } \
         probe_empty_effect_arguments() -> ! { perform Fail<>::fail(1) }",
        "effect Fail<E> { fail(error: E) -> ! } \
         probe_unclosed_effect_arguments() -> ! { perform Fail<i64::fail(1) }",
        "probe_bad_closure() { consume({ value, 42 => value }) }",
    ];

    let mut paths = Vec::new();
    for (index, source) in valid.into_iter().enumerate() {
        let path = directory.join(format!("valid-{index}.glorious"));
        fs::write(&path, source).unwrap();
        paths.push(path);
    }
    for (index, source) in malformed.into_iter().enumerate() {
        let path = directory.join(format!("error-{index}.glorious"));
        fs::write(&path, source).unwrap();
        paths.push(path);
    }
    paths
}

#[test]
fn rust_name_resolution_oracle_classifies_the_focused_corpus() {
    let directory = tempfile::tempdir().unwrap();
    let corpus = corpus(directory.path());
    for path in &corpus {
        let mut encoded = Vec::new();
        encode_rust_resolution(&mut encoded, &fs::read_to_string(path).unwrap());
        let expected = if path
            .file_name()
            .unwrap()
            .to_string_lossy()
            .starts_with("valid-")
        {
            0
        } else {
            3
        };
        assert_eq!(
            encoded.first().copied(),
            Some(expected),
            "unexpected Rust-oracle status for input {}: {encoded:?}",
            path.display()
        );
    }
}

#[test]
fn self_hosted_effect_path_syntax_and_name_resolution_match_rust_in_vm_and_native_execution() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            if std::env::var_os("G1_SELF_HOST_NAME_RESOLUTION_CHECK_ONLY").is_some() {
                let bundle = self_host_bundle();
                grandiose::compile_bundle_to_phases_with_options(
                    &bundle,
                    CompileOptions {
                        optimization_level: OptimizationLevel::O0,
                    },
                )
                .unwrap_or_else(|errors| {
                    for error in &errors {
                        if let Some(span) = error.span
                            && let Some(segment) = bundle.segment_at(span.start)
                        {
                            let base = segment.global_range().start;
                            eprintln!(
                                "{}:{}..{} (global {}..{}): {}",
                                segment.name(),
                                span.start - base,
                                span.end - base,
                                span.start,
                                span.end,
                                error.message
                            );
                        }
                    }
                    panic!("{errors:#?}")
                });
                return;
            }

            let directory = tempfile::tempdir().unwrap();
            let corpus = corpus(directory.path());
            let vm_path = directory.path().join("vm.bin");
            let mut expected = Vec::new();
            push_u32(&mut expected, corpus.len().try_into().unwrap());
            for path in &corpus {
                encode_rust_resolution(&mut expected, &fs::read_to_string(path).unwrap());
            }

            let phases = grandiose::compile_bundle_to_phases_with_options(
                &self_host_bundle(),
                CompileOptions {
                    optimization_level: OptimizationLevel::O2,
                },
            )
            .unwrap();
            let entry = phases.artifact.entry_function.unwrap();
            let verified = verify(phases.artifact.clone()).unwrap();
            for (index, path) in corpus.iter().enumerate() {
                let vm_one_path = directory.path().join(format!("vm-{index}.bin"));
                let vm = Vm::with_host(
                    verified.clone(),
                    ["process.args", "fs.read", "fs.write", "diagnostic"],
                    SystemHost::new(vec![
                        vm_one_path.clone().into_os_string(),
                        path.clone().into_os_string(),
                    ]),
                )
                .unwrap();
                assert_eq!(
                    vm.run(entry, vec![]).unwrap_or_else(|error| {
                        panic!("VM input {index} ({}) failed: {error:?}", path.display())
                    }),
                    Value::Unit
                );
                let mut expected_one = Vec::new();
                push_u32(&mut expected_one, 1);
                encode_rust_resolution(&mut expected_one, &fs::read_to_string(path).unwrap());
                assert_eq!(
                    fs::read(&vm_one_path).unwrap(),
                    expected_one,
                    "VM name resolution diverged for input {index} ({})",
                    path.display()
                );
            }
            let vm_args = std::iter::once(vm_path.clone().into_os_string())
                .chain(corpus.iter().map(|path| path.clone().into_os_string()))
                .collect::<Vec<OsString>>();
            let vm = Vm::with_host(
                verified,
                ["process.args", "fs.read", "fs.write", "diagnostic"],
                SystemHost::new(vm_args),
            )
            .unwrap();
            assert_eq!(vm.run(entry, vec![]).unwrap(), Value::Unit);
            assert_eq!(
                fs::read(&vm_path).unwrap(),
                expected,
                "VM name resolution diverged"
            );

            let asan = std::env::var_os("G1_SELF_HOST_NAME_RESOLUTION_ASAN").is_some();
            let module = grandiose::emit_llvm_ir(&phases, &LlvmOptions::default()).unwrap();
            let debug_directory = repository_root().join("target/self-host-name-resolution-debug");
            if asan {
                fs::create_dir_all(&debug_directory).unwrap();
                let functions = phases
                    .mir
                    .functions
                    .iter()
                    .enumerate()
                    .map(|(index, function)| format!("{index}\t{}\n", function.name))
                    .collect::<String>();
                fs::write(debug_directory.join("functions.txt"), functions).unwrap();
            }
            let llvm = if asan {
                debug_directory.join("self-host-name-resolution.ll")
            } else {
                directory.path().join("self-host-name-resolution.ll")
            };
            let executable = if asan {
                debug_directory.join("self-host-name-resolution")
            } else {
                directory.path().join("self-host-name-resolution")
            };
            fs::write(&llvm, module.ir).unwrap();
            let mut clang_command = Command::new("clang");
            clang_command
                .arg(&llvm)
                .arg(repository_root().join("crates/grandiose/src/native_runtime.c"))
                .arg(repository_root().join("crates/grandiose/src/native_host_runtime.c"))
                .arg("-O0");
            if asan {
                clang_command.args(["-fsanitize=address", "-fno-omit-frame-pointer", "-g"]);
            }
            let clang = clang_command.arg("-o").arg(&executable).output().unwrap();
            assert!(
                clang.status.success(),
                "{}",
                String::from_utf8_lossy(&clang.stderr)
            );

            let native_all_path = directory.path().join("native-all.bin");
            let native_all = Command::new(&executable)
                .arg(&native_all_path)
                .args(&corpus)
                .output()
                .unwrap();
            assert!(
                native_all.status.success(),
                "native whole-corpus status: {:?}\n{}",
                native_all.status,
                String::from_utf8_lossy(&native_all.stderr)
            );
            assert_eq!(
                fs::read(&native_all_path).unwrap(),
                expected,
                "native whole-corpus name resolution diverged"
            );
            for (index, path) in corpus.iter().enumerate() {
                let native_path = directory.path().join(format!("native-{index}.bin"));
                let native = Command::new(&executable)
                    .arg(&native_path)
                    .arg(path)
                    .output()
                    .unwrap();
                assert!(
                    native.status.success(),
                    "native input {index} ({}) status: {:?}\n{}",
                    native.status,
                    path.display(),
                    String::from_utf8_lossy(&native.stderr)
                );
                let mut expected_one = Vec::new();
                push_u32(&mut expected_one, 1);
                encode_rust_resolution(&mut expected_one, &fs::read_to_string(path).unwrap());
                assert_eq!(
                    fs::read(&native_path).unwrap(),
                    expected_one,
                    "native name resolution diverged for input {index} ({})",
                    path.display()
                );
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn self_host_resolution_generic_binders_shadow_global_aliases() {
    // Exact source from `generic_alias_shadowing.rs`: each generic binder must
    // resolve as a local type parameter rather than the same-named alias.
    let source = r#"
        type A = Text;
        type E = Text;
        type F = Text;

        choose<A, E, F>(answer: A, evidence: E, fallback: F) -> A {
            evidence;
            fallback;
            answer
        }

        answer() -> i64 { choose(42, "evidence", ()) }
        main() -> () { () }
    "#;
    let expected_one = {
        let mut output = Vec::new();
        output.push(0);
        encode_rust_generic_resolution(&mut output, source);
        output
    };
    let directory = tempfile::tempdir().unwrap();
    let input = directory.path().join("generic-binders.glorious");
    let vm_output = directory.path().join("vm.bin");
    fs::write(&input, source).unwrap();
    let phases = grandiose::compile_bundle_to_phases_with_options(
        &self_host_generic_bundle(),
        CompileOptions {
            optimization_level: OptimizationLevel::O2,
        },
    )
    .unwrap();
    let entry = phases.artifact.entry_function.unwrap();
    let verified = verify(phases.artifact.clone()).unwrap();
    let vm = Vm::with_host(
        verified,
        ["process.args", "fs.read", "fs.write", "diagnostic"],
        SystemHost::new(vec![vm_output.clone().into_os_string(), input.clone().into_os_string()]),
    )
    .unwrap();
    assert_eq!(vm.run(entry, vec![]).unwrap(), Value::Unit);
    let mut expected = Vec::new();
    push_u32(&mut expected, 1);
    expected.extend(&expected_one);
    assert_eq!(fs::read(&vm_output).unwrap(), expected);

    let module = grandiose::emit_llvm_ir(&phases, &LlvmOptions::default()).unwrap();
    let llvm = directory.path().join("generic-binders.ll");
    let executable = directory.path().join("generic-binders");
    fs::write(&llvm, module.ir).unwrap();
    let clang = Command::new("clang")
        .arg(&llvm)
        .arg(repository_root().join("crates/grandiose/src/native_runtime.c"))
        .arg(repository_root().join("crates/grandiose/src/native_host_runtime.c"))
        .arg("-O0")
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(clang.status.success(), "{}", String::from_utf8_lossy(&clang.stderr));
    let native_output = directory.path().join("native.bin");
    let native = Command::new(&executable)
        .arg(&native_output)
        .arg(&input)
        .output()
        .unwrap();
    assert!(native.status.success(), "{}", String::from_utf8_lossy(&native.stderr));
    assert_eq!(fs::read(&native_output).unwrap(), expected);
}

fn read_u32(bytes: &[u8], cursor: &mut usize) -> u32 {
    let end = *cursor + 4;
    let value = u32::from_le_bytes(bytes[*cursor..end].try_into().unwrap());
    *cursor = end;
    value
}

fn self_host_module_diagnostics(
    verified: &grandiose_vm::VerifiedArtifact,
    paths: &[PathBuf],
) -> Vec<(u8, u32, String)> {
    let directory = tempfile::tempdir().unwrap();
    let output = directory.path().join("module-diagnostics.bin");
    let args = std::iter::once(output.clone().into_os_string())
        .chain(paths.iter().map(|path| path.clone().into_os_string()))
        .collect::<Vec<OsString>>();
    let vm = Vm::with_host(
        verified.clone(),
        ["process.args", "fs.read", "fs.write", "diagnostic"],
        SystemHost::new(args),
    )
    .unwrap();
    assert_eq!(vm.run(verified.entry_function().unwrap(), vec![]).unwrap(), Value::Unit);
    let bytes = fs::read(output).unwrap();
    let mut cursor = 0;
    let mut diagnostics = Vec::new();
    while cursor < bytes.len() {
        let kind = bytes[cursor];
        cursor += 1;
        let span = read_u32(&bytes, &mut cursor);
        diagnostics.push((kind, span, String::new()));
    }
    diagnostics
}

#[test]
fn self_host_unit_missing_or_orphan_external_modules_are_errors() {
    let directory = tempfile::tempdir().unwrap();
    let main = directory.path().join("main.glorious");
    let absent = directory.path().join("absent/absent.glorious");
    let present = directory.path().join("present/present.glorious");
    let orphan = directory.path().join("orphan/orphan.glorious");
    fs::write(&main, "mod absent; main() -> { () }\n").unwrap();
    let missing_bundle = grandiose::source_bundle::SourceBundle::distributed(
        grandiose::source_bundle::Segment::new(main.to_string_lossy().into_owned(), "mod absent; main() -> { () }\n"),
        [],
    );
    let bootstrap_missing = grandiose::compile_bundle_to_bytecode(&missing_bundle).unwrap_err();
    assert!(bootstrap_missing.iter().any(|error| {
        error.message.contains("absent/absent.glorious") && error.span.is_some()
    }));
    let phases = grandiose::compile_bundle_to_phases_with_options(
        &self_host_module_bundle(),
        CompileOptions { optimization_level: OptimizationLevel::O2 },
    )
    .unwrap();
    let verified = verify(phases.artifact).unwrap();
    let missing = self_host_module_diagnostics(&verified, &[main.clone()]);
    assert_eq!(missing.len(), 1);
    assert_eq!(missing[0].0, 1);
    assert_ne!(missing[0].1, 0);
    assert!(absent.ends_with("absent/absent.glorious"));

    fs::write(&main, "mod present; main() -> { () }\n").unwrap();
    fs::create_dir_all(present.parent().unwrap()).unwrap();
    fs::create_dir_all(orphan.parent().unwrap()).unwrap();
    fs::write(&present, "pub ok() -> { () }\n").unwrap();
    fs::write(&orphan, "pub stray() -> { () }\n").unwrap();
    let orphan_bundle = grandiose::source_bundle::SourceBundle::distributed(
        grandiose::source_bundle::Segment::new(main.to_string_lossy().into_owned(), "mod present; main() -> { () }\n"),
        [
            grandiose::source_bundle::Segment::new(present.to_string_lossy().into_owned(), "pub ok() -> { () }\n"),
            grandiose::source_bundle::Segment::new(orphan.to_string_lossy().into_owned(), "pub stray() -> { () }\n"),
        ],
    );
    let bootstrap_orphan = grandiose::compile_bundle_to_bytecode(&orphan_bundle).unwrap_err();
    assert!(bootstrap_orphan.iter().any(|error| error.message.contains("orphan")));
    let orphan_diagnostics =
        self_host_module_diagnostics(&verified, &[main, present, orphan.clone()]);
    assert_eq!(orphan_diagnostics.len(), 1);
    assert_eq!(orphan_diagnostics[0].0, 2);
    assert_eq!(orphan_diagnostics[0].1, 0);
}

#[test]
fn self_host_unit_resolved_occurrence_keys_have_exact_path_spans() {
    let source = r#"
        mod api { pub answer() -> i64 { 42 } }
        use crate::api::answer as chosen;
        probe() -> i64 { chosen() }
        main() -> { () }
        "#;
    let bootstrap_bundle = raw_source_bundle(source);
    let bootstrap_program = grandiose::modules::parse_bundle(&bootstrap_bundle).unwrap();
    let bootstrap_resolved =
        grandiose::modules::resolve_program(&bootstrap_bundle, bootstrap_program).unwrap();
    let bootstrap_base = bootstrap_bundle.segments()[1].global_range().start;
    let bootstrap_spans = bootstrap_resolved
        .resolution
        .resolved_paths
        .keys()
        .map(|(start, end)| (start - bootstrap_base, end - bootstrap_base))
        .collect::<BTreeSet<_>>();
    let bootstrap_occurrences = bootstrap_spans
        .iter()
        .map(|(start, end)| &source[*start..*end])
        .collect::<Vec<_>>();
    assert!(bootstrap_occurrences.contains(&"chosen"), "{bootstrap_occurrences:#?}");
    assert!(bootstrap_occurrences.iter().all(|occurrence| {
        !occurrence.contains('(') && !occurrence.contains('{') && !occurrence.contains('<')
    }), "{bootstrap_occurrences:#?}");

    let directory = tempfile::tempdir().unwrap();
    let input = directory.path().join("occurrence-spans.glorious");
    let output = directory.path().join("occurrence-spans.bin");
    fs::write(&input, source).unwrap();
    let phases = grandiose::compile_bundle_to_phases_with_options(
        &self_host_bundle(),
        CompileOptions {
            optimization_level: OptimizationLevel::O2,
        },
    )
    .unwrap();
    let entry = phases.artifact.entry_function.unwrap();
    let verified = verify(phases.artifact.clone()).unwrap();
    let vm = Vm::with_host(
        verified,
        ["process.args", "fs.read", "fs.write", "diagnostic"],
        SystemHost::new(vec![output.clone().into_os_string(), input.into_os_string()]),
    )
    .unwrap();
    assert_eq!(vm.run(entry, vec![]).unwrap(), Value::Unit);

    let encoded = fs::read(output).unwrap();
    let mut expected = Vec::new();
    push_u32(&mut expected, 1);
    encode_rust_resolution(&mut expected, source);
    assert_eq!(encoded, expected);
    assert_eq!(bootstrap_spans.len(), 1);
}
