use std::{
    collections::{BTreeMap, BTreeSet},
    ffi::OsString,
    fs,
    path::{Path, PathBuf},
    process::Command,
};

use grandiose::{
    CompileOptions, LlvmOptions, OptimizationLevel, ast,
    compiler_core::{self as core, ExprKind, Stmt},
    modules::{ModuleResolution, ResolvedProgram},
    source_bundle::{Segment, SourceBundle},
};
use grandiose_vm::{Constant, SystemHost, Type, TypeId, UNIT, Value, Vm, verify};

const INPUT_NAME: &str = "typed-core-input.glorious";
const WRAPPER: &str = "\nmain() { () }\n";

fn repository_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_owned()
}

fn self_host_bundle_with_main(main: &str) -> SourceBundle {
    let root = repository_root().join("self-host/src");
    let primary = Segment::new(root.join("main.glorious").to_string_lossy(), main);
    let paths = [
        root.join("frontend/frontend.glorious"),
        root.join("frontend/lexer/lexer.glorious"),
        root.join("frontend/scanner/scanner.glorious"),
        root.join("frontend/headers/headers.glorious"),
        root.join("frontend/bodies/bodies.glorious"),
        root.join("frontend/resolution/resolution.glorious"),
        root.join("frontend/elaboration/elaboration.glorious"),
        root.join("probe/probe.glorious"),
        root.join("probe/elaboration/elaboration.glorious"),
    ];
    SourceBundle::distributed(
        primary,
        paths.into_iter().map(|path| {
            let mut source = fs::read_to_string(&path)
                .unwrap()
                .replace("pub mod lossless;\n", "");
            if path.ends_with("probe/probe.glorious") {
                source = source
                    .replace("pub mod lexer;\n", "")
                    .replace("pub mod scanner;\n", "")
                    .replace("pub mod headers;\n", "")
                    .replace("pub mod bodies;\n", "")
                    .replace("pub mod resolution;\n", "");
            }
            Segment::new(path.to_string_lossy(), source)
        }),
    )
}

fn self_host_bundle() -> SourceBundle {
    self_host_bundle_with_main(
        "mod frontend;\nmod probe;\n\nmain() { run_compiler_host(probe::elaboration::application) }\n",
    )
}

fn self_host_effect_bundle() -> SourceBundle {
    self_host_bundle_with_main(
        "mod frontend;\nmod probe;\n\nmain() { run_compiler_host(probe::elaboration::effect_interface_application) }\n",
    )
}

fn artifact_function_id(artifact: &grandiose_vm::Artifact, suffix: &str) -> u32 {
    artifact
        .functions
        .iter()
        .position(|function| function.name.ends_with(suffix))
        .unwrap_or_else(|| panic!("self-host probe is missing function `{suffix}`"))
        .try_into()
        .unwrap()
}

#[test]
#[ignore = "targeted self-host semantic arena debugger"]
fn inspect_self_host_interface_type_metadata() {
    let phases = grandiose::compile_bundle_to_phases_with_options(
        &self_host_bundle(),
        CompileOptions {
            optimization_level: OptimizationLevel::O2,
        },
    )
    .unwrap();
    let function = artifact_function_id(&phases.artifact, ":interface_type_metadata");
    let verified = verify(phases.artifact).unwrap();
    let source =
        fs::read_to_string(repository_root().join("target/self-host-replay/input.glorious"))
            .unwrap();
    for index in [363_u64, 364] {
        let vm = Vm::with_host(
            verified.clone(),
            ["process.args", "fs.read", "fs.write", "diagnostic"],
            SystemHost::new(Vec::<OsString>::new()),
        )
        .unwrap();
        let value = vm
            .run(
                function,
                vec![Value::Text(source.clone().into()), Value::U64(index)],
            )
            .unwrap();
        eprintln!("self-host semantic type {index}: {value:?}");
    }
}

#[test]
fn self_hosted_trait_and_impl_generic_member_signatures_collect_in_vm() {
    let phases = grandiose::compile_bundle_to_phases_with_options(
        &self_host_bundle(),
        CompileOptions {
            optimization_level: OptimizationLevel::O2,
        },
    )
    .unwrap();
    let function = artifact_function_id(&phases.artifact, ":interface_collection_status");
    let verified = verify(phases.artifact).unwrap();
    let source = "trait Replay<T> { \
            replay<U>(value: T, other: U) -> U where U: Use<[0, *]>; \
        } \
        struct Wrapper<T> { value: T } \
        impl<T> Replay<T> for Wrapper<T> { \
            replay<U>(value: T, other: U) -> U where U: Use<[0, *]> { other } \
        } \
        main() { () }";
    let vm = Vm::with_host(
        verified,
        ["process.args", "fs.read", "fs.write", "diagnostic"],
        SystemHost::new(Vec::<OsString>::new()),
    )
    .unwrap();
    let Value::U64(status) = vm.run(function, vec![Value::Text(source.into())]).unwrap()
    else {
        panic!("interface_collection_status did not return u8");
    };
    assert_eq!(status, 0, "trait and impl member signatures must collect");
}

#[test]
fn self_hosted_nominal_method_generic_owner_is_distinct_in_release_vm() {
    let phases = grandiose::compile_bundle_to_phases_with_options(
        &self_host_bundle(),
        CompileOptions {
            optimization_level: OptimizationLevel::O2,
        },
    )
    .unwrap();
    let function = artifact_function_id(
        &phases.artifact,
        ":nominal_method_generic_owner_status",
    );
    let verified = verify(phases.artifact).unwrap();
    let source = "trait Binder<T> { \
            select<U>(outer: T, receiver: &Self, inner: U) -> U; \
        } \
        struct Wrapper<T> { value: T } \
        impl<T> Binder<T> for Wrapper<T> { \
            select<U>(outer: T, receiver: &Self, inner: U) -> U { inner } \
        } \
        main() { () }";
    let vm = Vm::with_host(
        verified,
        ["process.args", "fs.read", "fs.write", "diagnostic"],
        SystemHost::new(Vec::<OsString>::new()),
    )
    .unwrap();
    let Value::U64(status) = vm.run(function, vec![Value::Text(source.into())]).unwrap()
    else {
        panic!("nominal_method_generic_owner_status did not return u8");
    };
    assert_eq!(
        status, 0,
        "enclosing T and method U must retain distinct generic owners"
    );
}

#[test]
fn self_hosted_generic_trait_headers_retain_supertrait_applications_in_vm() {
    let phases = grandiose::compile_bundle_to_phases_with_options(
        &self_host_bundle(),
        CompileOptions { optimization_level: OptimizationLevel::O2 },
    )
    .unwrap();
    let function = artifact_function_id(&phases.artifact, ":trait_header_collection_status");
    let verified = verify(phases.artifact).unwrap();
    let source = "trait Parent<T> {} trait Child<T>: Parent<T> + Parent<Vec<T>> {} \
        struct Wrapper<T> { value: T } impl<T> Child<T> for Wrapper<T> {}";
    let vm = Vm::with_host(
        verified,
        ["process.args", "fs.read", "fs.write", "diagnostic"],
        SystemHost::new(Vec::<OsString>::new()),
    )
    .unwrap();
    let Value::U64(status) = vm.run(function, vec![Value::Text(source.into())]).unwrap()
    else {
        panic!("trait_header_collection_status did not return u8");
    };
    assert_eq!(status, 0, "generic trait headers must retain their supertrait applications");
}

fn push_u32(output: &mut Vec<u8>, value: u32) {
    output.extend(value.to_le_bytes());
}

fn push_string(output: &mut Vec<u8>, value: &str) {
    push_u32(output, value.len().try_into().unwrap());
    output.extend(value.as_bytes());
}

fn encode_constraint_span(output: &mut Vec<u8>, source: &str, clause: Option<&ast::WhereClause>) {
    match clause {
        Some(clause) => push_string(output, &source[clause.span.start..clause.span.end]),
        None => push_string(output, ""),
    }
}

fn encode_quantity(output: &mut Vec<u8>, quantity: &ast::QuantitySyntax) {
    push_u32(output, quantity.lower.try_into().unwrap());
    match quantity.upper {
        Some(upper) => {
            output.push(1);
            push_u32(output, upper.try_into().unwrap());
        }
        None => output.push(0),
    }
}

fn encode_goal_argument(
    output: &mut Vec<u8>,
    argument: &ast::GoalArgument,
    effect_generics: &[ast::GenericParam],
    operation_generics: &[ast::GenericParam],
) {
    match argument {
        ast::GoalArgument::Type(ty) => {
            output.push(1);
            encode_effect_signature_type(output, ty, effect_generics, operation_generics);
        }
        ast::GoalArgument::Lifetime { name, .. } => {
            output.push(2);
            push_string(output, name);
        }
        ast::GoalArgument::Quantity(quantity) => {
            output.push(3);
            encode_quantity(output, quantity);
        }
        ast::GoalArgument::U32 { value, .. } => {
            output.push(4);
            push_u32(output, (*value).try_into().unwrap());
        }
    }
}

fn encode_associated_argument(
    output: &mut Vec<u8>,
    binding: &ast::AssociatedBinding,
    position: usize,
    ordinary_index: &mut usize,
    effect_generics: &[ast::GenericParam],
    operation_generics: &[ast::GenericParam],
) {
    if let Some(argument) = binding
        .const_arguments
        .iter()
        .find(|argument| argument.position == position)
    {
        match &argument.value {
            ast::ConstArgumentValueSyntax::Quantity(quantity) => {
                output.push(3);
                encode_quantity(output, quantity);
            }
            ast::ConstArgumentValueSyntax::U32 { value, .. } => {
                output.push(4);
                push_u32(output, (*value).try_into().unwrap());
            }
            other => panic!("unsupported focused associated const argument: {other:?}"),
        }
    } else {
        match &binding.arguments[*ordinary_index] {
            ast::AssociatedArgumentSyntax::Type(ty) => {
                output.push(1);
                encode_effect_signature_type(output, ty, effect_generics, operation_generics);
            }
            ast::AssociatedArgumentSyntax::Lifetime { name, .. } => {
                output.push(2);
                push_string(output, name);
            }
        }
        *ordinary_index += 1;
    }
}

fn encode_where_clause(
    output: &mut Vec<u8>,
    clause: Option<&ast::WhereClause>,
    effect_generics: &[ast::GenericParam],
    operation_generics: &[ast::GenericParam],
) {
    let Some(clause) = clause else {
        push_u32(output, 0);
        push_u32(output, 0);
        return;
    };
    push_u32(output, clause.goals.len().try_into().unwrap());
    for goal in &clause.goals {
        push_u32(
            output,
            goal.higher_ranked_lifetimes.len().try_into().unwrap(),
        );
        for binder in &goal.higher_ranked_lifetimes {
            push_string(output, &binder.name);
        }
        encode_effect_signature_type(output, &goal.subject, effect_generics, operation_generics);
        output.push(u8::from(goal.polarity == ast::GoalPolarity::Negative));
        push_string(output, &goal.relation.path.last().unwrap().name);
        push_u32(output, goal.relation.arguments.len().try_into().unwrap());
        for argument in &goal.relation.arguments {
            encode_goal_argument(output, argument, effect_generics, operation_generics);
        }
        push_u32(output, goal.relation.bindings.len().try_into().unwrap());
        for binding in &goal.relation.bindings {
            push_string(output, &binding.name);
            let argument_count = binding.arguments.len() + binding.const_arguments.len();
            push_u32(output, argument_count.try_into().unwrap());
            let mut ordinary_index = 0;
            for position in 0..argument_count {
                encode_associated_argument(
                    output,
                    binding,
                    position,
                    &mut ordinary_index,
                    effect_generics,
                    operation_generics,
                );
            }
            match &binding.value {
                ast::AssociatedBindingValue::Type(ty) => {
                    output.push(1);
                    encode_effect_signature_type(output, ty, effect_generics, operation_generics);
                }
                ast::AssociatedBindingValue::EffectRow(row) => {
                    output.push(2);
                    push_u32(output, row.effects.len().try_into().unwrap());
                    for effect in &row.effects {
                        encode_effect_signature_type(
                            output,
                            effect,
                            effect_generics,
                            operation_generics,
                        );
                    }
                    match &row.tail {
                        Some(tail) => {
                            output.push(1);
                            push_string(output, &tail.name);
                        }
                        None => output.push(0),
                    }
                }
            }
        }
    }
    push_u32(output, clause.lifetime_outlives.len().try_into().unwrap());
}

fn scalar_code(name: &str) -> Option<u8> {
    Some(match name {
        "u8" => 1,
        "u16" => 2,
        "u32" => 3,
        "u64" => 4,
        "u128" => 5,
        "usize" => 6,
        "i8" => 7,
        "i16" => 8,
        "i32" => 9,
        "i64" => 10,
        "i128" => 11,
        "isize" => 12,
        "f32" => 13,
        "f64" => 14,
        "char" => 15,
        _ => return None,
    })
}

fn encode_effect_signature_type(
    output: &mut Vec<u8>,
    ty: &ast::TypeSyntax,
    effect_generics: &[ast::GenericParam],
    operation_generics: &[ast::GenericParam],
) {
    use ast::TypeSyntaxKind;

    match &ty.kind {
        TypeSyntaxKind::Path(path) if path.len() == 1 => {
            let name = path[0].name.as_str();
            if let Some(ordinal) = operation_generics
                .iter()
                .position(|parameter| parameter.name == name)
            {
                output.extend([8, 2]);
                push_u32(output, ordinal.try_into().unwrap());
            } else if let Some(ordinal) = effect_generics
                .iter()
                .position(|parameter| parameter.name == name)
            {
                output.extend([8, 1]);
                push_u32(output, ordinal.try_into().unwrap());
            } else if let Some(kind) = scalar_code(name) {
                output.extend([3, kind]);
            } else {
                match name {
                    "Unit" => output.push(1),
                    "Text" => output.push(11),
                    "Bytes" => output.push(12),
                    other => panic!("focused effect oracle does not normalize `{other}`"),
                }
            }
        }
        TypeSyntaxKind::Tuple(elements) if elements.is_empty() => output.push(1),
        TypeSyntaxKind::Tuple(elements) => {
            output.push(4);
            push_u32(output, elements.len().try_into().unwrap());
            for element in elements {
                encode_effect_signature_type(output, element, effect_generics, operation_generics);
            }
        }
        TypeSyntaxKind::SharedReference { referent, .. } => {
            output.push(6);
            encode_effect_signature_type(output, referent, effect_generics, operation_generics);
        }
        TypeSyntaxKind::UniqueReference { referent, .. } => {
            output.push(7);
            encode_effect_signature_type(output, referent, effect_generics, operation_generics);
        }
        TypeSyntaxKind::Application {
            constructor,
            arguments,
            lifetime_arguments,
            ..
        } if constructor.simple_name() == Some("Array") && lifetime_arguments.is_empty() => {
            assert_eq!(arguments.len(), 1);
            output.push(9);
            encode_effect_signature_type(
                output,
                &arguments[0],
                effect_generics,
                operation_generics,
            );
        }
        TypeSyntaxKind::Never => output.push(2),
        other => panic!("unsupported focused effect signature type: {other:?}"),
    }
}

fn encode_rust_effect_interfaces(source: &str) -> Vec<u8> {
    let tokens = grandiose::lexer::lex(source).unwrap();
    let program = grandiose::parser::parse(tokens).unwrap();
    let mut output = vec![0];
    push_u32(&mut output, program.effects.len().try_into().unwrap());
    for declaration in &program.effects {
        let effect_generics = declaration
            .generics
            .as_ref()
            .map_or(&[][..], |generics| generics.params.as_slice());
        push_u32(&mut output, effect_generics.len().try_into().unwrap());
        encode_constraint_span(&mut output, source, declaration.where_clause.as_ref());
        encode_where_clause(
            &mut output,
            declaration.where_clause.as_ref(),
            effect_generics,
            &[],
        );
        push_u32(
            &mut output,
            declaration.operations.len().try_into().unwrap(),
        );
        for (ordinal, operation) in declaration.operations.iter().enumerate() {
            let operation_generics = operation
                .generics
                .as_ref()
                .map_or(&[][..], |generics| generics.params.as_slice());
            push_string(&mut output, &operation.name);
            push_u32(&mut output, ordinal.try_into().unwrap());
            push_u32(&mut output, operation_generics.len().try_into().unwrap());
            encode_constraint_span(&mut output, source, operation.where_clause.as_ref());
            encode_where_clause(
                &mut output,
                operation.where_clause.as_ref(),
                effect_generics,
                operation_generics,
            );
            push_u32(&mut output, operation.params.len().try_into().unwrap());
            for parameter in &operation.params {
                encode_effect_signature_type(
                    &mut output,
                    &parameter.ty,
                    effect_generics,
                    operation_generics,
                );
            }
            if operation.terminal {
                output.push(2);
            } else if let Some(result) = &operation.return_type {
                encode_effect_signature_type(
                    &mut output,
                    result,
                    effect_generics,
                    operation_generics,
                );
            } else {
                output.push(1);
            }
            output.push(u8::from(operation.terminal));
            push_u32(
                &mut output,
                if operation.terminal {
                    0
                } else {
                    operation.resumption_lower.try_into().unwrap()
                },
            );
            match if operation.terminal {
                Some(0)
            } else {
                operation.resumption_upper
            } {
                Some(upper) => {
                    output.push(1);
                    push_u32(&mut output, upper.try_into().unwrap());
                }
                None => output.push(0),
            }
        }
    }
    output
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct FunctionIdentity {
    path: Vec<String>,
    name: String,
}

fn encode_identity(output: &mut Vec<u8>, identity: &FunctionIdentity) {
    push_u32(output, identity.path.len().try_into().unwrap());
    for component in &identity.path {
        push_string(output, component);
    }
    push_string(output, &identity.name);
}

fn source_identity(
    graph: &ModuleResolution,
    bundle: &SourceBundle,
    function: &ast::Function,
) -> Result<FunctionIdentity, String> {
    let module = graph
        .owner(bundle, function.span)
        .ok_or_else(|| format!("no module owns source function {:?}", function.name))?;
    Ok(FunctionIdentity {
        path: graph.module(module).path.clone(),
        name: function.name.clone(),
    })
}

struct SourceFunction<'a> {
    source: &'a ast::Function,
    identity: FunctionIdentity,
    backend_name: String,
}

fn source_functions<'a>(
    resolved: &'a ResolvedProgram,
    bundle: &SourceBundle,
    original_len: usize,
) -> Result<Vec<SourceFunction<'a>>, String> {
    let input = &bundle.segments()[1];
    let input_end = input.global_range().start + original_len;
    let mut functions = resolved
        .program
        .functions
        .iter()
        .filter(|function| {
            let start = function.span.start;
            start >= input.global_range().start && start < input_end
        })
        .map(|function| {
            let module = resolved
                .resolution
                .owner(bundle, function.span)
                .ok_or_else(|| format!("source function {:?} has no owner", function.name))?;
            let backend_name = match resolved.resolution.definition_at(function.span) {
                Some(definition) => resolved.resolution.backend_spelling(definition),
                None if resolved.resolution.module(module).path.is_empty() => function.name.clone(),
                None => {
                    return Err(format!(
                        "non-root source function {:?} has no resolved definition",
                        function.name
                    ));
                }
            };
            Ok(SourceFunction {
                source: function,
                identity: source_identity(&resolved.resolution, bundle, function)?,
                backend_name,
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    functions.sort_by_key(|function| function.source.span.start);
    Ok(functions)
}

const NORMALIZED_AGGREGATE_TYPE_BASE: u32 = 0x8000_0000;

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum NormalizedType {
    Scalar(u32),
    Tuple(Vec<NormalizedType>),
    Struct(String),
    Enum(String),
}

struct TypeEncoder<'a> {
    types: &'a [Type],
    aggregate_ids: BTreeMap<NormalizedType, u32>,
}

impl<'a> TypeEncoder<'a> {
    fn new(types: &'a [Type], functions: &[&core::Function]) -> Result<Self, String> {
        let mut keys = BTreeSet::new();
        for function in functions {
            for parameter in &function.params {
                Self::collect_type(types, parameter.ty, &mut keys)?;
            }
            Self::collect_type(types, function.result, &mut keys)?;
            Self::collect_expression(types, &function.body, &mut keys)?;
        }
        let aggregate_ids = keys
            .into_iter()
            .enumerate()
            .map(|(index, key)| {
                let index = u32::try_from(index)
                    .map_err(|_| "normalized aggregate type identity overflow".to_owned())?;
                let id = NORMALIZED_AGGREGATE_TYPE_BASE
                    .checked_add(index)
                    .ok_or_else(|| "normalized aggregate type identity overflow".to_owned())?;
                Ok((key, id))
            })
            .collect::<Result<_, String>>()?;
        Ok(Self {
            types,
            aggregate_ids,
        })
    }

    fn descriptor(types: &[Type], ty: TypeId) -> Result<&Type, String> {
        types
            .get(ty as usize)
            .ok_or_else(|| format!("Core references unknown type t{ty}"))
    }

    fn key(types: &[Type], ty: TypeId) -> Result<NormalizedType, String> {
        // The self-host type wire reserves 0..19 for its predeclared
        // scalar ABI (Unit through Char); only user aggregates are
        // normalized into the high-bit namespace.
        if ty < 19 {
            return Ok(NormalizedType::Scalar(ty));
        }
        let descriptor = Self::descriptor(types, ty)?;
        if !descriptor.claimed_duplicable() {
            return Err(format!(
                "Stage A typed-Core fixture escaped copy-only contract with type t{ty}"
            ));
        }
        match descriptor.representation() {
            Type::Tuple { fields, .. } => Ok(NormalizedType::Tuple(
                fields
                    .iter()
                    .map(|field| Self::key(types, *field))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            Type::Struct { name, .. } => {
                if name.contains('<') {
                    return Err(format!(
                        "Stage A typed-Core fixture escaped monomorphic nominal contract with `{name}`"
                    ));
                }
                Ok(NormalizedType::Struct(name.clone()))
            }
            Type::Enum { name, .. } => {
                if name.contains('<') {
                    return Err(format!(
                        "Stage A typed-Core fixture escaped monomorphic nominal contract with `{name}`"
                    ));
                }
                Ok(NormalizedType::Enum(name.clone()))
            }
            other => Err(format!(
                "Stage A typed-Core fixture escaped aggregate contract with type t{ty} `{other:?}`"
            )),
        }
    }

    fn collect_type(
        types: &[Type],
        ty: TypeId,
        output: &mut BTreeSet<NormalizedType>,
    ) -> Result<(), String> {
        if ty < 19 {
            return Ok(());
        }
        let key = Self::key(types, ty)?;
        if let Type::Tuple { fields, .. } = Self::descriptor(types, ty)?.representation() {
            for field in fields {
                Self::collect_type(types, *field, output)?;
            }
        }
        output.insert(key);
        Ok(())
    }

    fn collect_expression(
        types: &[Type],
        expression: &core::Expr,
        output: &mut BTreeSet<NormalizedType>,
    ) -> Result<(), String> {
        Self::collect_type(types, expression.ty, output)?;
        match &expression.kind {
            ExprKind::Unit | ExprKind::Constant(_) | ExprKind::Local { .. } => {}
            ExprKind::Call { args, .. }
            | ExprKind::TailCall { args, .. }
            | ExprKind::CallSelf { args }
            | ExprKind::TailCallSelf { args }
            | ExprKind::Primitive { args, .. } => {
                for argument in args {
                    Self::collect_expression(types, argument, output)?;
                }
            }
            ExprKind::Block { statements, tail } => {
                for statement in statements {
                    match statement {
                        Stmt::Let { ty, value, .. } => {
                            Self::collect_type(types, *ty, output)?;
                            Self::collect_expression(types, value, output)?;
                        }
                        Stmt::Expr(expression) => {
                            Self::collect_expression(types, expression, output)?;
                        }
                        other => {
                            return Err(format!(
                                "unsupported statement in Stage A typed-Core oracle: {other:?}"
                            ));
                        }
                    }
                }
                Self::collect_expression(types, tail, output)?;
            }
            ExprKind::RefinementBranch {
                subject,
                positive,
                negative,
                ..
            } => {
                Self::collect_expression(types, subject, output)?;
                Self::collect_expression(types, positive, output)?;
                Self::collect_expression(types, negative, output)?;
            }
            ExprKind::Construct {
                nominal, fields, ..
            } => {
                Self::collect_type(types, *nominal, output)?;
                for field in fields {
                    Self::collect_expression(types, &field.value, output)?;
                }
            }
            ExprKind::Project { subject, .. } => {
                Self::collect_expression(types, subject, output)?;
            }
            other => {
                return Err(format!(
                    "unsupported wrapper in Stage A typed-Core oracle: {other:?}"
                ));
            }
        }
        Ok(())
    }

    fn id(&self, ty: TypeId) -> Result<u32, String> {
        if ty < 19 {
            return Ok(ty);
        }
        let key = Self::key(self.types, ty)?;
        self.aggregate_ids
            .get(&key)
            .copied()
            .ok_or_else(|| format!("aggregate type t{ty} was not collected before encoding"))
    }
}

struct Encoder<'a> {
    declaration_identities: &'a BTreeMap<u32, FunctionIdentity>,
    current_function: &'a FunctionIdentity,
    type_encoder: &'a TypeEncoder<'a>,
    all_functions: &'a BTreeMap<u32, &'a core::Function>,
    // Only the distributed zero-argument Bool constructors are normalized:
    // the self-host Core keeps those literals as direct constructs.
    bool_literal_calls: &'a BTreeMap<u32, u32>,
    locals: BTreeMap<u32, u32>,
    next_local: u32,
}

impl Encoder<'_> {
    fn write_type(&self, output: &mut Vec<u8>, ty: TypeId) -> Result<(), String> {
        push_u32(output, self.type_encoder.id(ty)?);
        Ok(())
    }

    fn bind(&mut self, local: u32) -> Result<u32, String> {
        let normalized = self.next_local;
        self.next_local = self
            .next_local
            .checked_add(1)
            .ok_or_else(|| "normalized local identity overflow".to_owned())?;
        if self.locals.insert(local, normalized).is_some() {
            return Err(format!("Core local l{local} was bound twice"));
        }
        Ok(normalized)
    }

    fn local(&self, local: u32) -> Result<u32, String> {
        self.locals
            .get(&local)
            .copied()
            .ok_or_else(|| format!("Core references unbound local l{local}"))
    }

    fn target(&self, declaration: u32) -> Result<&FunctionIdentity, String> {
        self.declaration_identities
            .get(&declaration)
            .ok_or_else(|| format!("call escaped focused corpus through fn#{declaration}"))
    }

    fn transparent_empty_block<'b>(mut expression: &'b core::Expr) -> &'b core::Expr {
        while let ExprKind::Block { statements, tail } = &expression.kind {
            if !statements.is_empty() {
                break;
            }
            expression = tail;
        }
        expression
    }

    /// Recognize only the bootstrap's exhaustive two-nullary-variant lowering.
    /// Other refinement branches retain semantic join evidence with no source-Core peer.
    fn nullary_variant_dispatch<'b>(
        &self,
        expression: &'b core::Expr,
    ) -> Result<Option<(&'b core::Expr, Vec<(u32, &'b core::Expr)>)>, String> {
        let expression = Self::transparent_empty_block(expression);
        let ExprKind::RefinementBranch {
            subject,
            pattern,
            bindings,
            retire_at_join,
            conditional_at_join,
            positive,
            negative,
            ..
        } = &expression.kind
        else {
            return Ok(None);
        };
        let ExprKind::Local { local, copy: true } = subject.kind else {
            return Ok(None);
        };
        let original_subject = subject.as_ref();
        let mut arms = Vec::new();
        let mut current = (
            pattern,
            bindings,
            retire_at_join,
            conditional_at_join,
            positive,
            negative,
        );
        loop {
            let (pattern, bindings, retire, conditional, positive, negative) = current;
            let core::DecisionPatternKind::Variant { variant, fields } = &pattern.kind else {
                return Ok(None);
            };
            if !fields.is_empty()
                || !bindings.is_empty()
                || !retire.is_empty()
                || !conditional.is_empty()
                || arms.iter().any(|(seen, _)| seen == variant)
            {
                return Ok(None);
            }
            arms.push((*variant, Self::transparent_empty_block(positive)));
            let negative = Self::transparent_empty_block(negative);
            let ExprKind::RefinementBranch {
                subject,
                pattern,
                bindings,
                retire_at_join,
                conditional_at_join,
                positive,
                negative,
                ..
            } = &negative.kind
            else {
                let ExprKind::Call { declaration, args } = &negative.kind else {
                    return Ok(None);
                };
                let Some(function) = self.all_functions.get(declaration) else {
                    return Ok(None);
                };
                if !args.is_empty()
                    || function.name != "unreachable"
                    || !function.no_return
                    || !function.params.is_empty()
                    || function.receiver_mode.is_some()
                    || function.receiver_type != UNIT
                    || !function.receiver_captures.is_empty()
                {
                    return Ok(None);
                }
                break;
            };
            if !matches!(subject.kind, ExprKind::Local { local: found, copy: true } if found == local)
            {
                return Ok(None);
            }
            current = (
                pattern,
                bindings,
                retire_at_join,
                conditional_at_join,
                positive,
                negative,
            );
        }
        if arms.len() != 2 {
            return Ok(None);
        }
        Ok(Some((original_subject, arms)))
    }

    fn write_nullary_variant_dispatch(
        &mut self,
        output: &mut Vec<u8>,
        expression: &core::Expr,
        subject_alias: Option<(u32, &core::Expr)>,
    ) -> Result<(), String> {
        let Some((subject, arms)) = self.nullary_variant_dispatch(expression)? else {
            return Err("unsupported refinement branch in focused typed-Core oracle".into());
        };
        let subject = match (subject_alias, &subject.kind) {
            (
                Some((local, replacement)),
                ExprKind::Local {
                    local: found,
                    copy: true,
                },
            ) if *found == local => replacement,
            (Some(_), _) => {
                return Err("synthetic handle result does not feed its refinement subject".into());
            }
            (None, _) => subject,
        };
        output.push(10);
        self.write_type(output, expression.ty)?;
        self.expression(output, subject)?;
        push_u32(output, arms.len().try_into().unwrap());
        for (variant, body) in arms {
            push_u32(output, variant);
            self.expression(output, body)?;
        }
        Ok(())
    }

    fn expression(&mut self, output: &mut Vec<u8>, expression: &core::Expr) -> Result<(), String> {
        self.type_encoder.id(expression.ty)?;
        if expression.reference.is_some() || !expression.reference_fields.is_empty() {
            return Err(
                "Stage A typed-Core fixture unexpectedly retained reference evidence".into(),
            );
        }

        match &expression.kind {
            ExprKind::Unit => {
                output.push(0);
                self.write_type(output, expression.ty)?;
            }
            ExprKind::Constant(value) => {
                if let Constant::Text(value) = value {
                    output.push(8);
                    self.write_type(output, expression.ty)?;
                    push_string(output, value);
                    return Ok(());
                }
                if let Constant::Bytes(value) = value {
                    output.push(11);
                    self.write_type(output, expression.ty)?;
                    push_u32(output, value.len().try_into().unwrap());
                    output.extend(value);
                    return Ok(());
                }
                output.push(1);
                self.write_type(output, expression.ty)?;
                let raw = match value {
                    Constant::U8(value) => u128::from(*value),
                    Constant::U16(value) => u128::from(*value),
                    Constant::U32(value) => u128::from(*value),
                    Constant::U64(value) => u128::from(*value),
                    Constant::U128(value) => *value,
                    Constant::I8(value) => *value as u128,
                    Constant::I16(value) => *value as u128,
                    Constant::I32(value) => *value as u128,
                    Constant::I64(value) => *value as u128,
                    Constant::I128(value) => *value as u128,
                    Constant::Usize(value) => u128::from(*value),
                    Constant::Isize(value) => *value as u128,
                    Constant::Char(value) => u128::from(*value as u32),
                    _ => {
                        return Err(format!(
                            "unsupported constant in focused typed-Core corpus: {value:?}:t{}",
                            expression.ty
                        ));
                    }
                };
                // Match the self-host probe's four little-endian Core words,
                // rather than truncating every integer to the old u64 wire slot.
                for word in 0..4 {
                    push_u32(output, (raw >> (word * 32)) as u32);
                }
            }
            ExprKind::Local { local, copy } => {
                output.push(2);
                self.write_type(output, expression.ty)?;
                push_u32(output, self.local(*local)?);
                output.push(u8::from(*copy));
            }
            ExprKind::Call { declaration, args }
            | ExprKind::TailCall { declaration, args } => {
                if args.is_empty()
                    && let Some(variant) = self.bool_literal_calls.get(declaration)
                {
                    // The distributed prelude exposes literals as calls; the
                    // self-host Core deliberately records their enum shape.
                    output.push(6);
                    self.write_type(output, expression.ty)?;
                    self.write_type(output, expression.ty)?;
                    push_u32(output, *variant + 1);
                    push_u32(output, 0);
                } else {
                    output.push(if matches!(
                        &expression.kind,
                        ExprKind::TailCall { .. }
                    ) { 4 } else { 3 });
                    self.write_type(output, expression.ty)?;
                    encode_identity(output, self.target(*declaration)?);
                    push_u32(output, args.len().try_into().unwrap());
                    for argument in args {
                        self.expression(output, argument)?;
                    }
                }
            }
            ExprKind::CallSelf { args } => {
                output.push(3);
                self.write_type(output, expression.ty)?;
                encode_identity(output, self.current_function);
                push_u32(output, args.len().try_into().unwrap());
                for argument in args {
                    self.expression(output, argument)?;
                }
            }
            ExprKind::TailCallSelf { args } => {
                output.push(4);
                self.write_type(output, expression.ty)?;
                encode_identity(output, self.current_function);
                push_u32(output, args.len().try_into().unwrap());
                for argument in args {
                    self.expression(output, argument)?;
                }
            }
            ExprKind::Primitive { primitive, args } => {
                output.push(9);
                self.write_type(output, expression.ty)?;
                push_u32(output, *primitive as u32);
                push_u32(output, args.len().try_into().unwrap());
                for argument in args {
                    self.expression(output, argument)?;
                }
            }
            ExprKind::Block { statements, tail } => {
                // Bootstrap materializes a copyable handle subject in a
                // compiler-generated `$handle$result$…` local.  The self host
                // dispatches that source local directly, so erase only this
                // exact administrative binding before emitting tag 10.
                if let [
                    Stmt::Let {
                        local,
                        name,
                        ty,
                        value,
                        ..
                    },
                ] = statements.as_slice()
                    && name.starts_with("$handle$result$")
                    && *ty == value.ty
                    && matches!(value.kind, ExprKind::Local { copy: true, .. })
                    && matches!(
                        Self::transparent_empty_block(tail).kind,
                        ExprKind::RefinementBranch { .. }
                    )
                {
                    return self.write_nullary_variant_dispatch(
                        output,
                        tail,
                        Some((*local, value)),
                    );
                }
                output.push(5);
                self.write_type(output, expression.ty)?;
                push_u32(output, statements.len().try_into().unwrap());
                for statement in statements {
                    self.statement(output, statement)?;
                }
                self.expression(output, tail)?;
            }
            ExprKind::RefinementBranch { .. } => {
                self.write_nullary_variant_dispatch(output, expression, None)?
            }
            ExprKind::Construct {
                nominal,
                variant,
                fields,
            } => {
                if *nominal != expression.ty {
                    return Err(format!(
                        "construction type t{} disagrees with nominal t{nominal}",
                        expression.ty
                    ));
                }
                let expected_fields = match self
                    .type_encoder
                    .types
                    .get(*nominal as usize)
                    .map(Type::representation)
                {
                    Some(Type::Tuple {
                        fields: expected, ..
                    }) => {
                        if variant.is_some() {
                            return Err("tuple construction unexpectedly names a variant".into());
                        }
                        expected.clone()
                    }
                    Some(Type::Struct {
                        fields: expected, ..
                    }) => {
                        if variant.is_some() {
                            return Err("struct construction unexpectedly names a variant".into());
                        }
                        expected.iter().map(|field| field.ty).collect()
                    }
                    Some(Type::Enum {
                        variants: expected, ..
                    }) => {
                        let variant = variant.ok_or_else(|| {
                            "enum construction omitted its resolved variant ordinal".to_owned()
                        })?;
                        expected
                            .get(variant as usize)
                            .ok_or_else(|| {
                                format!("enum construction names unknown variant {variant}")
                            })?
                            .fields
                            .iter()
                            .map(|field| field.ty)
                            .collect()
                    }
                    other => {
                        return Err(format!(
                            "construction names non-aggregate nominal t{nominal}: {other:?}"
                        ));
                    }
                };
                if fields.len() != expected_fields.len() {
                    return Err(format!(
                        "construction has {} Core fields, expected {}",
                        fields.len(),
                        expected_fields.len()
                    ));
                }
                output.push(6);
                self.write_type(output, expression.ty)?;
                self.write_type(output, *nominal)?;
                push_u32(output, variant.map_or(0, |variant| variant + 1));
                push_u32(output, fields.len().try_into().unwrap());
                for (index, (field, expected)) in fields.iter().zip(expected_fields).enumerate() {
                    if field.field != index as u32 {
                        return Err(format!(
                            "construction fields are not in canonical declaration order: expected field {index}, found {}",
                            field.field
                        ));
                    }
                    if field.value.ty != expected {
                        return Err(format!(
                            "construction field {index} has type t{}, expected t{expected}",
                            field.value.ty
                        ));
                    }
                    push_u32(output, field.field);
                    self.expression(output, &field.value)?;
                }
            }
            ExprKind::Project {
                subject,
                field,
                copy,
                variant,
            } => {
                if !copy {
                    return Err("Stage A projection unexpectedly consumes a noncopy field".into());
                }
                let expected = match self
                    .type_encoder
                    .types
                    .get(subject.ty as usize)
                    .map(Type::representation)
                {
                    Some(Type::Tuple { fields, .. }) => {
                        if variant.is_some() {
                            return Err("tuple projection unexpectedly names a variant".into());
                        }
                        fields.get(*field as usize).copied()
                    }
                    Some(Type::Struct { fields, .. }) => {
                        if variant.is_some() {
                            return Err("struct projection unexpectedly names a variant".into());
                        }
                        fields.get(*field as usize).map(|field| field.ty)
                    }
                    Some(Type::Enum { variants, .. }) => {
                        let variant = variant.ok_or_else(|| {
                            "enum payload projection lacks a dominating variant proof".to_owned()
                        })?;
                        variants
                            .get(variant as usize)
                            .and_then(|variant| variant.fields.get(*field as usize))
                            .map(|field| field.ty)
                    }
                    other => {
                        return Err(format!(
                            "projection subject t{} is not an aggregate: {other:?}",
                            subject.ty
                        ));
                    }
                }
                .ok_or_else(|| {
                    format!(
                        "projection names missing field {field} of subject t{}",
                        subject.ty
                    )
                })?;
                if expression.ty != expected {
                    return Err(format!(
                        "projection result has type t{}, expected t{expected}",
                        expression.ty
                    ));
                }
                output.push(7);
                self.write_type(output, expression.ty)?;
                push_u32(output, *field);
                output.push(u8::from(*copy));
                push_u32(output, variant.map_or(0, |variant| variant + 1));
                self.expression(output, subject)?;
            }
            other => {
                return Err(format!(
                    "unsupported wrapper in focused typed-Core oracle: {other:?}"
                ));
            }
        }
        Ok(())
    }

    fn statement(&mut self, output: &mut Vec<u8>, statement: &Stmt) -> Result<(), String> {
        match statement {
            Stmt::Let {
                local,
                name,
                ty,
                value,
                ..
            } => {
                self.type_encoder.id(*ty)?;
                let normalized = self.bind(*local)?;
                output.push(1);
                push_u32(output, normalized);
                push_string(output, name);
                self.write_type(output, *ty)?;
                self.expression(output, value)
            }
            Stmt::Expr(expression) => {
                output.push(2);
                self.expression(output, expression)
            }
            other => Err(format!(
                "unsupported statement in focused typed-Core oracle: {other:?}"
            )),
        }
    }
}

fn bool_call_variant(expression: &core::Expr, direct: &BTreeMap<u32, u32>) -> Option<u32> {
    match &expression.kind {
        ExprKind::Block { statements, tail } if statements.is_empty() => {
            bool_call_variant(tail, direct)
        }
        ExprKind::Call { declaration, args } | ExprKind::TailCall { declaration, args }
            if args.is_empty() => direct.get(declaration).copied(),
        _ => None,
    }
}

fn is_distributed_bool_abi(types: &[Type], function: &core::Function) -> bool {
    function.params.is_empty()
        && function.receiver_mode.is_none()
        && !function.no_return
        && function.outward_protocols.is_empty()
        && matches!(
            types.get(function.result as usize).map(Type::representation),
            // Source Bool is the distributed `Result<Unit, Unit>` alias.
            Some(Type::Enum { name, .. }) if name == "Result"
        )
}

fn distributed_bool_literal_calls(
    types: &[Type],
    core: &core::Program,
) -> BTreeMap<u32, u32> {
    let direct = core.functions.iter().filter_map(|function| {
        let variant = match function.name.as_str() {
            "__g1_bool_true" => 0,
            "__g1_bool_false" => 1,
            _ => return None,
        };
        // Only the exact prelude constructor definitions are roots.  Their
        // ABI prevents arbitrary source or external zero-argument calls from
        // entering the normalization set.
        if is_distributed_bool_abi(types, function) && !function.global_factory {
            Some((function.declaration, variant))
        } else { None }
    }).collect::<BTreeMap<_, _>>();
    let mut calls = direct.clone();
    for function in &core.functions {
        // Source uses resolve through compiler-generated global factories.
        // Admit one only when its complete body is an empty block forwarding
        // to an exact prelude root above.
        if function.global_factory && is_distributed_bool_abi(types, function)
            && let Some(variant) = bool_call_variant(&function.body, &direct)
        {
            calls.insert(function.declaration, variant);
        }
    }
    calls
}

fn encode_success(
    output: &mut Vec<u8>,
    bundle: &SourceBundle,
    resolved: &ResolvedProgram,
    original_len: usize,
    types: &[Type],
    core: &core::Program,
) -> Result<(), String> {
    let sources = source_functions(resolved, bundle, original_len)?;
    let by_backend = core
        .functions
        .iter()
        .map(|function| (function.name.as_str(), function))
        .collect::<BTreeMap<_, _>>();
    let all_functions = core
        .functions
        .iter()
        .map(|function| (function.declaration, function))
        .collect::<BTreeMap<_, _>>();

    let mut declarations = BTreeMap::new();
    let mut seen_identities = BTreeSet::new();
    for source in &sources {
        if !seen_identities.insert(source.identity.clone()) {
            return Err(format!("duplicate source identity {:?}", source.identity));
        }
        let function = by_backend
            .get(source.backend_name.as_str())
            .ok_or_else(|| {
                format!(
                    "no Core function corresponds to source identity {:?} ({:?})",
                    source.identity, source.backend_name
                )
            })?;
        if declarations
            .insert(function.declaration, source.identity.clone())
            .is_some()
        {
            return Err(format!(
                "two source functions share Core declaration fn#{}",
                function.declaration
            ));
        }
    }
    let source_core_functions = sources
        .iter()
        .map(|source| by_backend[source.backend_name.as_str()])
        .collect::<Vec<_>>();
    let type_encoder = TypeEncoder::new(types, &source_core_functions)?;
    let bool_literal_calls = distributed_bool_literal_calls(types, core);

    push_u32(output, sources.len().try_into().unwrap());
    for source in &sources {
        let function = by_backend[source.backend_name.as_str()];
        if function.global_factory
            || function.receiver_mode.is_some()
            || function.receiver_type != UNIT
            || !function.receiver_captures.is_empty()
            || function.no_return
            || !function.outward_protocols.is_empty()
            || !function.regions.is_empty()
        {
            return Err(format!(
                "focused source function acquired unsupported Core ABI state: {function:?}"
            ));
        }
        type_encoder.id(function.result)?;

        encode_identity(output, &source.identity);
        push_u32(output, function.params.len().try_into().unwrap());
        let mut encoder = Encoder {
            declaration_identities: &declarations,
            current_function: &source.identity,
            type_encoder: &type_encoder,
            all_functions: &all_functions,
            bool_literal_calls: &bool_literal_calls,
            locals: BTreeMap::new(),
            next_local: 0,
        };
        for parameter in &function.params {
            type_encoder.id(parameter.ty)?;
            let normalized = encoder.bind(parameter.local)?;
            push_u32(output, normalized);
            push_string(output, &parameter.name);
            encoder.write_type(output, parameter.ty)?;
        }
        encoder.write_type(output, function.result)?;
        encoder.expression(output, &function.body)?;
    }
    Ok(())
}

fn encode_rust_core(output: &mut Vec<u8>, source: &str) {
    if grandiose::lexer::lex(source).is_err() {
        output.push(1);
        return;
    }

    let augmented = format!("{source}{WRAPPER}");
    let bundle = SourceBundle::distributed(Segment::new(INPUT_NAME, augmented), []);
    let Ok(program) = grandiose::modules::parse_bundle(&bundle) else {
        output.push(3);
        return;
    };
    let Ok(resolved) = grandiose::modules::resolve_program(&bundle, program) else {
        output.push(3);
        return;
    };
    let Ok(phases) = grandiose::compile_bundle_to_phases_with_options(
        &bundle,
        CompileOptions {
            optimization_level: OptimizationLevel::O0,
        },
    ) else {
        output.push(4);
        return;
    };

    let mut encoded = Vec::new();
    encode_success(
        &mut encoded,
        &bundle,
        &resolved,
        source.len(),
        &phases.artifact.types,
        &phases.core,
    )
    .unwrap_or_else(|error| panic!("Rust Core projection failed for {source:?}: {error}"));
    output.push(0);
    output.extend(encoded);
}

fn corpus(directory: &Path) -> Vec<PathBuf> {
    let valid = [
        "probe_unit() { () }",
        // Bool is a prelude aggregate even when the focused probe has no
        // distributed-prelude declaration arena.  Keep literals and an ABI
        // parameter/return path separate from conditional lowering.
        "probe_true() -> Bool { true }",
        "probe_false() -> Bool { false }",
        "probe_bool_identity(value: Bool) -> Bool { value }",
        "probe_i64() -> i64 { 7 } probe_u64() -> u64 { 7 }",
        "probe_text() -> Text { \"hello, 🌍\" } probe_character() -> char { '💩' } \
         probe_byte() -> u8 { b'\\xff' }",
        // Full-width integer literals exercise the fourth Core word.  Before
        // the probe's 128-bit wire correction this valid native-oracle case
        // was rejected as `IntegerEncodingOverflow`.
        "probe_u128_max() -> u128 { 340282366920938463463374607431768211455 }",
        "probe_param(value: i64) -> i64 { value }",
        // Structural `-` must remain available without a prefix-fixity header.
        // It lowers to the checked integer-negation primitive, not a call.
        "probe_negate(value: i64) -> i64 { -value }",
        "probe_target(value: i64) -> i64 { value } \
         probe_forward(value: i64) -> i64 { probe_target(value) }",
        "probe_let() -> i64 { let value = 1; value }",
        "probe_chain() -> i64 { let first = 1; let second = first; second }",
        "probe_shadow(value: i64) -> i64 { \
         { let value = 2; value }; value }",
        "probe_target(value: i64) -> i64 { value } \
         probe_statement(value: i64) { probe_target(value); () }",
        "type Count = u64; \
         probe_scalar_alias(value: Count) -> Count { value }",
        "type Empty = Unit; \
         probe_unit_alias(value: Empty) -> Empty { value }",
        "type BackwardBase = i64; type Backward = BackwardBase; \
         type Forward = ForwardTarget; type ForwardTarget = u64; \
         probe_backward(value: Backward) -> Backward { value } \
         probe_forward_alias(value: Forward) -> Forward { value }",
        "mod aliases { pub type Count = u64; } \
         probe_qualified_alias(value: aliases::Count) -> aliases::Count { value }",
        "enum GenericResult<T, E> { Ok(T), Err(E) } \
         struct GenericPair<T, U> { left: T, right: U } \
         probe_generic_interfaces() { () }",
        "struct CharacterSlot { value: char } \
         probe_character_interface() { () }",
        // Keep decoded escapes on the Typed-Core wire: bytes are not text and
        // must retain a NUL payload rather than source spelling.
        "probe_bytes() -> Bytes { b\"ok\\x00\" }",
        "mod imported { pub struct TokenSpan { start: usize } } \
         use imported::TokenSpan; \
         struct ImportedHolder { span: TokenSpan } \
         probe_imported_interface() { () }",
        "struct Boxed<T> { value: T } \
         mod local_alias { \
             pub struct Tag {} \
             pub type LocalId = Boxed<Tag>; \
             pub struct Holder { value: LocalId } \
         } \
         probe_local_generic_alias() { () }",
        "mod qualified { \
             pub struct Range<T> { value: T } \
             pub mod nested { \
                 pub type LocalRange = super::Range<u64>; \
                 pub struct Holder { value: LocalRange } \
             } \
         } \
         probe_super_qualified_interface() { () }",
        "mod selected { pub struct LeftTag {} pub type TypeId = LeftTag; } \
         mod unselected { pub struct RightTag {} pub type TypeId = RightTag; } \
         use selected::TypeId; \
         struct ImportedDuplicateHolder { value: TypeId } \
         probe_exact_import_identity() { () }",
        "mod module_source { \
             pub mod imported_module { pub struct Thing {} } \
         } \
         mod module_user { \
             use super::module_source::imported_module; \
             pub struct Holder { value: imported_module::Thing } \
         } \
         probe_imported_module_identity() { () }",
        // Canonical wire support is restricted to exhaustive, nullary local enums.
        "enum ProbeChoice { Left, Right } \
         probe_variant_dispatch(value: ProbeChoice) -> i64 { \
             handle value { ProbeChoice::Left => 1, ProbeChoice::Right => 2 } \
         }",
    ];
    let errors = [
        "probe_bad_result() -> i64 { () }",
        "probe_bad_default_result() { 1 }",
        "probe_target(value: i64) -> i64 { value } \
         probe_bad_arity() -> i64 { probe_target() }",
        "probe_target(value: u64) -> u64 { value } \
         probe_bad_argument(value: i64) -> u64 { probe_target(value) }",
        "probe_value() -> i64 { 1 } \
         probe_bad_call_result() -> u64 { probe_value() }",
        "type Left = Right; type Right = Left; \
         probe_alias_cycle(value: Left) -> Left { value }",
    ];

    let mut paths = Vec::new();
    for (index, source) in valid.into_iter().enumerate() {
        let path = directory.join(format!("valid-{index}.glorious"));
        fs::write(&path, source).unwrap();
        paths.push(path);
    }
    for (index, source) in errors.into_iter().enumerate() {
        let path = directory.join(format!("error-{index}.glorious"));
        fs::write(&path, source).unwrap();
        paths.push(path);
    }
    paths
}

fn stage_a_corpus(directory: &Path) -> Vec<PathBuf> {
    let valid = [
        "singleton(value: i64) -> (i64,) { (value,) }",
        "pair(left: i64, right: u64) -> (i64, u64) { (left, right) } \
         second(value: (i64, u64)) -> u64 { value.1 }",
        "inferred(value: i64) -> i64 { let pair = (value, 2); pair.0 }",
        "struct Pair { left: i64, right: u64 } \
         make(left: i64, right: u64) -> Pair { Pair { right: right, left: left } } \
         read(value: Pair) -> u64 { value.right }",
        "struct Pair { left: i64, right: u64 } \
         left_value() -> i64 { 1 } right_value() -> u64 { 2 } \
         make() -> Pair { \
             Pair { right: right_value(), left: left_value() } \
         }",
        "struct Inner { value: i64 } struct Outer { inner: Inner, marker: u64 } \
         make(value: i64) -> Outer { \
             Outer { marker: 7, inner: Inner { value: value } } \
         } \
         read(value: Outer) -> i64 { value.inner.value }",
        "enum Choice { Empty, Number(i64), Pair(i64, u64) } \
         empty() -> Choice { Choice::Empty } \
         unary(value: i64) -> Choice { Choice::Number(value) } \
         multiple(left: i64, right: u64) -> Choice { Choice::Pair(left, right) }",
        "struct Pair { left: i64, right: u64 } \
         pair_passthrough(value: Pair) -> Pair { value } \
         forward(left: i64, right: u64) -> Pair { \
             pair_passthrough(Pair { left: left, right: right }) \
         }",
        "struct Pair { left: i64, right: i64 } \
         repeated(value: i64) -> Pair { \
             Pair { right: value, left: value } \
         }",
        "tuple_identity(value: (i64, u64)) -> (i64, u64) { value } \
         tuple_forward(left: i64, right: u64) -> (i64, u64) { \
             tuple_identity((left, right)) \
         }",
        "struct Pair { left: i64, right: u64 } type PairAlias = Pair; \
         make_alias(left: i64, right: u64) -> PairAlias { \
             Pair { left: left, right: right } \
         } \
         read_alias(value: PairAlias) -> u64 { value.right }",
    ];
    let errors = [
        "struct Pair { left: i64 } bad() -> Pair { Pair { nope: 1 } }",
        "struct Pair { left: i64 } bad() -> Pair { Pair { left: 1, left: 2 } }",
        "struct Pair { left: i64, right: i64 } bad() -> Pair { Pair { left: 1 } }",
        "mod hidden { pub struct Vault { private value: i64 } } \
         bad() -> hidden::Vault { hidden::Vault { value: 1 } }",
        "bad(value: (i64, u64)) -> i64 { value.2 }",
        "enum Choice { Number(i64) } bad() -> Choice { Choice::Number() }",
        "enum Choice { Number(i64) } bad() -> Choice { Choice::Number(()) }",
        "enum Choice { Empty } bad() -> Choice { Choice::Missing }",
        "struct A { b: B } struct B { a: A } bad() { () }",
    ];

    let mut paths = Vec::new();
    for (index, source) in valid.into_iter().enumerate() {
        let path = directory.join(format!("aggregate-valid-{index}.glorious"));
        fs::write(&path, source).unwrap();
        paths.push(path);
    }
    for (index, source) in errors.into_iter().enumerate() {
        let path = directory.join(format!("aggregate-error-{index}.glorious"));
        fs::write(&path, source).unwrap();
        paths.push(path);
    }
    paths
}

#[test]
fn rust_typed_core_oracle_classifies_the_focused_corpus() {
    let directory = tempfile::tempdir().unwrap();
    for path in corpus(directory.path()) {
        let mut encoded = Vec::new();
        encode_rust_core(&mut encoded, &fs::read_to_string(&path).unwrap());
        let expected = if path
            .file_name()
            .unwrap()
            .to_string_lossy()
            .starts_with("valid-")
        {
            0
        } else {
            4
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
fn rust_typed_core_oracle_classifies_stage_a_aggregates() {
    let directory = tempfile::tempdir().unwrap();
    for path in stage_a_corpus(directory.path()) {
        let mut encoded = Vec::new();
        encode_rust_core(&mut encoded, &fs::read_to_string(&path).unwrap());
        let name = path.file_name().unwrap().to_string_lossy();
        let expected = if name.starts_with("aggregate-valid-") {
            0
        } else if name == "aggregate-error-3.glorious" {
            3
        } else {
            4
        };
        assert_eq!(
            encoded.first().copied(),
            Some(expected),
            "unexpected Stage A Rust-oracle status for input {}: {encoded:?}",
            path.display()
        );
    }
}

#[test]
fn self_hosted_effect_interfaces_match_rust_semantics_and_rejections() {
    let phases = grandiose::compile_bundle_to_phases_with_options(
        &self_host_effect_bundle(),
        CompileOptions {
            optimization_level: OptimizationLevel::O2,
        },
    )
    .unwrap();
    let function = artifact_function_id(&phases.artifact, ":effect_interface_bytes");
    let entry = phases.artifact.entry_function.unwrap();
    let verified = verify(phases.artifact.clone()).unwrap();

    let source = "trait Marker {} \
        effect Control<'a, T, E: EffectRow> where T: Marker<T, Out = T> { \
        [0, infinity] choose<U>(left: &'a T, right: U) -> (T, U) \
            where for<'b> U: !Marker<[0, *], Out = { | E }>; \
        [0, 0] optional(value: Array<T>) -> Unit where 'a: 'a; \
        [2, 4] repeat(value: u16) -> u16; \
        stop(reason: Text) -> !; \
    }";
    let expected = encode_rust_effect_interfaces(source);
    let value = Vm::with_host(
        verified.clone(),
        ["process.args", "fs.read", "fs.write", "diagnostic"],
        SystemHost::new(Vec::<OsString>::new()),
    )
    .unwrap()
    .run(function, vec![Value::Text(source.to_owned().into())])
    .unwrap();
    let Value::Bytes(actual) = value else {
        panic!("effect interface probe returned {value:?}");
    };
    assert_eq!(actual.as_ref(), expected.as_slice());

    let rejected = [
        // The Rust parser rejects a duplicate binder before validation and
        // therefore has no stable G0113 code. The self-host header graph
        // intentionally preserves it until semantic collection, where 101 is
        // the precise duplicate-effect-generic classification.
        ("effect Bad<T, T> { stop() -> ! }", None, 101_u8),
        (
            "effect Bad<T> { stop<T>(value: T) -> ! }",
            Some("G0113"),
            103_u8,
        ),
        (
            "effect Bad { first() -> ! first(value: u8) -> ! }",
            Some("G0003"),
            102_u8,
        ),
        ("effect Bad { [0, 1] stop() -> ! }", Some("G0004"), 104_u8),
        (
            "effect Bad { [2, 1] choose() -> u8 }",
            Some("G0005"),
            105_u8,
        ),
        (
            "trait Marker {} effect Bad<T> where T: Marker<Out = T, Out = T> {}",
            None,
            3_u8,
        ),
    ];
    for &(invalid, rust_code, self_host_code) in &rejected {
        let tokens = grandiose::lexer::lex(invalid).unwrap();
        match (grandiose::parser::parse(tokens), rust_code) {
            (Err(_), None) => {}
            (Ok(program), Some(code)) => {
                let errors = grandiose::validate::validate(&program).unwrap_err();
                assert!(
                    errors
                        .iter()
                        .any(|error| error.code.as_deref() == Some(code)),
                    "Rust oracle did not report {code} for {invalid:?}: {errors:#?}"
                );
            }
            (Err(error), Some(code)) => {
                panic!("Rust parser rejected before expected {code}: {error:#?}")
            }
            (Ok(_), None) => panic!("Rust parser unexpectedly accepted {invalid:?}"),
        }
        let value = Vm::with_host(
            verified.clone(),
            ["process.args", "fs.read", "fs.write", "diagnostic"],
            SystemHost::new(Vec::<OsString>::new()),
        )
        .unwrap()
        .run(function, vec![Value::Text(invalid.to_owned().into())])
        .unwrap();
        let Value::Bytes(actual) = value else {
            panic!("effect rejection probe returned {value:?}");
        };
        assert_eq!(actual.as_ref(), &[self_host_code], "input: {invalid}");
    }

    let directory = tempfile::tempdir().unwrap();
    let mut paths = Vec::new();
    let mut expected_all = Vec::new();
    push_u32(&mut expected_all, (1 + rejected.len()).try_into().unwrap());
    expected_all.extend(&expected);
    let positive_path = directory.path().join("effect-valid.glorious");
    fs::write(&positive_path, source).unwrap();
    paths.push(positive_path);
    for (index, (invalid, _, self_host_code)) in rejected.iter().enumerate() {
        let path = directory
            .path()
            .join(format!("effect-error-{index}.glorious"));
        fs::write(&path, invalid).unwrap();
        paths.push(path);
        expected_all.push(*self_host_code);
    }

    let vm_path = directory.path().join("effect-vm.bin");
    let vm_args = std::iter::once(vm_path.clone().into_os_string())
        .chain(paths.iter().map(|path| path.clone().into_os_string()))
        .collect::<Vec<_>>();
    let vm = Vm::with_host(
        verified,
        ["process.args", "fs.read", "fs.write", "diagnostic"],
        SystemHost::new(vm_args),
    )
    .unwrap();
    assert_eq!(vm.run(entry, vec![]).unwrap(), Value::Unit);
    assert_eq!(fs::read(&vm_path).unwrap(), expected_all);

    let module = grandiose::emit_llvm_ir(&phases, &LlvmOptions::default()).unwrap();
    let llvm = directory.path().join("self-host-effect-interfaces.ll");
    let executable = directory.path().join("self-host-effect-interfaces");
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
    assert!(
        clang.status.success(),
        "{}",
        String::from_utf8_lossy(&clang.stderr)
    );
    let native_path = directory.path().join("effect-native.bin");
    let native = Command::new(&executable)
        .arg(&native_path)
        .args(&paths)
        .output()
        .unwrap();
    assert!(
        native.status.success(),
        "native effect interface status: {:?}\n{}",
        native.status,
        String::from_utf8_lossy(&native.stderr)
    );
    assert_eq!(fs::read(native_path).unwrap(), expected_all);
}

#[test]
// Header/interface-only parity probe. Body execution, handlers, resumptions,
// and outward-call metadata remain outside this focused partial corpus.
fn self_hosted_effect_control_headers_match_rust_oracle() {
    // These declarations are distilled from the effect-control integration
    // suites.  Keep both accepted rows and stable header rejections here: the
    // probe must agree with the bootstrap parser/validator, not merely parse
    // a happy-path effect.
    let corpus = [
        (
            "effect Ask { [1,1] ask() -> i64 }\nanswer() -> i64 / {Ask} { perform Ask::ask() }",
            true,
        ),
        (
            "effect Pick<const N: u32> { pick() -> ! }\nselected() -> / {Pick<1>} { () }",
            true,
        ),
        (
            "effect Fail<E> { fail(error: E) -> ! }\nselected() -> / {Fail<i64>} { () }",
            true,
        ),
        // Generic effect heads and generic operations are required by the
        // compiler's own collection protocols. Keep a nested generic result,
        // an operation-local where clause, and a following operation together:
        // the header cursor must not consume the latter as part of `where`.
        (
            "effect Convert<T> { convert<U>(value: U) -> U where U: Copy; finish(value: T) -> T }",
            true,
        ),
        (
            "effect Relay<'scope, const N: u32, E: EffectRow> { [0,1] forward<U>(value: U) -> U where U: Copy; stop() -> ! }",
            true,
        ),
        // shared_handler_resumption_quantities.rs: shared terminal/resumptive
        // alternatives carry [0,1], [1,1], or [2,2] resumption quantities plus
        // multi-operation terminal-only Gate heads.
        ("effect Carry { [0,1] take() -> i64 }", true),
        ("effect Carry { [1,1] take() -> i64 }", true),
        ("effect Carry { [2,2] take() -> i64 }", true),
        ("effect Gate { left() -> ! right() -> ! }", true),
        ("effect Gate { stop() -> ! [1,1] inspect() -> i64 }", true),
        // resumption_closure_capture.rs: exact/optional captures hand an
        // effectful closure one resumable quantity.
        ("effect Pick { [2,2] choose() -> i64 }", true),
        ("effect Stop { [0,1] stop() -> i64 }", true),
        // tail_resumption_acceptance.rs: tail is only legal for terminal,
        // finite one-shot continuations, so the accepted heads are one-shot.
        ("effect Ask { [1,1] ask() -> i64 }", true),
        ("effect Maybe { [0,1] ask() -> i64 }", true),
        ("effect Replay { [2,2] replay() -> i64 }", true),
        (
            "effect Bad<T, T> { stop() -> ! }",
            false,
        ),
        (
            "effect Bad { first() -> ! first(value: u8) -> ! }",
            false,
        ),
        (
            "effect Bad { [2,1] stop() -> u8 }",
            false,
        ),
    ];
    let phases = grandiose::compile_bundle_to_phases_with_options(
        &self_host_effect_bundle(),
        CompileOptions { optimization_level: OptimizationLevel::O2 },
    )
    .unwrap();
    let function = artifact_function_id(&phases.artifact, ":effect_interface_bytes");
    let vm = Vm::with_host(
        verify(phases.artifact).unwrap(),
        ["process.args", "fs.read", "fs.write", "diagnostic"],
        SystemHost::new(Vec::<OsString>::new()),
    )
    .unwrap();
    for (source, accepted) in corpus {
        // These are deliberately header-focused fixtures, but the bootstrap
        // validator only accepts complete programs. Add a neutral entry point
        // before asking either compiler for the accept/reject result.
        let source = format!("{source}\nmain() -> {{ () }}");
        let rust = grandiose::lexer::lex(&source)
            .ok()
            .and_then(|tokens| grandiose::parser::parse(tokens).ok())
            .and_then(|program| grandiose::validate::validate(&program).ok())
            .is_some();
        assert_eq!(rust, accepted, "bad Rust-oracle fixture: {source}");
        let value = vm.run(function, vec![Value::Text(source.clone().into())]).unwrap();
        let Value::Bytes(bytes) = value else { panic!("effect probe returned non-bytes"); };
        assert_eq!(bytes.first().copied() == Some(0), accepted, "source: {source}");
    }
}

#[test]
// Trait associated items are header-only at this stage: the bootstrap parser
// accepts their generic declarations/definitions even though the self-host
// trait database has not yet lowered their values.  Keep this oracle at the
// parser boundary so later semantic work cannot accidentally regress the
// declaration scan needed to compile trait-heavy sources.
fn self_hosted_trait_associated_item_headers_match_rust_oracle() {
    let corpus = [
        "trait Family<T> { type Member<U>; }",
        "trait Family { type Member<U>; } impl<T> Family for T { type Member<U> = U; }",
        "trait Carrier { type Effects<U>: EffectRow; } \
         impl<T> Carrier for T { type Effects<U> = {}; }",
    ];
    let phases = grandiose::compile_bundle_to_phases_with_options(
        &self_host_effect_bundle(),
        CompileOptions { optimization_level: OptimizationLevel::O2 },
    )
    .unwrap();
    let function = artifact_function_id(&phases.artifact, ":effect_interface_bytes");
    let vm = Vm::with_host(
        verify(phases.artifact).unwrap(),
        ["process.args", "fs.read", "fs.write", "diagnostic"],
        SystemHost::new(Vec::<OsString>::new()),
    )
    .unwrap();
    for declaration in corpus {
        let source = format!("{declaration}\nmain() -> {{ () }}");
        let rust = grandiose::lexer::lex(&source)
            .ok()
            .and_then(|tokens| grandiose::parser::parse(tokens).ok())
            .and_then(|program| grandiose::validate::validate(&program).ok())
            .is_some();
        assert!(rust, "bad Rust-oracle fixture: {source}");
        let value = vm.run(function, vec![Value::Text(source.clone().into())]).unwrap();
        let Value::Bytes(bytes) = value else { panic!("trait probe returned non-bytes"); };
        assert_eq!(bytes.first().copied(), Some(0), "source: {source}");
    }
}

#[test]
// Resumption-quantity interface parity distilled from the finite-resumption,
// multishot, quantity-breadth, nested-handler, and late-resumption integration
// suites. The self-host frontend currently elaborates effect interfaces
// (operation resumption bounds and terminal shape) but not yet effect bodies
// (`perform`/`resume`/`cancel`), so the positive corpus here is header-only and
// this suite remains `partial`: body execution and under/over-resumption
// rejections are intentionally outside this focused oracle.
fn self_hosted_resumption_quantity_interfaces_match_rust_oracle() {
    let phases = grandiose::compile_bundle_to_phases_with_options(
        &self_host_effect_bundle(),
        CompileOptions {
            optimization_level: OptimizationLevel::O2,
        },
    )
    .unwrap();
    let function = artifact_function_id(&phases.artifact, ":effect_interface_bytes");
    let vm = Vm::with_host(
        verify(phases.artifact).unwrap(),
        ["process.args", "fs.read", "fs.write", "diagnostic"],
        SystemHost::new(Vec::<OsString>::new()),
    )
    .unwrap();

    // Strong positive: the operation bound (lower/upper) and terminal shape are
    // normalized to identical bytes by the bootstrap oracle and the self-host
    // probe for a finite-bounded, multi-shot effect operation set.
    let positive = concat!(
        "effect Control { ",
        "[1,1] once(value: i64) -> i64; ",
        "[2,2] twice() -> i64; ",
        "[0,2] optional(value: i64) -> i64; ",
        "[4,4] four() -> i64; ",
        "stop(reason: Text) -> !; ",
        "}",
    );
    let expected = encode_rust_effect_interfaces(positive);
    let value = vm
        .run(function, vec![Value::Text(positive.to_owned().into())])
        .unwrap();
    let Value::Bytes(actual) = value else {
        panic!("effect probe returned {value:?}");
    };
    assert_eq!(
        actual.as_ref(),
        expected.as_slice(),
        "finite resumption-quantity interface bytes diverged"
    );

    // Finite-bound declarations drawn from the assigned suites, plus stable
    // header rejections. Acceptance matches the bootstrap parser/validator.
    let corpus = [
        // finite_resumption_quantities.rs
        ("effect Choose { [4,4] choose() -> i64 }", true),
        // multishot_effects.rs
        ("effect Choose { [2,2] choose() -> i64 }", true),
        // resumption_quantity_breadth.rs
        ("effect Choice { [0,2] choose() -> i64 }", true),
        ("effect Choice { [1,2] choose() -> i64 }", true),
        ("effect Choice { [1,1] choose() -> i64 }", true),
        // late_resumption_regressions.rs / nested_captured_handlers.rs
        ("effect Ask { [1,1] ask() -> i64 }", true),
        ("effect Stop { stop() -> ! }", true),
        // Present in the breadth suite; rejected only at the later bytecode
        // phase, so the shared header/interface oracle accepts it like the
        // bootstrap validator.
        ("effect Choice { [1,infinity] choose() -> i64 }", true),
        // Invalid interval and terminal-with-quantity rejections.
        ("effect Bad { [2, 1] stop() -> u8 }", false),
        ("effect Bad { [0, 1] stop() -> ! }", false),
    ];
    for (source, accepted) in corpus {
        // Keep the corpus header-focused while validating complete programs in
        // the bootstrap oracle and the self-host probe alike.
        let source = format!("{source}\nmain() -> {{ () }}");
        let rust = grandiose::lexer::lex(&source)
            .ok()
            .and_then(|tokens| grandiose::parser::parse(tokens).ok())
            .and_then(|program| grandiose::validate::validate(&program).ok())
            .is_some();
        assert_eq!(rust, accepted, "fixture Rust-oracle outcome: {source}");
        let value = vm
            .run(function, vec![Value::Text(source.clone().into())])
            .unwrap();
        let Value::Bytes(bytes) = value else {
            panic!("effect probe returned {value:?}");
        };
        assert_eq!(
            bytes.first().copied() == Some(0),
            accepted,
            "self-host probe status: {source}"
        );
    }
}

#[test]
fn self_host_effect_core_foundation_retains_control_and_rejects_lowering() {
    // This is an architectural contract, not a claim that the self-hosted
    // compiler executes effects yet.  The Core shapes must stay distinct from
    // ordinary calls, and lowering must keep rejecting them until one-shot
    // continuation cleanup and quantity checking are implemented.
    let root = repository_root();
    let core = fs::read_to_string(
        root.join("self-host/src/frontend/elaboration/elaboration.glorious"),
    )
    .unwrap();
    for required in [
        "Perform(InterfaceEffectOperationId, OperandRange)",
        "Resume(CoreValueId, CoreValueId)",
        "Handle(CoreComputationId, CoreHandlerClauseRange)",
        "pub struct CoreHandlerClause",
        "resumption: Option<CoreLocalId>",
        "CoreComputationView::Perform",
        "CoreComputationView::Resume",
        "CoreComputationView::Handle",
    ] {
        assert!(core.contains(required), "missing Typed Core effect foundation: {required}");
    }
    let lowering = fs::read_to_string(
        root.join("self-host/src/backend/lowering/lowering.glorious"),
    )
    .unwrap();
    assert!(lowering.contains("EffectControlNotLowered(CoreComputationId)"));
    assert_eq!(lowering.matches("Result::Err(LoweringError::EffectControlNotLowered(id))").count(), 3);
}

#[test]
fn self_host_effect_row_summary_is_conservative_and_keeps_fixed_point_edges() {
    // This is intentionally a Core-model gate.  It proves the first effect
    // analysis pass is a monotone demand/edge summary: handler syntax alone
    // cannot erase a `perform` before a future coverage pass proves every
    // operation and pattern path is closed.
    let root = repository_root();
    let core = fs::read_to_string(
        root.join("self-host/src/frontend/elaboration/elaboration.glorious"),
    )
    .unwrap();
    for required in [
        "pub struct CoreEffectSummary",
        "required_instances: Vec<EffectInstanceId>",
        "handler_candidates: Vec<EffectInstanceId>",
        "direct_calls: Vec<CallableInstanceId>",
        "indirect_calls: Vec<CallableSignatureId>",
        "pub core_effect_summary(body: &TypedBody) -> CoreEffectSummary",
        "CoreComputationView::Perform(_, instance, _, _)",
        "CoreComputationView::Handle(_, _, clauses)",
        "CoreComputationView::Call(_, _, instance, _)",
        "CoreComputationView::CallIndirect(_, _, signature, _)",
        "core_effect_summary_handler_candidates",
        "handlers are candidates only, never proof",
    ] {
        assert!(core.contains(required), "missing effect-row summary foundation: {required}");
    }
    let probe = fs::read_to_string(root.join("self-host/src/probe/elaboration/elaboration.glorious"))
        .unwrap();
    for required in [
        "pub core_effect_summary_shape(",
        "core_effect_summary(body)",
        "core_effect_summary_required_count",
        "core_effect_summary_handler_candidate_count",
        "core_effect_summary_direct_call_count",
        "core_effect_summary_indirect_call_count",
        "core_effect_summary_resume_count",
    ] {
        assert!(probe.contains(required), "missing effect-row summary probe: {required}");
    }
}

#[test]
fn self_host_callable_core_retains_ordered_closure_sites_and_indirect_calls() {
    // This is a Core-model gate: closure layout and instruction selection
    // belong to the future backend integration, but Typed Core must preserve
    // all semantic input deterministically before that work starts.
    let root = repository_root();
    let core = fs::read_to_string(
        root.join("self-host/src/frontend/elaboration/elaboration.glorious"),
    )
    .unwrap();
    for required in [
        "Callable(CallableSignatureId)",
        "pub struct CallableSignature",
        "pub struct ClosureSiteDescriptor",
        "pub struct CoreClosureCapture",
        "pub enum CoreCaptureMode { Borrow, Copy, Move }",
        "Closure(ClosureSiteId)",
        "CallIndirect(CoreValueId, CallableSignatureId, OperandRange)",
        "closure_captures_are_ordered",
        "push_closure_value",
        "push_indirect_call",
        "CoreValueView::Closure",
        "CoreComputationView::CallIndirect",
        "interface_callable_signature_effect_tail",
        "signature: CallableSignature\n) -> Slice<'a, TypeId>",
        "callable_signature_parameter_slice",
        "callable_signature_effect_slice",
    ] {
        assert!(core.contains(required), "missing callable Typed Core foundation: {required}");
    }

    let lowering = fs::read_to_string(
        root.join("self-host/src/backend/lowering/lowering.glorious"),
    )
    .unwrap();
    assert!(lowering.contains("CallableNotLowered(CoreValueId)"));
    assert!(lowering.contains("CoreComputationView::CallIndirect"));
}

#[test]
fn self_host_label_elaboration_retains_generative_lexical_control_in_core() {
    // This is intentionally a Typed-Core gate rather than an emitted-bytecode
    // claim: labels must remain direct control until the later MIR protected
    // control lowering exists.  It guards the two semantic invariants taken
    // from labels_leave.rs: nested same-name destinations shadow lexically,
    // and a call carries the destination identity rather than just its value.
    let root = repository_root();
    let core = fs::read_to_string(
        root.join("self-host/src/frontend/elaboration/elaboration.glorious"),
    )
    .unwrap();
    for required in [
        "LabelDestination(LabelDestinationId, CoreComputationId)",
        "Leave(LabelDestinationId, CoreValueId)",
        "active_label_destination_at(",
        "let current = index - 1;",
        "push_label_destination(&mut value.core, result_type)",
        "push_active_label(value, name, destination)",
        "CoreComputationKind::Leave(destination, payload)",
        "CoreComputationKind::LabelDestination(destination, child)",
        "type_id_from_u32(1)",
    ] {
        assert!(core.contains(required), "missing label Typed Core behavior: {required}");
    }
    let label_call = core
        .split("elaborate_label_call(")
        .nth(1)
        .expect("label call elaborator exists");
    assert!(
        label_call.contains("active_label_destination(value, name)"),
        "label calls must resolve only against the active lexical stack"
    );
    assert!(
        !label_call.contains("expected\n        )\n    } else"),
        "a label payload must not be checked against its surrounding result type"
    );
}

#[test]
fn self_host_label_lowering_preserves_protected_cfg_and_artifact_namespace() {
    // This is deliberately structural until the bootstrap VM gate is run: a
    // label is not an ordinary jump.  Its normal edge must pop then enter the
    // protected join, while Leave remains terminal and the GRBC metadata must
    // bound every emitted slot.
    let root = repository_root();
    let lowering = fs::read_to_string(
        root.join("self-host/src/backend/lowering/lowering.glorious"),
    )
    .unwrap();
    for required in [
        "active_labels: Vec<LabelDestinationId>",
        "leaving_labels: Vec<LabelDestinationId>",
        "emit_label_push",
        "emit_label_pop",
        "emit_leave",
        "CoreComputationView::LabelDestination(_, destination, child)",
        "CoreComputationView::Leave(_, destination, payload)",
        "emit_move(value, result, found)",
        "emit_label_pop(value, slot)",
        "emit_jump(value, join)",
        "bind_block(value, join)",
        "MirInstruction::Leave(slot, payload)",
        "mir_function_label_slot_count",
    ] {
        assert!(lowering.contains(required), "missing protected label lowering: {required}");
    }
    let emission = fs::read_to_string(
        root.join("self-host/src/backend/emission/emission.glorious"),
    )
    .unwrap();
    assert!(
        emission.contains("super::lowering::mir_function_label_slot_count(function)"),
        "function records must carry the MIR-derived label namespace bound"
    );
}

#[test]
fn self_host_is_refinement_core_retains_decision_shape_and_scoped_bindings() {
    // This is a structural Typed-Core gate.  `is` has no MIR lowering yet,
    // but it must already remain a decision with its pattern and success-edge
    // binding projection plan; lowering it to a subject-only Boolean here
    // would make the later refinement CFG impossible to recover faithfully.
    let root = repository_root();
    let core = fs::read_to_string(
        root.join("self-host/src/frontend/elaboration/elaboration.glorious"),
    )
    .unwrap();
    for required in [
        "CorePatternId",
        "CorePatternKind",
        "Float(Bytes)",
        "Text(Bytes)",
        "Character(u32)",
        "Byte(u8)",
        "Variant(TypeId, u32, CorePatternRange, Bool)",
        "Tuple(CorePatternRange, Bool)",
        "Struct(TypeId, CorePatternFieldRange, Bool)",
        "CorePatternPathSegment { Variant(u32), Field(u32) }",
        "CoreRefinementBinding",
        "path: CorePatternPathRange",
        "Refinement(CoreValueId, CorePatternId, CoreRefinementBindingRange)",
        "CoreComputationView::Refinement",
        "typed_body_refinement_bindings",
        "core_refinement_binding_path",
        "push_core_pattern",
        "push_refinement_binding",
    ] {
        assert!(core.contains(required), "missing is-refinement Core foundation: {required}");
    }
    assert!(
        !core.contains("Refinement(CoreValueId, Bool)"),
        "an is refinement must not erase its pattern into a fabricated Boolean"
    );
}

#[test]
fn self_host_is_elaboration_builds_structural_patterns_before_bool_conversion() {
    // This deliberately remains a source/Core contract: the branch CFG is a
    // separate MIR feature.  It prevents the elaborator from regressing to
    // the old subject-only path while that lowering is still pending.
    let root = repository_root();
    let core = fs::read_to_string(
        root.join("self-host/src/frontend/elaboration/elaboration.glorious"),
    )
    .unwrap();
    for required in [
        "elaborate_is(",
        "BodyExpressionView::Is(subject, pattern) => elaborate_is(",
        "elaborate_refinement_pattern(",
        "find_refinement_variant(",
        "CorePatternKind::Variant(",
        "CorePatternKind::Tuple(",
        "CorePatternPathSegment::Variant(",
        "CorePatternPathSegment::Field(",
        "push_refinement_binding(&mut value.core, local, ty, range)",
        "CoreComputationKind::Refinement(subject_value, core_pattern",
        "wrap_raw_bool(",
    ] {
        assert!(core.contains(required), "missing is elaboration layer: {required}");
    }
    let elaboration = core
        .split("elaborate_is(")
        .nth(1)
        .expect("is elaborator exists");
    assert!(
        elaboration.contains("let start = super::syntax::range_mark(&value.core.refinement_bindings)"),
        "success-edge bindings must be ranged before the recursive pattern walk"
    );
}

#[test]
fn self_hosted_monomorphic_perform_elaborates_like_bootstrap() {
    // Keep the first executable effect-body parity case intentionally narrow:
    // a monomorphic operation has no continuation lowering requirement, but
    // it must reach Typed Core as `Perform` with its checked payload/result.
    let source = "effect Ask { [1,1] ask(value: i64) -> i64 } \
        answer(value: i64) -> i64 / {Ask} { perform Ask::ask(value) }";
    let bootstrap = SourceBundle::distributed(
        Segment::new(INPUT_NAME, format!("{source}{WRAPPER}")),
        [],
    );
    assert!(
        grandiose::compile_bundle_to_phases_with_options(
            &bootstrap,
            CompileOptions { optimization_level: OptimizationLevel::O0 },
        )
        .is_ok(),
        "bootstrap compiler must accept the focused perform fixture"
    );

    let phases = grandiose::compile_bundle_to_phases_with_options(
        &self_host_bundle(),
        CompileOptions { optimization_level: OptimizationLevel::O0 },
    )
    .unwrap();
    let entry = phases.artifact.entry_function.unwrap();
    let verified = verify(phases.artifact).unwrap();
    let directory = tempfile::tempdir().unwrap();
    let input = directory.path().join("perform.glorious");
    let output = directory.path().join("perform.bin");
    fs::write(&input, source).unwrap();
    let vm = Vm::with_host(
        verified,
        ["process.args", "fs.read", "fs.write", "diagnostic"],
        SystemHost::new(vec![output.clone().into_os_string(), input.into_os_string()]),
    )
    .unwrap();
    assert_eq!(vm.run(entry, vec![]).unwrap(), Value::Unit);
    assert_eq!(fs::read(output).unwrap().first().copied(), Some(0));
}

#[test]
fn self_hosted_nested_perform_payload_elaborates_in_release_vm() {
    // A payload can itself suspend. The outer operation must therefore retain
    // the inner `Perform` as an embedded Core operand rather than requiring a
    // pre-existing value local.
    let source = "effect Ask { [1,1] ask(value: i64) -> i64 } \
        nested() -> i64 / {Ask} { perform Ask::ask(perform Ask::ask(40)) }";
    let bootstrap = SourceBundle::distributed(
        Segment::new(INPUT_NAME, format!("{source}{WRAPPER}")),
        [],
    );
    assert!(
        grandiose::compile_bundle_to_phases_with_options(
            &bootstrap,
            CompileOptions { optimization_level: OptimizationLevel::O2 },
        )
        .is_ok(),
        "bootstrap compiler must accept nested perform payloads"
    );

    let phases = grandiose::compile_bundle_to_phases_with_options(
        &self_host_bundle(),
        CompileOptions { optimization_level: OptimizationLevel::O2 },
    )
    .unwrap();
    let entry = phases.artifact.entry_function.unwrap();
    let verified = verify(phases.artifact).unwrap();
    let directory = tempfile::tempdir().unwrap();
    let input = directory.path().join("nested-perform.glorious");
    let output = directory.path().join("nested-perform.bin");
    fs::write(&input, source).unwrap();
    let vm = Vm::with_host(
        verified,
        ["process.args", "fs.read", "fs.write", "diagnostic"],
        SystemHost::new(vec![output.clone().into_os_string(), input.into_os_string()]),
    )
    .unwrap();
    assert_eq!(vm.run(entry, vec![]).unwrap(), Value::Unit);
    let encoded = fs::read(output).unwrap();
    assert_eq!(&encoded[..4], &1_u32.to_le_bytes());
    assert_eq!(encoded.get(4).copied(), Some(0));
}

#[test]
fn self_hosted_generic_struct_literals_infer_field_arguments_in_vm() {
    // The local initializer has no expected type.  Its `Box` application must
    // therefore be inferred from the field value itself, then agree with the
    // declared result type at the tail of the function.
    let source = "struct Box<T> { value: T } \
        make() -> Box<i64> { let boxed = Box { value: 1 }; boxed }";
    let bootstrap = SourceBundle::distributed(
        Segment::new(INPUT_NAME, format!("{source}{WRAPPER}")),
        [],
    );
    assert!(
        grandiose::compile_bundle_to_phases_with_options(
            &bootstrap,
            CompileOptions { optimization_level: OptimizationLevel::O2 },
        )
        .is_ok(),
        "bootstrap compiler must accept field-inferred generic products"
    );

    let phases = grandiose::compile_bundle_to_phases_with_options(
        &self_host_bundle(),
        CompileOptions { optimization_level: OptimizationLevel::O2 },
    )
    .unwrap();
    let entry = phases.artifact.entry_function.unwrap();
    let verified = verify(phases.artifact).unwrap();
    let directory = tempfile::tempdir().unwrap();
    let input = directory.path().join("generic-product.glorious");
    let output = directory.path().join("generic-product.bin");
    fs::write(&input, source).unwrap();
    let vm = Vm::with_host(
        verified,
        ["process.args", "fs.read", "fs.write", "diagnostic"],
        SystemHost::new(vec![output.clone().into_os_string(), input.into_os_string()]),
    )
    .unwrap();
    assert_eq!(vm.run(entry, vec![]).unwrap(), Value::Unit);
    let encoded = fs::read(output).unwrap();
    // The probe starts with a little-endian input count. The status for its
    // first input follows that four-byte framing word.
    assert_eq!(&encoded[..4], &1_u32.to_le_bytes());
    assert_eq!(encoded.get(4).copied(), Some(0));
}

#[test]
fn self_hosted_full_width_integer_literals_match_bootstrap_in_release_vm() {
    // Preserve all four Core integer words for the maximum `u128` value.
    // This is the widest contextual literal accepted by the current focused
    // self-host Typed Core corpus.
    let source = "u128_max() -> u128 { 340282366920938463463374607431768211455 }";
    let bootstrap = SourceBundle::distributed(
        Segment::new(INPUT_NAME, format!("{source}{WRAPPER}")),
        [],
    );
    assert!(
        grandiose::compile_bundle_to_phases_with_options(
            &bootstrap,
            CompileOptions { optimization_level: OptimizationLevel::O2 },
        )
        .is_ok(),
        "bootstrap compiler must accept the full-width literal corpus"
    );

    let phases = grandiose::compile_bundle_to_phases_with_options(
        &self_host_bundle(),
        CompileOptions { optimization_level: OptimizationLevel::O2 },
    )
    .unwrap();
    let entry = phases.artifact.entry_function.unwrap();
    let verified = verify(phases.artifact).unwrap();
    let directory = tempfile::tempdir().unwrap();
    let input = directory.path().join("full-width-integers.glorious");
    let output = directory.path().join("full-width-integers.bin");
    fs::write(&input, source).unwrap();
    let vm = Vm::with_host(
        verified,
        ["process.args", "fs.read", "fs.write", "diagnostic"],
        SystemHost::new(vec![output.clone().into_os_string(), input.into_os_string()]),
    )
    .unwrap();
    assert_eq!(vm.run(entry, vec![]).unwrap(), Value::Unit);
    let encoded = fs::read(output).unwrap();
    assert_eq!(&encoded[..4], &1_u32.to_le_bytes());
    assert_eq!(encoded.get(4).copied(), Some(0));
}

#[test]
fn self_hosted_typed_core_matches_rust_in_vm_and_native_execution() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            if std::env::var_os("G1_SELF_HOST_TYPED_CORE_CHECK_ONLY").is_some() {
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
            let mut corpus = corpus(directory.path());
            corpus.extend(stage_a_corpus(directory.path()));
            let mut expected = Vec::new();
            push_u32(&mut expected, corpus.len().try_into().unwrap());
            for path in &corpus {
                encode_rust_core(&mut expected, &fs::read_to_string(path).unwrap());
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
                let output_path = directory.path().join(format!("vm-{index}.bin"));
                let vm = Vm::with_host(
                    verified.clone(),
                    ["process.args", "fs.read", "fs.write", "diagnostic"],
                    SystemHost::new(vec![
                        output_path.clone().into_os_string(),
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
                encode_rust_core(&mut expected_one, &fs::read_to_string(path).unwrap());
                assert_eq!(
                    fs::read(&output_path).unwrap(),
                    expected_one,
                    "VM typed Core diverged for input {index} ({})",
                    path.display()
                );
            }

            let vm_all_path = directory.path().join("vm-all.bin");
            let vm_args = std::iter::once(vm_all_path.clone().into_os_string())
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
                fs::read(&vm_all_path).unwrap(),
                expected,
                "VM whole-corpus typed Core diverged"
            );

            let module = grandiose::emit_llvm_ir(&phases, &LlvmOptions::default()).unwrap();
            let llvm = directory.path().join("self-host-typed-core.ll");
            let executable = directory.path().join("self-host-typed-core");
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
                "native whole-corpus typed Core diverged"
            );

            for (index, path) in corpus.iter().enumerate() {
                let output_path = directory.path().join(format!("native-{index}.bin"));
                let native = Command::new(&executable)
                    .arg(&output_path)
                    .arg(path)
                    .output()
                    .unwrap();
                assert!(
                    native.status.success(),
                    "native input {index} ({}) status: {:?}\n{}",
                    path.display(),
                    native.status,
                    String::from_utf8_lossy(&native.stderr)
                );
                let mut expected_one = Vec::new();
                push_u32(&mut expected_one, 1);
                encode_rust_core(&mut expected_one, &fs::read_to_string(path).unwrap());
                assert_eq!(
                    fs::read(&output_path).unwrap(),
                    expected_one,
                    "native typed Core diverged for input {index} ({})",
                    path.display()
                );
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
