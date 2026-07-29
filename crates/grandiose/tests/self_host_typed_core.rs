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
use grandiose_vm::{Constant, I64, SystemHost, Type, TypeId, U64, UNIT, Value, Vm, verify};

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

fn self_host_bundle() -> SourceBundle {
    let root = repository_root().join("self-host/src");
    let primary = Segment::new(
        root.join("main.glorious").to_string_lossy(),
        "mod frontend;\n\nmain() { run_compiler_host(frontend::elaboration::application) }\n",
    );
    let paths = [
        root.join("frontend/frontend.glorious"),
        root.join("frontend/lexer/lexer.glorious"),
        root.join("frontend/scanner/scanner.glorious"),
        root.join("frontend/headers/headers.glorious"),
        root.join("frontend/bodies/bodies.glorious"),
        root.join("frontend/resolution/resolution.glorious"),
        root.join("frontend/elaboration/elaboration.glorious"),
    ];
    SourceBundle::distributed(
        primary,
        paths.into_iter().map(|path| {
            let source = fs::read_to_string(&path).unwrap();
            Segment::new(path.to_string_lossy(), source)
        }),
    )
}

fn push_u32(output: &mut Vec<u8>, value: u32) {
    output.extend(value.to_le_bytes());
}

fn push_u64(output: &mut Vec<u8>, value: u64) {
    output.extend(value.to_le_bytes());
}

fn push_string(output: &mut Vec<u8>, value: &str) {
    push_u32(output, value.len().try_into().unwrap());
    output.extend(value.as_bytes());
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
    Unit,
    U64,
    I64,
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
        match ty {
            UNIT => return Ok(NormalizedType::Unit),
            U64 => return Ok(NormalizedType::U64),
            I64 => return Ok(NormalizedType::I64),
            _ => {}
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
        if matches!(ty, UNIT | U64 | I64) {
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
            | ExprKind::TailCallSelf { args } => {
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
        if matches!(ty, UNIT | U64 | I64) {
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
                output.push(1);
                self.write_type(output, expression.ty)?;
                match value {
                    Constant::U64(value) if expression.ty == U64 => push_u64(output, *value),
                    Constant::I64(value) if expression.ty == I64 => {
                        output.extend(value.to_le_bytes())
                    }
                    _ => {
                        return Err(format!(
                            "unsupported constant in focused typed-Core corpus: {value:?}:t{}",
                            expression.ty
                        ));
                    }
                }
            }
            ExprKind::Local { local, copy } => {
                output.push(2);
                self.write_type(output, expression.ty)?;
                push_u32(output, self.local(*local)?);
                output.push(u8::from(*copy));
            }
            ExprKind::Call { declaration, args } => {
                output.push(3);
                self.write_type(output, expression.ty)?;
                encode_identity(output, self.target(*declaration)?);
                push_u32(output, args.len().try_into().unwrap());
                for argument in args {
                    self.expression(output, argument)?;
                }
            }
            ExprKind::TailCall { declaration, args } => {
                output.push(4);
                self.write_type(output, expression.ty)?;
                encode_identity(output, self.target(*declaration)?);
                push_u32(output, args.len().try_into().unwrap());
                for argument in args {
                    self.expression(output, argument)?;
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
            ExprKind::Block { statements, tail } => {
                output.push(5);
                self.write_type(output, expression.ty)?;
                push_u32(output, statements.len().try_into().unwrap());
                for statement in statements {
                    self.statement(output, statement)?;
                }
                self.expression(output, tail)?;
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
        "probe_i64() -> i64 { 7 } probe_u64() -> u64 { 7 }",
        "probe_param(value: i64) -> i64 { value }",
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
