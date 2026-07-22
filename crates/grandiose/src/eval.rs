use std::{
    cell::{OnceCell, RefCell},
    collections::{HashMap, HashSet},
    env, fmt,
    hash::{BuildHasherDefault, Hasher},
    io::{self, Write},
    ops::Range,
    path::PathBuf,
    rc::Rc,
    time::{Duration, Instant},
};

const DEFAULT_MAX_EVALUATION_FRAMES: usize = 1_000_000;
const MEMORY_TRIM_INTERVAL: Duration = Duration::from_secs(5);
const TEXT_TAIL_CHUNK_BYTES: usize = 64 * 1024;
const TEXT_EAGER_FLATTEN_BYTES: usize = 4096;

#[cfg(all(target_os = "linux", target_env = "gnu"))]
unsafe extern "C" {
    fn malloc_trim(pad: usize) -> std::ffi::c_int;
}

fn trim_process_memory() {
    #[cfg(all(target_os = "linux", target_env = "gnu"))]
    // SAFETY: malloc_trim has no pointer arguments and is safe to call between
    // evaluator steps; glibc synchronizes it with the process allocator.
    unsafe {
        malloc_trim(0);
    }
}

#[derive(Default)]
struct SpanHasher(u64);

impl Hasher for SpanHasher {
    fn finish(&self) -> u64 {
        self.0
    }

    fn write(&mut self, bytes: &[u8]) {
        let mut value = 0xcbf29ce484222325_u64;
        for byte in bytes {
            value = (value ^ u64::from(*byte)).wrapping_mul(0x100000001b3);
        }
        self.0 = value;
    }

    fn write_u64(&mut self, value: u64) {
        self.0 = value;
    }

    fn write_u128(&mut self, value: u128) {
        self.0 = (value as u64) ^ ((value >> 64) as u64).rotate_left(23);
    }
}

type SpanMap<V> = HashMap<u128, V, BuildHasherDefault<SpanHasher>>;
type SpanSet = HashSet<u128, BuildHasherDefault<SpanHasher>>;

use grandiose_vm::{
    Host as G1Host, HostLimits as G1HostLimits, Primitive, SystemHost as G1SystemHost,
};
use im::Vector;

use crate::{
    HostImportRole,
    ast::{
        AssignmentField, AssignmentPlaceKind, BinaryOp, DropDecl, Expr, ExprKind, Function,
        GoalPolarity, HandlerClause, Pattern, PatternKind, Program, Stmt, TraitMethod, TypeSyntax,
        TypeSyntaxKind, UnaryOp, pattern_field_index,
    },
    diagnostic::Diagnostic,
    span::Span,
};

fn span_key(span: Span) -> u128 {
    ((span.start as u128) << 64) | span.end as u128
}

#[derive(Clone, Debug, Default)]
pub struct Locals(Rc<LocalBinding>);

#[derive(Debug, Default)]
enum LocalBinding {
    #[default]
    Empty,
    Bound {
        name: Rc<str>,
        value: Rc<RefCell<Value>>,
        parent: Locals,
    },
}

impl Locals {
    fn new() -> Self {
        Self::default()
    }

    fn find(&self, requested: &str) -> Option<(usize, &Rc<RefCell<Value>>)> {
        let mut current = self;
        let mut depth = 0;
        loop {
            match current.0.as_ref() {
                LocalBinding::Empty => return None,
                LocalBinding::Bound {
                    name,
                    value,
                    parent,
                } => {
                    if name.as_ref() == requested {
                        return Some((depth, value));
                    }
                    current = parent;
                    depth += 1;
                }
            }
        }
    }

    fn get_at(&self, requested: &str, depth: usize) -> Option<&Rc<RefCell<Value>>> {
        let mut current = self;
        for _ in 0..depth {
            match current.0.as_ref() {
                LocalBinding::Bound { parent, .. } => current = parent,
                LocalBinding::Empty => return None,
            }
        }
        match current.0.as_ref() {
            LocalBinding::Bound { name, value, .. } if name.as_ref() == requested => Some(value),
            _ => None,
        }
    }

    fn insert(&mut self, name: impl Into<Rc<str>>, value: Value) {
        *self = Self(Rc::new(LocalBinding::Bound {
            name: name.into(),
            value: Rc::new(RefCell::new(value)),
            parent: self.clone(),
        }));
    }

    fn select(&self, names: &[Rc<str>]) -> Self {
        let mut selected = Self::new();
        for name in names {
            if let Some((_, value)) = self.find(name) {
                selected.insert(name.clone(), value.borrow().clone());
            }
        }
        selected
    }

    fn into_values(self) -> Vec<Value> {
        let mut values = Vec::new();
        let mut current = self;
        loop {
            match Rc::try_unwrap(current.0) {
                Ok(LocalBinding::Empty) => return values,
                Ok(LocalBinding::Bound { value, parent, .. }) => {
                    values.push(match Rc::try_unwrap(value) {
                        Ok(value) => value.into_inner(),
                        Err(value) => value.borrow().clone(),
                    });
                    current = parent;
                }
                Err(shared) => match shared.as_ref() {
                    LocalBinding::Empty => return values,
                    LocalBinding::Bound { value, parent, .. } => {
                        values.push(value.borrow().clone());
                        current = parent.clone();
                    }
                },
            }
        }
    }
}

impl Extend<(String, Value)> for Locals {
    fn extend<T: IntoIterator<Item = (String, Value)>>(&mut self, bindings: T) {
        for (name, value) in bindings {
            self.insert(name, value);
        }
    }
}

impl Extend<(Rc<str>, Value)> for Locals {
    fn extend<T: IntoIterator<Item = (Rc<str>, Value)>>(&mut self, bindings: T) {
        for (name, value) in bindings {
            self.insert(name, value);
        }
    }
}

impl FromIterator<(String, Value)> for Locals {
    fn from_iter<T: IntoIterator<Item = (String, Value)>>(bindings: T) -> Self {
        let mut locals = Self::new();
        locals.extend(bindings);
        locals
    }
}

enum TextRepr {
    Flat(String),
    Concat(Rc<Text>, Rc<Text>),
}

pub struct Text {
    repr: TextRepr,
    byte_len: usize,
    flattened: OnceCell<Rc<str>>,
}

struct TextChunks<'a> {
    pending: Vec<&'a Text>,
}

impl<'a> Iterator for TextChunks<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(text) = self.pending.pop() {
            match &text.repr {
                TextRepr::Flat(value) => return Some(value),
                TextRepr::Concat(left, right) => {
                    self.pending.push(right);
                    self.pending.push(left);
                }
            }
        }
        None
    }
}

impl Text {
    fn new(repr: TextRepr, byte_len: usize) -> Self {
        Self {
            repr,
            byte_len,
            flattened: OnceCell::new(),
        }
    }

    fn flat(value: String) -> Self {
        let byte_len = value.len();
        Self::new(TextRepr::Flat(value), byte_len)
    }

    fn concat(left: Rc<Self>, right: Rc<Self>) -> Self {
        let byte_len = left.byte_len + right.byte_len;
        Self::new(TextRepr::Concat(left, right), byte_len)
    }

    fn concatenate(left: Rc<Self>, right: Rc<Self>) -> Rc<Self> {
        if left.byte_len == 0 {
            return right;
        }
        if right.byte_len == 0 {
            return left;
        }

        let right_len = right.byte_len;
        match Rc::try_unwrap(left) {
            Ok(Self {
                repr: TextRepr::Flat(mut value),
                byte_len,
                ..
            }) => {
                for chunk in right.chunks() {
                    value.push_str(chunk);
                }
                Rc::new(Self::new(TextRepr::Flat(value), byte_len + right_len))
            }
            Ok(Self {
                repr: TextRepr::Concat(prefix, tail),
                byte_len,
                ..
            }) => match Rc::try_unwrap(tail) {
                Ok(Self {
                    repr: TextRepr::Flat(mut value),
                    byte_len: tail_len,
                    ..
                }) if tail_len + right_len <= TEXT_TAIL_CHUNK_BYTES => {
                    for chunk in right.chunks() {
                        value.push_str(chunk);
                    }
                    Rc::new(Self::new(
                        TextRepr::Concat(
                            prefix,
                            Rc::new(Self::new(TextRepr::Flat(value), tail_len + right_len)),
                        ),
                        byte_len + right_len,
                    ))
                }
                Ok(tail) => {
                    let left =
                        Rc::new(Self::new(TextRepr::Concat(prefix, Rc::new(tail)), byte_len));
                    Rc::new(Self::concat(left, right))
                }
                Err(tail) => {
                    let left = Rc::new(Self::new(TextRepr::Concat(prefix, tail), byte_len));
                    Rc::new(Self::concat(left, right))
                }
            },
            Err(left) => {
                // Eager-flatten small shared concatenations: copying both sides
                // into a fresh Flat (bounded by the threshold) keeps the millions
                // of short instruction-line strings Flat, so later str_* ops never
                // pay a flatten. Above the threshold we fall back to an O(1) Concat
                // rope, so this can never reintroduce O(n^2) on large accumulators.
                let total = left.byte_len + right_len;
                if total <= TEXT_EAGER_FLATTEN_BYTES {
                    let mut value = String::with_capacity(total);
                    for chunk in left.chunks() {
                        value.push_str(chunk);
                    }
                    for chunk in right.chunks() {
                        value.push_str(chunk);
                    }
                    Rc::new(Self::new(TextRepr::Flat(value), total))
                } else {
                    Rc::new(Self::concat(left, right))
                }
            }
        }
    }

    fn chunks(&self) -> TextChunks<'_> {
        TextChunks {
            pending: vec![self],
        }
    }

    fn flatten_shared(&self) -> Rc<str> {
        self.flattened
            .get_or_init(|| {
                let mut value = String::with_capacity(self.byte_len);
                for chunk in self.chunks() {
                    value.push_str(chunk);
                }
                Rc::from(value)
            })
            .clone()
    }

    fn flatten(&self) -> String {
        self.flatten_shared().to_string()
    }

    /// Hash the logical byte sequence without allocating a flattened String.
    /// Feeds raw chunk bytes so any rope structure of the same text hashes
    /// identically (used only for the declaration-lookup memoization key).
    fn content_hash(&self) -> u64 {
        use std::hash::Hasher;
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        for chunk in self.chunks() {
            hasher.write(chunk.as_bytes());
        }
        hasher.write_u8(0xff);
        hasher.finish()
    }

    fn byte_len(&self) -> usize {
        self.byte_len
    }

    fn character_len(&self) -> usize {
        self.chunks().map(|chunk| chunk.chars().count()).sum()
    }

    fn byte_at(&self, mut index: usize) -> Option<u8> {
        for chunk in self.chunks() {
            if index < chunk.len() {
                return Some(chunk.as_bytes()[index]);
            }
            index -= chunk.len();
        }
        None
    }

    fn equals_str(&self, other: &str) -> bool {
        self.byte_len == other.len() && self.chunks().flat_map(str::bytes).eq(other.bytes())
    }
}

impl PartialEq for Text {
    fn eq(&self, other: &Self) -> bool {
        self.byte_len == other.byte_len
            && self
                .chunks()
                .flat_map(str::bytes)
                .eq(other.chunks().flat_map(str::bytes))
    }
}

impl Eq for Text {}

impl fmt::Display for Text {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for chunk in self.chunks() {
            f.write_str(chunk)?;
        }
        Ok(())
    }
}

impl fmt::Debug for Text {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.flatten(), f)
    }
}

#[derive(Clone)]
pub struct TextRef(Rc<Text>);

impl From<String> for TextRef {
    fn from(value: String) -> Self {
        Self(Rc::new(Text::flat(value)))
    }
}

impl From<&str> for TextRef {
    fn from(value: &str) -> Self {
        value.to_owned().into()
    }
}

impl PartialEq for TextRef {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Eq for TextRef {}

impl fmt::Display for TextRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&*self.0, f)
    }
}

impl fmt::Debug for TextRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&*self.0, f)
    }
}

#[derive(Clone, Debug)]
pub enum Value {
    /// Internal marker for storage that has been moved out and has not yet
    /// been reinitialized. Well-typed source can only observe this through a
    /// recovery diagnostic, never as a source value.
    Uninitialized,
    Unit,
    Int(i64),
    /// A source magnitude awaiting contextual integer width selection.
    IntegerLiteral {
        negative: bool,
        magnitude: u128,
    },
    /// An integer whose source type cannot be represented faithfully by the
    /// recovery evaluator's compatibility, implicitly-i64 `Int` case. `raw` is the
    /// width-truncated two's-complement bit pattern.
    Integer {
        signed: bool,
        bits: u8,
        raw: u128,
    },
    /// A contextually f64 (or not-yet-contextualized) floating-point value.
    Float(f64),
    /// A contextually f32 floating-point value. Keeping the source width in
    /// recovery execution is required for exact primitive and bit semantics.
    Float32(f32),
    Char(char),
    String(TextRef),
    /// Immutable octets returned by the generation-1 filesystem host surface.
    Bytes(Rc<[u8]>),
    List(Vector<Value>),
    Array(ArrayRef),
    Struct {
        name: Rc<str>,
        fields: Rc<HashMap<String, Value>>,
    },
    Enum {
        name: Rc<str>,
        variant: Rc<str>,
        fields: Rc<Vec<Value>>,
    },
    Closure {
        params: Rc<[Rc<str>]>,
        body: Rc<Expr>,
        captures: Locals,
    },
    /// A capture-free ordinary source function used through an `Fn` value.
    /// Calls retain the original declaration identity and call-site authority.
    FunctionItem(usize),
    Reference {
        value: Rc<RefCell<Value>>,
        unique: bool,
    },
    /// A reference-root field projection. Keeping the root and path avoids
    /// turning `&mut wrapper.field` into a reference to a detached clone.
    ProjectedReference {
        root: Rc<RefCell<Value>>,
        fields: Rc<Vec<String>>,
        unique: bool,
    },
    Resumption(ResumptionValue),
}

/// Recovery-interpreter representation of the opaque G1 `Array<T>` machine
/// value.  The element type remains a static/compiler concern; the interpreter
/// retains only the slot state and the bytecode-specified logical capacity.
#[derive(Clone)]
pub struct ArrayRef(Rc<RefCell<InterpreterArray>>);

#[derive(Default)]
struct InterpreterArray {
    slots: Vec<Option<Rc<RefCell<Value>>>>,
    logical_capacity: usize,
}

impl fmt::Debug for ArrayRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let array = self.0.borrow();
        f.debug_struct("Array")
            .field("len", &array.slots.len())
            .field("capacity", &array.logical_capacity)
            .field(
                "initialized",
                &array.slots.iter().filter(|slot| slot.is_some()).count(),
            )
            .finish()
    }
}

impl PartialEq for ArrayRef {
    fn eq(&self, other: &Self) -> bool {
        if Rc::ptr_eq(&self.0, &other.0) {
            return true;
        }
        let left = self.0.borrow();
        let right = other.0.borrow();
        left.logical_capacity == right.logical_capacity
            && left.slots.len() == right.slots.len()
            && left
                .slots
                .iter()
                .zip(&right.slots)
                .all(|(left, right)| match (left, right) {
                    (None, None) => true,
                    (Some(left), Some(right)) => *left.borrow() == *right.borrow(),
                    _ => false,
                })
    }
}

#[derive(Clone)]
pub struct ResumptionValue {
    state: Rc<RefCell<ResumptionState>>,
}

impl fmt::Debug for ResumptionValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let state = if self.state.borrow().closed {
            "consumed"
        } else {
            "ready"
        };
        f.debug_tuple("Resumption").field(&state).finish()
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Uninitialized, Self::Uninitialized) => true,
            (Self::Unit, Self::Unit) => true,
            (Self::Int(a), Self::Int(b)) => a == b,
            (
                Self::IntegerLiteral {
                    negative,
                    magnitude,
                },
                Self::Int(value),
            )
            | (
                Self::Int(value),
                Self::IntegerLiteral {
                    negative,
                    magnitude,
                },
            ) => {
                if *negative {
                    i128::try_from(*magnitude).ok().and_then(i128::checked_neg)
                        == Some(i128::from(*value))
                } else {
                    u128::try_from(*value).is_ok_and(|value| value == *magnitude)
                }
            }
            (Self::Int(value), Self::Integer { signed, bits, raw })
            | (Self::Integer { signed, bits, raw }, Self::Int(value)) => {
                if *signed {
                    signed_integer(*raw, *bits) == i128::from(*value)
                } else {
                    u128::try_from(*value).is_ok_and(|value| value == *raw)
                }
            }
            (
                Self::Integer {
                    signed: asigned,
                    bits: abits,
                    raw: araw,
                },
                Self::Integer {
                    signed: bsigned,
                    bits: bbits,
                    raw: braw,
                },
            ) => asigned == bsigned && abits == bbits && araw == braw,
            // IEEE comparison, matching the bytecode FloatEq primitive.
            (Self::Float(a), Self::Float(b)) => a == b,
            (Self::Float32(a), Self::Float32(b)) => a == b,
            (Self::Char(a), Self::Char(b)) => a == b,
            (Self::String(a), Self::String(b)) => a == b,
            (Self::Bytes(a), Self::Bytes(b)) => a == b,
            (Self::List(a), Self::List(b)) => a == b,
            (Self::Array(a), Self::Array(b)) => a == b,
            (
                Self::Struct {
                    name: an,
                    fields: af,
                },
                Self::Struct {
                    name: bn,
                    fields: bf,
                },
            ) => an == bn && af == bf,
            (
                Self::Enum {
                    name: an,
                    variant: av,
                    fields: af,
                },
                Self::Enum {
                    name: bn,
                    variant: bv,
                    fields: bf,
                },
            ) => an == bn && av == bv && af == bf,
            (Self::Resumption(a), Self::Resumption(b)) => Rc::ptr_eq(&a.state, &b.state),
            (Self::FunctionItem(a), Self::FunctionItem(b)) => a == b,
            (Self::Reference { value: a, .. }, Self::Reference { value: b, .. }) => {
                *a.borrow() == *b.borrow()
            }
            (
                Self::ProjectedReference {
                    root: ar,
                    fields: af,
                    ..
                },
                Self::ProjectedReference {
                    root: br,
                    fields: bf,
                    ..
                },
            ) => af == bf && *ar.borrow() == *br.borrow(),
            _ => false,
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Uninitialized => write!(f, "<uninitialized>"),
            Self::Unit => write!(f, "()"),
            Self::Int(value) => write!(f, "{value}"),
            Self::IntegerLiteral {
                negative,
                magnitude,
            } => {
                if *negative {
                    write!(f, "-{magnitude}")
                } else {
                    write!(f, "{magnitude}")
                }
            }
            Self::Integer { signed, bits, raw } => {
                if *signed {
                    write!(f, "{}", signed_integer(*raw, *bits))
                } else {
                    write!(f, "{raw}")
                }
            }
            Self::Float(value) => write!(f, "{value}"),
            Self::Float32(value) => write!(f, "{value}"),
            Self::Char(value) => write!(f, "{value}"),
            Self::String(value) => write!(f, "{value}"),
            Self::Bytes(value) => write!(f, "<bytes len={}>", value.len()),
            Self::List(values) => {
                write!(f, "[")?;
                for (index, value) in values.iter().enumerate() {
                    if index > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{value}")?;
                }
                write!(f, "]")
            }
            Self::Array(array) => {
                let array = array.0.borrow();
                write!(
                    f,
                    "<array len={} capacity={}>",
                    array.slots.len(),
                    array.logical_capacity
                )
            }
            Self::Struct { name, .. } => write!(f, "{name} {{ ... }}"),
            Self::Enum { name, variant, .. } => write!(f, "{name}::{variant}"),
            Self::Closure { .. } => write!(f, "<closure>"),
            Self::FunctionItem(_) => write!(f, "<function>"),
            Self::Reference { unique, .. } => {
                if *unique {
                    write!(f, "<unique reference>")
                } else {
                    write!(f, "<shared reference>")
                }
            }
            Self::ProjectedReference { unique, .. } => {
                if *unique {
                    write!(f, "<unique projected reference>")
                } else {
                    write!(f, "<shared projected reference>")
                }
            }
            Self::Resumption(_) => write!(f, "<resumption>"),
        }
    }
}

fn projected_reference_value(root: &Rc<RefCell<Value>>, fields: &[String]) -> Option<Value> {
    let mut value = root.borrow().clone();
    for field in fields {
        value = match value {
            Value::Struct { fields, .. } => fields.get(field)?.clone(),
            Value::Enum { fields, .. } => fields.get(field.parse::<usize>().ok()?)?.clone(),
            Value::List(values) => values.get(field.parse::<usize>().ok()?)?.clone(),
            _ => return None,
        };
    }
    (!matches!(value, Value::Uninitialized)).then_some(value)
}

fn assignment_field_names(fields: &[AssignmentField]) -> Vec<String> {
    fields.iter().map(|field| field.name.clone()).collect()
}

fn replace_projected_value(
    value: &mut Value,
    fields: &[AssignmentField],
    replacement: Value,
    span: Span,
) -> Result<Value, Diagnostic> {
    let Some((field, tail)) = fields.split_first() else {
        return Ok(std::mem::replace(value, replacement));
    };
    match value {
        Value::Struct { fields, .. } => {
            let values = Rc::make_mut(fields);
            let selected = values.get_mut(&field.name).ok_or_else(|| {
                runtime(
                    field.span,
                    format!("value has no field named `{}`", field.name),
                )
            })?;
            replace_projected_value(selected, tail, replacement, span)
        }
        Value::List(values) => {
            let index = field.name.parse::<usize>().map_err(|_| {
                runtime(
                    field.span,
                    "tuple assignment requires a numeric field index",
                )
            })?;
            let mut selected = values
                .get(index)
                .cloned()
                .ok_or_else(|| runtime(field.span, format!("tuple has no field `{index}`")))?;
            let previous = replace_projected_value(&mut selected, tail, replacement, span)?;
            values.set(index, selected);
            Ok(previous)
        }
        Value::Enum { fields, .. } => {
            let index = field.name.parse::<usize>().map_err(|_| {
                runtime(
                    field.span,
                    "enum payload assignment requires a numeric field index",
                )
            })?;
            let values = Rc::make_mut(fields);
            let selected = values.get_mut(index).ok_or_else(|| {
                runtime(
                    field.span,
                    format!("active enum variant has no payload field `{index}`"),
                )
            })?;
            replace_projected_value(selected, tail, replacement, span)
        }
        Value::Uninitialized => Err(runtime(span, "assignment traverses uninitialized storage")),
        value => Err(runtime(
            field.span,
            format!("assignment field requires a struct or tuple, received `{value:?}`"),
        )),
    }
}

fn assign_cell_projection(
    root: &Rc<RefCell<Value>>,
    fields: &[AssignmentField],
    replacement: Value,
    span: Span,
) -> Result<Value, Diagnostic> {
    replace_projected_value(&mut root.borrow_mut(), fields, replacement, span)
}

fn local_projection(expression: &Expr) -> Option<(Rc<str>, Vec<AssignmentField>)> {
    fn collect(expression: &Expr, fields: &mut Vec<AssignmentField>) -> Option<Rc<str>> {
        match &expression.kind {
            ExprKind::Variable(path) if path.len() == 1 => Some(path[0].clone()),
            ExprKind::Field(subject, name) => {
                let root = collect(subject, fields)?;
                fields.push(AssignmentField {
                    name: name.clone(),
                    span: expression.span,
                });
                Some(root)
            }
            _ => None,
        }
    }
    let mut fields = Vec::new();
    let name = collect(expression, &mut fields)?;
    Some((name, fields))
}

fn dereference_projection(expression: &Expr) -> Option<(Expr, Vec<AssignmentField>)> {
    fn collect(expression: &Expr, fields: &mut Vec<AssignmentField>) -> Option<Expr> {
        match &expression.kind {
            ExprKind::Unary {
                op: UnaryOp::Dereference,
                operand,
            } => Some((**operand).clone()),
            ExprKind::Field(subject, name) => {
                let reference = collect(subject, fields)?;
                fields.push(AssignmentField {
                    name: name.clone(),
                    span: expression.span,
                });
                Some(reference)
            }
            _ => None,
        }
    }
    let mut fields = Vec::new();
    let reference = collect(expression, &mut fields)?;
    Some((reference, fields))
}

pub trait Host {
    fn perform(
        &mut self,
        effect: &str,
        operation: &str,
        args: Vec<Value>,
        span: Span,
    ) -> Result<Value, Diagnostic>;
}

pub struct SystemHost {
    pub working_directory: PathBuf,
    g1: G1SystemHost,
}

fn unwrap_expr(expression: Rc<Expr>) -> Expr {
    Rc::try_unwrap(expression).unwrap_or_else(|shared| (*shared).clone())
}

impl Default for SystemHost {
    fn default() -> Self {
        Self {
            working_directory: std::env::current_dir().unwrap_or_else(|_| PathBuf::from(".")),
            g1: G1SystemHost::new(Vec::new()),
        }
    }
}

impl SystemHost {
    /// Constructs a recovery host with the same per-call limits as the bytecode host.
    pub fn with_limits(limits: G1HostLimits) -> Self {
        Self {
            working_directory: std::env::current_dir().unwrap_or_else(|_| PathBuf::from(".")),
            g1: G1SystemHost::with_limits(Vec::new(), limits),
        }
    }

    /// Replaces the sink used by the exact G1 `diagnostic/write` host leaf.
    pub fn with_diagnostic_writer(mut self, writer: impl Write + Send + 'static) -> Self {
        self.g1 = self.g1.with_diagnostic_writer(writer);
        self
    }

    fn g1_path(&self, operation: &str, path: &str, span: Span) -> Result<String, Diagnostic> {
        // Preserve the G1 empty-path rejection before resolving relative paths against the
        // recovery evaluator's configurable working directory.
        if path.is_empty() {
            return Err(runtime(
                span,
                format!("{operation}: path must not be empty"),
            ));
        }
        self.working_directory
            .join(path)
            .into_os_string()
            .into_string()
            .map_err(|_| runtime(span, format!("{operation}: path is not valid UTF-8")))
    }

    fn g1_fault(span: Span, fault: grandiose_vm::HostFault) -> Diagnostic {
        runtime(span, fault.message)
    }
}

impl Host for SystemHost {
    fn perform(
        &mut self,
        effect: &str,
        operation: &str,
        args: Vec<Value>,
        span: Span,
    ) -> Result<Value, Diagnostic> {
        match (effect, operation, args.as_slice()) {
            ("fs.read", "read", [Value::String(path)]) => {
                let path = self.g1_path("fs.read", &path.0.flatten(), span)?;
                self.g1
                    .fs_read(path)
                    .map(|contents| Value::Bytes(contents.into()))
                    .map_err(|fault| Self::g1_fault(span, fault))
            }
            ("fs.write", "write", [Value::String(path), Value::Bytes(contents)]) => {
                let path = self.g1_path("fs.write", &path.0.flatten(), span)?;
                self.g1
                    .fs_write(path, contents.as_ref().to_vec())
                    .map(|_| Value::Unit)
                    .map_err(|fault| Self::g1_fault(span, fault))
            }
            ("diagnostic", "write", [Value::String(message)]) => self
                .g1
                .diagnostic_write(message.0.flatten())
                .map(|_| Value::Unit)
                .map_err(|fault| Self::g1_fault(span, fault)),
            ("Console", "write", [Value::String(text)]) => {
                print!("{text}");
                io::stdout().flush().ok();
                Ok(Value::Unit)
            }
            ("Console", "write_line", [Value::String(text)]) => {
                println!("{text}");
                Ok(Value::Unit)
            }
            ("Console", "error_line", [Value::String(text)]) => {
                eprintln!("{text}");
                Ok(Value::Unit)
            }
            ("Console", "read_line", []) => {
                let mut line = String::new();
                io::stdin().read_line(&mut line).map_err(|error| {
                    runtime(span, format!("Console::read_line failed: {error}"))
                })?;
                while line.ends_with(['\n', '\r']) {
                    line.pop();
                }
                Ok(Value::String(line.into()))
            }
            ("Files", "read_to_string", [Value::String(path)]) => {
                let path = self.working_directory.join(path.0.flatten());
                std::fs::read_to_string(&path)
                    .map(|contents| Value::String(contents.into()))
                    .map_err(|error| {
                        runtime(span, format!("could not read {}: {error}", path.display()))
                    })
            }
            ("Files", "write_string", [Value::String(path), Value::String(contents)]) => {
                let path = self.working_directory.join(path.0.flatten());
                std::fs::write(&path, contents.0.flatten().as_bytes())
                    .map(|_| Value::Unit)
                    .map_err(|error| {
                        runtime(span, format!("could not write {}: {error}", path.display()))
                    })
            }
            ("Files", "append_string", [Value::String(path), Value::String(contents)]) => {
                let path = self.working_directory.join(path.0.flatten());
                std::fs::OpenOptions::new()
                    .create(true)
                    .append(true)
                    .open(&path)
                    .and_then(|mut file| file.write_all(contents.0.flatten().as_bytes()))
                    .map(|_| Value::Unit)
                    .map_err(|error| {
                        runtime(
                            span,
                            format!("could not append {}: {error}", path.display()),
                        )
                    })
            }
            ("Diagnostics", "abort", [diagnostic]) => {
                Err(decode_compiler_diagnostic(diagnostic, span)?)
            }
            ("Diagnostics" | "Reporting", "report", [diagnostic]) => {
                let diagnostic = decode_compiler_diagnostic(diagnostic, span)?;
                diagnostic.write("", io::stderr()).map_err(|error| {
                    runtime(span, format!("could not render diagnostic: {error}"))
                })?;
                Ok(Value::Unit)
            }
            _ => Err(runtime(
                span,
                format!(
                    "unhandled effect operation `{effect}::{operation}` with {} argument(s)",
                    args.len()
                ),
            )
            .with_help("provide a host handler or correct the operation signature")),
        }
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct RuntimeLeafAuthority {
    by_function: HashMap<usize, RuntimeLeaf>,
    unbound_by_name: HashMap<String, RuntimeLeaf>,
    trusted_call_range: Option<Range<usize>>,
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum RuntimeLeaf {
    Primitive(Primitive),
    IntegerConversion {
        primitive: Primitive,
        target: IntegerKind,
    },
    FloatPrimitive(FloatRuntimeLeaf),
    HostImport(HostImportRole),
    Abort,
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum FloatRuntimeLeaf {
    Unary {
        primitive: Primitive,
        width: FloatKind,
    },
    Binary {
        primitive: Primitive,
        width: FloatKind,
    },
    Comparison {
        primitive: Primitive,
        width: FloatKind,
    },
    Convert {
        source: FloatKind,
        target: FloatKind,
    },
    IntToFloat {
        source: IntegerKind,
        target: FloatKind,
    },
    FloatToIntChecked {
        source: FloatKind,
        target: IntegerKind,
    },
    ToBits {
        source: FloatKind,
    },
    FromBits {
        target: FloatKind,
    },
}

impl RuntimeLeafAuthority {
    pub(crate) fn unbound(
        leaves: impl IntoIterator<Item = (String, RuntimeLeaf)>,
        trusted_call_range: Range<usize>,
    ) -> Self {
        Self {
            by_function: HashMap::new(),
            unbound_by_name: leaves.into_iter().collect(),
            trusted_call_range: Some(trusted_call_range),
        }
    }

    fn resolve(mut self, program: &Program) -> Self {
        let Some(trusted_call_range) = self.trusted_call_range.as_ref() else {
            return self;
        };
        let by_function = program
            .functions
            .iter()
            .enumerate()
            .filter(|(_, function)| {
                function.span.start >= trusted_call_range.start
                    && function.span.end <= trusted_call_range.end
            })
            .filter_map(|(index, function)| {
                let leaf = self.unbound_by_name.get(function.name.as_str()).copied()?;
                let leaf = match leaf {
                    RuntimeLeaf::Primitive(
                        primitive @ (Primitive::IntConvertChecked | Primitive::IntConvertWrapping),
                    ) => RuntimeLeaf::IntegerConversion {
                        primitive,
                        target: function.return_type.as_ref().and_then(integer_kind)?,
                    },
                    RuntimeLeaf::Primitive(primitive)
                        if crate::builtins::runtime_primitive_family(primitive)
                            == Some(crate::builtins::RuntimePrimitiveFamily::TypedFloat) =>
                    {
                        RuntimeLeaf::FloatPrimitive(float_runtime_leaf(function, primitive)?)
                    }
                    leaf => leaf,
                };
                Some((index, leaf))
            })
            .collect();
        self.by_function = by_function;
        self.unbound_by_name.clear();
        self
    }

    fn leaf(&self, function: usize) -> Option<RuntimeLeaf> {
        self.by_function.get(&function).copied()
    }

    fn authorizes_call(&self, span: Span) -> bool {
        self.trusted_call_range
            .as_ref()
            .is_some_and(|range| span.start >= range.start && span.end <= range.end)
    }
}

pub fn run(program: &Program, args: Vec<String>, host: &mut dyn Host) -> Result<Value, Diagnostic> {
    run_with_runtime(program, args, host, RuntimeLeafAuthority::default())
}

pub(crate) fn run_with_runtime(
    program: &Program,
    args: Vec<String>,
    host: &mut dyn Host,
    runtime_leaves: RuntimeLeafAuthority,
) -> Result<Value, Diagnostic> {
    run_entry_with_runtime(program, "main", args, host, runtime_leaves)
}

pub(crate) fn run_entry_with_runtime(
    program: &Program,
    entry_name: &str,
    args: Vec<String>,
    host: &mut dyn Host,
    runtime_leaves: RuntimeLeafAuthority,
) -> Result<Value, Diagnostic> {
    let runtime_leaves = runtime_leaves.resolve(program);
    // Keep the invocation arguments independently of the compatibility optional
    // `main(args)` adapter. The manifest-bound `process.args/get` leaf must see
    // the original invocation even when `main` itself has no parameter.
    let invocation_args = args.clone();
    let functions: Vec<_> = program
        .functions
        .iter()
        .map(|function| RuntimeFunction {
            declaration: function,
            parameter_names: Rc::new(
                function
                    .params
                    .iter()
                    .map(|parameter| Rc::<str>::from(parameter.name.as_str()))
                    .collect(),
            ),
        })
        .collect();
    let function_indices: HashMap<_, _> = functions
        .iter()
        .enumerate()
        .map(|(index, function)| (function.declaration.name.as_str(), index))
        .collect();
    let type_aliases = program
        .type_aliases
        .iter()
        .map(|alias| (alias.name.as_str(), &alias.target))
        .collect::<HashMap<_, _>>();
    let mut trait_methods = Vec::new();
    let mut trait_method_groups: Vec<Vec<usize>> = Vec::new();
    let mut trait_method_indices = HashMap::new();
    for implementation in &program.impls {
        if implementation.polarity != GoalPolarity::Positive {
            continue;
        }
        let Some(trait_name) = implementation
            .trait_ref
            .path
            .last()
            .map(|segment| segment.name.as_str())
        else {
            continue;
        };
        for method in &implementation.methods {
            if method.body.is_none() {
                continue;
            }
            let group = *trait_method_indices
                .entry((trait_name, method.name.as_str()))
                .or_insert_with(|| {
                    trait_method_groups.push(Vec::new());
                    trait_method_groups.len() - 1
                });
            let index = trait_methods.len();
            trait_methods.push(RuntimeTraitMethod {
                method,
                self_ty: &implementation.self_ty,
            });
            trait_method_groups[group].push(index);
        }
    }
    let main = function_indices
        .get(entry_name)
        .map(|index| functions[*index].declaration)
        .ok_or_else(|| Diagnostic::plain(format!("program does not declare `{entry_name}`")))?;
    let values = match main.params.len() {
        0 => Vec::new(),
        1 => vec![Value::List(
            args.into_iter()
                .map(|value| Value::String(value.into()))
                .collect(),
        )],
        _ => {
            return Err(runtime(
                main.span,
                format!(
                    "`{entry_name}` must accept zero parameters or one argument-list parameter"
                ),
            ));
        }
    };
    let structs = program
        .structs
        .iter()
        .map(|decl| {
            (
                decl.name.as_str(),
                decl.fields.iter().map(|field| field.name.clone()).collect(),
            )
        })
        .collect();
    let enum_variants = program
        .enums
        .iter()
        .flat_map(|decl| {
            decl.variants.iter().map(move |variant| {
                (
                    (decl.name.as_str(), variant.name.as_str()),
                    variant.fields.len(),
                )
            })
        })
        .collect();
    let effect_operations = program
        .effects
        .iter()
        .flat_map(|effect| {
            effect.operations.iter().map(move |operation| {
                (
                    (effect.name.as_str(), operation.name.as_str()),
                    OperationSemantics {
                        terminal: operation.terminal,
                        lower: operation.resumption_lower,
                        upper: operation.resumption_upper,
                    },
                )
            })
        })
        .collect();
    let drops = program
        .drops
        .iter()
        .map(|declaration| (declaration.target.as_str(), declaration))
        .collect();
    let function_count = functions.len();
    let mut evaluator = Evaluator {
        program,
        functions,
        function_indices,
        trait_methods,
        trait_method_groups,
        trait_method_indices,
        type_aliases,
        function_call_counts: vec![0; function_count],
        current_function: None,
        generic_witnesses: HashMap::new(),
        call_names: SpanMap::default(),
        call_kinds: SpanMap::default(),
        local_depths: SpanMap::default(),
        closure_captures: SpanMap::default(),
        validated_struct_literals: SpanSet::default(),
        bootstrap_fast_paths: env::var_os("GRANDIOSE_BOOTSTRAP_FAST_PATHS").is_some(),
        runtime_leaves,
        invocation_args,
        declaration_lookup_lists: Vec::new(),
        declaration_lookup_cache: HashMap::new(),
        declaration_lookup_hits: 0,
        declaration_lookup_misses: 0,
        structs,
        enum_variants,
        effect_operations,
        drops,
        globals: HashMap::new(),
        handlers: Vec::new(),
        next_handler_id: 0,
        host,
    };
    for binding in &program.globals {
        let value = evaluator.evaluate(binding.value.clone(), Locals::new())?;
        let name = binding
            .owner
            .as_ref()
            .map(|owner| format!("{owner}::{}", binding.name))
            .unwrap_or_else(|| binding.name.clone());
        evaluator.globals.insert(name, value);
    }
    let locals = main
        .params
        .iter()
        .map(|param| param.name.clone())
        .zip(values)
        .collect();
    let value = evaluator.evaluate(main.body.clone(), locals)?;
    if let Some(kind) = main.return_type.as_ref().and_then(integer_kind) {
        coerce_integer(value, kind, main.body.span)
    } else if let Some(kind) = main.return_type.as_ref().and_then(float_kind) {
        coerce_declared_float(value, kind, main.body.span)
    } else {
        Ok(value)
    }
}

struct RuntimeFunction<'a> {
    declaration: &'a Function,
    parameter_names: Rc<Vec<Rc<str>>>,
}

struct RuntimeTraitMethod<'a> {
    method: &'a TraitMethod,
    self_ty: &'a TypeSyntax,
}

struct Evaluator<'a> {
    program: &'a Program,
    functions: Vec<RuntimeFunction<'a>>,
    function_indices: HashMap<&'a str, usize>,
    trait_methods: Vec<RuntimeTraitMethod<'a>>,
    trait_method_groups: Vec<Vec<usize>>,
    trait_method_indices: HashMap<(&'a str, &'a str), usize>,
    type_aliases: HashMap<&'a str, &'a TypeSyntax>,
    function_call_counts: Vec<u64>,
    current_function: Option<usize>,
    /// Runtime witnesses for type parameters of the active recovery-evaluator
    /// call. Compiled execution resolves these calls statically; recovery
    /// execution retains enough evidence for the same receiverless choice.
    generic_witnesses: HashMap<String, Value>,
    call_names: SpanMap<Rc<str>>,
    call_kinds: SpanMap<CallKind>,
    local_depths: SpanMap<usize>,
    closure_captures: SpanMap<Rc<Vec<Rc<str>>>>,
    validated_struct_literals: SpanSet,
    bootstrap_fast_paths: bool,
    runtime_leaves: RuntimeLeafAuthority,
    invocation_args: Vec<String>,
    declaration_lookup_lists: Vec<Vector<Value>>,
    declaration_lookup_cache: HashMap<DeclarationLookupKey, Value>,
    declaration_lookup_hits: u64,
    declaration_lookup_misses: u64,
    structs: HashMap<&'a str, Vec<String>>,
    enum_variants: HashMap<(&'a str, &'a str), usize>,
    effect_operations: HashMap<(&'a str, &'a str), OperationSemantics>,
    drops: HashMap<&'a str, &'a DropDecl>,
    globals: HashMap<String, Value>,
    handlers: Vec<HandlerFrame>,
    next_handler_id: usize,
    host: &'a mut dyn Host,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum DeclarationLookupArgument {
    Unit,
    Int(i64),
    String(u64),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct DeclarationLookupKey {
    function: usize,
    list: usize,
    arguments: Vec<DeclarationLookupArgument>,
}

#[derive(Clone)]
struct HandlerFrame {
    id: usize,
    clauses: Rc<Vec<HandlerClause>>,
    captures: Locals,
}

#[derive(Clone)]
struct CapturedContinuation {
    handler_id: usize,
    frames: Vec<EvalFrame>,
    handlers: Vec<HandlerFrame>,
}

impl CapturedContinuation {
    /// Each multi-shot resume starts from the captured storage state. Cloning
    /// the `Rc` handles alone would make assignments in one invocation leak
    /// into later invocations, so clone the reachable cell graph while
    /// preserving alias identity inside the new snapshot.
    fn snapshot(&self) -> Self {
        let mut snapshot = ContinuationSnapshot::default();
        Self {
            handler_id: self.handler_id,
            frames: self
                .frames
                .iter()
                .map(|frame| snapshot.frame(frame))
                .collect(),
            handlers: self
                .handlers
                .iter()
                .map(|handler| snapshot.handler(handler))
                .collect(),
        }
    }
}

#[derive(Default)]
struct ContinuationSnapshot {
    cells: HashMap<usize, Rc<RefCell<Value>>>,
    locals: HashMap<usize, Locals>,
    arrays: HashMap<usize, ArrayRef>,
}

impl ContinuationSnapshot {
    fn cell(&mut self, source: &Rc<RefCell<Value>>) -> Rc<RefCell<Value>> {
        let key = Rc::as_ptr(source) as usize;
        if let Some(cell) = self.cells.get(&key) {
            return cell.clone();
        }
        let cell = Rc::new(RefCell::new(Value::Uninitialized));
        self.cells.insert(key, cell.clone());
        let value = self.value(&source.borrow());
        *cell.borrow_mut() = value;
        cell
    }

    fn locals(&mut self, source: &Locals) -> Locals {
        let key = Rc::as_ptr(&source.0) as usize;
        if let Some(locals) = self.locals.get(&key) {
            return locals.clone();
        }
        let locals = match source.0.as_ref() {
            LocalBinding::Empty => Locals::new(),
            LocalBinding::Bound {
                name,
                value,
                parent,
            } => Locals(Rc::new(LocalBinding::Bound {
                name: name.clone(),
                value: self.cell(value),
                parent: self.locals(parent),
            })),
        };
        self.locals.insert(key, locals.clone());
        locals
    }

    fn array(&mut self, source: &ArrayRef) -> ArrayRef {
        let key = Rc::as_ptr(&source.0) as usize;
        if let Some(array) = self.arrays.get(&key) {
            return array.clone();
        }
        let array = ArrayRef(Rc::new(RefCell::new(InterpreterArray::default())));
        self.arrays.insert(key, array.clone());
        let source = source.0.borrow();
        let slots = source
            .slots
            .iter()
            .map(|slot| slot.as_ref().map(|value| self.cell(value)))
            .collect();
        *array.0.borrow_mut() = InterpreterArray {
            slots,
            logical_capacity: source.logical_capacity,
        };
        array
    }

    fn value(&mut self, source: &Value) -> Value {
        match source {
            Value::Uninitialized => Value::Uninitialized,
            Value::Unit => Value::Unit,
            Value::Int(value) => Value::Int(*value),
            Value::Integer { signed, bits, raw } => Value::Integer {
                signed: *signed,
                bits: *bits,
                raw: *raw,
            },
            Value::IntegerLiteral {
                negative,
                magnitude,
            } => Value::IntegerLiteral {
                negative: *negative,
                magnitude: *magnitude,
            },
            Value::Float(value) => Value::Float(*value),
            Value::Float32(value) => Value::Float32(*value),
            Value::Char(value) => Value::Char(*value),
            Value::String(value) => Value::String(value.clone()),
            Value::Bytes(value) => Value::Bytes(value.clone()),
            Value::List(values) => {
                Value::List(values.iter().map(|value| self.value(value)).collect())
            }
            Value::Array(array) => Value::Array(self.array(array)),
            Value::Struct { name, fields } => Value::Struct {
                name: name.clone(),
                fields: Rc::new(
                    fields
                        .iter()
                        .map(|(name, value)| (name.clone(), self.value(value)))
                        .collect(),
                ),
            },
            Value::Enum {
                name,
                variant,
                fields,
            } => Value::Enum {
                name: name.clone(),
                variant: variant.clone(),
                fields: Rc::new(fields.iter().map(|value| self.value(value)).collect()),
            },
            Value::Closure {
                params,
                body,
                captures,
            } => Value::Closure {
                params: params.clone(),
                body: body.clone(),
                captures: self.locals(captures),
            },
            Value::FunctionItem(function) => Value::FunctionItem(*function),
            Value::Reference { value, unique } => Value::Reference {
                value: self.cell(value),
                unique: *unique,
            },
            Value::ProjectedReference {
                root,
                fields,
                unique,
            } => Value::ProjectedReference {
                root: self.cell(root),
                fields: fields.clone(),
                unique: *unique,
            },
            // A nested resumption is an affine runtime capability, not
            // ordinary mutable place storage. Static quantity checking rejects
            // duplicating it when that would be unsound.
            Value::Resumption(resumption) => Value::Resumption(resumption.clone()),
        }
    }

    fn handler(&mut self, source: &HandlerFrame) -> HandlerFrame {
        HandlerFrame {
            id: source.id,
            clauses: source.clauses.clone(),
            captures: self.locals(&source.captures),
        }
    }

    fn continuation(&mut self, source: &BlockContinuation) -> BlockContinuation {
        BlockContinuation {
            statements: source.statements.clone(),
            index: source.index,
            locals: self.locals(&source.locals),
        }
    }

    fn frame(&mut self, source: &EvalFrame) -> EvalFrame {
        let mut frame = source.clone();
        match &mut frame {
            EvalFrame::List { values, locals, .. } => {
                *values = values.iter().map(|value| self.value(value)).collect();
                *locals = self.locals(locals);
            }
            EvalFrame::Struct { values, locals, .. } => {
                *values = values
                    .iter()
                    .map(|(name, value)| (name.clone(), self.value(value)))
                    .collect();
                *locals = self.locals(locals);
            }
            EvalFrame::Block { locals, .. } | EvalFrame::CallCallee { locals, .. } => {
                *locals = self.locals(locals);
            }
            EvalFrame::AssignmentDereference {
                replacement,
                continuation,
                ..
            } => {
                *replacement = self.value(replacement);
                *continuation = self.continuation(continuation);
            }
            EvalFrame::AssignmentStoreAfterDestroy {
                root,
                replacement,
                continuation,
                ..
            } => {
                *root = self.cell(root);
                *replacement = self.value(replacement);
                *continuation = self.continuation(continuation);
            }
            EvalFrame::CallArgs(pending) => {
                pending.locals = self.locals(&pending.locals);
                pending.values = pending
                    .values
                    .iter()
                    .map(|value| self.value(value))
                    .collect();
                if let CallDesignator::Closure(value) = &mut pending.callee {
                    *value = self.value(value);
                }
            }
            EvalFrame::PerformArgs { values, locals, .. } => {
                *values = values.iter().map(|value| self.value(value)).collect();
                *locals = self.locals(locals);
            }
            EvalFrame::ResumptionBoundary {
                return_frames,
                return_handlers,
            } => {
                *return_frames = return_frames
                    .iter()
                    .map(|frame| self.frame(frame))
                    .collect();
                *return_handlers = return_handlers
                    .iter()
                    .map(|handler| self.handler(handler))
                    .collect();
            }
            EvalFrame::DropStructural { value, .. } => *value = self.value(value),
            EvalFrame::DestroyRemaining { values, .. } => {
                *values = values.iter().map(|value| self.value(value)).collect();
            }
            EvalFrame::BinaryLeft { locals, .. } => *locals = self.locals(locals),
            EvalFrame::BinaryRight { lhs, .. } => *lhs = self.value(lhs),
            EvalFrame::RefinementIf { locals, .. } => *locals = self.locals(locals),
            EvalFrame::Field { .. }
            | EvalFrame::MoveDereference { .. }
            | EvalFrame::MemoizeDeclarationLookup { .. }
            | EvalFrame::FunctionReturn { .. }
            | EvalFrame::GenericEnvironment { .. }
            | EvalFrame::HandleExit { .. }
            | EvalFrame::HandlerDelimiter { .. }
            | EvalFrame::Unary { .. }
            | EvalFrame::Reborrow { .. }
            | EvalFrame::Is { .. } => {}
        }
        frame
    }
}

#[derive(Clone, Copy)]
struct OperationSemantics {
    terminal: bool,
    lower: usize,
    upper: Option<usize>,
}

struct ResumptionState {
    continuation: CapturedContinuation,
    lower: usize,
    upper: Option<usize>,
    uses: usize,
    closed: bool,
}

enum Control {
    Expr(Expr, Locals),
    Value(Value),
}

#[derive(Clone)]
enum CallDesignator {
    Path { callee: Rc<Expr>, kind: CallKind },
    Closure(Value),
}

#[derive(Clone, Copy)]
enum CallKind {
    Resume,
    TailResume,
    Cancel,
    Destroy,
    Intrinsic(IntrinsicKind),
    EnumConstructor(usize),
    Function(usize),
    TraitMethodGroup(usize),
}

#[derive(Clone, Copy)]
enum IntrinsicKind {
    StrLen,
    StrByteLen,
    StrByteAt,
    StrCharAt,
    StrNextIndex,
    StrFind,
    StrFindFrom,
    StrRfind,
    StrSlice,
    StrTrim,
    StrTrimStart,
    StrTrimEnd,
    IsI64,
    IsAsciiWhitespace,
    IsAsciiDigit,
    IsAsciiIdentStart,
    IsAsciiIdentContinue,
    ParseI64,
    IntToString,
    BoolToString,
    ListLen,
    ListGet,
    ListPush,
    ListConcat,
    Debug,
    Assert,
    Invalid,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct IntegerKind {
    signed: bool,
    bits: u8,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum FloatKind {
    F32,
    F64,
}

fn integer_kind(ty: &crate::ast::TypeSyntax) -> Option<IntegerKind> {
    integer_kind_name(ty.simple_name()?)
}

fn integer_kind_name(name: &str) -> Option<IntegerKind> {
    let (signed, bits) = crate::builtins::integer_scalar_layout(name)?;
    Some(IntegerKind { signed, bits })
}

fn float_kind(ty: &crate::ast::TypeSyntax) -> Option<FloatKind> {
    float_kind_name(ty.simple_name()?)
}

fn float_kind_name(name: &str) -> Option<FloatKind> {
    match name {
        "f32" => Some(FloatKind::F32),
        "f64" => Some(FloatKind::F64),
        _ => None,
    }
}

fn float_runtime_leaf(function: &Function, primitive: Primitive) -> Option<FloatRuntimeLeaf> {
    let signature = crate::builtins::runtime_leaf_signature(&function.name, primitive)?;
    let params = function
        .params
        .iter()
        .map(|parameter| parameter.ty.simple_name())
        .collect::<Option<Vec<_>>>()?;
    let result = function.return_type.as_ref()?.simple_name()?;
    if !signature.matches(&params, Some(result)) {
        return None;
    }
    let expected = signature.parameters().collect::<Vec<_>>();
    match primitive {
        Primitive::FloatNeg => Some(FloatRuntimeLeaf::Unary {
            primitive,
            width: float_kind_name(expected[0])?,
        }),
        Primitive::FloatAdd
        | Primitive::FloatSub
        | Primitive::FloatMul
        | Primitive::FloatDiv
        | Primitive::FloatRem => Some(FloatRuntimeLeaf::Binary {
            primitive,
            width: float_kind_name(expected[0])?,
        }),
        Primitive::FloatEq
        | Primitive::FloatNe
        | Primitive::FloatLt
        | Primitive::FloatLe
        | Primitive::FloatGt
        | Primitive::FloatGe => Some(FloatRuntimeLeaf::Comparison {
            primitive,
            width: float_kind_name(expected[0])?,
        }),
        Primitive::FloatConvert => Some(FloatRuntimeLeaf::Convert {
            source: float_kind_name(expected[0])?,
            target: float_kind_name(signature.result())?,
        }),
        Primitive::IntToFloat => Some(FloatRuntimeLeaf::IntToFloat {
            source: integer_kind_name(expected[0])?,
            target: float_kind_name(signature.result())?,
        }),
        Primitive::FloatToIntChecked => Some(FloatRuntimeLeaf::FloatToIntChecked {
            source: float_kind_name(expected[0])?,
            target: integer_kind_name(signature.result())?,
        }),
        Primitive::FloatToBits => Some(FloatRuntimeLeaf::ToBits {
            source: float_kind_name(expected[0])?,
        }),
        Primitive::FloatFromBits => Some(FloatRuntimeLeaf::FromBits {
            target: float_kind_name(signature.result())?,
        }),
        _ => None,
    }
}

#[derive(Clone)]
enum EvalFrame {
    List {
        expressions: Rc<Vec<Expr>>,
        next: usize,
        values: Vec<Value>,
        locals: Locals,
    },
    Struct {
        name: Rc<str>,
        fields: Rc<Vec<(String, Expr)>>,
        next: usize,
        values: HashMap<String, Value>,
        locals: Locals,
        span: Span,
    },
    Field {
        name: String,
        span: Span,
    },
    Block {
        statements: Rc<Vec<Stmt>>,
        index: usize,
        locals: Locals,
    },
    AssignmentDereference {
        replacement: Value,
        fields: Vec<AssignmentField>,
        span: Span,
        continuation: BlockContinuation,
    },
    AssignmentStoreAfterDestroy {
        root: Rc<RefCell<Value>>,
        fields: Vec<AssignmentField>,
        replacement: Value,
        span: Span,
        continuation: BlockContinuation,
    },
    MoveDereference {
        fields: Vec<AssignmentField>,
        span: Span,
    },
    CallCallee {
        arguments: Rc<Vec<Expr>>,
        locals: Locals,
        span: Span,
    },
    CallArgs(PendingCallArguments),
    MemoizeDeclarationLookup {
        key: DeclarationLookupKey,
    },
    FunctionReturn {
        integer_kind: Option<IntegerKind>,
        float_kind: Option<FloatKind>,
        span: Span,
    },
    GenericEnvironment {
        previous: HashMap<String, Value>,
    },
    PerformArgs {
        effect: Rc<str>,
        operation: Rc<str>,
        arguments: Rc<Vec<Expr>>,
        next: usize,
        values: Vec<Value>,
        locals: Locals,
        span: Span,
    },
    HandleExit {
        handler_id: usize,
    },
    HandlerDelimiter {
        handler_id: usize,
    },
    ResumptionBoundary {
        return_frames: Vec<EvalFrame>,
        return_handlers: Vec<HandlerFrame>,
    },
    Unary {
        op: UnaryOp,
        span: Span,
    },
    Reborrow {
        unique: bool,
        span: Span,
    },
    DropStructural {
        value: Value,
        span: Span,
    },
    DestroyRemaining {
        values: Vec<Value>,
        span: Span,
    },
    BinaryLeft {
        op: BinaryOp,
        rhs: Expr,
        locals: Locals,
        span: Span,
    },
    BinaryRight {
        op: BinaryOp,
        lhs: Value,
        span: Span,
    },
    /// Complete an observational `subject is Pattern` decision after the
    /// subject has evaluated.
    Is {
        pattern: Rc<Pattern>,
        span: Span,
    },
    RefinementIf {
        pattern: Rc<Pattern>,
        positive: Expr,
        negative: Expr,
        locals: Locals,
        span: Span,
    },
}

#[derive(Clone)]
struct BlockContinuation {
    statements: Rc<Vec<Stmt>>,
    index: usize,
    locals: Locals,
}

#[derive(Clone)]
struct PendingCallArguments {
    callee: CallDesignator,
    arguments: Rc<Vec<Expr>>,
    next: usize,
    values: Vec<Value>,
    locals: Locals,
    span: Span,
}

fn pending_frame_span(frame: &EvalFrame) -> Option<Span> {
    match frame {
        EvalFrame::Struct { span, .. }
        | EvalFrame::Field { span, .. }
        | EvalFrame::CallCallee { span, .. }
        | EvalFrame::PerformArgs { span, .. }
        | EvalFrame::Unary { span, .. }
        | EvalFrame::Reborrow { span, .. }
        | EvalFrame::DropStructural { span, .. }
        | EvalFrame::DestroyRemaining { span, .. }
        | EvalFrame::FunctionReturn { span, .. }
        | EvalFrame::BinaryLeft { span, .. }
        | EvalFrame::BinaryRight { span, .. }
        | EvalFrame::Is { span, .. }
        | EvalFrame::RefinementIf { span, .. }
        | EvalFrame::AssignmentDereference { span, .. }
        | EvalFrame::AssignmentStoreAfterDestroy { span, .. }
        | EvalFrame::MoveDereference { span, .. } => Some(*span),
        EvalFrame::CallArgs(call) => Some(call.span),
        EvalFrame::List { .. }
        | EvalFrame::Block { .. }
        | EvalFrame::MemoizeDeclarationLookup { .. }
        | EvalFrame::GenericEnvironment { .. }
        | EvalFrame::HandleExit { .. }
        | EvalFrame::HandlerDelimiter { .. }
        | EvalFrame::ResumptionBoundary { .. } => None,
    }
}

fn bind_pattern_names(pattern: &Pattern, bound: &mut HashSet<String>) {
    match &pattern.kind {
        PatternKind::Binding(name) => {
            bound.insert(name.clone());
        }
        PatternKind::Variant { fields, .. } => {
            for field in fields {
                bind_pattern_names(field, bound);
            }
        }
        PatternKind::Tuple { elements, .. } => {
            for element in elements {
                bind_pattern_names(element, bound);
            }
        }
        PatternKind::Struct { fields, .. } => {
            for field in fields {
                bind_pattern_names(&field.pattern, bound);
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

fn collect_free_variables(expression: &Expr, bound: &HashSet<String>, free: &mut HashSet<String>) {
    match &expression.kind {
        ExprKind::Unit | ExprKind::Int(_) | ExprKind::String(_) => {}
        ExprKind::Variable(path) => {
            if path.len() == 1 && !bound.contains(path[0].as_ref()) {
                free.insert(path[0].to_string());
            }
        }
        ExprKind::Move(operand) => collect_free_variables(operand, bound, free),
        ExprKind::Closure { params, body } => {
            let mut nested_bound = bound.clone();
            nested_bound.extend(params.iter().map(|param| param.to_string()));
            collect_free_variables(body, &nested_bound, free);
        }
        ExprKind::List(expressions) | ExprKind::Tuple(expressions) => {
            for expression in expressions.iter() {
                collect_free_variables(expression, bound, free);
            }
        }
        ExprKind::Struct { fields, .. } => {
            for (_, expression) in fields.iter() {
                collect_free_variables(expression, bound, free);
            }
        }
        ExprKind::Field(subject, _)
        | ExprKind::Unary {
            operand: subject, ..
        } => {
            collect_free_variables(subject, bound, free);
        }
        ExprKind::Block(statements) => {
            let mut block_bound = bound.clone();
            for statement in statements.iter() {
                match statement {
                    Stmt::Let { name, value, .. } => {
                        collect_free_variables(value, &block_bound, free);
                        block_bound.insert(name.clone());
                    }
                    Stmt::Deconstruct { fields, value, .. } => {
                        collect_free_variables(value, &block_bound, free);
                        block_bound.extend(fields.iter().filter_map(|field| field.binding.clone()));
                    }
                    Stmt::Assign {
                        destination, value, ..
                    } => {
                        collect_free_variables(value, &block_bound, free);
                        match &destination.kind {
                            AssignmentPlaceKind::Local { name, .. } => {
                                if !block_bound.contains(name.as_ref()) {
                                    free.insert(name.to_string());
                                }
                            }
                            AssignmentPlaceKind::Dereference { reference, .. } => {
                                collect_free_variables(reference, &block_bound, free);
                            }
                        }
                    }
                    Stmt::Expr(expression) => {
                        collect_free_variables(expression, &block_bound, free);
                    }
                }
            }
        }
        ExprKind::Call(callee, arguments) => {
            collect_free_variables(callee, bound, free);
            for argument in arguments.iter() {
                collect_free_variables(argument, bound, free);
            }
        }
        ExprKind::Perform { args, .. } => {
            for argument in args.iter() {
                collect_free_variables(argument, bound, free);
            }
        }
        ExprKind::Handle {
            computation,
            clauses,
        } => {
            collect_free_variables(computation, bound, free);
            for clause in clauses.iter() {
                let mut clause_bound = bound.clone();
                for pattern in &clause.patterns {
                    bind_pattern_names(pattern, &mut clause_bound);
                }
                if let Some(resumption) = &clause.resumption {
                    clause_bound.insert(resumption.clone());
                }
                collect_free_variables(&clause.body, &clause_bound, free);
            }
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            collect_free_variables(lhs, bound, free);
            collect_free_variables(rhs, bound, free);
        }
        ExprKind::Float(_)
        | ExprKind::Char(_)
        | ExprKind::Byte(_)
        | ExprKind::ByteString(_)
        | ExprKind::LabelReference(_) => {}
        ExprKind::TypedClosure { params, body, .. } => {
            let mut nested_bound = bound.clone();
            nested_bound.extend(params.iter().map(|param| param.name.clone()));
            collect_free_variables(body, &nested_bound, free);
        }
        ExprKind::Labeled { body, .. } | ExprKind::LabelDestination { body, .. } => {
            collect_free_variables(body, bound, free);
        }
        ExprKind::Leave { value, .. } => {
            if let Some(value) = value {
                collect_free_variables(value, bound, free);
            }
        }
        ExprKind::Resume { resumption, value } | ExprKind::TailResume { resumption, value } => {
            collect_free_variables(resumption, bound, free);
            if let Some(value) = value {
                collect_free_variables(value, bound, free);
            }
        }
        ExprKind::Cancel { resumption } => collect_free_variables(resumption, bound, free),
        ExprKind::Is { subject, .. } => collect_free_variables(subject, bound, free),
        ExprKind::ContextBlock(statements) => {
            let context_block = Expr {
                kind: ExprKind::Block(statements.clone()),
                span: expression.span,
            };
            collect_free_variables(&context_block, bound, free);
        }
    }
}

fn process_memory_summary() -> String {
    let Ok(status) = std::fs::read_to_string("/proc/self/status") else {
        return "memory=unavailable".to_string();
    };
    let mut rss = "?";
    let mut peak = "?";
    let mut size = "?";
    for line in status.lines() {
        if let Some(value) = line.strip_prefix("VmRSS:") {
            rss = value.trim();
        } else if let Some(value) = line.strip_prefix("VmHWM:") {
            peak = value.trim();
        } else if let Some(value) = line.strip_prefix("VmSize:") {
            size = value.trim();
        }
    }
    format!("memory=[rss:{rss}, peak:{peak}, virtual:{size}]")
}

fn bootstrap_token_kind(variant: &'static str, fields: Vec<Value>) -> Value {
    Value::Enum {
        name: Rc::from("TokenKind"),
        variant: Rc::from(variant),
        fields: Rc::new(fields),
    }
}

fn bootstrap_token(kind: Value, start: usize, end: usize) -> Value {
    Value::Struct {
        name: Rc::from("Token"),
        fields: Rc::new(HashMap::from([
            ("kind".to_string(), kind),
            (
                "span".to_string(),
                Value::Struct {
                    name: Rc::from("SourceSpan"),
                    fields: Rc::new(HashMap::from([
                        ("start".to_string(), Value::Int(start as i64)),
                        ("end".to_string(), Value::Int(end as i64)),
                    ])),
                },
            ),
        ])),
    }
}

/// Interpreter-only acceleration for the self-hosting bootstrap. This mirrors
/// compiler/src/main.glorious's lexer, but returns ordinary evaluator values so the
/// parser and every later compiler phase still execute in Grandiose.
fn bootstrap_lex(source: &Value, span: Span) -> Result<Value, Diagnostic> {
    let Value::Struct { name, fields } = source else {
        return Err(runtime(span, "bootstrap lexer expected a SourceFile"));
    };
    if name.as_ref() != "SourceFile" {
        return Err(runtime(span, "bootstrap lexer expected a SourceFile"));
    }
    let Some(Value::String(text)) = fields.get("text") else {
        return Err(runtime(span, "bootstrap lexer expected SourceFile.text"));
    };
    let text = text.0.flatten();
    let bytes = text.as_bytes();
    let mut cursor = 0_usize;
    let mut tokens = Vector::new();

    while cursor < bytes.len() {
        if bytes[cursor].is_ascii_whitespace() {
            cursor += 1;
            continue;
        }
        let start = cursor;
        let byte = bytes[cursor];
        let kind = if byte.is_ascii_alphabetic() || byte == b'_' {
            cursor += 1;
            while cursor < bytes.len()
                && (bytes[cursor].is_ascii_alphanumeric() || bytes[cursor] == b'_')
            {
                cursor += 1;
            }
            bootstrap_token_kind(
                "Identifier",
                vec![Value::String(text[start..cursor].to_string().into())],
            )
        } else if byte.is_ascii_digit() {
            cursor += 1;
            while cursor < bytes.len() && bytes[cursor].is_ascii_digit() {
                cursor += 1;
            }
            bootstrap_token_kind(
                "Integer",
                vec![Value::String(text[start..cursor].to_string().into())],
            )
        } else if byte == b'"' {
            cursor += 1;
            let mut output = String::new();
            let mut closed = false;
            while cursor < bytes.len() {
                if bytes[cursor] == b'"' {
                    cursor += 1;
                    closed = true;
                    break;
                }
                if bytes[cursor] == b'\\' {
                    cursor += 1;
                    let Some(&escaped) = bytes.get(cursor) else {
                        return Err(runtime(
                            span,
                            "unfinished string escape in bootstrap source",
                        ));
                    };
                    cursor += 1;
                    output.push(match escaped {
                        b'n' => '\n',
                        b'r' => '\r',
                        b't' => '\t',
                        b'"' => '"',
                        b'\\' => '\\',
                        _ => {
                            return Err(runtime(span, "unknown string escape in bootstrap source"));
                        }
                    });
                } else {
                    let character = text[cursor..]
                        .chars()
                        .next()
                        .ok_or_else(|| runtime(span, "invalid UTF-8 in bootstrap source"))?;
                    output.push(character);
                    cursor += character.len_utf8();
                }
            }
            if !closed {
                return Err(runtime(
                    span,
                    "unfinished string literal in bootstrap source",
                ));
            }
            bootstrap_token_kind("String", vec![Value::String(output.into())])
        } else {
            cursor += 1;
            let (variant, consume_following) = match byte {
                b'(' => ("LeftParen", None),
                b')' => ("RightParen", None),
                b'{' => ("LeftBrace", None),
                b'}' => ("RightBrace", None),
                b'[' => ("LeftBracket", None),
                b']' => ("RightBracket", None),
                b'+' => ("Plus", None),
                b'*' => ("Star", None),
                b'/' => ("Slash", None),
                b',' => ("Comma", None),
                b';' => ("Semicolon", None),
                b'.' => ("Dot", None),
                b'&' => ("Ampersand", None),
                b':' if bytes.get(cursor) == Some(&b':') => ("DoubleColon", Some(b':')),
                b':' => ("Colon", None),
                b'=' if bytes.get(cursor) == Some(&b'=') => ("EqualEqual", Some(b'=')),
                b'=' if bytes.get(cursor) == Some(&b'>') => ("FatArrow", Some(b'>')),
                b'=' => ("Equal", None),
                b'!' if bytes.get(cursor) == Some(&b'=') => ("BangEqual", Some(b'=')),
                b'!' => ("Bang", None),
                b'<' if bytes.get(cursor) == Some(&b'=') => ("LessEqual", Some(b'=')),
                b'<' => ("Less", None),
                b'>' if bytes.get(cursor) == Some(&b'=') => ("GreaterEqual", Some(b'=')),
                b'>' => ("Greater", None),
                b'-' if bytes.get(cursor) == Some(&b'>') => ("Arrow", Some(b'>')),
                b'-' => ("Minus", None),
                _ => {
                    return Err(runtime(
                        span,
                        format!("bootstrap lexer rejected byte {start}"),
                    ));
                }
            };
            if consume_following.is_some() {
                cursor += 1;
            }
            bootstrap_token_kind(variant, Vec::new())
        };
        tokens.push_back(bootstrap_token(kind, start, cursor));
    }
    tokens.push_back(bootstrap_token(
        bootstrap_token_kind("End", Vec::new()),
        cursor,
        cursor,
    ));
    Ok(Value::List(tokens))
}

impl Evaluator<'_> {
    fn closure_capture_names(
        &mut self,
        span: Span,
        params: &[Rc<str>],
        body: &Expr,
    ) -> Rc<Vec<Rc<str>>> {
        let key = span_key(span);
        if let Some(names) = self.closure_captures.get(&key) {
            return names.clone();
        }
        let bound = params
            .iter()
            .map(|param| param.to_string())
            .collect::<HashSet<_>>();
        let mut free = HashSet::new();
        collect_free_variables(body, &bound, &mut free);
        let mut names = free.into_iter().map(Rc::<str>::from).collect::<Vec<_>>();
        names.sort_unstable_by(|left, right| left.as_ref().cmp(right.as_ref()));
        let names = Rc::new(names);
        self.closure_captures.insert(key, names.clone());
        names
    }

    fn call_name(&mut self, callee: &Expr, path: &[Rc<str>]) -> Rc<str> {
        let key = span_key(callee.span);
        if let Some(name) = self.call_names.get(&key) {
            return name.clone();
        }
        let name: Rc<str> = if path.len() == 1 {
            path[0].clone()
        } else {
            Rc::from(
                path.iter()
                    .map(|segment| segment.as_ref())
                    .collect::<Vec<_>>()
                    .join("::"),
            )
        };
        self.call_names.insert(key, name.clone());
        name
    }

    fn emit_telemetry(&mut self, elapsed: Duration, steps: u64, span: Span, frames: &[EvalFrame]) {
        let mut calls = 0;
        let mut blocks = 0;
        let mut handlers = 0;
        let mut performs = 0;
        let mut binaries = 0;
        let mut aggregates = 0;
        let mut other = 0;
        let mut callsites = HashMap::<(usize, usize), usize>::new();
        for frame in frames {
            match frame {
                EvalFrame::CallCallee { span, .. } => {
                    calls += 1;
                    *callsites.entry((span.start, span.end)).or_default() += 1;
                }
                EvalFrame::CallArgs(call) => {
                    calls += 1;
                    *callsites
                        .entry((call.span.start, call.span.end))
                        .or_default() += 1;
                }
                EvalFrame::Block { .. }
                | EvalFrame::AssignmentDereference { .. }
                | EvalFrame::AssignmentStoreAfterDestroy { .. } => blocks += 1,
                EvalFrame::MemoizeDeclarationLookup { .. }
                | EvalFrame::FunctionReturn { .. }
                | EvalFrame::GenericEnvironment { .. } => other += 1,
                EvalFrame::HandleExit { .. }
                | EvalFrame::HandlerDelimiter { .. }
                | EvalFrame::ResumptionBoundary { .. } => handlers += 1,
                EvalFrame::PerformArgs { .. } => performs += 1,
                EvalFrame::BinaryLeft { .. } | EvalFrame::BinaryRight { .. } => binaries += 1,
                EvalFrame::List { .. } | EvalFrame::Struct { .. } => aggregates += 1,
                EvalFrame::Field { .. }
                | EvalFrame::Unary { .. }
                | EvalFrame::Reborrow { .. }
                | EvalFrame::MoveDereference { .. }
                | EvalFrame::Is { .. }
                | EvalFrame::RefinementIf { .. }
                | EvalFrame::DropStructural { .. }
                | EvalFrame::DestroyRemaining { .. } => other += 1,
            }
        }
        let dominant_callsite = callsites
            .into_iter()
            .max_by_key(|(_, count)| *count)
            .map_or_else(
                || "none".to_string(),
                |((start, end), count)| format!("{start}..{end} x{count}"),
            );
        let mut hot_functions = self
            .function_call_counts
            .iter()
            .copied()
            .enumerate()
            .filter(|(_, count)| *count > 0)
            .collect::<Vec<_>>();
        hot_functions.sort_unstable_by_key(|(_, count)| std::cmp::Reverse(*count));
        let hot_functions = hot_functions
            .into_iter()
            .take(8)
            .map(|(index, count)| format!("{}={count}", self.functions[index].declaration.name))
            .collect::<Vec<_>>()
            .join(", ");
        let current_function = self
            .current_function
            .map(|index| self.functions[index].declaration.name.as_str())
            .unwrap_or("<entry>");
        eprintln!(
            "[grandiose telemetry] elapsed={}s steps={steps} span={}..{} current={} \
             frames={} handlers={} frame_mix=[call:{calls}, block:{blocks}, handler:{handlers}, \
             perform:{performs}, binary:{binaries}, aggregate:{aggregates}, other:{other}] \
             dominant_pending_call={} hot_calls=[{}] declaration_lookup_cache=[hits:{}, \
             misses:{}, entries:{}] {}",
            elapsed.as_secs(),
            span.start,
            span.end,
            current_function,
            frames.len(),
            self.handlers.len(),
            dominant_callsite,
            hot_functions,
            self.declaration_lookup_hits,
            self.declaration_lookup_misses,
            self.declaration_lookup_cache.len(),
            process_memory_summary(),
        );
        self.function_call_counts.fill(0);
        self.declaration_lookup_hits = 0;
        self.declaration_lookup_misses = 0;
    }

    fn evaluate(&mut self, expression: Expr, locals: Locals) -> Result<Value, Diagnostic> {
        let max_frames = env::var("GRANDIOSE_MAX_EVAL_FRAMES")
            .ok()
            .and_then(|value| value.parse().ok())
            .filter(|limit| *limit > 0)
            .unwrap_or(DEFAULT_MAX_EVALUATION_FRAMES);
        let telemetry_interval = env::var("GRANDIOSE_TELEMETRY_SECONDS")
            .ok()
            .and_then(|value| value.parse::<u64>().ok())
            .filter(|seconds| *seconds > 0)
            .map(Duration::from_secs);
        let started = Instant::now();
        let mut next_telemetry = telemetry_interval.map(|interval| started + interval);
        let mut next_memory_trim = started + MEMORY_TRIM_INTERVAL;
        let mut steps = 0_u64;
        let mut current_span = expression.span;
        let mut control = Control::Expr(expression, locals);
        let mut frames = Vec::<EvalFrame>::new();

        loop {
            steps = steps.wrapping_add(1);
            if let Control::Expr(expression, _) = &control {
                current_span = expression.span;
            }
            if steps & ((1 << 20) - 1) == 0 {
                let now = Instant::now();
                if now >= next_memory_trim {
                    trim_process_memory();
                    next_memory_trim = now + MEMORY_TRIM_INTERVAL;
                }
                if let Some(next) = next_telemetry
                    && now >= next
                {
                    self.emit_telemetry(now.duration_since(started), steps, current_span, &frames);
                    next_telemetry = telemetry_interval.map(|interval| now + interval);
                }
            }
            if frames.len() >= max_frames {
                let mut list = 0;
                let mut structure = 0;
                let mut field = 0;
                let mut block = 0;
                let mut call = 0;
                let mut perform = 0;
                let mut handler = 0;
                let mut resumption = 0;
                let mut unary = 0;
                let mut destroy = 0;
                let mut binary = 0;
                let mut callsites = HashMap::<(usize, usize), (Span, usize)>::new();
                for frame in &frames {
                    match frame {
                        EvalFrame::List { .. } => list += 1,
                        EvalFrame::Struct { .. } => structure += 1,
                        EvalFrame::Field { .. } => field += 1,
                        EvalFrame::Block { .. }
                        | EvalFrame::AssignmentDereference { .. }
                        | EvalFrame::AssignmentStoreAfterDestroy { .. } => block += 1,
                        EvalFrame::CallCallee { span, .. } => {
                            call += 1;
                            callsites
                                .entry((span.start, span.end))
                                .and_modify(|(_, count)| *count += 1)
                                .or_insert((*span, 1));
                        }
                        EvalFrame::CallArgs(pending) => {
                            call += 1;
                            callsites
                                .entry((pending.span.start, pending.span.end))
                                .and_modify(|(_, count)| *count += 1)
                                .or_insert((pending.span, 1));
                        }
                        EvalFrame::MemoizeDeclarationLookup { .. }
                        | EvalFrame::FunctionReturn { .. }
                        | EvalFrame::GenericEnvironment { .. } => call += 1,
                        EvalFrame::PerformArgs { .. } => perform += 1,
                        EvalFrame::HandleExit { .. } | EvalFrame::HandlerDelimiter { .. } => {
                            handler += 1
                        }
                        EvalFrame::ResumptionBoundary { .. } => resumption += 1,
                        EvalFrame::Unary { .. }
                        | EvalFrame::Reborrow { .. }
                        | EvalFrame::MoveDereference { .. } => unary += 1,
                        EvalFrame::DropStructural { .. } | EvalFrame::DestroyRemaining { .. } => {
                            destroy += 1
                        }
                        EvalFrame::BinaryLeft { .. }
                        | EvalFrame::BinaryRight { .. }
                        | EvalFrame::Is { .. }
                        | EvalFrame::RefinementIf { .. } => binary += 1,
                    }
                }
                let mut diagnostic = runtime(
                    current_span,
                    format!("evaluation retained at least {max_frames} pending computations"),
                )
                .with_help(
                    "make the recursive operation tail-recursive, or raise \
                     GRANDIOSE_MAX_EVAL_FRAMES for an intentionally deep computation",
                )
                .with_note(format!(
                    "pending frames: call={call}, block={block}, handler={handler}, \
                     perform={perform}, binary={binary}, list={list}, struct={structure}, \
                     field={field}, unary={unary}, destroy={destroy}, resumption={resumption}"
                ));
                if let Some((span, count)) = callsites.into_values().max_by_key(|(_, count)| *count)
                {
                    diagnostic = diagnostic
                        .with_related(span, format!("this callsite is pending {count} times"));
                } else if let Some(span) = frames.iter().rev().find_map(pending_frame_span) {
                    diagnostic = diagnostic.with_related(
                        span,
                        "this expression is among those waiting for the current computation",
                    );
                }
                return Err(diagnostic);
            }
            control = match control {
                Control::Expr(expr, locals) => match expr.kind {
                    ExprKind::Unit => Control::Value(Value::Unit),
                    ExprKind::Int(value) => {
                        let value = match self.program.numeric_literal(expr.span) {
                            Some(literal) => {
                                let magnitude = literal.as_u128(expr.span)?;
                                match i64::try_from(magnitude) {
                                    Ok(value) => Value::Int(value),
                                    Err(_) => Value::IntegerLiteral {
                                        negative: false,
                                        magnitude,
                                    },
                                }
                            }
                            None => Value::Int(value),
                        };
                        Control::Value(value)
                    }
                    ExprKind::Float(value) => Control::Value(Value::Float(
                        match self.program.numeric_literal(expr.span) {
                            Some(literal) => literal.as_f64(expr.span)?,
                            None => value,
                        },
                    )),
                    ExprKind::Char(value) => Control::Value(Value::Char(value)),
                    ExprKind::Byte(value) => Control::Value(Value::Integer {
                        signed: false,
                        bits: 8,
                        raw: u128::from(value),
                    }),
                    ExprKind::ByteString(ref value) => Control::Value(Value::Bytes(value.clone())),
                    ExprKind::String(value) => Control::Value(Value::String(value.as_ref().into())),
                    ExprKind::Move(operand) => {
                        if let Some((name, fields)) = local_projection(&operand) {
                            let root = locals
                                .find(name.as_ref())
                                .map(|(_, cell)| cell.clone())
                                .ok_or_else(|| {
                                    runtime(expr.span, format!("unknown local place `{name}`"))
                                })?;
                            let moved = assign_cell_projection(
                                &root,
                                &fields,
                                Value::Uninitialized,
                                expr.span,
                            )?;
                            if matches!(moved, Value::Uninitialized) {
                                return Err(runtime(
                                    expr.span,
                                    "cannot move from uninitialized storage",
                                ));
                            }
                            Control::Value(moved)
                        } else if let Some((reference, fields)) = dereference_projection(&operand) {
                            frames.push(EvalFrame::MoveDereference {
                                fields,
                                span: expr.span,
                            });
                            Control::Expr(reference, locals)
                        } else {
                            Control::Expr((*operand).clone(), locals)
                        }
                    }
                    ExprKind::Variable(path) => {
                        let value = if path.len() == 1 {
                            let key = span_key(expr.span);
                            let requested = path[0].as_ref();
                            let cached = self
                                .local_depths
                                .get(&key)
                                .and_then(|depth| locals.get_at(requested, *depth));
                            if let Some(value) = cached {
                                Some(value.borrow().clone())
                            } else if let Some((depth, value)) = locals.find(requested) {
                                let value = value.borrow().clone();
                                self.local_depths.insert(key, depth);
                                Some(value)
                            } else {
                                self.globals.get(requested).cloned().or_else(|| {
                                    self.function_indices
                                        .get(requested)
                                        .copied()
                                        .map(Value::FunctionItem)
                                })
                            }
                        } else if path.len() == 2
                            && self
                                .enum_variants
                                .get(&(path[0].as_ref(), path[1].as_ref()))
                                == Some(&0)
                        {
                            Some(Value::Enum {
                                name: path[0].clone(),
                                variant: path[1].clone(),
                                fields: Rc::new(Vec::new()),
                            })
                        } else if path.len() == 2 {
                            let qualified = format!("{}::{}", path[0], path[1]);
                            self.globals.get(&qualified).cloned()
                        } else {
                            None
                        };
                        let value = value.ok_or_else(|| {
                            let joined = path
                                .iter()
                                .map(|segment| segment.as_ref())
                                .collect::<Vec<_>>()
                                .join("::");
                            runtime(expr.span, format!("unknown value `{joined}`"))
                        })?;
                        if matches!(value, Value::Uninitialized) {
                            return Err(runtime(expr.span, "use of moved or uninitialized local"));
                        }
                        Control::Value(value)
                    }
                    ExprKind::Closure { params, body } => {
                        let capture_names = self.closure_capture_names(expr.span, &params, &body);
                        let captures = locals.select(&capture_names);
                        Control::Value(Value::Closure {
                            params,
                            body,
                            captures,
                        })
                    }
                    // The recovery evaluator is untyped, so an explicitly
                    // typed anonymous callable behaves as its inferred twin:
                    // annotations are enforced by `validate` and the bytecode
                    // path.
                    ExprKind::TypedClosure { params, body, .. } => {
                        let params = params
                            .iter()
                            .map(|param| Rc::<str>::from(param.name.as_str()))
                            .collect::<Rc<[Rc<str>]>>();
                        let capture_names = self.closure_capture_names(expr.span, &params, &body);
                        let captures = locals.select(&capture_names);
                        Control::Value(Value::Closure {
                            params,
                            body,
                            captures,
                        })
                    }
                    ExprKind::List(expressions) | ExprKind::Tuple(expressions) => {
                        if expressions.is_empty() {
                            Control::Value(Value::List(Vector::new()))
                        } else {
                            let first = expressions[0].clone();
                            frames.push(EvalFrame::List {
                                expressions,
                                next: 1,
                                values: Vec::new(),
                                locals: locals.clone(),
                            });
                            Control::Expr(first, locals)
                        }
                    }
                    ExprKind::Struct { name, fields } => {
                        let literal_key = span_key(expr.span);
                        if !self.validated_struct_literals.contains(&literal_key) {
                            let declared = self.structs.get(name.as_ref()).ok_or_else(|| {
                                runtime(expr.span, format!("unknown struct `{name}`"))
                            })?;
                            for (field, value) in fields.iter() {
                                if !declared.contains(field) {
                                    return Err(runtime(
                                        value.span,
                                        format!("struct `{name}` has no field named `{field}`"),
                                    ));
                                }
                            }
                            self.validated_struct_literals.insert(literal_key);
                        }
                        if fields.is_empty() {
                            Control::Value(Value::Struct {
                                name,
                                fields: Rc::new(HashMap::new()),
                            })
                        } else {
                            let first = fields[0].1.clone();
                            frames.push(EvalFrame::Struct {
                                name,
                                fields,
                                next: 1,
                                values: HashMap::new(),
                                locals: locals.clone(),
                                span: expr.span,
                            });
                            Control::Expr(first, locals)
                        }
                    }
                    ExprKind::Field(subject, name) => {
                        frames.push(EvalFrame::Field {
                            name,
                            span: expr.span,
                        });
                        Control::Expr(unwrap_expr(subject), locals)
                    }
                    ExprKind::Block(statements) | ExprKind::ContextBlock(statements) => {
                        if statements.is_empty() {
                            Control::Value(Value::Unit)
                        } else if statements.len() == 1 && matches!(&statements[0], Stmt::Expr(_)) {
                            Control::Expr(statement_expr(&statements[0]).clone(), locals)
                        } else {
                            let first = statement_expr(&statements[0]).clone();
                            frames.push(EvalFrame::Block {
                                statements,
                                index: 0,
                                locals: locals.clone(),
                            });
                            Control::Expr(first, locals)
                        }
                    }
                    ExprKind::Call(callee, arguments) => {
                        if let ExprKind::Variable(else_path) = &callee.kind
                            && else_path.len() == 1
                            && else_path[0].as_ref() == "else"
                            && let [if_expression, negative] = arguments.as_slice()
                            && let ExprKind::Call(if_callee, if_arguments) = &if_expression.kind
                            && let ExprKind::Variable(if_path) = &if_callee.kind
                            && if_path.len() == 1
                            && if_path[0].as_ref() == "if"
                            && let [condition, positive] = if_arguments.as_slice()
                            && let ExprKind::Is { subject, pattern } = &condition.kind
                        {
                            frames.push(EvalFrame::RefinementIf {
                                pattern: pattern.clone(),
                                positive: positive.clone(),
                                negative: negative.clone(),
                                locals: locals.clone(),
                                span: expr.span,
                            });
                            Control::Expr((**subject).clone(), locals)
                        } else {
                            let lexical_callable = match &callee.kind {
                                ExprKind::Variable(path) if path.len() == 1 => locals
                                    .find(path[0].as_ref())
                                    .map(|(_, value)| value.borrow().clone())
                                    .or_else(|| self.globals.get(path[0].as_ref()).cloned()),
                                _ => None,
                            };
                            let call_kind = match &callee.kind {
                                ExprKind::Variable(path) if lexical_callable.is_none() => {
                                    self.resolve_call_kind(&callee, path)
                                }
                                _ => None,
                            };
                            if let Some(kind) = call_kind {
                                self.begin_call_arguments(
                                    CallDesignator::Path { callee, kind },
                                    arguments,
                                    locals,
                                    expr.span,
                                    &mut frames,
                                )?
                            } else if let Some(value) = lexical_callable {
                                self.begin_call_arguments(
                                    CallDesignator::Closure(value),
                                    arguments,
                                    locals,
                                    expr.span,
                                    &mut frames,
                                )?
                            } else {
                                frames.push(EvalFrame::CallCallee {
                                    arguments,
                                    locals: locals.clone(),
                                    span: expr.span,
                                });
                                Control::Expr(unwrap_expr(callee), locals)
                            }
                        }
                    }
                    ExprKind::Perform {
                        effect,
                        operation,
                        args,
                    } => {
                        if args.is_empty() {
                            self.enter_perform(
                                effect,
                                operation,
                                Vec::new(),
                                expr.span,
                                &mut frames,
                            )
                            .inspect_err(|_| debug_abort_stack(&frames))?
                        } else {
                            let first = args[0].clone();
                            frames.push(EvalFrame::PerformArgs {
                                effect,
                                operation,
                                arguments: args,
                                next: 1,
                                values: Vec::new(),
                                locals: locals.clone(),
                                span: expr.span,
                            });
                            Control::Expr(first, locals)
                        }
                    }
                    ExprKind::Handle {
                        computation,
                        clauses,
                    } => {
                        let handler_id = self.next_handler_id;
                        self.next_handler_id += 1;
                        self.handlers.push(HandlerFrame {
                            id: handler_id,
                            clauses,
                            captures: locals.clone(),
                        });
                        frames.push(EvalFrame::HandleExit { handler_id });
                        Control::Expr(unwrap_expr(computation), locals)
                    }
                    ExprKind::Unary { op, operand } => {
                        let operand = unwrap_expr(operand);
                        if matches!(op, UnaryOp::BorrowShared | UnaryOp::BorrowUnique)
                            && let Some((name, fields)) = local_projection(&operand)
                        {
                            let local_root = locals
                                .find(name.as_ref())
                                .map(|(_, cell)| cell.clone())
                                .ok_or_else(|| {
                                    runtime(expr.span, format!("unknown local place `{name}`"))
                                })?;
                            let requested_unique = op == UnaryOp::BorrowUnique;
                            let (root, mut path, source_unique) = match local_root.borrow().clone()
                            {
                                Value::Reference { value, unique } => {
                                    (value, Vec::new(), Some(unique))
                                }
                                Value::ProjectedReference {
                                    root,
                                    fields,
                                    unique,
                                } => (root, fields.as_ref().clone(), Some(unique)),
                                _ => (local_root.clone(), Vec::new(), None),
                            };
                            if requested_unique && source_unique == Some(false) {
                                return Err(runtime(
                                    expr.span,
                                    "cannot create a unique borrow from a shared reference",
                                ));
                            }
                            path.extend(assignment_field_names(&fields));
                            if projected_reference_value(&root, &path).is_none() {
                                return Err(runtime(
                                    expr.span,
                                    "cannot borrow moved, uninitialized, or invalid local place",
                                ));
                            }
                            if path.is_empty() {
                                Control::Value(Value::Reference {
                                    value: root,
                                    unique: requested_unique,
                                })
                            } else {
                                Control::Value(Value::ProjectedReference {
                                    root,
                                    fields: Rc::new(path),
                                    unique: requested_unique,
                                })
                            }
                        } else {
                            match (op, operand.kind) {
                                (
                                    UnaryOp::BorrowShared | UnaryOp::BorrowUnique,
                                    ExprKind::Unary {
                                        op: UnaryOp::Dereference,
                                        operand: reference,
                                    },
                                ) => {
                                    frames.push(EvalFrame::Reborrow {
                                        unique: op == UnaryOp::BorrowUnique,
                                        span: expr.span,
                                    });
                                    Control::Expr(unwrap_expr(reference), locals)
                                }
                                (op, kind) => {
                                    frames.push(EvalFrame::Unary {
                                        op,
                                        span: expr.span,
                                    });
                                    Control::Expr(
                                        Expr {
                                            kind,
                                            span: operand.span,
                                        },
                                        locals,
                                    )
                                }
                            }
                        }
                    }
                    ExprKind::Binary { op, lhs, rhs } => {
                        frames.push(EvalFrame::BinaryLeft {
                            op,
                            rhs: unwrap_expr(rhs),
                            locals: locals.clone(),
                            span: expr.span,
                        });
                        Control::Expr(unwrap_expr(lhs), locals)
                    }
                    ExprKind::Is { subject, pattern } => {
                        frames.push(EvalFrame::Is {
                            pattern,
                            span: expr.span,
                        });
                        Control::Expr(unwrap_expr(subject), locals)
                    }
                    ExprKind::Resume { resumption, value } => {
                        let mut arguments = vec![unwrap_expr(resumption)];
                        arguments.extend(value.map(unwrap_expr));
                        let callee = Rc::new(Expr {
                            kind: ExprKind::Variable(Rc::from([Rc::from("resume")])),
                            span: expr.span,
                        });
                        self.begin_call_arguments(
                            CallDesignator::Path {
                                callee,
                                kind: CallKind::Resume,
                            },
                            Rc::new(arguments),
                            locals,
                            expr.span,
                            &mut frames,
                        )?
                    }
                    ExprKind::TailResume { resumption, value } => {
                        let mut arguments = vec![unwrap_expr(resumption)];
                        arguments.extend(value.map(unwrap_expr));
                        let callee = Rc::new(Expr {
                            kind: ExprKind::Variable(Rc::from([Rc::from("tail")])),
                            span: expr.span,
                        });
                        self.begin_call_arguments(
                            CallDesignator::Path {
                                callee,
                                kind: CallKind::TailResume,
                            },
                            Rc::new(arguments),
                            locals,
                            expr.span,
                            &mut frames,
                        )?
                    }
                    ExprKind::Cancel { resumption } => {
                        let callee = Rc::new(Expr {
                            kind: ExprKind::Variable(Rc::from([Rc::from("cancel")])),
                            span: expr.span,
                        });
                        self.begin_call_arguments(
                            CallDesignator::Path {
                                callee,
                                kind: CallKind::Cancel,
                            },
                            Rc::new(vec![unwrap_expr(resumption)]),
                            locals,
                            expr.span,
                            &mut frames,
                        )?
                    }
                    // Structural forms the pipeline rewrites or `validate`
                    // rejects before evaluation; reaching one here means the
                    // caller skipped those phases.
                    ExprKind::Labeled { .. }
                    | ExprKind::LabelReference(_)
                    | ExprKind::LabelDestination { .. }
                    | ExprKind::Leave { .. } => {
                        return Err(runtime(
                            expr.span,
                            "this syntax is parsed but not yet supported by the recovery evaluator",
                        ));
                    }
                },
                Control::Value(value) => {
                    let Some(frame) = frames.pop() else {
                        return Ok(value);
                    };
                    match frame {
                        EvalFrame::List {
                            expressions,
                            next,
                            mut values,
                            locals,
                        } => {
                            values.push(value);
                            if next == expressions.len() {
                                Control::Value(Value::List(values.into_iter().collect()))
                            } else {
                                let expression = expressions[next].clone();
                                frames.push(EvalFrame::List {
                                    expressions,
                                    next: next + 1,
                                    values,
                                    locals: locals.clone(),
                                });
                                Control::Expr(expression, locals)
                            }
                        }
                        EvalFrame::Struct {
                            name,
                            fields,
                            next,
                            mut values,
                            locals,
                            span,
                        } => {
                            let field_name = fields[next - 1].0.clone();
                            if values.insert(field_name.clone(), value).is_some() {
                                return Err(runtime(
                                    span,
                                    format!("field `{field_name}` is initialized more than once"),
                                ));
                            }
                            if next == fields.len() {
                                Control::Value(Value::Struct {
                                    name,
                                    fields: Rc::new(values),
                                })
                            } else {
                                let expression = fields[next].1.clone();
                                frames.push(EvalFrame::Struct {
                                    name,
                                    fields,
                                    next: next + 1,
                                    values,
                                    locals: locals.clone(),
                                    span,
                                });
                                Control::Expr(expression, locals)
                            }
                        }
                        EvalFrame::Field { name, span } => match value {
                            Value::Struct { fields, .. } => {
                                let selected = fields.get(&name).cloned().ok_or_else(|| {
                                    runtime(span, format!("value has no field named `{name}`"))
                                })?;
                                if matches!(selected, Value::Uninitialized) {
                                    return Err(runtime(
                                        span,
                                        format!(
                                            "field `{name}` has been moved or is uninitialized"
                                        ),
                                    ));
                                }
                                Control::Value(selected)
                            }
                            Value::Reference { value, unique } => {
                                let has_field = matches!(
                                    &*value.borrow(),
                                    Value::Struct { fields, .. } if fields.contains_key(&name)
                                );
                                if !has_field {
                                    return Err(runtime(
                                        span,
                                        format!("value has no field named `{name}`"),
                                    ));
                                }
                                let path = Rc::new(vec![name]);
                                if matches!(
                                    frames.last(),
                                    Some(EvalFrame::Field { .. })
                                        | Some(EvalFrame::Unary {
                                            op: UnaryOp::BorrowShared | UnaryOp::BorrowUnique,
                                            ..
                                        })
                                ) {
                                    Control::Value(Value::ProjectedReference {
                                        root: value,
                                        fields: path,
                                        unique,
                                    })
                                } else {
                                    Control::Value(
                                        projected_reference_value(&value, &path).ok_or_else(
                                            || {
                                                runtime(
                                                    span,
                                                    "projected reference no longer resolves",
                                                )
                                            },
                                        )?,
                                    )
                                }
                            }
                            Value::ProjectedReference {
                                root,
                                fields,
                                unique,
                            } => {
                                let mut path = fields.as_ref().clone();
                                path.push(name.clone());
                                if projected_reference_value(&root, &path).is_none() {
                                    return Err(runtime(
                                        span,
                                        format!("value has no field named `{name}`"),
                                    ));
                                }
                                let path = Rc::new(path);
                                if matches!(
                                    frames.last(),
                                    Some(EvalFrame::Field { .. })
                                        | Some(EvalFrame::Unary {
                                            op: UnaryOp::BorrowShared | UnaryOp::BorrowUnique,
                                            ..
                                        })
                                ) {
                                    Control::Value(Value::ProjectedReference {
                                        root,
                                        fields: path,
                                        unique,
                                    })
                                } else {
                                    Control::Value(
                                        projected_reference_value(&root, &path).ok_or_else(
                                            || {
                                                runtime(
                                                    span,
                                                    "projected reference no longer resolves",
                                                )
                                            },
                                        )?,
                                    )
                                }
                            }
                            Value::Enum { fields, .. } => {
                                let index = name.parse::<usize>().map_err(|_| {
                                    runtime(
                                        span,
                                        "enum payload projection requires a numeric field index",
                                    )
                                })?;
                                let selected = fields.get(index).cloned().ok_or_else(|| {
                                    runtime(
                                        span,
                                        format!(
                                            "active enum variant has no payload field `{index}`"
                                        ),
                                    )
                                })?;
                                if matches!(selected, Value::Uninitialized) {
                                    return Err(runtime(
                                        span,
                                        format!(
                                            "enum payload field `{index}` has been moved or is uninitialized"
                                        ),
                                    ));
                                }
                                Control::Value(selected)
                            }
                            Value::List(values) => {
                                let index = name.parse::<usize>().map_err(|_| {
                                    runtime(span, "tuple projection requires a numeric field index")
                                })?;
                                let selected = values.get(index).cloned().ok_or_else(|| {
                                    runtime(span, format!("tuple has no field `{index}`"))
                                })?;
                                if matches!(selected, Value::Uninitialized) {
                                    return Err(runtime(
                                        span,
                                        format!(
                                            "tuple field `{index}` has been moved or is uninitialized"
                                        ),
                                    ));
                                }
                                Control::Value(selected)
                            }
                            value => {
                                return Err(runtime(
                                    span,
                                    format!(
                                        "field projection requires a struct, received `{value:?}`"
                                    ),
                                ));
                            }
                        },
                        EvalFrame::Block {
                            statements,
                            index,
                            mut locals,
                        } => match &statements[index] {
                            Stmt::Let { name, .. } => {
                                locals.insert(name.clone(), value.clone());
                                self.advance_block(
                                    statements,
                                    index,
                                    locals,
                                    Value::Unit,
                                    &mut frames,
                                )?
                            }
                            statement @ Stmt::Deconstruct { .. } => {
                                bind_deconstruction(statement, &value, &mut locals)?;
                                self.advance_block(
                                    statements,
                                    index,
                                    locals,
                                    Value::Unit,
                                    &mut frames,
                                )?
                            }
                            Stmt::Assign {
                                destination, span, ..
                            } => {
                                let continuation = BlockContinuation {
                                    statements: statements.clone(),
                                    index,
                                    locals: locals.clone(),
                                };
                                match &destination.kind {
                                    AssignmentPlaceKind::Local { name, fields } => {
                                        let root = locals
                                            .find(name.as_ref())
                                            .map(|(_, cell)| cell.clone())
                                            .ok_or_else(|| {
                                                runtime(
                                                    destination.span,
                                                    format!("unknown local place `{name}`"),
                                                )
                                            })?;
                                        self.begin_assignment(
                                            root,
                                            fields.clone(),
                                            value,
                                            *span,
                                            continuation,
                                            &mut frames,
                                        )?
                                    }
                                    AssignmentPlaceKind::Dereference { reference, fields } => {
                                        frames.push(EvalFrame::AssignmentDereference {
                                            replacement: value,
                                            fields: fields.clone(),
                                            span: *span,
                                            continuation,
                                        });
                                        Control::Expr((**reference).clone(), locals)
                                    }
                                }
                            }
                            Stmt::Expr(_) => {
                                self.advance_block(statements, index, locals, value, &mut frames)?
                            }
                        },
                        EvalFrame::AssignmentDereference {
                            replacement,
                            mut fields,
                            span,
                            continuation,
                        } => {
                            let (root, base_fields, unique) = match value {
                                Value::Reference { value, unique } => (value, Vec::new(), unique),
                                Value::ProjectedReference {
                                    root,
                                    fields,
                                    unique,
                                } => (root, fields.as_ref().clone(), unique),
                                value => {
                                    return Err(runtime(
                                        span,
                                        format!(
                                            "assignment dereference requires a reference, received `{value:?}`"
                                        ),
                                    ));
                                }
                            };
                            if !unique {
                                return Err(runtime(
                                    span,
                                    "assignment dereference requires a unique reference",
                                ));
                            }
                            let mut combined = base_fields
                                .into_iter()
                                .map(|name| AssignmentField { name, span })
                                .collect::<Vec<_>>();
                            combined.append(&mut fields);
                            self.begin_assignment(
                                root,
                                combined,
                                replacement,
                                span,
                                continuation,
                                &mut frames,
                            )?
                        }
                        EvalFrame::AssignmentStoreAfterDestroy {
                            root,
                            fields,
                            replacement,
                            span,
                            continuation,
                        } => {
                            if value != Value::Unit {
                                return Err(runtime(
                                    span,
                                    "assignment destruction must return unit",
                                ));
                            }
                            let resident =
                                assign_cell_projection(&root, &fields, replacement, span)?;
                            if !matches!(resident, Value::Uninitialized) {
                                return Err(runtime(
                                    span,
                                    "assignment destination changed while old value was destroyed",
                                ));
                            }
                            self.advance_block(
                                continuation.statements,
                                continuation.index,
                                continuation.locals,
                                Value::Unit,
                                &mut frames,
                            )?
                        }
                        EvalFrame::MoveDereference { mut fields, span } => {
                            let (root, base_fields, unique) = match value {
                                Value::Reference { value, unique } => (value, Vec::new(), unique),
                                Value::ProjectedReference {
                                    root,
                                    fields,
                                    unique,
                                } => (root, fields.as_ref().clone(), unique),
                                value => {
                                    return Err(runtime(
                                        span,
                                        format!(
                                            "move dereference requires a reference, received `{value:?}`"
                                        ),
                                    ));
                                }
                            };
                            if !unique {
                                return Err(runtime(
                                    span,
                                    "move dereference requires a unique reference",
                                ));
                            }
                            let mut combined = base_fields
                                .into_iter()
                                .map(|name| AssignmentField { name, span })
                                .collect::<Vec<_>>();
                            combined.append(&mut fields);
                            let moved = assign_cell_projection(
                                &root,
                                &combined,
                                Value::Uninitialized,
                                span,
                            )?;
                            if matches!(moved, Value::Uninitialized) {
                                return Err(runtime(
                                    span,
                                    "cannot move from uninitialized storage",
                                ));
                            }
                            Control::Value(moved)
                        }
                        EvalFrame::CallCallee {
                            arguments,
                            locals,
                            span,
                        } => self.begin_call_arguments(
                            CallDesignator::Closure(value),
                            arguments,
                            locals,
                            span,
                            &mut frames,
                        )?,
                        EvalFrame::CallArgs(PendingCallArguments {
                            callee,
                            arguments,
                            next,
                            mut values,
                            locals,
                            span,
                        }) => {
                            values.push(value);
                            if next == arguments.len() {
                                self.enter_call(callee, values, span, &mut frames)?
                            } else {
                                self.continue_call_arguments(
                                    PendingCallArguments {
                                        callee,
                                        arguments,
                                        next,
                                        values,
                                        locals,
                                        span,
                                    },
                                    &mut frames,
                                )?
                            }
                        }
                        EvalFrame::MemoizeDeclarationLookup { key } => {
                            self.declaration_lookup_cache.insert(key, value.clone());
                            Control::Value(value)
                        }
                        EvalFrame::FunctionReturn {
                            integer_kind,
                            float_kind,
                            span,
                        } => Control::Value(if let Some(kind) = integer_kind {
                            coerce_integer(value, kind, span)?
                        } else if let Some(kind) = float_kind {
                            coerce_declared_float(value, kind, span)?
                        } else {
                            value
                        }),
                        EvalFrame::GenericEnvironment { previous } => {
                            self.generic_witnesses = previous;
                            Control::Value(value)
                        }
                        EvalFrame::PerformArgs {
                            effect,
                            operation,
                            arguments,
                            next,
                            mut values,
                            locals,
                            span,
                        } => {
                            values.push(value);
                            if next == arguments.len() {
                                self.enter_perform(effect, operation, values, span, &mut frames)
                                    .inspect_err(|_| debug_abort_stack(&frames))?
                            } else {
                                let expression = arguments[next].clone();
                                frames.push(EvalFrame::PerformArgs {
                                    effect,
                                    operation,
                                    arguments,
                                    next: next + 1,
                                    values,
                                    locals: locals.clone(),
                                    span,
                                });
                                Control::Expr(expression, locals)
                            }
                        }
                        EvalFrame::HandleExit { handler_id } => {
                            if self
                                .handlers
                                .last()
                                .is_some_and(|frame| frame.id == handler_id)
                            {
                                self.handlers.pop();
                            }
                            Control::Value(value)
                        }
                        EvalFrame::HandlerDelimiter { .. } => Control::Value(value),
                        EvalFrame::ResumptionBoundary {
                            return_frames,
                            return_handlers,
                        } => {
                            frames = return_frames;
                            self.handlers = return_handlers;
                            Control::Value(value)
                        }
                        EvalFrame::Unary { op, span } => match (op, value) {
                            (UnaryOp::Negate, Value::Int(value)) => Control::Value(Value::Int(
                                value
                                    .checked_neg()
                                    .ok_or_else(|| runtime(span, "integer negation overflowed"))?,
                            )),
                            (
                                UnaryOp::Negate,
                                Value::IntegerLiteral {
                                    negative: false,
                                    magnitude,
                                },
                            ) => Control::Value(Value::IntegerLiteral {
                                negative: true,
                                magnitude,
                            }),
                            (UnaryOp::BorrowShared, Value::Reference { value, .. }) => {
                                Control::Value(Value::Reference {
                                    value,
                                    unique: false,
                                })
                            }
                            (
                                UnaryOp::BorrowUnique,
                                Value::Reference {
                                    value,
                                    unique: true,
                                },
                            ) => Control::Value(Value::Reference {
                                value,
                                unique: true,
                            }),
                            (
                                UnaryOp::BorrowShared,
                                Value::ProjectedReference { root, fields, .. },
                            ) => Control::Value(Value::ProjectedReference {
                                root,
                                fields,
                                unique: false,
                            }),
                            (
                                UnaryOp::BorrowUnique,
                                Value::ProjectedReference {
                                    root,
                                    fields,
                                    unique: true,
                                },
                            ) => Control::Value(Value::ProjectedReference {
                                root,
                                fields,
                                unique: true,
                            }),
                            (UnaryOp::BorrowUnique, Value::Reference { .. })
                            | (UnaryOp::BorrowUnique, Value::ProjectedReference { .. }) => {
                                return Err(runtime(
                                    span,
                                    "cannot create a unique borrow from a shared reference",
                                ));
                            }
                            (UnaryOp::BorrowShared, value) => Control::Value(Value::Reference {
                                value: Rc::new(RefCell::new(value)),
                                unique: false,
                            }),
                            (UnaryOp::BorrowUnique, value) => Control::Value(Value::Reference {
                                value: Rc::new(RefCell::new(value)),
                                unique: true,
                            }),
                            (UnaryOp::Dereference, Value::Reference { value, .. }) => {
                                Control::Value(value.borrow().clone())
                            }
                            (
                                UnaryOp::Dereference,
                                Value::ProjectedReference { root, fields, .. },
                            ) => Control::Value(
                                projected_reference_value(&root, &fields).ok_or_else(|| {
                                    runtime(span, "projected reference no longer resolves")
                                })?,
                            ),
                            (operator, value) => {
                                return Err(runtime(
                                    span,
                                    format!("operator {operator:?} does not accept `{value:?}`"),
                                ));
                            }
                        },
                        EvalFrame::Reborrow { unique, span } => match value {
                            Value::Reference {
                                value,
                                unique: source_is_unique,
                            } if source_is_unique || !unique => {
                                Control::Value(Value::Reference { value, unique })
                            }
                            Value::Reference { .. } => {
                                return Err(runtime(
                                    span,
                                    "cannot create a unique reborrow from a shared reference",
                                ));
                            }
                            Value::ProjectedReference {
                                root,
                                fields,
                                unique: source_is_unique,
                            } if source_is_unique || !unique => {
                                Control::Value(Value::ProjectedReference {
                                    root,
                                    fields,
                                    unique,
                                })
                            }
                            Value::ProjectedReference { .. } => {
                                return Err(runtime(
                                    span,
                                    "cannot create a unique reborrow from a shared reference",
                                ));
                            }
                            value => {
                                return Err(runtime(
                                    span,
                                    format!("cannot reborrow non-reference value `{value:?}`"),
                                ));
                            }
                        },
                        EvalFrame::DropStructural {
                            value: dropped,
                            span,
                        } => {
                            if value != Value::Unit {
                                return Err(runtime(span, "Drop::drop must return unit"));
                            }
                            self.begin_structural_destroy(dropped, span, &mut frames)?
                        }
                        EvalFrame::DestroyRemaining { mut values, span } => {
                            if let Some(next) = values.pop() {
                                frames.push(EvalFrame::DestroyRemaining { values, span });
                                self.begin_destroy(next, span, &mut frames)?
                            } else {
                                Control::Value(Value::Unit)
                            }
                        }
                        EvalFrame::BinaryLeft {
                            op,
                            rhs,
                            locals,
                            span,
                        } => {
                            frames.push(EvalFrame::BinaryRight {
                                op,
                                lhs: value,
                                span,
                            });
                            Control::Expr(rhs, locals)
                        }
                        EvalFrame::BinaryRight { op, lhs, span } => {
                            Control::Value(binary(op, lhs, value, span)?)
                        }
                        EvalFrame::Is { pattern, .. } => {
                            // Matching only reads/clones the subject. Binder
                            // values are deliberately not installed in the
                            // surrounding lexical environment; they belong to
                            // a positive refinement branch, which compiled
                            // lowering represents explicitly.
                            let mut bindings = HashMap::new();
                            let matched =
                                match_pattern(self.program, &pattern, &value, &mut bindings);
                            Control::Value(truth(matched))
                        }
                        EvalFrame::RefinementIf {
                            pattern,
                            positive,
                            negative,
                            mut locals,
                            ..
                        } => {
                            let mut bindings = HashMap::new();
                            if match_pattern(self.program, &pattern, &value, &mut bindings) {
                                for (name, value) in bindings {
                                    locals.insert(name, value);
                                }
                                Control::Expr(positive, locals)
                            } else {
                                Control::Expr(negative, locals)
                            }
                        }
                    }
                }
            };
        }
    }

    fn advance_block(
        &mut self,
        statements: Rc<Vec<Stmt>>,
        index: usize,
        locals: Locals,
        result: Value,
        frames: &mut Vec<EvalFrame>,
    ) -> Result<Control, Diagnostic> {
        let next = index + 1;
        if next == statements.len() {
            return Ok(Control::Value(result));
        }
        let expression = statement_expr(&statements[next]).clone();
        if !matches!(&statements[next], Stmt::Expr(_)) || next + 1 != statements.len() {
            frames.push(EvalFrame::Block {
                statements,
                index: next,
                locals: locals.clone(),
            });
        }
        Ok(Control::Expr(expression, locals))
    }

    fn begin_assignment(
        &mut self,
        root: Rc<RefCell<Value>>,
        fields: Vec<AssignmentField>,
        replacement: Value,
        span: Span,
        continuation: BlockContinuation,
        frames: &mut Vec<EvalFrame>,
    ) -> Result<Control, Diagnostic> {
        let old = assign_cell_projection(&root, &fields, Value::Uninitialized, span)?;
        if matches!(old, Value::Uninitialized) {
            let resident = assign_cell_projection(&root, &fields, replacement, span)?;
            debug_assert!(matches!(resident, Value::Uninitialized));
            return self.advance_block(
                continuation.statements,
                continuation.index,
                continuation.locals,
                Value::Unit,
                frames,
            );
        }
        frames.push(EvalFrame::AssignmentStoreAfterDestroy {
            root,
            fields,
            replacement,
            span,
            continuation,
        });
        self.begin_destroy(old, span, frames)
    }

    fn resolve_call_kind(&mut self, callee: &Expr, path: &[Rc<str>]) -> Option<CallKind> {
        let key = span_key(callee.span);
        if let Some(kind) = self.call_kinds.get(&key) {
            return Some(*kind);
        }
        let kind = if path.len() == 1 {
            match path[0].as_ref() {
                "destroy" => Some(CallKind::Destroy),
                name => name
                    .strip_prefix("$trait_deferred$")
                    .and_then(|deferred| deferred.split_once('$'))
                    .and_then(|(trait_name, method)| {
                        self.trait_method_indices
                            .get(&(trait_name, method))
                            .copied()
                            .map(CallKind::TraitMethodGroup)
                    })
                    .or_else(|| {
                        self.function_indices
                            .get(name)
                            .copied()
                            .map(CallKind::Function)
                    }),
            }
        } else if path.len() == 2 && path[0].as_ref() == "core" {
            Some(CallKind::Intrinsic(intrinsic_kind(path[1].as_ref())))
        } else if path.len() == 2 {
            self.enum_variants
                .get(&(path[0].as_ref(), path[1].as_ref()))
                .copied()
                .map(CallKind::EnumConstructor)
                .or_else(|| {
                    self.trait_method_indices
                        .get(&(path[0].as_ref(), path[1].as_ref()))
                        .copied()
                        .map(CallKind::TraitMethodGroup)
                })
        } else {
            None
        };
        if let Some(kind) = kind {
            self.call_kinds.insert(key, kind);
        }
        kind
    }

    fn begin_call_arguments(
        &mut self,
        callee: CallDesignator,
        arguments: Rc<Vec<Expr>>,
        locals: Locals,
        span: Span,
        frames: &mut Vec<EvalFrame>,
    ) -> Result<Control, Diagnostic> {
        if arguments.is_empty() {
            self.enter_call(callee, Vec::new(), span, frames)
        } else {
            self.continue_call_arguments(
                PendingCallArguments {
                    callee,
                    arguments,
                    next: 0,
                    values: Vec::new(),
                    locals,
                    span,
                },
                frames,
            )
        }
    }

    fn continue_call_arguments(
        &mut self,
        pending: PendingCallArguments,
        frames: &mut Vec<EvalFrame>,
    ) -> Result<Control, Diagnostic> {
        let PendingCallArguments {
            callee,
            arguments,
            next,
            values,
            locals,
            span,
        } = pending;
        let argument = arguments[next].clone();
        // Bootstrap compatibility only: the evaluator derives contextual-block
        // thunking from the selected declaration interface. The shared parser
        // deliberately carries no callable/laziness classification.
        let expects_callable = match &callee {
            CallDesignator::Path {
                kind: CallKind::Function(function),
                ..
            } => self.functions.get(*function).is_some_and(|function| {
                let Some(parameter_type) = function
                    .declaration
                    .params
                    .get(next)
                    .and_then(|param| param.ty.simple_name())
                else {
                    return false;
                };
                function
                    .declaration
                    .where_clause
                    .iter()
                    .flat_map(|clause| &clause.goals)
                    .any(|goal| {
                        goal.subject.simple_name() == Some(parameter_type)
                            && goal.relation.path.len() == 1
                            && goal.relation.path[0].name == "Fn"
                    })
            }),
            _ => false,
        };
        frames.push(EvalFrame::CallArgs(PendingCallArguments {
            callee,
            arguments,
            next: next + 1,
            values,
            locals: locals.clone(),
            span,
        }));
        if expects_callable && matches!(&argument.kind, ExprKind::Block(_)) {
            Ok(Control::Value(Value::Closure {
                params: Rc::from([]),
                body: Rc::new(argument),
                captures: locals,
            }))
        } else {
            Ok(Control::Expr(argument, locals))
        }
    }

    fn enter_call(
        &mut self,
        callee: CallDesignator,
        args: Vec<Value>,
        span: Span,
        frames: &mut Vec<EvalFrame>,
    ) -> Result<Control, Diagnostic> {
        match callee {
            CallDesignator::Path { callee, kind } => {
                let ExprKind::Variable(path) = &callee.kind else {
                    return Err(runtime(span, "callable path invariant violated"));
                };
                let name = self.call_name(&callee, path);
                if matches!(kind, CallKind::Resume | CallKind::TailResume) {
                    let [Value::Resumption(resumption), value] = args.as_slice() else {
                        return Err(runtime(
                            span,
                            if matches!(kind, CallKind::TailResume) {
                                "`tail` expects a resumption and one operation-result value"
                            } else {
                                "`resume` expects a resumption and one operation-result value"
                            },
                        ));
                    };
                    let captured = {
                        let mut state = resumption.state.borrow_mut();
                        if matches!(kind, CallKind::TailResume) && state.upper != Some(1) {
                            return Err(runtime(
                                span,
                                "`tail` requires an optional or exact one-shot resumption",
                            ));
                        }
                        if state.closed || state.upper.is_some_and(|upper| state.uses >= upper) {
                            return Err(runtime(
                                span,
                                "this resumption has exhausted its declared upper bound",
                            )
                            .with_help("do not resume a continuation more often than its operation permits"));
                        }
                        state.uses += 1;
                        if state.upper == Some(state.uses) {
                            state.closed = true;
                        }
                        state.continuation.snapshot()
                    };
                    let return_frames = std::mem::take(frames);
                    let return_handlers = std::mem::replace(&mut self.handlers, captured.handlers);
                    frames.push(EvalFrame::ResumptionBoundary {
                        return_frames,
                        return_handlers,
                    });
                    frames.push(EvalFrame::HandlerDelimiter {
                        handler_id: captured.handler_id,
                    });
                    frames.extend(captured.frames);
                    return Ok(Control::Value(value.clone()));
                }
                if matches!(kind, CallKind::Cancel) {
                    let [Value::Resumption(resumption)] = args.as_slice() else {
                        return Err(runtime(span, "`cancel` expects exactly one resumption"));
                    };
                    let mut state = resumption.state.borrow_mut();
                    if state.closed {
                        return Err(runtime(span, "this resumption has already been consumed"));
                    }
                    if state.uses < state.lower {
                        return Err(runtime(
                            span,
                            "this resumption has not met its declared lower bound",
                        )
                        .with_help("resume it enough times before cancellation, or declare a zero lower bound"));
                    }
                    state.closed = true;
                    return Ok(Control::Value(Value::Unit));
                }
                if matches!(kind, CallKind::Destroy) {
                    let [value] = args.as_slice() else {
                        return Err(runtime(span, "`destroy` expects exactly one value"));
                    };
                    return self.begin_destroy(value.clone(), span, frames);
                }
                if let CallKind::Intrinsic(intrinsic_kind) = kind {
                    return intrinsic(intrinsic_kind, name.as_ref(), &args, span)
                        .map(Control::Value);
                }
                if let CallKind::EnumConstructor(arity) = kind {
                    if arity != args.len() {
                        return Err(runtime(
                            span,
                            format!(
                                "variant `{name}` expects {arity} field(s), but received {}",
                                args.len()
                            ),
                        ));
                    }
                    return Ok(Control::Value(Value::Enum {
                        name: path[0].clone(),
                        variant: path[1].clone(),
                        fields: Rc::new(args),
                    }));
                }
                if let CallKind::TraitMethodGroup(group) = kind {
                    let matches = self
                        .trait_method_groups
                        .get(group)
                        .into_iter()
                        .flatten()
                        .filter(|index| {
                            let candidate = &self.trait_methods[**index];
                            if let Some(receiver) = args.first() {
                                self.value_matches_type(receiver, candidate.self_ty, 0)
                            } else {
                                candidate.method.params.is_empty()
                                    && self.generic_witnesses.values().any(|witness| {
                                        self.value_matches_type(witness, candidate.self_ty, 0)
                                    })
                            }
                        })
                        .copied()
                        .collect::<Vec<_>>();
                    let [method_index] = matches.as_slice() else {
                        return Err(runtime(
                            span,
                            if matches.is_empty() {
                                if args.is_empty() {
                                    format!(
                                        "no implementation of receiverless trait method `{name}` matches the active generic type evidence"
                                    )
                                } else {
                                    format!(
                                        "no implementation of trait method `{name}` matches the runtime receiver"
                                    )
                                }
                            } else {
                                format!(
                                    "trait method `{name}` is ambiguous for the runtime type evidence"
                                )
                            },
                        ));
                    };
                    let method = &self.trait_methods[*method_index].method;
                    if method.params.len() != args.len() {
                        return Err(runtime(
                            span,
                            format!(
                                "trait method `{name}` expects {} argument(s), but received {}",
                                method.params.len(),
                                args.len()
                            ),
                        ));
                    }
                    let body = method
                        .body
                        .clone()
                        .expect("runtime trait method has a body");
                    let params = method
                        .params
                        .iter()
                        .map(|parameter| parameter.name.clone())
                        .collect::<Vec<_>>();
                    let return_kind = method.return_type.as_ref().and_then(integer_kind);
                    let return_float_kind = method.return_type.as_ref().and_then(float_kind);
                    let mut args = args;
                    for (argument, parameter) in args.iter_mut().zip(&method.params) {
                        let value = std::mem::replace(argument, Value::Unit);
                        *argument = if let Some(kind) = integer_kind(&parameter.ty) {
                            coerce_declared_integer(value, kind, parameter.span)?
                        } else if let Some(kind) = float_kind(&parameter.ty) {
                            coerce_declared_float(value, kind, parameter.span)?
                        } else {
                            value
                        };
                    }
                    let mut locals = Locals::new();
                    for (parameter, argument) in params.into_iter().zip(args) {
                        locals.insert(parameter, argument);
                    }
                    if (return_kind.is_some() || return_float_kind.is_some())
                        && !matches!(frames.last(), Some(EvalFrame::FunctionReturn { .. }))
                    {
                        frames.push(EvalFrame::FunctionReturn {
                            integer_kind: return_kind,
                            float_kind: return_float_kind,
                            span,
                        });
                    }
                    return Ok(Control::Expr(body, locals));
                }
                let CallKind::Function(function_index) = kind else {
                    unreachable!("all non-function call kinds returned above")
                };
                if self.bootstrap_fast_paths
                    && let Some(result) =
                        self.enter_bootstrap_pure_function(name.as_ref(), &args, span)
                {
                    return result.map(Control::Value);
                }
                self.function_call_counts[function_index] =
                    self.function_call_counts[function_index].wrapping_add(1);
                self.current_function = Some(function_index);
                let parameter_count = self
                    .functions
                    .get(function_index)
                    .ok_or_else(|| runtime(span, format!("unknown callable `{name}`")))?
                    .declaration
                    .params
                    .len();
                if args.len() != parameter_count {
                    return Err(runtime(
                        span,
                        format!(
                            "`{name}` expects {} argument(s), but received {}",
                            parameter_count,
                            args.len()
                        ),
                    ));
                }
                if let Some(leaf) = self.runtime_leaves.leaf(function_index) {
                    if matches!(
                        leaf,
                        RuntimeLeaf::Primitive(_)
                            | RuntimeLeaf::IntegerConversion { .. }
                            | RuntimeLeaf::FloatPrimitive(_)
                            | RuntimeLeaf::Abort
                    ) && !self.runtime_leaves.authorizes_call(span)
                    {
                        return Err(runtime(
                            span,
                            "manifest-bound runtime primitive leaves may be called only from their trusted standard-library source segment",
                        ));
                    }
                    let value = match leaf {
                        RuntimeLeaf::Primitive(primitive) => {
                            eval_runtime_primitive(primitive, &args, span)?
                        }
                        RuntimeLeaf::IntegerConversion { primitive, target } => {
                            eval_runtime_integer_conversion(primitive, target, &args, span)?
                        }
                        RuntimeLeaf::FloatPrimitive(leaf) => {
                            eval_runtime_float_primitive(leaf, &args, span)?
                        }
                        RuntimeLeaf::HostImport(role) => self.eval_host_import(role, args, span)?,
                        RuntimeLeaf::Abort => {
                            return Err(runtime(span, "explicit source abort"));
                        }
                    };
                    return Ok(Control::Value(value));
                }
                if let Some(key) = self.declaration_lookup_key(function_index, name.as_ref(), &args)
                {
                    if let Some(value) = self.declaration_lookup_cache.get(&key).cloned() {
                        self.declaration_lookup_hits = self.declaration_lookup_hits.wrapping_add(1);
                        return Ok(Control::Value(value));
                    }
                    self.declaration_lookup_misses = self.declaration_lookup_misses.wrapping_add(1);
                    frames.push(EvalFrame::MemoizeDeclarationLookup { key });
                }
                let function = self
                    .functions
                    .get(function_index)
                    .expect("validated function index");
                let generic_names = function
                    .declaration
                    .generics
                    .as_ref()
                    .map(|generics| {
                        generics
                            .params
                            .iter()
                            .map(|parameter| parameter.name.as_str())
                            .collect::<HashSet<_>>()
                    })
                    .unwrap_or_default();
                let mut inferred_witnesses = HashMap::new();
                for (parameter, argument) in function.declaration.params.iter().zip(&args) {
                    infer_generic_witnesses(
                        &parameter.ty,
                        argument,
                        &generic_names,
                        &mut inferred_witnesses,
                    );
                }
                let parameter_kinds = function
                    .declaration
                    .params
                    .iter()
                    .map(|parameter| integer_kind(&parameter.ty))
                    .collect::<Vec<_>>();
                let parameter_float_kinds = function
                    .declaration
                    .params
                    .iter()
                    .map(|parameter| float_kind(&parameter.ty))
                    .collect::<Vec<_>>();
                let return_kind = function
                    .declaration
                    .return_type
                    .as_ref()
                    .and_then(integer_kind);
                let return_float_kind = function
                    .declaration
                    .return_type
                    .as_ref()
                    .and_then(float_kind);
                let mut args = args;
                for (((argument, kind), float_kind), parameter) in args
                    .iter_mut()
                    .zip(parameter_kinds)
                    .zip(parameter_float_kinds)
                    .zip(&function.declaration.params)
                {
                    if let Some(kind) = kind {
                        *argument = coerce_declared_integer(
                            std::mem::replace(argument, Value::Unit),
                            kind,
                            parameter.span,
                        )?;
                    } else if let Some(kind) = float_kind {
                        *argument = coerce_declared_float(
                            std::mem::replace(argument, Value::Unit),
                            kind,
                            parameter.span,
                        )?;
                    }
                }
                let mut locals = Locals::new();
                for (parameter_name, argument) in function.parameter_names.iter().cloned().zip(args)
                {
                    locals.insert(parameter_name, argument);
                }
                if !inferred_witnesses.is_empty() {
                    let changes_type = inferred_witnesses.iter().any(|(name, witness)| {
                        self.generic_witnesses
                            .get(name)
                            .is_none_or(|active| !same_runtime_witness_type(active, witness))
                    });
                    if changes_type {
                        let mut next = self.generic_witnesses.clone();
                        next.extend(inferred_witnesses);
                        let previous = std::mem::replace(&mut self.generic_witnesses, next);
                        frames.push(EvalFrame::GenericEnvironment { previous });
                    }
                }
                // A caller's integer-return coercion also covers a statically
                // valid tail call, so do not retain one frame per recursive
                // call. This preserves the recovery evaluator's constant-space
                // tail-call behavior.
                if (return_kind.is_some() || return_float_kind.is_some())
                    && !matches!(frames.last(), Some(EvalFrame::FunctionReturn { .. }))
                {
                    frames.push(EvalFrame::FunctionReturn {
                        integer_kind: return_kind,
                        float_kind: return_float_kind,
                        span,
                    });
                }
                Ok(Control::Expr(function.declaration.body.clone(), locals))
            }
            CallDesignator::Closure(Value::Closure {
                params,
                body,
                captures,
            }) => {
                if args.len() != params.len() {
                    return Err(runtime(
                        span,
                        format!(
                            "closure expects {} argument(s), but received {}",
                            params.len(),
                            args.len()
                        ),
                    ));
                }
                let mut locals = captures;
                locals.extend(params.iter().cloned().zip(args));
                let body = Rc::try_unwrap(body).unwrap_or_else(|shared| (*shared).clone());
                Ok(Control::Expr(body, locals))
            }
            CallDesignator::Closure(Value::FunctionItem(function_index)) => {
                let name: Rc<str> = self
                    .functions
                    .get(function_index)
                    .ok_or_else(|| runtime(span, "unknown function item"))?
                    .declaration
                    .name
                    .as_str()
                    .into();
                let callee = Rc::new(Expr {
                    kind: ExprKind::Variable(Rc::from([name])),
                    span,
                });
                self.enter_call(
                    CallDesignator::Path {
                        callee,
                        kind: CallKind::Function(function_index),
                    },
                    args,
                    span,
                    frames,
                )
            }
            CallDesignator::Closure(value) => {
                Err(runtime(span, format!("`{value:?}` is not callable")))
            }
        }
    }

    fn value_matches_type(&self, value: &Value, ty: &TypeSyntax, depth: usize) -> bool {
        if depth > 32 {
            return false;
        }
        if !matches!(
            ty.kind,
            TypeSyntaxKind::SharedReference { referent: _, .. }
                | TypeSyntaxKind::UniqueReference { referent: _, .. }
        ) {
            match value {
                Value::Reference { value, .. } => {
                    return self.value_matches_type(&value.borrow(), ty, depth + 1);
                }
                Value::ProjectedReference { root, fields, .. } => {
                    return projected_reference_value(root, fields)
                        .is_some_and(|value| self.value_matches_type(&value, ty, depth + 1));
                }
                _ => {}
            }
        }
        match (&ty.kind, value) {
            (TypeSyntaxKind::SharedReference { referent, .. }, Value::Reference { value, .. })
            | (TypeSyntaxKind::UniqueReference { referent, .. }, Value::Reference { value, .. }) => {
                self.value_matches_type(&value.borrow(), referent, depth + 1)
            }
            (
                TypeSyntaxKind::SharedReference { referent, .. }
                | TypeSyntaxKind::UniqueReference { referent, .. },
                Value::ProjectedReference { root, fields, .. },
            ) => projected_reference_value(root, fields)
                .is_some_and(|value| self.value_matches_type(&value, referent, depth + 1)),
            (
                TypeSyntaxKind::SharedReference { referent, .. }
                | TypeSyntaxKind::UniqueReference { referent, .. },
                value,
            ) => self.value_matches_type(value, referent, depth + 1),
            (TypeSyntaxKind::Application { constructor, .. }, value) => {
                self.value_matches_type(value, constructor, depth + 1)
            }
            (TypeSyntaxKind::Path(path), value) if path.len() == 1 => {
                let name = path[0].name.as_str();
                if let Some(target) = self.type_aliases.get(name) {
                    return self.value_matches_type(value, target, depth + 1);
                }
                match value {
                    Value::Unit => name == "Unit",
                    Value::Int(_) => name == "i64",
                    Value::Integer { signed, bits, .. } => match (*signed, *bits) {
                        (true, 8) => name == "i8",
                        (true, 16) => name == "i16",
                        (true, 32) => name == "i32",
                        (true, 64) => name == "i64" || name == "isize",
                        (true, 128) => name == "i128",
                        (false, 8) => name == "u8",
                        (false, 16) => name == "u16",
                        (false, 32) => name == "u32",
                        (false, 64) => name == "u64" || name == "usize",
                        (false, 128) => name == "u128",
                        _ => false,
                    },
                    Value::Float(_) => name == "f64",
                    Value::Float32(_) => name == "f32",
                    Value::Char(_) => name == "Char",
                    Value::String(_) => name == "Text",
                    Value::Bytes(_) => name == "Bytes",
                    Value::Struct { name: actual, .. } | Value::Enum { name: actual, .. } => {
                        actual.as_ref() == name
                    }
                    _ => false,
                }
            }
            _ => false,
        }
    }

    fn eval_host_import(
        &mut self,
        role: HostImportRole,
        args: Vec<Value>,
        span: Span,
    ) -> Result<Value, Diagnostic> {
        match role {
            HostImportRole::ProcessArgsGet => {
                if !args.is_empty() {
                    return Err(runtime(span, "`process.args/get` expects no arguments"));
                }
                let slots = self
                    .invocation_args
                    .iter()
                    .map(|argument| {
                        Some(Rc::new(RefCell::new(Value::String(
                            argument.as_str().into(),
                        ))))
                    })
                    .collect::<Vec<_>>();
                let logical_capacity = slots.len();
                Ok(Value::Array(ArrayRef(Rc::new(RefCell::new(
                    InterpreterArray {
                        slots,
                        logical_capacity,
                    },
                )))))
            }
            HostImportRole::FsRead => self.host.perform("fs.read", "read", args, span),
            HostImportRole::FsWrite => self.host.perform("fs.write", "write", args, span),
            HostImportRole::DiagnosticWrite => self.host.perform("diagnostic", "write", args, span),
        }
    }

    fn declaration_lookup_key(
        &mut self,
        function: usize,
        name: &str,
        args: &[Value],
    ) -> Option<DeclarationLookupKey> {
        if !self.bootstrap_fast_paths
            || !matches!(
                name,
                "lookup_callable"
                    | "lookup_global"
                    | "lookup_type_alias"
                    | "lookup_struct"
                    | "lookup_enum"
                    | "lookup_effect"
                    | "lookup_variant"
                    | "lookup_struct_field"
            )
            || !matches!(args.last(), Some(Value::Int(0)))
        {
            return None;
        }
        let Value::List(values) = args.first()? else {
            return None;
        };
        if values.is_inline() {
            return None;
        }
        let list = self
            .declaration_lookup_lists
            .iter()
            .position(|candidate| candidate.ptr_eq(values))
            .unwrap_or_else(|| {
                let index = self.declaration_lookup_lists.len();
                self.declaration_lookup_lists.push(values.clone());
                index
            });
        let arguments = args[1..]
            .iter()
            .map(|argument| match argument {
                Value::Unit => Some(DeclarationLookupArgument::Unit),
                Value::Int(value) => Some(DeclarationLookupArgument::Int(*value)),
                Value::String(value) => {
                    Some(DeclarationLookupArgument::String(value.0.content_hash()))
                }
                _ => None,
            })
            .collect::<Option<Vec<_>>>()?;
        Some(DeclarationLookupKey {
            function,
            list,
            arguments,
        })
    }

    fn enter_bootstrap_pure_function(
        &self,
        name: &str,
        args: &[Value],
        span: Span,
    ) -> Option<Result<Value, Diagnostic>> {
        match (name, args) {
            ("lex", [source]) => Some(bootstrap_lex(source, span)),
            (
                "lookup_parameter",
                [
                    Value::List(parameters),
                    Value::String(requested),
                    Value::Int(index),
                ],
            ) => {
                let start = match usize::try_from(*index) {
                    Ok(index) => index,
                    Err(_) => return Some(Err(runtime(span, "list index cannot be negative"))),
                };
                for candidate in parameters.iter().skip(start) {
                    let Value::Struct { fields, .. } = candidate else {
                        return Some(Err(runtime(
                            span,
                            "bootstrap parameter lookup encountered a non-struct value",
                        )));
                    };
                    let Some(Value::String(candidate_name)) = fields.get("name") else {
                        return Some(Err(runtime(
                            span,
                            "bootstrap parameter lookup encountered a value without a string name",
                        )));
                    };
                    if candidate_name == requested {
                        return Some(Ok(Value::Enum {
                            name: Rc::from("ParameterLookup"),
                            variant: Rc::from("Found"),
                            fields: Rc::new(vec![candidate.clone()]),
                        }));
                    }
                }
                Some(Ok(Value::Enum {
                    name: Rc::from("ParameterLookup"),
                    variant: Rc::from("Missing"),
                    fields: Rc::new(Vec::new()),
                }))
            }
            (
                "variant_payload_offset",
                [
                    Value::List(variants),
                    Value::Int(target),
                    Value::Int(index),
                    Value::Int(initial_offset),
                ],
            ) => {
                let mut index = *index;
                let mut offset = *initial_offset;
                while index < *target {
                    let Some(Value::Struct { fields, .. }) = usize::try_from(index)
                        .ok()
                        .and_then(|index| variants.get(index))
                    else {
                        return Some(Err(runtime(
                            span,
                            "bootstrap variant payload offset encountered an invalid variant index",
                        )));
                    };
                    let Some(Value::List(payload_fields)) = fields.get("fields") else {
                        return Some(Err(runtime(
                            span,
                            "bootstrap variant payload offset encountered a variant without fields",
                        )));
                    };
                    offset = match offset.checked_add(payload_fields.len() as i64) {
                        Some(offset) => offset,
                        None => return Some(Err(runtime(span, "integer addition overflowed"))),
                    };
                    index += 1;
                }
                Some(Ok(Value::Int(offset)))
            }
            (
                "closure_capture_storage_index",
                [
                    Value::List(captures),
                    Value::Int(capture_index),
                    Value::Int(index),
                    Value::Int(initial_storage_index),
                ],
            ) => {
                let mut index = *index;
                let mut storage_index = *initial_storage_index;
                while index < *capture_index {
                    let Some(Value::Struct { fields, .. }) = usize::try_from(index)
                        .ok()
                        .and_then(|index| captures.get(index))
                    else {
                        return Some(Err(runtime(
                            span,
                            "bootstrap closure capture indexing encountered an invalid capture index",
                        )));
                    };
                    let Some(Value::String(drop_flag)) = fields.get("drop_flag") else {
                        return Some(Err(runtime(
                            span,
                            "bootstrap closure capture indexing encountered a capture without a drop flag",
                        )));
                    };
                    let width = if drop_flag.0.byte_len() == 0 { 1 } else { 2 };
                    storage_index = match storage_index.checked_add(width) {
                        Some(storage_index) => storage_index,
                        None => return Some(Err(runtime(span, "integer addition overflowed"))),
                    };
                    index += 1;
                }
                Some(Ok(Value::Int(storage_index)))
            }
            _ => None,
        }
    }

    fn begin_destroy(
        &mut self,
        value: Value,
        span: Span,
        frames: &mut Vec<EvalFrame>,
    ) -> Result<Control, Diagnostic> {
        let target = match &value {
            Value::Struct { name, .. } | Value::Enum { name, .. } => Some(name.as_ref()),
            _ => None,
        };
        if let Some(declaration) = target.and_then(|name| self.drops.get(name).copied()) {
            frames.push(EvalFrame::DropStructural {
                value: value.clone(),
                span,
            });
            let mut locals = Locals::new();
            locals.insert(
                "self",
                Value::Reference {
                    value: Rc::new(RefCell::new(value)),
                    unique: true,
                },
            );
            Ok(Control::Expr(declaration.body.clone(), locals))
        } else {
            self.begin_structural_destroy(value, span, frames)
        }
    }

    fn begin_structural_destroy(
        &mut self,
        value: Value,
        span: Span,
        frames: &mut Vec<EvalFrame>,
    ) -> Result<Control, Diagnostic> {
        let mut values = match value {
            Value::Struct { name, fields } => self
                .structs
                .get(name.as_ref())
                .into_iter()
                .flat_map(|field_names| field_names.iter())
                .filter_map(|field_name| fields.get(field_name).cloned())
                .collect::<Vec<_>>(),
            Value::Enum { fields, .. } => {
                Rc::try_unwrap(fields).unwrap_or_else(|shared| (*shared).clone())
            }
            Value::List(fields) => fields.into_iter().collect(),
            Value::Closure { captures, .. } => captures.into_values(),
            _ => Vec::new(),
        };
        if let Some(next) = values.pop() {
            frames.push(EvalFrame::DestroyRemaining { values, span });
            self.begin_destroy(next, span, frames)
        } else {
            Ok(Control::Value(Value::Unit))
        }
    }

    fn enter_perform(
        &mut self,
        effect: Rc<str>,
        operation: Rc<str>,
        args: Vec<Value>,
        span: Span,
        frames: &mut Vec<EvalFrame>,
    ) -> Result<Control, Diagnostic> {
        let selected = self
            .handlers
            .iter()
            .enumerate()
            .rev()
            .flat_map(|(handler_index, frame)| {
                frame
                    .clauses
                    .iter()
                    .map(move |clause| (handler_index, frame, clause))
            })
            .find_map(|(handler_index, frame, clause)| {
                if clause.effect.as_str() != effect.as_ref()
                    || clause.operation.as_str() != operation.as_ref()
                    || clause.patterns.len() != args.len()
                {
                    return None;
                }
                let mut bindings = HashMap::new();
                clause
                    .patterns
                    .iter()
                    .zip(&args)
                    .all(|(pattern, value)| {
                        match_pattern(self.program, pattern, value, &mut bindings)
                    })
                    .then(|| {
                        (
                            handler_index,
                            frame.id,
                            clause.body.clone(),
                            clause.resumption.clone(),
                            frame.captures.clone(),
                            bindings,
                        )
                    })
            });
        if let Some((handler_index, handler_id, body, resumption, mut locals, bindings)) = selected
        {
            let operation_semantics = self
                .effect_operations
                .get(&(effect.as_ref(), operation.as_ref()))
                .copied()
                .ok_or_else(|| runtime(span, "performed operation disappeared after validation"))?;
            let terminal = operation_semantics.terminal;
            let exit_index = frames
                .iter()
                .rposition(|frame| {
                    matches!(
                        frame,
                        EvalFrame::HandleExit {
                            handler_id: candidate
                        } | EvalFrame::HandlerDelimiter {
                            handler_id: candidate
                        } if *candidate == handler_id
                    )
                })
                .ok_or_else(|| runtime(span, "active handler has no continuation delimiter"))?;
            let continuation_frames = frames.split_off(exit_index + 1);
            let continuation_handlers = (!terminal).then(|| self.handlers.clone());
            // A clause runs outside the handler that selected it. Deepness means
            // that a resumption reinstalls the handler around its captured
            // continuation, not that the clause body is recursively handled.
            // The delimiter and any inner continuation are abandoned on the
            // transfer to the clause.
            frames.truncate(exit_index);
            self.handlers.truncate(handler_index);
            locals.extend(bindings);
            if terminal {
                if resumption.is_some() {
                    return Err(runtime(
                        span,
                        "terminal operation unexpectedly bound a resumption",
                    ));
                }
            } else {
                let name = resumption.ok_or_else(|| {
                    runtime(
                        span,
                        "resumptive operation clause has no continuation binding",
                    )
                    .with_help("write `with k => ...` after the operation patterns")
                })?;
                locals.insert(
                    name,
                    Value::Resumption(ResumptionValue {
                        state: Rc::new(RefCell::new(ResumptionState {
                            continuation: CapturedContinuation {
                                handler_id,
                                frames: continuation_frames,
                                handlers: continuation_handlers
                                    .expect("resumptive handler snapshot"),
                            },
                            lower: operation_semantics.lower,
                            upper: operation_semantics.upper,
                            uses: 0,
                            closed: false,
                        })),
                    }),
                );
            }
            Ok(Control::Expr(body, locals))
        } else {
            self.host
                .perform(effect.as_ref(), operation.as_ref(), args, span)
                .map(Control::Value)
        }
    }
}

fn debug_abort_stack(frames: &[EvalFrame]) {
    if std::env::var_os("GRANDIOSE_DEBUG_ABORT").is_none() {
        return;
    }
    let spans: Vec<(usize, usize)> = frames
        .iter()
        .filter_map(|frame| match frame {
            EvalFrame::CallCallee { span, .. } => Some((span.start, span.end)),
            EvalFrame::CallArgs(call) => Some((call.span.start, call.span.end)),
            _ => None,
        })
        .collect();
    let tail = &spans[spans.len().saturating_sub(40)..];
    eprintln!("abort call stack (innermost last): {tail:?}");
}

fn infer_generic_witnesses(
    formal: &TypeSyntax,
    value: &Value,
    generic_names: &HashSet<&str>,
    witnesses: &mut HashMap<String, Value>,
) {
    match (&formal.kind, value) {
        (TypeSyntaxKind::Path(path), value)
            if path.len() == 1 && generic_names.contains(path[0].name.as_str()) =>
        {
            witnesses.insert(path[0].name.clone(), value.clone());
        }
        (
            TypeSyntaxKind::SharedReference { referent, .. }
            | TypeSyntaxKind::UniqueReference { referent, .. },
            Value::Reference { value, .. },
        ) => infer_generic_witnesses(referent, &value.borrow(), generic_names, witnesses),
        (
            TypeSyntaxKind::SharedReference { referent, .. }
            | TypeSyntaxKind::UniqueReference { referent, .. },
            Value::ProjectedReference { root, fields, .. },
        ) => {
            if let Some(value) = projected_reference_value(root, fields) {
                infer_generic_witnesses(referent, &value, generic_names, witnesses);
            }
        }
        (
            TypeSyntaxKind::SharedReference { referent, .. }
            | TypeSyntaxKind::UniqueReference { referent, .. },
            value,
        ) => infer_generic_witnesses(referent, value, generic_names, witnesses),
        _ => {}
    }
}

fn same_runtime_witness_type(left: &Value, right: &Value) -> bool {
    match (left, right) {
        (Value::Reference { value: left, .. }, Value::Reference { value: right, .. }) => {
            same_runtime_witness_type(&left.borrow(), &right.borrow())
        }
        (
            Value::ProjectedReference {
                root: left,
                fields: left_fields,
                ..
            },
            Value::ProjectedReference {
                root: right,
                fields: right_fields,
                ..
            },
        ) => projected_reference_value(left, left_fields)
            .zip(projected_reference_value(right, right_fields))
            .is_some_and(|(left, right)| same_runtime_witness_type(&left, &right)),
        (Value::Int(_), Value::Int(_))
        | (Value::IntegerLiteral { .. }, Value::IntegerLiteral { .. }) => true,
        (
            Value::Integer {
                signed: left_signed,
                bits: left_bits,
                ..
            },
            Value::Integer {
                signed: right_signed,
                bits: right_bits,
                ..
            },
        ) => left_signed == right_signed && left_bits == right_bits,
        (Value::Struct { name: left, .. }, Value::Struct { name: right, .. })
        | (Value::Enum { name: left, .. }, Value::Enum { name: right, .. }) => left == right,
        (Value::Unit, Value::Unit)
        | (Value::Float(_), Value::Float(_))
        | (Value::Float32(_), Value::Float32(_))
        | (Value::Char(_), Value::Char(_))
        | (Value::String(_), Value::String(_))
        | (Value::Bytes(_), Value::Bytes(_))
        | (Value::List(_), Value::List(_))
        | (Value::Array(_), Value::Array(_)) => true,
        _ => false,
    }
}

fn match_pattern(
    program: &Program,
    pattern: &Pattern,
    value: &Value,
    bindings: &mut HashMap<String, Value>,
) -> bool {
    match (&pattern.kind, value) {
        (PatternKind::Wildcard, _) => true,
        (PatternKind::Binding(name), value) => {
            bindings.insert(name.clone(), value.clone()).is_none()
        }
        (PatternKind::Unit, Value::Unit) => true,
        (PatternKind::Int(a), Value::Int(b)) => a == b,
        (PatternKind::Int(literal), Value::Integer { signed, bits, raw }) => {
            if *signed {
                signed_integer(*raw, *bits) == i128::from(*literal)
            } else {
                u128::try_from(*literal).is_ok_and(|literal| literal == *raw)
            }
        }
        (PatternKind::Float(a), Value::Float(b)) => {
            program
                .numeric_literal(pattern.span)
                .and_then(|literal| literal.as_f64(pattern.span).ok())
                .unwrap_or(*a)
                == *b
        }
        (PatternKind::Float(a), Value::Float32(b)) => {
            program
                .numeric_literal(pattern.span)
                .and_then(|literal| literal.as_f64(pattern.span).ok())
                .unwrap_or(*a) as f32
                == *b
        }
        (PatternKind::Char(a), Value::Char(b)) => a == b,
        (PatternKind::Byte(literal), Value::Int(b)) => i64::from(*literal) == *b,
        (PatternKind::Byte(literal), Value::Integer { signed, bits, raw }) => {
            if *signed {
                signed_integer(*raw, *bits) == i128::from(*literal)
            } else {
                *raw == u128::from(*literal)
            }
        }
        (PatternKind::String(a), Value::String(b)) => b.0.equals_str(a),
        (
            PatternKind::Variant { path, fields, rest },
            Value::Enum {
                name,
                variant,
                fields: values,
            },
        ) => {
            path.len() == 2
                && path[0].as_str() == name.as_ref()
                && path[1].as_str() == variant.as_ref()
                && fields.len() <= values.len()
                && fields.iter().enumerate().all(|(position, pattern)| {
                    let index = pattern_field_index(*rest, position, fields.len(), values.len());
                    match_pattern(program, pattern, &values[index], bindings)
                })
        }
        (PatternKind::Tuple { elements, rest }, Value::List(values)) => match rest {
            None => {
                elements.len() <= values.len()
                    && elements
                        .iter()
                        .zip(values.iter())
                        .all(|(pattern, value)| match_pattern(program, pattern, value, bindings))
            }
            Some(rest) => {
                // `..` absorbs the middle: prefix patterns match from the
                // front, the remainder matches from the back.
                elements.len() <= values.len()
                    && elements.iter().enumerate().all(|(position, pattern)| {
                        let index = if position < rest.before {
                            position
                        } else {
                            values.len() - (elements.len() - position)
                        };
                        match_pattern(program, pattern, &values[index], bindings)
                    })
            }
        },
        (
            PatternKind::Struct { name, fields, .. },
            Value::Struct {
                name: value_name,
                fields: values,
            },
        ) => {
            name.as_str() == value_name.as_ref()
                && fields.iter().all(|field| {
                    values.get(&field.field).is_some_and(|value| {
                        match_pattern(program, &field.pattern, value, bindings)
                    })
                })
        }
        _ => false,
    }
}

fn statement_expr(statement: &Stmt) -> &Expr {
    match statement {
        Stmt::Let { value, .. }
        | Stmt::Deconstruct { value, .. }
        | Stmt::Assign { value, .. }
        | Stmt::Expr(value) => value,
    }
}

fn bind_deconstruction(
    statement: &Stmt,
    value: &Value,
    locals: &mut Locals,
) -> Result<(), Diagnostic> {
    let Stmt::Deconstruct {
        ty, fields, span, ..
    } = statement
    else {
        unreachable!("bind_deconstruction requires a deconstruction statement")
    };
    if let Some(ty) = ty {
        let Value::Struct {
            name,
            fields: values,
        } = value
        else {
            return Err(runtime(
                *span,
                "struct deconstruction requires a struct value",
            ));
        };
        if name.as_ref() != ty {
            return Err(runtime(
                *span,
                format!("cannot deconstruct `{name}` with a `{ty}` pattern"),
            ));
        }
        for field in fields {
            let field_value = values.get(&field.field).cloned().ok_or_else(|| {
                runtime(
                    field.span,
                    format!("struct `{ty}` has no field named `{}`", field.field),
                )
            })?;
            if let Some(binding) = &field.binding {
                locals.insert(binding.clone(), field_value);
            }
        }
    } else {
        let Value::List(values) = value else {
            return Err(runtime(
                *span,
                "tuple deconstruction requires a tuple value",
            ));
        };
        for field in fields {
            let offset = field
                .field
                .parse::<usize>()
                .map_err(|_| runtime(field.span, "invalid tuple deconstruction element index"))?;
            let index = if field.from_end {
                values.len().checked_sub(offset)
            } else {
                Some(offset)
            };
            let field_value = index.and_then(|index| values.get(index)).ok_or_else(|| {
                runtime(field.span, "tuple deconstruction element is out of bounds")
            })?;
            if let Some(binding) = &field.binding {
                locals.insert(binding.clone(), field_value.clone());
            }
        }
    }
    Ok(())
}

fn intrinsic_kind(name: &str) -> IntrinsicKind {
    match name {
        "str_len" => IntrinsicKind::StrLen,
        "str_byte_len" => IntrinsicKind::StrByteLen,
        "str_byte_at" => IntrinsicKind::StrByteAt,
        "str_char_at" => IntrinsicKind::StrCharAt,
        "str_next_index" => IntrinsicKind::StrNextIndex,
        "str_find" => IntrinsicKind::StrFind,
        "str_find_from" => IntrinsicKind::StrFindFrom,
        "str_rfind" => IntrinsicKind::StrRfind,
        "str_slice" => IntrinsicKind::StrSlice,
        "str_trim" => IntrinsicKind::StrTrim,
        "str_trim_start" => IntrinsicKind::StrTrimStart,
        "str_trim_end" => IntrinsicKind::StrTrimEnd,
        "is_i64" => IntrinsicKind::IsI64,
        "is_ascii_whitespace" => IntrinsicKind::IsAsciiWhitespace,
        "is_ascii_digit" => IntrinsicKind::IsAsciiDigit,
        "is_ascii_ident_start" => IntrinsicKind::IsAsciiIdentStart,
        "is_ascii_ident_continue" => IntrinsicKind::IsAsciiIdentContinue,
        "parse_i64" => IntrinsicKind::ParseI64,
        "int_to_string" => IntrinsicKind::IntToString,
        "bool_to_string" => IntrinsicKind::BoolToString,
        "list_len" => IntrinsicKind::ListLen,
        "list_get" => IntrinsicKind::ListGet,
        "list_push" | "list_push_owned" => IntrinsicKind::ListPush,
        "list_concat" => IntrinsicKind::ListConcat,
        "debug" => IntrinsicKind::Debug,
        "assert" => IntrinsicKind::Assert,
        _ => IntrinsicKind::Invalid,
    }
}

fn array_reference(
    value: &Value,
    require_unique: bool,
    span: Span,
) -> Result<ArrayRef, Diagnostic> {
    let (referent, unique) = match value {
        Value::Reference { value, unique } => (Some(value.borrow().clone()), *unique),
        Value::ProjectedReference {
            root,
            fields,
            unique,
        } => (projected_reference_value(root, fields), *unique),
        _ => (None, false),
    };
    let Some(referent) = referent else {
        return Err(runtime(span, "Array primitive expected an array reference"));
    };
    if require_unique && !unique {
        return Err(runtime(span, "Array mutation requires a unique reference"));
    }
    let Value::Array(array) = referent else {
        return Err(runtime(
            span,
            "Array primitive reference has the wrong referent type",
        ));
    };
    Ok(array)
}

fn array_index(value: &Value, what: &str, span: Span) -> Result<usize, Diagnostic> {
    let value = match value {
        Value::Int(value) => {
            return usize::try_from(*value)
                .map_err(|_| runtime(span, format!("{what} cannot be negative")));
        }
        Value::Integer {
            signed: false,
            bits: 64,
            raw,
        } => *raw,
        _ => return Err(runtime(span, format!("{what} must be a usize"))),
    };
    usize::try_from(value).map_err(|_| runtime(span, format!("{what} is too large")))
}

fn unsigned_scalar(value: &Value, bits: u8) -> Option<u128> {
    match value {
        Value::Int(value) => u128::try_from(*value)
            .ok()
            .filter(|value| *value <= integer_mask(bits)),
        Value::Integer {
            signed: false,
            bits: value_bits,
            raw,
        } if *value_bits == bits => Some(*raw),
        _ => None,
    }
}

fn array_length_value(value: usize, span: Span) -> Result<Value, Diagnostic> {
    i64::try_from(value).map(Value::Int).map_err(|_| {
        runtime(
            span,
            "Array length does not fit the recovery interpreter's usize",
        )
    })
}

fn grow_interpreter_array(
    array: &mut InterpreterArray,
    required: usize,
    span: Span,
) -> Result<(), Diagnostic> {
    if required > array.logical_capacity {
        let capacity = required
            .max(4)
            .checked_next_power_of_two()
            .ok_or_else(|| runtime(span, "Array capacity overflowed"))?;
        if capacity > array.slots.capacity() {
            array
                .slots
                .try_reserve_exact(capacity.saturating_sub(array.slots.len()))
                .map_err(|_| runtime(span, "Array allocation failed"))?;
        }
        array.logical_capacity = capacity;
    } else if required > array.slots.capacity() {
        array
            .slots
            .try_reserve_exact(required.saturating_sub(array.slots.len()))
            .map_err(|_| runtime(span, "Array allocation failed"))?;
    }
    Ok(())
}

// Keep recovery execution subject to the same finite primitive-output bound as
// the bytecode VM.  Besides preserving differential behavior, this prevents a
// small trusted call from turning length amplification into an allocator abort.
const MAX_PRIMITIVE_ALLOCATION_BYTES: usize = 64 * 1024 * 1024;

fn checked_primitive_output_len(
    left: usize,
    right: usize,
    span: Span,
) -> Result<usize, Diagnostic> {
    let length = left
        .checked_add(right)
        .ok_or_else(|| runtime(span, "runtime primitive allocation overflowed"))?;
    if length > MAX_PRIMITIVE_ALLOCATION_BYTES || length > isize::MAX as usize {
        Err(runtime(span, "runtime primitive allocation overflowed"))
    } else {
        Ok(length)
    }
}

fn reserve_primitive_output<T>(
    values: &mut Vec<T>,
    count: usize,
    span: Span,
) -> Result<(), Diagnostic> {
    let bytes = count
        .checked_mul(std::mem::size_of::<T>().max(1))
        .ok_or_else(|| runtime(span, "runtime primitive allocation overflowed"))?;
    if bytes > MAX_PRIMITIVE_ALLOCATION_BYTES || bytes > isize::MAX as usize {
        return Err(runtime(span, "runtime primitive allocation overflowed"));
    }
    values
        .try_reserve_exact(count)
        .map_err(|_| runtime(span, "runtime primitive allocation overflowed"))
}

fn check_primitive_output_count<T>(count: usize, span: Span) -> Result<(), Diagnostic> {
    let bytes = count
        .checked_mul(std::mem::size_of::<T>().max(1))
        .ok_or_else(|| runtime(span, "runtime primitive allocation overflowed"))?;
    if bytes > MAX_PRIMITIVE_ALLOCATION_BYTES || bytes > isize::MAX as usize {
        Err(runtime(span, "runtime primitive allocation overflowed"))
    } else {
        Ok(())
    }
}

fn eval_runtime_primitive(
    primitive: Primitive,
    args: &[Value],
    span: Span,
) -> Result<Value, Diagnostic> {
    if matches!(
        primitive,
        Primitive::IntWrappingAdd
            | Primitive::IntWrappingSub
            | Primitive::IntWrappingMul
            | Primitive::IntBitAnd
            | Primitive::IntBitOr
            | Primitive::IntBitXor
            | Primitive::IntBitNot
            | Primitive::IntShl
            | Primitive::IntShr
    ) {
        return eval_runtime_integer_primitive(primitive, args, span);
    }
    match (primitive, args) {
        (Primitive::CharFromU32Checked, [value]) => {
            let scalar = unsigned_scalar(value, 32)
                .and_then(|value| u32::try_from(value).ok())
                .ok_or_else(|| runtime(span, "char conversion requires a u32 scalar"))?;
            char::from_u32(scalar)
                .map(Value::Char)
                .ok_or_else(|| runtime(span, "integer is not a valid Unicode scalar"))
        }
        (Primitive::CharToU32, [Value::Char(value)]) => Ok(Value::Integer {
            signed: false,
            bits: 32,
            raw: u128::from(u32::from(*value)),
        }),
        (Primitive::CharFromU32Checked | Primitive::CharToU32, _) => Err(runtime(
            span,
            format!("invalid call to character primitive {primitive:?}"),
        )),
        (Primitive::TextByteLen, [Value::String(text)]) => {
            array_length_value(text.0.byte_len(), span)
        }
        (Primitive::TextConcat, [Value::String(left), Value::String(right)]) => {
            checked_primitive_output_len(left.0.byte_len(), right.0.byte_len(), span)?;
            Ok(Value::String(TextRef(Text::concatenate(
                left.0.clone(),
                right.0.clone(),
            ))))
        }
        (Primitive::TextEq, [Value::String(left), Value::String(right)]) => {
            Ok(Value::Int(i64::from(left == right)))
        }
        (Primitive::TextFromUtf8Checked, [Value::Bytes(bytes)]) => {
            if bytes.len() > MAX_PRIMITIVE_ALLOCATION_BYTES {
                return Err(runtime(span, "runtime primitive allocation overflowed"));
            }
            let text = std::str::from_utf8(bytes)
                .map_err(|_| runtime(span, "byte sequence is not valid UTF-8"))?;
            Ok(Value::String(text.into()))
        }
        (Primitive::TextAsBytes, [Value::String(text)]) => {
            let text = text.0.flatten_shared();
            let mut bytes = Vec::new();
            reserve_primitive_output(&mut bytes, text.len(), span)?;
            bytes.extend_from_slice(text.as_bytes());
            Ok(Value::Bytes(bytes.into()))
        }
        (Primitive::BytesLen, [Value::Bytes(bytes)]) => array_length_value(bytes.len(), span),
        (Primitive::BytesConcat, [Value::Bytes(left), Value::Bytes(right)]) => {
            let length = checked_primitive_output_len(left.len(), right.len(), span)?;
            let mut bytes = Vec::new();
            reserve_primitive_output(&mut bytes, length, span)?;
            bytes.extend_from_slice(left);
            bytes.extend_from_slice(right);
            Ok(Value::Bytes(bytes.into()))
        }
        (Primitive::BytesGet, [Value::Bytes(bytes), index]) => {
            let index = array_index(index, "Bytes index", span)?;
            bytes
                .get(index)
                .copied()
                .map(|byte| Value::Int(i64::from(byte)))
                .ok_or_else(|| runtime(span, "Bytes index is out of bounds"))
        }
        (Primitive::BytesSlice, [Value::Bytes(bytes), start, end]) => {
            let start = array_index(start, "Bytes slice start", span)?;
            let end = array_index(end, "Bytes slice end", span)?;
            let slice = bytes
                .get(start..end)
                .ok_or_else(|| runtime(span, "Bytes slice is out of bounds"))?;
            let mut result = Vec::new();
            reserve_primitive_output(&mut result, slice.len(), span)?;
            result.extend_from_slice(slice);
            Ok(Value::Bytes(result.into()))
        }
        (Primitive::BytesFromArrayMove, [Value::Array(array)]) => {
            let array = array.0.borrow();
            let mut bytes = Vec::new();
            reserve_primitive_output(&mut bytes, array.slots.len(), span)?;
            for slot in &array.slots {
                let Some(value) = slot else {
                    return Err(runtime(span, "Array slot is empty"));
                };
                let byte = unsigned_scalar(&value.borrow(), 8)
                    .and_then(|byte| u8::try_from(byte).ok())
                    .ok_or_else(|| runtime(span, "byte Array element is outside the u8 range"))?;
                bytes.push(byte);
            }
            Ok(Value::Bytes(bytes.into()))
        }
        (Primitive::BytesToArray, [Value::Bytes(bytes)]) => {
            // The VM charges this allocation as `Option<Value>` slots even
            // though recovery cells use an additional Rc/RefCell indirection.
            check_primitive_output_count::<Option<Value>>(bytes.len(), span)?;
            let mut slots = Vec::new();
            reserve_primitive_output(&mut slots, bytes.len(), span)?;
            slots.extend(bytes.iter().map(|byte| {
                Some(Rc::new(RefCell::new(Value::Integer {
                    signed: false,
                    bits: 8,
                    raw: u128::from(*byte),
                })))
            }));
            Ok(Value::Array(ArrayRef(Rc::new(RefCell::new(
                InterpreterArray {
                    logical_capacity: slots.len(),
                    slots,
                },
            )))))
        }
        (
            Primitive::TextByteLen
            | Primitive::TextConcat
            | Primitive::TextEq
            | Primitive::TextFromUtf8Checked
            | Primitive::TextAsBytes
            | Primitive::BytesLen
            | Primitive::BytesConcat
            | Primitive::BytesGet
            | Primitive::BytesSlice
            | Primitive::BytesFromArrayMove
            | Primitive::BytesToArray,
            _,
        ) => Err(runtime(
            span,
            format!("invalid call to Text/Bytes primitive {primitive:?}"),
        )),
        _ => eval_array_primitive(primitive, args, span),
    }
}

fn eval_runtime_integer_primitive(
    primitive: Primitive,
    args: &[Value],
    span: Span,
) -> Result<Value, Diagnostic> {
    let value = args
        .first()
        .ok_or_else(|| runtime(span, "integer primitive is missing its operand"))?;
    let Some(kind) = typed_integer_kind(value) else {
        return Err(runtime(
            span,
            "integer primitive requires a typed integer operand",
        ));
    };
    let raw = |value: &Value| -> Result<u128, Diagnostic> {
        let value = coerce_integer(value.clone(), kind, span)?;
        Ok(match value {
            Value::Int(value) => value as u128 & integer_mask(kind.bits),
            Value::Integer { raw, .. } => raw,
            _ => unreachable!("integer coercion returned a non-integer"),
        })
    };
    let make = |raw| Value::Integer {
        signed: kind.signed,
        bits: kind.bits,
        raw: raw & integer_mask(kind.bits),
    };
    let first = raw(value)?;
    let result = match primitive {
        Primitive::IntBitNot => {
            if args.len() != 1 {
                return Err(runtime(span, "bit_not expects one operand"));
            }
            !first
        }
        Primitive::IntWrappingAdd
        | Primitive::IntWrappingSub
        | Primitive::IntWrappingMul
        | Primitive::IntBitAnd
        | Primitive::IntBitOr
        | Primitive::IntBitXor => {
            let [_, right] = args else {
                return Err(runtime(
                    span,
                    "binary integer primitive expects two operands",
                ));
            };
            let right = raw(right)?;
            match primitive {
                Primitive::IntWrappingAdd => first.wrapping_add(right),
                Primitive::IntWrappingSub => first.wrapping_sub(right),
                Primitive::IntWrappingMul => first.wrapping_mul(right),
                Primitive::IntBitAnd => first & right,
                Primitive::IntBitOr => first | right,
                Primitive::IntBitXor => first ^ right,
                _ => unreachable!(),
            }
        }
        Primitive::IntShl | Primitive::IntShr => {
            let [_, count] = args else {
                return Err(runtime(span, "integer shift expects two operands"));
            };
            let Value::Integer {
                signed: false,
                bits: 32,
                raw: count,
            } = count
            else {
                return Err(runtime(span, "integer shift count must be u32"));
            };
            let count = u32::try_from(*count)
                .ok()
                .filter(|count| *count < u32::from(kind.bits))
                .ok_or_else(|| runtime(span, "invalid integer shift count"))?;
            if primitive == Primitive::IntShl {
                first << count
            } else if kind.signed {
                (signed_integer(first, kind.bits) >> count) as u128
            } else {
                first >> count
            }
        }
        _ => unreachable!("caller filters scalar runtime primitives"),
    };
    Ok(make(result))
}

fn eval_runtime_float_primitive(
    leaf: FloatRuntimeLeaf,
    args: &[Value],
    span: Span,
) -> Result<Value, Diagnostic> {
    let bool_value = |value: bool| Value::Integer {
        signed: false,
        bits: 32,
        raw: u128::from(value),
    };
    match leaf {
        FloatRuntimeLeaf::Unary { primitive, width } => {
            let [value] = args else {
                return Err(runtime(span, "unary float primitive expects one operand"));
            };
            if primitive != Primitive::FloatNeg {
                return Err(runtime(span, "invalid unary float primitive"));
            }
            match width {
                FloatKind::F32 => Ok(Value::Float32(canonical_f32(-float_as_f32(value, span)?))),
                FloatKind::F64 => Ok(Value::Float(canonical_f64(-float_as_f64(value, span)?))),
            }
        }
        FloatRuntimeLeaf::Binary { primitive, width } => {
            let [left, right] = args else {
                return Err(runtime(span, "binary float primitive expects two operands"));
            };
            match width {
                FloatKind::F32 => {
                    let (left, right) = (float_as_f32(left, span)?, float_as_f32(right, span)?);
                    let result = match primitive {
                        Primitive::FloatAdd => left + right,
                        Primitive::FloatSub => left - right,
                        Primitive::FloatMul => left * right,
                        Primitive::FloatDiv => left / right,
                        Primitive::FloatRem => left % right,
                        _ => return Err(runtime(span, "invalid binary float primitive")),
                    };
                    Ok(Value::Float32(canonical_f32(result)))
                }
                FloatKind::F64 => {
                    let (left, right) = (float_as_f64(left, span)?, float_as_f64(right, span)?);
                    let result = match primitive {
                        Primitive::FloatAdd => left + right,
                        Primitive::FloatSub => left - right,
                        Primitive::FloatMul => left * right,
                        Primitive::FloatDiv => left / right,
                        Primitive::FloatRem => left % right,
                        _ => return Err(runtime(span, "invalid binary float primitive")),
                    };
                    Ok(Value::Float(canonical_f64(result)))
                }
            }
        }
        FloatRuntimeLeaf::Comparison { primitive, width } => {
            let [left, right] = args else {
                return Err(runtime(span, "float comparison expects two operands"));
            };
            let result = match width {
                FloatKind::F32 => {
                    let (left, right) = (float_as_f32(left, span)?, float_as_f32(right, span)?);
                    compare_float(primitive, left, right, span)?
                }
                FloatKind::F64 => {
                    let (left, right) = (float_as_f64(left, span)?, float_as_f64(right, span)?);
                    compare_float(primitive, left, right, span)?
                }
            };
            Ok(bool_value(result))
        }
        FloatRuntimeLeaf::Convert { source, target } => {
            let [value] = args else {
                return Err(runtime(span, "float conversion expects one operand"));
            };
            match (source, target) {
                (FloatKind::F32, FloatKind::F64) => Ok(Value::Float(canonical_f64(f64::from(
                    float_as_f32(value, span)?,
                )))),
                (FloatKind::F64, FloatKind::F32) => Ok(Value::Float32(canonical_f32(
                    float_as_f64(value, span)? as f32,
                ))),
                _ => Err(runtime(span, "float conversion requires different widths")),
            }
        }
        FloatRuntimeLeaf::IntToFloat { source, target } => {
            let [value] = args else {
                return Err(runtime(
                    span,
                    "integer-to-float conversion expects one operand",
                ));
            };
            let value = integer_raw_for_kind(value, source, span)?;
            match (source.signed, target) {
                (true, FloatKind::F32) => {
                    Ok(Value::Float32(canonical_f32(
                        signed_integer(value, source.bits) as f32,
                    )))
                }
                (false, FloatKind::F32) => Ok(Value::Float32(canonical_f32(value as f32))),
                (true, FloatKind::F64) => Ok(Value::Float(canonical_f64(signed_integer(
                    value,
                    source.bits,
                ) as f64))),
                (false, FloatKind::F64) => Ok(Value::Float(canonical_f64(value as f64))),
            }
        }
        FloatRuntimeLeaf::FloatToIntChecked { source, target } => {
            let [value] = args else {
                return Err(runtime(
                    span,
                    "float-to-integer conversion expects one operand",
                ));
            };
            let value = match source {
                FloatKind::F32 => f64::from(float_as_f32(value, span)?),
                FloatKind::F64 => float_as_f64(value, span)?,
            };
            if !value.is_finite() {
                return Err(runtime(span, "float-to-integer conversion is out of range"));
            }
            let raw = if target.signed {
                let limit = 2_f64.powi(i32::from(target.bits - 1));
                if value < -limit || value >= limit {
                    return Err(runtime(span, "float-to-integer conversion is out of range"));
                }
                (value.trunc() as i128) as u128
            } else {
                let limit = 2_f64.powi(i32::from(target.bits));
                if value < 0.0 || value >= limit {
                    return Err(runtime(span, "float-to-integer conversion is out of range"));
                }
                value.trunc() as u128
            };
            Ok(Value::Integer {
                signed: target.signed,
                bits: target.bits,
                raw: raw & integer_mask(target.bits),
            })
        }
        FloatRuntimeLeaf::ToBits { source } => {
            let [value] = args else {
                return Err(runtime(
                    span,
                    "float-to-bits conversion expects one operand",
                ));
            };
            match source {
                FloatKind::F32 => Ok(Value::Integer {
                    signed: false,
                    bits: 32,
                    raw: u128::from(canonical_f32(float_as_f32(value, span)?).to_bits()),
                }),
                FloatKind::F64 => Ok(Value::Integer {
                    signed: false,
                    bits: 64,
                    raw: u128::from(canonical_f64(float_as_f64(value, span)?).to_bits()),
                }),
            }
        }
        FloatRuntimeLeaf::FromBits { target } => {
            let [value] = args else {
                return Err(runtime(
                    span,
                    "bits-to-float conversion expects one operand",
                ));
            };
            let source = match target {
                FloatKind::F32 => IntegerKind {
                    signed: false,
                    bits: 32,
                },
                FloatKind::F64 => IntegerKind {
                    signed: false,
                    bits: 64,
                },
            };
            let bits = integer_raw_for_kind(value, source, span)?;
            match target {
                FloatKind::F32 => Ok(Value::Float32(canonical_f32(f32::from_bits(bits as u32)))),
                FloatKind::F64 => Ok(Value::Float(canonical_f64(f64::from_bits(bits as u64)))),
            }
        }
    }
}

fn canonical_f32(value: f32) -> f32 {
    if value.is_nan() {
        f32::from_bits(0x7fc0_0000)
    } else {
        value
    }
}

fn canonical_f64(value: f64) -> f64 {
    if value.is_nan() {
        f64::from_bits(0x7ff8_0000_0000_0000)
    } else {
        value
    }
}

fn float_as_f32(value: &Value, span: Span) -> Result<f32, Diagnostic> {
    match value {
        Value::Float32(value) => Ok(*value),
        // Float literals start unconstrained in recovery execution and obtain
        // their exact width at the trusted declaration boundary.
        Value::Float(value) => Ok(canonical_f32(*value as f32)),
        value => Err(runtime(
            span,
            format!("expected an f32 value, received `{value:?}`"),
        )),
    }
}

fn float_as_f64(value: &Value, span: Span) -> Result<f64, Diagnostic> {
    match value {
        Value::Float(value) => Ok(*value),
        Value::Float32(value) => Ok(f64::from(*value)),
        value => Err(runtime(
            span,
            format!("expected an f64 value, received `{value:?}`"),
        )),
    }
}

fn coerce_declared_float(value: Value, kind: FloatKind, span: Span) -> Result<Value, Diagnostic> {
    match kind {
        FloatKind::F32 => Ok(Value::Float32(canonical_f32(float_as_f32(&value, span)?))),
        FloatKind::F64 => Ok(Value::Float(canonical_f64(float_as_f64(&value, span)?))),
    }
}

fn compare_float<T: PartialEq + PartialOrd>(
    primitive: Primitive,
    left: T,
    right: T,
    span: Span,
) -> Result<bool, Diagnostic> {
    match primitive {
        Primitive::FloatEq => Ok(left == right),
        Primitive::FloatNe => Ok(left != right),
        Primitive::FloatLt => Ok(left < right),
        Primitive::FloatLe => Ok(left <= right),
        Primitive::FloatGt => Ok(left > right),
        Primitive::FloatGe => Ok(left >= right),
        _ => Err(runtime(span, "invalid float comparison primitive")),
    }
}

fn integer_raw_for_kind(value: &Value, kind: IntegerKind, span: Span) -> Result<u128, Diagnostic> {
    match coerce_integer(value.clone(), kind, span)? {
        Value::Int(value) => Ok(value as u128 & integer_mask(kind.bits)),
        Value::Integer { raw, .. } => Ok(raw),
        _ => unreachable!("integer coercion returned a non-integer"),
    }
}

fn eval_runtime_integer_conversion(
    primitive: Primitive,
    target: IntegerKind,
    args: &[Value],
    span: Span,
) -> Result<Value, Diagnostic> {
    let [value] = args else {
        return Err(runtime(span, "integer conversion expects one operand"));
    };
    let Some(source) = typed_integer_kind(value) else {
        return Err(runtime(
            span,
            "integer conversion requires a typed integer operand",
        ));
    };
    let value = coerce_integer(value.clone(), source, span)?;
    let raw = match value {
        Value::Int(value) => value as u128 & integer_mask(source.bits),
        Value::Integer { raw, .. } => raw,
        _ => unreachable!("integer coercion returned a non-integer"),
    };
    let converted = if primitive == Primitive::IntConvertWrapping {
        if source.signed {
            signed_integer(raw, source.bits) as u128
        } else {
            raw
        }
    } else if primitive == Primitive::IntConvertChecked {
        if source.signed {
            let value = signed_integer(raw, source.bits);
            if target.signed {
                let (minimum, maximum) = if target.bits == 128 {
                    (i128::MIN, i128::MAX)
                } else {
                    let limit = 1_i128 << (target.bits - 1);
                    (-limit, limit - 1)
                };
                if value < minimum || value > maximum {
                    return Err(runtime(span, "integer conversion is out of range"));
                }
                value as u128
            } else {
                u128::try_from(value)
                    .ok()
                    .filter(|value| *value <= integer_mask(target.bits))
                    .ok_or_else(|| runtime(span, "integer conversion is out of range"))?
            }
        } else if target.signed {
            let maximum = if target.bits == 128 {
                i128::MAX as u128
            } else {
                (1_u128 << (target.bits - 1)) - 1
            };
            if raw > maximum {
                return Err(runtime(span, "integer conversion is out of range"));
            }
            raw
        } else {
            if raw > integer_mask(target.bits) {
                return Err(runtime(span, "integer conversion is out of range"));
            }
            raw
        }
    } else {
        return Err(runtime(span, "invalid integer conversion primitive"));
    };
    Ok(Value::Integer {
        signed: target.signed,
        bits: target.bits,
        raw: converted & integer_mask(target.bits),
    })
}

fn eval_array_primitive(
    primitive: Primitive,
    args: &[Value],
    span: Span,
) -> Result<Value, Diagnostic> {
    match (primitive, args) {
        (Primitive::ArrayNew, [length, fill]) => {
            let length = array_index(length, "Array length", span)?;
            let mut slots = Vec::new();
            slots
                .try_reserve_exact(length)
                .map_err(|_| runtime(span, "Array allocation failed"))?;
            slots.extend((0..length).map(|_| Some(Rc::new(RefCell::new(fill.clone())))));
            Ok(Value::Array(ArrayRef(Rc::new(RefCell::new(
                InterpreterArray {
                    slots,
                    logical_capacity: length,
                },
            )))))
        }
        (Primitive::ArrayEmpty, []) => Ok(Value::Array(ArrayRef(Rc::new(RefCell::new(
            InterpreterArray::default(),
        ))))),
        (Primitive::ArrayLen, [reference]) => {
            let array = array_reference(reference, false, span)?;
            let length = array.0.borrow().slots.len();
            array_length_value(length, span)
        }
        (Primitive::ArrayCapacity, [reference]) => {
            let array = array_reference(reference, false, span)?;
            let capacity = array.0.borrow().logical_capacity;
            array_length_value(capacity, span)
        }
        (Primitive::ArrayGetCopy, [reference, index]) => {
            let array = array_reference(reference, false, span)?;
            let index = array_index(index, "Array index", span)?;
            let array = array.0.borrow();
            array
                .slots
                .get(index)
                .ok_or_else(|| runtime(span, "Array index is out of bounds"))?
                .as_ref()
                .map(|value| value.borrow().clone())
                .ok_or_else(|| runtime(span, "Array slot is empty"))
        }
        (Primitive::ArrayGetMove, [reference, index]) => {
            let array = array_reference(reference, true, span)?;
            let index = array_index(index, "Array index", span)?;
            let value = array
                .0
                .borrow_mut()
                .slots
                .get_mut(index)
                .ok_or_else(|| runtime(span, "Array index is out of bounds"))?
                .take()
                .ok_or_else(|| runtime(span, "Array slot is empty"))?;
            Ok(value.borrow().clone())
        }
        (Primitive::ArrayGetBorrowShared | Primitive::ArrayGetBorrowUnique, [reference, index]) => {
            let unique = primitive == Primitive::ArrayGetBorrowUnique;
            let array = array_reference(reference, unique, span)?;
            let index = array_index(index, "Array index", span)?;
            let value = array
                .0
                .borrow()
                .slots
                .get(index)
                .ok_or_else(|| runtime(span, "Array index is out of bounds"))?
                .as_ref()
                .cloned()
                .ok_or_else(|| runtime(span, "Array slot is empty"))?;
            Ok(Value::Reference { value, unique })
        }
        (Primitive::ArraySetMove, [reference, index, value]) => {
            let array = array_reference(reference, true, span)?;
            let index = array_index(index, "Array index", span)?;
            let mut array = array.0.borrow_mut();
            let slot = array
                .slots
                .get_mut(index)
                .ok_or_else(|| runtime(span, "Array index is out of bounds"))?;
            if slot.is_some() {
                return Err(runtime(span, "Array slot is already initialized"));
            }
            *slot = Some(Rc::new(RefCell::new(value.clone())));
            Ok(Value::Unit)
        }
        (Primitive::ArrayPushMove, [reference, value]) => {
            let array = array_reference(reference, true, span)?;
            let mut array = array.0.borrow_mut();
            let required = array
                .slots
                .len()
                .checked_add(1)
                .ok_or_else(|| runtime(span, "Array capacity overflowed"))?;
            grow_interpreter_array(&mut array, required, span)?;
            array.slots.push(Some(Rc::new(RefCell::new(value.clone()))));
            Ok(Value::Unit)
        }
        (Primitive::ArrayPopMove, [reference]) => {
            let array = array_reference(reference, true, span)?;
            let value = array
                .0
                .borrow_mut()
                .slots
                .pop()
                .ok_or_else(|| runtime(span, "Array is empty"))?
                .ok_or_else(|| runtime(span, "Array slot is empty"))?;
            Ok(value.borrow().clone())
        }
        (Primitive::ArrayReserve, [reference, additional]) => {
            let array = array_reference(reference, true, span)?;
            let additional = array_index(additional, "Array reserve amount", span)?;
            let mut array = array.0.borrow_mut();
            let required = array
                .slots
                .len()
                .checked_add(additional)
                .ok_or_else(|| runtime(span, "Array capacity overflowed"))?;
            grow_interpreter_array(&mut array, required, span)?;
            Ok(Value::Unit)
        }
        (Primitive::ArrayFinishDrained, [Value::Array(array)]) => {
            if array.0.borrow().slots.iter().any(Option::is_some) {
                Err(runtime(span, "Array is not fully drained"))
            } else {
                Ok(Value::Unit)
            }
        }
        (primitive, _) => Err(runtime(
            span,
            format!("invalid call to Array primitive {primitive:?}"),
        )),
    }
}

fn intrinsic(
    kind: IntrinsicKind,
    name: &str,
    args: &[Value],
    span: Span,
) -> Result<Value, Diagnostic> {
    let value = match (kind, args) {
        (IntrinsicKind::StrLen, [Value::String(value)]) => {
            Value::Int(value.0.character_len() as i64)
        }
        (IntrinsicKind::StrByteLen, [Value::String(value)]) => {
            Value::Int(value.0.byte_len() as i64)
        }
        (IntrinsicKind::StrByteAt, [Value::String(value), Value::Int(index)]) => {
            let index = usize::try_from(*index)
                .map_err(|_| runtime(span, "string byte index cannot be negative"))?;
            Value::Int(value.0.byte_at(index).ok_or_else(|| {
                runtime(span, format!("string byte index {index} is out of bounds"))
            })? as i64)
        }
        (IntrinsicKind::StrCharAt, [Value::String(value), Value::Int(index)]) => {
            let index = usize::try_from(*index)
                .map_err(|_| runtime(span, "character index cannot be negative"))?;
            let flattened = value.0.flatten_shared();
            let character = flattened
                .get(index..)
                .and_then(|tail| tail.chars().next())
                .ok_or_else(|| {
                    runtime(
                        span,
                        format!(
                            "character index {index} is out of bounds or not on a UTF-8 boundary"
                        ),
                    )
                })?;
            Value::String(character.to_string().into())
        }
        (IntrinsicKind::StrNextIndex, [Value::String(value), Value::Int(index)]) => {
            let index = usize::try_from(*index)
                .map_err(|_| runtime(span, "character index cannot be negative"))?;
            let flattened = value.0.flatten_shared();
            let character = flattened
                .get(index..)
                .and_then(|tail| tail.chars().next())
                .ok_or_else(|| {
                    runtime(
                        span,
                        format!(
                            "character index {index} is out of bounds or not on a UTF-8 boundary"
                        ),
                    )
                })?;
            Value::Int((index + character.len_utf8()) as i64)
        }
        (IntrinsicKind::StrFind, [Value::String(value), Value::String(needle)]) => {
            let value = value.0.flatten_shared();
            let needle = needle.0.flatten_shared();
            Value::Int(value.find(&*needle).map_or(-1, |index| index as i64))
        }
        (
            IntrinsicKind::StrFindFrom,
            [
                Value::String(value),
                Value::String(needle),
                Value::Int(start),
            ],
        ) => {
            let value = value.0.flatten_shared();
            let needle = needle.0.flatten_shared();
            let start = usize::try_from(*start)
                .map_err(|_| runtime(span, "string search start cannot be negative"))?;
            Value::Int(
                value
                    .get(start..)
                    .and_then(|tail| tail.find(&*needle))
                    .map_or(-1, |index| (start + index) as i64),
            )
        }
        (IntrinsicKind::StrRfind, [Value::String(value), Value::String(needle)]) => {
            let value = value.0.flatten_shared();
            let needle = needle.0.flatten_shared();
            Value::Int(value.rfind(&*needle).map_or(-1, |index| index as i64))
        }
        (IntrinsicKind::StrSlice, [Value::String(value), Value::Int(start), Value::Int(end)]) => {
            let start = usize::try_from(*start)
                .map_err(|_| runtime(span, "string slice start cannot be negative"))?;
            let end = usize::try_from(*end)
                .map_err(|_| runtime(span, "string slice end cannot be negative"))?;
            let flattened = value.0.flatten_shared();
            Value::String(flattened.get(start..end).ok_or_else(|| runtime(span, format!("string slice {start}..{end} is out of bounds or not on UTF-8 boundaries")))?.to_owned().into())
        }
        (IntrinsicKind::StrTrim, [Value::String(value)]) => {
            Value::String(value.0.flatten_shared().trim().to_owned().into())
        }
        (IntrinsicKind::StrTrimStart, [Value::String(value)]) => {
            let flattened = value.0.flatten_shared();
            Value::Int((flattened.len() - flattened.trim_start().len()) as i64)
        }
        (IntrinsicKind::StrTrimEnd, [Value::String(value)]) => {
            Value::Int(value.0.flatten_shared().trim_end().len() as i64)
        }
        (IntrinsicKind::IsI64, [Value::String(value)]) => {
            truth(value.0.flatten_shared().parse::<i64>().is_ok())
        }
        (IntrinsicKind::IsAsciiWhitespace, [Value::String(value)]) => {
            truth(value.0.byte_len() == 1 && value.0.byte_at(0).unwrap().is_ascii_whitespace())
        }
        (IntrinsicKind::IsAsciiDigit, [Value::String(value)]) => {
            truth(value.0.byte_len() == 1 && value.0.byte_at(0).unwrap().is_ascii_digit())
        }
        (IntrinsicKind::IsAsciiIdentStart, [Value::String(value)]) => truth(
            value.0.byte_len() == 1
                && (value.0.byte_at(0).unwrap().is_ascii_alphabetic()
                    || value.0.byte_at(0).unwrap() == b'_'),
        ),
        (IntrinsicKind::IsAsciiIdentContinue, [Value::String(value)]) => truth(
            value.0.byte_len() == 1
                && (value.0.byte_at(0).unwrap().is_ascii_alphanumeric()
                    || value.0.byte_at(0).unwrap() == b'_'),
        ),
        (IntrinsicKind::ParseI64, [Value::String(value)]) => {
            Value::Int(
                value.0.flatten_shared().parse::<i64>().map_err(|_| {
                    runtime(span, format!("`{value}` is not a signed 64-bit integer"))
                })?,
            )
        }
        (IntrinsicKind::IntToString, [Value::Int(value)]) => {
            Value::String(value.to_string().into())
        }
        (IntrinsicKind::BoolToString, [value]) if is_truth(value) => Value::String("true".into()),
        (IntrinsicKind::BoolToString, [value]) if is_falsehood(value) => {
            Value::String("false".into())
        }
        (IntrinsicKind::ListLen, [Value::List(values)]) => Value::Int(values.len() as i64),
        (IntrinsicKind::ListGet, [Value::List(values), Value::Int(index)]) => values
            .get(*index as usize)
            .cloned()
            .ok_or_else(|| runtime(span, format!("list index {index} is out of bounds")))?,
        (IntrinsicKind::ListPush, [Value::List(values), value]) => {
            let mut result = values.clone();
            result.push_back(value.clone());
            Value::List(result)
        }
        (IntrinsicKind::ListConcat, [Value::List(front), Value::List(back)]) => {
            let mut result = front.clone();
            result.append(back.clone());
            Value::List(result)
        }
        (IntrinsicKind::Debug, [value]) => Value::String(format!("{value:?}").into()),
        (IntrinsicKind::Assert, [value]) if is_truth(value) => Value::Unit,
        (IntrinsicKind::Assert, [value]) if is_falsehood(value) => {
            return Err(runtime(span, "assertion failed"));
        }
        _ => return Err(runtime(span, format!("invalid call to intrinsic `{name}`"))),
    };
    Ok(value)
}

fn integer_mask(bits: u8) -> u128 {
    if bits == 128 {
        u128::MAX
    } else {
        (1_u128 << bits) - 1
    }
}

fn signed_integer(raw: u128, bits: u8) -> i128 {
    let raw = raw & integer_mask(bits);
    if bits == 128 {
        raw as i128
    } else {
        ((raw << (128 - bits)) as i128) >> (128 - bits)
    }
}

fn coerce_integer(value: Value, kind: IntegerKind, span: Span) -> Result<Value, Diagnostic> {
    if let Value::Integer { signed, bits, .. } = &value
        && (*signed != kind.signed || *bits != kind.bits)
    {
        return Err(runtime(
            span,
            "integer value does not match its source-declared type",
        ));
    }
    let raw = match value {
        Value::Int(value) if kind.signed => {
            let (minimum, maximum) = if kind.bits == 128 {
                (i128::MIN, i128::MAX)
            } else {
                let limit = 1_i128 << (kind.bits - 1);
                (-limit, limit - 1)
            };
            let value = i128::from(value);
            if value < minimum || value > maximum {
                return Err(runtime(span, "integer value is outside its declared type"));
            }
            value as u128 & integer_mask(kind.bits)
        }
        Value::Int(value) => {
            let value = u128::try_from(value)
                .map_err(|_| runtime(span, "negative value has an unsigned integer type"))?;
            if value > integer_mask(kind.bits) {
                return Err(runtime(span, "integer value is outside its declared type"));
            }
            value
        }
        Value::IntegerLiteral {
            negative,
            magnitude,
        } => {
            if negative {
                if !kind.signed {
                    return Err(runtime(span, "negative value has an unsigned integer type"));
                }
                let minimum_magnitude = 1_u128 << (kind.bits - 1);
                if magnitude > minimum_magnitude {
                    return Err(runtime(span, "integer value is outside its declared type"));
                }
                0_u128.wrapping_sub(magnitude) & integer_mask(kind.bits)
            } else {
                let maximum = if kind.signed {
                    (1_u128 << (kind.bits - 1)) - 1
                } else {
                    integer_mask(kind.bits)
                };
                if magnitude > maximum {
                    return Err(runtime(span, "integer value is outside its declared type"));
                }
                magnitude
            }
        }
        Value::Integer { raw, .. } => raw,
        value => {
            return Err(runtime(
                span,
                format!("expected an integer value, received `{value:?}`"),
            ));
        }
    };
    if kind
        == (IntegerKind {
            signed: true,
            bits: 64,
        })
    {
        Ok(Value::Int(signed_integer(raw, 64) as i64))
    } else {
        Ok(Value::Integer {
            signed: kind.signed,
            bits: kind.bits,
            raw,
        })
    }
}

fn coerce_declared_integer(
    value: Value,
    kind: IntegerKind,
    span: Span,
) -> Result<Value, Diagnostic> {
    let value = coerce_integer(value, kind, span)?;
    if kind
        == (IntegerKind {
            signed: true,
            bits: 64,
        })
    {
        let Value::Int(value) = value else {
            unreachable!("i64 coercion must use the compatibility integer representation")
        };
        Ok(Value::Integer {
            signed: true,
            bits: 64,
            raw: value as u128,
        })
    } else {
        Ok(value)
    }
}

fn typed_integer_kind(value: &Value) -> Option<IntegerKind> {
    match value {
        Value::Int(_) => Some(IntegerKind {
            signed: true,
            bits: 64,
        }),
        Value::Integer { signed, bits, .. } => Some(IntegerKind {
            signed: *signed,
            bits: *bits,
        }),
        _ => None,
    }
}

fn compare_integer_values(
    op: BinaryOp,
    lhs: Value,
    rhs: Value,
    span: Span,
) -> Result<Option<bool>, Diagnostic> {
    let (Some(left_kind), Some(right_kind)) = (typed_integer_kind(&lhs), typed_integer_kind(&rhs))
    else {
        return Ok(None);
    };
    let kind = match (&lhs, &rhs) {
        (Value::Integer { .. }, Value::Int(_)) => left_kind,
        (Value::Int(_), Value::Integer { .. }) => right_kind,
        _ if left_kind == right_kind => left_kind,
        _ => {
            return Err(runtime(
                span,
                "integer operands have different source-declared types",
            ));
        }
    };
    let lhs = coerce_integer(lhs, kind, span)?;
    let rhs = coerce_integer(rhs, kind, span)?;
    let raw = |value: Value| match value {
        Value::Int(value) => value as u128,
        Value::Integer { raw, .. } => raw,
        _ => unreachable!("integer coercion returned a non-integer"),
    };
    let (left, right) = (raw(lhs), raw(rhs));
    use BinaryOp::*;
    let result = if kind.signed {
        let (left, right) = (
            signed_integer(left, kind.bits),
            signed_integer(right, kind.bits),
        );
        match op {
            Eq => left == right,
            NotEq => left != right,
            Lt => left < right,
            LtEq => left <= right,
            Gt => left > right,
            GtEq => left >= right,
            _ => return Ok(None),
        }
    } else {
        match op {
            Eq => left == right,
            NotEq => left != right,
            Lt => left < right,
            LtEq => left <= right,
            Gt => left > right,
            GtEq => left >= right,
            _ => return Ok(None),
        }
    };
    Ok(Some(result))
}

fn arithmetic_integer_values(
    op: BinaryOp,
    lhs: Value,
    rhs: Value,
    span: Span,
) -> Result<Option<Value>, Diagnostic> {
    if !matches!(lhs, Value::Integer { .. }) && !matches!(rhs, Value::Integer { .. }) {
        return Ok(None);
    }
    let left_kind = typed_integer_kind(&lhs).expect("typed integer operand");
    let right_kind = typed_integer_kind(&rhs).expect("typed integer operand");
    let kind = match (&lhs, &rhs) {
        (Value::Integer { .. }, Value::Int(_)) => left_kind,
        (Value::Int(_), Value::Integer { .. }) => right_kind,
        _ if left_kind == right_kind => left_kind,
        _ => {
            return Err(runtime(
                span,
                "integer operands have different source-declared types",
            ));
        }
    };
    let raw = |value: Value| -> Result<u128, Diagnostic> {
        match coerce_integer(value, kind, span)? {
            Value::Int(value) => Ok(value as u128 & integer_mask(kind.bits)),
            Value::Integer { raw, .. } => Ok(raw),
            _ => unreachable!("integer coercion returned a non-integer"),
        }
    };
    let (left, right) = (raw(lhs)?, raw(rhs)?);
    use BinaryOp::*;
    let result = if kind.signed {
        let (left, right) = (
            signed_integer(left, kind.bits),
            signed_integer(right, kind.bits),
        );
        let minimum = if kind.bits == 128 {
            i128::MIN
        } else {
            -(1_i128 << (kind.bits - 1))
        };
        if matches!(op, Div | Rem) && left == minimum && right == -1 {
            return Err(runtime(span, "integer arithmetic overflowed"));
        }
        let result = match op {
            Add => left.checked_add(right),
            Sub => left.checked_sub(right),
            Mul => left.checked_mul(right),
            Div if right == 0 => return Err(runtime(span, "division by zero")),
            Div => left.checked_div(right),
            Rem if right == 0 => return Err(runtime(span, "remainder by zero")),
            Rem => left.checked_rem(right),
            _ => return Ok(None),
        }
        .ok_or_else(|| runtime(span, "integer arithmetic overflowed"))?;
        let (minimum, maximum) = if kind.bits == 128 {
            (i128::MIN, i128::MAX)
        } else {
            let limit = 1_i128 << (kind.bits - 1);
            (-limit, limit - 1)
        };
        if result < minimum || result > maximum {
            return Err(runtime(span, "integer arithmetic overflowed"));
        }
        result as u128 & integer_mask(kind.bits)
    } else {
        match op {
            Add => left.checked_add(right),
            Sub => left.checked_sub(right),
            Mul => left.checked_mul(right),
            Div if right == 0 => return Err(runtime(span, "division by zero")),
            Div => left.checked_div(right),
            Rem if right == 0 => return Err(runtime(span, "remainder by zero")),
            Rem => left.checked_rem(right),
            _ => return Ok(None),
        }
        .filter(|result| *result <= integer_mask(kind.bits))
        .ok_or_else(|| runtime(span, "integer arithmetic overflowed"))?
    };
    Ok(Some(Value::Integer {
        signed: kind.signed,
        bits: kind.bits,
        raw: result,
    }))
}

fn binary(op: BinaryOp, lhs: Value, rhs: Value, span: Span) -> Result<Value, Diagnostic> {
    use BinaryOp::*;
    if matches!(op, Add | Sub | Mul | Div | Rem)
        && let Some(result) = arithmetic_integer_values(op, lhs.clone(), rhs.clone(), span)?
    {
        return Ok(result);
    }
    if matches!(op, Eq | NotEq | Lt | LtEq | Gt | GtEq)
        && let Some(result) = compare_integer_values(op, lhs.clone(), rhs.clone(), span)?
    {
        return Ok(truth(result));
    }
    match (op, lhs, rhs) {
        (Add, Value::Int(a), Value::Int(b)) => a
            .checked_add(b)
            .map(Value::Int)
            .ok_or_else(|| runtime(span, "integer addition overflowed")),
        (Add, Value::String(a), Value::String(b)) => {
            Ok(Value::String(TextRef(Text::concatenate(a.0, b.0))))
        }
        (Sub, Value::Int(a), Value::Int(b)) => a
            .checked_sub(b)
            .map(Value::Int)
            .ok_or_else(|| runtime(span, "integer subtraction overflowed")),
        (Mul, Value::Int(a), Value::Int(b)) => a
            .checked_mul(b)
            .map(Value::Int)
            .ok_or_else(|| runtime(span, "integer multiplication overflowed")),
        (Div, Value::Int(_), Value::Int(0)) => Err(runtime(span, "division by zero")),
        (Div, Value::Int(a), Value::Int(b)) => a
            .checked_div(b)
            .map(Value::Int)
            .ok_or_else(|| runtime(span, "integer division overflowed")),
        (Rem, Value::Int(_), Value::Int(0)) => Err(runtime(span, "remainder by zero")),
        (Rem, Value::Int(a), Value::Int(b)) => a
            .checked_rem(b)
            .map(Value::Int)
            .ok_or_else(|| runtime(span, "integer remainder overflowed")),
        (Eq, a, b) => Ok(truth(a == b)),
        (NotEq, a, b) => Ok(truth(a != b)),
        (Lt, Value::Int(a), Value::Int(b)) => Ok(truth(a < b)),
        (LtEq, Value::Int(a), Value::Int(b)) => Ok(truth(a <= b)),
        (Gt, Value::Int(a), Value::Int(b)) => Ok(truth(a > b)),
        (GtEq, Value::Int(a), Value::Int(b)) => Ok(truth(a >= b)),
        (operator, lhs, rhs) => Err(runtime(
            span,
            format!("operator {operator:?} does not accept `{lhs:?}` and `{rhs:?}`"),
        )),
    }
}

fn truth(value: bool) -> Value {
    Value::Enum {
        name: "Result".into(),
        variant: if value { "Ok" } else { "Err" }.into(),
        fields: Rc::new(vec![Value::Unit]),
    }
}

fn is_truth(value: &Value) -> bool {
    matches!(value, Value::Enum { name, variant, .. } if name.as_ref() == "Result" && variant.as_ref() == "Ok")
}

fn is_falsehood(value: &Value) -> bool {
    matches!(value, Value::Enum { name, variant, .. } if name.as_ref() == "Result" && variant.as_ref() == "Err")
}

fn runtime(span: Span, message: impl Into<String>) -> Diagnostic {
    Diagnostic::error("runtime error", message, span)
}

fn decode_compiler_diagnostic(value: &Value, call_span: Span) -> Result<Diagnostic, Diagnostic> {
    let fields = struct_fields(value, "CompilerDiagnostic", call_span)?;
    let severity = field(fields, "severity", call_span)?;
    let severity = match severity {
        Value::Enum {
            name,
            variant,
            fields,
        } if name.as_ref() == "DiagnosticSeverity" && fields.is_empty() => variant.as_ref(),
        value => {
            return Err(runtime(
                call_span,
                format!(
                    "compiler diagnostic field `severity` must be DiagnosticSeverity, received `{value:?}`"
                ),
            ));
        }
    };
    let code = string_field(fields, "code", call_span)?;
    let title = string_field(fields, "title", call_span)?;
    let message = string_field(fields, "message", call_span)?;
    let help = string_field(fields, "help", call_span)?;
    let note = string_field(fields, "note", call_span)?;

    let source_fields =
        struct_fields(field(fields, "source", call_span)?, "SourceFile", call_span)?;
    let path = string_field(source_fields, "path", call_span)?;
    let source = string_field(source_fields, "text", call_span)?;
    let source_len = source.len();
    let primary = decode_source_span(
        field(fields, "primary", call_span)?,
        source.len(),
        call_span,
    )?;

    let diagnostic = match severity {
        "Error" => Diagnostic::error(title, message, primary),
        "Warning" => Diagnostic::warning(title, message, primary),
        "Advice" => Diagnostic::advice(title, message, primary),
        variant => {
            return Err(runtime(
                call_span,
                format!("unknown diagnostic severity `{variant}`"),
            ));
        }
    };
    let mut diagnostic = diagnostic
        .with_code(code)
        .with_help(help)
        .with_note(note)
        .with_embedded_source(path, source);
    let secondary = field(fields, "secondary", call_span)?;
    let Value::List(labels) = secondary else {
        return Err(runtime(
            call_span,
            "compiler diagnostic field `secondary` must be a list",
        ));
    };
    for label in labels {
        let label_fields = struct_fields(label, "DiagnosticLabel", call_span)?;
        let span = decode_source_span(
            field(label_fields, "span", call_span)?,
            source_len,
            call_span,
        )?;
        let message = string_field(label_fields, "message", call_span)?;
        diagnostic = diagnostic.with_related(span, message);
    }
    Ok(diagnostic)
}

fn struct_fields<'a>(
    value: &'a Value,
    expected: &str,
    span: Span,
) -> Result<&'a HashMap<String, Value>, Diagnostic> {
    match value {
        Value::Struct { name, fields } if name.as_ref() == expected => Ok(fields.as_ref()),
        _ => Err(runtime(
            span,
            format!("Diagnostics::abort expected `{expected}`, received `{value:?}`"),
        )),
    }
}

fn field<'a>(
    fields: &'a HashMap<String, Value>,
    name: &str,
    span: Span,
) -> Result<&'a Value, Diagnostic> {
    fields.get(name).ok_or_else(|| {
        runtime(
            span,
            format!("compiler diagnostic is missing field `{name}`"),
        )
    })
}

fn string_field(
    fields: &HashMap<String, Value>,
    name: &str,
    span: Span,
) -> Result<String, Diagnostic> {
    match field(fields, name, span)? {
        Value::String(value) => Ok(value.to_string()),
        value => Err(runtime(
            span,
            format!("compiler diagnostic field `{name}` must be String, received `{value:?}`"),
        )),
    }
}

fn decode_source_span(
    value: &Value,
    source_len: usize,
    call_span: Span,
) -> Result<Span, Diagnostic> {
    let fields = struct_fields(value, "SourceSpan", call_span)?;
    let Value::Int(start) = field(fields, "start", call_span)? else {
        return Err(runtime(call_span, "source span `start` must be i64"));
    };
    let Value::Int(end) = field(fields, "end", call_span)? else {
        return Err(runtime(call_span, "source span `end` must be i64"));
    };
    let start = usize::try_from(*start).unwrap_or(0).min(source_len);
    let end = usize::try_from(*end)
        .unwrap_or(start)
        .clamp(start, source_len);
    Ok(Span::new(start, end))
}

#[cfg(test)]
mod array_runtime_tests {
    use super::*;

    const TEST_SPAN: Span = Span { start: 1, end: 2 };

    fn call(primitive: Primitive, args: &[Value]) -> Result<Value, Diagnostic> {
        eval_runtime_primitive(primitive, args, TEST_SPAN)
    }

    fn array_reference(array: &Value, unique: bool) -> Value {
        Value::Reference {
            value: Rc::new(RefCell::new(array.clone())),
            unique,
        }
    }

    fn typed_integer(kind: IntegerKind, raw: u128) -> Value {
        Value::Integer {
            signed: kind.signed,
            bits: kind.bits,
            raw: raw & integer_mask(kind.bits),
        }
    }

    fn float_call(leaf: FloatRuntimeLeaf, args: &[Value]) -> Result<Value, Diagnostic> {
        eval_runtime_float_primitive(leaf, args, TEST_SPAN)
    }

    #[test]
    fn recovery_float_arithmetic_and_comparisons_are_width_exact() {
        for primitive in [
            Primitive::FloatAdd,
            Primitive::FloatSub,
            Primitive::FloatMul,
            Primitive::FloatDiv,
            Primitive::FloatRem,
        ] {
            let result = float_call(
                FloatRuntimeLeaf::Binary {
                    primitive,
                    width: FloatKind::F32,
                },
                &[Value::Float32(7.0), Value::Float32(2.0)],
            )
            .unwrap();
            let expected = match primitive {
                Primitive::FloatAdd => 9.0,
                Primitive::FloatSub => 5.0,
                Primitive::FloatMul => 14.0,
                Primitive::FloatDiv => 3.5,
                Primitive::FloatRem => 1.0,
                _ => unreachable!(),
            };
            assert_eq!(result, Value::Float32(expected));
        }
        assert_eq!(
            float_call(
                FloatRuntimeLeaf::Binary {
                    primitive: Primitive::FloatAdd,
                    width: FloatKind::F32,
                },
                &[Value::Float32(16_777_216.0), Value::Float32(1.0)],
            )
            .unwrap(),
            Value::Float32(16_777_216.0)
        );
        assert_eq!(
            float_call(
                FloatRuntimeLeaf::Unary {
                    primitive: Primitive::FloatNeg,
                    width: FloatKind::F64,
                },
                &[Value::Float(3.5)],
            )
            .unwrap(),
            Value::Float(-3.5)
        );
        for (primitive, expected) in [
            (Primitive::FloatEq, false),
            (Primitive::FloatNe, true),
            (Primitive::FloatLt, false),
            (Primitive::FloatLe, false),
            (Primitive::FloatGt, false),
            (Primitive::FloatGe, false),
        ] {
            assert_eq!(
                float_call(
                    FloatRuntimeLeaf::Comparison {
                        primitive,
                        width: FloatKind::F64,
                    },
                    &[Value::Float(f64::NAN), Value::Float(0.0)],
                )
                .unwrap(),
                typed_integer(
                    IntegerKind {
                        signed: false,
                        bits: 32,
                    },
                    u128::from(expected),
                )
            );
        }
    }

    #[test]
    fn recovery_float_bits_canonicalize_nan_and_preserve_signed_zero() {
        for (width, value, expected) in [
            (FloatKind::F32, Value::Float32(-0.0), 0x8000_0000_u128),
            (
                FloatKind::F32,
                Value::Float32(f32::from_bits(0x7fa1_2345)),
                0x7fc0_0000,
            ),
            (FloatKind::F64, Value::Float(-0.0), 0x8000_0000_0000_0000),
            (
                FloatKind::F64,
                Value::Float(f64::from_bits(0x7ff0_0000_0000_0001)),
                0x7ff8_0000_0000_0000,
            ),
        ] {
            let bits = float_call(FloatRuntimeLeaf::ToBits { source: width }, &[value]).unwrap();
            let bits_kind = IntegerKind {
                signed: false,
                bits: if width == FloatKind::F32 { 32 } else { 64 },
            };
            assert_eq!(bits, typed_integer(bits_kind, expected));
            let roundtrip =
                float_call(FloatRuntimeLeaf::FromBits { target: width }, &[bits]).unwrap();
            match (width, roundtrip) {
                (FloatKind::F32, Value::Float32(value)) => {
                    assert_eq!(u128::from(value.to_bits()), expected)
                }
                (FloatKind::F64, Value::Float(value)) => {
                    assert_eq!(u128::from(value.to_bits()), expected)
                }
                _ => panic!("wrong recovered float width"),
            }
        }
    }

    #[test]
    fn recovery_float_integer_conversions_cover_every_g1_width_and_boundaries() {
        let integer_kinds = [
            IntegerKind {
                signed: false,
                bits: 8,
            },
            IntegerKind {
                signed: false,
                bits: 16,
            },
            IntegerKind {
                signed: false,
                bits: 32,
            },
            IntegerKind {
                signed: false,
                bits: 64,
            },
            IntegerKind {
                signed: false,
                bits: 128,
            },
            IntegerKind {
                signed: true,
                bits: 8,
            },
            IntegerKind {
                signed: true,
                bits: 16,
            },
            IntegerKind {
                signed: true,
                bits: 32,
            },
            IntegerKind {
                signed: true,
                bits: 64,
            },
            IntegerKind {
                signed: true,
                bits: 128,
            },
        ];
        for kind in integer_kinds {
            let raw = if kind.signed {
                (-37_i128) as u128 & integer_mask(kind.bits)
            } else {
                37
            };
            for target in [FloatKind::F32, FloatKind::F64] {
                let converted = float_call(
                    FloatRuntimeLeaf::IntToFloat {
                        source: kind,
                        target,
                    },
                    &[typed_integer(kind, raw)],
                )
                .unwrap();
                let expected = if kind.signed { -37.0 } else { 37.0 };
                match converted {
                    Value::Float32(value) => assert_eq!(value, expected as f32),
                    Value::Float(value) => assert_eq!(value, expected),
                    _ => panic!("integer conversion returned a non-float"),
                }
            }
            let converted = float_call(
                FloatRuntimeLeaf::FloatToIntChecked {
                    source: FloatKind::F64,
                    target: kind,
                },
                &[Value::Float(if kind.signed { -37.75 } else { 37.75 })],
            )
            .unwrap();
            assert_eq!(converted, typed_integer(kind, raw));

            let limit = if kind.signed {
                2_f64.powi(i32::from(kind.bits - 1))
            } else {
                2_f64.powi(i32::from(kind.bits))
            };
            assert!(
                float_call(
                    FloatRuntimeLeaf::FloatToIntChecked {
                        source: FloatKind::F64,
                        target: kind,
                    },
                    &[Value::Float(limit)],
                )
                .unwrap_err()
                .message
                .contains("out of range")
            );
        }
        for hostile in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
            assert!(
                float_call(
                    FloatRuntimeLeaf::FloatToIntChecked {
                        source: FloatKind::F64,
                        target: IntegerKind {
                            signed: true,
                            bits: 64,
                        },
                    },
                    &[Value::Float(hostile)],
                )
                .is_err()
            );
        }

        assert_eq!(
            float_call(
                FloatRuntimeLeaf::Convert {
                    source: FloatKind::F32,
                    target: FloatKind::F64,
                },
                &[Value::Float32(0.1)],
            )
            .unwrap(),
            Value::Float(f64::from(0.1_f32))
        );
    }

    #[test]
    fn recovery_float_leaf_power_follows_exact_trusted_declaration_identity() {
        struct NoHost;
        impl Host for NoHost {
            fn perform(
                &mut self,
                _effect: &str,
                _operation: &str,
                _args: Vec<Value>,
                span: Span,
            ) -> Result<Value, Diagnostic> {
                Err(runtime(span, "unexpected host operation"))
            }
        }

        let bundle = crate::SourceBundle::raw_with_trusted_standard_for_conformance(
            crate::Segment::new(
                "trusted.glorious",
                "__g1_f32_add(left: f32, right: f32) -> f32 { () }
                 probe() -> f32 { __g1_f32_add(16777216.0, 1.0) }",
            ),
            crate::Segment::new("main.glorious", "main() -> { () }"),
            [],
        );
        let value = crate::run_bundle_entry_with_manifest_for_conformance(
            &bundle,
            "probe",
            &mut NoHost,
            &crate::compiler_traits::TrustedTraitManifest::trusted_distribution(),
        )
        .unwrap();
        assert_eq!(value, Value::Float32(16_777_216.0));

        // The same spelling in user code remains an ordinary function: its
        // body executes and does not acquire primitive authority by name.
        let untrusted = crate::SourceBundle::raw_with_trusted_standard_for_conformance(
            crate::Segment::new("trusted.glorious", "main() -> { () }"),
            crate::Segment::new(
                "user.glorious",
                "__g1_f32_add(left: f32, right: f32) -> f32 { left }
                 probe() -> f32 { __g1_f32_add(2.0, 3.0) }",
            ),
            [],
        );
        let value = crate::run_bundle_entry_with_manifest_for_conformance(
            &untrusted,
            "probe",
            &mut NoHost,
            &crate::compiler_traits::TrustedTraitManifest::trusted_distribution(),
        )
        .unwrap();
        assert_eq!(value, Value::Float32(2.0));
    }

    #[test]
    fn recovery_character_primitives_accept_scalars_and_reject_hostile_values() {
        let grin = typed_integer(
            IntegerKind {
                signed: false,
                bits: 32,
            },
            0x1F600,
        );
        assert_eq!(
            call(Primitive::CharFromU32Checked, &[grin]).unwrap(),
            Value::Char('😀')
        );
        assert_eq!(
            call(Primitive::CharToU32, &[Value::Char('€')]).unwrap(),
            typed_integer(
                IntegerKind {
                    signed: false,
                    bits: 32,
                },
                0x20AC,
            )
        );

        for scalar in [0xD800, 0x11_0000] {
            let hostile = typed_integer(
                IntegerKind {
                    signed: false,
                    bits: 32,
                },
                scalar,
            );
            assert!(call(Primitive::CharFromU32Checked, &[hostile]).is_err());
        }
        assert!(call(Primitive::CharToU32, &[Value::Int(65)]).is_err());
    }

    #[test]
    fn recovery_evaluator_pattern_test_is_observational_and_returns_source_bool() {
        struct NoHost;
        impl Host for NoHost {
            fn perform(
                &mut self,
                _effect: &str,
                _operation: &str,
                _args: Vec<Value>,
                span: Span,
            ) -> Result<Value, Diagnostic> {
                Err(runtime(span, "unexpected host operation"))
            }
        }

        let program = crate::parser::parse(
            crate::lexer::lex(
                "enum Choice { Yes(i64), No }
                 main() -> Bool { Choice::Yes(42) is Choice::Yes(found) }",
            )
            .unwrap(),
        )
        .unwrap();
        let value = run(&program, vec![], &mut NoHost).unwrap();
        assert!(is_truth(&value), "{value:?}");
    }

    #[test]
    fn integer_conversion_primitives_cover_every_recovery_width_and_sign_pair() {
        let kinds = [8, 16, 32, 64, 128]
            .into_iter()
            .flat_map(|bits| {
                [false, true]
                    .into_iter()
                    .map(move |signed| IntegerKind { signed, bits })
            })
            .collect::<Vec<_>>();
        for source in &kinds {
            let values = if source.signed {
                vec![
                    1_u128 << (source.bits - 1),
                    integer_mask(source.bits),
                    0,
                    (1_u128 << (source.bits - 1)) - 1,
                ]
            } else {
                vec![0, 1, integer_mask(source.bits)]
            };
            for target in &kinds {
                for raw in &values {
                    let input = typed_integer(*source, *raw);
                    let wrapped = eval_runtime_integer_conversion(
                        Primitive::IntConvertWrapping,
                        *target,
                        std::slice::from_ref(&input),
                        TEST_SPAN,
                    )
                    .unwrap();
                    let mathematical_raw = if source.signed {
                        signed_integer(*raw, source.bits) as u128
                    } else {
                        *raw
                    };
                    assert_eq!(
                        wrapped,
                        typed_integer(*target, mathematical_raw),
                        "wrapping {source:?} -> {target:?} for {raw:#x}"
                    );

                    let representable = if source.signed {
                        let value = signed_integer(*raw, source.bits);
                        if target.signed {
                            let (minimum, maximum) = if target.bits == 128 {
                                (i128::MIN, i128::MAX)
                            } else {
                                let limit = 1_i128 << (target.bits - 1);
                                (-limit, limit - 1)
                            };
                            (minimum..=maximum).contains(&value)
                        } else {
                            value >= 0 && (value as u128) <= integer_mask(target.bits)
                        }
                    } else if target.signed {
                        let maximum = if target.bits == 128 {
                            i128::MAX as u128
                        } else {
                            (1_u128 << (target.bits - 1)) - 1
                        };
                        *raw <= maximum
                    } else {
                        *raw <= integer_mask(target.bits)
                    };
                    let checked = eval_runtime_integer_conversion(
                        Primitive::IntConvertChecked,
                        *target,
                        &[input],
                        TEST_SPAN,
                    );
                    assert_eq!(
                        checked.is_ok(),
                        representable,
                        "checked {source:?} -> {target:?} for {raw:#x}"
                    );
                }
            }
        }
    }

    #[test]
    fn integer_comparisons_preserve_every_source_width_and_signedness() {
        use BinaryOp::*;
        for bits in [8, 16, 32, 64, 128] {
            for signed in [false, true] {
                let kind = IntegerKind { signed, bits };
                let (low, high) = if signed {
                    (1_u128 << (bits - 1), (1_u128 << (bits - 1)) - 1)
                } else {
                    (0, integer_mask(bits))
                };
                let low = typed_integer(kind, low);
                let high = typed_integer(kind, high);
                for (op, expected) in [
                    (Eq, false),
                    (NotEq, true),
                    (Lt, true),
                    (LtEq, true),
                    (Gt, false),
                    (GtEq, false),
                ] {
                    assert_eq!(
                        compare_integer_values(op, low.clone(), high.clone(), TEST_SPAN).unwrap(),
                        Some(expected),
                        "{op:?} must respect signed={signed}, bits={bits}",
                    );
                }
                assert_eq!(
                    compare_integer_values(Eq, high.clone(), high, TEST_SPAN).unwrap(),
                    Some(true),
                );
            }
        }

        // usize/isize use the frozen 64-bit G1 model, which is covered by the
        // two 64-bit rows above rather than the host Rust pointer width.
    }

    #[test]
    fn typed_integer_context_lifts_literals_without_erasing_unsigned_order() {
        let u128_kind = IntegerKind {
            signed: false,
            bits: 128,
        };
        let maximum = typed_integer(u128_kind, u128::MAX);
        assert_eq!(
            compare_integer_values(BinaryOp::Lt, Value::Int(1), maximum, TEST_SPAN,).unwrap(),
            Some(true),
        );
        assert!(
            coerce_integer(Value::Int(-1), u128_kind, TEST_SPAN)
                .unwrap_err()
                .message
                .contains("negative")
        );
    }

    #[test]
    fn recovery_checked_arithmetic_preserves_typed_integer_kinds_and_traps() {
        use BinaryOp::*;
        for bits in [8, 16, 32, 64, 128] {
            for signed in [false, true] {
                let kind = IntegerKind { signed, bits };
                let left = typed_integer(kind, 23);
                let right = typed_integer(kind, 5);
                for (op, expected) in [(Add, 28), (Sub, 18), (Mul, 115), (Div, 4), (Rem, 3)] {
                    assert_eq!(
                        arithmetic_integer_values(op, left.clone(), right.clone(), TEST_SPAN)
                            .unwrap(),
                        Some(typed_integer(kind, expected)),
                        "{op:?} must preserve signed={signed}, bits={bits}",
                    );
                }

                if signed {
                    let negative = typed_integer(kind, integer_mask(bits) - 22);
                    assert_eq!(
                        arithmetic_integer_values(Rem, negative, right.clone(), TEST_SPAN).unwrap(),
                        Some(typed_integer(kind, integer_mask(bits) - 2)),
                        "signed remainder must preserve the dividend's sign at {bits} bits",
                    );
                }

                let zero = typed_integer(kind, 0);
                for op in [Div, Rem] {
                    assert!(
                        arithmetic_integer_values(op, left.clone(), zero.clone(), TEST_SPAN)
                            .unwrap_err()
                            .message
                            .contains("zero")
                    );
                }

                if signed {
                    let minimum = typed_integer(kind, 1_u128 << (bits - 1));
                    let negative_one = typed_integer(kind, integer_mask(bits));
                    for op in [Div, Rem] {
                        assert!(
                            arithmetic_integer_values(
                                op,
                                minimum.clone(),
                                negative_one.clone(),
                                TEST_SPAN
                            )
                            .unwrap_err()
                            .message
                            .contains("overflow")
                        );
                    }
                }
            }
        }

        let u128_kind = IntegerKind {
            signed: false,
            bits: 128,
        };
        let huge = (1_u128 << 127) + 123_456_789;
        let divisor = 97_u128;
        assert_eq!(
            arithmetic_integer_values(
                Rem,
                typed_integer(u128_kind, huge),
                typed_integer(u128_kind, divisor),
                TEST_SPAN,
            )
            .unwrap(),
            Some(typed_integer(u128_kind, huge % divisor)),
            "recovery must not narrow u128 values through i128",
        );
    }

    #[test]
    fn declared_integer_widths_remain_distinct_from_each_other_but_not_literals() {
        let u8_value = coerce_declared_integer(
            Value::Int(1),
            IntegerKind {
                signed: false,
                bits: 8,
            },
            TEST_SPAN,
        )
        .unwrap();
        let i64_value = coerce_declared_integer(
            Value::Int(1),
            IntegerKind {
                signed: true,
                bits: 64,
            },
            TEST_SPAN,
        )
        .unwrap();
        assert!(matches!(
            i64_value,
            Value::Integer {
                signed: true,
                bits: 64,
                ..
            }
        ));
        assert!(
            compare_integer_values(BinaryOp::Eq, u8_value.clone(), i64_value, TEST_SPAN)
                .unwrap_err()
                .message
                .contains("different source-declared types")
        );
        assert_eq!(
            compare_integer_values(BinaryOp::Eq, u8_value, Value::Int(1), TEST_SPAN).unwrap(),
            Some(true),
            "an untyped literal is contextually interpreted as the typed operand",
        );
    }

    #[test]
    fn all_array_leaves_preserve_slots_borrows_and_frozen_capacity_growth() {
        let array = call(Primitive::ArrayEmpty, &[]).unwrap();
        let shared = array_reference(&array, false);
        let unique = array_reference(&array, true);
        assert_eq!(
            call(Primitive::ArrayLen, std::slice::from_ref(&shared)).unwrap(),
            Value::Int(0)
        );
        assert_eq!(
            call(Primitive::ArrayCapacity, std::slice::from_ref(&shared)).unwrap(),
            Value::Int(0)
        );

        call(Primitive::ArrayReserve, &[unique.clone(), Value::Int(3)]).unwrap();
        assert_eq!(
            call(Primitive::ArrayCapacity, std::slice::from_ref(&shared)).unwrap(),
            Value::Int(4)
        );
        call(Primitive::ArrayPushMove, &[unique.clone(), Value::Int(10)]).unwrap();
        assert_eq!(
            call(Primitive::ArrayLen, std::slice::from_ref(&shared)).unwrap(),
            Value::Int(1)
        );

        let borrowed = call(
            Primitive::ArrayGetBorrowUnique,
            &[unique.clone(), Value::Int(0)],
        )
        .unwrap();
        let Value::Reference {
            value,
            unique: true,
        } = borrowed
        else {
            panic!("unique element borrow must be represented as a unique reference");
        };
        *value.borrow_mut() = Value::Int(11);
        assert_eq!(
            call(
                Primitive::ArrayGetBorrowShared,
                &[shared.clone(), Value::Int(0)]
            )
            .unwrap(),
            Value::Reference {
                value: value.clone(),
                unique: false,
            }
        );
        assert_eq!(
            call(Primitive::ArrayGetCopy, &[shared.clone(), Value::Int(0)]).unwrap(),
            Value::Int(11)
        );
        assert_eq!(
            call(Primitive::ArrayGetMove, &[unique.clone(), Value::Int(0)]).unwrap(),
            Value::Int(11)
        );
        assert!(
            call(Primitive::ArrayGetCopy, &[shared.clone(), Value::Int(0)])
                .unwrap_err()
                .message
                .contains("empty")
        );

        call(
            Primitive::ArraySetMove,
            &[unique.clone(), Value::Int(0), Value::Int(12)],
        )
        .unwrap();
        assert!(
            call(
                Primitive::ArraySetMove,
                &[unique.clone(), Value::Int(0), Value::Int(13)]
            )
            .unwrap_err()
            .message
            .contains("already initialized")
        );
        assert_eq!(
            call(Primitive::ArrayPopMove, &[unique]).unwrap(),
            Value::Int(12)
        );
        assert_eq!(
            call(Primitive::ArrayFinishDrained, &[array]).unwrap(),
            Value::Unit
        );
    }

    #[test]
    fn filled_array_capacity_is_exact_and_finish_requires_every_slot_moved() {
        let array = call(Primitive::ArrayNew, &[Value::Int(3), Value::Int(7)]).unwrap();
        let shared = array_reference(&array, false);
        let unique = array_reference(&array, true);
        assert_eq!(
            call(Primitive::ArrayLen, std::slice::from_ref(&shared)).unwrap(),
            Value::Int(3)
        );
        assert_eq!(
            call(Primitive::ArrayCapacity, &[shared]).unwrap(),
            Value::Int(3)
        );
        assert!(
            call(Primitive::ArrayFinishDrained, std::slice::from_ref(&array))
                .unwrap_err()
                .message
                .contains("not fully drained")
        );
        for index in 0..3 {
            assert_eq!(
                call(
                    Primitive::ArrayGetMove,
                    &[unique.clone(), Value::Int(index)]
                )
                .unwrap(),
                Value::Int(7)
            );
        }
        assert_eq!(
            call(Primitive::ArrayFinishDrained, &[array]).unwrap(),
            Value::Unit
        );
    }

    #[test]
    fn push_and_reserve_follow_minimum_four_and_power_of_two_growth() {
        let array = call(Primitive::ArrayNew, &[Value::Int(3), Value::Int(1)]).unwrap();
        let shared = array_reference(&array, false);
        let unique = array_reference(&array, true);
        call(Primitive::ArrayReserve, &[unique.clone(), Value::Int(2)]).unwrap();
        assert_eq!(
            call(Primitive::ArrayCapacity, std::slice::from_ref(&shared)).unwrap(),
            Value::Int(8)
        );
        call(Primitive::ArrayPushMove, &[unique, Value::Int(2)]).unwrap();
        assert_eq!(call(Primitive::ArrayLen, &[shared]).unwrap(), Value::Int(4));
    }

    #[test]
    fn text_and_bytes_leaves_match_frozen_scalar_and_binary_semantics() {
        let unicode = Value::String("a😀".into());
        assert_eq!(
            call(Primitive::TextByteLen, std::slice::from_ref(&unicode)).unwrap(),
            Value::Int(5)
        );
        assert_eq!(
            call(
                Primitive::TextConcat,
                &[Value::String("grand".into()), Value::String("iose".into())]
            )
            .unwrap(),
            Value::String("grandiose".into())
        );
        assert_eq!(
            call(
                Primitive::TextEq,
                &[Value::String("same".into()), Value::String("same".into())]
            )
            .unwrap(),
            Value::Int(1)
        );
        assert_eq!(
            call(
                Primitive::TextEq,
                &[Value::String("same".into()), Value::String("other".into())]
            )
            .unwrap(),
            Value::Int(0)
        );

        let raw = Value::Bytes(Rc::from(&b"hello"[..]));
        assert_eq!(
            call(Primitive::TextFromUtf8Checked, std::slice::from_ref(&raw)).unwrap(),
            Value::String("hello".into())
        );
        assert_eq!(
            call(Primitive::TextAsBytes, &[Value::String("hé".into())]).unwrap(),
            Value::Bytes(Rc::from(&b"h\xc3\xa9"[..]))
        );
        assert!(
            call(
                Primitive::TextFromUtf8Checked,
                &[Value::Bytes(Rc::from(&b"\xff"[..]))]
            )
            .unwrap_err()
            .message
            .contains("UTF-8")
        );

        assert_eq!(
            call(Primitive::BytesLen, std::slice::from_ref(&raw)).unwrap(),
            Value::Int(5)
        );
        assert_eq!(
            call(
                Primitive::BytesConcat,
                &[
                    Value::Bytes(Rc::from(&b"ab"[..])),
                    Value::Bytes(Rc::from(&b"cd"[..]))
                ]
            )
            .unwrap(),
            Value::Bytes(Rc::from(&b"abcd"[..]))
        );
        assert_eq!(
            call(Primitive::BytesGet, &[raw.clone(), Value::Int(1)]).unwrap(),
            Value::Int(i64::from(b'e'))
        );
        assert_eq!(
            call(
                Primitive::BytesSlice,
                &[raw.clone(), Value::Int(1), Value::Int(4)]
            )
            .unwrap(),
            Value::Bytes(Rc::from(&b"ell"[..]))
        );
        assert!(
            call(Primitive::BytesGet, &[raw.clone(), Value::Int(5)])
                .unwrap_err()
                .message
                .contains("out of bounds")
        );
        assert!(
            call(Primitive::BytesSlice, &[raw, Value::Int(4), Value::Int(1)])
                .unwrap_err()
                .message
                .contains("out of bounds")
        );
    }

    #[test]
    fn bytes_array_conversion_is_independent_exact_capacity_and_rejects_holes() {
        let bytes = Value::Bytes(Rc::from(&b"\0\x7f\xff"[..]));
        let array = call(Primitive::BytesToArray, std::slice::from_ref(&bytes)).unwrap();
        let shared = array_reference(&array, false);
        let unique = array_reference(&array, true);
        assert_eq!(
            call(Primitive::ArrayLen, std::slice::from_ref(&shared)).unwrap(),
            Value::Int(3)
        );
        assert_eq!(
            call(Primitive::ArrayCapacity, std::slice::from_ref(&shared)).unwrap(),
            Value::Int(3)
        );
        assert_eq!(
            call(Primitive::BytesFromArrayMove, std::slice::from_ref(&array)).unwrap(),
            bytes
        );

        assert_eq!(
            call(Primitive::ArrayGetMove, &[unique.clone(), Value::Int(0)]).unwrap(),
            Value::Int(0)
        );
        call(
            Primitive::ArraySetMove,
            &[unique.clone(), Value::Int(0), Value::Int(1)],
        )
        .unwrap();
        assert_eq!(
            call(Primitive::BytesFromArrayMove, std::slice::from_ref(&array)).unwrap(),
            Value::Bytes(Rc::from(&b"\x01\x7f\xff"[..]))
        );

        assert_eq!(
            call(Primitive::ArrayGetMove, &[unique, Value::Int(0)]).unwrap(),
            Value::Int(1)
        );
        assert!(
            call(Primitive::BytesFromArrayMove, &[array])
                .unwrap_err()
                .message
                .contains("empty")
        );

        // Converting to an Array copies the immutable bytes into mutable cells.
        assert_eq!(bytes, Value::Bytes(Rc::from(&b"\0\x7f\xff"[..])));
    }
}
