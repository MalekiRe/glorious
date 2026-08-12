//! Deterministic marker-trait coherence and ground-goal solving.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use grandiose_vm::Primitive;

use crate::ast::{
    AssociatedArgumentSyntax, ConstArgumentValueSyntax, ConstAssociatedArgumentSyntax, ConstKind,
    GenericParamKind, GoalArgument, GoalPolarity, ImplDecl, Program, QuantitySyntax, TraitDecl,
    TraitRefSyntax, TypeSyntax, TypeSyntaxKind,
};
use crate::compiler_typeck::{
    DeclarationKey, GenericParamKey, NominalInstanceKey, NominalKey, ProvisionalConst,
    ProvisionalType, predefined_runtime_use_interval, provisional_signature_type_any,
};
use crate::diagnostic::Diagnostic;

const MAX_DEPTH: usize = 128;
const MAX_ANSWERS_PER_TABLE: usize = 1_024;
const MAX_STEPS: usize = 1_000_000;
const MAX_PROJECTION_STEPS: usize = 256;
const MAX_TABLES: usize = 65_536;
pub(crate) const EFFECT_ROW_MEMBER_PREFIX: &str = "$effect_row_member$";
pub(crate) const EFFECT_ROW_TAIL_PREFIX: &str = "$effect_row_tail$";
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum TraitKey {
    /// Identity assigned by the trusted, out-of-band manifest.
    External(u64),
    /// Identity assigned to a source declaration.  The variant keeps a source
    /// declaration distinct from an equally-spelled external declaration.
    Local(String),
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum GenericParameterKind {
    Type,
    Lifetime,
    Const(ConstKind),
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ConstValue {
    Quantity { lower: u32, upper: Option<u32> },
    U32(u32),
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
// Canonical lifetime identities used by rigid goals and higher-ranked
// placeholder universes. Region inference remains a later ownership phase.
pub(crate) enum LifetimeArg {
    Static,
    #[allow(dead_code)]
    Rigid(u32),
    Placeholder {
        universe: u32,
        index: u32,
    },
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum GenericArg {
    Type(ProvisionalType),
    Lifetime(LifetimeArg),
    Const(ConstValue),
    RigidConst(u32, ConstKind),
}

fn const_value_kind(value: &ConstValue) -> ConstKind {
    match value {
        ConstValue::Quantity { .. } => ConstKind::Quantity,
        ConstValue::U32(_) => ConstKind::U32,
    }
}

fn generic_arg_has_const_kind(argument: &GenericArg, kind: ConstKind) -> bool {
    match argument {
        GenericArg::Const(value) => const_value_kind(value) == kind,
        GenericArg::RigidConst(_, actual) => *actual == kind,
        GenericArg::Type(_) | GenericArg::Lifetime(_) => false,
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AssociatedItemKind {
    Type,
    EffectRow,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TraitPolicy {
    CompilerSealed,
    ExternalOpen,
    DedicatedUse,
    DedicatedDrop,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum IntrinsicRole {
    Drop,
    Use,
    Fn,
    RunsIn,
    Label,
    Environment,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ManifestAssociatedItem {
    pub name: String,
    pub parameters: Vec<GenericParameterKind>,
    pub kind: AssociatedItemKind,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ManifestTrait {
    pub id: u64,
    pub display_name: String,
    pub parameters: Vec<GenericParameterKind>,
    pub associated_items: Vec<ManifestAssociatedItem>,
    pub policy: TraitPolicy,
    pub role: Option<IntrinsicRole>,
}

/// Frozen runtime type-constructor roles supplied out of band by the compiler
/// distribution. Source spelling is deliberately not part of the role.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum MachineTypeRole {
    Array,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ManifestMachineType {
    pub id: u64,
    pub display_name: String,
    pub parameters: Vec<GenericParameterKind>,
    pub role: MachineTypeRole,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ManifestPrimitiveLeaf {
    pub id: u64,
    pub display_name: String,
    pub primitive: Primitive,
}

/// Frozen host-import identities supplied by the compiler distribution.  The
/// source declaration name is only a lookup key inside the trusted standard
/// library segment; it is not itself authority.
#[derive(Clone, Copy, Debug, serde::Deserialize, Eq, Ord, PartialEq, PartialOrd, serde::Serialize)]
pub enum HostImportRole {
    ProcessArgsGet,
    FsRead,
    FsWrite,
    DiagnosticWrite,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ManifestHostImportLeaf {
    pub id: u64,
    pub display_name: String,
    pub role: HostImportRole,
}

/// The finite machine boundary. It contains declaration bindings, not source
/// keywords: a compiler only grants a leaf authority after resolving the named
/// declaration inside the explicitly trusted standard-library bundle entry.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct TrustedRuntimeManifest {
    machine_types: Vec<ManifestMachineType>,
    primitive_leaves: Vec<ManifestPrimitiveLeaf>,
    host_import_leaves: Vec<ManifestHostImportLeaf>,
}

impl TrustedRuntimeManifest {
    pub fn new(
        machine_types: Vec<ManifestMachineType>,
        primitive_leaves: Vec<ManifestPrimitiveLeaf>,
    ) -> Result<Self, Vec<Diagnostic>> {
        Self::with_host_imports(machine_types, primitive_leaves, vec![])
    }

    pub fn with_host_imports(
        mut machine_types: Vec<ManifestMachineType>,
        mut primitive_leaves: Vec<ManifestPrimitiveLeaf>,
        mut host_import_leaves: Vec<ManifestHostImportLeaf>,
    ) -> Result<Self, Vec<Diagnostic>> {
        machine_types.sort_by_key(|declaration| declaration.id);
        primitive_leaves.sort_by_key(|declaration| declaration.id);
        host_import_leaves.sort_by_key(|declaration| declaration.id);
        let mut errors = Vec::new();
        let mut ids = BTreeSet::new();
        let mut type_names = BTreeSet::new();
        let mut roles = BTreeSet::new();
        for declaration in &machine_types {
            if !ids.insert(declaration.id) {
                errors.push(Diagnostic::plain(format!(
                    "trusted runtime manifest contains duplicate id {}",
                    declaration.id
                )));
            }
            if declaration.display_name.is_empty() || !type_names.insert(&declaration.display_name)
            {
                errors.push(Diagnostic::plain(format!(
                    "trusted runtime manifest contains duplicate or empty machine type name `{}`",
                    declaration.display_name
                )));
            }
            if !roles.insert(declaration.role) {
                errors.push(Diagnostic::plain(format!(
                    "trusted runtime manifest contains duplicate machine type role {:?}",
                    declaration.role
                )));
            }
            let expected = match declaration.role {
                MachineTypeRole::Array => vec![GenericParameterKind::Type],
            };
            if declaration.parameters != expected {
                errors.push(Diagnostic::plain(format!(
                    "trusted machine type `{}` does not match the frozen {:?} schema",
                    declaration.display_name, declaration.role
                )));
            }
        }
        let mut leaf_names = BTreeSet::new();
        let mut primitives = BTreeSet::new();
        for declaration in &primitive_leaves {
            if !ids.insert(declaration.id) {
                errors.push(Diagnostic::plain(format!(
                    "trusted runtime manifest contains duplicate id {}",
                    declaration.id
                )));
            }
            if declaration.display_name.is_empty() || !leaf_names.insert(&declaration.display_name)
            {
                errors.push(Diagnostic::plain(format!(
                    "trusted runtime manifest contains duplicate or empty primitive leaf name `{}`",
                    declaration.display_name
                )));
            }
            let family = crate::builtins::runtime_primitive_family(declaration.primitive);
            if family.is_none() {
                errors.push(Diagnostic::plain(format!(
                    "trusted primitive leaf `{}` is outside the generation-1 Text/Bytes/Array frontend slice",
                    declaration.display_name
                )));
            }
            let repeatable_typed_float =
                family == Some(crate::builtins::RuntimePrimitiveFamily::TypedFloat);
            if !repeatable_typed_float && !primitives.insert(declaration.primitive as u32) {
                errors.push(Diagnostic::plain(format!(
                    "trusted runtime manifest contains duplicate primitive identity {:?}",
                    declaration.primitive
                )));
            } else {
                primitives.insert(declaration.primitive as u32);
            }
        }
        let requires_array = primitive_leaves.iter().any(|declaration| {
            crate::builtins::runtime_primitive_family(declaration.primitive)
                == Some(crate::builtins::RuntimePrimitiveFamily::ArrayDependent)
        });
        if requires_array && !roles.contains(&MachineTypeRole::Array) {
            errors.push(Diagnostic::plain(
                "trusted Array-dependent primitive leaves require one Array machine type constructor",
            ));
        }
        let mut host_roles = BTreeSet::new();
        for declaration in &host_import_leaves {
            if !ids.insert(declaration.id) {
                errors.push(Diagnostic::plain(format!(
                    "trusted runtime manifest contains duplicate id {}",
                    declaration.id
                )));
            }
            if declaration.display_name.is_empty() || !leaf_names.insert(&declaration.display_name)
            {
                errors.push(Diagnostic::plain(format!(
                    "trusted runtime manifest contains duplicate or empty host-import leaf name `{}`",
                    declaration.display_name
                )));
            }
            if !host_roles.insert(declaration.role) {
                errors.push(Diagnostic::plain(format!(
                    "trusted runtime manifest contains duplicate host-import role {:?}",
                    declaration.role
                )));
            }
        }
        if errors.is_empty() {
            Ok(Self {
                machine_types,
                primitive_leaves,
                host_import_leaves,
            })
        } else {
            Err(errors)
        }
    }

    pub fn empty() -> Self {
        Self::default()
    }

    /// Runtime identities shipped with the generation-1 distribution.  These
    /// names bind only declarations in the trusted embedded standard-library
    /// segment; spelling one in user source grants no primitive authority.
    pub fn distributed_generation_1() -> Self {
        let machine_types = vec![ManifestMachineType {
            id: 0x21,
            display_name: "Array".into(),
            parameters: vec![GenericParameterKind::Type],
            role: MachineTypeRole::Array,
        }];
        let leaves = crate::builtins::distributed_runtime_primitive_leaves()
            .into_iter()
            .map(|(id, display_name, primitive)| ManifestPrimitiveLeaf {
                id,
                display_name,
                primitive,
            })
            .collect::<Vec<_>>();
        let host_imports = [
            (
                0x0100,
                "__g1_process_args_get",
                HostImportRole::ProcessArgsGet,
            ),
            (0x0101, "__g1_fs_read", HostImportRole::FsRead),
            (0x0102, "__g1_fs_write", HostImportRole::FsWrite),
            (
                0x0103,
                "__g1_diagnostic_write",
                HostImportRole::DiagnosticWrite,
            ),
        ]
        .into_iter()
        .map(|(id, display_name, role)| ManifestHostImportLeaf {
            id,
            display_name: display_name.into(),
            role,
        })
        .collect();
        Self::with_host_imports(machine_types, leaves, host_imports)
            .expect("the built-in generation-1 runtime manifest is valid")
    }

    pub(crate) fn machine_type(&self, role: MachineTypeRole) -> Option<&ManifestMachineType> {
        self.machine_types
            .iter()
            .find(|declaration| declaration.role == role)
    }

    pub(crate) fn primitive_leaves(&self) -> &[ManifestPrimitiveLeaf] {
        &self.primitive_leaves
    }

    pub(crate) fn host_import_leaves(&self) -> &[ManifestHostImportLeaf] {
        &self.host_import_leaves
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TrustedTraitManifest {
    declarations: Vec<ManifestTrait>,
    runtime: TrustedRuntimeManifest,
}

impl TrustedTraitManifest {
    pub fn new(mut declarations: Vec<ManifestTrait>) -> Result<Self, Vec<Diagnostic>> {
        declarations.sort_by_key(|declaration| declaration.id);
        let mut errors = Vec::new();
        let mut ids = BTreeSet::new();
        let mut names = BTreeSet::new();
        let mut roles = BTreeSet::new();
        for declaration in &declarations {
            if !ids.insert(declaration.id) {
                errors.push(Diagnostic::plain(format!(
                    "trusted trait manifest contains duplicate id {}",
                    declaration.id
                )));
            }
            if declaration.display_name.is_empty() || !names.insert(&declaration.display_name) {
                errors.push(Diagnostic::plain(format!(
                    "trusted trait manifest contains duplicate or empty display name `{}`",
                    declaration.display_name
                )));
            }
            if let Some(role) = declaration.role
                && !roles.insert(role)
            {
                errors.push(Diagnostic::plain(format!(
                    "trusted trait manifest contains duplicate intrinsic role {role:?}"
                )));
            }
            let mut items = BTreeSet::new();
            for item in &declaration.associated_items {
                if item.name.is_empty() || !items.insert(&item.name) {
                    errors.push(Diagnostic::plain(format!(
                        "trusted trait `{}` contains duplicate or empty associated item `{}`",
                        declaration.display_name, item.name
                    )));
                }
            }
            let expected_policy = match declaration.role {
                Some(IntrinsicRole::Use) => TraitPolicy::DedicatedUse,
                Some(IntrinsicRole::Drop) => TraitPolicy::DedicatedDrop,
                Some(_) => TraitPolicy::CompilerSealed,
                None => declaration.policy,
            };
            if declaration.policy != expected_policy
                || (declaration.role.is_none()
                    && matches!(
                        declaration.policy,
                        TraitPolicy::DedicatedUse | TraitPolicy::DedicatedDrop
                    ))
            {
                errors.push(Diagnostic::plain(format!(
                    "trusted trait `{}` has a conflicting intrinsic role and policy",
                    declaration.display_name
                )));
            }
            if let Some(role) = declaration.role {
                let (parameters, items) = intrinsic_role_schema(role);
                if declaration.display_name != intrinsic_role_name(role)
                    || declaration.parameters != parameters
                    || declaration.associated_items != items
                {
                    errors.push(Diagnostic::plain(format!(
                        "trusted trait `{}` does not match the frozen {role:?} intrinsic schema",
                        declaration.display_name
                    )));
                }
            }
        }
        for role in [
            IntrinsicRole::Drop,
            IntrinsicRole::Use,
            IntrinsicRole::Fn,
            IntrinsicRole::RunsIn,
            IntrinsicRole::Label,
            IntrinsicRole::Environment,
        ] {
            if !roles.contains(&role) {
                errors.push(Diagnostic::plain(format!(
                    "trusted trait manifest is missing required intrinsic role {role:?}"
                )));
            }
        }
        if errors.is_empty() {
            Ok(Self {
                declarations,
                runtime: TrustedRuntimeManifest::empty(),
            })
        } else {
            Err(errors)
        }
    }

    pub fn trusted_default() -> Self {
        use GenericParameterKind::{Const, Lifetime, Type};
        let item = |name: &str, parameters, kind| ManifestAssociatedItem {
            name: name.into(),
            parameters,
            kind,
        };
        Self::new(vec![
            ManifestTrait {
                id: 1,
                display_name: "Drop".into(),
                parameters: vec![],
                associated_items: vec![],
                policy: TraitPolicy::DedicatedDrop,
                role: Some(IntrinsicRole::Drop),
            },
            ManifestTrait {
                id: 2,
                display_name: "Use".into(),
                parameters: vec![Const(ConstKind::Quantity)],
                associated_items: vec![],
                policy: TraitPolicy::DedicatedUse,
                role: Some(IntrinsicRole::Use),
            },
            ManifestTrait {
                id: 3,
                display_name: "Fn".into(),
                parameters: vec![Type],
                associated_items: vec![
                    item("Output", vec![], AssociatedItemKind::Type),
                    item("Effects", vec![], AssociatedItemKind::EffectRow),
                ],
                policy: TraitPolicy::CompilerSealed,
                role: Some(IntrinsicRole::Fn),
            },
            ManifestTrait {
                id: 4,
                display_name: "RunsIn".into(),
                parameters: vec![Type, Type],
                associated_items: vec![item("After", vec![], AssociatedItemKind::Type)],
                policy: TraitPolicy::CompilerSealed,
                role: Some(IntrinsicRole::RunsIn),
            },
            ManifestTrait {
                id: 5,
                display_name: "Label".into(),
                parameters: vec![Type],
                associated_items: vec![],
                policy: TraitPolicy::CompilerSealed,
                role: Some(IntrinsicRole::Label),
            },
            ManifestTrait {
                id: 6,
                display_name: "Environment".into(),
                parameters: vec![Lifetime],
                associated_items: vec![],
                policy: TraitPolicy::CompilerSealed,
                role: Some(IntrinsicRole::Environment),
            },
        ])
        .expect("the built-in trusted trait manifest is valid")
    }

    /// Complete authority set paired with the embedded distribution standard
    /// library. Conformance fixtures may continue to supply a deliberately
    /// smaller runtime manifest explicitly.
    pub fn trusted_distribution() -> Self {
        Self::trusted_default().with_runtime(TrustedRuntimeManifest::distributed_generation_1())
    }

    pub fn with_runtime(mut self, runtime: TrustedRuntimeManifest) -> Self {
        self.runtime = runtime;
        self
    }

    pub(crate) fn runtime(&self) -> &TrustedRuntimeManifest {
        &self.runtime
    }
}

fn intrinsic_role_name(role: IntrinsicRole) -> &'static str {
    match role {
        IntrinsicRole::Drop => "Drop",
        IntrinsicRole::Use => "Use",
        IntrinsicRole::Fn => "Fn",
        IntrinsicRole::RunsIn => "RunsIn",
        IntrinsicRole::Label => "Label",
        IntrinsicRole::Environment => "Environment",
    }
}

fn intrinsic_role_schema(
    role: IntrinsicRole,
) -> (Vec<GenericParameterKind>, Vec<ManifestAssociatedItem>) {
    use GenericParameterKind::{Const, Lifetime, Type};
    let item = |name: &str, kind| ManifestAssociatedItem {
        name: name.into(),
        parameters: vec![],
        kind,
    };
    match role {
        IntrinsicRole::Drop => (vec![], vec![]),
        IntrinsicRole::Use => (vec![Const(ConstKind::Quantity)], vec![]),
        IntrinsicRole::Fn => (
            vec![Type],
            vec![
                item("Output", AssociatedItemKind::Type),
                item("Effects", AssociatedItemKind::EffectRow),
            ],
        ),
        IntrinsicRole::RunsIn => (
            vec![Type, Type],
            vec![item("After", AssociatedItemKind::Type)],
        ),
        IntrinsicRole::Label => (vec![Type], vec![]),
        IntrinsicRole::Environment => (vec![Lifetime], vec![]),
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Pattern {
    Bound(u32),
    Ground(ProvisionalType),
    Nominal(NominalKey, Vec<NominalPatternArg>),
    Shared(Box<Pattern>),
    Unique(Box<Pattern>),
    Tuple(Vec<Pattern>),
    Projection {
        subject: Box<Pattern>,
        trait_key: TraitKey,
        arguments: Vec<GenericArgPattern>,
        item: String,
        item_arguments: Vec<GenericArgPattern>,
    },
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum NominalPatternArg {
    Type(Pattern),
    Const(ConstPattern),
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum ConstPattern {
    Bound(u32, ConstKind),
    Value(ConstValue),
}

const HIGHER_RANKED_CONST_FLAG: u32 = 1 << 31;

fn const_binder_pattern(binder: Binder, kind: ConstKind) -> ConstPattern {
    ConstPattern::Bound(
        binder.index
            | if binder.higher_ranked {
                HIGHER_RANKED_CONST_FLAG
            } else {
                0
            },
        kind,
    )
}

fn instantiate_bound_const(
    index: u32,
    kind: ConstKind,
    substitutions: &BTreeMap<u32, GenericArg>,
    universe: u32,
) -> Option<GenericArg> {
    if index & HIGHER_RANKED_CONST_FLAG == 0 {
        return substitutions
            .get(&index)
            .filter(|argument| generic_arg_has_const_kind(argument, kind))
            .cloned();
    }
    let binder = index & !HIGHER_RANKED_CONST_FLAG;
    Some(GenericArg::RigidConst(
        HIGHER_RANKED_CONST_FLAG | ((universe & 0x7fff) << 16) | (binder & 0xffff),
        kind,
    ))
}

fn encode_const_value(value: &ConstValue) -> ProvisionalType {
    ProvisionalType::Const(match value {
        ConstValue::U32(value) => ProvisionalConst::U32(*value),
        ConstValue::Quantity { lower, upper } => ProvisionalConst::Quantity {
            lower: *lower,
            upper: *upper,
        },
    })
}

fn encode_const_argument(argument: &GenericArg) -> Option<ProvisionalType> {
    match argument {
        GenericArg::Const(value) => Some(encode_const_value(value)),
        GenericArg::RigidConst(index, kind) => {
            Some(ProvisionalType::Const(ProvisionalConst::Rigid {
                index: *index,
                kind: *kind,
            }))
        }
        GenericArg::Type(_) | GenericArg::Lifetime(_) => None,
    }
}

fn decode_const_argument(ty: &ProvisionalType) -> Option<GenericArg> {
    Some(match ty {
        ProvisionalType::Const(ProvisionalConst::U32(value)) => {
            GenericArg::Const(ConstValue::U32(*value))
        }
        ProvisionalType::Const(ProvisionalConst::Quantity { lower, upper }) => {
            GenericArg::Const(ConstValue::Quantity {
                lower: *lower,
                upper: *upper,
            })
        }
        ProvisionalType::Const(ProvisionalConst::Rigid { index, kind }) => {
            GenericArg::RigidConst(*index, *kind)
        }
        _ => return None,
    })
}

fn instantiate_ground_pattern(ty: &ProvisionalType, universe: u32) -> ProvisionalType {
    match ty {
        ProvisionalType::Param(GenericParamKey {
            owner: DeclarationKey::Function(owner),
            ordinal,
        }) if owner == "$higher_ranked_universe_1" => ProvisionalType::Param(GenericParamKey {
            owner: DeclarationKey::Function(format!("$higher_ranked_universe_{universe}")),
            ordinal: *ordinal,
        }),
        _ => ty.clone(),
    }
}

fn instantiate_const_pattern(
    pattern: &ConstPattern,
    substitutions: &BTreeMap<u32, GenericArg>,
) -> Option<ProvisionalType> {
    match pattern {
        ConstPattern::Value(value) => Some(encode_const_value(value)),
        ConstPattern::Bound(index, _) => encode_const_argument(substitutions.get(index)?),
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum GenericArgPattern {
    Type(Pattern),
    Lifetime(LifetimePattern),
    Const(ConstPattern),
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum LifetimePattern {
    Bound(u32),
    Static,
    HigherRanked(u32),
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum SuperArgumentPattern {
    Type(Pattern),
    Const(ConstPattern),
    LifetimeBound(u32),
    LifetimeStatic,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct SupertraitTemplate {
    trait_key: TraitKey,
    arguments: Vec<SuperArgumentPattern>,
    bindings: Vec<AssociatedPattern>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct DedicatedUseRequirement {
    trait_key: TraitKey,
    value: ConstValue,
}

#[derive(Clone, Copy)]
struct Binder {
    index: u32,
    kind: GenericParameterKind,
    higher_ranked: bool,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct AssociatedPattern {
    item: String,
    arguments: Vec<GenericArgPattern>,
    value: Pattern,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct GoalPattern {
    polarity: GoalPolarity,
    trait_key: TraitKey,
    subject: Pattern,
    arguments: Vec<GenericArgPattern>,
    bindings: Vec<AssociatedPattern>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ImplEntry {
    binders: usize,
    head: GoalPattern,
    super_goals: Vec<GoalPattern>,
    goals: Vec<GoalPattern>,
    associated_values: Vec<AssociatedPattern>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct GroundGoal {
    polarity: GoalPolarity,
    trait_key: TraitKey,
    subject: ProvisionalType,
    arguments: Vec<GenericArg>,
    bindings: Vec<AssociatedValue>,
    projections: Vec<AssociatedKey>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct AssociatedValue {
    pub(crate) item: String,
    pub(crate) arguments: Vec<GenericArg>,
    pub(crate) value: ProvisionalType,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct AssociatedKey {
    item: String,
    arguments: Vec<GenericArg>,
}

impl AssociatedValue {
    fn key(&self) -> AssociatedKey {
        AssociatedKey {
            item: self.item.clone(),
            arguments: self.arguments.clone(),
        }
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct TraitFact {
    pub(crate) polarity: GoalPolarity,
    pub(crate) trait_key: TraitKey,
    pub(crate) subject: ProvisionalType,
    pub(crate) arguments: Vec<GenericArg>,
    pub(crate) bindings: Vec<AssociatedValue>,
}

#[derive(Clone, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct ParamEnv {
    facts: Vec<TraitFact>,
    conflicts: BTreeSet<FactHead>,
    equality_conflicts: BTreeSet<(FactHead, AssociatedKey)>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct FactHead {
    trait_key: TraitKey,
    subject: ProvisionalType,
    arguments: Vec<GenericArg>,
}

impl ParamEnv {
    pub(crate) fn is_consistent(&self) -> bool {
        self.conflicts.is_empty() && self.equality_conflicts.is_empty()
    }

    pub(crate) fn contains_exact(
        &self,
        polarity: GoalPolarity,
        trait_key: &TraitKey,
        subject: &ProvisionalType,
        arguments: &[GenericArg],
        bindings: &[AssociatedValue],
    ) -> bool {
        self.facts.iter().any(|fact| {
            fact.polarity == polarity
                && &fact.trait_key == trait_key
                && &fact.subject == subject
                && fact.arguments == arguments
                && fact.bindings == bindings
        })
    }

    /// Returns the argument lists carried by exact lexical facts with this
    /// polarity, trait, and subject. Generic-call inference uses these facts
    /// to recover associated marker arguments that are not present in an
    /// ordinary value parameter type. In particular, `L: Label<B>` makes `B`
    /// available when a generic label is forwarded through a control helper.
    pub(crate) fn matching_argument_lists(
        &self,
        polarity: GoalPolarity,
        trait_key: &TraitKey,
        subject: &ProvisionalType,
    ) -> Vec<Vec<GenericArg>> {
        self.facts
            .iter()
            .filter(|fact| {
                fact.polarity == polarity
                    && &fact.trait_key == trait_key
                    && &fact.subject == subject
                    && fact.bindings.is_empty()
            })
            .map(|fact| fact.arguments.clone())
            .collect()
    }

    /// Returns whether lexical positive `Use` evidence contains the requested
    /// interval. Quantity evidence is an interval contract rather than an
    /// invariant ordinary trait argument: `Use<[0,infinity]>` therefore
    /// entails `Use<[0,0]>` for the same symbolic subject.
    pub(crate) fn use_quantity_contains(
        &self,
        trait_key: &TraitKey,
        subject: &ProvisionalType,
        lower: u32,
        upper: Option<u32>,
    ) -> bool {
        self.facts.iter().any(|fact| {
            let [
                GenericArg::Const(ConstValue::Quantity {
                    lower: available_lower,
                    upper: available_upper,
                }),
            ] = fact.arguments.as_slice()
            else {
                return false;
            };
            fact.polarity == GoalPolarity::Positive
                && &fact.trait_key == trait_key
                && &fact.subject == subject
                && fact.bindings.is_empty()
                && *available_lower <= lower
                && match (*available_upper, upper) {
                    (None, _) => true,
                    (Some(_), None) => false,
                    (Some(available), Some(requested)) => available >= requested,
                }
        })
    }

    #[cfg(test)]
    fn canonical_text(&self) -> String {
        let mut text = self
            .facts
            .iter()
            .map(|fact| format!("{fact:?}\n"))
            .collect::<String>();
        for conflict in &self.conflicts {
            writeln!(text, "conflict {conflict:?}").unwrap();
        }
        for conflict in &self.equality_conflicts {
            writeln!(text, "equality conflict {conflict:?}").unwrap();
        }
        text
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct TableKey {
    goal: GroundGoal,
    param_env: ParamEnv,
}

#[derive(Clone)]
enum TableState {
    Evaluating,
    Complete(TableAnswer),
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct TableAnswer {
    result: SolveResult,
    associated_values: BTreeMap<AssociatedKey, ProvisionalType>,
    cycle_trace: Option<Vec<TableKey>>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum SolveResult {
    Proven,
    Refuted,
    NoEvidence,
    Ambiguous,
    Overflow,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum SolverLimit {
    NestedFrames,
    AnswersPerTable,
    Steps,
    ProjectionSteps,
    Tables,
}

impl SolverLimit {
    pub(crate) fn maximum(self) -> usize {
        match self {
            Self::NestedFrames => MAX_DEPTH,
            Self::AnswersPerTable => MAX_ANSWERS_PER_TABLE,
            Self::Steps => MAX_STEPS,
            Self::ProjectionSteps => MAX_PROJECTION_STEPS,
            Self::Tables => MAX_TABLES,
        }
    }

    fn label(self) -> &'static str {
        match self {
            Self::NestedFrames => "nested solver frames",
            Self::AnswersPerTable => "distinct answers per table",
            Self::Steps => "solver steps",
            Self::ProjectionSteps => "projection normalization steps",
            Self::Tables => "solver tables",
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum SolveFailure {
    Cycle {
        trace: Vec<String>,
    },
    Limit {
        limit: SolverLimit,
        trace: Vec<String>,
    },
}

impl SolveFailure {
    pub(crate) fn diagnostic_text(&self) -> String {
        match self {
            Self::Cycle { trace } => format!("cycle trace: {}", trace.join(" -> ")),
            Self::Limit { limit, trace } => {
                let suffix = if trace.is_empty() {
                    String::new()
                } else {
                    format!("; trace: {}", trace.join(" -> "))
                };
                format!(
                    "{} limit {} exceeded{suffix}",
                    limit.label(),
                    limit.maximum()
                )
            }
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct SolveReport {
    pub(crate) result: SolveResult,
    pub(crate) failure: Option<SolveFailure>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct SolverBudget {
    steps: usize,
    projection_steps: usize,
}

impl SolverBudget {
    pub(crate) fn begin_declaration(&mut self) {
        self.steps = 0;
        self.projection_steps = 0;
    }

    #[cfg(test)]
    pub(crate) fn exhausted_for_test() -> Self {
        Self {
            steps: MAX_STEPS.saturating_add(1),
            projection_steps: MAX_PROJECTION_STEPS.saturating_add(1),
        }
    }
}

#[derive(Default)]
struct SolverDiagnostics {
    active: Vec<TableKey>,
    cycle: Option<Vec<TableKey>>,
    limit: Option<(SolverLimit, Vec<TableKey>)>,
}

impl SolverDiagnostics {
    fn goal_text(key: &TableKey) -> String {
        format!("{:?} @ {:?}", key.goal, key.param_env)
    }

    fn record_cycle(&mut self, key: &TableKey) {
        let Some(start) = self.active.iter().rposition(|active| active == key) else {
            return;
        };
        let mut trace = self.active[start..].to_vec();
        trace.push(key.clone());
        if self
            .cycle
            .as_ref()
            .is_none_or(|existing| (trace.len(), &trace) < (existing.len(), existing))
        {
            self.cycle = Some(trace);
        }
    }

    fn record_limit(&mut self, limit: SolverLimit, attempted: Option<&TableKey>) {
        let mut trace = self.active.clone();
        if let Some(attempted) = attempted
            && trace.last() != Some(attempted)
        {
            trace.push(attempted.clone());
        }
        if self.limit.as_ref().is_none_or(|existing| {
            (trace.len(), &trace, limit) < (existing.1.len(), &existing.1, existing.0)
        }) {
            self.limit = Some((limit, trace));
        }
    }

    fn consider_cycle(&mut self, trace: &Option<Vec<TableKey>>) {
        let Some(trace) = trace else { return };
        if self
            .cycle
            .as_ref()
            .is_none_or(|existing| (trace.len(), trace) < (existing.len(), existing))
        {
            self.cycle = Some(trace.clone());
        }
    }

    fn failure_for(&self, result: SolveResult) -> Option<SolveFailure> {
        match result {
            SolveResult::Ambiguous => self.cycle.as_ref().map(|trace| SolveFailure::Cycle {
                trace: trace.iter().map(Self::goal_text).collect(),
            }),
            SolveResult::Overflow => {
                self.limit
                    .as_ref()
                    .map(|(limit, trace)| SolveFailure::Limit {
                        limit: *limit,
                        trace: trace.iter().map(Self::goal_text).collect(),
                    })
            }
            _ => None,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct TraitDb {
    traits: BTreeMap<String, TraitSchema>,
    trait_names: BTreeMap<TraitKey, String>,
    nominals: BTreeMap<String, NominalSchema>,
    type_const_arguments: BTreeMap<(usize, usize), Vec<crate::ast::ConstAssociatedArgumentSyntax>>,
    impls: Vec<ImplEntry>,
    candidates: BTreeMap<CandidateKey, Vec<usize>>,
    intrinsic_use_key: Option<TraitKey>,
    array_nominal: Option<NominalKey>,
}

#[derive(Clone, Debug)]
struct NominalSchema {
    parameters: Vec<GenericParameterKind>,
    identity: NominalKey,
}

fn nominal_parameter_kind(parameter: &crate::ast::GenericParam) -> GenericParameterKind {
    match parameter.kind {
        GenericParamKind::Type => GenericParameterKind::Type,
        GenericParamKind::Lifetime => GenericParameterKind::Lifetime,
        GenericParamKind::Const(kind) => GenericParameterKind::Const(kind),
        GenericParamKind::EffectRow => unreachable!("validated outside callable rows"),
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum HeadConstructor {
    Any,
    Predefined(String),
    Nominal(NominalKey),
    Tuple(usize),
    Shared,
    Unique,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct CandidateKey {
    polarity: GoalPolarity,
    trait_key: TraitKey,
    constructor: HeadConstructor,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct TraitSchema {
    key: TraitKey,
    parameters: Vec<GenericParameterKind>,
    associated_types: BTreeMap<String, Vec<GenericParameterKind>>,
    associated_items: BTreeMap<String, ManifestAssociatedItem>,
    associated_effect_row_parameters: BTreeMap<String, BTreeSet<usize>>,
    supertraits: Vec<SupertraitTemplate>,
    dedicated_use_requirement: Option<DedicatedUseRequirement>,
    policy: TraitPolicy,
    role: Option<IntrinsicRole>,
}

impl TraitDb {
    /// Rebind source-span keyed const arguments after reusing the structural
    /// database. Callable-body edits may alter these entries while leaving
    /// trait, nominal, alias, effect, and impl declarations unchanged.
    pub(crate) fn with_current_type_const_arguments(mut self, program: &Program) -> Self {
        self.type_const_arguments = program
            .type_const_arguments
            .iter()
            .map(|entry| {
                (
                    (entry.application.start, entry.application.end),
                    entry.arguments.clone(),
                )
            })
            .collect();
        self
    }

    /// Predefined runtime leaves carry their `Use` capability out of band:
    /// source cannot lawfully implement the external intrinsic for them, and
    /// requiring the distributed standard library to do so would violate the
    /// same orphan rule that protects every other external trait.  Reflect the
    /// runtime type descriptor's maximal capability as intrinsic solver
    /// evidence instead.
    fn predefined_use_contains(goal: &GroundGoal) -> bool {
        let ProvisionalType::Predefined(name) = &goal.subject else {
            return false;
        };
        let Some((principal_lower, principal_upper)) =
            predefined_runtime_use_interval(name.as_str())
        else {
            return false;
        };
        let [
            GenericArg::Const(ConstValue::Quantity {
                lower: requested_lower,
                upper: requested_upper,
            }),
        ] = goal.arguments.as_slice()
        else {
            return false;
        };
        if goal.polarity != GoalPolarity::Positive || !goal.bindings.is_empty() {
            return false;
        }
        principal_lower <= *requested_lower
            && match (principal_upper, *requested_upper) {
                (None, _) => true,
                (Some(_), None) => false,
                (Some(principal), Some(requested)) => requested <= principal,
            }
    }

    fn candidate_indices(&self, goal: &GroundGoal) -> Vec<usize> {
        let mut candidates = self
            .candidates
            .get(&CandidateKey {
                polarity: goal.polarity,
                trait_key: goal.trait_key.clone(),
                constructor: HeadConstructor::Any,
            })
            .cloned()
            .unwrap_or_default();
        if let Some(constructor) = ground_constructor(&goal.subject)
            && let Some(specific) = self.candidates.get(&CandidateKey {
                polarity: goal.polarity,
                trait_key: goal.trait_key.clone(),
                constructor,
            })
        {
            candidates.extend(specific);
        }
        candidates.sort_unstable();
        candidates.dedup();
        candidates
    }

    fn matches_candidate(
        &self,
        pattern: &GoalPattern,
        goal: &GroundGoal,
        substitutions: &mut BTreeMap<u32, GenericArg>,
    ) -> bool {
        if self
            .schema_by_key(&pattern.trait_key)
            .is_none_or(|schema| schema.role != Some(IntrinsicRole::Use))
        {
            return matches_goal(pattern, goal, substitutions);
        }
        if pattern.polarity != goal.polarity
            || pattern.trait_key != goal.trait_key
            || !pattern.bindings.is_empty()
            || !goal.bindings.is_empty()
            || pattern.arguments.len() != 1
            || goal.arguments.len() != 1
            || !matches_pattern(&pattern.subject, &goal.subject, substitutions)
        {
            return false;
        }
        match (&pattern.arguments[0], &goal.arguments[0]) {
            (
                GenericArgPattern::Const(ConstPattern::Value(ConstValue::Quantity {
                    lower: principal_lower,
                    upper: principal_upper,
                })),
                GenericArg::Const(ConstValue::Quantity {
                    lower: requested_lower,
                    upper: requested_upper,
                }),
            ) => {
                principal_lower <= requested_lower
                    && match (principal_upper, requested_upper) {
                        (None, _) => true,
                        (Some(_), None) => false,
                        (Some(principal), Some(requested)) => requested <= principal,
                    }
            }
            (pattern, actual) => matches_generic_arg(pattern, actual, substitutions),
        }
    }

    #[allow(dead_code)]
    pub(crate) fn build(program: &Program) -> Result<Self, Vec<Diagnostic>> {
        Self::build_with_manifest(program, &TrustedTraitManifest::trusted_default())
    }

    pub(crate) fn build_with_manifest(
        program: &Program,
        manifest: &TrustedTraitManifest,
    ) -> Result<Self, Vec<Diagnostic>> {
        let mut errors = Vec::new();
        let mut traits = BTreeMap::new();
        let mut trait_names = BTreeMap::new();
        for declaration in &manifest.declarations {
            let key = TraitKey::External(declaration.id);
            trait_names.insert(key.clone(), declaration.display_name.clone());
            traits.insert(
                declaration.display_name.clone(),
                TraitSchema {
                    key,
                    parameters: declaration.parameters.clone(),
                    associated_types: declaration
                        .associated_items
                        .iter()
                        .map(|item| (item.name.clone(), item.parameters.clone()))
                        .collect(),
                    associated_items: declaration
                        .associated_items
                        .iter()
                        .map(|item| (item.name.clone(), item.clone()))
                        .collect(),
                    associated_effect_row_parameters: BTreeMap::new(),
                    supertraits: vec![],
                    dedicated_use_requirement: None,
                    policy: declaration.policy,
                    role: declaration.role,
                },
            );
        }
        let intrinsic_keys = traits
            .values()
            .filter_map(|schema| schema.role.map(|role| (role, schema.key.clone())))
            .collect::<BTreeMap<_, _>>();
        for schema in traits.values_mut() {
            let template = match schema.role {
                Some(IntrinsicRole::Drop) => {
                    schema.dedicated_use_requirement = Some(DedicatedUseRequirement {
                        trait_key: intrinsic_keys[&IntrinsicRole::Use].clone(),
                        value: ConstValue::Quantity {
                            lower: 0,
                            upper: Some(0),
                        },
                    });
                    None
                }
                Some(IntrinsicRole::RunsIn) => Some(SupertraitTemplate {
                    trait_key: intrinsic_keys[&IntrinsicRole::Fn].clone(),
                    arguments: vec![SuperArgumentPattern::Type(Pattern::Bound(1))],
                    bindings: vec![],
                }),
                Some(IntrinsicRole::Label) => Some(SupertraitTemplate {
                    trait_key: intrinsic_keys[&IntrinsicRole::Fn].clone(),
                    arguments: vec![SuperArgumentPattern::Type(Pattern::Tuple(vec![
                        Pattern::Bound(0),
                    ]))],
                    bindings: vec![AssociatedPattern {
                        item: "Output".into(),
                        arguments: vec![],
                        value: Pattern::Ground(ProvisionalType::Predefined("Never".into())),
                    }],
                }),
                _ => None,
            };
            if let Some(template) = template {
                schema.supertraits.push(template);
            }
        }
        for declaration in &program.traits {
            if traits.contains_key(&declaration.name) {
                errors.push(error(
                    declaration.span,
                    format!(
                        "reserved external trait `{}` cannot be redeclared",
                        declaration.name
                    ),
                ));
            } else if traits
                .insert(
                    declaration.name.clone(),
                    TraitSchema {
                        key: TraitKey::Local(declaration.name.clone()),
                        parameters: declaration
                            .generics
                            .iter()
                            .flat_map(|generics| &generics.params)
                            .map(|parameter| match parameter.kind {
                                GenericParamKind::Type => GenericParameterKind::Type,
                                GenericParamKind::Lifetime => GenericParameterKind::Lifetime,
                                GenericParamKind::EffectRow => {
                                    unreachable!("validated outside callable rows")
                                }
                                GenericParamKind::Const(kind) => GenericParameterKind::Const(kind),
                            })
                            .collect(),
                        associated_types: declaration
                            .associated_types
                            .iter()
                            .map(|item| {
                                (
                                    item.name.clone(),
                                    item.generics
                                        .iter()
                                        .flat_map(|generics| &generics.params)
                                        .map(|parameter| match parameter.kind {
                                            GenericParamKind::Type => GenericParameterKind::Type,
                                            GenericParamKind::Lifetime => {
                                                GenericParameterKind::Lifetime
                                            }
                                            GenericParamKind::EffectRow => {
                                                GenericParameterKind::Type
                                            }
                                            GenericParamKind::Const(kind) => {
                                                GenericParameterKind::Const(kind)
                                            }
                                        })
                                        .collect(),
                                )
                            })
                            .collect(),
                        associated_items: declaration
                            .associated_types
                            .iter()
                            .map(|item| {
                                let parameters = item
                                    .generics
                                    .iter()
                                    .flat_map(|generics| &generics.params)
                                    .map(|parameter| match parameter.kind {
                                        GenericParamKind::Type => GenericParameterKind::Type,
                                        GenericParamKind::Lifetime => {
                                            GenericParameterKind::Lifetime
                                        }
                                        GenericParamKind::EffectRow => GenericParameterKind::Type,
                                        GenericParamKind::Const(kind) => {
                                            GenericParameterKind::Const(kind)
                                        }
                                    })
                                    .collect();
                                (
                                    item.name.clone(),
                                    ManifestAssociatedItem {
                                        name: item.name.clone(),
                                        parameters,
                                        kind: match item.kind {
                                            crate::ast::AssociatedItemSyntaxKind::Type => {
                                                AssociatedItemKind::Type
                                            }
                                            crate::ast::AssociatedItemSyntaxKind::EffectRow => {
                                                AssociatedItemKind::EffectRow
                                            }
                                        },
                                    },
                                )
                            })
                            .collect(),
                        associated_effect_row_parameters: declaration
                            .associated_types
                            .iter()
                            .map(|item| {
                                (
                                    item.name.clone(),
                                    item.generics
                                        .iter()
                                        .flat_map(|generics| &generics.params)
                                        .enumerate()
                                        .filter_map(|(index, parameter)| {
                                            (parameter.kind == GenericParamKind::EffectRow)
                                                .then_some(index)
                                        })
                                        .collect(),
                                )
                            })
                            .collect(),
                        supertraits: vec![],
                        dedicated_use_requirement: None,
                        policy: TraitPolicy::ExternalOpen,
                        role: None,
                    },
                )
                .is_some()
            {
                errors.push(error(
                    declaration.span,
                    format!("trait `{}` is declared more than once", declaration.name),
                ));
            }
        }
        for (name, schema) in &traits {
            trait_names.insert(schema.key.clone(), name.clone());
        }
        let mut nominals = program
            .structs
            .iter()
            .map(|declaration| {
                (
                    declaration.name.clone(),
                    NominalSchema {
                        parameters: declaration
                            .generics
                            .as_ref()
                            .map_or_else(Vec::new, |generics| {
                                generics.params.iter().map(nominal_parameter_kind).collect()
                            }),
                        identity: NominalKey(declaration.name.clone()),
                    },
                )
            })
            .chain(program.enums.iter().map(|declaration| {
                (
                    declaration.name.clone(),
                    NominalSchema {
                        parameters: declaration
                            .generics
                            .as_ref()
                            .map_or_else(Vec::new, |generics| {
                                generics.params.iter().map(nominal_parameter_kind).collect()
                            }),
                        identity: NominalKey(declaration.name.clone()),
                    },
                )
            }))
            .collect::<BTreeMap<_, _>>();
        let mut array_nominal = None;
        for machine in &manifest.runtime.machine_types {
            let identity = NominalKey(machine.display_name.clone());
            if machine.role == MachineTypeRole::Array {
                array_nominal = Some(identity.clone());
            }
            nominals
                .entry(machine.display_name.clone())
                .or_insert_with(|| NominalSchema {
                    parameters: machine.parameters.clone(),
                    identity,
                });
        }
        let mut local_owners = nominals.keys().cloned().collect::<BTreeSet<_>>();
        let generic_aliases = program
            .type_aliases
            .iter()
            .filter(|alias| alias.generics.is_some())
            .map(|alias| (alias.name.clone(), alias))
            .collect::<BTreeMap<_, _>>();
        let monomorphic_aliases = program
            .type_aliases
            .iter()
            .filter(|alias| alias.generics.is_none())
            .map(|alias| (alias.name.clone(), alias.target.clone()))
            .collect::<BTreeMap<_, _>>();
        // A transparent alias preserves orphan ownership only when its outer
        // constructor is a source-local nominal. Alias normalization in the
        // second database build replaces this provisional head with the real one.
        for alias in &program.type_aliases {
            nominals.insert(
                alias.name.clone(),
                NominalSchema {
                    parameters: alias.generics.as_ref().map_or_else(Vec::new, |generics| {
                        generics.params.iter().map(nominal_parameter_kind).collect()
                    }),
                    identity: NominalKey(alias.name.clone()),
                },
            );
        }
        loop {
            let before = local_owners.len();
            for alias in &program.type_aliases {
                let outer = match &alias.target.kind {
                    TypeSyntaxKind::Path(path) if path.len() == 1 => Some(path[0].name.as_str()),
                    TypeSyntaxKind::Application { constructor, .. } => constructor.simple_name(),
                    _ => None,
                };
                if outer.is_some_and(|name| local_owners.contains(name)) {
                    local_owners.insert(alias.name.clone());
                    if let Some(identity) = outer
                        .and_then(|name| nominals.get(name))
                        .map(|schema| schema.identity.clone())
                        && let Some(schema) = nominals.get_mut(&alias.name)
                    {
                        schema.identity = identity;
                    }
                }
            }
            if local_owners.len() == before {
                break;
            }
        }
        nominals.retain(|name, _| {
            local_owners.contains(name)
                || !program.type_aliases.iter().any(|alias| &alias.name == name)
        });
        let trait_snapshot = traits.clone();
        for declaration in &program.traits {
            match lower_supertraits(declaration, &trait_snapshot, &nominals) {
                Ok(supertraits) => {
                    traits
                        .get_mut(&declaration.name)
                        .expect("source trait schema is registered")
                        .supertraits = supertraits;
                }
                Err(diagnostics) => errors.extend(diagnostics),
            }
        }
        errors.extend(supertrait_cycle_errors(&traits, program));
        let effects = program
            .effects
            .iter()
            .map(|effect| {
                (
                    effect.name.clone(),
                    effect
                        .generics
                        .iter()
                        .flat_map(|generics| &generics.params)
                        .filter(|parameter| parameter.kind == GenericParamKind::Type)
                        .count(),
                )
            })
            .collect::<BTreeMap<_, _>>();
        let type_const_arguments = program
            .type_const_arguments
            .iter()
            .map(|entry| {
                (
                    (entry.application.start, entry.application.end),
                    entry.arguments.clone(),
                )
            })
            .collect::<BTreeMap<_, _>>();
        let mut impls = Vec::new();
        for declaration in &program.impls {
            match lower_impl(
                declaration,
                &traits,
                &nominals,
                &local_owners,
                &generic_aliases,
                &monomorphic_aliases,
                &effects,
                &type_const_arguments,
                false,
            ) {
                Ok(entry) => impls.push((entry, declaration.span)),
                Err(diagnostic) => errors.push(diagnostic),
            }
        }
        let intrinsic_name = |role| {
            traits
                .iter()
                .find_map(|(name, schema)| (schema.role == Some(role)).then(|| name.clone()))
                .expect("trusted intrinsic schema is present")
        };
        let use_name = intrinsic_name(IntrinsicRole::Use);
        for declaration in &program.uses {
            let implementation = ImplDecl {
                generics: declaration.generics.clone(),
                polarity: GoalPolarity::Positive,
                trait_ref: TraitRefSyntax {
                    path: vec![crate::ast::TypePathSegment {
                        name: use_name.clone(),
                        span: declaration.quantity.span,
                    }],
                    arguments: vec![GoalArgument::Quantity(declaration.quantity.clone())],
                    bindings: vec![],
                    span: declaration.span,
                },
                self_ty: declaration.target.clone(),
                where_clause: declaration.where_clause.clone(),
                associated_types: vec![],
                methods: vec![],
                span: declaration.span,
            };
            match lower_impl(
                &implementation,
                &traits,
                &nominals,
                &local_owners,
                &generic_aliases,
                &monomorphic_aliases,
                &effects,
                &type_const_arguments,
                true,
            ) {
                Ok(entry) => impls.push((entry, declaration.span)),
                Err(diagnostic) => errors.push(diagnostic),
            }
        }
        let drop_name = intrinsic_name(IntrinsicRole::Drop);
        for declaration in &program.drops {
            let implementation = ImplDecl {
                generics: declaration.generics.clone(),
                polarity: GoalPolarity::Positive,
                trait_ref: TraitRefSyntax {
                    path: vec![crate::ast::TypePathSegment {
                        name: drop_name.clone(),
                        span: declaration.span,
                    }],
                    arguments: vec![],
                    bindings: vec![],
                    span: declaration.span,
                },
                self_ty: declaration.target_type.clone(),
                where_clause: declaration.where_clause.clone(),
                associated_types: vec![],
                methods: vec![],
                span: declaration.span,
            };
            match lower_impl(
                &implementation,
                &traits,
                &nominals,
                &local_owners,
                &generic_aliases,
                &monomorphic_aliases,
                &effects,
                &type_const_arguments,
                true,
            ) {
                Ok(entry) => impls.push((entry, declaration.span)),
                Err(diagnostic) => errors.push(diagnostic),
            }
        }
        impls.sort_by(|(left, _), (right, _)| left.cmp(right));
        impls.dedup_by(|left, right| {
            left.0.head.polarity == GoalPolarity::Negative && left.0 == right.0
        });
        let intrinsic_use_key = traits
            .values()
            .find(|schema| schema.role == Some(IntrinsicRole::Use))
            .map(|schema| schema.key.clone())
            .expect("trusted Use intrinsic is present");
        for left in 0..impls.len() {
            for right in left + 1..impls.len() {
                if impls[left].0.head.trait_key == impls[right].0.head.trait_key
                    && (impls[left].0.head.polarity == GoalPolarity::Positive
                        || impls[right].0.head.polarity == GoalPolarity::Positive)
                    && if impls[left].0.head.trait_key == intrinsic_use_key {
                        use_heads_overlap(&impls[left].0.head, &impls[right].0.head)
                    } else {
                        goal_overlaps(&impls[left].0.head, &impls[right].0.head)
                    }
                {
                    errors.push(error(
                        impls[right].1,
                        format!(
                            "overlapping implementations of `{}`",
                            trait_names
                                .get(&impls[right].0.head.trait_key)
                                .cloned()
                                .unwrap_or_else(|| "<unknown trait>".into())
                        ),
                    ));
                }
            }
        }
        errors.extend(recursive_impl_errors(
            &impls,
            &trait_names,
            Some(&intrinsic_use_key),
        ));
        if errors.is_empty() {
            let impl_spans = impls.iter().map(|(_, span)| *span).collect::<Vec<_>>();
            let impls = impls
                .into_iter()
                .map(|(entry, _)| entry)
                .collect::<Vec<_>>();
            let mut candidates = BTreeMap::<CandidateKey, Vec<usize>>::new();
            for (index, implementation) in impls.iter().enumerate() {
                if let Some(constructor) = pattern_constructor(&implementation.head.subject) {
                    candidates
                        .entry(CandidateKey {
                            polarity: implementation.head.polarity,
                            trait_key: implementation.head.trait_key.clone(),
                            constructor,
                        })
                        .or_default()
                        .push(index);
                }
            }
            let database = Self {
                traits,
                trait_names,
                nominals,
                type_const_arguments,
                impls,
                candidates,
                intrinsic_use_key: Some(intrinsic_use_key),
                array_nominal,
            };
            let validation_errors = validate_supertrait_impls(&database, &impl_spans);
            if validation_errors.is_empty() {
                Ok(database)
            } else {
                Err(validation_errors)
            }
        } else {
            Err(errors)
        }
    }

    pub(crate) fn has_arity(&self, name: &str, arity: usize) -> bool {
        self.traits
            .get(name)
            .is_some_and(|schema| schema.parameters.len() == arity)
    }

    pub(crate) fn arity(&self, name: &str) -> Option<usize> {
        self.traits.get(name).map(|schema| schema.parameters.len())
    }

    pub(crate) fn trait_key(&self, name: &str) -> Option<&TraitKey> {
        self.traits.get(name).map(|schema| &schema.key)
    }

    pub(crate) fn trait_display_name(&self, key: &TraitKey) -> &str {
        self.trait_names
            .get(key)
            .map_or("<unknown trait>", String::as_str)
    }

    pub(crate) fn intrinsic_key(&self, role: IntrinsicRole) -> Option<&TraitKey> {
        self.traits
            .values()
            .find(|schema| schema.role == Some(role))
            .map(|schema| &schema.key)
    }

    pub(crate) fn drop_use_requirement(&self) -> Option<(u32, Option<u32>)> {
        let schema = self
            .traits
            .values()
            .find(|schema| schema.role == Some(IntrinsicRole::Drop))?;
        match &schema.dedicated_use_requirement.as_ref()?.value {
            ConstValue::Quantity { lower, upper } => Some((*lower, *upper)),
            ConstValue::U32(_) => None,
        }
    }

    pub(crate) fn is_ordinary_open(&self, name: &str) -> bool {
        self.traits.get(name).is_some_and(|schema| {
            schema.policy == TraitPolicy::ExternalOpen && schema.role.is_none()
        })
    }

    pub(crate) fn arguments_match(&self, name: &str, arguments: &[GenericArg]) -> bool {
        self.traits.get(name).is_some_and(|schema| {
            schema.parameters.len() == arguments.len()
                && schema
                    .parameters
                    .iter()
                    .zip(arguments)
                    .all(|(kind, argument)| match (kind, argument) {
                        (GenericParameterKind::Type, GenericArg::Type(_)) => true,
                        (GenericParameterKind::Lifetime, GenericArg::Lifetime(_)) => true,
                        (GenericParameterKind::Const(kind), argument) => {
                            generic_arg_has_const_kind(argument, *kind)
                        }
                        _ => false,
                    })
        })
    }

    pub(crate) fn parameter_kinds(&self, name: &str) -> Option<&[GenericParameterKind]> {
        self.traits
            .get(name)
            .map(|schema| schema.parameters.as_slice())
    }

    fn schema_by_key(&self, key: &TraitKey) -> Option<&TraitSchema> {
        self.traits.values().find(|schema| &schema.key == key)
    }

    pub(crate) fn associated_type_arity(&self, trait_name: &str, item: &str) -> Option<usize> {
        self.traits
            .get(trait_name)?
            .associated_types
            .get(item)
            .map(Vec::len)
    }

    pub(crate) fn associated_item_kind(
        &self,
        trait_name: &str,
        item: &str,
    ) -> Option<AssociatedItemKind> {
        self.traits
            .get(trait_name)?
            .associated_items
            .get(item)
            .map(|item| item.kind.clone())
    }

    pub(crate) fn associated_effect_row_parameter_positions(
        &self,
        trait_name: &str,
        item: &str,
    ) -> Option<&BTreeSet<usize>> {
        self.traits
            .get(trait_name)?
            .associated_effect_row_parameters
            .get(item)
    }

    #[allow(dead_code)]
    pub(crate) fn solve(&self, trait_name: &str, subject: &ProvisionalType) -> SolveResult {
        self.solve_with_arguments(trait_name, subject, &[])
    }

    pub(crate) fn solve_with_arguments(
        &self,
        trait_name: &str,
        subject: &ProvisionalType,
        arguments: &[ProvisionalType],
    ) -> SolveResult {
        self.solve_with_polarity(GoalPolarity::Positive, trait_name, subject, arguments)
    }

    pub(crate) fn solve_with_polarity(
        &self,
        polarity: GoalPolarity,
        trait_name: &str,
        subject: &ProvisionalType,
        arguments: &[ProvisionalType],
    ) -> SolveResult {
        self.solve_with_bindings(polarity, trait_name, subject, arguments, &[])
    }

    pub(crate) fn solve_with_bindings(
        &self,
        polarity: GoalPolarity,
        trait_name: &str,
        subject: &ProvisionalType,
        arguments: &[ProvisionalType],
        bindings: &[(String, ProvisionalType)],
    ) -> SolveResult {
        let bindings = bindings
            .iter()
            .map(|(item, value)| AssociatedValue {
                item: item.clone(),
                arguments: vec![],
                value: value.clone(),
            })
            .collect::<Vec<_>>();
        self.solve_with_param_env_values(
            &ParamEnv::default(),
            polarity,
            trait_name,
            subject,
            arguments,
            &bindings,
        )
    }

    pub(crate) fn param_env(&self, facts: impl IntoIterator<Item = TraitFact>) -> ParamEnv {
        let mut facts = facts.into_iter().collect::<Vec<_>>();
        loop {
            facts.sort();
            facts.dedup();
            let mut implied = Vec::new();
            for fact in facts
                .iter()
                .filter(|fact| fact.polarity == GoalPolarity::Positive)
            {
                let Some(schema) = self.schema_by_key(&fact.trait_key) else {
                    continue;
                };
                for template in &schema.supertraits {
                    if let Some(fact) = instantiate_supertrait_fact(template, schema, fact) {
                        implied.push(fact);
                    }
                }
            }
            let before = facts.len();
            facts.extend(implied);
            facts.sort();
            facts.dedup();
            if facts.len() == before {
                break;
            }
        }
        let mut conflicts = BTreeSet::new();
        let mut equality_conflicts = BTreeSet::new();
        for fact in &mut facts {
            let head = fact_head(fact);
            if self.schema_by_key(&fact.trait_key).is_none_or(|schema| {
                schema.parameters.len() != fact.arguments.len()
                    || !schema.parameters.iter().zip(&fact.arguments).all(
                        |(parameter, argument)| match (parameter, argument) {
                            (GenericParameterKind::Type, GenericArg::Type(_)) => true,
                            (GenericParameterKind::Lifetime, GenericArg::Lifetime(_)) => true,
                            (GenericParameterKind::Const(expected), argument) => {
                                generic_arg_has_const_kind(argument, *expected)
                            }
                            _ => false,
                        },
                    )
            }) || (fact.polarity == GoalPolarity::Negative && !fact.bindings.is_empty())
                || fact.bindings.iter().any(|binding| {
                    self.schema_by_key(&fact.trait_key)
                        .and_then(|schema| schema.associated_types.get(&binding.item).map(Vec::len))
                        != Some(binding.arguments.len())
                })
            {
                conflicts.insert(head.clone());
            }
            fact.bindings.sort();
            if fact.bindings.windows(2).any(|pair| {
                pair[0].item == pair[1].item
                    && pair[0].arguments == pair[1].arguments
                    && pair[0].value != pair[1].value
            }) {
                for pair in fact.bindings.windows(2) {
                    if pair[0].key() == pair[1].key() && pair[0].value != pair[1].value {
                        equality_conflicts.insert((head.clone(), pair[0].key()));
                    }
                }
            }
            fact.bindings.dedup();
        }
        facts.sort();
        facts.dedup();
        for (index, left) in facts.iter().enumerate() {
            for right in facts.iter().skip(index + 1) {
                if fact_head(left) != fact_head(right) {
                    continue;
                }
                let conflicting_polarity = left.polarity != right.polarity;
                let left_values = left
                    .bindings
                    .iter()
                    .map(|binding| (binding.key(), &binding.value))
                    .collect::<BTreeMap<_, _>>();
                let conflicting_value = right.bindings.iter().any(|binding| {
                    left_values
                        .get(&binding.key())
                        .is_some_and(|existing| *existing != &binding.value)
                });
                if conflicting_polarity || conflicting_value {
                    if conflicting_polarity {
                        conflicts.insert(fact_head(left));
                    } else {
                        for binding in &right.bindings {
                            if left_values
                                .get(&binding.key())
                                .is_some_and(|existing| *existing != &binding.value)
                            {
                                equality_conflicts.insert((fact_head(left), binding.key()));
                            }
                        }
                    }
                }
            }
        }
        ParamEnv {
            facts,
            conflicts,
            equality_conflicts,
        }
    }

    pub(crate) fn solve_with_param_env_values(
        &self,
        param_env: &ParamEnv,
        polarity: GoalPolarity,
        trait_name: &str,
        subject: &ProvisionalType,
        arguments: &[ProvisionalType],
        bindings: &[AssociatedValue],
    ) -> SolveResult {
        self.solve_with_param_env_values_detailed(
            param_env, polarity, trait_name, subject, arguments, bindings,
        )
        .result
    }

    pub(crate) fn solve_with_param_env_values_detailed(
        &self,
        param_env: &ParamEnv,
        polarity: GoalPolarity,
        trait_name: &str,
        subject: &ProvisionalType,
        arguments: &[ProvisionalType],
        bindings: &[AssociatedValue],
    ) -> SolveReport {
        let mut budget = SolverBudget::default();
        self.solve_with_param_env_values_detailed_with_budget(
            &mut budget,
            param_env,
            polarity,
            trait_name,
            subject,
            arguments,
            bindings,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn solve_with_param_env_values_detailed_with_budget(
        &self,
        budget: &mut SolverBudget,
        param_env: &ParamEnv,
        polarity: GoalPolarity,
        trait_name: &str,
        subject: &ProvisionalType,
        arguments: &[ProvisionalType],
        bindings: &[AssociatedValue],
    ) -> SolveReport {
        let Some(trait_key) = self.trait_key(trait_name) else {
            return SolveReport {
                result: SolveResult::NoEvidence,
                failure: None,
            };
        };
        let arguments = arguments
            .iter()
            .cloned()
            .map(GenericArg::Type)
            .collect::<Vec<_>>();
        self.solve_with_key_detailed_with_budget(
            budget, param_env, polarity, trait_key, subject, &arguments, bindings,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn solve_with_generic_arguments_detailed_with_budget(
        &self,
        budget: &mut SolverBudget,
        param_env: &ParamEnv,
        polarity: GoalPolarity,
        trait_name: &str,
        subject: &ProvisionalType,
        arguments: &[GenericArg],
        bindings: &[AssociatedValue],
    ) -> SolveReport {
        let Some(trait_key) = self.trait_key(trait_name) else {
            return SolveReport {
                result: SolveResult::NoEvidence,
                failure: None,
            };
        };
        self.solve_with_key_detailed_with_budget(
            budget, param_env, polarity, trait_key, subject, arguments, bindings,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn solve_with_key_detailed_with_budget(
        &self,
        budget: &mut SolverBudget,
        param_env: &ParamEnv,
        polarity: GoalPolarity,
        trait_key: &TraitKey,
        subject: &ProvisionalType,
        arguments: &[GenericArg],
        bindings: &[AssociatedValue],
    ) -> SolveReport {
        std::thread::scope(|scope| {
            std::thread::Builder::new()
                .name("grandiose-trait-solver".into())
                .stack_size(16 * 1024 * 1024)
                .spawn_scoped(scope, || {
                    self.solve_with_param_env_values_detailed_inner(
                        budget, param_env, polarity, trait_key, subject, arguments, bindings,
                    )
                })
                .map_or_else(
                    |_| SolveReport {
                        result: SolveResult::Overflow,
                        failure: Some(SolveFailure::Limit {
                            limit: SolverLimit::NestedFrames,
                            trace: vec![],
                        }),
                    },
                    |handle| {
                        handle.join().unwrap_or(SolveReport {
                            result: SolveResult::Overflow,
                            failure: Some(SolveFailure::Limit {
                                limit: SolverLimit::NestedFrames,
                                trace: vec![],
                            }),
                        })
                    },
                )
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn solve_with_param_env_values_detailed_inner(
        &self,
        budget: &mut SolverBudget,
        param_env: &ParamEnv,
        polarity: GoalPolarity,
        trait_key: &TraitKey,
        subject: &ProvisionalType,
        arguments: &[GenericArg],
        bindings: &[AssociatedValue],
    ) -> SolveReport {
        if self.schema_by_key(trait_key).is_none_or(|schema| {
            schema.parameters.len() != arguments.len()
                || !schema
                    .parameters
                    .iter()
                    .zip(arguments)
                    .all(|(kind, argument)| match (kind, argument) {
                        (GenericParameterKind::Type, GenericArg::Type(_)) => true,
                        (GenericParameterKind::Lifetime, GenericArg::Lifetime(_)) => true,
                        (GenericParameterKind::Const(kind), argument) => {
                            generic_arg_has_const_kind(argument, *kind)
                        }
                        _ => false,
                    })
        }) {
            return SolveReport {
                result: SolveResult::NoEvidence,
                failure: None,
            };
        }
        let mut tables = BTreeMap::new();
        let mut diagnostics = SolverDiagnostics::default();
        let mut canonical_bindings = bindings.to_vec();
        canonical_bindings.sort();
        canonical_bindings.dedup();
        let goal = GroundGoal {
            polarity,
            trait_key: trait_key.clone(),
            subject: subject.clone(),
            arguments: arguments.to_vec(),
            bindings: canonical_bindings,
            projections: vec![],
        };
        let answer = self.solve_inner(
            goal.clone(),
            param_env,
            &mut tables,
            0,
            &mut budget.steps,
            &mut budget.projection_steps,
            &mut diagnostics,
        );
        if answer.result != SolveResult::NoEvidence {
            return SolveReport {
                result: answer.result,
                failure: diagnostics.failure_for(answer.result),
            };
        }
        let inverse = GroundGoal {
            polarity: match polarity {
                GoalPolarity::Positive => GoalPolarity::Negative,
                GoalPolarity::Negative => GoalPolarity::Positive,
            },
            bindings: vec![],
            projections: vec![],
            ..goal
        };
        let inverse_answer = self.solve_inner(
            inverse,
            param_env,
            &mut tables,
            0,
            &mut budget.steps,
            &mut budget.projection_steps,
            &mut diagnostics,
        );
        let result = match inverse_answer.result {
            SolveResult::Proven => SolveResult::Refuted,
            SolveResult::Ambiguous => SolveResult::Ambiguous,
            SolveResult::Overflow => SolveResult::Overflow,
            SolveResult::Refuted | SolveResult::NoEvidence => SolveResult::NoEvidence,
        };
        SolveReport {
            result,
            failure: diagnostics.failure_for(result),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn solve_inner(
        &self,
        goal: GroundGoal,
        param_env: &ParamEnv,
        tables: &mut BTreeMap<TableKey, TableState>,
        depth: usize,
        steps: &mut usize,
        projection_steps: &mut usize,
        diagnostics: &mut SolverDiagnostics,
    ) -> TableAnswer {
        *steps = steps.saturating_add(1);
        let table_key = TableKey {
            goal: goal.clone(),
            param_env: param_env.clone(),
        };
        if *steps > MAX_STEPS {
            diagnostics.record_limit(SolverLimit::Steps, Some(&table_key));
            return table_answer(SolveResult::Overflow);
        }
        if let Some(state) = tables.get(&table_key) {
            return match state {
                TableState::Evaluating => {
                    diagnostics.record_cycle(&table_key);
                    table_answer(SolveResult::Ambiguous)
                }
                TableState::Complete(answer) => {
                    diagnostics.consider_cycle(&answer.cycle_trace);
                    answer.clone()
                }
            };
        }
        if depth >= MAX_DEPTH {
            diagnostics.record_limit(SolverLimit::NestedFrames, Some(&table_key));
            return table_answer(SolveResult::Overflow);
        }
        if tables.len() >= MAX_TABLES {
            diagnostics.record_limit(SolverLimit::Tables, Some(&table_key));
            return table_answer(SolveResult::Overflow);
        }
        tables.insert(table_key.clone(), TableState::Evaluating);
        diagnostics.active.push(table_key.clone());
        let lexical = lexical_answer(&goal, param_env);
        if lexical.result != SolveResult::NoEvidence {
            tables.insert(table_key, TableState::Complete(lexical.clone()));
            diagnostics.active.pop();
            return lexical;
        }
        if self.intrinsic_use_key.as_ref() == Some(&goal.trait_key)
            && Self::predefined_use_contains(&goal)
        {
            let answer = table_answer(SolveResult::Proven);
            tables.insert(table_key, TableState::Complete(answer.clone()));
            diagnostics.active.pop();
            return answer;
        }
        if goal.polarity == GoalPolarity::Positive
            && self.intrinsic_use_key.as_ref() == Some(&goal.trait_key)
            && let ProvisionalType::Nominal(instance) = &goal.subject
            && self.array_nominal.as_ref() == Some(&instance.declaration)
            && let [element] = instance.arguments.as_slice()
        {
            let answer = self.solve_inner(
                GroundGoal {
                    subject: element.clone(),
                    ..goal.clone()
                },
                param_env,
                tables,
                depth + 1,
                steps,
                projection_steps,
                diagnostics,
            );
            tables.insert(table_key, TableState::Complete(answer.clone()));
            diagnostics.active.pop();
            return answer;
        }
        let mut answers = 0usize;
        let mut distinct_answers = BTreeSet::new();
        let mut uncertain = None;
        let mut associated_values = BTreeMap::new();
        let candidate_indices = self.candidate_indices(&goal);
        for implementation in candidate_indices
            .into_iter()
            .map(|index| &self.impls[index])
        {
            let mut substitutions = BTreeMap::new();
            if !self.matches_candidate(&implementation.head, &goal, &mut substitutions) {
                continue;
            }
            let mut candidate = SolveResult::Proven;
            for goal in implementation
                .super_goals
                .iter()
                .chain(&implementation.goals)
            {
                let instantiated = match self.instantiate_goal(
                    goal,
                    &substitutions,
                    param_env,
                    tables,
                    depth + 1,
                    steps,
                    projection_steps,
                    diagnostics,
                ) {
                    Ok(goal) => goal,
                    Err(result) => {
                        candidate = result;
                        break;
                    }
                };
                let answer = self.solve_inner(
                    instantiated,
                    param_env,
                    tables,
                    depth + 1,
                    steps,
                    projection_steps,
                    diagnostics,
                );
                if answer.result != SolveResult::Proven {
                    candidate = answer.result;
                    break;
                }
            }
            let mut candidate_values = BTreeMap::new();
            if candidate == SolveResult::Proven {
                let requested = goal
                    .bindings
                    .iter()
                    .map(AssociatedValue::key)
                    .chain(goal.projections.iter().cloned())
                    .collect::<BTreeSet<_>>();
                for key in requested {
                    let Some(definition) = implementation
                        .associated_values
                        .iter()
                        .find(|definition| definition.item == key.item)
                    else {
                        candidate = SolveResult::NoEvidence;
                        break;
                    };
                    let mut item_substitutions = substitutions.clone();
                    if definition.arguments.len() != key.arguments.len()
                        || !definition.arguments.iter().zip(&key.arguments).all(
                            |(pattern, actual)| {
                                matches_generic_arg(pattern, actual, &mut item_substitutions)
                            },
                        )
                    {
                        candidate = SolveResult::NoEvidence;
                        break;
                    }
                    match self.instantiate_pattern(
                        &definition.value,
                        &item_substitutions,
                        param_env,
                        tables,
                        depth + 1,
                        steps,
                        projection_steps,
                        diagnostics,
                    ) {
                        Ok(value) => {
                            candidate_values.insert(key, value);
                        }
                        Err(result) => {
                            candidate = result;
                            break;
                        }
                    }
                }
            }
            if candidate == SolveResult::Proven
                && goal
                    .bindings
                    .iter()
                    .any(|binding| candidate_values.get(&binding.key()) != Some(&binding.value))
            {
                candidate = SolveResult::NoEvidence;
            }
            match candidate {
                SolveResult::Proven => {
                    answers += 1;
                    distinct_answers.insert(candidate_values.clone());
                    if distinct_answers.len() > MAX_ANSWERS_PER_TABLE {
                        diagnostics.record_limit(SolverLimit::AnswersPerTable, None);
                        uncertain = Some(SolveResult::Overflow);
                        break;
                    }
                    associated_values = candidate_values;
                }
                SolveResult::Ambiguous | SolveResult::Overflow => uncertain = Some(candidate),
                SolveResult::Refuted | SolveResult::NoEvidence => {}
            }
        }
        let proven = (goal.polarity == GoalPolarity::Negative && answers > 0)
            || (goal.polarity == GoalPolarity::Positive && answers == 1 && uncertain.is_none());
        let result = if proven {
            SolveResult::Proven
        } else if uncertain == Some(SolveResult::Overflow) {
            SolveResult::Overflow
        } else if answers > 1 || uncertain == Some(SolveResult::Ambiguous) {
            SolveResult::Ambiguous
        } else {
            SolveResult::NoEvidence
        };
        let answer = TableAnswer {
            result,
            associated_values: if result == SolveResult::Proven {
                associated_values
            } else {
                BTreeMap::new()
            },
            cycle_trace: (result == SolveResult::Ambiguous)
                .then(|| diagnostics.cycle.clone())
                .flatten(),
        };
        tables.insert(table_key, TableState::Complete(answer.clone()));
        diagnostics.active.pop();
        answer
    }

    #[cfg(test)]
    pub(crate) fn normalize_type(
        &self,
        syntax: &TypeSyntax,
    ) -> Result<ProvisionalType, SolveResult> {
        self.normalize_type_detailed(syntax)
            .map_err(|report| report.result)
    }

    #[cfg(test)]
    pub(crate) fn normalize_type_detailed(
        &self,
        syntax: &TypeSyntax,
    ) -> Result<ProvisionalType, SolveReport> {
        let mut budget = SolverBudget::default();
        self.normalize_type_detailed_with_budget(syntax, &mut budget)
    }

    pub(crate) fn normalize_type_detailed_with_budget(
        &self,
        syntax: &TypeSyntax,
        budget: &mut SolverBudget,
    ) -> Result<ProvisionalType, SolveReport> {
        std::thread::scope(|scope| {
            std::thread::Builder::new()
                .name("grandiose-projection-normalizer".into())
                .stack_size(8 * 1024 * 1024)
                .spawn_scoped(scope, || self.normalize_type_inner(syntax, budget))
                .map_err(|_| SolveReport {
                    result: SolveResult::Overflow,
                    failure: Some(SolveFailure::Limit {
                        limit: SolverLimit::NestedFrames,
                        trace: vec![],
                    }),
                })?
                .join()
                .unwrap_or_else(|_| {
                    Err(SolveReport {
                        result: SolveResult::Overflow,
                        failure: Some(SolveFailure::Limit {
                            limit: SolverLimit::NestedFrames,
                            trace: vec![],
                        }),
                    })
                })
        })
    }

    pub(crate) fn normalize_effect_row_projection_with_budget(
        &self,
        syntax: &TypeSyntax,
        budget: &mut SolverBudget,
    ) -> Result<Vec<crate::compiler_typeck::CallableEffect>, SolveReport> {
        let TypeSyntaxKind::Projection {
            subject,
            trait_ref,
            item,
            arguments: item_arguments,
            const_arguments: item_const_arguments,
        } = &syntax.kind
        else {
            return Err(SolveReport {
                result: SolveResult::NoEvidence,
                failure: None,
            });
        };
        let trait_name = relation_name(trait_ref).map_err(|_| SolveReport {
            result: SolveResult::NoEvidence,
            failure: None,
        })?;
        let schema = self.traits.get(&trait_name).ok_or(SolveReport {
            result: SolveResult::NoEvidence,
            failure: None,
        })?;
        let associated_item = schema.associated_items.get(&item.name).ok_or(SolveReport {
            result: SolveResult::NoEvidence,
            failure: None,
        })?;
        if associated_item.kind != AssociatedItemKind::EffectRow
            || trait_ref.arguments.len() != schema.parameters.len()
        {
            return Err(SolveReport {
                result: SolveResult::NoEvidence,
                failure: None,
            });
        }
        let binders = BTreeMap::new();
        let projection = Pattern::Projection {
            subject: Box::new(
                pattern_with_const_arguments(
                    subject,
                    &binders,
                    &self.nominals,
                    &self.traits,
                    false,
                    &self.type_const_arguments,
                )
                .map_err(|_| SolveReport {
                    result: SolveResult::NoEvidence,
                    failure: None,
                })?,
            ),
            trait_key: schema.key.clone(),
            arguments: lower_generic_arguments(
                &trait_ref.arguments,
                &schema.parameters,
                &binders,
                &self.nominals,
                &self.traits,
            )
            .map_err(|_| SolveReport {
                result: SolveResult::NoEvidence,
                failure: None,
            })?,
            item: item.name.clone(),
            item_arguments: lower_associated_arguments(
                item_arguments,
                item_const_arguments,
                &associated_item.parameters,
                &binders,
                &self.nominals,
                &self.traits,
            )
            .map_err(|_| SolveReport {
                result: SolveResult::NoEvidence,
                failure: None,
            })?,
        };
        let mut tables = BTreeMap::new();
        let mut diagnostics = SolverDiagnostics::default();
        let normalized = self
            .instantiate_pattern(
                &projection,
                &BTreeMap::new(),
                &ParamEnv::default(),
                &mut tables,
                0,
                &mut budget.steps,
                &mut budget.projection_steps,
                &mut diagnostics,
            )
            .map_err(|result| SolveReport {
                result,
                failure: diagnostics.failure_for(result),
            })?;
        let ProvisionalType::Tuple(members) = normalized else {
            return Err(SolveReport {
                result: SolveResult::NoEvidence,
                failure: None,
            });
        };
        members
            .into_iter()
            .map(|member| {
                let ProvisionalType::Nominal(instance) = member else {
                    return Err(SolveReport {
                        result: SolveResult::NoEvidence,
                        failure: None,
                    });
                };
                let Some(name) = instance
                    .declaration
                    .0
                    .strip_prefix(EFFECT_ROW_MEMBER_PREFIX)
                else {
                    return Err(SolveReport {
                        result: SolveResult::NoEvidence,
                        failure: None,
                    });
                };
                Ok(crate::compiler_typeck::CallableEffect {
                    declaration: crate::compiler_typeck::ProtocolKey(name.to_owned()),
                    arguments: instance.arguments,
                })
            })
            .collect()
    }

    pub(crate) fn normalize_symbolic_effect_row_projection_with_budget(
        &self,
        syntax: &TypeSyntax,
        symbolic_binders: &BTreeMap<String, ProvisionalType>,
        param_env: &ParamEnv,
        budget: &mut SolverBudget,
    ) -> Result<Vec<crate::compiler_typeck::CallableEffect>, SolveReport> {
        let TypeSyntaxKind::Projection {
            subject,
            trait_ref,
            item,
            arguments: item_arguments,
            const_arguments: item_const_arguments,
        } = &syntax.kind
        else {
            return Err(SolveReport {
                result: SolveResult::NoEvidence,
                failure: None,
            });
        };
        let trait_name = relation_name(trait_ref).map_err(|_| SolveReport {
            result: SolveResult::NoEvidence,
            failure: None,
        })?;
        let schema = self.traits.get(&trait_name).ok_or(SolveReport {
            result: SolveResult::NoEvidence,
            failure: None,
        })?;
        let associated_item = schema.associated_items.get(&item.name).ok_or(SolveReport {
            result: SolveResult::NoEvidence,
            failure: None,
        })?;
        if associated_item.kind != AssociatedItemKind::EffectRow
            || trait_ref.arguments.len() != schema.parameters.len()
        {
            return Err(SolveReport {
                result: SolveResult::NoEvidence,
                failure: None,
            });
        }
        let binders = symbolic_binders
            .keys()
            .enumerate()
            .map(|(index, name)| {
                (
                    name.as_str(),
                    Binder {
                        index: index as u32,
                        kind: GenericParameterKind::Type,
                        higher_ranked: false,
                    },
                )
            })
            .collect::<BTreeMap<_, _>>();
        let substitutions = binders
            .iter()
            .map(|(name, binder)| {
                (
                    binder.index,
                    GenericArg::Type(symbolic_binders[*name].clone()),
                )
            })
            .collect::<BTreeMap<_, _>>();
        let projection = Pattern::Projection {
            subject: Box::new(
                pattern_with_const_arguments(
                    subject,
                    &binders,
                    &self.nominals,
                    &self.traits,
                    false,
                    &self.type_const_arguments,
                )
                .map_err(|_| SolveReport {
                    result: SolveResult::NoEvidence,
                    failure: None,
                })?,
            ),
            trait_key: schema.key.clone(),
            arguments: lower_generic_arguments(
                &trait_ref.arguments,
                &schema.parameters,
                &binders,
                &self.nominals,
                &self.traits,
            )
            .map_err(|_| SolveReport {
                result: SolveResult::NoEvidence,
                failure: None,
            })?,
            item: item.name.clone(),
            item_arguments: lower_associated_arguments(
                item_arguments,
                item_const_arguments,
                &associated_item.parameters,
                &binders,
                &self.nominals,
                &self.traits,
            )
            .map_err(|_| SolveReport {
                result: SolveResult::NoEvidence,
                failure: None,
            })?,
        };
        let mut tables = BTreeMap::new();
        let mut diagnostics = SolverDiagnostics::default();
        let normalized = self
            .instantiate_pattern(
                &projection,
                &substitutions,
                param_env,
                &mut tables,
                0,
                &mut budget.steps,
                &mut budget.projection_steps,
                &mut diagnostics,
            )
            .map_err(|result| SolveReport {
                result,
                failure: diagnostics.failure_for(result),
            })?;
        let ProvisionalType::Tuple(members) = normalized else {
            return Err(SolveReport {
                result: SolveResult::NoEvidence,
                failure: None,
            });
        };
        members
            .into_iter()
            .map(|member| {
                if let ProvisionalType::Param(parameter) = member {
                    return Ok(crate::compiler_typeck::CallableEffect {
                        declaration: crate::compiler_typeck::ProtocolKey(
                            EFFECT_ROW_TAIL_PREFIX.to_owned(),
                        ),
                        arguments: vec![ProvisionalType::Param(parameter)],
                    });
                }
                let ProvisionalType::Nominal(instance) = member else {
                    return Err(SolveReport {
                        result: SolveResult::NoEvidence,
                        failure: None,
                    });
                };
                let Some(name) = instance
                    .declaration
                    .0
                    .strip_prefix(EFFECT_ROW_MEMBER_PREFIX)
                else {
                    return Err(SolveReport {
                        result: SolveResult::NoEvidence,
                        failure: None,
                    });
                };
                Ok(crate::compiler_typeck::CallableEffect {
                    declaration: crate::compiler_typeck::ProtocolKey(name.to_owned()),
                    arguments: instance.arguments,
                })
            })
            .collect()
    }

    pub(crate) fn normalize_symbolic_type_with_budget(
        &self,
        syntax: &TypeSyntax,
        symbolic_binders: &BTreeMap<String, ProvisionalType>,
        param_env: &ParamEnv,
        budget: &mut SolverBudget,
    ) -> Result<ProvisionalType, SolveReport> {
        let binders = symbolic_binders
            .keys()
            .enumerate()
            .map(|(index, name)| {
                (
                    name.as_str(),
                    Binder {
                        index: index as u32,
                        kind: GenericParameterKind::Type,
                        higher_ranked: false,
                    },
                )
            })
            .collect::<BTreeMap<_, _>>();
        let substitutions = binders
            .iter()
            .map(|(name, binder)| {
                (
                    binder.index,
                    GenericArg::Type(symbolic_binders[*name].clone()),
                )
            })
            .collect::<BTreeMap<_, _>>();
        let pattern = pattern_with_const_arguments(
            syntax,
            &binders,
            &self.nominals,
            &self.traits,
            false,
            &self.type_const_arguments,
        )
        .map_err(|_| SolveReport {
            result: SolveResult::NoEvidence,
            failure: None,
        })?;
        let mut tables = BTreeMap::new();
        let mut diagnostics = SolverDiagnostics::default();
        self.instantiate_pattern(
            &pattern,
            &substitutions,
            param_env,
            &mut tables,
            0,
            &mut budget.steps,
            &mut budget.projection_steps,
            &mut diagnostics,
        )
        .map_err(|result| SolveReport {
            result,
            failure: diagnostics.failure_for(result),
        })
    }

    fn normalize_type_inner(
        &self,
        syntax: &TypeSyntax,
        budget: &mut SolverBudget,
    ) -> Result<ProvisionalType, SolveReport> {
        let pattern = pattern_with_const_arguments(
            syntax,
            &BTreeMap::new(),
            &self.nominals,
            &self.traits,
            false,
            &self.type_const_arguments,
        )
        .map_err(|_| SolveReport {
            result: SolveResult::NoEvidence,
            failure: None,
        })?;
        let mut tables = BTreeMap::new();
        let mut diagnostics = SolverDiagnostics::default();
        self.instantiate_pattern(
            &pattern,
            &BTreeMap::new(),
            &ParamEnv::default(),
            &mut tables,
            0,
            &mut budget.steps,
            &mut budget.projection_steps,
            &mut diagnostics,
        )
        .map_err(|result| SolveReport {
            result,
            failure: diagnostics.failure_for(result),
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn instantiate_pattern(
        &self,
        pattern: &Pattern,
        substitutions: &BTreeMap<u32, GenericArg>,
        param_env: &ParamEnv,
        tables: &mut BTreeMap<TableKey, TableState>,
        depth: usize,
        steps: &mut usize,
        projection_steps: &mut usize,
        diagnostics: &mut SolverDiagnostics,
    ) -> Result<ProvisionalType, SolveResult> {
        match pattern {
            Pattern::Bound(index) => substitutions
                .get(index)
                .and_then(|argument| match argument {
                    GenericArg::Type(ty) => Some(ty.clone()),
                    GenericArg::Lifetime(_)
                    | GenericArg::Const(_)
                    | GenericArg::RigidConst(_, _) => None,
                })
                .ok_or(SolveResult::NoEvidence),
            Pattern::Ground(ty) => Ok(instantiate_ground_pattern(ty, depth as u32 + 1)),
            Pattern::Nominal(declaration, arguments) => {
                Ok(ProvisionalType::Nominal(NominalInstanceKey {
                    declaration: declaration.clone(),
                    arguments: arguments
                        .iter()
                        .map(|argument| match argument {
                            NominalPatternArg::Type(argument) => self.instantiate_pattern(
                                argument,
                                substitutions,
                                param_env,
                                tables,
                                depth,
                                steps,
                                projection_steps,
                                diagnostics,
                            ),
                            NominalPatternArg::Const(argument) => {
                                instantiate_const_pattern(argument, substitutions)
                                    .ok_or(SolveResult::NoEvidence)
                            }
                        })
                        .collect::<Result<Vec<_>, _>>()?,
                }))
            }
            Pattern::Shared(referent) => Ok(ProvisionalType::Shared(Box::new(
                self.instantiate_pattern(
                    referent,
                    substitutions,
                    param_env,
                    tables,
                    depth,
                    steps,
                    projection_steps,
                    diagnostics,
                )?,
            ))),
            Pattern::Unique(referent) => Ok(ProvisionalType::Unique(Box::new(
                self.instantiate_pattern(
                    referent,
                    substitutions,
                    param_env,
                    tables,
                    depth,
                    steps,
                    projection_steps,
                    diagnostics,
                )?,
            ))),
            Pattern::Tuple(elements) => Ok(ProvisionalType::Tuple(
                elements
                    .iter()
                    .map(|element| {
                        self.instantiate_pattern(
                            element,
                            substitutions,
                            param_env,
                            tables,
                            depth,
                            steps,
                            projection_steps,
                            diagnostics,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            Pattern::Projection {
                subject,
                trait_key,
                arguments,
                item,
                item_arguments,
            } => {
                *projection_steps = projection_steps.saturating_add(1);
                if *projection_steps > MAX_PROJECTION_STEPS {
                    diagnostics.record_limit(SolverLimit::ProjectionSteps, None);
                    return Err(SolveResult::Overflow);
                }
                let subject = self.instantiate_pattern(
                    subject,
                    substitutions,
                    param_env,
                    tables,
                    depth,
                    steps,
                    projection_steps,
                    diagnostics,
                )?;
                let arguments = arguments
                    .iter()
                    .map(|argument| {
                        self.instantiate_generic_pattern(
                            argument,
                            substitutions,
                            param_env,
                            tables,
                            depth,
                            steps,
                            projection_steps,
                            diagnostics,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let item_arguments = item_arguments
                    .iter()
                    .map(|argument| {
                        self.instantiate_generic_pattern(
                            argument,
                            substitutions,
                            param_env,
                            tables,
                            depth,
                            steps,
                            projection_steps,
                            diagnostics,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let schema = self
                    .schema_by_key(trait_key)
                    .ok_or(SolveResult::NoEvidence)?;
                if schema.parameters.len() != arguments.len()
                    || schema.associated_types.get(item).map(Vec::len) != Some(item_arguments.len())
                {
                    return Err(SolveResult::NoEvidence);
                }
                let key = AssociatedKey {
                    item: item.clone(),
                    arguments: item_arguments,
                };
                let answer = self.solve_inner(
                    GroundGoal {
                        polarity: GoalPolarity::Positive,
                        trait_key: trait_key.clone(),
                        subject,
                        arguments,
                        bindings: vec![],
                        projections: vec![key.clone()],
                    },
                    param_env,
                    tables,
                    depth,
                    steps,
                    projection_steps,
                    diagnostics,
                );
                if answer.result != SolveResult::Proven {
                    return Err(answer.result);
                }
                answer
                    .associated_values
                    .get(&key)
                    .cloned()
                    .ok_or(SolveResult::NoEvidence)
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn instantiate_generic_pattern(
        &self,
        pattern: &GenericArgPattern,
        substitutions: &BTreeMap<u32, GenericArg>,
        param_env: &ParamEnv,
        tables: &mut BTreeMap<TableKey, TableState>,
        depth: usize,
        steps: &mut usize,
        projection_steps: &mut usize,
        diagnostics: &mut SolverDiagnostics,
    ) -> Result<GenericArg, SolveResult> {
        match pattern {
            GenericArgPattern::Type(pattern) => self
                .instantiate_pattern(
                    pattern,
                    substitutions,
                    param_env,
                    tables,
                    depth,
                    steps,
                    projection_steps,
                    diagnostics,
                )
                .map(GenericArg::Type),
            GenericArgPattern::Lifetime(LifetimePattern::Static) => {
                Ok(GenericArg::Lifetime(LifetimeArg::Static))
            }
            GenericArgPattern::Lifetime(LifetimePattern::Bound(index)) => substitutions
                .get(index)
                .filter(|argument| matches!(argument, GenericArg::Lifetime(_)))
                .cloned()
                .ok_or(SolveResult::NoEvidence),
            GenericArgPattern::Lifetime(LifetimePattern::HigherRanked(index)) => {
                Ok(GenericArg::Lifetime(LifetimeArg::Placeholder {
                    universe: depth as u32 + 1,
                    index: *index,
                }))
            }
            GenericArgPattern::Const(ConstPattern::Value(value)) => {
                Ok(GenericArg::Const(value.clone()))
            }
            GenericArgPattern::Const(ConstPattern::Bound(index, kind)) => {
                instantiate_bound_const(*index, *kind, substitutions, depth as u32 + 1)
                    .ok_or(SolveResult::NoEvidence)
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn instantiate_goal(
        &self,
        pattern: &GoalPattern,
        substitutions: &BTreeMap<u32, GenericArg>,
        param_env: &ParamEnv,
        tables: &mut BTreeMap<TableKey, TableState>,
        depth: usize,
        steps: &mut usize,
        projection_steps: &mut usize,
        diagnostics: &mut SolverDiagnostics,
    ) -> Result<GroundGoal, SolveResult> {
        Ok(GroundGoal {
            polarity: pattern.polarity,
            trait_key: pattern.trait_key.clone(),
            subject: self.instantiate_pattern(
                &pattern.subject,
                substitutions,
                param_env,
                tables,
                depth,
                steps,
                projection_steps,
                diagnostics,
            )?,
            arguments: pattern
                .arguments
                .iter()
                .map(|argument| match argument {
                    GenericArgPattern::Type(argument) => self
                        .instantiate_pattern(
                            argument,
                            substitutions,
                            param_env,
                            tables,
                            depth,
                            steps,
                            projection_steps,
                            diagnostics,
                        )
                        .map(GenericArg::Type),
                    GenericArgPattern::Lifetime(LifetimePattern::Static) => {
                        Ok(GenericArg::Lifetime(LifetimeArg::Static))
                    }
                    GenericArgPattern::Lifetime(LifetimePattern::Bound(index)) => substitutions
                        .get(index)
                        .filter(|argument| matches!(argument, GenericArg::Lifetime(_)))
                        .cloned()
                        .ok_or(SolveResult::NoEvidence),
                    GenericArgPattern::Lifetime(LifetimePattern::HigherRanked(index)) => {
                        Ok(GenericArg::Lifetime(LifetimeArg::Placeholder {
                            universe: depth as u32 + 1,
                            index: *index,
                        }))
                    }
                    GenericArgPattern::Const(ConstPattern::Value(value)) => {
                        Ok(GenericArg::Const(value.clone()))
                    }
                    GenericArgPattern::Const(ConstPattern::Bound(index, kind)) => {
                        instantiate_bound_const(*index, *kind, substitutions, depth as u32 + 1)
                            .ok_or(SolveResult::NoEvidence)
                    }
                })
                .collect::<Result<Vec<_>, _>>()?,
            bindings: pattern
                .bindings
                .iter()
                .map(|binding| {
                    Ok(AssociatedValue {
                        item: binding.item.clone(),
                        arguments: binding
                            .arguments
                            .iter()
                            .map(|argument| {
                                self.instantiate_generic_pattern(
                                    argument,
                                    substitutions,
                                    param_env,
                                    tables,
                                    depth,
                                    steps,
                                    projection_steps,
                                    diagnostics,
                                )
                            })
                            .collect::<Result<Vec<_>, _>>()?,
                        value: self.instantiate_pattern(
                            &binding.value,
                            substitutions,
                            param_env,
                            tables,
                            depth,
                            steps,
                            projection_steps,
                            diagnostics,
                        )?,
                    })
                })
                .collect::<Result<Vec<_>, SolveResult>>()?,
            projections: vec![],
        })
    }

    pub(crate) fn canonical_text(&self) -> String {
        let mut output = String::new();
        for (name, schema) in &self.traits {
            writeln!(
                output,
                "trait {:?} {name} {:?} {:?} {:?} {:?} {:?} {:?}",
                schema.key,
                schema.parameters,
                schema.associated_items,
                schema.supertraits,
                schema.dedicated_use_requirement,
                schema.policy,
                schema.role
            )
            .unwrap();
        }
        for implementation in &self.impls {
            writeln!(output, "impl {implementation:?}").unwrap();
        }
        output
    }

    #[allow(dead_code)]
    pub(crate) fn fingerprint(&self) -> u64 {
        let mut hash = 0xcbf29ce484222325_u64;
        for byte in self.canonical_text().bytes() {
            hash ^= u64::from(byte);
            hash = hash.wrapping_mul(0x100000001b3);
        }
        hash
    }
}

fn effect_row_pattern(
    row: &crate::ast::EffectRowSyntax,
    binders: &BTreeMap<&str, Binder>,
    nominals: &BTreeMap<String, NominalSchema>,
    traits: &BTreeMap<String, TraitSchema>,
    effects: &BTreeMap<String, usize>,
) -> Result<Pattern, Diagnostic> {
    let mut members = row
        .effects
        .iter()
        .map(|member| {
            let (name, arguments) = match &member.kind {
                TypeSyntaxKind::Path(path) if path.len() == 1 => {
                    (path[0].name.as_str(), [].as_slice())
                }
                TypeSyntaxKind::Application {
                    constructor,
                    arguments,
                    ..
                } => (
                    constructor.simple_name().ok_or_else(|| {
                        error(
                            member.span,
                            "effect-row members require a named effect constructor",
                        )
                    })?,
                    arguments.as_slice(),
                ),
                _ => {
                    return Err(error(
                        member.span,
                        "associated effect rows contain only declared effect applications",
                    ));
                }
            };
            let Some(expected) = effects.get(name) else {
                return Err(error(
                    member.span,
                    format!("unknown effect `{name}` in associated effect row"),
                ));
            };
            if *expected != arguments.len() {
                return Err(error(
                    member.span,
                    format!(
                        "effect `{name}` expects {expected} type argument(s), found {}",
                        arguments.len()
                    ),
                ));
            }
            Ok(Pattern::Nominal(
                NominalKey(format!("{EFFECT_ROW_MEMBER_PREFIX}{name}")),
                arguments
                    .iter()
                    .map(|argument| {
                        pattern(argument, binders, nominals, traits, false)
                            .map(NominalPatternArg::Type)
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            ))
        })
        .collect::<Result<Vec<_>, Diagnostic>>()?;
    if let Some(tail) = &row.tail {
        let binder = binders.get(tail.name.as_str()).ok_or_else(|| {
            error(
                tail.span,
                format!("unbound associated effect-row tail `{}`", tail.name),
            )
        })?;
        if binder.kind != GenericParameterKind::Type {
            return Err(error(
                tail.span,
                "associated effect-row tail has the wrong kind",
            ));
        }
        members.push(if binder.higher_ranked {
            Pattern::Ground(ProvisionalType::Param(GenericParamKey {
                owner: DeclarationKey::Function("$higher_ranked_universe_1".into()),
                ordinal: binder.index,
            }))
        } else {
            Pattern::Bound(binder.index)
        });
    }
    members.sort();
    members.dedup();
    Ok(Pattern::Tuple(members))
}

#[allow(clippy::too_many_arguments)]
fn lower_impl(
    declaration: &ImplDecl,
    traits: &BTreeMap<String, TraitSchema>,
    nominals: &BTreeMap<String, NominalSchema>,
    local_owners: &BTreeSet<String>,
    generic_aliases: &BTreeMap<String, &crate::ast::TypeAliasDecl>,
    monomorphic_aliases: &BTreeMap<String, TypeSyntax>,
    effects: &BTreeMap<String, usize>,
    type_const_arguments: &BTreeMap<(usize, usize), Vec<crate::ast::ConstAssociatedArgumentSyntax>>,
    dedicated_authority: bool,
) -> Result<ImplEntry, Diagnostic> {
    let trait_name = relation_name(&declaration.trait_ref)?;
    let relation_arguments = &declaration.trait_ref.arguments;
    let Some(schema) = traits.get(&trait_name) else {
        return Err(error(
            declaration.span,
            format!("unknown trait `{trait_name}`"),
        ));
    };
    match schema.policy {
        TraitPolicy::CompilerSealed => {
            return Err(error(
                declaration.span,
                format!("source impls for sealed external trait `{trait_name}` are unsupported"),
            ));
        }
        TraitPolicy::DedicatedUse | TraitPolicy::DedicatedDrop if !dedicated_authority => {
            return Err(error(
                declaration.span,
                format!("intrinsic trait `{trait_name}` requires its dedicated declaration form"),
            ));
        }
        TraitPolicy::DedicatedUse | TraitPolicy::DedicatedDrop => {}
        TraitPolicy::ExternalOpen => {}
    }
    if schema.parameters.len() != relation_arguments.len() {
        return Err(error(
            declaration.span,
            format!("wrong arity for trait `{trait_name}`"),
        ));
    }
    let definition_names = declaration
        .associated_types
        .iter()
        .map(|definition| definition.name.clone())
        .collect::<BTreeSet<_>>();
    let schema_names = schema
        .associated_types
        .keys()
        .cloned()
        .collect::<BTreeSet<_>>();
    if declaration.polarity == GoalPolarity::Negative && !definition_names.is_empty() {
        return Err(error(
            declaration.span,
            "negative implementations cannot define associated types",
        ));
    }
    if declaration.polarity == GoalPolarity::Positive && definition_names != schema_names {
        let missing = schema
            .associated_types
            .keys()
            .filter(|name| !definition_names.contains(*name))
            .cloned()
            .collect::<Vec<_>>();
        let extra = definition_names
            .difference(&schema_names)
            .cloned()
            .collect::<Vec<_>>();
        return Err(error(
            declaration.span,
            format!(
                "associated type definitions must be complete and exact; missing {missing:?}, extra {extra:?}"
            ),
        ));
    }
    let binders = declaration
        .generics
        .iter()
        .flat_map(|generics| &generics.params)
        .enumerate()
        .map(|(index, parameter)| {
            (
                parameter.name.as_str(),
                Binder {
                    index: index as u32,
                    kind: match parameter.kind {
                        GenericParamKind::Type => GenericParameterKind::Type,
                        GenericParamKind::Lifetime => GenericParameterKind::Lifetime,
                        GenericParamKind::EffectRow => {
                            unreachable!("validated outside callable rows")
                        }
                        GenericParamKind::Const(kind) => GenericParameterKind::Const(kind),
                    },
                    higher_ranked: false,
                },
            )
        })
        .collect::<BTreeMap<_, _>>();
    fn expand_alias_head(
        syntax: &TypeSyntax,
        aliases: &BTreeMap<String, TypeSyntax>,
        generic_aliases: &BTreeMap<String, &crate::ast::TypeAliasDecl>,
        visiting: &mut BTreeSet<String>,
    ) -> Result<TypeSyntax, Diagnostic> {
        if let Some(name) = syntax.simple_name()
            && let Some(target) = aliases.get(name)
        {
            if !visiting.insert(name.to_owned()) {
                return Err(error(
                    syntax.span,
                    format!("type alias cycle contains `{name}`"),
                ));
            }
            let expanded = expand_alias_head(target, aliases, generic_aliases, visiting);
            visiting.remove(name);
            return expanded;
        }
        let TypeSyntaxKind::Application {
            constructor,
            arguments,
            ..
        } = &syntax.kind
        else {
            return Ok(syntax.clone());
        };
        let Some(name) = constructor.simple_name() else {
            return Ok(syntax.clone());
        };
        let Some(alias) = generic_aliases.get(name).copied() else {
            return Ok(syntax.clone());
        };
        if !visiting.insert(name.to_owned()) {
            return Err(error(
                syntax.span,
                format!("generic type alias cycle contains `{name}`"),
            ));
        }
        let params = &alias.generics.as_ref().unwrap().params;
        let identity_target = match &alias.target.kind {
            TypeSyntaxKind::Application {
                constructor: target_constructor,
                arguments: target_arguments,
                ..
            } if params.len() == arguments.len() && params.len() == target_arguments.len() => {
                let identity = params
                    .iter()
                    .zip(target_arguments)
                    .all(|(param, argument)| {
                        matches!(param.kind, GenericParamKind::Type)
                            && argument.simple_name() == Some(param.name.as_str())
                    });
                identity.then_some(target_constructor.as_ref())
            }
            _ => None,
        };
        let Some(target_constructor) = identity_target else {
            visiting.remove(name);
            return Err(error(
                syntax.span,
                "generic type alias impl heads require identity-preserving ordered substitution into one nominal constructor",
            ));
        };
        let expanded = TypeSyntax {
            kind: TypeSyntaxKind::Application {
                constructor: Box::new(target_constructor.clone()),
                arguments: arguments.clone(),
                lifetime_arguments: vec![],
                const_arguments: vec![],
            },
            span: syntax.span,
        };
        let expanded = expand_alias_head(&expanded, aliases, generic_aliases, visiting);
        visiting.remove(name);
        expanded
    }
    let self_ty = expand_alias_head(
        &declaration.self_ty,
        monomorphic_aliases,
        generic_aliases,
        &mut BTreeSet::new(),
    )?;
    let subject = pattern_with_const_arguments(
        &self_ty,
        &binders,
        nominals,
        traits,
        true,
        type_const_arguments,
    )?;
    let outer_name = match &self_ty.kind {
        TypeSyntaxKind::Path(path) if path.len() == 1 => Some(path[0].name.as_str()),
        TypeSyntaxKind::Application { constructor, .. } => constructor.simple_name(),
        _ => None,
    };
    let local_outer = outer_name.is_some_and(|name| local_owners.contains(name));
    if matches!(schema.key, TraitKey::External(_)) && !local_outer {
        return Err(error(
            declaration.span,
            format!(
                "orphan implementation of external trait `{trait_name}` requires a source-local outer nominal type"
            ),
        ));
    }
    let arguments = lower_generic_arguments(
        relation_arguments,
        &schema.parameters,
        &binders,
        nominals,
        traits,
    )?;
    let head = GoalPattern {
        polarity: declaration.polarity,
        trait_key: schema.key.clone(),
        subject,
        arguments,
        bindings: vec![],
    };
    let mut used = BTreeSet::new();
    collect_goal_binders(&head, &mut used);
    // Nominal and reference lifetimes are erased from `Pattern` because they
    // do not contribute to runtime type identity. They still constrain an
    // implementation binder at the source impl head. Preserve that distinction
    // here instead of either retaining regions in runtime patterns or treating
    // every declared lifetime as constrained.
    fn collect_impl_head_lifetime_binders(
        syntax: &TypeSyntax,
        binders: &BTreeMap<&str, Binder>,
        found: &mut BTreeSet<u32>,
    ) {
        fn record(name: &str, binders: &BTreeMap<&str, Binder>, found: &mut BTreeSet<u32>) {
            if let Some(binder) = binders.get(name)
                && binder.kind == GenericParameterKind::Lifetime
                && !binder.higher_ranked
            {
                found.insert(binder.index);
            }
        }
        match &syntax.kind {
            TypeSyntaxKind::Application {
                constructor,
                arguments,
                lifetime_arguments,
                ..
            } => {
                for argument in lifetime_arguments {
                    record(&argument.lifetime.name, binders, found);
                }
                collect_impl_head_lifetime_binders(constructor, binders, found);
                for argument in arguments {
                    collect_impl_head_lifetime_binders(argument, binders, found);
                }
            }
            TypeSyntaxKind::SharedReference { lifetime, referent }
            | TypeSyntaxKind::UniqueReference { lifetime, referent } => {
                if let Some(lifetime) = lifetime {
                    record(&lifetime.name, binders, found);
                }
                collect_impl_head_lifetime_binders(referent, binders, found);
            }
            TypeSyntaxKind::Tuple(elements) => {
                for element in elements {
                    collect_impl_head_lifetime_binders(element, binders, found);
                }
            }
            TypeSyntaxKind::Projection {
                subject,
                trait_ref,
                arguments,
                ..
            } => {
                collect_impl_head_lifetime_binders(subject, binders, found);
                for argument in &trait_ref.arguments {
                    match argument {
                        GoalArgument::Type(ty) => {
                            collect_impl_head_lifetime_binders(ty, binders, found)
                        }
                        GoalArgument::Lifetime { name, .. } => record(name, binders, found),
                        GoalArgument::Quantity(_) | GoalArgument::U32 { .. } => {}
                    }
                }
                for argument in arguments {
                    match argument {
                        AssociatedArgumentSyntax::Type(ty) => {
                            collect_impl_head_lifetime_binders(ty, binders, found)
                        }
                        AssociatedArgumentSyntax::Lifetime { name, .. } => {
                            record(name, binders, found)
                        }
                    }
                }
            }
            TypeSyntaxKind::Path(_) | TypeSyntaxKind::Never => {}
        }
    }
    collect_impl_head_lifetime_binders(&self_ty, &binders, &mut used);
    for argument in relation_arguments {
        match argument {
            GoalArgument::Type(ty) => collect_impl_head_lifetime_binders(ty, &binders, &mut used),
            GoalArgument::Lifetime { name, .. } => {
                if let Some(binder) = binders.get(name.as_str())
                    && binder.kind == GenericParameterKind::Lifetime
                    && !binder.higher_ranked
                {
                    used.insert(binder.index);
                }
            }
            GoalArgument::Quantity(_) | GoalArgument::U32 { .. } => {}
        }
    }
    if used.len() != binders.len() {
        return Err(error(
            declaration.span,
            "every impl binder must be constrained by the impl head",
        ));
    }
    let mut goals = Vec::new();
    for goal in declaration
        .where_clause
        .iter()
        .flat_map(|clause| &clause.goals)
    {
        let mut goal_binders = binders.clone();
        for (index, parameter) in goal.higher_ranked_lifetimes.iter().enumerate() {
            let kind = match parameter.kind {
                GenericParamKind::Type => GenericParameterKind::Type,
                GenericParamKind::Lifetime => GenericParameterKind::Lifetime,
                GenericParamKind::Const(kind) => GenericParameterKind::Const(kind),
                GenericParamKind::EffectRow => GenericParameterKind::Type,
            };
            goal_binders.insert(
                parameter.name.as_str(),
                Binder {
                    index: index as u32,
                    kind,
                    higher_ranked: true,
                },
            );
        }
        let trait_name = relation_name(&goal.relation)?;
        let relation_arguments = &goal.relation.arguments;
        let Some(schema) = traits.get(&trait_name) else {
            return Err(error(
                goal.span,
                format!("unknown trait `{trait_name}` in impl where clause"),
            ));
        };
        if schema.parameters.len() != relation_arguments.len() {
            return Err(error(
                goal.span,
                format!("wrong arity for trait `{trait_name}` in impl where clause"),
            ));
        }
        if goal.polarity == GoalPolarity::Negative && !goal.relation.bindings.is_empty() {
            return Err(error(
                goal.span,
                "negative goals cannot bind associated types",
            ));
        }
        if let Some(binding) = goal
            .relation
            .bindings
            .iter()
            .find(|binding| !schema.associated_items.contains_key(&binding.name))
        {
            return Err(error(
                binding.span,
                format!(
                    "unknown associated type `{}` for `{trait_name}`",
                    binding.name
                ),
            ));
        }
        let mut bindings = goal
            .relation
            .bindings
            .iter()
            .map(|binding| {
                let item = &schema.associated_items[&binding.name];
                (|| {
                    let expected_arity = item.parameters.len();
                    if binding.arguments.len() + binding.const_arguments.len() != expected_arity {
                        return Err(error(
                            binding.span,
                            format!(
                                "wrong arity for associated type `{}`; expected {expected_arity}",
                                binding.name
                            ),
                        ));
                    }
                    Ok(AssociatedPattern {
                        item: binding.name.clone(),
                        arguments: lower_associated_arguments(
                            &binding.arguments,
                            &binding.const_arguments,
                            &item.parameters,
                            &goal_binders,
                            nominals,
                            traits,
                        )?,
                        value: match (&item.kind, &binding.value) {
                            (
                                AssociatedItemKind::Type,
                                crate::ast::AssociatedBindingValue::Type(value),
                            ) => pattern(value, &goal_binders, nominals, traits, false)?,
                            (
                                AssociatedItemKind::EffectRow,
                                crate::ast::AssociatedBindingValue::EffectRow(row),
                            ) => effect_row_pattern(row, &goal_binders, nominals, traits, effects)?,
                            (AssociatedItemKind::Type, _) => {
                                return Err(error(
                                    binding.span,
                                    format!(
                                        "associated type `{}` requires a type value",
                                        binding.name
                                    ),
                                ));
                            }
                            (AssociatedItemKind::EffectRow, _) => {
                                return Err(error(
                                    binding.span,
                                    format!(
                                        "associated effect row `{}` requires `{{...}}` row syntax",
                                        binding.name
                                    ),
                                ));
                            }
                        },
                    })
                })()
            })
            .collect::<Result<Vec<_>, Diagnostic>>()?;
        bindings.sort();
        goals.push(GoalPattern {
            polarity: goal.polarity,
            trait_key: schema.key.clone(),
            subject: pattern(&goal.subject, &goal_binders, nominals, traits, false)?,
            arguments: lower_generic_arguments(
                relation_arguments,
                &schema.parameters,
                &goal_binders,
                nominals,
                traits,
            )?,
            bindings,
        });
    }
    goals.sort();
    goals.dedup();
    let mut associated_values = declaration
        .associated_types
        .iter()
        .map(|definition| {
            let item = &schema.associated_items[&definition.name];
            let expected_kinds = &item.parameters;
            let parameters = definition
                .generics
                .iter()
                .flat_map(|generics| &generics.params)
                .collect::<Vec<_>>();
            if parameters.len() != expected_kinds.len() {
                return Err(error(
                    definition.span,
                    format!(
                        "wrong binder arity for associated type `{}`; expected {}",
                        definition.name
                        , expected_kinds.len()
                    ),
                ));
            }
            let mut item_binders = binders.clone();
            let effect_row_parameters = schema
                .associated_effect_row_parameters
                .get(&definition.name)
                .cloned()
                .unwrap_or_default();
            let arguments = parameters
                .iter()
                .enumerate()
                .zip(expected_kinds)
                .map(|((ordinal, parameter), expected)| {
                    let index = binders.len() as u32 + ordinal as u32;
                    if effect_row_parameters.contains(&ordinal)
                        != (parameter.kind == GenericParamKind::EffectRow)
                    {
                        return Err(error(
                            parameter.span,
                            "associated item binder has the wrong kind",
                        ));
                    }
                    let kind = match parameter.kind {
                        GenericParamKind::Type => GenericParameterKind::Type,
                        GenericParamKind::Lifetime => GenericParameterKind::Lifetime,
                        GenericParamKind::EffectRow if item.kind == AssociatedItemKind::EffectRow => {
                            GenericParameterKind::Type
                        }
                        GenericParamKind::EffectRow => return Err(error(parameter.span,
                            "effect-row binders are valid only on associated effect-row items")),
                        GenericParamKind::Const(kind) => GenericParameterKind::Const(kind),
                    };
                    if &kind != expected {
                        return Err(error(parameter.span, "associated type binder has the wrong kind"));
                    }
                    item_binders.insert(parameter.name.as_str(), Binder { index, kind, higher_ranked: false });
                    Ok(match kind {
                        GenericParameterKind::Type => GenericArgPattern::Type(Pattern::Bound(index)),
                        GenericParameterKind::Lifetime => GenericArgPattern::Lifetime(LifetimePattern::Bound(index)),
                        GenericParameterKind::Const(kind) => GenericArgPattern::Const(ConstPattern::Bound(index, kind)),
                    })
                })
                .collect::<Result<Vec<_>, Diagnostic>>()?;
            let value = match (&item.kind, &definition.value) {
                (AssociatedItemKind::Type, crate::ast::AssociatedBindingValue::Type(value)) => {
                    pattern(value, &item_binders, nominals, traits, false).map_err(|_| {
                        error(
                            definition.value.span(),
                            "associated type definition contains an unresolved or unknown binder or type",
                        )
                    })?
                }
                (
                    AssociatedItemKind::EffectRow,
                    crate::ast::AssociatedBindingValue::EffectRow(row),
                ) => effect_row_pattern(row, &item_binders, nominals, traits, effects)?,
                (AssociatedItemKind::Type, crate::ast::AssociatedBindingValue::EffectRow(_)) => {
                    return Err(error(
                        definition.value.span(),
                        format!("associated type `{}` requires a type value", definition.name),
                    ));
                }
                (AssociatedItemKind::EffectRow, crate::ast::AssociatedBindingValue::Type(_)) => {
                    return Err(error(
                        definition.value.span(),
                        format!(
                            "associated effect row `{}` requires `{{...}}` row syntax",
                            definition.name
                        ),
                    ));
                }
            };
            Ok(AssociatedPattern {
                item: definition.name.clone(),
                arguments,
                value,
            })
        })
        .collect::<Result<Vec<_>, Diagnostic>>()?;
    associated_values.sort();
    let mut super_goals = if declaration.polarity == GoalPolarity::Positive {
        schema
            .supertraits
            .iter()
            .filter_map(|template| instantiate_supertrait_goal_pattern(template, schema, &head))
            .collect()
    } else {
        vec![]
    };
    if declaration.polarity == GoalPolarity::Positive
        && let Some(requirement) = &schema.dedicated_use_requirement
    {
        super_goals.push(GoalPattern {
            polarity: GoalPolarity::Positive,
            trait_key: requirement.trait_key.clone(),
            subject: head.subject.clone(),
            arguments: vec![GenericArgPattern::Const(ConstPattern::Value(
                requirement.value.clone(),
            ))],
            bindings: vec![],
        });
        super_goals.sort();
        super_goals.dedup();
    }
    Ok(ImplEntry {
        binders: binders.len(),
        head,
        super_goals,
        goals,
        associated_values,
    })
}

fn lower_supertraits(
    declaration: &TraitDecl,
    traits: &BTreeMap<String, TraitSchema>,
    nominals: &BTreeMap<String, NominalSchema>,
) -> Result<Vec<SupertraitTemplate>, Vec<Diagnostic>> {
    let mut errors = Vec::new();
    let mut binders = declaration
        .generics
        .iter()
        .flat_map(|generics| &generics.params)
        .enumerate()
        .map(|(index, parameter)| {
            (
                parameter.name.as_str(),
                Binder {
                    index: index as u32,
                    kind: match parameter.kind {
                        GenericParamKind::Type => GenericParameterKind::Type,
                        GenericParamKind::Lifetime => GenericParameterKind::Lifetime,
                        GenericParamKind::EffectRow => {
                            unreachable!("validated outside callable rows")
                        }
                        GenericParamKind::Const(kind) => GenericParameterKind::Const(kind),
                    },
                    higher_ranked: false,
                },
            )
        })
        .collect::<BTreeMap<_, _>>();
    if binders.contains_key("Self") {
        errors.push(error(
            declaration.span,
            "`Self` is reserved as the implicit supertrait subject",
        ));
        return Err(errors);
    }
    binders.insert(
        "Self",
        Binder {
            index: binders.len() as u32,
            kind: GenericParameterKind::Type,
            higher_ranked: false,
        },
    );
    let mut templates = Vec::new();
    for relation in &declaration.supertraits {
        let trait_name = match relation_name(relation) {
            Ok(name) => name,
            Err(diagnostic) => {
                errors.push(diagnostic);
                continue;
            }
        };
        let Some(schema) = traits.get(&trait_name) else {
            errors.push(error(
                relation.span,
                format!("unknown supertrait `{trait_name}`"),
            ));
            continue;
        };
        if schema.policy != TraitPolicy::ExternalOpen {
            errors.push(error(
                relation.span,
                format!(
                    "source supertrait `{trait_name}` is not an ordinary open trait; intrinsic Use and Drop supertraits are not yet supported"
                ),
            ));
            continue;
        }
        let arguments = match lower_generic_arguments(
            &relation.arguments,
            &schema.parameters,
            &binders,
            nominals,
            traits,
        ) {
            Ok(arguments) => arguments
                .into_iter()
                .map(|argument| match argument {
                    GenericArgPattern::Type(pattern) => SuperArgumentPattern::Type(pattern),
                    GenericArgPattern::Lifetime(LifetimePattern::Bound(index)) => {
                        SuperArgumentPattern::LifetimeBound(index)
                    }
                    GenericArgPattern::Lifetime(LifetimePattern::Static) => {
                        SuperArgumentPattern::LifetimeStatic
                    }
                    GenericArgPattern::Lifetime(LifetimePattern::HigherRanked(index)) => {
                        SuperArgumentPattern::LifetimeBound(index)
                    }
                    GenericArgPattern::Const(pattern) => SuperArgumentPattern::Const(pattern),
                })
                .collect(),
            Err(diagnostic) => {
                errors.push(diagnostic);
                continue;
            }
        };
        let mut bindings = Vec::new();
        for binding in &relation.bindings {
            let Some(item) = schema.associated_items.get(&binding.name) else {
                errors.push(error(
                    binding.span,
                    format!(
                        "unknown associated type `{}` for `{trait_name}`",
                        binding.name
                    ),
                ));
                continue;
            };
            if item.kind == AssociatedItemKind::EffectRow {
                continue;
            }
            let expected_arity = item.parameters.len();
            if binding.arguments.len() + binding.const_arguments.len() != expected_arity {
                errors.push(error(
                    binding.span,
                    format!(
                        "wrong arity for associated type `{}`; expected {expected_arity}",
                        binding.name
                    ),
                ));
                continue;
            }
            match lower_associated_arguments(
                &binding.arguments,
                &binding.const_arguments,
                &item.parameters,
                &binders,
                nominals,
                traits,
            )
            .and_then(|arguments| {
                Ok(AssociatedPattern {
                    item: binding.name.clone(),
                    arguments,
                    value: pattern(
                        binding.value.as_type().ok_or_else(|| {
                            error(
                                binding.span,
                                format!("associated type `{}` requires a type value", binding.name),
                            )
                        })?,
                        &binders,
                        nominals,
                        traits,
                        false,
                    )?,
                })
            }) {
                Ok(binding) => bindings.push(binding),
                Err(diagnostic) => errors.push(diagnostic),
            }
        }
        bindings.sort();
        bindings.dedup();
        templates.push(SupertraitTemplate {
            trait_key: schema.key.clone(),
            arguments,
            bindings,
        });
    }
    templates.sort();
    templates.dedup();
    if errors.is_empty() {
        Ok(templates)
    } else {
        Err(errors)
    }
}

fn substitute_super_pattern(
    pattern: &Pattern,
    substitutions: &BTreeMap<u32, GenericArgPattern>,
) -> Option<Pattern> {
    match pattern {
        Pattern::Bound(index) => match substitutions.get(index)? {
            GenericArgPattern::Type(pattern) => Some(pattern.clone()),
            GenericArgPattern::Lifetime(_) | GenericArgPattern::Const(_) => None,
        },
        Pattern::Ground(ty) => Some(Pattern::Ground(ty.clone())),
        Pattern::Nominal(name, arguments) => Some(Pattern::Nominal(
            name.clone(),
            arguments
                .iter()
                .map(|argument| match argument {
                    NominalPatternArg::Type(argument) => {
                        substitute_super_pattern(argument, substitutions)
                            .map(NominalPatternArg::Type)
                    }
                    NominalPatternArg::Const(ConstPattern::Value(value)) => Some(
                        NominalPatternArg::Const(ConstPattern::Value(value.clone())),
                    ),
                    NominalPatternArg::Const(ConstPattern::Bound(index, kind)) => substitutions
                        .get(index)
                        .and_then(|argument| match argument {
                            GenericArgPattern::Const(argument) => {
                                Some(NominalPatternArg::Const(argument.clone()))
                            }
                            GenericArgPattern::Type(_) | GenericArgPattern::Lifetime(_) => None,
                        })
                        .filter(|argument| {
                            matches!(argument, NominalPatternArg::Const(ConstPattern::Bound(_, actual)) if actual == kind)
                                || matches!(argument, NominalPatternArg::Const(ConstPattern::Value(value)) if const_value_kind(value) == *kind)
                        }),
                })
                .collect::<Option<Vec<_>>>()?,
        )),
        Pattern::Shared(referent) => Some(Pattern::Shared(Box::new(substitute_super_pattern(
            referent,
            substitutions,
        )?))),
        Pattern::Unique(referent) => Some(Pattern::Unique(Box::new(substitute_super_pattern(
            referent,
            substitutions,
        )?))),
        Pattern::Tuple(elements) => Some(Pattern::Tuple(
            elements
                .iter()
                .map(|element| substitute_super_pattern(element, substitutions))
                .collect::<Option<Vec<_>>>()?,
        )),
        Pattern::Projection {
            subject,
            trait_key,
            arguments,
            item,
            item_arguments,
        } => Some(Pattern::Projection {
            subject: Box::new(substitute_super_pattern(subject, substitutions)?),
            trait_key: trait_key.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_super_generic_pattern(argument, substitutions))
                .collect::<Option<Vec<_>>>()?,
            item: item.clone(),
            item_arguments: item_arguments
                .iter()
                .map(|argument| substitute_super_generic_pattern(argument, substitutions))
                .collect::<Option<Vec<_>>>()?,
        }),
    }
}

fn substitute_super_generic_pattern(
    pattern: &GenericArgPattern,
    substitutions: &BTreeMap<u32, GenericArgPattern>,
) -> Option<GenericArgPattern> {
    match pattern {
        GenericArgPattern::Type(pattern) => {
            substitute_super_pattern(pattern, substitutions).map(GenericArgPattern::Type)
        }
        GenericArgPattern::Lifetime(LifetimePattern::Bound(index)) => substitutions
            .get(index)
            .filter(|argument| matches!(argument, GenericArgPattern::Lifetime(_)))
            .cloned(),
        GenericArgPattern::Lifetime(pattern) => Some(GenericArgPattern::Lifetime(pattern.clone())),
        GenericArgPattern::Const(ConstPattern::Bound(index, kind)) => substitutions
            .get(index)
            .filter(|argument| matches!(argument, GenericArgPattern::Const(ConstPattern::Bound(_, actual)) if actual == kind))
            .cloned(),
        GenericArgPattern::Const(pattern) => Some(GenericArgPattern::Const(pattern.clone())),
    }
}

fn instantiate_supertrait_goal_pattern(
    template: &SupertraitTemplate,
    schema: &TraitSchema,
    head: &GoalPattern,
) -> Option<GoalPattern> {
    if schema.parameters.len() != head.arguments.len() {
        return None;
    }
    let mut substitutions = head
        .arguments
        .iter()
        .cloned()
        .enumerate()
        .map(|(index, argument)| (index as u32, argument))
        .collect::<BTreeMap<_, _>>();
    substitutions.insert(
        schema.parameters.len() as u32,
        GenericArgPattern::Type(head.subject.clone()),
    );
    let arguments = template
        .arguments
        .iter()
        .map(|argument| match argument {
            SuperArgumentPattern::Type(pattern) => substitute_super_pattern(pattern, &substitutions)
                .map(GenericArgPattern::Type),
            SuperArgumentPattern::Const(ConstPattern::Value(value)) => Some(
                GenericArgPattern::Const(ConstPattern::Value(value.clone())),
            ),
            SuperArgumentPattern::Const(ConstPattern::Bound(index, kind)) => substitutions
                .get(index)
                .filter(|argument| {
                    matches!(argument, GenericArgPattern::Const(ConstPattern::Bound(_, actual)) if actual == kind)
                        || matches!(argument, GenericArgPattern::Const(ConstPattern::Value(value)) if const_value_kind(value) == *kind)
                })
                .cloned(),
            SuperArgumentPattern::LifetimeBound(index) => substitutions
                .get(index)
                .filter(|argument| matches!(argument, GenericArgPattern::Lifetime(_)))
                .cloned(),
            SuperArgumentPattern::LifetimeStatic => {
                Some(GenericArgPattern::Lifetime(LifetimePattern::Static))
            }
        })
        .collect::<Option<Vec<_>>>()?;
    let bindings = template
        .bindings
        .iter()
        .map(|binding| {
            Some(AssociatedPattern {
                item: binding.item.clone(),
                arguments: binding
                    .arguments
                    .iter()
                    .map(|argument| substitute_super_generic_pattern(argument, &substitutions))
                    .collect::<Option<Vec<_>>>()?,
                value: substitute_super_pattern(&binding.value, &substitutions)?,
            })
        })
        .collect::<Option<Vec<_>>>()?;
    Some(GoalPattern {
        polarity: GoalPolarity::Positive,
        trait_key: template.trait_key.clone(),
        subject: head.subject.clone(),
        arguments,
        bindings,
    })
}

fn supertrait_cycle_errors(
    traits: &BTreeMap<String, TraitSchema>,
    program: &Program,
) -> Vec<Diagnostic> {
    fn reaches(
        current: &TraitKey,
        target: &TraitKey,
        by_key: &BTreeMap<TraitKey, &TraitSchema>,
        visiting: &mut BTreeSet<TraitKey>,
    ) -> bool {
        if current == target {
            return true;
        }
        if !visiting.insert(current.clone()) {
            return false;
        }
        let found = by_key.get(current).is_some_and(|schema| {
            schema
                .supertraits
                .iter()
                .any(|parent| reaches(&parent.trait_key, target, by_key, visiting))
        });
        visiting.remove(current);
        found
    }

    let by_key = traits
        .values()
        .map(|schema| (schema.key.clone(), schema))
        .collect::<BTreeMap<_, _>>();
    let mut errors = Vec::new();
    for declaration in &program.traits {
        let schema = &traits[&declaration.name];
        if schema.supertraits.iter().any(|parent| {
            reaches(
                &parent.trait_key,
                &schema.key,
                &by_key,
                &mut BTreeSet::new(),
            )
        }) {
            errors.push(error(
                declaration.span,
                format!(
                    "supertrait declaration cycle contains `{}`",
                    declaration.name
                ),
            ));
        }
    }
    errors
}

fn collect_type_pattern_binders(pattern: &Pattern, found: &mut BTreeSet<u32>) {
    match pattern {
        Pattern::Bound(index) => {
            found.insert(*index);
        }
        Pattern::Nominal(_, arguments) => {
            for argument in arguments {
                if let NominalPatternArg::Type(argument) = argument {
                    collect_type_pattern_binders(argument, found);
                }
            }
        }
        Pattern::Tuple(arguments) => {
            for argument in arguments {
                collect_type_pattern_binders(argument, found);
            }
        }
        Pattern::Shared(referent) | Pattern::Unique(referent) => {
            collect_type_pattern_binders(referent, found);
        }
        Pattern::Projection {
            subject,
            arguments,
            item_arguments,
            ..
        } => {
            collect_type_pattern_binders(subject, found);
            for argument in arguments.iter().chain(item_arguments) {
                collect_generic_pattern_binders(argument, found);
            }
        }
        Pattern::Ground(_) => {}
    }
}

fn rigid_goal_fact(
    goal: &GoalPattern,
    substitutions: &BTreeMap<u32, GenericArg>,
) -> Option<TraitFact> {
    let subject = instantiate_super_pattern(&goal.subject, substitutions)?;
    let arguments = goal
        .arguments
        .iter()
        .map(|argument| match argument {
            GenericArgPattern::Type(pattern) => {
                instantiate_super_pattern(pattern, substitutions).map(GenericArg::Type)
            }
            GenericArgPattern::Lifetime(LifetimePattern::Static) => {
                Some(GenericArg::Lifetime(LifetimeArg::Static))
            }
            GenericArgPattern::Lifetime(LifetimePattern::Bound(index)) => substitutions
                .get(index)
                .filter(|argument| matches!(argument, GenericArg::Lifetime(_)))
                .cloned(),
            GenericArgPattern::Lifetime(LifetimePattern::HigherRanked(index)) => {
                Some(GenericArg::Lifetime(LifetimeArg::Placeholder {
                    universe: 1,
                    index: *index,
                }))
            }
            GenericArgPattern::Const(ConstPattern::Value(value)) => {
                Some(GenericArg::Const(value.clone()))
            }
            GenericArgPattern::Const(ConstPattern::Bound(index, kind)) => substitutions
                .get(index)
                .filter(|argument| generic_arg_has_const_kind(argument, *kind))
                .cloned(),
        })
        .collect::<Option<Vec<_>>>()?;
    let bindings = goal
        .bindings
        .iter()
        .map(|binding| {
            Some(AssociatedValue {
                item: binding.item.clone(),
                arguments: binding
                    .arguments
                    .iter()
                    .map(|argument| instantiate_super_generic_pattern(argument, substitutions))
                    .collect::<Option<Vec<_>>>()?,
                value: instantiate_super_pattern(&binding.value, substitutions)?,
            })
        })
        .collect::<Option<Vec<_>>>()?;
    Some(TraitFact {
        polarity: goal.polarity,
        trait_key: goal.trait_key.clone(),
        subject,
        arguments,
        bindings,
    })
}

fn validate_supertrait_impls(database: &TraitDb, spans: &[crate::span::Span]) -> Vec<Diagnostic> {
    let mut errors = Vec::new();
    for (impl_index, implementation) in database.impls.iter().enumerate() {
        if database
            .schema_by_key(&implementation.head.trait_key)
            .is_some_and(|schema| schema.role == Some(IntrinsicRole::Drop))
        {
            // Dedicated drop checking reports the source-facing structural
            // diagnostic. The solver still retains and enforces this frozen
            // super-goal whenever Drop evidence is requested.
            continue;
        }
        if implementation.super_goals.is_empty() {
            continue;
        }
        let mut implied = implementation
            .goals
            .iter()
            .filter(|goal| goal.polarity == GoalPolarity::Positive)
            .cloned()
            .collect::<BTreeSet<_>>();
        loop {
            let before = implied.len();
            let current = implied.iter().cloned().collect::<Vec<_>>();
            for goal in current {
                let Some(schema) = database.schema_by_key(&goal.trait_key) else {
                    continue;
                };
                for template in &schema.supertraits {
                    if let Some(parent) =
                        instantiate_supertrait_goal_pattern(template, schema, &goal)
                    {
                        implied.insert(parent);
                    }
                }
            }
            if implied.len() == before {
                break;
            }
        }
        let mut type_binders = BTreeSet::new();
        collect_type_pattern_binders(&implementation.head.subject, &mut type_binders);
        for argument in &implementation.head.arguments {
            if let GenericArgPattern::Type(pattern) = argument {
                collect_type_pattern_binders(pattern, &mut type_binders);
            }
        }
        let mut substitutions = type_binders
            .into_iter()
            .map(|index| {
                (
                    index,
                    GenericArg::Type(ProvisionalType::Predefined(format!(
                        "$supertrait_rigid_{impl_index}_{index}"
                    ))),
                )
            })
            .collect::<BTreeMap<_, _>>();
        for argument in &implementation.head.arguments {
            if let GenericArgPattern::Const(ConstPattern::Bound(index, kind)) = argument {
                substitutions
                    .entry(*index)
                    .or_insert(GenericArg::RigidConst(*index, *kind));
            }
        }
        let lexical_facts = implementation
            .goals
            .iter()
            .filter_map(|goal| rigid_goal_fact(goal, &substitutions))
            .collect::<Vec<_>>();
        let param_env = database.param_env(lexical_facts);
        for obligation in &implementation.super_goals {
            if implied.contains(obligation) {
                continue;
            }
            let Some(goal) = rigid_goal_fact(obligation, &substitutions) else {
                errors.push(error(
                    spans[impl_index],
                    "implementation supertrait obligation could not be instantiated universally",
                ));
                continue;
            };
            let mut budget = SolverBudget::default();
            let report = database.solve_with_key_detailed_with_budget(
                &mut budget,
                &param_env,
                GoalPolarity::Positive,
                &goal.trait_key,
                &goal.subject,
                &goal.arguments,
                &goal.bindings,
            );
            if report.result != SolveResult::Proven {
                let detail = report
                    .failure
                    .map(|failure| format!("; {}", failure.diagnostic_text()))
                    .unwrap_or_default();
                errors.push(error(
                    spans[impl_index],
                    format!(
                        "implementation does not prove required supertrait `{}`{detail}",
                        database.trait_display_name(&goal.trait_key)
                    ),
                ));
            }
        }
    }
    errors
}

fn relation_name(relation: &TraitRefSyntax) -> Result<String, Diagnostic> {
    if relation.path.len() != 1 {
        return Err(error(
            relation.span,
            "trait references cannot have qualification",
        ));
    }
    Ok(relation.path[0].name.clone())
}

fn lower_generic_arguments(
    arguments: &[GoalArgument],
    expected: &[GenericParameterKind],
    binders: &BTreeMap<&str, Binder>,
    nominals: &BTreeMap<String, NominalSchema>,
    traits: &BTreeMap<String, TraitSchema>,
) -> Result<Vec<GenericArgPattern>, Diagnostic> {
    arguments.iter().zip(expected).map(|(argument, expected)| match (argument, expected) {
        (GoalArgument::Type(syntax), GenericParameterKind::Type) => {
            pattern(syntax, binders, nominals, traits, false).map(GenericArgPattern::Type)
        }
        (GoalArgument::Lifetime { name, span }, GenericParameterKind::Lifetime) => {
            if name == "'static" {
                Ok(GenericArgPattern::Lifetime(LifetimePattern::Static))
            } else {
                let Some(binder) = binders.get(name.as_str()) else {
                    return Err(error(*span, format!("unbound lifetime argument `{name}`")));
                };
                if binder.kind != GenericParameterKind::Lifetime {
                    return Err(error(*span, format!("`{name}` is not a lifetime binder")));
                }
                Ok(GenericArgPattern::Lifetime(if binder.higher_ranked {
                    LifetimePattern::HigherRanked(binder.index)
                } else {
                    LifetimePattern::Bound(binder.index)
                }))
            }
        }
        (GoalArgument::Quantity(quantity), GenericParameterKind::Const(ConstKind::Quantity)) => {
            let lower = u32::try_from(quantity.lower).map_err(|_| error(quantity.span,
                "quantity lower bound exceeds the u32 const domain"))?;
            let upper = quantity.upper.map(u32::try_from).transpose().map_err(|_| error(
                quantity.span, "quantity upper bound exceeds the u32 const domain"))?;
            if upper.is_some_and(|upper| lower > upper) {
                return Err(error(quantity.span, "quantity lower bound exceeds its upper bound"));
            }
            Ok(GenericArgPattern::Const(ConstPattern::Value(ConstValue::Quantity { lower, upper })))
        }
        (GoalArgument::U32 { value, span }, GenericParameterKind::Const(ConstKind::U32)) => {
            let value = u32::try_from(*value).map_err(|_| error(*span,
                "u32 const argument exceeds the u32 domain"))?;
            Ok(GenericArgPattern::Const(ConstPattern::Value(ConstValue::U32(value))))
        }
        (GoalArgument::Type(syntax), GenericParameterKind::Const(kind)) => {
            let Some(name) = syntax.simple_name() else {
                return Err(error(syntax.span, "const arguments must be a structural literal or const parameter"));
            };
            let Some(binder) = binders.get(name) else {
                return Err(error(
                    syntax.span,
                    format!("trait argument has type syntax `{name}` where const kind `{kind:?}` was expected"),
                ));
            };
            if binder.kind != GenericParameterKind::Const(*kind) {
                return Err(error(syntax.span, format!("const parameter `{name}` has the wrong kind")));
            }
            Ok(GenericArgPattern::Const(const_binder_pattern(*binder, *kind)))
        }
        (_, GenericParameterKind::Lifetime) => Err(error(
            argument_span(argument),
            "trait generic argument has the wrong kind; expected a lifetime",
        )),
        (_, GenericParameterKind::Const(kind)) => Err(error(
            argument_span(argument),
            format!("trait generic argument has the wrong kind; expected const `{kind:?}`"),
        )),
        _ => Err(error(
            argument_span(argument),
            "trait generic argument has the wrong kind; expected a type",
        )),
    }).collect()
}

/// One associated argument in complete source order: either an entry of the
/// ordinary type/lifetime list or a structural const argument recorded beside
/// it with its original position.
enum AssociatedArgumentRef<'a> {
    Syntax(&'a AssociatedArgumentSyntax),
    Const(&'a ConstArgumentValueSyntax),
}

impl AssociatedArgumentRef<'_> {
    fn span(&self) -> crate::span::Span {
        match self {
            Self::Syntax(argument) => argument.span(),
            Self::Const(value) => value.span(),
        }
    }
}

/// Restores the complete source ordering of an associated argument list from
/// the type/lifetime entries and the positioned structural const entries.
fn merged_associated_arguments<'a>(
    arguments: &'a [AssociatedArgumentSyntax],
    const_arguments: &'a [ConstAssociatedArgumentSyntax],
) -> Vec<AssociatedArgumentRef<'a>> {
    let total = arguments.len() + const_arguments.len();
    let mut ordinary = arguments.iter();
    let mut merged = Vec::with_capacity(total);
    for position in 0..total {
        if let Some(constant) = const_arguments
            .iter()
            .find(|argument| argument.position == position)
        {
            merged.push(AssociatedArgumentRef::Const(&constant.value));
        } else if let Some(argument) = ordinary.next() {
            merged.push(AssociatedArgumentRef::Syntax(argument));
        }
    }
    merged
}

fn quantity_const_value(quantity: &QuantitySyntax) -> Result<ConstValue, Diagnostic> {
    let lower = u32::try_from(quantity.lower).map_err(|_| {
        error(
            quantity.span,
            "quantity lower bound exceeds the u32 const domain",
        )
    })?;
    let upper = quantity.upper.map(u32::try_from).transpose().map_err(|_| {
        error(
            quantity.span,
            "quantity upper bound exceeds the u32 const domain",
        )
    })?;
    if upper.is_some_and(|upper| lower > upper) {
        return Err(error(
            quantity.span,
            "quantity lower bound exceeds its upper bound",
        ));
    }
    Ok(ConstValue::Quantity { lower, upper })
}

fn lower_associated_arguments(
    arguments: &[AssociatedArgumentSyntax],
    const_arguments: &[ConstAssociatedArgumentSyntax],
    expected: &[GenericParameterKind],
    binders: &BTreeMap<&str, Binder>,
    nominals: &BTreeMap<String, NominalSchema>,
    traits: &BTreeMap<String, TraitSchema>,
) -> Result<Vec<GenericArgPattern>, Diagnostic> {
    let merged = merged_associated_arguments(arguments, const_arguments);
    if merged.len() != expected.len() {
        return Err(error(
            merged
                .first()
                .map_or(crate::span::Span::new(0, 0), AssociatedArgumentRef::span),
            format!(
                "wrong associated argument arity; expected {}",
                expected.len()
            ),
        ));
    }
    merged
        .iter()
        .zip(expected)
        .map(|(argument, expected)| match (argument, expected) {
            (
                AssociatedArgumentRef::Syntax(AssociatedArgumentSyntax::Type(syntax)),
                GenericParameterKind::Type,
            ) => pattern(syntax, binders, nominals, traits, false).map(GenericArgPattern::Type),
            (
                AssociatedArgumentRef::Syntax(AssociatedArgumentSyntax::Lifetime { name, span }),
                GenericParameterKind::Lifetime,
            ) => {
                if name == "'static" {
                    Ok(GenericArgPattern::Lifetime(LifetimePattern::Static))
                } else {
                    let binder = binders.get(name.as_str()).ok_or_else(|| {
                        error(*span, format!("unbound lifetime argument `{name}`"))
                    })?;
                    if binder.kind != GenericParameterKind::Lifetime {
                        return Err(error(*span, format!("`{name}` is not a lifetime binder")));
                    }
                    Ok(GenericArgPattern::Lifetime(if binder.higher_ranked {
                        LifetimePattern::HigherRanked(binder.index)
                    } else {
                        LifetimePattern::Bound(binder.index)
                    }))
                }
            }
            // A structural const argument against a declared const binder kind.
            (
                AssociatedArgumentRef::Const(ConstArgumentValueSyntax::Quantity(quantity)),
                GenericParameterKind::Const(ConstKind::Quantity),
            ) => Ok(GenericArgPattern::Const(ConstPattern::Value(
                quantity_const_value(quantity)?,
            ))),
            (
                AssociatedArgumentRef::Const(ConstArgumentValueSyntax::U32 { value, span }),
                GenericParameterKind::Const(ConstKind::U32),
            ) => {
                let value = u32::try_from(*value)
                    .map_err(|_| error(*span, "u32 const argument exceeds the u32 domain"))?;
                Ok(GenericArgPattern::Const(ConstPattern::Value(
                    ConstValue::U32(value),
                )))
            }
            // A named binder in a const position: reclassified by the declared
            // parameter kind, preserved symbolically as its bound index.
            (
                AssociatedArgumentRef::Syntax(AssociatedArgumentSyntax::Type(syntax)),
                GenericParameterKind::Const(kind),
            ) => {
                let Some(name) = syntax.simple_name() else {
                    return Err(error(
                        syntax.span,
                        "const arguments must be a structural literal or const parameter",
                    ));
                };
                let Some(binder) = binders.get(name) else {
                    return Err(error(
                        syntax.span,
                        format!("unbound const argument `{name}`; expected const kind `{kind:?}`"),
                    ));
                };
                if binder.kind != GenericParameterKind::Const(*kind) {
                    return Err(error(
                        syntax.span,
                        format!("const parameter `{name}` has the wrong kind"),
                    ));
                }
                Ok(GenericArgPattern::Const(const_binder_pattern(
                    *binder, *kind,
                )))
            }
            (argument, expected) => Err(error(
                argument.span(),
                format!("associated argument has the wrong kind; expected {expected:?}"),
            )),
        })
        .collect()
}

fn argument_span(argument: &GoalArgument) -> crate::span::Span {
    match argument {
        GoalArgument::Type(syntax) => syntax.span,
        GoalArgument::Lifetime { span, .. } => *span,
        GoalArgument::Quantity(quantity) => quantity.span,
        GoalArgument::U32 { span, .. } => *span,
    }
}

fn const_pattern_value(
    syntax: &crate::ast::ConstArgumentValueSyntax,
    expected: ConstKind,
) -> Result<ConstPattern, Diagnostic> {
    match (syntax, expected) {
        (crate::ast::ConstArgumentValueSyntax::U32 { value, span }, ConstKind::U32) => {
            let value = u32::try_from(*value)
                .map_err(|_| error(*span, "u32 const argument exceeds the u32 domain"))?;
            Ok(ConstPattern::Value(ConstValue::U32(value)))
        }
        (crate::ast::ConstArgumentValueSyntax::Quantity(quantity), ConstKind::Quantity) => {
            Ok(ConstPattern::Value(quantity_const_value(quantity)?))
        }
        (crate::ast::ConstArgumentValueSyntax::U32 { span, .. }, kind) => Err(error(
            *span,
            format!("const argument has the wrong kind; expected {kind:?}"),
        )),
        (crate::ast::ConstArgumentValueSyntax::Quantity(quantity), kind) => Err(error(
            quantity.span,
            format!("const argument has the wrong kind; expected {kind:?}"),
        )),
        (crate::ast::ConstArgumentValueSyntax::Expression(expression), expected) => {
            let value = crate::ast::evaluate_const_expression(expression, |_| None)
                .map_err(|message| error(expression.span, message))?;
            match (value, expected) {
                (crate::ast::EvaluatedConst::U32(value), ConstKind::U32) => {
                    Ok(ConstPattern::Value(ConstValue::U32(value)))
                }
                (crate::ast::EvaluatedConst::Quantity { lower, upper }, ConstKind::Quantity) => {
                    Ok(ConstPattern::Value(ConstValue::Quantity { lower, upper }))
                }
                (_, kind) => Err(error(
                    expression.span,
                    format!("const expression has the wrong kind; expected {kind:?}"),
                )),
            }
        }
    }
}

fn pattern(
    syntax: &TypeSyntax,
    binders: &BTreeMap<&str, Binder>,
    nominals: &BTreeMap<String, NominalSchema>,
    traits: &BTreeMap<String, TraitSchema>,
    head: bool,
) -> Result<Pattern, Diagnostic> {
    pattern_with_const_arguments(syntax, binders, nominals, traits, head, &BTreeMap::new())
}

fn pattern_with_const_arguments(
    syntax: &TypeSyntax,
    binders: &BTreeMap<&str, Binder>,
    nominals: &BTreeMap<String, NominalSchema>,
    traits: &BTreeMap<String, TraitSchema>,
    head: bool,
    type_const_arguments: &BTreeMap<(usize, usize), Vec<crate::ast::ConstAssociatedArgumentSyntax>>,
) -> Result<Pattern, Diagnostic> {
    match &syntax.kind {
        TypeSyntaxKind::Path(path) if path.len() == 1 => {
            if let Some(binder) = binders.get(path[0].name.as_str()) {
                if binder.kind != GenericParameterKind::Type {
                    return Err(error(
                        syntax.span,
                        format!(
                            "const parameter `{}` cannot be used in a type position",
                            path[0].name
                        ),
                    ));
                }
                if binder.higher_ranked {
                    Ok(Pattern::Ground(ProvisionalType::Param(GenericParamKey {
                        owner: DeclarationKey::Function("$higher_ranked_universe_1".into()),
                        ordinal: binder.index,
                    })))
                } else {
                    Ok(Pattern::Bound(binder.index))
                }
            } else if is_predefined(&path[0].name) {
                Ok(Pattern::Ground(ProvisionalType::Predefined(
                    if path[0].name == "char" {
                        "Char".to_owned()
                    } else {
                        path[0].name.clone()
                    },
                )))
            } else if let Some(schema) = nominals.get(&path[0].name) {
                if !schema.parameters.is_empty() {
                    return Err(error(
                        syntax.span,
                        format!("unknown or unapplied nominal type `{}`", path[0].name),
                    ));
                }
                Ok(Pattern::Nominal(schema.identity.clone(), vec![]))
            } else {
                Err(error(
                    syntax.span,
                    format!("unknown or unapplied nominal type `{}`", path[0].name),
                ))
            }
        }
        TypeSyntaxKind::Application {
            constructor,
            arguments,
            lifetime_arguments,
            ..
        } => {
            let Some(name) = constructor.simple_name() else {
                return Err(error(
                    syntax.span,
                    "impl heads require a simple nominal constructor",
                ));
            };
            let Some(schema) = nominals.get(name) else {
                return Err(error(
                    syntax.span,
                    format!("unknown nominal constructor or wrong arity for `{name}`"),
                ));
            };
            let const_arguments = type_const_arguments
                .get(&(syntax.span.start, syntax.span.end))
                .map_or(&[][..], Vec::as_slice);
            if schema.parameters.len()
                != arguments.len() + lifetime_arguments.len() + const_arguments.len()
            {
                return Err(error(
                    syntax.span,
                    format!("unknown nominal constructor or wrong arity for `{name}`"),
                ));
            }
            let lifetime_positions = lifetime_arguments
                .iter()
                .map(|argument| argument.position)
                .collect::<BTreeSet<_>>();
            let const_by_position = const_arguments
                .iter()
                .map(|argument| (argument.position, &argument.value))
                .collect::<BTreeMap<_, _>>();
            let mut source_types = arguments.iter();
            let mut lowered = Vec::new();
            for (position, parameter) in schema.parameters.iter().enumerate() {
                match parameter {
                    GenericParameterKind::Lifetime => {
                        if !lifetime_positions.contains(&position) {
                            return Err(error(
                                syntax.span,
                                format!("nominal argument {position} must be a lifetime"),
                            ));
                        }
                    }
                    GenericParameterKind::Type => {
                        if lifetime_positions.contains(&position)
                            || const_by_position.contains_key(&position)
                        {
                            return Err(error(
                                syntax.span,
                                format!("nominal argument {position} must be a type"),
                            ));
                        }
                        let argument = source_types.next().ok_or_else(|| {
                            error(
                                syntax.span,
                                format!("missing nominal type argument {position}"),
                            )
                        })?;
                        lowered.push(NominalPatternArg::Type(pattern_with_const_arguments(
                            argument,
                            binders,
                            nominals,
                            traits,
                            false,
                            type_const_arguments,
                        )?));
                    }
                    GenericParameterKind::Const(kind) => {
                        if lifetime_positions.contains(&position) {
                            return Err(error(
                                syntax.span,
                                format!("nominal argument {position} must be a const"),
                            ));
                        }
                        let const_pattern = if let Some(value) = const_by_position.get(&position) {
                            const_pattern_value(value, *kind)?
                        } else {
                            let argument = source_types.next().ok_or_else(|| {
                                error(
                                    syntax.span,
                                    format!("missing nominal const argument {position}"),
                                )
                            })?;
                            let Some(name) = argument.simple_name() else {
                                return Err(error(
                                    argument.span,
                                    "const arguments must be a structural literal or const parameter",
                                ));
                            };
                            let binder = binders.get(name).ok_or_else(|| {
                                error(argument.span, format!("unbound const argument `{name}`"))
                            })?;
                            if binder.kind != GenericParameterKind::Const(*kind) {
                                return Err(error(
                                    argument.span,
                                    format!("const parameter `{name}` has the wrong kind"),
                                ));
                            }
                            const_binder_pattern(*binder, *kind)
                        };
                        lowered.push(NominalPatternArg::Const(const_pattern));
                    }
                }
            }
            if source_types.next().is_some() {
                return Err(error(syntax.span, "too many nominal type arguments"));
            }
            Ok(Pattern::Nominal(schema.identity.clone(), lowered))
        }
        TypeSyntaxKind::SharedReference { referent, .. } => {
            Ok(Pattern::Shared(Box::new(pattern_with_const_arguments(
                referent,
                binders,
                nominals,
                traits,
                false,
                type_const_arguments,
            )?)))
        }
        TypeSyntaxKind::UniqueReference { referent, .. } => {
            Ok(Pattern::Unique(Box::new(pattern_with_const_arguments(
                referent,
                binders,
                nominals,
                traits,
                false,
                type_const_arguments,
            )?)))
        }
        TypeSyntaxKind::Tuple(elements) if elements.is_empty() => {
            Ok(Pattern::Ground(ProvisionalType::Predefined("Unit".into())))
        }
        TypeSyntaxKind::Tuple(elements) => Ok(Pattern::Tuple(
            elements
                .iter()
                .map(|element| {
                    pattern_with_const_arguments(
                        element,
                        binders,
                        nominals,
                        traits,
                        false,
                        type_const_arguments,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?,
        )),
        TypeSyntaxKind::Projection {
            subject,
            trait_ref,
            item,
            arguments: item_arguments,
            const_arguments: item_const_arguments,
        } if !head => {
            if !trait_ref.bindings.is_empty() {
                return Err(error(
                    trait_ref.span,
                    "projection trait references cannot contain equality bindings",
                ));
            }
            let trait_name = relation_name(trait_ref)?;
            let schema = traits.get(&trait_name).ok_or_else(|| {
                error(
                    trait_ref.span,
                    format!("unknown trait `{trait_name}` in projection"),
                )
            })?;
            if trait_ref.arguments.len() != schema.parameters.len() {
                return Err(error(
                    trait_ref.span,
                    "wrong trait argument arity in projection",
                ));
            }
            let associated_item = schema.associated_items.get(&item.name).ok_or_else(|| {
                error(
                    item.span,
                    format!("unknown associated type `{}`", item.name),
                )
            })?;
            if associated_item.kind != AssociatedItemKind::Type {
                return Err(error(
                    item.span,
                    format!(
                        "associated effect row `{}` is valid only inside an effect-row projection",
                        item.name
                    ),
                ));
            }
            let item_kinds = &associated_item.parameters;
            Ok(Pattern::Projection {
                subject: Box::new(pattern_with_const_arguments(
                    subject,
                    binders,
                    nominals,
                    traits,
                    false,
                    type_const_arguments,
                )?),
                trait_key: schema.key.clone(),
                arguments: lower_generic_arguments(
                    &trait_ref.arguments,
                    &schema.parameters,
                    binders,
                    nominals,
                    traits,
                )?,
                item: item.name.clone(),
                item_arguments: lower_associated_arguments(
                    item_arguments,
                    item_const_arguments,
                    item_kinds,
                    binders,
                    nominals,
                    traits,
                )?,
            })
        }
        _ => Err(error(syntax.span, "unsupported marker impl head")),
    }
}

pub(crate) fn is_predefined(name: &str) -> bool {
    matches!(
        name,
        "Unit"
            | "u8"
            | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "i8"
            | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "usize"
            | "isize"
            | "f32"
            | "f64"
            | "char"
            | "Char"
            | "Text"
            | "Bytes"
    )
}

fn collect_binders(pattern: &Pattern, found: &mut BTreeSet<u32>) {
    match pattern {
        Pattern::Bound(index) => {
            found.insert(*index);
        }
        Pattern::Nominal(_, arguments) => arguments.iter().for_each(|argument| match argument {
            NominalPatternArg::Type(argument) => collect_binders(argument, found),
            NominalPatternArg::Const(ConstPattern::Bound(index, _)) => {
                found.insert(*index);
            }
            NominalPatternArg::Const(ConstPattern::Value(_)) => {}
        }),
        Pattern::Shared(referent) | Pattern::Unique(referent) => collect_binders(referent, found),
        Pattern::Tuple(elements) => elements
            .iter()
            .for_each(|element| collect_binders(element, found)),
        Pattern::Projection {
            subject,
            arguments,
            item_arguments,
            ..
        } => {
            collect_binders(subject, found);
            arguments
                .iter()
                .for_each(|argument| collect_generic_pattern_binders(argument, found));
            item_arguments
                .iter()
                .for_each(|argument| collect_generic_pattern_binders(argument, found));
        }
        Pattern::Ground(_) => {}
    }
}

fn collect_generic_pattern_binders(pattern: &GenericArgPattern, found: &mut BTreeSet<u32>) {
    match pattern {
        GenericArgPattern::Type(pattern) => collect_binders(pattern, found),
        GenericArgPattern::Lifetime(LifetimePattern::Bound(index))
        | GenericArgPattern::Const(ConstPattern::Bound(index, _)) => {
            found.insert(*index);
        }
        GenericArgPattern::Lifetime(LifetimePattern::Static | LifetimePattern::HigherRanked(_))
        | GenericArgPattern::Const(ConstPattern::Value(_)) => {}
    }
}

fn collect_goal_binders(goal: &GoalPattern, found: &mut BTreeSet<u32>) {
    collect_binders(&goal.subject, found);
    for argument in &goal.arguments {
        match argument {
            GenericArgPattern::Type(argument) => collect_binders(argument, found),
            GenericArgPattern::Lifetime(LifetimePattern::Bound(index)) => {
                found.insert(*index);
            }
            GenericArgPattern::Lifetime(LifetimePattern::Static) => {}
            GenericArgPattern::Lifetime(LifetimePattern::HigherRanked(_)) => {}
            GenericArgPattern::Const(ConstPattern::Bound(index, _)) => {
                found.insert(*index);
            }
            GenericArgPattern::Const(ConstPattern::Value(_)) => {}
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum OverlapTerm {
    TypeVariable(u64),
    ConstVariable(u64, ConstKind),
    Const(ConstValue),
    Ground(ProvisionalType),
    Nominal(NominalKey, Vec<OverlapTerm>),
    Shared(Box<OverlapTerm>),
    Unique(Box<OverlapTerm>),
    Tuple(Vec<OverlapTerm>),
}

fn overlap_term(pattern: &Pattern, namespace: u64, wildcard: &mut u32) -> OverlapTerm {
    match pattern {
        Pattern::Bound(index) => OverlapTerm::TypeVariable(namespace | u64::from(*index)),
        Pattern::Ground(ty) => OverlapTerm::Ground(ty.clone()),
        Pattern::Nominal(name, arguments) => OverlapTerm::Nominal(
            name.clone(),
            arguments
                .iter()
                .map(|argument| match argument {
                    NominalPatternArg::Type(argument) => {
                        overlap_term(argument, namespace, wildcard)
                    }
                    NominalPatternArg::Const(ConstPattern::Bound(index, kind)) => {
                        OverlapTerm::ConstVariable(namespace | u64::from(*index), *kind)
                    }
                    NominalPatternArg::Const(ConstPattern::Value(value)) => {
                        OverlapTerm::Const(value.clone())
                    }
                })
                .collect(),
        ),
        Pattern::Shared(referent) => {
            OverlapTerm::Shared(Box::new(overlap_term(referent, namespace, wildcard)))
        }
        Pattern::Unique(referent) => {
            OverlapTerm::Unique(Box::new(overlap_term(referent, namespace, wildcard)))
        }
        Pattern::Tuple(elements) => OverlapTerm::Tuple(
            elements
                .iter()
                .map(|element| overlap_term(element, namespace, wildcard))
                .collect(),
        ),
        Pattern::Projection { .. } => {
            let index = namespace | (1 << 31) | u64::from(*wildcard);
            *wildcard = wildcard.saturating_add(1);
            OverlapTerm::TypeVariable(index)
        }
    }
}

fn overlap_generic_arg(
    pattern: &GenericArgPattern,
    namespace: u64,
    wildcard: &mut u32,
) -> OverlapTerm {
    match pattern {
        GenericArgPattern::Type(pattern) => overlap_term(pattern, namespace, wildcard),
        GenericArgPattern::Lifetime(LifetimePattern::Bound(index)) => {
            OverlapTerm::TypeVariable(namespace | (1_u64 << 62) | u64::from(*index))
        }
        GenericArgPattern::Lifetime(LifetimePattern::Static) => OverlapTerm::TypeVariable(u64::MAX),
        GenericArgPattern::Lifetime(LifetimePattern::HigherRanked(index)) => {
            OverlapTerm::TypeVariable(namespace | (1_u64 << 61) | u64::from(*index))
        }
        GenericArgPattern::Const(ConstPattern::Bound(index, kind)) => {
            OverlapTerm::ConstVariable(namespace | u64::from(*index), *kind)
        }
        GenericArgPattern::Const(ConstPattern::Value(value)) => OverlapTerm::Const(value.clone()),
    }
}

fn resolve_overlap(term: OverlapTerm, substitutions: &BTreeMap<u64, OverlapTerm>) -> OverlapTerm {
    match term {
        OverlapTerm::TypeVariable(index) => substitutions
            .get(&index)
            .cloned()
            .map_or(OverlapTerm::TypeVariable(index), |term| {
                resolve_overlap(term, substitutions)
            }),
        OverlapTerm::ConstVariable(index, kind) => substitutions
            .get(&index)
            .cloned()
            .map_or(OverlapTerm::ConstVariable(index, kind), |term| {
                resolve_overlap(term, substitutions)
            }),
        term => term,
    }
}

fn overlap_occurs(
    variable: u64,
    term: OverlapTerm,
    substitutions: &BTreeMap<u64, OverlapTerm>,
) -> bool {
    match resolve_overlap(term, substitutions) {
        OverlapTerm::TypeVariable(index) | OverlapTerm::ConstVariable(index, _) => {
            index == variable
        }
        OverlapTerm::Nominal(_, arguments) => arguments
            .into_iter()
            .any(|argument| overlap_occurs(variable, argument, substitutions)),
        OverlapTerm::Shared(referent) | OverlapTerm::Unique(referent) => {
            overlap_occurs(variable, *referent, substitutions)
        }
        OverlapTerm::Tuple(elements) => elements
            .into_iter()
            .any(|element| overlap_occurs(variable, element, substitutions)),
        OverlapTerm::Ground(_) | OverlapTerm::Const(_) => false,
    }
}

fn unify_overlap(
    left: OverlapTerm,
    right: OverlapTerm,
    substitutions: &mut BTreeMap<u64, OverlapTerm>,
) -> bool {
    let left = resolve_overlap(left, substitutions);
    let right = resolve_overlap(right, substitutions);
    match (left, right) {
        (OverlapTerm::TypeVariable(left), OverlapTerm::TypeVariable(right)) if left == right => {
            true
        }
        (OverlapTerm::TypeVariable(index), term) | (term, OverlapTerm::TypeVariable(index)) => {
            if matches!(
                term,
                OverlapTerm::ConstVariable(_, _) | OverlapTerm::Const(_)
            ) {
                return false;
            }
            if overlap_occurs(index, term.clone(), substitutions) {
                return false;
            }
            substitutions.insert(index, term);
            true
        }
        (
            OverlapTerm::ConstVariable(left, left_kind),
            OverlapTerm::ConstVariable(right, right_kind),
        ) if left == right => left_kind == right_kind,
        (OverlapTerm::ConstVariable(index, kind), term)
        | (term, OverlapTerm::ConstVariable(index, kind)) => {
            let compatible = match &term {
                OverlapTerm::Const(value) => const_value_kind(value) == kind,
                OverlapTerm::ConstVariable(_, other) => *other == kind,
                _ => false,
            };
            if compatible {
                substitutions.insert(index, term);
            }
            compatible
        }
        (OverlapTerm::Const(left), OverlapTerm::Const(right)) => left == right,
        (OverlapTerm::Ground(left), OverlapTerm::Ground(right)) => left == right,
        (OverlapTerm::Nominal(left, la), OverlapTerm::Nominal(right, ra)) => {
            left == right
                && la.len() == ra.len()
                && la
                    .into_iter()
                    .zip(ra)
                    .all(|(left, right)| unify_overlap(left, right, substitutions))
        }
        (OverlapTerm::Shared(left), OverlapTerm::Shared(right))
        | (OverlapTerm::Unique(left), OverlapTerm::Unique(right)) => {
            unify_overlap(*left, *right, substitutions)
        }
        (OverlapTerm::Tuple(left), OverlapTerm::Tuple(right)) => {
            left.len() == right.len()
                && left
                    .into_iter()
                    .zip(right)
                    .all(|(left, right)| unify_overlap(left, right, substitutions))
        }
        _ => false,
    }
}

fn goal_overlaps(left: &GoalPattern, right: &GoalPattern) -> bool {
    if left.trait_key != right.trait_key || left.arguments.len() != right.arguments.len() {
        return false;
    }
    let mut substitutions = BTreeMap::new();
    let mut left_wildcard = 0;
    let mut right_wildcard = 0;
    unify_overlap(
        overlap_term(&left.subject, 0, &mut left_wildcard),
        overlap_term(&right.subject, 1 << 32, &mut right_wildcard),
        &mut substitutions,
    ) && left
        .arguments
        .iter()
        .zip(&right.arguments)
        .all(|(left, right)| {
            unify_overlap(
                overlap_generic_arg(left, 0, &mut left_wildcard),
                overlap_generic_arg(right, 1 << 32, &mut right_wildcard),
                &mut substitutions,
            )
        })
}

fn use_heads_overlap(left: &GoalPattern, right: &GoalPattern) -> bool {
    let mut substitutions = BTreeMap::new();
    let mut left_wildcard = 0;
    let mut right_wildcard = 0;
    left.trait_key == right.trait_key
        && unify_overlap(
            overlap_term(&left.subject, 0, &mut left_wildcard),
            overlap_term(&right.subject, 1 << 32, &mut right_wildcard),
            &mut substitutions,
        )
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct ConstructorMeasure {
    constant: usize,
    coefficients: BTreeMap<u32, usize>,
}

impl ConstructorMeasure {
    fn add(&mut self, other: Self) {
        self.constant = self.constant.saturating_add(other.constant);
        for (binder, coefficient) in other.coefficients {
            let value = self.coefficients.entry(binder).or_default();
            *value = value.saturating_add(coefficient);
        }
    }

    fn strictly_dominates(&self, other: &Self) -> bool {
        let no_growth = other.coefficients.iter().all(|(binder, coefficient)| {
            self.coefficients.get(binder).copied().unwrap_or_default() >= *coefficient
        });
        let strict_coefficient = self.coefficients.iter().any(|(binder, coefficient)| {
            *coefficient > other.coefficients.get(binder).copied().unwrap_or_default()
        });
        no_growth
            && self.constant >= other.constant
            && (self.constant > other.constant || strict_coefficient)
    }
}

fn provisional_measure(ty: &ProvisionalType) -> usize {
    let mut measure = 0;
    provisional_signature_type_any(ty, &mut |_| {
        measure += 1;
        false
    });
    measure
}

fn pattern_measure(pattern: &Pattern) -> Option<ConstructorMeasure> {
    match pattern {
        Pattern::Bound(binder) => Some(ConstructorMeasure {
            constant: 0,
            coefficients: BTreeMap::from([(*binder, 1)]),
        }),
        Pattern::Ground(ty) => Some(ConstructorMeasure {
            constant: provisional_measure(ty),
            coefficients: BTreeMap::new(),
        }),
        Pattern::Nominal(_, arguments) => {
            let mut measure = ConstructorMeasure {
                constant: 1,
                coefficients: BTreeMap::new(),
            };
            for argument in arguments {
                if let NominalPatternArg::Type(argument) = argument {
                    measure.add(pattern_measure(argument)?);
                }
            }
            Some(measure)
        }
        Pattern::Tuple(arguments) => {
            let mut measure = ConstructorMeasure {
                constant: 1,
                coefficients: BTreeMap::new(),
            };
            for argument in arguments {
                measure.add(pattern_measure(argument)?);
            }
            Some(measure)
        }
        Pattern::Shared(referent) | Pattern::Unique(referent) => {
            let mut measure = ConstructorMeasure {
                constant: 1,
                coefficients: BTreeMap::new(),
            };
            measure.add(pattern_measure(referent)?);
            Some(measure)
        }
        Pattern::Projection { .. } => None,
    }
}

fn goal_measure(goal: &GoalPattern) -> Option<ConstructorMeasure> {
    let mut measure = pattern_measure(&goal.subject)?;
    for argument in &goal.arguments {
        if let GenericArgPattern::Type(argument) = argument {
            measure.add(pattern_measure(argument)?);
        }
    }
    Some(measure)
}

fn path_exists(start: usize, target: usize, adjacency: &[BTreeSet<usize>]) -> bool {
    let mut pending = vec![start];
    let mut visited = BTreeSet::new();
    while let Some(node) = pending.pop() {
        if node == target {
            return true;
        }
        if visited.insert(node) {
            pending.extend(adjacency[node].iter().rev().copied());
        }
    }
    false
}

fn recursive_impl_errors(
    impls: &[(ImplEntry, crate::span::Span)],
    trait_names: &BTreeMap<TraitKey, String>,
    dedicated_use_key: Option<&TraitKey>,
) -> Vec<Diagnostic> {
    let mut adjacency = vec![BTreeSet::new(); impls.len()];
    let mut edges = Vec::new();
    for (source, (implementation, _)) in impls.iter().enumerate() {
        if dedicated_use_key == Some(&implementation.head.trait_key) {
            // The principal-interval engine owns conditional Use reachability,
            // cycle, and overflow diagnostics. Its graph admits finite chains
            // whose individual nominal edges need not strictly decrease, so
            // the ordinary trait constructor-measure rule is inapplicable.
            continue;
        }
        for goal in implementation
            .super_goals
            .iter()
            .chain(&implementation.goals)
        {
            for (target, (candidate, _)) in impls.iter().enumerate() {
                if goal.polarity == candidate.head.polarity && goal_overlaps(goal, &candidate.head)
                {
                    adjacency[source].insert(target);
                    edges.push((source, target, goal.clone()));
                }
            }
        }
    }
    let mut errors = Vec::new();
    for (source, target, goal) in edges {
        if source != target && !path_exists(target, source, &adjacency) {
            continue;
        }
        let implementation = &impls[source].0;
        let decreasing = goal_measure(&implementation.head)
            .zip(goal_measure(&goal))
            .is_some_and(|(head, obligation)| head.strictly_dominates(&obligation));
        if !decreasing {
            errors.push(error(
                impls[source].1,
                format!(
                    "recursive implementation where-goal for `{}` does not strictly decrease the type-constructor measure",
                    trait_names.get(&goal.trait_key).map_or("<unknown trait>", String::as_str)
                ),
            ));
        }
    }
    errors
}

fn pattern_constructor(pattern: &Pattern) -> Option<HeadConstructor> {
    match pattern {
        Pattern::Bound(_) => Some(HeadConstructor::Any),
        Pattern::Ground(ProvisionalType::Predefined(name)) => {
            Some(HeadConstructor::Predefined(name.clone()))
        }
        Pattern::Nominal(name, _) => Some(HeadConstructor::Nominal(name.clone())),
        Pattern::Tuple(elements) => Some(HeadConstructor::Tuple(elements.len())),
        Pattern::Shared(_) => Some(HeadConstructor::Shared),
        Pattern::Unique(_) => Some(HeadConstructor::Unique),
        _ => None,
    }
}

fn ground_constructor(ty: &ProvisionalType) -> Option<HeadConstructor> {
    match ty {
        ProvisionalType::Predefined(name) => Some(HeadConstructor::Predefined(name.clone())),
        ProvisionalType::Nominal(instance) => {
            Some(HeadConstructor::Nominal(instance.declaration.clone()))
        }
        ProvisionalType::Tuple(elements) => Some(HeadConstructor::Tuple(elements.len())),
        ProvisionalType::Shared(_) => Some(HeadConstructor::Shared),
        ProvisionalType::Unique(_) => Some(HeadConstructor::Unique),
        _ => None,
    }
}

fn matches_pattern(
    pattern: &Pattern,
    ty: &ProvisionalType,
    substitutions: &mut BTreeMap<u32, GenericArg>,
) -> bool {
    match pattern {
        Pattern::Bound(index) => {
            if let Some(existing) = substitutions.get(index) {
                existing == &GenericArg::Type(ty.clone())
            } else {
                substitutions.insert(*index, GenericArg::Type(ty.clone()));
                true
            }
        }
        Pattern::Ground(expected) => expected == ty,
        Pattern::Nominal(name, arguments) => match ty {
            ProvisionalType::Nominal(NominalInstanceKey {
                declaration,
                arguments: actual,
            }) => {
                declaration == name
                    && arguments.len() == actual.len()
                    && arguments
                        .iter()
                        .zip(actual)
                        .all(|(pattern, ty)| match pattern {
                            NominalPatternArg::Type(pattern) => {
                                matches_pattern(pattern, ty, substitutions)
                            }
                            NominalPatternArg::Const(pattern) => decode_const_argument(ty)
                                .is_some_and(|actual| {
                                    matches_generic_arg(
                                        &GenericArgPattern::Const(pattern.clone()),
                                        &actual,
                                        substitutions,
                                    )
                                }),
                        })
            }
            _ => false,
        },
        Pattern::Shared(referent) => match ty {
            ProvisionalType::Shared(actual) => matches_pattern(referent, actual, substitutions),
            _ => false,
        },
        Pattern::Unique(referent) => match ty {
            ProvisionalType::Unique(actual) => matches_pattern(referent, actual, substitutions),
            _ => false,
        },
        Pattern::Tuple(elements) => match ty {
            ProvisionalType::Tuple(actual) => {
                elements.len() == actual.len()
                    && elements
                        .iter()
                        .zip(actual)
                        .all(|(pattern, ty)| matches_pattern(pattern, ty, substitutions))
            }
            _ => false,
        },
        Pattern::Projection { .. } => false,
    }
}

fn matches_generic_arg(
    pattern: &GenericArgPattern,
    actual: &GenericArg,
    substitutions: &mut BTreeMap<u32, GenericArg>,
) -> bool {
    match (pattern, actual) {
        (GenericArgPattern::Type(pattern), GenericArg::Type(actual)) => {
            matches_pattern(pattern, actual, substitutions)
        }
        (GenericArgPattern::Lifetime(LifetimePattern::Static), GenericArg::Lifetime(actual)) => {
            actual == &LifetimeArg::Static
        }
        (
            GenericArgPattern::Lifetime(LifetimePattern::Bound(index)),
            GenericArg::Lifetime(actual),
        ) => {
            let actual = GenericArg::Lifetime(actual.clone());
            if let Some(existing) = substitutions.get(index) {
                existing == &actual
            } else {
                substitutions.insert(*index, actual);
                true
            }
        }
        (GenericArgPattern::Const(ConstPattern::Value(expected)), GenericArg::Const(actual)) => {
            expected == actual
        }
        (GenericArgPattern::Const(ConstPattern::Bound(index, kind)), GenericArg::Const(actual))
            if const_value_kind(actual) == *kind =>
        {
            let actual = GenericArg::Const(actual.clone());
            if let Some(existing) = substitutions.get(index) {
                existing == &actual
            } else {
                substitutions.insert(*index, actual);
                true
            }
        }
        (
            GenericArgPattern::Const(ConstPattern::Bound(index, kind)),
            GenericArg::RigidConst(actual_index, actual_kind),
        ) if actual_kind == kind => {
            let actual = GenericArg::RigidConst(*actual_index, *actual_kind);
            if let Some(existing) = substitutions.get(index) {
                existing == &actual
            } else {
                substitutions.insert(*index, actual);
                true
            }
        }
        _ => false,
    }
}

fn matches_goal(
    pattern: &GoalPattern,
    goal: &GroundGoal,
    substitutions: &mut BTreeMap<u32, GenericArg>,
) -> bool {
    pattern.polarity == goal.polarity
        && pattern.trait_key == goal.trait_key
        && pattern.arguments.len() == goal.arguments.len()
        && matches_pattern(&pattern.subject, &goal.subject, substitutions)
        && pattern
            .arguments
            .iter()
            .zip(&goal.arguments)
            .all(|(pattern, actual)| matches_generic_arg(pattern, actual, substitutions))
}

fn table_answer(result: SolveResult) -> TableAnswer {
    TableAnswer {
        result,
        associated_values: BTreeMap::new(),
        cycle_trace: None,
    }
}

fn same_fact_head(fact: &TraitFact, goal: &GroundGoal) -> bool {
    fact.trait_key == goal.trait_key
        && fact.subject == goal.subject
        && fact.arguments == goal.arguments
}

fn fact_head(fact: &TraitFact) -> FactHead {
    FactHead {
        trait_key: fact.trait_key.clone(),
        subject: fact.subject.clone(),
        arguments: fact.arguments.clone(),
    }
}

fn instantiate_super_pattern(
    pattern: &Pattern,
    substitutions: &BTreeMap<u32, GenericArg>,
) -> Option<ProvisionalType> {
    match pattern {
        Pattern::Bound(index) => match substitutions.get(index)? {
            GenericArg::Type(ty) => Some(ty.clone()),
            GenericArg::Lifetime(_) | GenericArg::Const(_) | GenericArg::RigidConst(_, _) => None,
        },
        Pattern::Ground(ty) => Some(ty.clone()),
        Pattern::Nominal(declaration, arguments) => {
            Some(ProvisionalType::Nominal(NominalInstanceKey {
                declaration: declaration.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| match argument {
                        NominalPatternArg::Type(argument) => {
                            instantiate_super_pattern(argument, substitutions)
                        }
                        NominalPatternArg::Const(argument) => {
                            instantiate_const_pattern(argument, substitutions)
                        }
                    })
                    .collect::<Option<Vec<_>>>()?,
            }))
        }
        Pattern::Shared(referent) => Some(ProvisionalType::Shared(Box::new(
            instantiate_super_pattern(referent, substitutions)?,
        ))),
        Pattern::Unique(referent) => Some(ProvisionalType::Unique(Box::new(
            instantiate_super_pattern(referent, substitutions)?,
        ))),
        Pattern::Tuple(elements) => Some(ProvisionalType::Tuple(
            elements
                .iter()
                .map(|element| instantiate_super_pattern(element, substitutions))
                .collect::<Option<Vec<_>>>()?,
        )),
        Pattern::Projection { .. } => None,
    }
}

fn instantiate_super_generic_pattern(
    pattern: &GenericArgPattern,
    substitutions: &BTreeMap<u32, GenericArg>,
) -> Option<GenericArg> {
    match pattern {
        GenericArgPattern::Type(pattern) => {
            instantiate_super_pattern(pattern, substitutions).map(GenericArg::Type)
        }
        GenericArgPattern::Lifetime(LifetimePattern::Static) => {
            Some(GenericArg::Lifetime(LifetimeArg::Static))
        }
        GenericArgPattern::Lifetime(LifetimePattern::Bound(index)) => substitutions
            .get(index)
            .filter(|argument| matches!(argument, GenericArg::Lifetime(_)))
            .cloned(),
        GenericArgPattern::Lifetime(LifetimePattern::HigherRanked(index)) => {
            Some(GenericArg::Lifetime(LifetimeArg::Placeholder {
                universe: 1,
                index: *index,
            }))
        }
        GenericArgPattern::Const(ConstPattern::Value(value)) => {
            Some(GenericArg::Const(value.clone()))
        }
        GenericArgPattern::Const(ConstPattern::Bound(index, kind)) => {
            instantiate_bound_const(*index, *kind, substitutions, 1)
        }
    }
}

fn instantiate_supertrait_fact(
    template: &SupertraitTemplate,
    schema: &TraitSchema,
    fact: &TraitFact,
) -> Option<TraitFact> {
    if schema.parameters.len() != fact.arguments.len() {
        return None;
    }
    let mut substitutions = fact
        .arguments
        .iter()
        .cloned()
        .enumerate()
        .map(|(index, argument)| (index as u32, argument))
        .collect::<BTreeMap<_, _>>();
    substitutions.insert(
        schema.parameters.len() as u32,
        GenericArg::Type(fact.subject.clone()),
    );
    let arguments = template
        .arguments
        .iter()
        .map(|argument| match argument {
            SuperArgumentPattern::Type(pattern) => {
                instantiate_super_pattern(pattern, &substitutions).map(GenericArg::Type)
            }
            SuperArgumentPattern::Const(ConstPattern::Value(value)) => {
                Some(GenericArg::Const(value.clone()))
            }
            SuperArgumentPattern::Const(ConstPattern::Bound(index, kind)) => substitutions
                .get(index)
                .filter(|argument| generic_arg_has_const_kind(argument, *kind))
                .cloned(),
            SuperArgumentPattern::LifetimeBound(index) => substitutions
                .get(index)
                .filter(|argument| matches!(argument, GenericArg::Lifetime(_)))
                .cloned(),
            SuperArgumentPattern::LifetimeStatic => Some(GenericArg::Lifetime(LifetimeArg::Static)),
        })
        .collect::<Option<Vec<_>>>()?;
    let bindings = template
        .bindings
        .iter()
        .map(|binding| {
            Some(AssociatedValue {
                item: binding.item.clone(),
                arguments: binding
                    .arguments
                    .iter()
                    .map(|argument| instantiate_super_generic_pattern(argument, &substitutions))
                    .collect::<Option<Vec<_>>>()?,
                value: instantiate_super_pattern(&binding.value, &substitutions)?,
            })
        })
        .collect::<Option<Vec<_>>>()?;
    Some(TraitFact {
        polarity: GoalPolarity::Positive,
        trait_key: template.trait_key.clone(),
        subject: fact.subject.clone(),
        arguments,
        bindings,
    })
}

fn lexical_answer(goal: &GroundGoal, param_env: &ParamEnv) -> TableAnswer {
    let head = FactHead {
        trait_key: goal.trait_key.clone(),
        subject: goal.subject.clone(),
        arguments: goal.arguments.clone(),
    };
    let contradictory = param_env.conflicts.contains(&head)
        || goal
            .bindings
            .iter()
            .map(AssociatedValue::key)
            .chain(goal.projections.iter().cloned())
            .any(|key| param_env.equality_conflicts.contains(&(head.clone(), key)));
    if contradictory {
        return table_answer(SolveResult::Ambiguous);
    }
    let mut found = false;
    let mut associated_values = BTreeMap::new();
    for fact in param_env
        .facts
        .iter()
        .filter(|fact| fact.polarity == goal.polarity && same_fact_head(fact, goal))
    {
        let fact_values = fact
            .bindings
            .iter()
            .map(|binding| (binding.key(), binding.value.clone()))
            .collect::<BTreeMap<_, _>>();
        if goal
            .bindings
            .iter()
            .any(|binding| fact_values.get(&binding.key()) != Some(&binding.value))
            || goal
                .projections
                .iter()
                .any(|key| !fact_values.contains_key(key))
        {
            continue;
        }
        found = true;
        for (name, value) in fact_values {
            if associated_values
                .insert(name.clone(), value.clone())
                .is_some_and(|existing| existing != value)
            {
                return table_answer(SolveResult::Ambiguous);
            }
        }
    }
    if found {
        TableAnswer {
            result: SolveResult::Proven,
            associated_values,
            cycle_trace: None,
        }
    } else {
        table_answer(SolveResult::NoEvidence)
    }
}

fn error(span: crate::span::Span, message: impl Into<String>) -> Diagnostic {
    Diagnostic::error("marker trait error", message, span).with_code("G1TR001")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn distributed_runtime_manifest_freezes_scalar_text_bytes_and_array_table() {
        let runtime = TrustedRuntimeManifest::distributed_generation_1();
        assert_eq!(
            runtime.machine_types,
            vec![ManifestMachineType {
                id: 0x21,
                display_name: "Array".into(),
                parameters: vec![GenericParameterKind::Type],
                role: MachineTypeRole::Array,
            }]
        );
        let expected = crate::builtins::distributed_runtime_primitive_leaves();
        assert_eq!(runtime.primitive_leaves.len(), expected.len());
        for (actual, (id, name, primitive)) in runtime.primitive_leaves.iter().zip(expected) {
            assert_eq!(actual.id, id);
            assert_eq!(actual.display_name, name);
            assert_eq!(actual.primitive, primitive);
        }
    }

    fn associated(item: &str, value: ProvisionalType) -> AssociatedValue {
        AssociatedValue {
            item: item.into(),
            arguments: vec![],
            value,
        }
    }

    fn gat_associated(
        item: &str,
        arguments: Vec<ProvisionalType>,
        value: ProvisionalType,
    ) -> AssociatedValue {
        AssociatedValue {
            item: item.into(),
            arguments: arguments.into_iter().map(GenericArg::Type).collect(),
            value,
        }
    }

    fn database(source: &str) -> TraitDb {
        let source = format!("{source} main() -> {{ () }}");
        let tokens = crate::lexer::lex(&source).unwrap();
        let program = crate::parser::parse(tokens).unwrap();
        TraitDb::build(&program).unwrap()
    }

    fn nominal(name: &str, arguments: Vec<ProvisionalType>) -> ProvisionalType {
        ProvisionalType::Nominal(NominalInstanceKey {
            declaration: NominalKey(name.into()),
            arguments,
        })
    }

    #[test]
    fn solves_ground_and_recursive_constructor_implementations() {
        let db = database(
            "trait Marker {} struct Box<T> { value: T } \
             impl Marker for i64 {} \
             impl<T> Marker for Box<T> where T: Marker {}",
        );
        let integer = ProvisionalType::Predefined("i64".into());
        assert_eq!(db.solve("Marker", &integer), SolveResult::Proven);
        assert_eq!(
            db.solve("Marker", &nominal("Box", vec![integer])),
            SolveResult::Proven
        );
        assert_eq!(
            db.solve("Marker", &ProvisionalType::Predefined("Text".into())),
            SolveResult::NoEvidence
        );
    }

    #[test]
    fn nondecreasing_recursive_impls_are_rejected_before_solving() {
        let source = "trait Marker {} struct Box<T> { value: T } \
                      impl<T> Marker for Box<T> where Box<T>: Marker {} main()->{()}";
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        let errors = TraitDb::build(&program).unwrap_err();
        assert!(errors.iter().any(|diagnostic| {
            diagnostic.code.as_deref() == Some("G1TR001")
                && diagnostic.message.contains("does not strictly decrease")
        }));
    }

    #[test]
    fn finite_same_trait_dependency_into_a_base_impl_is_not_recursive() {
        let db = database(
            "trait Marker {} struct A {} struct B {} \
             impl Marker for A where B: Marker {} impl Marker for B {}",
        );
        assert_eq!(
            db.solve("Marker", &nominal("A", vec![])),
            SolveResult::Proven
        );
    }

    #[test]
    fn mutual_candidate_cycle_requires_every_edge_to_strictly_decrease() {
        let source = "trait Marker {} struct A<T>{value:T} struct B<T>{value:T} \
                      struct Box<T>{value:T} \
                      impl<T> Marker for A<T> where B<T>:Marker {} \
                      impl<T> Marker for B<Box<T>> where A<T>:Marker {} main()->{()}";
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        let errors = TraitDb::build(&program).unwrap_err();
        assert!(
            errors
                .iter()
                .any(|diagnostic| diagnostic.message.contains("does not strictly decrease"))
        );
    }

    #[test]
    fn exact_gat_cycle_reports_a_deterministic_shortest_repeating_trace() {
        let source = "trait Family { type Member<T>; } \
                      impl Family for Text { type Member<T> = <Text as Family>::Member<T>; } \
                      inspect(value:<Text as Family>::Member<i64>)->{()} main()->{()}";
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        let db = TraitDb::build(&program).unwrap();
        let projection = &program
            .functions
            .iter()
            .find(|function| function.name == "inspect")
            .unwrap()
            .params[0]
            .ty;
        let first = db.normalize_type_detailed(projection).unwrap_err();
        let second = db.normalize_type_detailed(projection).unwrap_err();
        assert_eq!(first, second);
        assert_eq!(first.result, SolveResult::Ambiguous);
        assert!(matches!(
            first.failure,
            Some(SolveFailure::Cycle { ref trace })
                if trace.len() == 2 && trace.first() == trace.last()
        ));
    }

    #[test]
    fn negative_evidence_is_explicit_and_can_have_recursive_obligations() {
        let db = database(
            "trait Blocked {} trait Allowed {} struct Box<T> { value: T } \
             impl !Blocked for Text {} \
             impl<T> !Allowed for Box<T> where T: !Blocked {}",
        );
        let text = ProvisionalType::Predefined("Text".into());
        let integer = ProvisionalType::Predefined("i64".into());
        assert_eq!(
            db.solve_with_polarity(GoalPolarity::Negative, "Blocked", &text, &[]),
            SolveResult::Proven
        );
        assert_eq!(
            db.solve_with_polarity(GoalPolarity::Positive, "Blocked", &text, &[]),
            SolveResult::Refuted
        );
        assert_eq!(
            db.solve_with_polarity(GoalPolarity::Negative, "Blocked", &integer, &[]),
            SolveResult::NoEvidence
        );
        assert_eq!(
            db.solve_with_polarity(
                GoalPolarity::Negative,
                "Allowed",
                &nominal("Box", vec![text]),
                &[],
            ),
            SolveResult::Proven
        );
        assert_eq!(
            db.solve_with_polarity(
                GoalPolarity::Negative,
                "Allowed",
                &nominal("Box", vec![integer]),
                &[],
            ),
            SolveResult::NoEvidence
        );
    }

    #[test]
    fn overlapping_negative_facts_deduplicate_but_positive_negative_overlap_rejects() {
        let db = database(
            "trait Marker {} struct Box<T> { value: T } \
             impl<T> !Marker for Box<T> {} impl !Marker for Box<Text> {}",
        );
        assert_eq!(
            db.solve_with_polarity(
                GoalPolarity::Negative,
                "Marker",
                &nominal("Box", vec![ProvisionalType::Predefined("Text".into())]),
                &[],
            ),
            SolveResult::Proven
        );

        let source = "trait Marker {} struct Box<T> { value: T } \
                      impl<T> Marker for Box<T> {} impl !Marker for Box<Text> {} \
                      main() -> { () }";
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        let errors = TraitDb::build(&program).unwrap_err();
        assert!(
            errors
                .iter()
                .any(|error| error.message.contains("overlapping"))
        );
    }

    #[test]
    fn negative_database_is_source_order_independent() {
        let first =
            database("trait Left {} trait Right {} impl !Left for i64 {} impl !Right for Text {}");
        let second =
            database("impl !Right for Text {} trait Right {} impl !Left for i64 {} trait Left {}");
        assert_eq!(first.canonical_text(), second.canonical_text());
        assert_eq!(first.fingerprint(), second.fingerprint());
    }

    #[test]
    fn associated_answers_substitute_binders_and_enforce_equalities() {
        let db = database(
            "trait Value { type Item; } struct Box<T> { value: T } \
             struct Wrap<T> { value: T } \
             impl<T> Value for Box<T> { type Item = Wrap<T>; }",
        );
        let text = ProvisionalType::Predefined("Text".into());
        let subject = nominal("Box", vec![text.clone()]);
        let expected = nominal("Wrap", vec![text]);
        assert_eq!(
            db.solve_with_bindings(
                GoalPolarity::Positive,
                "Value",
                &subject,
                &[],
                &[("Item".into(), expected)],
            ),
            SolveResult::Proven
        );
        assert_eq!(
            db.solve_with_bindings(
                GoalPolarity::Positive,
                "Value",
                &subject,
                &[],
                &[("Item".into(), ProvisionalType::Predefined("i64".into()))],
            ),
            SolveResult::NoEvidence
        );
    }

    #[test]
    fn recursively_normalizes_ground_associated_projections() {
        let source = "trait Value { type Item; } struct Box<T> { value: T } \
                      struct Wrap<T> { value: T } \
                      impl<T> Value for Box<T> { type Item = Wrap<T>; } \
                      inspect(value: <Box<Text> as Value>::Item) -> { () } main() -> { () }";
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        let db = TraitDb::build(&program).unwrap();
        let projection = &program
            .functions
            .iter()
            .find(|function| function.name == "inspect")
            .unwrap()
            .params[0]
            .ty;
        assert_eq!(
            db.normalize_type(projection),
            Ok(nominal(
                "Wrap",
                vec![ProvisionalType::Predefined("Text".into())]
            ))
        );
    }

    #[test]
    fn generic_associated_types_key_item_arguments_and_substitute_item_binders() {
        let source = "trait Family<C> { type Member<T>; } \
                      struct Box<S> { value:S } struct Triple<A,B,C> { first:A second:B third:C } \
                      impl<S,C> Family<C> for Box<S> { type Member<U> = Triple<S,C,U>; } \
                      inspect(value:<Box<i64> as Family<Text>>::Member<u16>)->{()} main()->{()}";
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        let db = TraitDb::build(&program).unwrap();
        let projection = &program
            .functions
            .iter()
            .find(|function| function.name == "inspect")
            .unwrap()
            .params[0]
            .ty;
        let integer = ProvisionalType::Predefined("i64".into());
        let text = ProvisionalType::Predefined("Text".into());
        let short = ProvisionalType::Predefined("u16".into());
        let subject = nominal("Box", vec![integer.clone()]);
        let expected = nominal("Triple", vec![integer.clone(), text.clone(), short.clone()]);
        assert_eq!(db.normalize_type(projection), Ok(expected.clone()));
        assert_eq!(
            db.solve_with_param_env_values(
                &ParamEnv::default(),
                GoalPolarity::Positive,
                "Family",
                &subject,
                std::slice::from_ref(&text),
                &[gat_associated("Member", vec![short.clone()], expected)],
            ),
            SolveResult::Proven
        );
        assert_eq!(
            db.solve_with_param_env_values(
                &ParamEnv::default(),
                GoalPolarity::Positive,
                "Family",
                &subject,
                &[text],
                &[gat_associated(
                    "Member",
                    vec![ProvisionalType::Predefined("u8".into())],
                    nominal(
                        "Triple",
                        vec![integer, ProvisionalType::Predefined("Text".into()), short]
                    ),
                )],
            ),
            SolveResult::NoEvidence
        );
    }

    #[test]
    fn gat_definition_binders_are_alpha_renamed_and_shadow_impl_binders() {
        let source = "trait Family { type Member<T>; } \
                      struct Box<T> { value:T } \
                      impl<T> Family for Box<T> { type Member<T> = T; } \
                      inspect(value:<Box<Text> as Family>::Member<i64>)->{()} main()->{()}";
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        let db = TraitDb::build(&program).unwrap();
        let projection = &program
            .functions
            .iter()
            .find(|function| function.name == "inspect")
            .unwrap()
            .params[0]
            .ty;
        assert_eq!(
            db.normalize_type(projection),
            Ok(ProvisionalType::Predefined("i64".into()))
        );
    }

    #[test]
    fn lifetime_gat_arguments_normalize_and_key_equalities_exactly() {
        let source = "trait Family { type Member<'a,T>; } impl Family for Text { type Member<'x,U> = U; } inspect(value:<Text as Family>::Member<'static,i64>)->{()} main()->{()}";
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        let db = TraitDb::build(&program).unwrap();
        let projection = &program
            .functions
            .iter()
            .find(|function| function.name == "inspect")
            .unwrap()
            .params[0]
            .ty;
        assert_eq!(
            db.normalize_type(projection),
            Ok(ProvisionalType::Predefined("i64".into()))
        );

        let reordered = "main()->{()} inspect(value:<Text as Family>::Member<'static,i64>)->{()} impl Family for Text { type Member<'renamed,V> = V; } trait Family { type Member<'scope,T>; }";
        let reordered = crate::parser::parse(crate::lexer::lex(reordered).unwrap()).unwrap();
        let reordered = TraitDb::build(&reordered).unwrap();
        assert_eq!(db.canonical_text(), reordered.canonical_text());
        assert_eq!(db.fingerprint(), reordered.fingerprint());

        let fact = |lifetime, value: &str| TraitFact {
            polarity: GoalPolarity::Positive,
            trait_key: TraitKey::Local("Family".into()),
            subject: ProvisionalType::Predefined("Text".into()),
            arguments: vec![],
            bindings: vec![AssociatedValue {
                item: "Member".into(),
                arguments: vec![
                    GenericArg::Lifetime(lifetime),
                    GenericArg::Type(ProvisionalType::Predefined("i64".into())),
                ],
                value: ProvisionalType::Predefined(value.into()),
            }],
        };
        assert!(
            db.param_env([
                fact(LifetimeArg::Static, "Text"),
                fact(LifetimeArg::Rigid(1), "i64"),
            ])
            .is_consistent()
        );
        assert!(
            !db.param_env([
                fact(LifetimeArg::Static, "Text"),
                fact(LifetimeArg::Static, "i64"),
            ])
            .is_consistent()
        );
    }

    #[test]
    fn lexical_gat_equalities_conflict_per_item_application() {
        let db = database("trait Family { type Member<T>; }");
        let parameter = ProvisionalType::Param(crate::compiler_typeck::GenericParamKey {
            owner: crate::compiler_typeck::DeclarationKey::Function("owner".into()),
            ordinal: 0,
        });
        let i64_ty = ProvisionalType::Predefined("i64".into());
        let text_ty = ProvisionalType::Predefined("Text".into());
        let u16_ty = ProvisionalType::Predefined("u16".into());
        let environment = db.param_env([
            TraitFact {
                polarity: GoalPolarity::Positive,
                trait_key: TraitKey::Local("Family".into()),
                subject: parameter.clone(),
                arguments: vec![],
                bindings: vec![gat_associated(
                    "Member",
                    vec![i64_ty.clone()],
                    text_ty.clone(),
                )],
            },
            TraitFact {
                polarity: GoalPolarity::Positive,
                trait_key: TraitKey::Local("Family".into()),
                subject: parameter.clone(),
                arguments: vec![],
                bindings: vec![gat_associated(
                    "Member",
                    vec![u16_ty.clone()],
                    i64_ty.clone(),
                )],
            },
        ]);
        assert!(environment.is_consistent());
        assert_eq!(
            db.solve_with_param_env_values(
                &environment,
                GoalPolarity::Positive,
                "Family",
                &parameter,
                &[],
                &[gat_associated("Member", vec![i64_ty], text_ty)],
            ),
            SolveResult::Proven
        );
        assert_eq!(
            db.solve_with_param_env_values(
                &environment,
                GoalPolarity::Positive,
                "Family",
                &parameter,
                &[],
                &[gat_associated(
                    "Member",
                    vec![u16_ty],
                    ProvisionalType::Predefined("Text".into())
                )],
            ),
            SolveResult::NoEvidence
        );
    }

    #[test]
    fn lexical_param_environments_are_canonical_isolated_and_precede_globals() {
        let db = database(
            "trait Marker {} struct Box<T> { value: T } \
             impl Marker for Text {} impl<T> Marker for Box<T> where T: Marker {}",
        );
        let parameter = ProvisionalType::Param(crate::compiler_typeck::GenericParamKey {
            owner: crate::compiler_typeck::DeclarationKey::Function("outer".into()),
            ordinal: 0,
        });
        let fact = TraitFact {
            polarity: GoalPolarity::Positive,
            trait_key: TraitKey::Local("Marker".into()),
            subject: parameter.clone(),
            arguments: vec![],
            bindings: vec![],
        };
        let environment = db.param_env([fact.clone(), fact]);
        let reordered = db.param_env([TraitFact {
            polarity: GoalPolarity::Positive,
            trait_key: TraitKey::Local("Marker".into()),
            subject: parameter.clone(),
            arguments: vec![],
            bindings: vec![],
        }]);
        assert_eq!(environment.canonical_text(), reordered.canonical_text());
        assert_eq!(
            db.solve_with_param_env_values(
                &environment,
                GoalPolarity::Positive,
                "Marker",
                &nominal("Box", vec![parameter.clone()]),
                &[],
                &[],
            ),
            SolveResult::Proven
        );
        assert_eq!(
            db.solve_with_param_env_values(
                &ParamEnv::default(),
                GoalPolarity::Positive,
                "Marker",
                &nominal("Box", vec![parameter.clone()]),
                &[],
                &[],
            ),
            SolveResult::NoEvidence
        );
        let shadow = ProvisionalType::Param(crate::compiler_typeck::GenericParamKey {
            owner: crate::compiler_typeck::DeclarationKey::Function("inner".into()),
            ordinal: 0,
        });
        assert_eq!(
            db.solve_with_param_env_values(
                &environment,
                GoalPolarity::Positive,
                "Marker",
                &shadow,
                &[],
                &[],
            ),
            SolveResult::NoEvidence
        );
        let text = ProvisionalType::Predefined("Text".into());
        assert_eq!(
            db.solve_with_param_env_values(
                &db.param_env([TraitFact {
                    polarity: GoalPolarity::Positive,
                    trait_key: TraitKey::Local("Marker".into()),
                    subject: text.clone(),
                    arguments: vec![],
                    bindings: vec![],
                }]),
                GoalPolarity::Positive,
                "Marker",
                &text,
                &[],
                &[],
            ),
            SolveResult::Proven
        );
        assert_eq!(
            db.solve_with_param_env_values(
                &db.param_env([TraitFact {
                    polarity: GoalPolarity::Positive,
                    trait_key: TraitKey::Local("Value".into()),
                    subject: parameter.clone(),
                    arguments: vec![],
                    bindings: vec![],
                }]),
                GoalPolarity::Positive,
                "Value",
                &parameter,
                &[],
                &[associated(
                    "Item",
                    ProvisionalType::Predefined("i64".into()),
                )],
            ),
            SolveResult::NoEvidence
        );
    }

    #[test]
    fn lexical_use_quantity_facts_entail_contained_intervals_only() {
        let key = TraitKey::Local("Use".into());
        let subject = ProvisionalType::Param(crate::compiler_typeck::GenericParamKey {
            owner: crate::compiler_typeck::DeclarationKey::Function("owner".into()),
            ordinal: 0,
        });
        let environment = ParamEnv {
            facts: vec![TraitFact {
                polarity: GoalPolarity::Positive,
                trait_key: key.clone(),
                subject: subject.clone(),
                arguments: vec![GenericArg::Const(ConstValue::Quantity {
                    lower: 0,
                    upper: None,
                })],
                bindings: vec![],
            }],
            ..ParamEnv::default()
        };
        assert!(environment.use_quantity_contains(&key, &subject, 0, Some(0)));
        assert!(environment.use_quantity_contains(&key, &subject, 1, None));

        let affine = ParamEnv {
            facts: vec![TraitFact {
                polarity: GoalPolarity::Positive,
                trait_key: key.clone(),
                subject: subject.clone(),
                arguments: vec![GenericArg::Const(ConstValue::Quantity {
                    lower: 0,
                    upper: Some(1),
                })],
                bindings: vec![],
            }],
            ..ParamEnv::default()
        };
        assert!(!affine.use_quantity_contains(&key, &subject, 0, None));
        assert!(!affine.use_quantity_contains(&key, &subject, 2, Some(2)));
    }

    #[test]
    fn lexical_polarity_and_associated_equalities_are_exact_and_conflicts_ambiguous() {
        let db = database("trait Value { type Item; }");
        let parameter = ProvisionalType::Param(crate::compiler_typeck::GenericParamKey {
            owner: crate::compiler_typeck::DeclarationKey::Function("owner".into()),
            ordinal: 0,
        });
        let integer = ProvisionalType::Predefined("i64".into());
        let negative = db.param_env([TraitFact {
            polarity: GoalPolarity::Negative,
            trait_key: TraitKey::Local("Value".into()),
            subject: parameter.clone(),
            arguments: vec![],
            bindings: vec![],
        }]);
        assert_eq!(
            db.solve_with_param_env_values(
                &negative,
                GoalPolarity::Negative,
                "Value",
                &parameter,
                &[],
                &[],
            ),
            SolveResult::Proven
        );
        assert_eq!(
            db.solve_with_param_env_values(
                &ParamEnv::default(),
                GoalPolarity::Negative,
                "Value",
                &parameter,
                &[],
                &[],
            ),
            SolveResult::NoEvidence
        );
        let equality = db.param_env([TraitFact {
            polarity: GoalPolarity::Positive,
            trait_key: TraitKey::Local("Value".into()),
            subject: parameter.clone(),
            arguments: vec![],
            bindings: vec![associated("Item", integer.clone())],
        }]);
        assert_eq!(
            db.solve_with_param_env_values(
                &equality,
                GoalPolarity::Positive,
                "Value",
                &parameter,
                &[],
                &[],
            ),
            SolveResult::Proven
        );
        assert_eq!(
            db.solve_with_param_env_values(
                &equality,
                GoalPolarity::Positive,
                "Value",
                &parameter,
                &[],
                &[associated("Item", integer)],
            ),
            SolveResult::Proven
        );
        let conflict = db.param_env([
            TraitFact {
                polarity: GoalPolarity::Positive,
                trait_key: TraitKey::Local("Value".into()),
                subject: parameter.clone(),
                arguments: vec![],
                bindings: vec![associated(
                    "Item",
                    ProvisionalType::Predefined("i64".into()),
                )],
            },
            TraitFact {
                polarity: GoalPolarity::Positive,
                trait_key: TraitKey::Local("Value".into()),
                subject: parameter.clone(),
                arguments: vec![],
                bindings: vec![associated(
                    "Item",
                    ProvisionalType::Predefined("Text".into()),
                )],
            },
        ]);
        assert!(!conflict.is_consistent());
        assert_eq!(
            db.solve_with_param_env_values(
                &conflict,
                GoalPolarity::Positive,
                "Value",
                &parameter,
                &[],
                &[associated(
                    "Item",
                    ProvisionalType::Predefined("i64".into()),
                )],
            ),
            SolveResult::Ambiguous
        );
        let polarity_conflict = db.param_env([
            TraitFact {
                polarity: GoalPolarity::Positive,
                trait_key: TraitKey::Local("Value".into()),
                subject: parameter.clone(),
                arguments: vec![],
                bindings: vec![],
            },
            TraitFact {
                polarity: GoalPolarity::Negative,
                trait_key: TraitKey::Local("Value".into()),
                subject: parameter.clone(),
                arguments: vec![],
                bindings: vec![],
            },
        ]);
        assert_eq!(
            db.solve_with_param_env_values(
                &polarity_conflict,
                GoalPolarity::Positive,
                "Value",
                &parameter,
                &[],
                &[],
            ),
            SolveResult::Ambiguous
        );
    }

    #[test]
    fn lexical_fact_precedes_a_globally_overflowing_candidate_chain() {
        let db = database(
            "trait Marker {} struct Box<T> { value: T } \
             impl<T> Marker for Box<T> where T: Marker {}",
        );
        let mut subject = ProvisionalType::Predefined("Text".into());
        for _ in 0..=MAX_DEPTH {
            subject = nominal("Box", vec![subject]);
        }
        assert_eq!(db.solve("Marker", &subject), SolveResult::Overflow);
        let environment = db.param_env([TraitFact {
            polarity: GoalPolarity::Positive,
            trait_key: TraitKey::Local("Marker".into()),
            subject: subject.clone(),
            arguments: vec![],
            bindings: vec![],
        }]);
        assert_eq!(
            db.solve_with_param_env_values(
                &environment,
                GoalPolarity::Positive,
                "Marker",
                &subject,
                &[],
                &[],
            ),
            SolveResult::Proven
        );
    }

    #[test]
    fn deeply_recursive_evidence_reports_overflow() {
        let db = database(
            "trait Marker {} struct Box<T> { value: T } \
             impl Marker for i64 {} \
             impl<T> Marker for Box<T> where T: Marker {}",
        );
        let mut subject = ProvisionalType::Predefined("i64".into());
        for _ in 0..=MAX_DEPTH {
            subject = nominal("Box", vec![subject]);
        }
        let report = db.solve_with_param_env_values_detailed(
            &ParamEnv::default(),
            GoalPolarity::Positive,
            "Marker",
            &subject,
            &[],
            &[],
        );
        assert_eq!(report.result, SolveResult::Overflow);
        assert!(matches!(
            report.failure,
            Some(SolveFailure::Limit {
                limit: SolverLimit::NestedFrames,
                ref trace,
            }) if trace.len() == MAX_DEPTH + 1
        ));
    }

    #[test]
    fn declaration_step_budget_is_aggregate_and_resets_explicitly() {
        let db = database("trait Marker {} impl Marker for i64 {}");
        let integer = ProvisionalType::Predefined("i64".into());
        let mut budget = SolverBudget {
            steps: MAX_STEPS,
            projection_steps: 0,
        };
        let overflow = db.solve_with_param_env_values_detailed_with_budget(
            &mut budget,
            &ParamEnv::default(),
            GoalPolarity::Positive,
            "Marker",
            &integer,
            &[],
            &[],
        );
        assert!(matches!(
            overflow.failure,
            Some(SolveFailure::Limit {
                limit: SolverLimit::Steps,
                ..
            })
        ));
        budget.begin_declaration();
        assert_eq!(
            db.solve_with_param_env_values_detailed_with_budget(
                &mut budget,
                &ParamEnv::default(),
                GoalPolarity::Positive,
                "Marker",
                &integer,
                &[],
                &[],
            )
            .result,
            SolveResult::Proven
        );
    }

    #[test]
    fn canonical_table_budget_is_local_to_each_query() {
        let db = database("trait Marker {} impl Marker for i64 {}");
        let mut tables = BTreeMap::new();
        for index in 0..MAX_TABLES {
            tables.insert(
                TableKey {
                    goal: GroundGoal {
                        polarity: GoalPolarity::Positive,
                        trait_key: TraitKey::Local(format!("Synthetic{index}")),
                        subject: ProvisionalType::Predefined("i64".into()),
                        arguments: vec![],
                        bindings: vec![],
                        projections: vec![],
                    },
                    param_env: ParamEnv::default(),
                },
                TableState::Complete(table_answer(SolveResult::NoEvidence)),
            );
        }
        let mut diagnostics = SolverDiagnostics::default();
        let mut steps = 0;
        let mut projection_steps = 0;
        let answer = db.solve_inner(
            GroundGoal {
                polarity: GoalPolarity::Positive,
                trait_key: TraitKey::Local("Marker".into()),
                subject: ProvisionalType::Predefined("i64".into()),
                arguments: vec![],
                bindings: vec![],
                projections: vec![],
            },
            &ParamEnv::default(),
            &mut tables,
            0,
            &mut steps,
            &mut projection_steps,
            &mut diagnostics,
        );
        assert_eq!(answer.result, SolveResult::Overflow);
        assert!(matches!(
            diagnostics.failure_for(answer.result),
            Some(SolveFailure::Limit {
                limit: SolverLimit::Tables,
                ..
            })
        ));

        // A completed query cannot consume the table allowance of an
        // independent query issued later in the same compilation.
        let report = db.solve_with_param_env_values_detailed(
            &ParamEnv::default(),
            GoalPolarity::Positive,
            "Marker",
            &ProvisionalType::Predefined("i64".into()),
            &[],
            &[],
        );
        assert_eq!(report.result, SolveResult::Proven);
    }

    #[test]
    fn canonical_database_is_source_order_independent() {
        let first =
            database("trait Left {} trait Right {} impl Left for i64 {} impl Right for Text {}");
        let second =
            database("impl Right for Text {} trait Right {} impl Left for i64 {} trait Left {}");
        assert_eq!(first.canonical_text(), second.canonical_text());
        assert_eq!(first.fingerprint(), second.fingerprint());
    }

    #[test]
    fn constructor_index_matches_exhaustive_candidate_filter_on_a_small_model() {
        let db = database(
            "trait Marker {} trait Blocked {} struct Box<T>{value:T} struct Wrap<T>{value:T} \
             impl Marker for i64 {} impl<T> Marker for Box<T> {} \
             impl !Blocked for Text {} impl<T> !Blocked for Wrap<T> {}",
        );
        let types = [
            ProvisionalType::Predefined("i64".into()),
            ProvisionalType::Predefined("Text".into()),
            nominal("Box", vec![ProvisionalType::Predefined("Text".into())]),
            nominal("Wrap", vec![ProvisionalType::Predefined("i64".into())]),
        ];
        for polarity in [GoalPolarity::Positive, GoalPolarity::Negative] {
            for trait_name in ["Marker", "Blocked"] {
                for subject in &types {
                    let goal = GroundGoal {
                        polarity,
                        trait_key: TraitKey::Local(trait_name.into()),
                        subject: subject.clone(),
                        arguments: vec![],
                        bindings: vec![],
                        projections: vec![],
                    };
                    let exhaustive = db
                        .impls
                        .iter()
                        .enumerate()
                        .filter_map(|(index, implementation)| {
                            let mut substitutions = BTreeMap::new();
                            matches_goal(&implementation.head, &goal, &mut substitutions)
                                .then_some(index)
                        })
                        .collect::<Vec<_>>();
                    let indexed = db
                        .candidate_indices(&goal)
                        .into_iter()
                        .filter(|index| {
                            let mut substitutions = BTreeMap::new();
                            matches_goal(&db.impls[*index].head, &goal, &mut substitutions)
                        })
                        .collect::<Vec<_>>();
                    assert_eq!(indexed, exhaustive, "{polarity:?} {trait_name} {subject:?}");
                }
            }
        }
    }

    #[test]
    fn conservative_overlap_is_rejected() {
        let tokens = crate::lexer::lex(
            "trait Marker {} struct Box<T> { value: T } \
             impl<T> Marker for Box<T> {} impl Marker for Box<i64> {} main() -> { () }",
        )
        .unwrap();
        let program = crate::parser::parse(tokens).unwrap();
        let errors = TraitDb::build(&program).unwrap_err();
        assert!(
            errors
                .iter()
                .any(|error| error.message.contains("overlapping"))
        );
    }

    #[test]
    fn local_blanket_impls_select_for_predefined_nominal_and_parameter_subjects() {
        let db = database(
            "trait Identity{type Out;} struct Box<T>{value:T} \
             impl<T> Identity for T{type Out=T;}",
        );
        let subjects = [
            ProvisionalType::Predefined("i64".into()),
            nominal("Box", vec![ProvisionalType::Predefined("Text".into())]),
            ProvisionalType::Param(GenericParamKey {
                owner: DeclarationKey::Function("generic".into()),
                ordinal: 0,
            }),
        ];
        for subject in subjects {
            assert_eq!(
                db.solve_with_param_env_values(
                    &ParamEnv::default(),
                    GoalPolarity::Positive,
                    "Identity",
                    &subject,
                    &[],
                    &[associated("Out", subject.clone())],
                ),
                SolveResult::Proven
            );
            let goal = GroundGoal {
                polarity: GoalPolarity::Positive,
                trait_key: db.trait_key("Identity").unwrap().clone(),
                subject,
                arguments: vec![],
                bindings: vec![],
                projections: vec![],
            };
            assert_eq!(db.candidate_indices(&goal), vec![0]);
        }
    }

    #[test]
    fn blanket_heads_are_canonical_across_source_and_binder_reordering() {
        let first =
            database("trait Left{} trait Right{} impl<T> Left for T{} impl<U> !Right for U{}");
        let second =
            database("impl<X> !Right for X{} trait Right{} impl<Y> Left for Y{} trait Left{}");
        assert_eq!(first.canonical_text(), second.canonical_text());
        assert_eq!(first.fingerprint(), second.fingerprint());
        let text = ProvisionalType::Predefined("Text".into());
        assert_eq!(first.solve("Left", &text), SolveResult::Proven);
        assert_eq!(
            first.solve_with_polarity(GoalPolarity::Negative, "Right", &text, &[]),
            SolveResult::Proven
        );
    }

    #[test]
    fn blanket_heads_conflict_with_overlapping_positive_and_negative_nominal_heads() {
        for specific in ["impl Mark for Box<i64>{}", "impl !Mark for Box<i64>{}"] {
            let source = format!(
                "trait Mark{{}} struct Box<T>{{value:T}} impl<T> Mark for T{{}} \
                 {specific} main()->{{()}}"
            );
            let program = crate::parser::parse(crate::lexer::lex(&source).unwrap()).unwrap();
            let errors = TraitDb::build(&program).unwrap_err();
            assert!(errors.iter().any(|error| {
                error.code.as_deref() == Some("G1TR001")
                    && error
                        .message
                        .contains("overlapping implementations of `Mark`")
                    && error.span.is_some()
            }));
        }

        let source = "trait Mark{} struct Box<T>{value:T} \
                      impl<T> !Mark for T{} impl Mark for Box<i64>{} main()->{()}";
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        assert!(TraitDb::build(&program).unwrap_err().iter().any(|error| {
            error
                .message
                .contains("overlapping implementations of `Mark`")
        }));
    }

    #[test]
    fn recursive_blanket_where_goals_must_strictly_decrease() {
        for source in [
            "trait Loop{} impl<T> Loop for T where T:Loop{} main()->{()}",
            "trait Left{} trait Right{} impl<T> Left for T where T:Right{} \
             impl<U> Right for U where U:Left{} main()->{()}",
        ] {
            let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
            let errors = TraitDb::build(&program).unwrap_err();
            assert!(errors.iter().any(|error| {
                error.code.as_deref() == Some("G1TR001")
                    && error.message.contains("does not strictly decrease")
                    && error.span.is_some()
            }));
        }
    }

    #[test]
    fn joint_overlap_uses_finite_substitutions_and_trait_arguments() {
        let db = database(
            "trait Rel<To> {} struct Box<T> { value: T } \
             impl<T> Rel<T> for Box<T> {} \
             impl<U> Rel<Box<U>> for Box<U> {}",
        );
        let integer = ProvisionalType::Predefined("i64".into());
        let boxed_integer = nominal("Box", vec![integer.clone()]);
        assert_eq!(
            db.solve_with_arguments("Rel", &boxed_integer, std::slice::from_ref(&integer)),
            SolveResult::Proven
        );
        assert_eq!(
            db.solve_with_arguments("Rel", &boxed_integer, std::slice::from_ref(&boxed_integer),),
            SolveResult::Proven
        );
    }

    #[test]
    fn unsupported_impl_shapes_and_unknown_names_are_structured_errors() {
        let cases = [
            "trait Drop {} main() -> { () }",
            "impl !Drop for i64 {} main() -> { () }",
            "trait Marker {} impl Marker for Missing {} main() -> { () }",
            "trait Marker {} struct Box<T> { value: T } impl<T, U> Marker for Box<T> {} main() -> { () }",
            "trait Marker {} impl Unknown for i64 {} main() -> { () }",
        ];
        for source in cases {
            let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
            let errors = TraitDb::build(&program).unwrap_err();
            assert!(
                errors
                    .iter()
                    .all(|error| error.code.as_deref() == Some("G1TR001") && error.span.is_some())
            );
        }
    }

    fn manifest_with_open(name: &str, id: u64) -> TrustedTraitManifest {
        let mut declarations = TrustedTraitManifest::trusted_default().declarations;
        declarations.push(ManifestTrait {
            id,
            display_name: name.into(),
            parameters: vec![],
            associated_items: vec![],
            policy: TraitPolicy::ExternalOpen,
            role: None,
        });
        TrustedTraitManifest::new(declarations).unwrap()
    }

    #[test]
    fn external_open_orphan_policy_uses_declaration_provenance_for_both_polarities() {
        let manifest = manifest_with_open("Remote", 100);
        for source in [
            "struct Local {} impl Remote for Local {} main() -> { () }",
            "struct Local {} impl !Remote for Local {} main() -> { () }",
        ] {
            let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
            TraitDb::build_with_manifest(&program, &manifest).unwrap();
        }
        for source in [
            "impl Remote for i64 {} main() -> { () }",
            "impl !Remote for i64 {} main() -> { () }",
        ] {
            let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
            let errors = TraitDb::build_with_manifest(&program, &manifest).unwrap_err();
            assert!(
                errors
                    .iter()
                    .any(|error| error.message.contains("orphan implementation"))
            );
        }
        let source = "struct Local {} type Alias=Local; type Chained=Alias; impl Remote for Chained {} main() -> { () }";
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        let db = TraitDb::build_with_manifest(&program, &manifest).unwrap();
        assert_eq!(
            db.solve("Remote", &nominal("Local", vec![])),
            SolveResult::Proven
        );
    }

    #[test]
    fn external_associated_const_parameters_bind_by_declared_kind() {
        let mut declarations = TrustedTraitManifest::trusted_default().declarations;
        declarations.push(ManifestTrait {
            id: 100,
            display_name: "Remote".into(),
            parameters: vec![],
            associated_items: vec![ManifestAssociatedItem {
                name: "Item".into(),
                parameters: vec![GenericParameterKind::Const(ConstKind::U32)],
                kind: AssociatedItemKind::Type,
            }],
            policy: TraitPolicy::ExternalOpen,
            role: None,
        });
        let manifest = TrustedTraitManifest::new(declarations).unwrap();
        // A type binder against the manifest's declared const kind is a
        // precise kind mismatch, not a blanket rejection.
        let source = "struct Local{} impl Remote for Local { type Item<T> = T; } main()->{()}";
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        let errors = TraitDb::build_with_manifest(&program, &manifest).unwrap_err();
        assert!(errors.iter().any(|error| {
            error.code.as_deref() == Some("G1TR001")
                && error
                    .message
                    .contains("associated type binder has the wrong kind")
        }));
        // A conforming const binder is accepted.
        let source =
            "struct Local{} impl Remote for Local { type Item<const N: u32> = i64; } main()->{()}";
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        TraitDb::build_with_manifest(&program, &manifest).unwrap();
    }

    #[test]
    fn generic_alias_impl_heads_require_identity_preserving_substitution() {
        let manifest = manifest_with_open("Remote", 100);
        let source = "struct Local<T>{value:T} type Wrapped<X> = Local<X>; impl<T> Remote for Wrapped<T>{} main()->{()}";
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        let db = TraitDb::build_with_manifest(&program, &manifest).unwrap();
        assert_eq!(
            db.solve(
                "Remote",
                &nominal("Local", vec![ProvisionalType::Predefined("Text".into())])
            ),
            SolveResult::Proven
        );
        let reordered = "main()->{()} impl<T> Remote for Wrapped<T>{} type Wrapped<X> = Local<X>; struct Local<T>{value:T}";
        let reordered = crate::parser::parse(crate::lexer::lex(reordered).unwrap()).unwrap();
        let reordered = TraitDb::build_with_manifest(&reordered, &manifest).unwrap();
        assert_eq!(db.canonical_text(), reordered.canonical_text());
        assert_eq!(db.fingerprint(), reordered.fingerprint());
        for source in [
            "struct Local<T>{value:T} type Fixed<T> = Local<Text>; impl<T> Remote for Fixed<T>{} main()->{()}",
            "struct Pair<A,B>{left:A, right:B} type Swap<A,B> = Pair<B,A>; impl<A,B> Remote for Swap<A,B>{} main()->{()}",
        ] {
            let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
            let errors = TraitDb::build_with_manifest(&program, &manifest).unwrap_err();
            assert!(errors.iter().any(|error| {
                error
                    .message
                    .contains("identity-preserving ordered substitution")
                    && error.code.as_deref() == Some("G1TR001")
                    && error.span.is_some()
            }));
        }
    }

    #[test]
    fn rigid_lifetime_arguments_flow_through_impls_where_goals_and_canonical_keys() {
        let source = "trait Gate<'a>{} trait Scoped<'a>{} struct Local{} impl<'a> Gate<'a> for Text{} impl<'a> Scoped<'a> for Local where Text:Gate<'a>{} main()->{()}";
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        let db = TraitDb::build(&program).unwrap();
        let local = ProvisionalType::Nominal(NominalInstanceKey {
            declaration: NominalKey("Local".into()),
            arguments: vec![],
        });
        let gate_goal = GroundGoal {
            polarity: GoalPolarity::Positive,
            trait_key: db.trait_key("Gate").unwrap().clone(),
            subject: ProvisionalType::Predefined("Text".into()),
            arguments: vec![GenericArg::Lifetime(LifetimeArg::Static)],
            bindings: vec![],
            projections: vec![],
        };
        assert_eq!(db.candidate_indices(&gate_goal).len(), 1);
        assert!(matches_goal(
            &db.impls[db.candidate_indices(&gate_goal)[0]].head,
            &gate_goal,
            &mut BTreeMap::new()
        ));
        let solve = |db: &TraitDb, lifetime| {
            let mut budget = SolverBudget::default();
            db.solve_with_generic_arguments_detailed_with_budget(
                &mut budget,
                &ParamEnv::default(),
                GoalPolarity::Positive,
                "Scoped",
                &local,
                &[GenericArg::Lifetime(lifetime)],
                &[],
            )
            .result
        };
        let mut gate_budget = SolverBudget::default();
        assert_eq!(
            db.solve_with_generic_arguments_detailed_with_budget(
                &mut gate_budget,
                &ParamEnv::default(),
                GoalPolarity::Positive,
                "Gate",
                &ProvisionalType::Predefined("Text".into()),
                &[GenericArg::Lifetime(LifetimeArg::Static)],
                &[],
            )
            .result,
            SolveResult::Proven
        );
        assert_eq!(solve(&db, LifetimeArg::Static), SolveResult::Proven);
        assert_eq!(solve(&db, LifetimeArg::Rigid(7)), SolveResult::Proven);

        let reordered = "main()->{()} impl<'a> Scoped<'a> for Local where Text:Gate<'a>{} struct Local{} impl<'a> Gate<'a> for Text{} trait Scoped<'a>{} trait Gate<'a>{}";
        let reordered = crate::parser::parse(crate::lexer::lex(reordered).unwrap()).unwrap();
        let reordered = TraitDb::build(&reordered).unwrap();
        assert_eq!(db.canonical_text(), reordered.canonical_text());
        assert_eq!(db.fingerprint(), reordered.fingerprint());
        assert_eq!(
            solve(&reordered, LifetimeArg::Rigid(7)),
            SolveResult::Proven
        );

        let negative =
            "trait Scoped<'a>{} struct Local{} impl<'a> !Scoped<'a> for Local{} main()->{()}";
        let negative = crate::parser::parse(crate::lexer::lex(negative).unwrap()).unwrap();
        let negative = TraitDb::build(&negative).unwrap();
        let mut budget = SolverBudget::default();
        assert_eq!(
            negative
                .solve_with_generic_arguments_detailed_with_budget(
                    &mut budget,
                    &ParamEnv::default(),
                    GoalPolarity::Negative,
                    "Scoped",
                    &local,
                    &[GenericArg::Lifetime(LifetimeArg::Rigid(9))],
                    &[],
                )
                .result,
            SolveResult::Proven
        );
    }

    #[test]
    fn nominal_lifetime_argument_constrains_its_impl_binder() {
        let source = "trait Marker{} struct View<'a>{value:&'a Text} impl<'a> Marker for View<'a>{} main()->{()}";
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        let db = TraitDb::build(&program).unwrap();
        assert_eq!(
            db.solve(
                "Marker",
                &ProvisionalType::Nominal(NominalInstanceKey {
                    declaration: NominalKey("View".into()),
                    arguments: vec![],
                }),
            ),
            SolveResult::Proven,
        );

        let unconstrained = "trait Marker{} struct View<'a>{value:&'a Text} impl<'a,'b> Marker for View<'a>{} main()->{()}";
        let program = crate::parser::parse(crate::lexer::lex(unconstrained).unwrap()).unwrap();
        let errors = TraitDb::build(&program).unwrap_err();
        assert!(errors.iter().any(|error| {
            error
                .message
                .contains("every impl binder must be constrained by the impl head")
        }));

        let trait_argument = "trait Marker<'a>{} impl<'a> Marker<'a> for Text{} main()->{()}";
        let program = crate::parser::parse(crate::lexer::lex(trait_argument).unwrap()).unwrap();
        TraitDb::build(&program).unwrap();
    }

    #[test]
    fn higher_ranked_where_goals_use_fresh_canonical_placeholders() {
        let source = "trait All<'a>{} trait Never<'a>{} trait Needs{} trait Avoids{} struct Local{} impl<'a> All<'a> for Text{} impl<'a> !Never<'a> for Text{} impl Needs for Local where for<'a> Text:All<'a>{} impl Avoids for Local where for<'a> Text:!Never<'a>{} main()->{()}";
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        let db = TraitDb::build(&program).unwrap();
        let local = ProvisionalType::Nominal(NominalInstanceKey {
            declaration: NominalKey("Local".into()),
            arguments: vec![],
        });
        assert_eq!(db.solve("Needs", &local), SolveResult::Proven);
        assert_eq!(db.solve("Avoids", &local), SolveResult::Proven);

        let reordered = "main()->{()} impl Avoids for Local where for<'n> Text:!Never<'n>{} impl Needs for Local where for<'renamed> Text:All<'renamed>{} struct Local{} impl<'x> !Never<'x> for Text{} impl<'x> All<'x> for Text{} trait Avoids{} trait Needs{} trait Never<'z>{} trait All<'z>{}";
        let reordered = crate::parser::parse(crate::lexer::lex(reordered).unwrap()).unwrap();
        let reordered = TraitDb::build(&reordered).unwrap();
        assert_eq!(db.canonical_text(), reordered.canonical_text());
        assert_eq!(db.fingerprint(), reordered.fingerprint());
        assert_eq!(reordered.solve("Needs", &local), SolveResult::Proven);
        assert_eq!(reordered.solve("Avoids", &local), SolveResult::Proven);

        let unbound = "trait All<'a>{} trait Needs{} struct Local{} impl Needs for Local where Text:All<'missing>{} main()->{()}";
        let unbound = crate::parser::parse(crate::lexer::lex(unbound).unwrap()).unwrap();
        let errors = TraitDb::build(&unbound).unwrap_err();
        assert!(errors.iter().any(|error| {
            error.code.as_deref() == Some("G1TR001")
                && error
                    .message
                    .contains("unbound lifetime argument `'missing`")
                && error.span.is_some()
        }));

        let type_universe = "trait Every<T>{} trait Only<T>{} trait Project<T>{type Out;} trait Universal{} trait NotUniversal{} trait NoLeak{} struct Witness{} impl<T> Every<T> for Text{} impl Only<i64> for Text{} impl<T> Project<T> for Text{type Out=T;} impl Universal for Witness where for<T> Text:Every<T>{} impl NotUniversal for Witness where for<T> Text:Only<T>{} impl NoLeak for Witness where for<T> Text:Project<T,Out=i64>{} main()->{()}";
        let type_universe =
            crate::parser::parse(crate::lexer::lex(type_universe).unwrap()).unwrap();
        let type_universe = TraitDb::build(&type_universe).unwrap();
        let witness = ProvisionalType::Nominal(NominalInstanceKey {
            declaration: NominalKey("Witness".into()),
            arguments: vec![],
        });
        assert_eq!(
            type_universe.solve("Universal", &witness),
            SolveResult::Proven,
            "a blanket implementation must satisfy a universally quantified type goal"
        );
        assert_eq!(
            type_universe.solve("NotUniversal", &witness),
            SolveResult::NoEvidence,
            "one concrete implementation must not satisfy `for<T>`"
        );
        assert_eq!(
            type_universe.solve("NoLeak", &witness),
            SolveResult::NoEvidence,
            "a higher-ranked placeholder must not leak into a preexisting associated equality"
        );
    }

    #[test]
    fn nested_higher_ranked_type_goals_use_distinct_universes() {
        let source = "trait Pair<A,B>{} trait Outer<A>{} trait Witness{} struct Local{} impl<X> Pair<X,X> for Text{} impl<U> Outer<U> for Text where for<V> Text:Pair<U,V>{} impl Witness for Local where for<T> Text:Outer<T>{} main()->{()}";
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        let db = TraitDb::build(&program).unwrap();
        let local = ProvisionalType::Nominal(NominalInstanceKey {
            declaration: NominalKey("Local".into()),
            arguments: vec![],
        });
        let placeholder = ProvisionalType::Param(GenericParamKey {
            owner: DeclarationKey::Function("$higher_ranked_universe_1".into()),
            ordinal: 0,
        });
        let text = ProvisionalType::Predefined("Text".into());
        assert_eq!(
            db.solve_with_param_env_values(
                &ParamEnv::default(),
                GoalPolarity::Positive,
                "Pair",
                &text,
                &[placeholder.clone(), placeholder.clone()],
                &[],
            ),
            SolveResult::Proven,
        );
        assert_eq!(
            db.solve_with_param_env_values(
                &ParamEnv::default(),
                GoalPolarity::Positive,
                "Outer",
                &text,
                &[placeholder],
                &[],
            ),
            SolveResult::NoEvidence,
            "the nested universal must be fresh even when its ordinal equals the outer placeholder",
        );
        assert_eq!(
            db.solve("Witness", &local),
            SolveResult::NoEvidence,
            "an inner higher-ranked binder must not alias an outer binder with the same ordinal"
        );

        let universal = "trait Pair<A,B>{} trait Outer<A>{} trait Witness{} struct Local{} impl<X,Y> Pair<X,Y> for Text{} impl<U> Outer<U> for Text where for<V> Text:Pair<U,V>{} impl Witness for Local where for<T> Text:Outer<T>{} main()->{()}";
        let program = crate::parser::parse(crate::lexer::lex(universal).unwrap()).unwrap();
        let db = TraitDb::build(&program).unwrap();
        assert_eq!(db.solve("Witness", &local), SolveResult::Proven);
    }

    #[test]
    fn monomorphic_alias_impl_heads_expand_to_their_true_supported_shape() {
        let db = database("trait Marker{} type Scalar=i64; impl Marker for Scalar{}");
        assert_eq!(
            db.solve("Marker", &ProvisionalType::Predefined("i64".into())),
            SolveResult::Proven
        );

        let borrowed =
            database("trait Marker{} type Borrowed=&i64; impl Marker for Borrowed{} main()->{()}");
        assert_eq!(
            borrowed.solve(
                "Marker",
                &ProvisionalType::Shared(Box::new(ProvisionalType::Predefined("i64".into())))
            ),
            SolveResult::Proven
        );
        let pair =
            database("trait Marker{} type Pair=(i64,i64); impl Marker for Pair{} main()->{()}");
        assert_eq!(
            pair.solve(
                "Marker",
                &ProvisionalType::Tuple(vec![
                    ProvisionalType::Predefined("i64".into()),
                    ProvisionalType::Predefined("i64".into()),
                ])
            ),
            SolveResult::Proven
        );
    }

    #[test]
    fn quantity_const_arguments_match_ground_and_binder_impl_patterns() {
        let fixed =
            database("trait Quota<const Q: Quantity>{} struct S{} impl Quota<[0,1]> for S{}");
        let key = fixed.trait_key("Quota").unwrap().clone();
        let mut budget = SolverBudget::default();
        assert_eq!(
            fixed
                .solve_with_key_detailed_with_budget(
                    &mut budget,
                    &ParamEnv::default(),
                    GoalPolarity::Positive,
                    &key,
                    &nominal("S", vec![]),
                    &[GenericArg::Const(ConstValue::Quantity {
                        lower: 0,
                        upper: Some(1)
                    })],
                    &[],
                )
                .result,
            SolveResult::Proven
        );
        let generic = database(
            "trait Quota<const Q: Quantity>{} struct S{} impl<const Q: Quantity> Quota<Q> for S{}",
        );
        let key = generic.trait_key("Quota").unwrap().clone();
        assert_eq!(
            generic
                .solve_with_key_detailed_with_budget(
                    &mut budget,
                    &ParamEnv::default(),
                    GoalPolarity::Positive,
                    &key,
                    &nominal("S", vec![]),
                    &[GenericArg::Const(ConstValue::Quantity {
                        lower: 2,
                        upper: None
                    })],
                    &[],
                )
                .result,
            SolveResult::Proven
        );
    }

    #[test]
    fn nominal_const_impl_heads_select_by_value_and_preserve_source_order() {
        let db = database(
            "trait Mark{} struct Cell<'a,const N:u32,T>{value:T} \
             impl Mark for Cell<'static,7,Text>{} \
             impl Mark for Cell<'static,8,i64>{}",
        );
        let cell = |value: u32, ty: &str| {
            nominal(
                "Cell",
                vec![
                    encode_const_value(&ConstValue::U32(value)),
                    ProvisionalType::Predefined(ty.into()),
                ],
            )
        };
        assert_eq!(db.solve("Mark", &cell(7, "Text")), SolveResult::Proven);
        assert_eq!(db.solve("Mark", &cell(8, "i64")), SolveResult::Proven);
        assert_eq!(db.solve("Mark", &cell(7, "i64")), SolveResult::NoEvidence);
        assert_eq!(db.solve("Mark", &cell(8, "Text")), SolveResult::NoEvidence);
    }

    #[test]
    fn nominal_const_impl_binders_instantiate_and_overlap_fixed_heads() {
        let generic = database(
            "trait Mark{} struct Token<const N:u32>{value:i64} \
             impl<const N:u32> Mark for Token<N>{}",
        );
        for value in [0, 7, u32::MAX] {
            assert_eq!(
                generic.solve(
                    "Mark",
                    &nominal("Token", vec![encode_const_value(&ConstValue::U32(value))]),
                ),
                SolveResult::Proven
            );
        }

        let source = "trait Mark{} struct Token<const N:u32>{value:i64} \
                      impl<const N:u32> Mark for Token<N>{} \
                      impl Mark for Token<7>{} main()->{()}";
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        let errors = TraitDb::build(&program).unwrap_err();
        assert!(errors.iter().any(|error| {
            error.code.as_deref() == Some("G1TR001")
                && error.message.contains("overlapping implementations")
        }));
    }

    #[test]
    fn nominal_const_substitutions_flow_through_where_goals_and_associated_values() {
        let db = database(
            "trait Inner{} trait Family{type Out;} \
             struct Token<const N:u32>{value:i64} \
             impl Inner for Token<7>{} \
             impl<const N:u32> Family for Token<N> where Token<N>:Inner \
             {type Out=Token<N>;}",
        );
        let token = |value| nominal("Token", vec![encode_const_value(&ConstValue::U32(value))]);
        assert_eq!(
            db.solve_with_param_env_values(
                &ParamEnv::default(),
                GoalPolarity::Positive,
                "Family",
                &token(7),
                &[],
                &[associated("Out", token(7))],
            ),
            SolveResult::Proven
        );
        assert_eq!(
            db.solve_with_param_env_values(
                &ParamEnv::default(),
                GoalPolarity::Positive,
                "Family",
                &token(8),
                &[],
                &[associated("Out", token(8))],
            ),
            SolveResult::NoEvidence
        );
    }

    #[test]
    fn distinct_nominal_const_impl_heads_do_not_overlap() {
        let db = database(
            "trait Mark{} struct Token<const N:u32>{value:i64} \
             impl Mark for Token<7>{} impl Mark for Token<8>{}",
        );
        assert_eq!(
            db.solve(
                "Mark",
                &nominal("Token", vec![encode_const_value(&ConstValue::U32(7))]),
            ),
            SolveResult::Proven
        );
        assert_eq!(
            db.solve(
                "Mark",
                &nominal("Token", vec![encode_const_value(&ConstValue::U32(9))]),
            ),
            SolveResult::NoEvidence
        );
    }

    #[test]
    fn universal_supertrait_validation_uses_negative_lexical_prerequisites() {
        database(
            "trait Gate{} trait Parent{} trait Child:Parent{} \
             struct Box<T>{value:T} \
             impl<T> Parent for Box<T> where T:!Gate{} \
             impl<U> Child for Box<U> where U:!Gate{}",
        );
    }

    #[test]
    fn universal_supertrait_validation_is_alpha_equivalent_under_binder_permutation() {
        database(
            "trait Parent{} trait Child:Parent{} \
             struct Pair<A,B>{left:A,right:B} \
             impl<A,B> Parent for Pair<B,A>{} \
             impl<X,Y> Child for Pair<X,Y>{}",
        );
    }

    #[test]
    fn supertrait_const_parameter_kinds_cannot_be_alpha_unified() {
        let source = "trait Parent<const N:u32>{} \
                      trait Child<const Q:Quantity>:Parent<Q>{} main()->{()}";
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        let errors = TraitDb::build(&program).unwrap_err();
        assert!(errors.iter().any(|diagnostic| {
            diagnostic.code.as_deref() == Some("G1TR001")
                && diagnostic.message.contains("wrong kind")
        }));
    }

    #[test]
    fn intrinsic_authority_cannot_be_created_by_source_spelling() {
        for source in [
            "trait Fn<T> { type Output; type Effects; } main() -> { () }",
            "struct Local {} impl Fn<i64> for Local { type Output = i64; type Effects = i64; } main() -> { () }",
            "struct Local {} impl !Drop for Local {} main() -> { () }",
        ] {
            let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
            assert!(TraitDb::build(&program).is_err());
        }
    }

    #[test]
    fn dedicated_use_evidence_entails_only_intervals_inside_the_principal_interval() {
        let db = database("struct Token{} impl Use<[0,2]> for Token{}");
        let token = nominal("Token", vec![]);
        let solve = |lower, upper| {
            let mut budget = SolverBudget::default();
            db.solve_with_key_detailed_with_budget(
                &mut budget,
                &ParamEnv::default(),
                GoalPolarity::Positive,
                db.intrinsic_key(IntrinsicRole::Use).unwrap(),
                &token,
                &[GenericArg::Const(ConstValue::Quantity { lower, upper })],
                &[],
            )
            .result
        };
        assert_eq!(solve(0, Some(0)), SolveResult::Proven);
        assert_eq!(solve(1, Some(2)), SolveResult::Proven);
        assert_eq!(solve(0, Some(3)), SolveResult::NoEvidence);
        assert_eq!(solve(0, None), SolveResult::NoEvidence);

        let mut budget = SolverBudget::default();
        assert_eq!(
            db.solve_with_key_detailed_with_budget(
                &mut budget,
                &ParamEnv::default(),
                GoalPolarity::Negative,
                db.intrinsic_key(IntrinsicRole::Use).unwrap(),
                &token,
                &[GenericArg::Const(ConstValue::Quantity {
                    lower: 0,
                    upper: Some(0),
                })],
                &[],
            )
            .result,
            SolveResult::Refuted
        );
    }

    #[test]
    fn predefined_use_evidence_tracks_runtime_type_capabilities() {
        let db = database("");
        let use_key = db.intrinsic_key(IntrinsicRole::Use).unwrap();
        let solve = |name: &str, lower, upper| {
            let mut budget = SolverBudget::default();
            db.solve_with_key_detailed_with_budget(
                &mut budget,
                &ParamEnv::default(),
                GoalPolarity::Positive,
                use_key,
                &ProvisionalType::Predefined(name.into()),
                &[GenericArg::Const(ConstValue::Quantity { lower, upper })],
                &[],
            )
            .result
        };
        for name in [
            "Unit", "u8", "u16", "u32", "u64", "u128", "i8", "i16", "i32", "i64", "i128", "usize",
            "isize", "f32", "f64", "Char", "Text", "Bytes",
        ] {
            assert_eq!(
                solve(name, 0, None),
                SolveResult::Proven,
                "{name} should expose its persistent runtime capability"
            );
            assert_eq!(solve(name, 0, Some(0)), SolveResult::Proven);
        }
        assert_eq!(solve("Never", 1, Some(1)), SolveResult::Proven);
        assert_eq!(solve("Never", 0, Some(0)), SolveResult::NoEvidence);
        assert_eq!(solve("Never", 0, None), SolveResult::NoEvidence);
    }

    #[test]
    fn dedicated_use_has_one_coherent_principal_interval_per_overlapping_head() {
        let source = "struct Token{} impl Use<[0,1]> for Token{} \
                      impl Use<[0,2]> for Token{} main()->{()}";
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        let errors = TraitDb::build(&program).unwrap_err();
        assert!(errors.iter().any(|error| {
            error.code.as_deref() == Some("G1TR001")
                && error
                    .message
                    .contains("overlapping implementations of `Use`")
                && error.span.is_some()
        }));
    }

    #[test]
    fn dedicated_use_where_goals_transport_associated_projection_evidence() {
        let db = database(
            "trait Family{type Item;} struct Good{} struct Wrap<T>{value:T} \
             impl Family for Good{type Item=i64;} \
             impl<T> Use<[0,1]> for Wrap<T> where T:Family<Item=i64>{}",
        );
        let requested = [GenericArg::Const(ConstValue::Quantity {
            lower: 0,
            upper: Some(0),
        })];
        let use_key = db.intrinsic_key(IntrinsicRole::Use).unwrap();
        let solve = |argument| {
            let mut budget = SolverBudget::default();
            db.solve_with_key_detailed_with_budget(
                &mut budget,
                &ParamEnv::default(),
                GoalPolarity::Positive,
                use_key,
                &nominal("Wrap", vec![argument]),
                &requested,
                &[],
            )
            .result
        };
        assert_eq!(solve(nominal("Good", vec![])), SolveResult::Proven);
        assert_eq!(
            solve(ProvisionalType::Predefined("Text".into())),
            SolveResult::NoEvidence
        );
    }

    #[test]
    fn dedicated_drop_evidence_enforces_the_frozen_zero_use_supertrait() {
        let affine = database(
            "struct Token{} impl Use<[0,1]> for Token{} \
             impl Drop for Token{drop(&mut self)->{()}}",
        );
        let token = nominal("Token", vec![]);
        assert_eq!(affine.solve("Drop", &token), SolveResult::Proven);

        let linear = database(
            "struct Token{} impl Use<[1,1]> for Token{} \
             impl Drop for Token{drop(&mut self)->{()}}",
        );
        assert_eq!(linear.solve("Drop", &token), SolveResult::NoEvidence);
    }

    #[test]
    fn manifest_rejects_duplicate_missing_and_malformed_intrinsic_identity() {
        let default = TrustedTraitManifest::trusted_default();
        let mut duplicate = default.declarations.clone();
        duplicate.push(duplicate[0].clone());
        assert!(TrustedTraitManifest::new(duplicate).is_err());

        let mut missing = default.declarations.clone();
        missing.retain(|declaration| declaration.role != Some(IntrinsicRole::Use));
        assert!(TrustedTraitManifest::new(missing).is_err());

        let mut malformed = default.declarations;
        let use_decl = malformed
            .iter_mut()
            .find(|declaration| declaration.role == Some(IntrinsicRole::Use))
            .unwrap();
        use_decl.parameters = vec![GenericParameterKind::Type];
        assert!(TrustedTraitManifest::new(malformed).is_err());
    }

    // ===== Const-kinded generic arguments for associated types and GATs =====

    #[test]
    fn concrete_const_gat_projection_normalizes() {
        let source = "trait Buffer { type Slot<const N: u32>; } \
             impl Buffer for Text { type Slot<const N: u32> = i64; } \
             inspect(value: <Text as Buffer>::Slot<3>) -> { () } main() -> { () }";
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        let db = TraitDb::build(&program).unwrap();
        let projection = &program
            .functions
            .iter()
            .find(|function| function.name == "inspect")
            .unwrap()
            .params[0]
            .ty;
        assert_eq!(
            db.normalize_type(projection),
            Ok(ProvisionalType::Predefined("i64".into()))
        );
    }

    #[test]
    fn open_effect_row_gat_normalization_preserves_canonical_members_and_symbolic_tail() {
        let source = "effect Fail<E>{fail(error:E)->!} struct Carrier{} \
                      trait Capability{type Effects<e:EffectRow>:EffectRow;} \
                      impl Capability for Carrier{type Effects<r:EffectRow> = {Fail<i64>|r};} \
                      forward<e:EffectRow>()-> / {<Carrier as Capability>::Effects<e>}{()} \
                      main()->{()}";
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        let db = TraitDb::build(&program).unwrap();
        let projection = &program
            .functions
            .iter()
            .find(|function| function.name == "forward")
            .unwrap()
            .outward_effects
            .as_ref()
            .unwrap()
            .effects[0];
        let tail = ProvisionalType::Param(GenericParamKey {
            owner: DeclarationKey::Function("forward".into()),
            ordinal: 0,
        });
        let mut budget = SolverBudget::default();
        let row = db
            .normalize_symbolic_effect_row_projection_with_budget(
                projection,
                &BTreeMap::from([("e".into(), tail.clone())]),
                &ParamEnv::default(),
                &mut budget,
            )
            .unwrap();
        assert!(row.iter().any(|member| member.declaration.0 == "Fail"));
        assert!(row.iter().any(|member| {
            member.declaration.0 == EFFECT_ROW_TAIL_PREFIX && member.arguments == vec![tail.clone()]
        }));
    }

    #[test]
    fn generic_const_substitution_selects_and_normalizes_through_impls() {
        let source = "trait Family<const N: u32> { type Member<const M: u32>; } \
             struct S {} \
             impl<const K: u32> Family<K> for S { type Member<const M: u32> = Text; } \
             inspect(value: <S as Family<7>>::Member<9>) -> { () } main() -> { () }";
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        let db = TraitDb::build(&program).unwrap();
        let projection = &program
            .functions
            .iter()
            .find(|function| function.name == "inspect")
            .unwrap()
            .params[0]
            .ty;
        assert_eq!(
            db.normalize_type(projection),
            Ok(ProvisionalType::Predefined("Text".into()))
        );
    }

    #[test]
    fn impl_selection_is_distinguished_by_const_values() {
        let source = "trait Tagged<const N: u32> { type Out; } struct S {} \
             impl Tagged<3> for S { type Out = i64; } \
             impl Tagged<4> for S { type Out = Text; } \
             low(value: <S as Tagged<3>>::Out) -> { () } \
             high(value: <S as Tagged<4>>::Out) -> { () } main() -> { () }";
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        let db = TraitDb::build(&program).unwrap();
        let param = |name: &str| {
            &program
                .functions
                .iter()
                .find(|function| function.name == name)
                .unwrap()
                .params[0]
                .ty
        };
        assert_eq!(
            db.normalize_type(param("low")),
            Ok(ProvisionalType::Predefined("i64".into()))
        );
        assert_eq!(
            db.normalize_type(param("high")),
            Ok(ProvisionalType::Predefined("Text".into()))
        );
        let mut budget = SolverBudget::default();
        assert_eq!(
            db.solve_with_generic_arguments_detailed_with_budget(
                &mut budget,
                &ParamEnv::default(),
                GoalPolarity::Positive,
                "Tagged",
                &nominal("S", vec![]),
                &[GenericArg::Const(ConstValue::U32(5))],
                &[],
            )
            .result,
            SolveResult::NoEvidence
        );
    }

    #[test]
    fn mixed_lifetime_type_and_const_arguments_preserve_positions() {
        let source = "trait Family { type Member<'a, const N: u32, T>; } \
             impl Family for Text { type Member<'x, const M: u32, U> = U; } \
             inspect(value: <Text as Family>::Member<'static, 5, i64>) -> { () } main() -> { () }";
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        let db = TraitDb::build(&program).unwrap();
        let projection = &program
            .functions
            .iter()
            .find(|function| function.name == "inspect")
            .unwrap()
            .params[0]
            .ty;
        assert_eq!(
            db.normalize_type(projection),
            Ok(ProvisionalType::Predefined("i64".into()))
        );
    }

    #[test]
    fn associated_equalities_with_const_arguments_key_per_application() {
        let db = database("trait Family { type Member<const N: u32>; }");
        let fact = |value: u32, result: &str| TraitFact {
            polarity: GoalPolarity::Positive,
            trait_key: TraitKey::Local("Family".into()),
            subject: ProvisionalType::Predefined("Text".into()),
            arguments: vec![],
            bindings: vec![AssociatedValue {
                item: "Member".into(),
                arguments: vec![GenericArg::Const(ConstValue::U32(value))],
                value: ProvisionalType::Predefined(result.into()),
            }],
        };
        assert!(
            db.param_env([fact(3, "i64"), fact(4, "Text")])
                .is_consistent()
        );
        assert!(
            !db.param_env([fact(3, "i64"), fact(3, "Text")])
                .is_consistent()
        );
    }

    #[test]
    fn rigid_consts_stay_symbolic_and_never_equate_eagerly() {
        let db = database("trait Family { type Member<const N: u32>; }");
        let fact = |argument: GenericArg, result: &str| TraitFact {
            polarity: GoalPolarity::Positive,
            trait_key: TraitKey::Local("Family".into()),
            subject: ProvisionalType::Predefined("Text".into()),
            arguments: vec![],
            bindings: vec![AssociatedValue {
                item: "Member".into(),
                arguments: vec![argument],
                value: ProvisionalType::Predefined(result.into()),
            }],
        };
        // Distinct rigid const binders never merge.
        assert!(
            db.param_env([
                fact(GenericArg::RigidConst(1, ConstKind::U32), "i64"),
                fact(GenericArg::RigidConst(2, ConstKind::U32), "Text"),
            ])
            .is_consistent()
        );
        // A rigid const is not eagerly equated with an unrelated value.
        assert!(
            db.param_env([
                fact(GenericArg::RigidConst(1, ConstKind::U32), "i64"),
                fact(GenericArg::Const(ConstValue::U32(3)), "Text"),
            ])
            .is_consistent()
        );
        // The same rigid const cannot own two conflicting equalities.
        assert!(
            !db.param_env([
                fact(GenericArg::RigidConst(1, ConstKind::U32), "i64"),
                fact(GenericArg::RigidConst(1, ConstKind::U32), "Text"),
            ])
            .is_consistent()
        );
    }

    #[test]
    fn const_gat_fingerprints_are_deterministic_across_reordering() {
        let source = "trait Family { type Member<const N: u32, T>; } \
             impl Family for Text { type Member<const M: u32, U> = U; } \
             inspect(value: <Text as Family>::Member<5, i64>) -> { () } main() -> { () }";
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        let db = TraitDb::build(&program).unwrap();
        let reordered = "main() -> { () } \
             impl Family for Text { type Member<const Renamed: u32, V> = V; } \
             trait Family { type Member<const N: u32, T>; } \
             inspect(value: <Text as Family>::Member<5, i64>) -> { () }";
        let reordered = crate::parser::parse(crate::lexer::lex(reordered).unwrap()).unwrap();
        let reordered = TraitDb::build(&reordered).unwrap();
        assert_eq!(db.canonical_text(), reordered.canonical_text());
        assert_eq!(db.fingerprint(), reordered.fingerprint());
    }

    #[test]
    fn const_gat_argument_errors_are_structured_with_exact_spans() {
        let cases: [(&str, &str, &str); 6] = [
            (
                "trait Family { type Member<const N: u32>; } struct Box<T> { value: T } \
                 trait Marker {} impl<T> Marker for Box<T> where T: Family<Member<3, 4> = i64> {} \
                 main() -> { () }",
                "wrong arity for associated type `Member`",
                "Member<3, 4> = i64",
            ),
            (
                "trait Family { type Member<const N: u32>; } struct Box<T> { value: T } \
                 trait Marker {} impl<T> Marker for Box<T> where T: Family<Member<i64> = i64> {} \
                 main() -> { () }",
                "unbound const argument `i64`",
                "i64",
            ),
            (
                "trait Family { type Member<T>; } struct Box<T> { value: T } \
                 trait Marker {} impl<T> Marker for Box<T> where T: Family<Member<3> = i64> {} \
                 main() -> { () }",
                "associated argument has the wrong kind",
                "3",
            ),
            (
                "trait Family { type Member<const N: u32>; } \
                 impl Family for Text { type Member<T> = i64; } main() -> { () }",
                "associated type binder has the wrong kind",
                "T",
            ),
            (
                "trait Quota { type Slot<const Q: Quantity>; } struct Box<T> { value: T } \
                 trait Marker {} impl<T> Marker for Box<T> where T: Quota<Slot<[2, 1]> = i64> {} \
                 main() -> { () }",
                "quantity lower bound exceeds its upper bound",
                "[2, 1]",
            ),
            (
                "trait Family { type Member<const N: u32>; } struct Box<T> { value: T } \
                 trait Marker {} impl<T> Marker for Box<T> where T: Family<Member<4294967296> = i64> {} \
                 main() -> { () }",
                "u32 const argument exceeds the u32 domain",
                "4294967296",
            ),
        ];
        for (source, needle, spanned) in cases {
            let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
            let errors = TraitDb::build(&program).unwrap_err();
            let found = errors
                .iter()
                .find(|error| error.message.contains(needle))
                .unwrap_or_else(|| panic!("expected `{needle}` in {errors:#?}"));
            let span = found.span.expect("const argument diagnostics carry spans");
            assert_eq!(&source[span.start..span.end], spanned, "{needle}");
        }
    }

    #[test]
    fn unbound_const_names_in_projections_are_rejected() {
        let source = "trait Family { type Member<const N: u32>; } \
             impl Family for Text { type Member<const M: u32> = i64; } \
             inspect(value: <Text as Family>::Member<Unbound>) -> { () } main() -> { () }";
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        let db = TraitDb::build(&program).unwrap();
        let projection = &program
            .functions
            .iter()
            .find(|function| function.name == "inspect")
            .unwrap()
            .params[0]
            .ty;
        assert!(db.normalize_type(projection).is_err());
    }

    #[test]
    fn const_gat_normalization_cycles_are_reported_not_hung() {
        let source = "trait Family { type Member<const N: u32>; } \
             impl Family for Text { type Member<const N: u32> = <Text as Family>::Member<N>; } \
             inspect(value: <Text as Family>::Member<5>) -> { () } main() -> { () }";
        let program = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap();
        let db = TraitDb::build(&program).unwrap();
        let projection = &program
            .functions
            .iter()
            .find(|function| function.name == "inspect")
            .unwrap()
            .params[0]
            .ty;
        let report = db.normalize_type_detailed(projection).unwrap_err();
        assert!(report.failure.is_some(), "{report:?}");
    }

    #[test]
    fn malformed_const_argument_syntax_is_rejected_by_the_parser() {
        for (source, needle) in [
            (
                "inspect(value: <Text as Family>::Member<1.5>) -> { () } main() -> { () }",
                "invalid const argument",
            ),
            (
                "inspect(value: <Text as Family>::Member<[1>) -> { () } main() -> { () }",
                "expected `,` between quantity bounds",
            ),
        ] {
            let error = crate::parser::parse(crate::lexer::lex(source).unwrap()).unwrap_err();
            assert!(
                error.title.contains(needle) || error.message.contains(needle),
                "{source}: {error:?}"
            );
        }
    }
}
