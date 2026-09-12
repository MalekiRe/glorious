import GloriousLanguage.Target

/-! One declaration inventory, supplied source closure, and grounded fixed-point
resolution. Aliases and imports retain authority rather than duplicating it. -/
namespace Glorious.Language

structure SourceAnchor where
  file : Identity
  node : List Nat
  deriving DecidableEq, BEq, Repr, Inhabited

structure FieldDefinition where
  header : Header
  type : Term
  deriving Repr, Inhabited

structure VariantDefinition where
  header : Header
  fields : List FieldDefinition
  deriving Repr, Inhabited

structure DataDefinition where
  header : Header
  generics : List Binder
  requirements : List Constraint
  variants : List VariantDefinition
  isEnum : Bool
  nonExhaustive : Bool
  representation : Representation
  principalRestriction : Option Principal
  quantitySource : Option Term
  invariant : Option DeclId
  dropHook : Option DeclId
  deriving Repr, Inhabited

structure AliasDefinition where
  header : Header
  generics : List Binder
  value : Term
  deriving Repr, Inhabited

structure TraitDefinition where
  header : Header
  generics : List Binder
  requirements : List Constraint
  members : List DeclId
  unsafeAllowed : Bool
  relation : IntrinsicRelation
  deriving Repr, Inhabited

structure AssociatedDefinition where
  header : Header
  owner : DeclId
  generics : List Binder
  kind : Kind
  requirements : List Constraint
  defaultValue : Option Term
  deriving Repr, Inhabited

structure ImplDefinition where
  header : Header
  generics : List Binder
  trait : DeclId
  arguments : List Term
  requirements : List Constraint
  associated : List (DeclId × Term)
  functions : List (DeclId × DeclId)
  unsafeAllowed : Bool
  negative : Bool
  deriving Repr, Inhabited

inductive BodyOrigin where
  | source (anchor : SourceAnchor)
  | traitMember (trait : DeclId)
  | runtime (manifest : Identity)
  | foreign
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Published invocation judgments. The whole-program admission predicate
checks each judgment against the corresponding structural body. -/
structure InvocationRelation where
  receiver : Term
  access : Term
  arguments : List Term
  result : Term
  effects : Term
  after : Term
  unsafeAllowed : Bool
  deriving Repr, Inhabited

structure FunctionDefinition where
  header : Header
  signature : Signature
  parameters : List Identity
  origin : BodyOrigin
  cABI : Bool
  exportName : Option String
  owner : Option DeclId
  captures : List Term := []
  invocations : List InvocationRelation := []
  deriving Repr, Inhabited

structure OperationDefinition where
  header : Header
  family : DeclId
  signature : Signature
  terminal : Bool
  quantity : Option Quantity
  deriving Repr, Inhabited

structure EffectDefinition where
  header : Header
  generics : List Binder
  requirements : List Constraint
  operations : List DeclId
  deriving Repr, Inhabited

structure ConstantDefinition where
  header : Header
  generics : List Binder
  type : Term
  value : Term
  deriving Repr, Inhabited

structure GlobalDefinition where
  header : Header
  type : Term
  initializer : SourceAnchor
  deriving Repr, Inhabited

structure ModuleDefinition where
  header : Header
  module : ModuleId
  directory : List String
  file : Identity
  inline : Bool
  parent : Option ModuleId
  deriving Repr, Inhabited

structure ImportDefinition where
  header : Header
  tree : Source.ImportTree
  prelude : Bool
  deriving Repr, Inhabited

structure FixityDefinition where
  header : Header
  operator : String
  kind : Source.FixityKind
  precedence : Nat
  target : DeclId
  deriving Repr, Inhabited

inductive Definition where
  | data (value : DataDefinition)
  | alias (value : AliasDefinition)
  | trait (value : TraitDefinition)
  | associated (value : AssociatedDefinition)
  | implementation (value : ImplDefinition)
  | function (value : FunctionDefinition)
  | operation (value : OperationDefinition)
  | effect (value : EffectDefinition)
  | constant (value : ConstantDefinition)
  | global (value : GlobalDefinition)
  | module (value : ModuleDefinition)
  | import (value : ImportDefinition)
  | fixity (value : FixityDefinition)
  deriving Repr, Inhabited

def Definition.header : Definition → Header
  | .data d => d.header | .alias d => d.header | .trait d => d.header
  | .associated d => d.header | .implementation d => d.header | .function d => d.header
  | .operation d => d.header | .effect d => d.header | .constant d => d.header
  | .global d => d.header | .module d => d.header | .import d => d.header | .fixity d => d.header

def InvocationRelation.terms (relation : InvocationRelation) : List Term :=
  relation.receiver :: relation.access :: relation.result :: relation.effects :: relation.after :: relation.arguments

/-- Complete semantic template projection. In particular, captures, generic
defaults and published invocation contracts belong to the declaration and
cannot smuggle an execution-specific identity into its immutable meaning. -/
def Definition.terms : Definition → List Term
  | .data entry =>
      (entry.variants.flatMap (·.fields)).map (·.type) ++ entry.quantitySource.toList ++
        entry.requirements.flatMap Constraint.terms ++ entry.generics.flatMap (fun binder => binder.defaultValue.toList)
  | .alias entry => entry.value :: entry.generics.flatMap (fun binder => binder.defaultValue.toList)
  | .function entry => entry.signature.terms ++ entry.captures ++ entry.invocations.flatMap InvocationRelation.terms
  | .trait entry => entry.requirements.flatMap Constraint.terms ++ entry.generics.flatMap (fun binder => binder.defaultValue.toList)
  | .associated entry => entry.defaultValue.toList ++ entry.requirements.flatMap Constraint.terms ++
      entry.generics.flatMap (fun binder => binder.defaultValue.toList)
  | .implementation entry => entry.arguments ++ entry.associated.map Prod.snd ++
      entry.requirements.flatMap Constraint.terms ++ entry.generics.flatMap (fun binder => binder.defaultValue.toList)
  | .effect entry => entry.requirements.flatMap Constraint.terms ++ entry.generics.flatMap (fun binder => binder.defaultValue.toList)
  | .operation entry => entry.signature.terms
  | .constant entry => entry.type :: entry.value :: entry.generics.flatMap (fun binder => binder.defaultValue.toList)
  | .global entry => [entry.type]
  | .module _ | .import _ | .fixity _ => []

def Definition.Lexical (definition : Definition) : Prop :=
  ∀ term ∈ definition.terms, term.Lexical

structure Package where
  id : Identity
  name : String
  root : Identity
  dependencies : List (String × Identity)
  noStd : Bool
  noPrelude : Bool
  deriving Repr, Inhabited

structure Input where
  packages : List Package
  files : List Source.File
  target : TargetProfile
  manifest : Manifest

structure Program where
  input : Input
  declarations : List Definition
  origins : List (DeclId × SourceAnchor)

def Program.lookup (program : Program) (id : DeclId) : Option Definition :=
  program.declarations.find? (fun declaration => declaration.header.id == id)

def Program.data (program : Program) (id : DeclId) : Option DataDefinition :=
  match program.lookup id with | some (.data data) => some data | _ => none
def Program.alias (program : Program) (id : DeclId) : Option AliasDefinition :=
  match program.lookup id with | some (.alias declaration) => some declaration | _ => none
def Program.trait (program : Program) (id : DeclId) : Option TraitDefinition :=
  match program.lookup id with | some (.trait declaration) => some declaration | _ => none
def Program.associated (program : Program) (id : DeclId) : Option AssociatedDefinition :=
  match program.lookup id with | some (.associated declaration) => some declaration | _ => none
def Program.function (program : Program) (id : DeclId) : Option FunctionDefinition :=
  match program.lookup id with | some (.function declaration) => some declaration | _ => none
def Program.operation (program : Program) (id : DeclId) : Option OperationDefinition :=
  match program.lookup id with | some (.operation declaration) => some declaration | _ => none
def Program.effect (program : Program) (id : DeclId) : Option EffectDefinition :=
  match program.lookup id with | some (.effect declaration) => some declaration | _ => none
def Program.constant (program : Program) (id : DeclId) : Option ConstantDefinition :=
  match program.lookup id with | some (.constant declaration) => some declaration | _ => none

def Program.Constructor (program : Program) (constructor : DeclId)
    (data : DataDefinition) (variant : VariantDefinition) : Prop :=
  program.data data.header.id = some data ∧ variant ∈ data.variants ∧ variant.header.id = constructor

def Program.Header (program : Program) (header : Header) : Prop :=
  (∃ declaration ∈ program.declarations, declaration.header = header) ∨
  (∃ data variant, program.Constructor header.id data variant ∧ variant.header = header) ∨
  (∃ data variant field, program.Constructor variant.header.id data variant ∧
    field ∈ variant.fields ∧ field.header = header)

def normalizedPackageName (name : String) : String :=
  String.ofList (name.toList.map (fun c => if c = '-' then '_' else c))

def Input.WellFormed (input : Input) : Prop :=
  (input.packages.map (·.id)).Nodup ∧ (input.files.map (·.id)).Nodup ∧
  (input.packages.map (fun package => normalizedPackageName package.name)).Nodup ∧
  (∀ package ∈ input.packages,
    Source.Identifier (normalizedPackageName package.name) ∧
    (∃ root ∈ input.files, root.id = package.root ∧ root.package = package.id) ∧
    (package.dependencies.map (fun dependency => normalizedPackageName dependency.1)).Nodup ∧
    (∀ dependency ∈ package.dependencies, ∃ target ∈ input.packages, target.id = dependency.2)) ∧
  input.target.Valid ∧ input.manifest.WellFormed input.target

inductive ImportSelection where
  | explicit (path : Source.Path) (name : String)
  | glob (path : Source.Path)
  deriving Repr, Inhabited

inductive SelectsImport : Source.Path → Source.ImportTree → ImportSelection → Prop where
  | named {prefixForm path rename name} :
      name = rename.getD (path.getLastD "") → path ≠ [] →
      SelectsImport prefixForm (.name path rename) (.explicit (prefixForm ++ path) name)
  | glob {prefixForm path} : SelectsImport prefixForm (.glob path) (.glob (prefixForm ++ path))
  | group {prefixForm path children child selection} : child ∈ children →
      SelectsImport (prefixForm ++ path) child selection → SelectsImport prefixForm (.group path children) selection

abbrev ResolutionChoice := ModuleId → Namespace → String → Header → Prop

/- Finite derivations are grounded in declarations. A proposed resolution
filters qualified uses, but cannot itself create a candidate. Selection and
ambiguity are defined outside this positive inductive fixed point. -/
mutual
  inductive NameCandidate (program : Program) (choice : ResolutionChoice) :
      ModuleId → Namespace → String → Nat → Header → Prop where
    | declaration {module nameSpace name header} : program.Header header →
        header.sourceVisible = true →
        header.module = module → header.nameSpace = nameSpace → header.name = name →
        NameCandidate program choice module nameSpace name 3 header
    | explicit {module nameSpace name imported path header} : Definition.import imported ∈ program.declarations →
        imported.header.module = module → imported.prelude = false →
        SelectsImport [] imported.tree (.explicit path name) → QualifiedAt program choice module nameSpace path header →
        Visible header module → NameCandidate program choice module nameSpace name 2 header
    | glob {module nameSpace name imported path target header rank} : Definition.import imported ∈ program.declarations →
        imported.header.module = module → imported.prelude = false → SelectsImport [] imported.tree (.glob path) →
        ModulePathAt program choice module path target →
        NameCandidate program choice target nameSpace name rank header → choice target nameSpace name header →
        Visible header module → NameCandidate program choice module nameSpace name 1 header
    | prelude {module nameSpace name imported path header package} : Definition.import imported ∈ program.declarations →
        imported.header.module = module → imported.prelude = true → package ∈ program.input.packages →
        package.id = module.package → package.noPrelude = false → package.noStd = false →
        SelectsImport [] imported.tree (.explicit path name) → QualifiedAt program choice module nameSpace path header →
        Visible header module → NameCandidate program choice module nameSpace name 0 header
    | preludeGlob {module nameSpace name imported path target header rank package} :
        Definition.import imported ∈ program.declarations → imported.header.module = module →
        imported.prelude = true → package ∈ program.input.packages → package.id = module.package →
        package.noPrelude = false → package.noStd = false → SelectsImport [] imported.tree (.glob path) →
        ModulePathAt program choice module path target →
        NameCandidate program choice target nameSpace name rank header → choice target nameSpace name header →
        Visible header module → NameCandidate program choice module nameSpace name 0 header
    | effectOperation {module name rank effectHeader effect operation} :
        NameCandidate program choice module .effect name rank effectHeader →
        program.effect effectHeader.id = some effect → operation.header.id ∈ effect.operations →
        program.operation operation.header.id = some operation → Visible operation.header module →
        NameCandidate program choice module .value operation.header.name rank operation.header

  inductive QualifiedAt (program : Program) (choice : ResolutionChoice) :
      ModuleId → Namespace → Source.Path → Header → Prop where
    | bare {module nameSpace name header rank} : NameCandidate program choice module nameSpace name rank header →
        choice module nameSpace name header → QualifiedAt program choice module nameSpace [name] header
    | member {module nameSpace prefixForm target name header rank} : ModulePathAt program choice module prefixForm target →
        NameCandidate program choice target nameSpace name rank header → choice target nameSpace name header →
        Visible header module → QualifiedAt program choice module nameSpace (prefixForm ++ [name]) header
    | inherent {module path dataHeader member header} : QualifiedAt program choice module .type path dataHeader →
        program.Header header → header.module.package = dataHeader.id.package →
        (∃ function, program.function header.id = some function ∧ function.owner = some dataHeader.id) →
        header.name = member → Visible header module →
        QualifiedAt program choice module header.nameSpace (path ++ [member]) header
    | operation {module path effectHeader effect operation name} : QualifiedAt program choice module .effect path effectHeader →
        program.effect effectHeader.id = some effect → operation.header.id ∈ effect.operations →
        program.operation operation.header.id = some operation → operation.header.name = name →
        Visible operation.header module → QualifiedAt program choice module .value (path ++ [name]) operation.header

  inductive ModulePathAt (program : Program) (choice : ResolutionChoice) : ModuleId → Source.Path → ModuleId → Prop where
    | self {module} : ModulePathAt program choice module ["self"] module
    | crate {module} : ModulePathAt program choice module ["crate"] ⟨module.package,[]⟩
    | parent {module prefixForm parent} : module.path = prefixForm ++ [parent] →
        ModulePathAt program choice module ["super"] ⟨module.package,prefixForm⟩
    | dependency {module package name id} : package ∈ program.input.packages → package.id = module.package →
        (name,id) ∈ package.dependencies → ModulePathAt program choice module [normalizedPackageName name] ⟨id,[]⟩
    | resolved {module path header child} : QualifiedAt program choice module .type path header →
        program.lookup header.id = some (.module child) → ModulePathAt program choice module path child.module
end

def SelectedCandidate (program : Program) (choice : ResolutionChoice)
    (module : ModuleId) (nameSpace : Namespace) (name : String) (header : Header) : Prop :=
  ∃ rank, NameCandidate program choice module nameSpace name rank header ∧
    (∀ otherRank other, NameCandidate program choice module nameSpace name otherRank other → otherRank ≤ rank) ∧
    (∀ other, NameCandidate program choice module nameSpace name rank other → other.id = header.id)

def ResolutionModel (program : Program) (choice : ResolutionChoice) : Prop :=
  ∀ module nameSpace name header,
    choice module nameSpace name header ↔ SelectedCandidate program choice module nameSpace name header

/-- There must be a grounded solution, and every solution must agree on the
selected declaration. An inconsistent or underdetermined import closure is not
permission to pick a source-order-dependent answer. -/
def Resolves (program : Program) (module : ModuleId) (nameSpace : Namespace)
    (name : String) (header : Header) : Prop :=
  (∃ choice, ResolutionModel program choice) ∧
    ∀ choice, ResolutionModel program choice → choice module nameSpace name header

def Qualified (program : Program) (module : ModuleId) (nameSpace : Namespace)
    (path : Source.Path) (header : Header) : Prop :=
  (∃ choice, ResolutionModel program choice) ∧
    ∀ choice, ResolutionModel program choice → QualifiedAt program choice module nameSpace path header

def ModulePath (program : Program) (module : ModuleId) (path : Source.Path) (target : ModuleId) : Prop :=
  (∃ choice, ResolutionModel program choice) ∧
    ∀ choice, ResolutionModel program choice → ModulePathAt program choice module path target

def SourceClosure (program : Program) : Prop :=
  program.input.WellFormed ∧
  (∀ definition ∈ program.declarations, ∃ package ∈ program.input.packages, package.id = definition.header.id.package) ∧
  (∀ module, Definition.module module ∈ program.declarations →
    ∃ file ∈ program.input.files, file.id = module.file ∧ file.package = module.module.package ∧
      (module.inline = true ∨ module.parent = none ∨ file.logicalPath = module.directory ++ [module.header.name ++ ".glorious"])) ∧
  (∀ file ∈ program.input.files, ∃ module, Definition.module module ∈ program.declarations ∧ module.file = file.id) ∧
  (∀ module, Definition.module module ∈ program.declarations → module.parent = none →
    module.module.path = [] ∧ ∃ package ∈ program.input.packages, package.id = module.module.package ∧ package.root = module.file)

theorem resolution_identity_unique {program : Program} {module nameSpace name left right}
    (a : Resolves program module nameSpace name left) (b : Resolves program module nameSpace name right) :
    left.id = right.id := by
  obtain ⟨choice, model⟩ := a.1
  obtain ⟨rank, candidate, maximum, unique⟩ := (model _ _ _ _).mp (a.2 choice model)
  obtain ⟨rank', candidate', maximum', _⟩ := (model _ _ _ _).mp (b.2 choice model)
  have ranks := Nat.le_antisymm (maximum _ _ candidate') (maximum' _ _ candidate)
  subst rank'
  exact (unique _ candidate').symm

end Glorious.Language
