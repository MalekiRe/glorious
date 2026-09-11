import GloriousLanguage.Target

/-! One declaration inventory, supplied source closure, and least-fixed-point
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
  unsafe : Bool
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
  unsafe : Bool
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
  unsafe : Bool
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

structure EnvironmentDefinition where
  header : Header
  brand : Term
  region : Term
  residents : List Term
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
  | environment (value : EnvironmentDefinition)
  deriving Repr, Inhabited

def Definition.header : Definition → Header
  | .data d => d.header | .alias d => d.header | .trait d => d.header
  | .associated d => d.header | .implementation d => d.header | .function d => d.header
  | .operation d => d.header | .effect d => d.header | .constant d => d.header
  | .global d => d.header | .module d => d.header | .import d => d.header | .fixity d => d.header
  | .environment d => d.header

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
  | named {prefix path rename name} :
      name = rename.getD (path.getLastD "") → path ≠ [] →
      SelectsImport prefix (.name path rename) (.explicit (prefix ++ path) name)
  | glob {prefix path} : SelectsImport prefix (.glob path) (.glob (prefix ++ path))
  | group {prefix path children child selection} : child ∈ children →
      SelectsImport (prefix ++ path) child selection → SelectsImport prefix (.group path children) selection

/-- Candidate provenance carries precedence but never argument types. Benign
import cycles can have finite derivations from a real declaration; a cycle
with no such base does not create a name. -/
mutual
  inductive NameCandidate (program : Program) : ModuleId → Namespace → String → Nat → Header → Prop where
    | declaration {module namespace name header} : program.Header header →
        header.sourceVisible = true →
        header.module = module → header.namespace = namespace → header.name = name →
        NameCandidate program module namespace name 3 header
    | explicit {module namespace name import path header} : Definition.import import ∈ program.declarations →
        import.header.module = module → import.prelude = false →
        SelectsImport [] import.tree (.explicit path name) → Qualified program module namespace path header →
        Visible header module → NameCandidate program module namespace name 2 header
    | glob {module namespace name import path target header rank} : Definition.import import ∈ program.declarations →
        import.header.module = module → import.prelude = false → SelectsImport [] import.tree (.glob path) →
        ModulePath program module path target → NameCandidate program target namespace name rank header →
        Visible header module → NameCandidate program module namespace name 1 header
    | prelude {module namespace name import path header package} : Definition.import import ∈ program.declarations →
        import.header.module = module → import.prelude = true → package ∈ program.input.packages →
        package.id = module.package → package.noPrelude = false →
        SelectsImport [] import.tree (.explicit path name) → Qualified program module namespace path header →
        Visible header module → NameCandidate program module namespace name 0 header
    | effectOperation {module name rank effectHeader effect operation} :
        NameCandidate program module .effect name rank effectHeader →
        program.effect effectHeader.id = some effect → operation.header.id ∈ effect.operations →
        program.operation operation.header.id = some operation → Visible operation.header module →
        NameCandidate program module .value operation.header.name rank operation.header

  inductive Resolves (program : Program) : ModuleId → Namespace → String → Header → Prop where
    | selected {module namespace name rank header} : NameCandidate program module namespace name rank header →
        (∀ otherRank other, NameCandidate program module namespace name otherRank other → otherRank ≤ rank) →
        (∀ other, NameCandidate program module namespace name rank other → other.id = header.id) →
        Resolves program module namespace name header

  inductive Qualified (program : Program) : ModuleId → Namespace → Source.Path → Header → Prop where
    | bare {module namespace name header} : Resolves program module namespace name header →
        Qualified program module namespace [name] header
    | member {module namespace prefix target name header} : ModulePath program module prefix target →
        Resolves program target namespace name header → Visible header module →
        Qualified program module namespace (prefix ++ [name]) header
    | inherent {module path dataHeader member header} : Qualified program module .type path dataHeader →
        program.Header header → header.module.package = dataHeader.id.package →
        (∃ function, program.function header.id = some function ∧ function.owner = some dataHeader.id) →
        header.name = member → Visible header module →
        Qualified program module header.namespace (path ++ [member]) header
    | operation {module path effectHeader effect operation name} : Qualified program module .effect path effectHeader →
        program.effect effectHeader.id = some effect → operation.header.id ∈ effect.operations →
        program.operation operation.header.id = some operation → operation.header.name = name →
        Visible operation.header module → Qualified program module .value (path ++ [name]) operation.header

  inductive ModulePath (program : Program) : ModuleId → Source.Path → ModuleId → Prop where
    | self {module} : ModulePath program module ["self"] module
    | crate {module} : ModulePath program module ["crate"] ⟨module.package,[]⟩
    | parent {module prefix parent} : module.path = prefix ++ [parent] →
        ModulePath program module ["super"] ⟨module.package,prefix⟩
    | dependency {module package name id} : package ∈ program.input.packages → package.id = module.package →
        (name,id) ∈ package.dependencies → ModulePath program module [normalizedPackageName name] ⟨id,[]⟩
    | local {module name child} : Definition.module child ∈ program.declarations → child.parent = some module →
        child.header.name = name → Visible child.header module → ModulePath program module [name] child.module
    | descend {module prefix parent name child} : ModulePath program module prefix parent →
        Definition.module child ∈ program.declarations → child.parent = some parent → child.header.name = name →
        Visible child.header module → ModulePath program module (prefix ++ [name]) child.module
end

def SourceClosure (program : Program) : Prop :=
  program.input.WellFormed ∧
  (∀ definition ∈ program.declarations, ∃ package ∈ program.input.packages, package.id = definition.header.id.package) ∧
  (∀ module, Definition.module module ∈ program.declarations →
    ∃ file ∈ program.input.files, file.id = module.file ∧ file.package = module.module.package ∧
      (module.inline = true ∨ module.parent = none ∨ file.logicalPath = module.directory ++ [module.header.name ++ ".glorious"])) ∧
  (∀ file ∈ program.input.files, ∃ module, Definition.module module ∈ program.declarations ∧ module.file = file.id) ∧
  (∀ module, Definition.module module ∈ program.declarations → module.parent = none →
    module.module.path = [] ∧ ∃ package ∈ program.input.packages, package.id = module.module.package ∧ package.root = module.file)

theorem resolution_identity_unique {program : Program} {module namespace name left right}
    (a : Resolves program module namespace name left) (b : Resolves program module namespace name right) :
    left.id = right.id := by
  cases a with
  | selected candidate maximum unique =>
    cases b with
    | selected candidate' maximum' unique' =>
      have ranks := Nat.le_antisymm (maximum _ _ candidate') (maximum' _ _ candidate)
      subst ranks
      exact (unique _ candidate').symm

end Glorious.Language
