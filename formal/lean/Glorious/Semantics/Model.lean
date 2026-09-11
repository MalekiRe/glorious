import Glorious.Effects

/-! The shared, name-independent semantic vocabulary. All later phases consume
    these identities and terms; spelling is retained only for resolution and
    diagnostics. `Term` is kinded by `kindOf`, not by a second syntax tree. -/
namespace Glorious.Semantics

abbrev Id := Nat

structure Span where
  file : Id := 0
  start : Nat := 0
  stop : Nat := 0
  deriving BEq, DecidableEq, Repr, Inhabited

inductive Problem where
  | invalidSource | ambiguous | unknownName | privacy | duplicate
  | kindMismatch | typeMismatch | occursCheck | universeLeak
  | coherence | missingEvidence | recursiveNormalization | resourceLimit
  | uninitialized | moved | duplicateOwner | illegalCopy | illegalDiscard
  | loanConflict | loanHole | escapingReference | escapingBrand | openAvailability
  | missingEffect | invalidResumption | replay | cancellation | tail
  | unsafeOperation | invalidLayout | invalidScalar | invalidPointer
  | incompatibleABI | missingImport | malformedCore | unsupportedContract
  deriving BEq, DecidableEq, Repr, Inhabited

structure Diagnostic where
  problem : Problem
  span : Span := {}
  message : String
  related : List Span := []
  deriving Repr, Inhabited

abbrev Check := Except Diagnostic

def reject (problem : Problem) (message : String) (span : Span := {}) : Check α :=
  .error ⟨problem, span, message, []⟩

def require (condition : Bool) (problem : Problem) (message : String)
    (span : Span := {}) : Check Unit :=
  if condition then .ok () else reject problem message span

def getRequired (value : Option α) (problem : Problem) (message : String)
    (span : Span := {}) : Check α :=
  match value with | some value => .ok value | none => reject problem message span

def lookup [BEq κ] (key : κ) (entries : List (κ × α)) : Option α :=
  (entries.find? (fun entry => entry.1 == key)).map Prod.snd

def put [BEq κ] (key : κ) (value : α) (entries : List (κ × α)) : List (κ × α) :=
  (key, value) :: entries.filter (fun entry => entry.1 != key)

def unique [BEq α] (values : List α) : Bool :=
  values.length == values.eraseDups.length

inductive Kind where
  | type | region | constant | effect | row | brand
  deriving BEq, DecidableEq, Repr, Inhabited

inductive Mutability where
  | shared | unique
  deriving BEq, DecidableEq, Repr, Inhabited

inductive IntWidth where
  | w8 | w16 | w32 | w64 | w128 | pointer
  deriving BEq, DecidableEq, Repr, Inhabited

inductive FloatWidth where
  | w32 | w64
  deriving BEq, DecidableEq, Repr, Inhabited

inductive ScalarType where
  | integer (signed : Bool) (width : IntWidth)
  | floating (width : FloatWidth)
  | character
  deriving BEq, DecidableEq, Repr, Inhabited

inductive ScalarValue where
  | integer (signed : Bool) (width : IntWidth) (value : Int)
  | floating (width : FloatWidth) (bits : Nat)
  | character (value : Nat)
  deriving BEq, DecidableEq, Repr, Inhabited

inductive Term where
  | param (id : Id) (kind : Kind)
  | «meta» (id : Id) (kind : Kind) (level : Nat)
  | rigid (id : Id) (kind : Kind) (level : Nat)
  | unit | bottom
  | scalar (type : ScalarType)
  | tuple (fields : List Term)
  | array (element length : Term)
  | reference (mode : Mutability) (region referent : Term)
  | rawPointer (mode : Mutability) (referent : Term)
  | named (path : List String) (arguments : List Term) (kind : Kind)
  | nominal (declaration : DeclId) (arguments : List Term)
  | alias (declaration : DeclId) (arguments : List Term)
  | callable (declaration : DeclId) (arguments : List Term)
  | continuation (identity : Id) (argument result effects : Term)
  | label (brand region result : Term)
  | environment (brand region : Term)
  | available (brand region : Term)
  | bindings (brand region : Term) (arguments : List Term)
  | effect (declaration : DeclId) (arguments : List Term)
  | row (instances tails : List Term)
  | projection (traitDecl member : DeclId) (arguments : List Term) (kind : Kind)
  | constant (value : ScalarValue)
  | constantTuple (values : List Term)
  | constantConstructor (declaration : DeclId) (arguments fields : List Term)
  | staticRegion
  deriving BEq, Repr, Inhabited

def Term.kind : Term → Kind
  | .param _ k | .meta _ k _ | .rigid _ k _ | .projection _ _ _ k | .named _ _ k => k
  | .staticRegion => .region
  | .effect .. => .effect
  | .row .. => .row
  | .constant .. | .constantTuple .. | .constantConstructor .. => .constant
  | _ => .type

def Term.children : Term → List Term
  | .tuple xs | .constantTuple xs => xs
  | .array a b | .reference _ a b | .environment a b | .available a b => [a, b]
  | .rawPointer _ a => [a]
  | .nominal _ xs | .alias _ xs | .callable _ xs | .effect _ xs | .projection _ _ xs _ | .named _ xs _ => xs
  | .continuation _ a b e | .label a b e => [a, b, e]
  | .bindings a b xs => a :: b :: xs
  | .row xs ys | .constantConstructor _ xs ys => xs ++ ys
  | _ => []

def Term.mapChildren (f : Term → Term) : Term → Term
  | .tuple xs => .tuple (xs.map f)
  | .array a b => .array (f a) (f b)
  | .reference m a b => .reference m (f a) (f b)
  | .rawPointer m a => .rawPointer m (f a)
  | .named p xs k => .named p (xs.map f) k
  | .nominal d xs => .nominal d (xs.map f)
  | .alias d xs => .alias d (xs.map f)
  | .callable d xs => .callable d (xs.map f)
  | .continuation id a b e => .continuation id (f a) (f b) (f e)
  | .label a b c => .label (f a) (f b) (f c)
  | .environment a b => .environment (f a) (f b)
  | .available a b => .available (f a) (f b)
  | .bindings a b xs => .bindings (f a) (f b) (xs.map f)
  | .effect d xs => .effect d (xs.map f)
  | .row xs ys => .row (xs.map f) (ys.map f)
  | .projection d m xs k => .projection d m (xs.map f) k
  | .constantTuple xs => .constantTuple (xs.map f)
  | .constantConstructor d xs ys => .constantConstructor d (xs.map f) (ys.map f)
  | t => t

def Term.mapChildrenM (f : Term → Check Term) : Term → Check Term
  | .tuple xs => return .tuple (← xs.mapM f)
  | .array a b => return .array (← f a) (← f b)
  | .reference m a b => return .reference m (← f a) (← f b)
  | .rawPointer m a => return .rawPointer m (← f a)
  | .named p xs k => return .named p (← xs.mapM f) k
  | .nominal d xs => return .nominal d (← xs.mapM f)
  | .alias d xs => return .alias d (← xs.mapM f)
  | .callable d xs => return .callable d (← xs.mapM f)
  | .continuation id a b e => return .continuation id (← f a) (← f b) (← f e)
  | .label a b c => return .label (← f a) (← f b) (← f c)
  | .environment a b => return .environment (← f a) (← f b)
  | .available a b => return .available (← f a) (← f b)
  | .bindings a b xs => return .bindings (← f a) (← f b) (← xs.mapM f)
  | .effect d xs => return .effect d (← xs.mapM f)
  | .row xs ys => return .row (← xs.mapM f) (← ys.mapM f)
  | .projection d m xs k => return .projection d m (← xs.mapM f) k
  | .constantTuple xs => return .constantTuple (← xs.mapM f)
  | .constantConstructor d xs ys => return .constantConstructor d (← xs.mapM f) (← ys.mapM f)
  | t => return t

def Term.any (fuel : Nat) (predicate : Term → Bool) (term : Term) : Bool :=
  match fuel with
  | 0 => true -- conservative query: exhausted traversal cannot prove absence
  | n + 1 => predicate term || term.children.any (Term.any n predicate)

def closedTerm (fuel : Nat) (term : Term) : Bool :=
  !(term.any fuel (fun t => match t with | .param .. | .meta .. | .projection .. | .alias .. | .named .. => true | _ => false))

structure Binder where
  id : Id
  name : String
  kind : Kind
  defaultValue : Option Term := none
  deriving Repr, Inhabited

inductive Constraint where
  | named (path : List String) (arguments : List Term) (negative : Bool := false)
  | equal (left right : Term)
  | outlives (long short : Term)
  | rowIncludes (allowed required : Term)
  | implements (traitDecl : DeclId) (arguments : List Term) (negative : Bool := false)
  | use (type : Term) (quantity : Quantity)
  | callable (receiver arguments output effects : Term) (unsafeAllowed : Bool)
  | runsIn (receiver access arguments after : Term) (unsafeAllowed : Bool)
  | higherRanked (binders : List Binder) (obligations : List Constraint)
  deriving Repr, Inhabited

inductive Namespace where
  | type | value | trait | effect | region | label
  deriving BEq, DecidableEq, Repr, Inhabited

structure ModuleId where
  packageId : Id
  path : List String
  deriving BEq, DecidableEq, Repr, Inhabited

inductive Visibility where
  | «private» | «public» | package | parent
  deriving BEq, DecidableEq, Repr, Inhabited

structure Path where
  components : List String
  deriving BEq, DecidableEq, Repr, Inhabited

structure DeclHeader where
  id : DeclId
  module : ModuleId
  name : String
  visibility : Visibility := .private
  span : Span := {}
  deriving Repr

structure FieldDecl where
  header : DeclHeader
  type : Term
  deriving Repr

structure VariantDecl where
  header : DeclHeader
  fields : List FieldDecl
  deriving Repr

inductive Representation where
  | glorious | c | transparent | integer (signed : Bool) (width : IntWidth)
  deriving BEq, DecidableEq, Repr, Inhabited

structure DataDecl where
  header : DeclHeader
  generics : List Binder := []
  variants : List VariantDecl
  isEnum : Bool
  nonExhaustive : Bool := false
  representation : Representation := .glorious
  principalRestriction : Option Principal := none
  quantityMarker : Option Term := none
  dropHook : Option DeclId := none
  invariantContract : Option DeclId := none
  deriving Repr

structure AliasDecl where
  header : DeclHeader
  generics : List Binder
  value : Term
  deriving Repr

inductive ReceiverMode where
  | shared | unique | owned
  deriving BEq, DecidableEq, Repr, Inhabited

inductive ABI where
  | glorious | c
  deriving BEq, DecidableEq, Repr, Inhabited

structure Signature where
  generics : List Binder := []
  arguments : List Term
  output : Term := .unit
  effects : Term := .row [] []
  constraints : List Constraint := []
  unsafeCall : Bool := false
  abi : ABI := .glorious
  receiver : Option ReceiverMode := none
  deriving Repr, Inhabited

structure TraitMember where
  header : DeclHeader
  generics : List Binder := []
  kind : Kind
  defaultValue : Option Term := none
  signature : Option Signature := none
  deriving Repr

structure TraitDecl where
  header : DeclHeader
  generics : List Binder
  supertraits : List Constraint
  members : List TraitMember
  sealed : Bool := false
  unsafeContract : Bool := false
  deriving Repr

structure ImplDecl where
  header : DeclHeader
  generics : List Binder
  traitDecl : DeclId
  arguments : List Term
  requirements : List Constraint
  associated : List (DeclId × Term)
  methods : List (DeclId × DeclId)
  negative : Bool := false
  unsafeImpl : Bool := false
  traitPath : Option Path := none
  deriving Repr

structure OperationDecl where
  header : DeclHeader
  signature : Signature
  quantity : Option (Nat × Option Nat) := none
  deriving Repr

structure EffectDecl where
  header : DeclHeader
  generics : List Binder
  requirements : List Constraint := []
  operations : List OperationDecl
  deriving Repr

inductive Projection where
  | field (index : Nat)
  | variant (declaration : DeclId)
  | index (constant : Nat)
  | dynamicIndex (value : Id)
  | dereference
  deriving BEq, DecidableEq, Repr, Inhabited

structure Place where
  root : Id
  projections : List Projection := []
  deriving BEq, DecidableEq, Repr, Inhabited

inductive Pattern where
  | wildcard
  | binder (id : Id) (name : String) (forced : Bool := false)
  | constant (value : Term)
  | tuple (fields : List Pattern)
  | array (before after : List Pattern) (rest : Option Id)
  | constructor (declaration : DeclId) (fields : List (Nat × Pattern)) (rest : Bool)
  | named (path : Path) (fields : List Pattern)
  | record (path : Path) (fields : List (String × Pattern)) (rest : Bool)
  | reference (mode : Mutability) (pattern : Pattern)
  deriving Repr, Inhabited

inductive CaptureMode where
  | shared | unique | owned
  deriving BEq, DecidableEq, Repr, Inhabited

structure Capture where
  source : Place
  mode : CaptureMode
  parameter : Id
  type : Term
  deriving Repr

inductive Literal where
  | integer (magnitude : Nat) (suffix : Option ScalarType) (directlyNegated : Bool := false)
  | decimalFloat (sign : Bool) (significand : Nat) (decimalExponent : Int)
      (width : Option FloatWidth)
  | character (scalar : Nat)
  | text (bytes : List UInt8)
  | bytes (bytes : List UInt8)
  deriving Repr, Inhabited

structure Parameter where
  id : Id
  name : String
  type : Option Term
  mutable : Bool := false
  deriving Repr, Inhabited

mutual
  inductive Expr where
    | unit (span : Span)
    | literal (span : Span) (literal : Literal)
    | name (span : Span) (path : Path) (arguments : List Term)
    | «local» (span : Span) (id : Id)
    | tuple (span : Span) (fields : List Expr)
    | array (span : Span) (fields : List Expr)
    | construct (span : Span) (declaration : DeclId) (arguments : List Term)
        (fields : List (Nat × Expr))
    | record (span : Span) (path : Path) (arguments : List Term) (fields : List (String × Expr))
    | project (span : Span) (value : Expr) (projection : Projection)
    | block (span : Span) (statements : List Statement) (result : Option Expr)
    | apply (span : Span) (callee : Expr) (arguments : List Expr)
    | tail (span : Span) (callee : Expr) (arguments : List Expr)
    | lambda (span : Span) (identity : DeclId) (parameters : List Parameter)
        (output effects : Option Term) (body : Expr) (assertedMoves : List Place)
    | patternCallable (span : Span) (identity : DeclId) (clauses : List PatternClause)
    | borrow (span : Span) (mode : Mutability) (value : Expr)
    | move (span : Span) (value : Expr)
    | test (span : Span) (value : Expr) (pattern : Pattern)
    | label (span : Span) (identity : Id) (name : String) (output : Option Term) (body : Expr)
    | handle (span : Span) (body : Expr) (clauses : List HandlerClause)
    | unsafeScope (span : Span) (body : Expr)
    | operatorChain (span : Span) (parts : List ChainPart)
    deriving Repr

  inductive Statement where
    | binding (span : Span) (pattern : Pattern) (mutable : Bool)
        (annotation : Option Term) (initializer : Expr)
    | assign (span : Span) (destination value : Expr)
    | discard (span : Span) (value : Expr)
    deriving Repr

  inductive PatternClause where
    | clause (span : Span) (pattern : Pattern) (body : Expr)
    deriving Repr

  inductive HandlerClause where
    | completion (span : Span) (pattern : Pattern) (body : Expr)
    | operation (span : Span) (operation : DeclId) (effectArgs : List Term)
        (patterns : List Pattern) (continuation : Option Parameter) (body : Expr)
    deriving Repr

  inductive ChainPart where
    | operand (value : Expr)
    | operator (spelling : String) (span : Span)
    deriving Repr
end

def Expr.span : Expr → Span
  | .unit s | .literal s .. | .name s .. | .local s .. | .tuple s .. | .array s ..
  | .construct s .. | .record s .. | .project s .. | .block s .. | .apply s .. | .tail s ..
  | .lambda s .. | .patternCallable s .. | .borrow s .. | .move s .. | .test s ..
  | .label s .. | .handle s .. | .unsafeScope s .. | .operatorChain s .. => s

structure FunctionDecl where
  header : DeclHeader
  signature : Signature
  parameters : List Parameter
  body : Option Expr
  runtimeBinding : Option DeclId := none
  exportName : Option String := none
  owner : Option Term := none
  traitMember : Option DeclId := none
  deriving Repr

structure ConstDecl where
  header : DeclHeader
  generics : List Binder := []
  type : Term
  value : Term
  runtimeGlobal : Bool := false
  deriving Repr

inductive Associativity where
  | left | right | none | «prefix»
  deriving BEq, DecidableEq, Repr, Inhabited

structure Fixity where
  module : ModuleId
  spelling : String
  associativity : Associativity
  precedence : Nat
  target : DeclId
  span : Span := {}
  targetPath : Option Path := none
  deriving Repr

structure Import where
  module : ModuleId
  source : Path
  «namespace» : Namespace
  aliasName : Option String := none
  glob : Bool := false
  prelude : Bool := false
  «public» : Bool := false
  includeOperations : Bool := false
  span : Span := {}
  deriving Repr

structure ModuleDecl where
  identity : ModuleId
  children : List ModuleId
  imports : List Import
  noImplicitPrelude : Bool := false
  deriving Repr

structure Target where
  triple : String
  pointerBits : Nat
  littleEndian : Bool
  scalarAlignments : List (ScalarType × Nat)
  maxObjectSize : Nat
  abiGeneration : Nat
  layoutIdentity : String
  callableConvention : Nat
  intrinsicManifest : String
  cEnabled : Bool := false
  deriving BEq, Repr

inductive LeafKind where
  | scalar | memory | layout | staticData | host | foreign
  deriving BEq, DecidableEq, Repr, Inhabited

structure RuntimeImport where
  identity : DeclId
  signature : Signature
  kind : LeafKind
  capability : Option String
  allocationDomain : Option Id
  retainedCallback : Bool := false
  replayable : Bool := false
  symbol : String := ""
  primitive : Option String := none
  deriving Repr

structure Limits where
  normalization : Nat := 2048
  solving : Nat := 4096
  elaboration : Nat := 16384
  analysis : Nat := 16384
  alternatives : Nat := 4096
  layout : Nat := 1024
  execution : Nat := 100000
  deriving Repr

structure Package where
  id : Id
  name : String
  dependencies : List Id
  root : ModuleId
  deriving Repr

structure Program where
  packages : List Package
  modules : List ModuleDecl
  dataTypes : List DataDecl
  aliases : List AliasDecl
  traits : List TraitDecl
  implementations : List ImplDecl
  effects : List EffectDecl
  functions : List FunctionDecl
  constants : List ConstDecl
  fixities : List Fixity
  target : Target
  imports : List RuntimeImport
  grantedCapabilities : List String
  limits : Limits := {}
  deriving Repr

def Program.function (program : Program) (id : DeclId) : Option FunctionDecl :=
  program.functions.find? (fun f => f.header.id == id)

def Program.dataType (program : Program) (id : DeclId) : Option DataDecl :=
  program.dataTypes.find? (fun d => d.header.id == id)

def Program.operation (program : Program) (id : DeclId) : Option (EffectDecl × OperationDecl) :=
  program.effects.findSome? (fun e => (e.operations.find? (fun op => op.header.id == id)).map (e, ·))

def Program.constructor (program : Program) (id : DeclId) : Option (DataDecl × VariantDecl) :=
  program.dataTypes.findSome? (fun d => (d.variants.find? (fun v => v.header.id == id)).map (d, ·))

def Program.traitDecl (program : Program) (id : DeclId) : Option TraitDecl :=
  program.traits.find? (fun t => t.header.id == id)

end Glorious.Semantics
