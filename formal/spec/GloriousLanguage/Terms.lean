import GloriousLanguage.Foundation

/-! Kinded semantic terms. Declaration identities, generic binders, generative
brands, storage owners, and inference cells are not interchangeable identities. -/
namespace Glorious.Language

inductive Kind where
  | type | region | constant | effect | row | brand | quantity
  deriving DecidableEq, BEq, Repr, Inhabited

inductive Width where
  | fixed (bits : Nat) | pointer
  deriving DecidableEq, BEq, Repr, Inhabited

inductive FloatWidth where
  | single | double
  deriving DecidableEq, BEq, Repr, Inhabited

inductive Scalar where
  | integer (signed : Bool) (width : Width)
  | floating (width : FloatWidth)
  | character
  deriving DecidableEq, BEq, Repr, Inhabited

inductive ScalarValue where
  | integer (signed : Bool) (width : Width) (value : Int)
  | floating (width : FloatWidth) (bits : Nat)
  | character (scalar : Nat)
  deriving DecidableEq, BEq, Repr, Inhabited

def ScalarValue.type : ScalarValue → Scalar
  | .integer sign width _ => .integer sign width
  | .floating width _ => .floating width
  | .character _ => .character

inductive Term where
  | parameter (binder : Identity) (kind : Kind)
  | variable (cell : Identity) (kind : Kind) (universe : Nat)
  | rigid (binder : Identity) (kind : Kind) (universe : Nat)
  | unit | bottom | scalar (type : Scalar)
  | tuple (fields : List Term)
  | array (element length : Term)
  | reference (mode : Mutability) (region referent : Term)
  | rawPointer (mode : Mutability) (referent : Term)
  | nominal (declaration : DeclId) (arguments : List Term)
  | alias (declaration : DeclId) (arguments : List Term)
  | callable (declaration : DeclId) (arguments : List Term)
  | continuation (brand argument answer effects : Term) (quantity : Quantity)
  | label (brand region result : Term)
  | environment (brand region : Term)
  | available (brand region : Term)
  | bindings (brand region : Term) (arguments : List Term)
  | effect (declaration : DeclId) (arguments : List Term)
  | row (instances tails : List Term)
  | projection (traitDecl member : DeclId) (ownerArguments itemArguments : List Term) (kind : Kind)
  | constant (value : ScalarValue)
  | constantTuple (fields : List Term)
  | constantConstructor (declaration : DeclId) (arguments fields : List Term)
  | principal (value : Principal)
  | quantity (value : Quantity)
  | staticRegion
  deriving BEq, Repr, Inhabited

def Term.kind : Term → Kind
  | .parameter _ k | .variable _ k _ | .rigid _ k _ | .projection _ _ _ _ k => k
  | .staticRegion => .region
  | .effect .. => .effect
  | .row .. => .row
  | .constant .. | .constantTuple .. | .constantConstructor .. => .constant
  | .principal .. | .quantity .. => .quantity
  | _ => .type

def Term.children : Term → List Term
  | .tuple fields | .constantTuple fields => fields
  | .array a b | .reference _ a b | .environment a b | .available a b => [a, b]
  | .rawPointer _ a => [a]
  | .nominal _ xs | .alias _ xs | .callable _ xs | .effect _ xs => xs
  | .continuation a b c d _ => [a, b, c, d]
  | .label a b c => [a, b, c]
  | .bindings a b xs => a :: b :: xs
  | .row xs ys | .projection _ _ xs ys _ | .constantConstructor _ xs ys => xs ++ ys
  | _ => []

def Term.mapChildren (f : Term → Term) : Term → Term
  | .tuple xs => .tuple (xs.map f)
  | .array a b => .array (f a) (f b)
  | .reference m a b => .reference m (f a) (f b)
  | .rawPointer m a => .rawPointer m (f a)
  | .nominal d xs => .nominal d (xs.map f)
  | .alias d xs => .alias d (xs.map f)
  | .callable d xs => .callable d (xs.map f)
  | .continuation a b c d q => .continuation (f a) (f b) (f c) (f d) q
  | .label a b c => .label (f a) (f b) (f c)
  | .environment a b => .environment (f a) (f b)
  | .available a b => .available (f a) (f b)
  | .bindings a b xs => .bindings (f a) (f b) (xs.map f)
  | .effect d xs => .effect d (xs.map f)
  | .row xs ys => .row (xs.map f) (ys.map f)
  | .projection d m xs ys k => .projection d m (xs.map f) (ys.map f) k
  | .constantTuple xs => .constantTuple (xs.map f)
  | .constantConstructor d xs ys => .constantConstructor d (xs.map f) (ys.map f)
  | term => term

def SameHead (a b : Term) : Prop := a.mapChildren (fun _ => .unit) = b.mapChildren (fun _ => .unit)

inductive Occurs : Term → Term → Prop where
  | here {term} : Occurs term term
  | child {needle parent child} : child ∈ parent.children → Occurs needle child → Occurs needle parent

abbrev Substitution := Table Term

inductive Substitutes (substitution : Substitution) : Term → Term → Prop where
  | selected {id kind value} : substitution.get id = some value → value.kind = kind →
      Substitutes substitution (.parameter id kind) value
  | free {id kind} : substitution.get id = none →
      Substitutes substitution (.parameter id kind) (.parameter id kind)
  | node {a b} : (∀ id kind, a ≠ .parameter id kind) → SameHead a b →
      ListRel (Substitutes substitution) a.children b.children → Substitutes substitution a b

structure Binder where
  id : Identity
  name : String
  kind : Kind
  defaultValue : Option Term := none
  deriving Repr, Inhabited

def Instantiates (binders : List Binder) (arguments : List Term) (substitution : Substitution) : Prop :=
  (binders.map (·.id)).Nodup ∧
  ListRel (fun binder term => binder.kind = term.kind) binders arguments ∧
  substitution = (binders.map (·.id)).zip arguments

inductive Constraint where
  | equal (left right : Term)
  | outlives (long short : Term)
  | typeOutlives (type region : Term)
  | rowIncludes (allowed required : Term)
  | implements (trait : DeclId) (arguments : List Term) (negative : Bool)
  | use (type : Term) (quantity : Quantity)
  | callable (receiver : Term) (arguments : List Term) (output effects : Term) (unsafeAllowed : Bool)
  | runsIn (receiver access : Term) (arguments : List Term) (after : Term) (unsafeAllowed : Bool)
  | quantified (binders : List Binder) (requirements : List Constraint)
  deriving Repr, Inhabited

structure Signature where
  generics : List Binder := []
  parameters : List Term
  result : Term
  effects : Term := .row [] []
  constraints : List Constraint := []
  unsafe : Bool := false
  deriving Repr, Inhabited

inductive Visibility where
  | private | public | package | parent
  deriving DecidableEq, BEq, Repr, Inhabited

inductive Namespace where
  | type | value | trait | effect | region | label | parameter
  deriving DecidableEq, BEq, Repr, Inhabited

structure Header where
  id : DeclId
  module : ModuleId
  name : String
  namespace : Namespace
  visibility : Visibility
  span : Span
  sourceVisible : Bool := true
  deriving Repr, Inhabited

def Descendant (child parent : ModuleId) : Prop :=
  child.package = parent.package ∧ ∃ suffix, child.path = parent.path ++ suffix

def Visible (header : Header) (requester : ModuleId) : Prop :=
  match header.visibility with
  | .public => True
  | .package => requester.package = header.module.package
  | .private => Descendant requester header.module
  | .parent => Descendant requester { header.module with path := header.module.path.dropLast }

inductive RegionIncludes (assumptions : List Constraint) : Term → Term → Prop where
  | refl {region} : RegionIncludes assumptions region region
  | static {region} : RegionIncludes assumptions .staticRegion region
  | assumed {a b} : Constraint.outlives a b ∈ assumptions → RegionIncludes assumptions a b
  | trans {a b c} : RegionIncludes assumptions a b → RegionIncludes assumptions b c →
      RegionIncludes assumptions a c

def NoLeak (universe : Nat) (term : Term) : Prop :=
  ∀ id kind level, Occurs (.rigid id kind level) term → level ≤ universe

def Resolved (term : Term) : Prop :=
  (∀ id kind level, ¬ Occurs (.variable id kind level) term) ∧
  (∀ declaration arguments, ¬ Occurs (.alias declaration arguments) term) ∧
  (∀ trait member owner item kind, ¬ Occurs (.projection trait member owner item kind) term)

def Closed (term : Term) : Prop := Resolved term ∧
  (∀ id kind, ¬ Occurs (.parameter id kind) term) ∧
  (∀ id kind level, ¬ Occurs (.rigid id kind level) term)

theorem sameHead_kind {a b : Term} (same : SameHead a b) : a.kind = b.kind := by
  have preserves (f : Term → Term) (term : Term) : (term.mapChildren f).kind = term.kind := by
    cases term <;> rfl
  have kinds := congrArg Term.kind same
  simpa only [preserves] using kinds

theorem substitution_kind {substitution : Substitution} {a b : Term}
    (proof : Substitutes substitution a b) : a.kind = b.kind := by
  cases proof with
  | selected _ kinded => exact kinded.symm
  | free _ => rfl
  | node _ same _ => exact sameHead_kind same

end Glorious.Language
