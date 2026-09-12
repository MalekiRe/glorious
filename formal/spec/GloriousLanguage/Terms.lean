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

inductive RuntimeBrand where
  | label (identity : Identity)
  | resumption (identity : Identity)
  | proof (identity : Identity)
  deriving DecidableEq, BEq, Repr, Inhabited

inductive Term where
  | parameter (binder : Identity) (kind : Kind)
  | variable (cell : Identity) (kind : Kind) (universeLevel : Nat)
  | rigid (binder : Identity) (kind : Kind) (universeLevel : Nat)
  | runtimeRegion (identity : Identity)
  | runtimeBrand (identity : RuntimeBrand)
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
  | environment (brand region : Term) (residents : List Term)
  | available (brand region : Term) (residents : List Term)
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
  | .staticRegion | .runtimeRegion _ => .region
  | .runtimeBrand _ => .brand
  | .effect .. => .effect
  | .row .. => .row
  | .constant .. | .constantTuple .. | .constantConstructor .. => .constant
  | .principal .. | .quantity .. => .quantity
  | _ => .type

def Term.children : Term → List Term
  | .tuple fields | .constantTuple fields => fields
  | .array a b | .reference _ a b => [a, b]
  | .rawPointer _ a => [a]
  | .nominal _ xs | .alias _ xs | .callable _ xs | .effect _ xs => xs
  | .continuation a b c d _ => [a, b, c, d]
  | .label a b c => [a, b, c]
  | .environment a b xs | .available a b xs | .bindings a b xs => a :: b :: xs
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
  | .environment a b xs => .environment (f a) (f b) (xs.map f)
  | .available a b xs => .available (f a) (f b) (xs.map f)
  | .bindings a b xs => .bindings (f a) (f b) (xs.map f)
  | .effect d xs => .effect d (xs.map f)
  | .row xs ys => .row (xs.map f) (ys.map f)
  | .projection d m xs ys k => .projection d m (xs.map f) (ys.map f) k
  | .constantTuple xs => .constantTuple (xs.map f)
  | .constantConstructor d xs ys => .constantConstructor d (xs.map f) (ys.map f)
  | term => term

def SameHead (a b : Term) : Prop := a.mapChildren (fun _ => .unit) = b.mapChildren (fun _ => .unit)

def Access.type (access : Access) (region type : Term) : Term :=
  match access with
  | .owned => type
  | .shared => .reference .shared region type
  | .unique => .reference .unique region type

inductive Occurs : Term → Term → Prop where
  | here {term} : Occurs term term
  | child {needle parent child} : child ∈ parent.children → Occurs needle child → Occurs needle parent

/-- Immutable declaration templates contain lexical identities and kinded
parameters, never identities allocated by a particular runtime execution. -/
def Term.Lexical (term : Term) : Prop :=
  (∀ id, ¬ Occurs (.runtimeRegion id) term) ∧
  (∀ brand, ¬ Occurs (.runtimeBrand brand) term)

theorem Term.Lexical.child {parent child : Term} (lexical : parent.Lexical)
    (member : child ∈ parent.children) : child.Lexical :=
  ⟨fun id occurs => lexical.1 id (.child member occurs),
    fun brand occurs => lexical.2 brand (.child member occurs)⟩

/-- Runtime region renaming preserves every other semantic identity. Snapshot
relocation and its finite-permutation proof use this one structural action. -/
def Term.renameRuntimeRegions (rename : Identity → Identity) : Term → Term
  | .runtimeRegion id => .runtimeRegion (rename id)
  | .tuple fields => .tuple (fields.map (Term.renameRuntimeRegions rename))
  | .array a b => .array (a.renameRuntimeRegions rename) (b.renameRuntimeRegions rename)
  | .reference mode a b => .reference mode (a.renameRuntimeRegions rename) (b.renameRuntimeRegions rename)
  | .rawPointer mode a => .rawPointer mode (a.renameRuntimeRegions rename)
  | .nominal id arguments => .nominal id (arguments.map (Term.renameRuntimeRegions rename))
  | .alias id arguments => .alias id (arguments.map (Term.renameRuntimeRegions rename))
  | .callable id arguments => .callable id (arguments.map (Term.renameRuntimeRegions rename))
  | .continuation a b c d q => .continuation (a.renameRuntimeRegions rename) (b.renameRuntimeRegions rename)
      (c.renameRuntimeRegions rename) (d.renameRuntimeRegions rename) q
  | .label a b c => .label (a.renameRuntimeRegions rename) (b.renameRuntimeRegions rename) (c.renameRuntimeRegions rename)
  | .environment a b residents => .environment (a.renameRuntimeRegions rename) (b.renameRuntimeRegions rename)
      (residents.map (Term.renameRuntimeRegions rename))
  | .available a b residents => .available (a.renameRuntimeRegions rename) (b.renameRuntimeRegions rename)
      (residents.map (Term.renameRuntimeRegions rename))
  | .bindings a b arguments => .bindings (a.renameRuntimeRegions rename) (b.renameRuntimeRegions rename)
      (arguments.map (Term.renameRuntimeRegions rename))
  | .effect id arguments => .effect id (arguments.map (Term.renameRuntimeRegions rename))
  | .row instances tails => .row (instances.map (Term.renameRuntimeRegions rename)) (tails.map (Term.renameRuntimeRegions rename))
  | .projection trait member owners items kind => .projection trait member
      (owners.map (Term.renameRuntimeRegions rename)) (items.map (Term.renameRuntimeRegions rename)) kind
  | .constantTuple fields => .constantTuple (fields.map (Term.renameRuntimeRegions rename))
  | .constantConstructor id arguments fields => .constantConstructor id
      (arguments.map (Term.renameRuntimeRegions rename)) (fields.map (Term.renameRuntimeRegions rename))
  | term => term

/-- Generativity, not liveness: a type may retain an expired region, but cannot
refer to a concrete identity that has never been allocated. -/
def Term.RuntimeRegionsBelow (bound : Identity) (term : Term) : Prop :=
  ∀ id, Occurs (.runtimeRegion id) term → id < bound

theorem Term.RuntimeRegionsBelow.child {bound : Identity} {parent child : Term}
    (supported : parent.RuntimeRegionsBelow bound) (member : child ∈ parent.children) :
    child.RuntimeRegionsBelow bound := fun id occurs => supported id (.child member occurs)

theorem Term.RuntimeRegionsBelow.mono {lower upper : Identity} {term : Term}
    (supported : term.RuntimeRegionsBelow lower) (bound : lower ≤ upper) : term.RuntimeRegionsBelow upper :=
  fun id occurs => Nat.lt_of_lt_of_le (supported id occurs) bound

theorem Term.Lexical.runtimeRegionsBelow {term : Term} (lexical : term.Lexical) (bound : Identity) :
    term.RuntimeRegionsBelow bound := fun id occurs => False.elim (lexical.1 id occurs)

abbrev Substitution := Table Term

def Term.substitute (substitution : Substitution) : Term → Term
  | .parameter id kind => (substitution.get id).getD (.parameter id kind)
  | .tuple fields => .tuple (fields.map (Term.substitute substitution))
  | .array a b => .array (a.substitute substitution) (b.substitute substitution)
  | .reference mode a b => .reference mode (a.substitute substitution) (b.substitute substitution)
  | .rawPointer mode a => .rawPointer mode (a.substitute substitution)
  | .nominal id arguments => .nominal id (arguments.map (Term.substitute substitution))
  | .alias id arguments => .alias id (arguments.map (Term.substitute substitution))
  | .callable id arguments => .callable id (arguments.map (Term.substitute substitution))
  | .continuation a b c d uses => .continuation (a.substitute substitution) (b.substitute substitution)
      (c.substitute substitution) (d.substitute substitution) uses
  | .label a b c => .label (a.substitute substitution) (b.substitute substitution) (c.substitute substitution)
  | .environment a b residents => .environment (a.substitute substitution) (b.substitute substitution)
      (residents.map (Term.substitute substitution))
  | .available a b residents => .available (a.substitute substitution) (b.substitute substitution)
      (residents.map (Term.substitute substitution))
  | .bindings a b arguments => .bindings (a.substitute substitution) (b.substitute substitution)
      (arguments.map (Term.substitute substitution))
  | .effect id arguments => .effect id (arguments.map (Term.substitute substitution))
  | .row instances tails => .row (instances.map (Term.substitute substitution)) (tails.map (Term.substitute substitution))
  | .projection trait member owners items kind => .projection trait member
      (owners.map (Term.substitute substitution)) (items.map (Term.substitute substitution)) kind
  | .constantTuple fields => .constantTuple (fields.map (Term.substitute substitution))
  | .constantConstructor id arguments fields => .constantConstructor id
      (arguments.map (Term.substitute substitution)) (fields.map (Term.substitute substitution))
  | term => term

/-- Lexical scope names and concrete generative identities inhabit distinct
constructors. Closing a caller's scope can never rename an already concrete
region or brand supplied through a generic argument or capture. -/
structure ScopeInstantiation where
  regions : Table Identity := []
  brands : Table RuntimeBrand := []
  deriving Repr, Inhabited

def ScopeInstantiation.term (scope : ScopeInstantiation) : Term → Term
  | .rigid id .region 0 => ((scope.regions.get id).map Term.runtimeRegion).getD (.rigid id .region 0)
  | .rigid id .brand 0 => ((scope.brands.get id).map Term.runtimeBrand).getD (.rigid id .brand 0)
  | .tuple fields => .tuple (fields.map scope.term)
  | .array a b => .array (scope.term a) (scope.term b)
  | .reference mode a b => .reference mode (scope.term a) (scope.term b)
  | .rawPointer mode a => .rawPointer mode (scope.term a)
  | .nominal id arguments => .nominal id (arguments.map scope.term)
  | .alias id arguments => .alias id (arguments.map scope.term)
  | .callable id arguments => .callable id (arguments.map scope.term)
  | .continuation a b c d quantity => .continuation (scope.term a) (scope.term b) (scope.term c) (scope.term d) quantity
  | .label a b c => .label (scope.term a) (scope.term b) (scope.term c)
  | .environment a b residents => .environment (scope.term a) (scope.term b) (residents.map scope.term)
  | .available a b residents => .available (scope.term a) (scope.term b) (residents.map scope.term)
  | .bindings a b arguments => .bindings (scope.term a) (scope.term b) (arguments.map scope.term)
  | .effect id arguments => .effect id (arguments.map scope.term)
  | .row instances tails => .row (instances.map scope.term) (tails.map scope.term)
  | .projection trait member owners items kind => .projection trait member (owners.map scope.term) (items.map scope.term) kind
  | .constantTuple fields => .constantTuple (fields.map scope.term)
  | .constantConstructor id arguments fields => .constantConstructor id (arguments.map scope.term) (fields.map scope.term)
  | term => term

theorem ScopeInstantiation.kind (scope : ScopeInstantiation) (term : Term) : (scope.term term).kind = term.kind := by
  cases term <;> try simp only [ScopeInstantiation.term, Term.kind]
  rename_i id kind level
  cases kind <;> cases level <;> simp only [ScopeInstantiation.term]
  all_goals cases h : scope.regions.get id <;> cases k : scope.brands.get id <;> simp_all only [Option.map, Option.getD]

/-- The checked graph of the single substitution operation. No substituted
occurrence may change kind, even inside a type whose outer kind is unchanged. -/
def Substitutes (substitution : Substitution) (before after : Term) : Prop :=
  before.kind = after.kind ∧ after = before.substitute substitution ∧
  ∀ id kind value, Occurs (.parameter id kind) before → substitution.get id = some value → value.kind = kind

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

def Constraint.mapTerms (f : Term → Term) : Constraint → Constraint
  | .equal a b => .equal (f a) (f b)
  | .outlives a b => .outlives (f a) (f b)
  | .typeOutlives a b => .typeOutlives (f a) (f b)
  | .rowIncludes a b => .rowIncludes (f a) (f b)
  | .implements trait arguments negative => .implements trait (arguments.map f) negative
  | .use type quantity => .use (f type) quantity
  | .callable receiver arguments output effects unsafeAllowed =>
      .callable (f receiver) (arguments.map f) (f output) (f effects) unsafeAllowed
  | .runsIn receiver access arguments after unsafeAllowed =>
      .runsIn (f receiver) (f access) (arguments.map f) (f after) unsafeAllowed
  | .quantified binders requirements =>
      .quantified (binders.map (fun binder => { binder with defaultValue := binder.defaultValue.map f }))
        (requirements.map (Constraint.mapTerms f))

/-- All semantic terms of a constraint, including defaults under quantifiers.
Declaration admission and instantiation proofs inspect this same projection. -/
def Constraint.terms : Constraint → List Term
  | .equal a b | .outlives a b | .typeOutlives a b | .rowIncludes a b => [a,b]
  | .implements _ arguments _ => arguments
  | .use type _ => [type]
  | .callable receiver arguments result effects _ => receiver :: result :: effects :: arguments
  | .runsIn receiver access arguments after _ => receiver :: access :: after :: arguments
  | .quantified binders requirements =>
      binders.flatMap (fun binder => binder.defaultValue.toList) ++ requirements.flatMap Constraint.terms

def Constraint.substitute (substitution : Substitution) : Constraint → Constraint
  | .equal a b => .equal (a.substitute substitution) (b.substitute substitution)
  | .outlives a b => .outlives (a.substitute substitution) (b.substitute substitution)
  | .typeOutlives a b => .typeOutlives (a.substitute substitution) (b.substitute substitution)
  | .rowIncludes a b => .rowIncludes (a.substitute substitution) (b.substitute substitution)
  | .implements trait arguments negative => .implements trait (arguments.map (Term.substitute substitution)) negative
  | .use type quantity => .use (type.substitute substitution) quantity
  | .callable receiver arguments output effects unsafeAllowed => .callable (receiver.substitute substitution)
      (arguments.map (Term.substitute substitution)) (output.substitute substitution) (effects.substitute substitution) unsafeAllowed
  | .runsIn receiver access arguments after unsafeAllowed => .runsIn (receiver.substitute substitution)
      (access.substitute substitution) (arguments.map (Term.substitute substitution)) (after.substitute substitution) unsafeAllowed
  | .quantified binders requirements =>
      let restricted := substitution.filter (fun entry => !(binders.any (fun binder => binder.id == entry.1)))
      .quantified (binders.map (fun binder => { binder with defaultValue := binder.defaultValue.map (Term.substitute restricted) }))
        (requirements.map (Constraint.substitute restricted))

/-- Bound declaration identities are globally fresh; checking this condition
also rejects accidental capture in externally supplied substitutions. -/
def Constraint.SubstitutionAdmissible (substitution : Substitution) : Constraint → Prop
  | .equal a b | .outlives a b | .typeOutlives a b | .rowIncludes a b =>
      Substitutes substitution a (a.substitute substitution) ∧ Substitutes substitution b (b.substitute substitution)
  | .implements _ arguments _ => ∀ argument ∈ arguments, Substitutes substitution argument (argument.substitute substitution)
  | .use type _ => Substitutes substitution type (type.substitute substitution)
  | .callable receiver arguments output effects _ =>
      ∀ term ∈ receiver :: output :: effects :: arguments, Substitutes substitution term (term.substitute substitution)
  | .runsIn receiver access arguments after _ =>
      ∀ term ∈ receiver :: access :: after :: arguments, Substitutes substitution term (term.substitute substitution)
  | .quantified binders requirements =>
      let restricted := substitution.filter (fun entry => !(binders.any (fun binder => binder.id == entry.1)))
      (∀ entry ∈ restricted, ∀ binder ∈ binders, ¬ Occurs (.parameter binder.id binder.kind) entry.2) ∧
      (∀ binder ∈ binders, ∀ value, binder.defaultValue = some value → Substitutes restricted value (value.substitute restricted)) ∧
      ∀ requirement ∈ requirements, requirement.SubstitutionAdmissible restricted

def SubstituteConstraint (substitution : Substitution) (before after : Constraint) : Prop :=
  before.SubstitutionAdmissible substitution ∧ after = before.substitute substitution

structure Signature where
  generics : List Binder := []
  parameters : List Term
  result : Term
  effects : Term := .row [] []
  constraints : List Constraint := []
  unsafeAllowed : Bool := false
  deriving Repr, Inhabited

/-- Complete semantic signature terms, shared by declaration and external
binding admission, including defaults below quantified constraints. -/
def Signature.terms (signature : Signature) : List Term :=
  signature.result :: signature.effects :: signature.parameters ++
    signature.constraints.flatMap Constraint.terms ++
    signature.generics.flatMap (fun binder => binder.defaultValue.toList)

def Signature.mapTerms (f : Term → Term) (signature : Signature) : Signature :=
  { signature with
    generics := signature.generics.map (fun binder => { binder with defaultValue := binder.defaultValue.map f })
    parameters := signature.parameters.map f
    result := f signature.result
    effects := f signature.effects
    constraints := signature.constraints.map (Constraint.mapTerms f) }

def Signature.close (signature : Signature) (scope : ScopeInstantiation) : Signature :=
  signature.mapTerms scope.term

inductive Visibility where
  | privateScope | publicScope | package | parent
  deriving DecidableEq, BEq, Repr, Inhabited

inductive Namespace where
  | type | value | trait | effect | region | label | parameter
  deriving DecidableEq, BEq, Repr, Inhabited

structure Header where
  id : DeclId
  module : ModuleId
  name : String
  nameSpace : Namespace
  visibility : Visibility
  span : Span
  sourceVisible : Bool := true
  deriving Repr, Inhabited

def Descendant (child parent : ModuleId) : Prop :=
  child.package = parent.package ∧ ∃ suffix, child.path = parent.path ++ suffix

def Visible (header : Header) (requester : ModuleId) : Prop :=
  match header.visibility with
  | .publicScope => True
  | .package => requester.package = header.module.package
  | .privateScope => Descendant requester header.module
  | .parent => Descendant requester { header.module with path := header.module.path.dropLast }

inductive RegionIncludes (assumptions : List Constraint) : Term → Term → Prop where
  | refl {region} : RegionIncludes assumptions region region
  | static {region} : RegionIncludes assumptions .staticRegion region
  | assumed {a b} : Constraint.outlives a b ∈ assumptions → RegionIncludes assumptions a b
  | trans {a b c} : RegionIncludes assumptions a b → RegionIncludes assumptions b c →
      RegionIncludes assumptions a c

def NoLeak (universeLevel : Nat) (term : Term) : Prop :=
  ∀ id kind level, Occurs (.rigid id kind level) term → level ≤ universeLevel

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
  exact proof.1

end Glorious.Language
