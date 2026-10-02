import Grounded.Model

/-! Static type resolution, finite inline layout and owned-use permissions. These contracts
do not depend on expression checking or execution. -/
namespace Grounded

mutual
/-- Alias expansion is finite and independent of declaration order. No alias
identity survives in the resolved type (§4.3). -/
inductive ResolvesType (aliases : Aliases) : TypeExpr → Ty → Prop where
  | concrete (type : Ty) : ResolvesType aliases (.concrete type) type
  | alias {name : Nat} {body : TypeExpr} {type : Ty}
      (declared : aliases name = some body) (expanded : ResolvesType aliases body type) :
      ResolvesType aliases (.alias name) type
  | tuple {head : TypeExpr} {tail : List TypeExpr} {first : Ty} {rest : List Ty}
      (firstType : ResolvesType aliases head first) (restTypes : ResolvesTypes aliases tail rest) :
      ResolvesType aliases (.tuple head tail) (.tuple first rest)
  | array {element : TypeExpr} {type : Ty} (length : Nat)
      (resolved : ResolvesType aliases element type) :
      ResolvesType aliases (.array element length) (.array type length)

inductive ResolvesTypes (aliases : Aliases) : List TypeExpr → List Ty → Prop where
  | nil : ResolvesTypes aliases [] []
  | cons {head : TypeExpr} {tail : List TypeExpr} {first : Ty} {rest : List Ty}
      (firstType : ResolvesType aliases head first) (restTypes : ResolvesTypes aliases tail rest) :
      ResolvesTypes aliases (head :: tail) (first :: rest)
end

/-- Finite alias resolution has one result, including nested aggregate aliases. -/
theorem ResolvesType.unique {aliases : Aliases} {source : TypeExpr} {type : Ty}
    (resolved : ResolvesType aliases source type) :
    ∀ other, ResolvesType aliases source other → other = type := by
  induction resolved using ResolvesType.rec
    (motive_2 := fun source types _ => ∀ others, ResolvesTypes aliases source others → others = types) with
  | concrete type => intro other found; cases found; rfl
  | alias declared expanded ih =>
    intro other found
    cases found with
    | alias otherDeclared otherExpanded =>
      cases Option.some.inj (declared.symm.trans otherDeclared)
      exact ih _ otherExpanded
  | tuple first rest firstIH restIH =>
    intro other found
    cases found with
    | tuple otherFirst otherRest => rw [firstIH _ otherFirst, restIH _ otherRest]
  | array length element ih =>
    intro other found
    cases found with
    | array _ otherElement => rw [ih _ otherElement]
  | nil => rename_i others found; cases found; rfl
  | cons first rest firstIH restIH =>
    rename_i others found
    cases found with
    | cons otherFirst otherRest => rw [firstIH _ otherFirst, restIH _ otherRest]


inductive Annotation (aliases : Aliases) : Option TypeExpr → Ty → Prop where
  | inferred (type : Ty) : Annotation aliases none type
  | explicit {source : TypeExpr} {type : Ty} (resolved : ResolvesType aliases source type) :
      Annotation aliases (some source) type

/-- Inline type expansion must be finite, including every enum variant. There
are no indirections in this subset; zero array length does not license Self. -/
inductive FiniteLayout (target : Target) (data : DataDeclarations) : Ty → Prop where
  | unit : FiniteLayout target data .unit
  | never : FiniteLayout target data .never
  | integer (type : IntegerType) : FiniteLayout target data (.integer type)
  | character : FiniteLayout target data .character
  | tuple {head : Ty} {tail : List Ty} (first : FiniteLayout target data head)
      (rest : ∀ type ∈ tail, FiniteLayout target data type) :
      FiniteLayout target data (.tuple head tail)
  | array {element : Ty} {length : Nat} (resident : FiniteLayout target data element)
      (size : length < 2 ^ target.pointerBits) : FiniteLayout target data (.array element length)
  | nominal {identity : Nat} {declaration : DataDecl}
      (declared : data identity = some declaration)
      (schemas : ∀ schema ∈ declaration.schemas, schema.Valid)
      (fields : ∀ schema ∈ declaration.schemas, ∀ field ∈ schema.residents,
        FiniteLayout target data field.type) : FiniteLayout target data (.nominal identity)

/-- The two independent owned-use permissions in §7. Copy does not mean move;
    discard permits zero use. Exact ownership grants neither permission. -/
inductive UsePermission where
  | copy | discard

/-- The three ordinary principal intervals describe permitted owned-use counts. -/
@[simp] def Principal.Permits : Principal → Nat → Prop
  | .duplicable, _ => True
  | .affine, quantity => quantity ≤ 1
  | .exact, quantity => quantity = 1

/-- Requested owned-use counts are not principal declarations. An absent upper
endpoint denotes infinity; reversed finite intervals are not valid requests. -/
structure QuantityBound where
  lower : Nat
  upper : Option Nat

def QuantityBound.Contains (bound : QuantityBound) (quantity : Nat) : Prop :=
  bound.lower ≤ quantity ∧ match bound.upper with
    | none => True
    | some upper => quantity ≤ upper

def QuantityBound.Valid (bound : QuantityBound) : Prop :=
  match bound.upper with
  | none => True
  | some upper => bound.lower ≤ upper

/-- Zero-only use is an internal destruction predicate, not a public bound. -/
def QuantityBound.Public (bound : QuantityBound) : Prop :=
  bound.Valid ∧ bound.upper ≠ some 0

/-- A public request denotes an interval contained in the actual principal,
not a claim that the principal equals that interval. -/
def Principal.Satisfies (principal : Principal) (requested : QuantityBound) : Prop :=
  requested.Public ∧ ∀ quantity, requested.Contains quantity → principal.Permits quantity

theorem Principal.satisfies_iff (principal : Principal) (requested : QuantityBound) :
    principal.Satisfies requested ↔ requested.Public ∧
      (requested.Contains 0 → principal ≠ .exact) ∧
      ((∃ quantity, 1 < quantity ∧ requested.Contains quantity) → principal = .duplicable) := by
  constructor
  · rintro ⟨admissible, permitted⟩
    refine ⟨admissible, ?_, ?_⟩
    · intro zero
      have allowed := permitted 0 zero
      cases principal <;> simp_all
    · rintro ⟨quantity, multiple, member⟩
      have allowed := permitted quantity member
      cases principal with
      | duplicable => rfl
      | affine => have bound : quantity ≤ 1 := allowed; omega
      | exact => have once : quantity = 1 := allowed; omega
  · rintro ⟨admissible, zero, multiple⟩
    refine ⟨admissible, fun quantity member => ?_⟩
    cases principal with
    | duplicable => trivial
    | affine =>
      by_cases atMost : quantity ≤ 1
      · exact atMost
      · have impossible := multiple ⟨quantity, by omega, member⟩
        contradiction
    | exact =>
      have positive : quantity ≠ 0 := by
        intro absent
        subst quantity
        exact zero member rfl
      by_cases atMost : quantity ≤ 1
      · exact Nat.le_antisymm atMost (by omega)
      · have impossible := multiple ⟨quantity, by omega, member⟩
        contradiction

@[simp] theorem Principal.satisfies_copy (principal : Principal) :
    principal.Satisfies ⟨0, none⟩ ↔ principal = .duplicable := by
  cases principal <;> simp [Satisfies, QuantityBound.Public, QuantityBound.Valid, QuantityBound.Contains]
  all_goals first | exact ⟨0, by omega⟩ | exact ⟨2, by omega⟩

@[simp] theorem Principal.satisfies_discard (principal : Principal) :
    principal.Satisfies ⟨0, some 1⟩ ↔ principal ≠ .exact := by
  cases principal <;> simp [Satisfies, QuantityBound.Public, QuantityBound.Valid, QuantityBound.Contains]
  exact ⟨0, by omega⟩

@[simp] theorem Principal.satisfies_once (principal : Principal) :
    principal.Satisfies ⟨1, some 1⟩ := by
  refine ⟨by simp [QuantityBound.Public, QuantityBound.Valid], ?_⟩
  intro quantity member
  have same : quantity = 1 := by
    simp only [QuantityBound.Contains] at member
    omega
  subst quantity
  cases principal <;> simp

@[simp] def UsePermission.request : UsePermission → QuantityBound
  | .copy => ⟨0, none⟩
  | .discard => ⟨0, some 1⟩

def UsePermission.Allows (permission : UsePermission) : Option Principal → Prop
  | none => True
  | some principal => principal.Satisfies permission.request

/-- One structural producer for Copy and MayDiscard. This logical fragment has
no custom Drop hooks or indirections; every resident contributes its permission. -/
inductive UsePermitted (data : DataDeclarations) (permission : UsePermission) : Ty → Prop where
  | unit : UsePermitted data permission .unit
  | never : UsePermitted data permission .never
  | integer (type : IntegerType) : UsePermitted data permission (.integer type)
  | character : UsePermitted data permission .character
  | tuple {head : Ty} {tail : List Ty} (first : UsePermitted data permission head)
      (rest : ∀ type ∈ tail, UsePermitted data permission type) :
      UsePermitted data permission (.tuple head tail)
  | array {element : Ty} (length : Nat) (resident : UsePermitted data permission element) :
      UsePermitted data permission (.array element length)
  | emptyArray (element : Ty) : UsePermitted data permission (.array element 0)
  | nominal {identity : Nat} {declaration : DataDecl}
      (declared : data identity = some declaration)
      (restriction : permission.Allows declaration.restriction)
      (fields : ∀ schema ∈ declaration.schemas, ∀ field ∈ schema.residents,
        UsePermitted data permission field.type) :
      UsePermitted data permission (.nominal identity)

theorem UsePermission.copy_allows_discard {restriction : Option Principal}
    (allowed : UsePermission.copy.Allows restriction) : UsePermission.discard.Allows restriction := by
  cases restriction with
  | none => trivial
  | some principal => cases principal <;> simp_all [UsePermission.Allows]

/-- Structural Copy evidence entails zero-use permission, not conversely. -/
theorem UsePermitted.copy_discard {data : DataDeclarations} {type : Ty}
    (copy : UsePermitted data .copy type) : UsePermitted data .discard type := by
  induction copy with
  | unit => exact .unit
  | never => exact .never
  | integer type => exact .integer type
  | character => exact .character
  | tuple first rest firstIH restIH => exact .tuple firstIH restIH
  | array length resident ih => exact .array length ih
  | emptyArray element => exact .emptyArray element
  | nominal declared restriction fields ih => exact .nominal declared (UsePermission.copy_allows_discard restriction) ih
/-- All requested counts use the same Copy/MayDiscard producer. Count one
requires neither capability; zero requires disposal, and repeated use requires
Copy. Invalid and zero-only public requests are rejected before interpretation. -/
def Ty.SatisfiesUse (data : DataDeclarations) (type : Ty) (requested : QuantityBound) : Prop :=
  requested.Public ∧
    (requested.Contains 0 → UsePermitted data .discard type) ∧
    ((∃ quantity, 1 < quantity ∧ requested.Contains quantity) → UsePermitted data .copy type)

/-- Principal classification is an interpretation of existing permissions, not
another structural inference pass or a second permission table. -/
def Ty.HasPrincipal (data : DataDeclarations) (type : Ty) (principal : Principal) : Prop :=
  ∀ permission, UsePermitted data permission type ↔ permission.Allows (some principal)

theorem Ty.HasPrincipal.unique {data : DataDeclarations} {type : Ty} {first second : Principal}
    (left : type.HasPrincipal data first) (right : type.HasPrincipal data second) : first = second := by
  have leftCopy := left .copy
  have leftDiscard := left .discard
  have rightCopy := right .copy
  have rightDiscard := right .discard
  cases first <;> cases second <;> simp_all [UsePermission.Allows]

theorem Ty.HasPrincipal.satisfies {data : DataDeclarations} {type : Ty} {principal : Principal}
    (classified : type.HasPrincipal data principal) (requested : QuantityBound) :
    type.SatisfiesUse data requested ↔ principal.Satisfies requested := by
  have copies : UsePermitted data .copy type ↔ principal = .duplicable := by
    simpa [UsePermission.Allows] using classified .copy
  have discards : UsePermitted data .discard type ↔ principal ≠ .exact := by
    simpa [UsePermission.Allows] using classified .discard
  simp only [Ty.SatisfiesUse, Principal.satisfies_iff, copies, discards]

theorem finite_permissions {α : Type} (items : List α) (permission : α → Prop)
    (each : ∀ item ∈ items, permission item ∨ ¬ permission item) :
    (∀ item ∈ items, permission item) ∨ ∃ item ∈ items, ¬ permission item := by
  induction items with
  | nil => exact .inl (by simp)
  | cons head tail ih =>
    rcases each head (by simp) with allowed | denied
    · rcases ih (fun item member => each item (by simp [member])) with all | missing
      · exact .inl (by intro item member; cases member with | head => exact allowed | tail _ member => exact all item member)
      · obtain ⟨item, member, denied⟩ := missing
        exact .inr ⟨item, by simp [member], denied⟩
    · exact .inr ⟨head, by simp, denied⟩

/-- Finite inline layout supplies a finite constructive derivation of either
permission or its refutation, including every variant and empty arrays. -/
theorem FiniteLayout.permission_cases {target : Target} {data : DataDeclarations} {type : Ty}
    (finite : FiniteLayout target data type) (permission : UsePermission) :
    UsePermitted data permission type ∨ ¬ UsePermitted data permission type := by
  induction finite with
  | unit => exact .inl .unit
  | never => exact .inl .never
  | integer type => exact .inl (.integer type)
  | character => exact .inl .character
  | tuple first rest headIH tailIH =>
    rcases headIH with allowed | denied
    · rcases finite_permissions _ _ tailIH with all | missing
      · exact .inl (.tuple allowed all)
      · obtain ⟨type, member, denied⟩ := missing
        exact .inr (by intro available; cases available with | tuple _ fields => exact denied (fields type member))
    · exact .inr (by intro available; cases available with | tuple head _ => exact denied head)
  | @array element length resident size ih =>
    by_cases empty : length = 0
    · subst length; exact .inl (.emptyArray element)
    · rcases ih with allowed | denied
      · exact .inl (.array length allowed)
      · exact .inr (by
          intro available
          cases available with
          | array _ element => exact denied element
          | emptyArray => exact empty rfl)
  | @nominal identity declaration declared schemas fields ih =>
    have restriction : permission.Allows declaration.restriction ∨ ¬ permission.Allows declaration.restriction := by
      cases declaration.restriction with
      | none => exact .inl trivial
      | some principal => cases principal <;> cases permission <;> simp [UsePermission.Allows]
    rcases restriction with allowed | denied
    · have each : ∀ schema ∈ declaration.schemas,
          (∀ field ∈ schema.residents, UsePermitted data permission field.type) ∨
          ¬ (∀ field ∈ schema.residents, UsePermitted data permission field.type) := by
        intro schema member
        rcases finite_permissions schema.residents _ (ih schema member) with all | missing
        · exact .inl all
        · obtain ⟨field, included, denied⟩ := missing
          exact .inr (fun all => denied (all field included))
      rcases finite_permissions declaration.schemas _ each with all | missing
      · exact .inl (.nominal declared allowed all)
      · obtain ⟨schema, member, denied⟩ := missing
        exact .inr (by
          intro available
          cases available with
          | nominal found _ residents =>
            cases Option.some.inj (found.symm.trans declared)
            exact denied (residents schema member))
    · exact .inr (by
        intro available
        cases available with
        | nominal found restriction _ =>
          cases Option.some.inj (found.symm.trans declared)
          exact denied restriction)

/-- Valid finite ordinary types have one principal, with refuted permissions
derived from the same finite structural evidence rather than missing evidence. -/
theorem Ty.principal_exists {target : Target} {data : DataDeclarations} {type : Ty}
    (finite : FiniteLayout target data type) :

    ∃ principal, type.HasPrincipal data principal ∧
      ∀ other, type.HasPrincipal data other → other = principal := by

  have finish (principal : Principal) (classified : type.HasPrincipal data principal) :
      ∃ principal, type.HasPrincipal data principal ∧
        ∀ other, type.HasPrincipal data other → other = principal :=
    ⟨principal, classified, fun _ other => other.unique classified⟩
  rcases finite.permission_cases .copy with copies | copies
  · apply finish .duplicable
    have discards := copies.copy_discard
    intro permission
    cases permission <;> simp [UsePermission.Allows, copies, discards]
  · rcases finite.permission_cases .discard with discards | discards
    · apply finish .affine
      intro permission
      cases permission <;> simp [UsePermission.Allows, copies, discards]
    · apply finish .exact
      intro permission
      cases permission <;> simp [UsePermission.Allows, copies, discards]
/-- A manual class must be supported by every owned field of every variant.
No declaration means inference; an exact restriction requests no zero-use or
Copy capability. This uses the same permission producer as expression checking. -/
def DataDecl.PrincipalValid (data : DataDeclarations) (declaration : DataDecl) : Prop :=
  match declaration.restriction with
  | none | some .exact => True
  | some .duplicable => ∀ schema ∈ declaration.schemas, ∀ field ∈ schema.residents,
      UsePermitted data .copy field.type
  | some .affine => ∀ schema ∈ declaration.schemas, ∀ field ∈ schema.residents,
      UsePermitted data .discard field.type

def DataDeclarations.PrincipalsValid (data : DataDeclarations) : Prop :=
  ∀ identity declaration, data identity = some declaration → declaration.PrincipalValid data

/-- An admitted explicit principal denotes exactly its declared permissions;
structural intersection cannot silently narrow an invalid declaration. -/
theorem DataDeclarations.PrincipalsValid.principal {data : DataDeclarations}
    (valid : data.PrincipalsValid) {identity : Nat} {declaration : DataDecl} {principal : Principal}
    (declared : data identity = some declaration) (manual : declaration.restriction = some principal) :
    Ty.HasPrincipal data (.nominal identity) principal := by
  intro permission
  constructor
  · intro permitted
    cases permitted with
    | nominal found restriction fields =>
      cases Option.some.inj (found.symm.trans declared)
      simpa only [manual] using restriction
  · intro allowed
    apply UsePermitted.nominal declared (by simpa only [manual] using allowed)
    have fields := valid identity declaration declared
    unfold DataDecl.PrincipalValid at fields
    rw [manual] at fields
    intro schema included field member
    cases principal with
    | exact => cases permission <;> simp [UsePermission.Allows] at allowed
    | affine =>
      cases permission with
      | copy => simp [UsePermission.Allows] at allowed
      | discard => exact fields schema included field member
    | duplicable =>
      cases permission with
      | copy => exact fields schema included field member
      | discard => exact (fields schema included field member).copy_discard

/-- Direct inline containment, not a reference or pointer-referent edge. -/
inductive InlineChild (data : DataDeclarations) : Ty → Ty → Prop where
  | tupleHead (first : Ty) (rest : List Ty) : InlineChild data first (.tuple first rest)
  | tupleTail {first : Ty} {rest : List Ty} {child : Ty} (member : child ∈ rest) :
      InlineChild data child (.tuple first rest)
  | array (element : Ty) (length : Nat) : InlineChild data element (.array element length)
  | nominal {identity : Nat} {declaration : DataDecl} {schema : Fields} {field : Field}
      (declared : data identity = some declaration) (variant : schema ∈ declaration.schemas)
      (member : field ∈ schema.residents) : InlineChild data field.type (.nominal identity)

/-- Finite layout witnesses establish well-founded inline containment. -/
theorem FiniteLayout.accessible {target : Target} {data : DataDeclarations} {type : Ty}
    (finite : FiniteLayout target data type) : Acc (InlineChild data) type := by
  induction finite with
  | unit | never | integer | character => constructor; intro child edge; cases edge
  | tuple first rest firstIH restIH =>
    constructor
    intro child edge
    cases edge with
    | tupleHead => exact firstIH
    | tupleTail member => exact restIH child member
  | array resident size ih =>
    constructor
    intro child edge
    cases edge
    exact ih
  | nominal declared schemas fields ih =>
    constructor
    intro child edge
    cases edge with
    | nominal found variant member =>
      cases Option.some.inj (found.symm.trans declared)
      exact ih _ variant _ member

private theorem accessible_not_cycle {α : Sort _} {relation : α → α → Prop} {value : α}
    (accessible : Acc relation value) : ¬ Relation.TransGen relation value value := by
  induction accessible with
  | intro value accessible ih =>
    intro cycle
    cases cycle with
    | single edge => exact ih _ edge (.single edge)
    | tail chain edge => exact ih _ edge ((Relation.TransGen.single edge).trans chain)

theorem FiniteLayout.no_inline_cycle {target : Target} {data : DataDeclarations} {type : Ty}
    (finite : FiniteLayout target data type) : ¬ Relation.TransGen (InlineChild data) type type :=
  accessible_not_cycle finite.accessible

/-- One admission product checks all decoded nominal declarations, not only
those whose constructors are reached by a function body. -/
structure DataDeclarations.Valid (data : DataDeclarations) (target : Target) : Prop where
  principals : data.PrincipalsValid
  layouts : ∀ identity declaration, data identity = some declaration →
    FiniteLayout target data (.nominal identity)

/-- Syntactic alias references whose expansion is required by a decoded type. -/
inductive TypeExpr.MentionsAlias (name : Nat) : TypeExpr → Prop where
  | alias : TypeExpr.MentionsAlias name (.alias name)
  | tupleHead {head : TypeExpr} {tail : List TypeExpr} (mentioned : TypeExpr.MentionsAlias name head) :
      TypeExpr.MentionsAlias name (.tuple head tail)
  | tupleTail {head : TypeExpr} {tail : List TypeExpr} {source : TypeExpr}
      (member : source ∈ tail) (mentioned : TypeExpr.MentionsAlias name source) :
      TypeExpr.MentionsAlias name (.tuple head tail)
  | array {element : TypeExpr} {length : Nat} (mentioned : TypeExpr.MentionsAlias name element) :
      TypeExpr.MentionsAlias name (.array element length)

inductive AliasDependency (aliases : Aliases) : Nat → Nat → Prop where
  | intro {parent child : Nat} {body : TypeExpr} (declared : aliases parent = some body)
      (mentioned : body.MentionsAlias child) : AliasDependency aliases child parent

/-- The actual expansion derivation supplies declaration existence and
well-foundedness for every alias reference; no second expander is involved. -/
theorem ResolvesType.alias_dependencies {aliases : Aliases} {source : TypeExpr} {type : Ty}
    (resolved : ResolvesType aliases source type) :
    ∀ name, source.MentionsAlias name → (∃ body, aliases name = some body) ∧ Acc (AliasDependency aliases) name := by
  induction resolved using ResolvesType.rec
    (motive_2 := fun sources _ _ => ∀ source ∈ sources, ∀ name, source.MentionsAlias name →
      (∃ body, aliases name = some body) ∧ Acc (AliasDependency aliases) name) with
  | concrete => intro name mentioned; cases mentioned
  | alias declared expanded ih =>
    intro name mentioned
    cases mentioned
    refine ⟨⟨_, declared⟩, .intro _ ?_⟩
    intro child edge
    cases edge with
    | intro found reference =>
      cases Option.some.inj (found.symm.trans declared)
      exact (ih child reference).2
  | tuple first rest firstIH restIH =>
    intro name mentioned
    cases mentioned with
    | tupleHead reference => exact firstIH name reference
    | tupleTail member reference => exact restIH _ member name reference
  | array length element ih =>
    intro name mentioned
    cases mentioned with
    | array reference => exact ih name reference
  | nil => rename_i source member name mentioned; cases member
  | cons head tail headIH tailIH =>
    rename_i source member name mentioned
    cases member with
    | head => exact headIH name mentioned
    | tail _ member => exact tailIH source member name mentioned

theorem ResolvesType.no_alias_cycle {aliases : Aliases} {name : Nat} {type : Ty}
    (resolved : ResolvesType aliases (.alias name) type) :
    ¬ Relation.TransGen (AliasDependency aliases) name name :=
  accessible_not_cycle (resolved.alias_dependencies name .alias).2

/-- Validate every alias body, including unused declarations, with the same
finite expansion and layout judgments consumed by source type elaboration. -/
def Aliases.Valid (aliases : Aliases) (target : Target) (data : DataDeclarations) : Prop :=
  ∀ name body, aliases name = some body →
    ∃ type, ResolvesType aliases body type ∧ FiniteLayout target data type





end Grounded
