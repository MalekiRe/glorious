import Grounded.Model

/-! Static type resolution, finite inline layout and owned-use permissions. These contracts
do not depend on expression checking or execution. -/
namespace Grounded

mutual
/-- Alias expansion is finite and independent of declaration order. No alias
identity survives in the resolved type (§4.3). -/
inductive ResolvesType (aliases : Aliases) : TypeExpr → Ty → Prop where
  | concrete (type : Ty) : ResolvesType aliases (.concrete type) type
  | alias {name : String} {body : TypeExpr} {type : Ty}
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

def UsePermission.Allows (permission : UsePermission) : Option Principal → Prop
  | none | some .duplicable => True
  | some .affine => permission = .discard
  | some .exact => False

/-- One structural producer for Copy and MayDiscard. This logical fragment has
no custom Drop hooks or indirections; every resident contributes its permission. -/
inductive UsePermitted (data : DataDeclarations) (permission : UsePermission) : Ty → Prop where
  | unit : UsePermitted data permission .unit
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
  | integer type => exact .integer type
  | character => exact .character
  | tuple first rest firstIH restIH => exact .tuple firstIH restIH
  | array length resident ih => exact .array length ih
  | emptyArray element => exact .emptyArray element
  | nominal declared restriction fields ih => exact .nominal declared (UsePermission.copy_allows_discard restriction) ih

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
theorem DataDeclarations.PrincipalsValid.permission {data : DataDeclarations}
    (valid : data.PrincipalsValid) {identity : Nat} {declaration : DataDecl} {principal : Principal}
    (declared : data identity = some declaration) (manual : declaration.restriction = some principal)
    (permission : UsePermission) :
    UsePermitted data permission (.nominal identity) ↔ permission.Allows (some principal) := by
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



end Grounded
