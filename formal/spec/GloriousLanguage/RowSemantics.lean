import GloriousLanguage.Terms

/-! The structural row quotient used by definitional conversion. This quotient
does not expand declarations, discharge assumptions, or identify distinct
scalar types.  In particular, its unordered rows do not impose an order on
generative runtime identities. -/
namespace Glorious.Language

inductive RowEquivalent : Term → Term → Prop where
  | refl {term} : RowEquivalent term term
  | symm {left right} : RowEquivalent left right → RowEquivalent right left
  | trans {left middle right} : RowEquivalent left middle → RowEquivalent middle right → RowEquivalent left right
  | congr {left right} : SameHead left right → ListRel RowEquivalent left.children right.children →
      RowEquivalent left right
  | permutation {instances tails instances' tails'} : instances.Perm instances' → tails.Perm tails' →
      RowEquivalent (.row instances tails) (.row instances' tails')
  | flatten {instances tails nested nestedTails} :
      RowEquivalent (.row instances (.row nested nestedTails :: tails))
        (.row (instances ++ nested) (nestedTails ++ tails))
  | duplicate {left right rest tails} : RowEquivalent left right →
      RowEquivalent (.row (left :: right :: rest) tails) (.row (left :: rest) tails)
  | tailDuplicate {instances left right tails} : RowEquivalent left right →
      RowEquivalent (.row instances (left :: right :: tails)) (.row instances (left :: tails))

instance rowSetoid : Setoid Term where
  r := RowEquivalent
  iseqv := ⟨fun _ => .refl, fun equal => .symm equal, fun first second => .trans first second⟩

/-- Declaration-free equality classes. Positive definitional reductions are
kept separate; quotienting only the row laws cannot manufacture a type equality. -/
abbrev SemanticTerm := Quotient rowSetoid

def SemanticTerm.ofTerm (term : Term) : SemanticTerm := Quotient.mk rowSetoid term

theorem SemanticTerm.ofTerm_equal {left right : Term} :
    SemanticTerm.ofTerm left = SemanticTerm.ofTerm right ↔ RowEquivalent left right :=
  ⟨Quotient.exact, fun equal => Quotient.sound equal⟩

theorem RowEquivalent.kind_eq {left right : Term} (equal : RowEquivalent left right) :
    left.kind = right.kind := by
  refine RowEquivalent.rec (motive_1 := fun left right _ => left.kind = right.kind)
    (motive_2 := fun _ _ _ => True) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ equal
  · intros; rfl
  · intro _ _ _ ih; exact ih.symm
  · intro _ _ _ _ _ first second; exact first.trans second
  · intro _ _ same _ _; exact sameHead_kind same
  all_goals intros; first | rfl | trivial

def SemanticTerm.kind : SemanticTerm → Kind := Quotient.lift Term.kind (fun _ _ equal => equal.kind_eq)

/-- Scalar discrimination is a theorem of the structural quotient, not an
assumed consistency premise on static equality. -/
def Term.scalarDiscriminator : Term → Option Scalar
  | .scalar type => some type
  | _ => none

theorem SameHead.scalarDiscriminator_eq {left right : Term} (same : SameHead left right) :
    left.scalarDiscriminator = right.scalarDiscriminator := by
  have heads := congrArg Term.scalarDiscriminator same
  have unchanged (term : Term) :
      (term.mapChildren (fun _ => .unit)).scalarDiscriminator = term.scalarDiscriminator := by
    cases term <;> rfl
  simpa only [unchanged] using heads

theorem RowEquivalent.scalarDiscriminator_eq {left right : Term} (equal : RowEquivalent left right) :
    left.scalarDiscriminator = right.scalarDiscriminator := by
  refine RowEquivalent.rec
    (motive_1 := fun left right _ => left.scalarDiscriminator = right.scalarDiscriminator)
    (motive_2 := fun _ _ _ => True) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ equal
  · intros; rfl
  · intro _ _ _ ih; exact ih.symm
  · intro _ _ _ _ _ first second; exact first.trans second
  · intro _ _ same _ _; exact same.scalarDiscriminator_eq
  all_goals intros; first | rfl | trivial

theorem SemanticTerm.scalar_injective {left right : Scalar}
    (same : ofTerm (.scalar left) = ofTerm (.scalar right)) : left = right :=
  Option.some.inj (RowEquivalent.scalarDiscriminator_eq (Quotient.exact same))

theorem Term.renameRuntimeRegions_children (rename : Identity → Identity) (term : Term) :
    (term.renameRuntimeRegions rename).children = term.children.map (Term.renameRuntimeRegions rename) := by
  cases term <;> simp only [Term.renameRuntimeRegions,Term.children,List.map_cons,List.map_nil,List.map_append]

theorem Term.renameRuntimeRegions_head (rename : Identity → Identity) (term : Term) :
    (term.renameRuntimeRegions rename).mapChildren (fun _ => .unit) =
      (term.mapChildren (fun _ => .unit)).renameRuntimeRegions rename := by
  cases term <;> simp only [Term.renameRuntimeRegions,Term.mapChildren,List.map_map,Function.comp_def]
  all_goals try rfl
  all_goals congr 1
  all_goals apply List.map_congr_left
  all_goals intro child _
  all_goals simp only [Term.renameRuntimeRegions]

theorem SameHead.renameRuntimeRegions {left right : Term} (same : SameHead left right)
    (rename : Identity → Identity) :
    SameHead (left.renameRuntimeRegions rename) (right.renameRuntimeRegions rename) := by
  unfold SameHead at same ⊢
  rw [Term.renameRuntimeRegions_head,Term.renameRuntimeRegions_head,same]

theorem RowEquivalent.renameRuntimeRegions {left right : Term} (equal : RowEquivalent left right)
    (rename : Identity → Identity) :
    RowEquivalent (left.renameRuntimeRegions rename) (right.renameRuntimeRegions rename) := by
  refine RowEquivalent.rec
    (motive_1 := fun left right _ => RowEquivalent (left.renameRuntimeRegions rename) (right.renameRuntimeRegions rename))
    (motive_2 := fun left right _ => ListRel RowEquivalent
      (left.map (Term.renameRuntimeRegions rename)) (right.map (Term.renameRuntimeRegions rename)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ equal
  · intros; exact .refl
  · intro _ _ _ ih; exact .symm ih
  · intro _ _ _ _ _ first second; exact .trans first second
  · intro _ _ same _ children
    exact .congr (same.renameRuntimeRegions rename) (by
      simpa only [Term.renameRuntimeRegions_children] using children)
  · intro _ _ _ _ instances tails
    simp only [Term.renameRuntimeRegions]
    exact .permutation (instances.map _) (tails.map _)
  · intros; simpa only [Term.renameRuntimeRegions,List.map_cons,List.map_append] using
      (RowEquivalent.flatten (instances := _) (tails := _) (nested := _) (nestedTails := _))
  · intro _ _ _ _ _ ih
    simp only [Term.renameRuntimeRegions,List.map_cons]
    exact .duplicate ih
  · intro _ _ _ _ _ ih
    simp only [Term.renameRuntimeRegions,List.map_cons]
    exact .tailDuplicate ih
  · exact .nil
  · intro _ _ _ _ _ _ head tail; exact .cons head tail

def SemanticTerm.renameRuntimeRegions (rename : Identity → Identity) : SemanticTerm → SemanticTerm :=
  Quotient.lift (fun term => ofTerm (term.renameRuntimeRegions rename))
    (fun _ _ equal => Quotient.sound (equal.renameRuntimeRegions rename))

theorem SemanticTerm.renameRuntimeRegions_ofTerm (rename : Identity → Identity) (term : Term) :
    (ofTerm term).renameRuntimeRegions rename = ofTerm (term.renameRuntimeRegions rename) := rfl

theorem Term.parameter_of_sameHead {id : Identity} {kind : Kind} {term : Term}
    (same : SameHead (.parameter id kind) term) : term = .parameter id kind := by
  cases term <;> simp_all [SameHead,Term.mapChildren]

theorem Term.substitute_children {term : Term} (notParameter : ∀ id kind, term ≠ .parameter id kind)
    (substitution : Substitution) :
    (term.substitute substitution).children = term.children.map (Term.substitute substitution) := by
  cases term <;> simp only [Term.substitute,Term.children,List.map_cons,List.map_nil,List.map_append]
  case parameter id kind => exact False.elim (notParameter id kind rfl)

theorem Term.substitute_head {term : Term} (notParameter : ∀ id kind, term ≠ .parameter id kind)
    (substitution : Substitution) :
    (term.substitute substitution).mapChildren (fun _ => .unit) = term.mapChildren (fun _ => .unit) := by
  cases term <;> simp only [Term.substitute,Term.mapChildren,List.map_map,Function.comp_def]
  case parameter id kind => exact False.elim (notParameter id kind rfl)

theorem RowEquivalent.substitute {left right : Term} (equal : RowEquivalent left right)
    (substitution : Substitution) : RowEquivalent (left.substitute substitution) (right.substitute substitution) := by
  classical
  refine RowEquivalent.rec
    (motive_1 := fun left right _ => RowEquivalent (left.substitute substitution) (right.substitute substitution))
    (motive_2 := fun left right _ => ListRel RowEquivalent
      (left.map (Term.substitute substitution)) (right.map (Term.substitute substitution)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ equal
  · intros; exact .refl
  · intro _ _ _ ih; exact .symm ih
  · intro _ _ _ _ _ first second; exact .trans first second
  · intro left right same _ children
    by_cases parameter : ∃ id kind, left = .parameter id kind
    · obtain ⟨id,kind,rfl⟩ := parameter
      obtain rfl := Term.parameter_of_sameHead same
      exact .refl
    · have notLeft : ∀ id kind, left ≠ .parameter id kind := by simpa using parameter
      have notRight : ∀ id kind, right ≠ .parameter id kind := by
        intro id kind equal
        subst right
        exact notLeft id kind (Term.parameter_of_sameHead same.symm)
      apply RowEquivalent.congr
      · change (left.substitute substitution).mapChildren _ = (right.substitute substitution).mapChildren _
        rw [Term.substitute_head notLeft,Term.substitute_head notRight]
        exact same
      · rw [Term.substitute_children notLeft,Term.substitute_children notRight]
        exact children
  · intro _ _ _ _ instances tails
    simp only [Term.substitute]
    exact .permutation (instances.map _) (tails.map _)
  · intros; simpa only [Term.substitute,List.map_cons,List.map_append] using
      (RowEquivalent.flatten (instances := _) (tails := _) (nested := _) (nestedTails := _))
  · intro _ _ _ _ _ ih
    simp only [Term.substitute,List.map_cons]
    exact .duplicate ih
  · intro _ _ _ _ _ ih
    simp only [Term.substitute,List.map_cons]
    exact .tailDuplicate ih
  · exact .nil
  · intro _ _ _ _ _ _ head tail; exact .cons head tail

theorem ListRel.maps {α β γ : Type} {relation : β → γ → Prop} (values : List α) (left : α → β) (right : α → γ)
    (related : ∀ value ∈ values, relation (left value) (right value)) :
    ListRel relation (values.map left) (values.map right) := by
  induction values with
  | nil => exact .nil
  | cons value values ih =>
      exact .cons (related value (by simp)) (ih (fun member present => related member (by simp [present])))

theorem Term.substitutions_rowEquivalent (term : Term) {left right : Substitution}
    (agree : ∀ id kind, RowEquivalent ((left.get id).getD (.parameter id kind))
      ((right.get id).getD (.parameter id kind))) :
    RowEquivalent (term.substitute left) (term.substitute right) := by
  cases term
  case parameter id kind => simpa only [Term.substitute] using agree id kind
  all_goals apply RowEquivalent.congr
  all_goals first
    | simp only [SameHead,Term.substitute,Term.mapChildren,List.map_map,Function.comp_def]
    | skip
  all_goals simp only [Term.children]
  all_goals first
    | exact .nil
    | apply ListRel.maps; intro child _; exact child.substitutions_rowEquivalent agree
    | apply ListRel.append
      all_goals apply ListRel.maps; intro child _; exact child.substitutions_rowEquivalent agree
    | repeat' apply ListRel.cons
      all_goals first
        | exact .nil
        | exact Term.substitutions_rowEquivalent _ agree
        | apply ListRel.maps; intro child _; exact child.substitutions_rowEquivalent agree
termination_by term

theorem SemanticTerm.renameRuntimeRegions_kind (rename : Identity → Identity) (term : SemanticTerm) :
    (term.renameRuntimeRegions rename).kind = term.kind := by
  induction term using Quotient.ind with
  | _ term => change (term.renameRuntimeRegions rename).kind = term.kind
              cases term <;> simp only [Term.renameRuntimeRegions,Term.kind]

end Glorious.Language
