import GloriousLanguage.Static

/-! Coherence consequences of actual declared heads. Selection does not
require eager normal forms, and associated result confluence is not assumed. -/
namespace Glorious.Language

theorem List.pair_value_unique {α β : Type} {entries : List (α × β)}
    (unique : (entries.map Prod.fst).Nodup) {key : α} {first second : β}
    (left : (key,first) ∈ entries) (right : (key,second) ∈ entries) : first = second := by
  induction entries with
  | nil => simp at left
  | cons entry entries ih =>
    have distinct := List.nodup_cons.mp unique
    rcases List.mem_cons.mp left with atHead | inTail
    · subst entry
      rcases List.mem_cons.mp right with atHead | inTail
      · exact congrArg Prod.snd atHead.symm
      · exact False.elim (distinct.1 (List.mem_map.mpr ⟨_,inTail,rfl⟩))
    · rcases List.mem_cons.mp right with atHead | inOtherTail
      · subst entry
        exact False.elim (distinct.1 (List.mem_map.mpr ⟨_,inTail,rfl⟩))
      · exact ih distinct.2 inTail inOtherTail

theorem ProgramWellFormed.implementation_identity_unique {program : Program}
    (valid : ProgramWellFormed program) {left right : ImplDefinition}
    (leftMember : Definition.implementation left ∈ program.declarations)
    (rightMember : Definition.implementation right ∈ program.declarations)
    (same : left.header.id = right.header.id) : left = right := by
  have unique : ((program.declarations.map (fun declaration => (declaration.header.id,declaration))).map Prod.fst).Nodup := by
    simpa only [List.map_map,Function.comp_def] using valid.2.1
  have first : (left.header.id,Definition.implementation left) ∈
      program.declarations.map (fun declaration => (declaration.header.id,declaration)) :=
    List.mem_map.mpr ⟨_,leftMember,rfl⟩
  have second : (left.header.id,Definition.implementation right) ∈
      program.declarations.map (fun declaration => (declaration.header.id,declaration)) := by
    rw [same]
    exact List.mem_map.mpr ⟨_,rightMember,rfl⟩
  have equal := List.pair_value_unique unique first second
  cases equal
  rfl

theorem ProgramWellFormed.associated_members_unique {program : Program} (valid : ProgramWellFormed program)
    {implementation : ImplDefinition} (member : Definition.implementation implementation ∈ program.declarations) :
    (implementation.associated.map Prod.fst).Nodup := by
  have declaration := (valid.2.2.2.2.1 _ member).2.1
  obtain ⟨_,_,_,_,_,members,_⟩ := declaration
  exact members

theorem SelectsImpl.declaration {program : Program} {context : Context} {trait : DeclId} {arguments : List Term}
    {negative : Bool} {implementation : ImplDefinition} {substitution : Substitution}
    (selected : SelectsImpl program context trait arguments negative implementation substitution) :
    Definition.implementation implementation ∈ program.declarations := by
  cases selected with
  | selected member _ _ _ _ => exact member

theorem SelectsImpl.unique {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {trait : DeclId} {arguments : List Term} {firstNegative secondNegative : Bool}
    {first second : ImplDefinition} {firstSub secondSub : Substitution}
    (left : SelectsImpl program context trait arguments firstNegative first firstSub)
    (right : SelectsImpl program context trait arguments secondNegative second secondSub) :
    first = second ∧ SubstitutionsConvertible program context firstSub secondSub := by
  cases left with
  | selected member trait _ matched _ =>
    cases right with
    | selected otherMember otherTrait _ otherMatched _ =>
      obtain ⟨same,arguments⟩ := valid.2.2.2.2.2 context _ _ member otherMember
        (trait.trans otherTrait.symm) _ _ _ matched otherMatched
      exact ⟨valid.implementation_identity_unique member otherMember same,arguments⟩

theorem SelectsImpl.implementation_unique {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {trait : DeclId} {arguments : List Term} {firstNegative secondNegative : Bool}
    {first second : ImplDefinition} {firstSub secondSub : Substitution}
    (left : SelectsImpl program context trait arguments firstNegative first firstSub)
    (right : SelectsImpl program context trait arguments secondNegative second secondSub) : first = second :=
  (left.unique valid right).1

theorem ProjectionDomain.unique {program : Program} {context : Context}
    {trait member : DeclId} {owners items : List Term} {first second : AssociatedDefinition}
    {firstOwner firstItem secondOwner secondItem : Substitution}
    (left : ProjectionDomain program context trait member owners items first firstOwner firstItem)
    (right : ProjectionDomain program context trait member owners items second secondOwner secondItem) :
    first = second ∧ firstOwner = secondOwner ∧ firstItem = secondItem := by
  cases left with
  | valid traitFound _ associatedFound _ ownerInst itemInst _ _ _ =>
    cases right with
    | valid otherTrait _ otherAssociated _ otherOwner otherItem _ _ _ =>
      have traitSame := Option.some.inj (traitFound.symm.trans otherTrait)
      have associatedSame := Option.some.inj (associatedFound.symm.trans otherAssociated)
      subst_vars
      exact ⟨rfl,ownerInst.2.2.trans otherOwner.2.2.symm,itemInst.2.2.trans otherItem.2.2.symm⟩

end Glorious.Language
