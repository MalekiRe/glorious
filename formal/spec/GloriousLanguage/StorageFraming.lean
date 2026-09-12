import GloriousLanguage.TransferPreservation

/-! Full resident framing for non-overlapping physical storage updates. -/
namespace Glorious.Language

theorem Value.replace_disjoint {before after : Value} {path observed : List Nat} {replacement : Option Value}
    (written : before.replace path replacement = some after)
    (outside : ¬ ∃ suffix, observed = path ++ suffix) (reverse : ¬ ∃ suffix, path = observed ++ suffix) :
    after.atPath observed = before.atPath observed := by
  induction path generalizing before after observed with
  | nil => exact False.elim (outside ⟨observed,rfl⟩)
  | cons index path ih =>
    cases observed with
    | nil => exact False.elim (reverse ⟨index :: path,rfl⟩)
    | cons other observed =>
      rcases Value.replace_cons_shape written with ⟨field,found,⟨rfl,rfl⟩ | ⟨child,changed,rfl,replaced,rfl⟩⟩
      · have different : index ≠ other := by
          intro same
          subst other
          exact outside ⟨observed,rfl⟩
        simp [Value.atPath,Value.withFields,Value.fields,List.getElem?_set_ne different]
      · by_cases same : index = other
        · subst other
          have bound := List.getElem?_eq_some_iff.mp found |>.1
          change ((before.fields.set index (some changed))[index]?.join >>= fun child => child.atPath observed) = _
          rw [List.getElem?_set_self bound]
          simp only [Value.atPath,found,Option.join_some]
          exact ih replaced
            (fun ⟨suffix,equal⟩ => outside ⟨suffix,by simp [equal]⟩)
            (fun ⟨suffix,equal⟩ => reverse ⟨suffix,by simp [equal]⟩)
        · simp [Value.atPath,Value.withFields,Value.fields,List.getElem?_set_ne same]

/-- Full value framing, including capture fields rather than only their
headers, for storage handoff and invocation-reference cleanup. -/
theorem World.write_disjoint {before after : World} {address observed : Address} {value : Option Value}
    (written : before.write address value = some after) (outside : ¬ address.Overlaps observed) :
    after.read observed = before.read observed := by
  have update := World.write_value_update written
  unfold World.write at written
  cases selected : before.root address with
  | none => simp [selected] at written
  | some root =>
    obtain ⟨found,live,generation⟩ := World.root_found selected
    simp only [selected] at written
    dsimp at written
    by_cases sameRoot : observed.root = address.root
    · by_cases sameGeneration : observed.generation = address.generation
      · have pathOutside : ¬ ∃ suffix, observed.fields = address.fields ++ suffix :=
          fun included => outside ((show address.Prefix observed from ⟨sameRoot.symm,sameGeneration.symm,included⟩).overlaps)
        have reverse : ¬ ∃ suffix, address.fields = observed.fields ++ suffix :=
          fun included => outside ⟨sameRoot.symm,sameGeneration.symm,Or.inl included⟩
        split at written
        next empty =>
          have fields : address.fields = [] := by simpa using empty
          exact False.elim (pathOutside ⟨observed.fields,by simp [fields]⟩)
        next =>
          cases resident : root.value with
          | none => simp [resident] at written
          | some tree =>
            simp only [resident] at written
            dsimp at written
            cases replaced : tree.replace address.fields value with
            | none => simp [replaced] at written
            | some changed =>
              simp only [replaced] at written
              dsimp at written
              cases (Option.some.inj written).symm
              have observedGeneration : root.generation = observed.generation := generation.trans sameGeneration.symm
              simpa [World.read,World.root,Table.get_set,sameRoot,found,live,observedGeneration,resident]
                using Value.replace_disjoint replaced pathOutside reverse
      · rcases update with ⟨changedRoot,_,changedFound,equal⟩
        have same := Option.some.inj (changedFound.symm.trans found)
        subst changedRoot
        subst after
        have different : root.generation ≠ observed.generation := by omega
        simp [World.read,World.root,sameRoot,Table.get_set,found,live,different]
    · rcases update with ⟨_,_,_,equal⟩
      subst after
      simp [World.read,World.root,Table.get_set_other _ _ _ _ sameRoot]

end Glorious.Language
