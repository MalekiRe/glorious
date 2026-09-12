import GloriousLanguage.AllocationFraming

namespace Glorious.Language

theorem Allocates.worldTypedWithOrigins {program : Kernel.Program} {before after : World} {home region type layout mutable address}
    {originBound : Identity} (typed : Typing.WorldTypedWithOrigins program before originBound)
    (allocated : Allocates program.declarations before home region type layout mutable address after) :
    Typing.WorldTypedWithOrigins program after originBound := by
  refine ⟨allocated.wellFormedWithOrigins typed.1,?_,?_,?_⟩
  · intro observed value resident
    have old := (allocated.resident typed.1).mp resident
    apply (typed.2.1 observed value old).transport
    · intro id loan found _
      refine ⟨?_,fun _ type => type.retained (fun _ selected => allocated.roots typed.1 selected) (allocated.read typed.1)⟩
      cases allocated
      exact found
    · cases allocated; rfl
    · intro pointer origin id source
      obtain ⟨root,selected,address,bound⟩ := origin id source
      exact ⟨root,allocated.roots typed.1 selected,address,bound⟩
  · intro id root value found contents
    cases allocated
    by_cases fresh : id = before.nextRoot
    · subst id
      simp only [Table.get_set] at found
      cases found
      cases contents
    · exact typed.2.2.1 id root value
        (by simpa only [Table.get_set_other _ _ _ _ fresh] using found) contents
  · intro id root found
    cases allocated with
    | fresh request _ =>
      by_cases fresh : id = before.nextRoot
      · subst id
        simp only [Table.get_set] at found
        cases found
        exact request.type_supported
      · exact typed.2.2.2 id root (by simpa only [Table.get_set_other _ _ _ _ fresh] using found)

theorem Allocates.worldTyped {program : Kernel.Program} {before after : World} {home region type layout mutable address}
    (typed : Typing.WorldTyped program before)
    (allocated : Allocates program.declarations before home region type layout mutable address after) :
    Typing.WorldTyped program after := by
  have checked := allocated.worldTypedWithOrigins typed
  cases allocated
  exact checked

end Glorious.Language
