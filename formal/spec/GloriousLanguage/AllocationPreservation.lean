import GloriousLanguage.AllocationFraming
import GloriousLanguage.LayoutContext

namespace Glorious.Language

theorem Allocates.fresh_root {program : Program} {before after : World}
    {home region type layout mutable address}
    (allocated : Allocates program before home region type layout mutable address after) :
    address.root = before.nextRoot ∧ after.nextRoot = before.nextRoot + 1 := by
  cases allocated
  exact ⟨rfl,rfl⟩

theorem Allocates.layoutOf {program : Program} {before after : World}
    {home : Home} {region : Identity} {type : Term} {layout : Layout} {mutable : Bool} {address : Address}
    (allocated : Allocates program before home region type layout mutable address after)
    {module : ModuleId} {unsafeAllowed : Bool} :
    LayoutOf program ⟨[],[],0,module,unsafeAllowed,{}⟩ type layout := by
  cases allocated with
  | fresh request extent =>
    obtain ⟨module,unsafeAllowed,derived⟩ := request.layout_of
    exact derived.runtime_context

/-- Actual allocation realizes the fresh root from the request's own closed
layout evidence and retains every already-realized live root. -/
theorem Allocates.layoutRealized {program : Program} {before after : World}
    {home : Home} {region : Identity} {type : Term} {layout : Layout} {mutable : Bool} {address : Address}
    (allocated : Allocates program before home region type layout mutable address after)
    {module : ModuleId} {unsafeAllowed : Bool}
    (retained : World.LayoutRealized program before module unsafeAllowed) :
    World.LayoutRealized program after module unsafeAllowed := by
  cases allocated with
  | fresh request extent =>
    intro id root found live
    by_cases fresh : id = before.nextRoot
    · subst fresh
      rw [Table.get_set] at found
      have same := Option.some.inj found
      subst same
      obtain ⟨sourceModule,sourceUnsafe,derived⟩ := request.layout_of
      exact derived.runtime_context
    · rw [Table.get_set_other _ _ _ _ fresh] at found
      exact retained id root found live


theorem Allocates.worldTypedWithOrigins {program : Kernel.Program} {before after : World} {home region type layout mutable address}
    {originBound : Identity} (typed : Typing.WorldTypedWithOrigins program before originBound)
    (allocated : Allocates program.declarations before home region type layout mutable address after) :
    Typing.WorldTypedWithOrigins program after originBound := by
  refine ⟨allocated.wellFormedWithOrigins typed.1,?_,?_,?_,allocated.layoutRealized typed.2.2.2.2⟩
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
      · exact typed.2.2.2.1 id root (by simpa only [Table.get_set_other _ _ _ _ fresh] using found)

theorem Allocates.worldTyped {program : Kernel.Program} {before after : World} {home region type layout mutable address}
    (typed : Typing.WorldTyped program before)
    (allocated : Allocates program.declarations before home region type layout mutable address after) :
    Typing.WorldTyped program after := by
  have checked := allocated.worldTypedWithOrigins typed
  cases allocated
  exact checked

end Glorious.Language
