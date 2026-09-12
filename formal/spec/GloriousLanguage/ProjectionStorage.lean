import GloriousLanguage.ProjectionResolution
import GloriousLanguage.Preservation

/-! Recursive projection composition and storage-location transport. Dynamic
indices compose through the authoritative resolver; they do not require a
separate prefix/suffix evaluator or a second operand snapshot. -/
namespace Glorious.Language

theorem World.Stores.child {world : World} {address : Address} {value child : Value} {index : Nat}
    (stored : world.Stores address value) (field : value.fields[index]? = some (some child)) :
    world.Stores (address.child index) child := by
  change world.read { address with fields := address.fields ++ [index] } = some child
  rw [World.read_append,stored]
  simp [Value.atPath,field]

theorem World.Stores.vacant_child {world : World} {address : Address} {value : Value} {index : Nat}
    (stored : world.Stores address value) (field : value.fields[index]? = some none) :
    world.Vacant (address.child index) := by
  obtain ⟨root,selected,rest⟩ := Option.bind_eq_some_iff.mp stored
  obtain ⟨whole,contents,located⟩ := Option.bind_eq_some_iff.mp rest
  exact ⟨root,selected,Or.inr ⟨address.fields,index,whole,rfl,contents,value,located,field⟩⟩

namespace Kernel

theorem ResolvesProjections.nonempty_stored {world : World} {environment : Environment}
    {base result : Address} {authority permission : Authority} {projections : List Projection}
    (resolved : ResolvesProjections world environment base authority projections result permission)
    (nonempty : projections ≠ []) : ∃ value, world.Stores base value := by
  induction resolved with
  | nil => exact False.elim (nonempty rfl)
  | field stored => exact ⟨_,stored⟩
  | vacantField stored => exact ⟨_,stored⟩
  | index _ _ _ _ _ _ _ ih => exact ih (by simp)
  | dereference stored => exact ⟨_,stored⟩

/-- Resolution preserves real storage location, including a vacant final
field. Dereferencing uses the existing live-loan location invariant. -/
theorem ResolvesProjections.located {world : World} {environment : Environment}
    {base result : Address} {authority permission : Authority} {projections : List Projection}
    (loans : world.LiveLoanLocations) (baseLocated : world.Located base)
    (resolved : ResolvesProjections world environment base authority projections result permission) :
    world.Located result := by
  induction resolved with
  | nil => exact baseLocated
  | field stored field rest ih => exact ih (Or.inl ⟨_,stored.child field⟩)
  | vacantField stored field => exact Or.inr (stored.vacant_child field)
  | index _ _ _ _ _ _ _ ih => exact ih baseLocated
  | dereference _ _ _ _ found live _ _ ih => exact ih (loans _ _ found live)

theorem ResolvesPlace.located {world : World} {environment : Environment} {place : Place}
    {result : Address} {permission : Authority} (loans : world.LiveLoanLocations)
    (bindings : ∀ binding ∈ environment, world.Located binding.address)
    (resolved : ResolvesPlace world environment place result permission) : world.Located result := by
  cases resolved with
  | localSlot selected resolved => exact resolved.located loans (bindings _ selected.1)

/-- Arbitrary projection sequences compose, so a later dynamic index is
evaluated in the same environment after every earlier field/reference hop. -/
theorem ResolvesProjections.append {world : World} {environment : Environment}
    {base middle result : Address} {authority intermediate permission : Authority}
    {first last : List Projection}
    (initial : ResolvesProjections world environment base authority first middle intermediate)
    (suffix : ResolvesProjections world environment middle intermediate last result permission) :
    ResolvesProjections world environment base authority (first ++ last) result permission := by
  induction initial generalizing result permission last with
  | nil => exact suffix
  | field stored field rest ih => exact .field stored field (ih suffix)
  | vacantField stored field =>
      cases last with
      | nil => cases suffix; exact .vacantField stored field
      | cons next rest =>
          exact False.elim ((stored.vacant_child field).not_stored (suffix.nonempty_stored (by simp)))
  | @index base authority localSlot projections binding value integer result permission
      selected stored head initialized permitted nonnegative rest ih =>
      exact .index selected stored head initialized permitted nonnegative (ih suffix)
  | dereference stored head initialized permitted found live view rest ih =>
      exact .dereference stored head initialized permitted found live view (ih suffix)

theorem ResolvesProjections.split {world : World} {environment : Environment}
    {base result : Address} {authority permission : Authority} {projections first last : List Projection}
    (resolved : ResolvesProjections world environment base authority projections result permission)
    (sequence : projections = first ++ last) :
    ∃ middle intermediate, ResolvesProjections world environment base authority first middle intermediate ∧
      ResolvesProjections world environment middle intermediate last result permission := by
  induction resolved generalizing first last with
  | nil =>
      have empty : first = [] ∧ last = [] := by simpa using sequence.symm
      rcases empty with ⟨rfl,rfl⟩
      exact ⟨_,_,.nil,.nil⟩
  | field stored field rest ih =>
      cases first with
      | nil =>
          simp only [List.nil_append] at sequence
          subst last
          exact ⟨_,_,.nil,.field stored field rest⟩
      | cons projection first =>
          obtain ⟨rfl,tail⟩ := List.cons.inj sequence
          obtain ⟨middle,intermediate,initial,suffix⟩ := ih tail
          exact ⟨middle,intermediate,.field stored field initial,suffix⟩
  | vacantField stored field =>
      cases first with
      | nil =>
          simp only [List.nil_append] at sequence
          subst last
          exact ⟨_,_,.nil,.vacantField stored field⟩
      | cons projection first =>
          obtain ⟨rfl,tail⟩ := List.cons.inj sequence
          have empty : first = [] ∧ last = [] := by simpa using tail.symm
          rcases empty with ⟨rfl,rfl⟩
          exact ⟨_,_,.vacantField stored field,.nil⟩
  | @index base authority localSlot projections binding value integer result permission
      selected stored head initialized permitted nonnegative rest ih =>
      cases first with
      | nil =>
          simp only [List.nil_append] at sequence
          subst last
          exact ⟨_,_,.nil,.index selected stored head initialized permitted nonnegative rest⟩
      | cons projection first =>
          obtain ⟨rfl,tail⟩ := List.cons.inj sequence
          obtain ⟨middle,intermediate,initial,suffix⟩ :=
            ih (first := .field integer.toNat :: first) (last := last) (congrArg (List.cons _) tail)
          exact ⟨middle,intermediate,.index selected stored head initialized permitted nonnegative initial,suffix⟩
  | dereference stored head initialized permitted found live view rest ih =>
      cases first with
      | nil =>
          simp only [List.nil_append] at sequence
          subst last
          exact ⟨_,_,.nil,.dereference stored head initialized permitted found live view rest⟩
      | cons projection first =>
          obtain ⟨rfl,tail⟩ := List.cons.inj sequence
          obtain ⟨middle,intermediate,initial,suffix⟩ := ih tail
          exact ⟨middle,intermediate,.dereference stored head initialized permitted found live view initial,suffix⟩

theorem ResolvesProjections.append_iff {world : World} {environment : Environment}
    {base result : Address} {authority permission : Authority} {first last : List Projection} :
    ResolvesProjections world environment base authority (first ++ last) result permission ↔
      ∃ middle intermediate, ResolvesProjections world environment base authority first middle intermediate ∧
        ResolvesProjections world environment middle intermediate last result permission :=
  ⟨fun resolved => resolved.split rfl,fun ⟨_,_,initial,suffix⟩ => initial.append suffix⟩

end Kernel
end Glorious.Language
