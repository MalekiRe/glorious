import GloriousLanguage.PrivateStorage

/-! Preservation of an actual vacant private slot through source execution.
The active task and writable binding frame provide operand exclusion; the
saved hook guard is deliberately permitted to retain its private handle. -/
namespace Glorious.Language.Execution

open Kernel


theorem Captures.private_slot {program : Kernel.Program} {context : Context} {before after : World}
    {captures : List Capture} {addresses : List Address} {id : Identity} {root : Root}
    (captured : Captures program context before captures addresses after)
    (well : before.WellFormed) (slot : before.PrivateSlot id root) :
    after.PrivateSlot id root ∧ ∀ address ∈ addresses, address.root ≠ id := by
  induction captured with
  | nil => exact ⟨slot,by simp⟩
  | owned _ _ temporary acquired _ ih =>
    have outside := temporary.choose_spec.fresh_avoids (slot.bound well)
    obtain ⟨finish,rest⟩ := ih (acquired.wellFormed (temporary.wellFormed well))
      (acquired.private_slot (temporary.private_slot well slot) outside)
    exact ⟨finish,fun address member => (List.mem_cons.mp member).elim (fun same => same ▸ outside) (rest address)⟩
  | borrowed _ _ _ temporary borrowed _ ih =>
    have outside := temporary.choose_spec.fresh_avoids (slot.bound well)
    obtain ⟨finish,rest⟩ := ih (FormsLoan.wellFormed (temporary.wellFormed well) borrowed)
      (borrowed.private_slot (temporary.private_slot well slot) outside)
    exact ⟨finish,fun address member => (List.mem_cons.mp member).elim (fun same => same ▸ outside) (rest address)⟩

theorem AtomStep.private_slot {program : Kernel.Program} {before after : State} {event : Option Event}
    {id : Identity} {root : Root} (step : AtomStep program before event after)
    (well : before.world.WellFormed) (slot : before.world.PrivateSlot id root)
    (taskOutside : id ∉ before.task.rootSupport) : after.world.PrivateSlot id root := by
  cases step
  all_goals try exact slot
  all_goals simp_all only [Task.rootSupport,List.mem_append,List.mem_cons,
    not_or,List.not_mem_nil,or_false]
  case constant written =>
    have current := slot.write written (Ne.symm taskOutside.2)
    exact ⟨current.found,current.vacant,current.safe,current.internalHome⟩
  case acquire acquired => exact acquired.private_slot slot (Ne.symm taskOutside.2)
  case borrow borrowed => exact borrowed.private_slot slot (Ne.symm taskOutside.2)
  case construct created | function created | operation created | label created =>
    exact created.private_slot slot (Ne.symm taskOutside.2)
  case closure captured _ _ created =>
    exact created.private_slot (captured.private_slot well slot).1 (Ne.symm taskOutside.2)

theorem LocalStep.private_slot {program : Kernel.Program} {before after : State} {event : Option Event}
    {id : Identity} {root : Root} (step : LocalStep program before event after)
    (well : before.world.WellFormed) (slot : before.world.PrivateSlot id root)
    (taskOutside : id ∉ before.task.rootSupport)
    (bindingOutside : ∀ context destination next rest,
      before.frames = .binding context destination next :: rest → destination.root ≠ id) :
    after.world.PrivateSlot id root := by
  cases step
  all_goals try exact slot
  all_goals simp_all only [Task.rootSupport,List.mem_append,List.mem_cons,
    not_or,List.not_mem_nil,or_false]
  case evaluate allocated | bind allocated | invoke allocated => exact allocated.private_slot (slot.bound well) slot
  case result kept | activationReturn kept _ _ | scopeReturn kept _ _ => exact (kept.private_slot well slot).1
  case transfer moved => exact moved.private_slot slot (Ne.symm taskOutside.2.1)
  case call consumed => exact consumed.private_slot slot
  case enter entered | enterTail entered _ _ _ _ => exact (entered.private_slot well slot taskOutside.2).1
  case bindReturn moved => exact moved.private_slot slot (bindingOutside _ _ _ _ rfl)
  case scope fresh _ => exact FreshRegion.private_slot fresh slot
  case patternBind bound => exact (bound.private_slot well slot).1
  case patternShell deconstructed =>
    cases deconstructed with
    | shell stored _ _ _ written => exact slot.write written (slot.stored_outside stored)
  case destroyHook temporary borrowed _ =>
    exact borrowed.private_slot (temporary.private_slot well slot)
      (temporary.choose_spec.fresh_avoids (slot.bound well))
  case destroyReference stored _ _ _ written => exact slot.write written (slot.stored_outside stored)
  case shellDone stored _ _ written => exact slot.write written (slot.stored_outside stored)
  case retire retired => exact retired.private_slot slot (Ne.symm taskOutside.1)
  case regionEnd ended =>
    obtain ⟨_,_,rfl⟩ := ended
    exact ⟨slot.found,slot.vacant,slot.safe,slot.internalHome⟩
  case loanEnd ended | releaseRoot _ _ ended | releaseChild _ _ ended => exact ended.private_slot slot

end Glorious.Language.Execution
