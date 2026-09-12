import GloriousLanguage.PrivateLocalControl
import GloriousLanguage.PrivateForeignPreservation
import GloriousLanguage.ControlOriginPreservation

/-! The complete executable relation preserves a saved private caller slot
until the actual first pop of its hook guard. Finite-run factorization follows
all six transition families; it never assumes future stack privacy. -/
namespace Glorious.Language.Execution

open Kernel

theorem Step.private_guard {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {event : Option Event}
    {id owner savedScope loan : Identity} {root : Root} {inner outer : List Frame}
    {caller : Context} {address handle : Address} {authority : Authority} {next : Task}
    (step : Step program host before event after)
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (admitted : before.ControlWellFormed) (slot : before.world.PrivateSlot id root)
    (home : root.home = .temporary owner savedScope) (control : PrivateControl id owner inner before.task)
    (stack : before.frames = inner ++ .hook caller address authority handle loan next :: outer)
    (outerOutside : id ∉ outer.flatMap Frame.rootSupport)
    (noLeave : ∀ brand, event ≠ some (.leave brand))
    (noReplay : ∀ key last, event ≠ some (.replay key last))
    (noOperation : ∀ operation arguments, event ≠ some (.perform operation arguments)) :
    after.world.PrivateSlot id root ∧
      ((∃ remaining, after.frames = remaining ++ .hook caller address authority handle loan next :: outer ∧
        PrivateControl id owner remaining after.task) ∨
      (LocalStep program before event after ∧ event = none ∧ inner = [] ∧ after.frames = outer)) := by
  have ownerBound : owner < before.nextActivation :=
    admitted.activations.homes id root slot.found owner (by simp [HomeOwnedByActivation,home])
  rcases step with localStep | atom | effect | branch | primitive | foreign
  · refine ⟨localStep.private_slot typed.1 slot control.1
      (fun context destination body rest frames => control.binding_outside (stack.symm.trans frames)),?_⟩
    exact (localStep.private_control typed.1 slot home ownerBound control stack).elim Or.inl
      (fun returned => Or.inr ⟨localStep,returned⟩)
  · have frames : after.frames = before.frames := by cases atom <;> rfl
    exact ⟨atom.private_slot typed.1 slot control.1,
      Or.inl ⟨inner,frames.trans stack,atom.private_control typed.1 slot control⟩⟩
  · exact ⟨effect.private_slot valid inventory typed admitted.suspensions slot control.2.2.1 noReplay,
      Or.inl (effect.private_control valid inventory typed admitted.suspensions slot home ownerBound control stack noOperation noReplay)⟩
  · obtain ⟨frames,afterControl⟩ := branch.private_control typed.1 slot control noLeave
    exact ⟨branch.private_slot typed.1 slot control.1 control.2.2.1,
      Or.inl ⟨inner,frames.trans stack,afterControl⟩⟩
  · have frames : after.frames = before.frames := by cases primitive <;> rfl
    exact ⟨primitive.private_slot typed.1 slot control.1,
      Or.inl ⟨inner,frames.trans stack,primitive.private_control control⟩⟩
  · exact ⟨foreign.private_slot valid inventory lawful typed slot control.1,
      Or.inl (foreign.private_control valid inventory lawful typed slot control stack outerOutside)⟩

/-- The return alternative identifies a concrete silent source step in the
original run, with the exact same slot on both sides. The factorized suffix
carries no slot-privacy obligation: its caller may retire the handle. -/
theorem Run.private_until_guard_pop {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event}
    {id owner savedScope loan : Identity} {root : Root} {inner outer : List Frame}
    {caller : Context} {address handle : Address} {authority : Authority} {next : Task}
    (run : Run program host before trace after)
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (admitted : before.ControlWellFormed) (slot : before.world.PrivateSlot id root)
    (home : root.home = .temporary owner savedScope) (control : PrivateControl id owner inner before.task)
    (stack : before.frames = inner ++ .hook caller address authority handle loan next :: outer)
    (outerOutside : id ∉ outer.flatMap Frame.rootSupport)
    (safe : ∀ event ∈ trace, (∀ brand, event ≠ .leave brand) ∧
      (∀ key last, event ≠ .replay key last) ∧ (∀ operation arguments, event ≠ .perform operation arguments)) :
    (∃ remaining, after.frames = remaining ++ .hook caller address authority handle loan next :: outer ∧
      after.world.PrivateSlot id root ∧ PrivateControl id owner remaining after.task) ∨
    (∃ returning returned first last,
      trace = first ++ last ∧ Run program host before first returning ∧
      LocalStep program returning none returned ∧ Run program host returned last after ∧
      returning.frames = .hook caller address authority handle loan next :: outer ∧ returned.frames = outer ∧
      returning.world.PrivateSlot id root ∧ returned.world.PrivateSlot id root ∧
      PrivateControl id owner [] returning.task) := by
  induction run generalizing inner with
  | refl => exact Or.inl ⟨inner,stack,slot,control⟩
  | @silent before middle after trace step rest ih =>
    obtain ⟨middleSlot,middleControl⟩ := step.private_guard valid inventory lawful typed admitted slot home control stack outerOutside
      (by simp) (by simp) (by simp)
    rcases middleControl with ⟨remaining,middleFrames,middleControl⟩ | ⟨localStep,_,rfl,middleFrames⟩
    · rcases ih (step.worldTyped valid inventory lawful typed) (step.controlWellFormed valid inventory lawful typed admitted)
        middleSlot middleControl middleFrames safe with final | ⟨returning,returned,first,last,traceEq,lead,popped,finish,frames,afterFrames,kept,afterKept,returnControl⟩
      · exact Or.inl final
      · exact Or.inr ⟨returning,returned,first,last,traceEq,.silent step lead,popped,finish,frames,afterFrames,kept,afterKept,returnControl⟩
    · exact Or.inr ⟨before,middle,[],trace,rfl,.refl,localStep,rest,stack,middleFrames,slot,middleSlot,control⟩
  | @visible before middle after event trace step rest ih =>
    have safeEvent := safe event List.mem_cons_self
    obtain ⟨middleSlot,middleControl⟩ := step.private_guard valid inventory lawful typed admitted slot home control stack outerOutside
      (fun brand equal => safeEvent.1 brand (Option.some.inj equal))
      (fun key last equal => safeEvent.2.1 key last (Option.some.inj equal))
      (fun operation arguments equal => safeEvent.2.2 operation arguments (Option.some.inj equal))
    rcases middleControl with ⟨remaining,middleFrames,middleControl⟩ | ⟨_,impossible,_⟩
    · rcases ih (step.worldTyped valid inventory lawful typed) (step.controlWellFormed valid inventory lawful typed admitted)
        middleSlot middleControl middleFrames (fun observed member => safe observed (List.mem_cons_of_mem event member)) with
        final | ⟨returning,returned,first,last,traceEq,lead,popped,finish,frames,afterFrames,kept,afterKept,returnControl⟩
      · exact Or.inl final
      · exact Or.inr ⟨returning,returned,event :: first,last,by simp only [traceEq,List.cons_append],
          .visible step lead,popped,finish,frames,afterFrames,kept,afterKept,returnControl⟩
    · cases impossible

end Glorious.Language.Execution
