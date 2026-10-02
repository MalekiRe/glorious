import OwnershipMir.ShellSafety
import OwnershipMir.TreeFrame

namespace OwnershipMir

@[simp] theorem update_overwrite {α : Type} {n : Nat} (slots : Fin n → α) (i : Fin n) (a b : α) :
    update (update slots i a) i b = update slots i b := by
  funext j
  simp only [update]
  split <;> rfl

@[simp] theorem update_self {α : Type} {n : Nat} (slots : Fin n → α) (i : Fin n) :
    update slots i (slots i) = slots := by
  funext j
  by_cases same : j = i
  · subst j; simp [update]
  · simp [update, same]

def disposeAt {n : Nat} (root : Fin n) (path : List Direction) (layout : Layout) : Command n :=
  .dispose ⟨root, path, layout⟩

/-- Right-to-left fields, then the enclosing storage. Nested holes emit no
instructions; a wholly empty root still retires its binding. No custom hooks. -/
def cleanupTree {n : Nat} (root : Fin n) (path : List Direction) : Shape → List (Command n)
  | .hole layout => if path = [] then [disposeAt root path layout] else []
  | .nil => [disposeAt root path .nil]
  | .leaf kind => [disposeAt root path (.atom kind)]
  | .pair left right =>
    cleanupTree root (path ++ [.right]) right ++
      (cleanupTree root (path ++ [.left]) left ++
        [disposeAt root path (.pair (left.layout id) (right.layout id))])
  | .wrap shell body =>
    cleanupTree root (path ++ [.body]) body ++
      [disposeAt root path (.wrap shell (body.layout id))]

def clearFocused {n : Nat} (context : Context n) (root : Fin n) (frame : TreeFrame Kind) (shape : Shape) : Context n :=
  ⟨update context.slots root (frame.rebuild (shape.layout id) none), none⟩

theorem disposeAt_checked {n : Nat} (context : Context n) (root : Fin n) (frame : TreeFrame Kind)
    (shape : Shape) (empty : context.temp = none) (resident : context.slots root = some (frame.plug shape))
    (allowed : shape.disposable) (exhausted : shape.shallow) :
    Code.Checked Command.Checked context (sequence [disposeAt root frame.path (shape.layout id)])
      (clearFocused context root frame shape) := by
  have found : (Place.mk root frame.path (shape.layout id)).find context.slots =
      some ⟨some shape, frame.rebuild (shape.layout id)⟩ := by
    simp only [Place.find, resident]
    exact frame.focus _ _
  exact .act (.dispose empty found rfl rfl allowed exhausted) .halt

@[simp] theorem frame_left_clear (frame : TreeFrame Kind) (right : Shape) (layout : Layout) :
    (frame.compose (.left .hole right)).rebuild layout none = some (frame.plug (.pair (.hole layout) right)) :=
  frame.nested_rebuild _ (by intro h; cases h) layout

@[simp] theorem frame_right_clear (frame : TreeFrame Kind) (left : Shape) (layout : Layout) :
    (frame.compose (.right left .hole)).rebuild layout none = some (frame.plug (.pair left (.hole layout))) :=
  frame.nested_rebuild _ (by intro h; cases h) layout

@[simp] theorem frame_body_clear (frame : TreeFrame Kind) (shell : Shell) (layout : Layout) :
    (frame.compose (.body shell .hole)).rebuild layout none = some (frame.plug (.wrap shell (.hole layout))) :=
  frame.nested_rebuild _ (by intro h; cases h) layout

/-- General cleanup admission is derived structurally from current occupancy.
Every child transition feeds the next checker context; no future readiness,
whole-aggregate drop, or assumed cleanup execution is supplied. -/
theorem cleanupTree_checked {n : Nat} (root : Fin n) (shape : Shape) (frame : TreeFrame Kind)
    (context : Context n) (empty : context.temp = none)
    (resident : context.slots root = some (frame.plug shape)) (allowed : shape.disposable) :
    Code.Checked Command.Checked context (sequence (cleanupTree root frame.path shape))
      (clearFocused context root frame shape) := by
  induction shape generalizing frame context with
  | hole layout =>
    cases frame with
    | hole => exact disposeAt_checked context root .hole (.hole layout) empty resident allowed trivial
    | left f r =>
      have same : clearFocused context root (.left f r) (.hole layout) = context := by
        simp only [clearFocused, Tree.layout, TreeFrame.rebuild, Option.getD_none]
        rw [← resident, update_self]
        cases context
        simp_all
      rw [same]
      exact .halt
    | right l f =>
      have same : clearFocused context root (.right l f) (.hole layout) = context := by
        simp only [clearFocused, Tree.layout, TreeFrame.rebuild, Option.getD_none]
        rw [← resident, update_self]
        cases context
        simp_all
      rw [same]
      exact .halt
    | body s f =>
      have same : clearFocused context root (.body s f) (.hole layout) = context := by
        simp only [clearFocused, Tree.layout, TreeFrame.rebuild, Option.getD_none]
        rw [← resident, update_self]
        cases context
        simp_all
      rw [same]
      exact .halt
  | nil => exact disposeAt_checked context root frame .nil empty resident allowed trivial
  | leaf kind => exact disposeAt_checked context root frame (.leaf kind) empty resident allowed trivial
  | pair left right leftIH rightIH =>
    let rightDone : Context n := ⟨update context.slots root
      (some (frame.plug (.pair left (.hole (right.layout id))))), none⟩
    let bothDone : Context n := ⟨update context.slots root
      (some (frame.plug (.pair (.hole (left.layout id)) (.hole (right.layout id))))), none⟩
    have rightChecked : Code.Checked Command.Checked context
        (sequence (cleanupTree root (frame.path ++ [.right]) right)) rightDone := by
      simpa [clearFocused, TreeFrame.path, rightDone] using
        rightIH (frame.compose (.right left .hole)) context empty
          (by simpa [TreeFrame.plug] using resident) allowed.2
    have leftChecked : Code.Checked Command.Checked rightDone
        (sequence (cleanupTree root (frame.path ++ [.left]) left)) bothDone := by
      simpa [clearFocused, TreeFrame.path, rightDone, bothDone] using
        leftIH (frame.compose (.left .hole (.hole (right.layout id)))) rightDone rfl
          (by simp [rightDone, TreeFrame.plug]) allowed.1
    have release : Code.Checked Command.Checked bothDone
        (sequence [disposeAt root frame.path (.pair (left.layout id) (right.layout id))])
        (clearFocused context root frame (.pair left right)) := by
      simpa [clearFocused, bothDone, Tree.layout] using
        disposeAt_checked bothDone root frame (.pair (.hole (left.layout id)) (.hole (right.layout id)))
          rfl (by simp [bothDone]) ⟨trivial, trivial⟩ trivial
    exact sequence_checked_append rightChecked (sequence_checked_append leftChecked release)
  | wrap shell body ih =>
    let bodyDone : Context n := ⟨update context.slots root
      (some (frame.plug (.wrap shell (.hole (body.layout id))))), none⟩
    have bodyChecked : Code.Checked Command.Checked context
        (sequence (cleanupTree root (frame.path ++ [.body]) body)) bodyDone := by
      simpa [clearFocused, TreeFrame.path, bodyDone] using
        ih (frame.compose (.body shell .hole)) context empty
          (by simpa [TreeFrame.plug] using resident) allowed.2
    have release : Code.Checked Command.Checked bodyDone
        (sequence [disposeAt root frame.path (.wrap shell (body.layout id))])
        (clearFocused context root frame (.wrap shell body)) := by
      simpa [clearFocused, bodyDone, Tree.layout] using
        disposeAt_checked bodyDone root frame (.wrap shell (.hole (body.layout id)))
          rfl (by simp [bodyDone]) ⟨allowed.1, trivial⟩ trivial
    exact sequence_checked_append bodyChecked release

/-- Finite cleanup has an actual terminating execution, derived from local
progress. Structured user code can still diverge before reaching scope exit. -/
theorem sequence_run {n : Nat} {signature : Signature} (commands : List (Command n))
    {before after : Context n} (checked : Code.Checked Command.Checked before (sequence commands) after)
    {state : State n} (typed : state.Typed signature before) :
    ∃ result, Run (Step Command.exec) ⟨sequence commands, state⟩ ⟨.halt, result⟩ ∧
      result.Typed signature after ∧ Conserves signature state result := by
  obtain ⟨result, executed, final, conserved⟩ := Block.checked_exec Command.Checked.sound commands checked typed
  exact ⟨result, Block.exec_run commands executed .halt, final, conserved⟩

end OwnershipMir
