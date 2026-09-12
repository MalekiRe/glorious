import GloriousLanguage.Control

/-! Callback runtime ownership follows real control continuations. Coverage
records which outer callbacks a host session actually received; liveness uses
the model's existing runtime inventory, never a second runtime registry. -/
namespace Glorious.Language

namespace Execution

def Task.CallbackCovers (ambient : List Identity) : Task → Prop
  | .destroy _ _ _ next | .destroyFields _ _ _ _ next | .finishShell _ _ next
  | .retire _ next | .cleanup _ _ next | .closeRegion _ next | .closeLoan _ next
  | .releaseLoan _ next | .transfer _ _ _ next | .cancel _ _ next => next.CallbackCovers ambient
  | .foreign session _ => ambient ⊆ session.heldRuntimes
  | .foreignCallbackReturned session entry _ _ => ambient ⊆ entry.runtime :: session.heldRuntimes
  | _ => True

def Frame.CallbackCovers (ambient : List Identity) : Frame → Prop
  | .hook _ _ _ _ _ next => next.CallbackCovers ambient
  | .hostCallback session _ _ _ _ => ambient ⊆ session.heldRuntimes
  | _ => True

def FramesCallbackCovers : List Frame → Prop
  | [] => True
  | frame :: rest => frame.CallbackCovers (Foreign.AmbientRuntimes rest) ∧ FramesCallbackCovers rest

def State.CallbackControl (state : State) : Prop :=
  state.task.CallbackCovers (Foreign.AmbientRuntimes state.frames) ∧ FramesCallbackCovers state.frames

def State.callbackRuntimes (state : State) : List Identity :=
  state.task.callbackRuntimes ++ Foreign.AmbientRuntimes state.frames

theorem Task.CallbackCovers.mono {task : Task} {before after : List Identity}
    (covered : task.CallbackCovers before) (smaller : after ⊆ before) : task.CallbackCovers after := by
  induction task <;> simp_all only [Task.CallbackCovers]
  all_goals exact List.Subset.trans smaller covered

theorem Frame.CallbackCovers.mono {frame : Frame} {before after : List Identity}
    (covered : frame.CallbackCovers before) (smaller : after ⊆ before) : frame.CallbackCovers after := by
  cases frame <;> simp_all only [Frame.CallbackCovers]
  · exact covered.mono smaller
  · exact List.Subset.trans smaller covered

theorem Task.ForeignFree.callback_runtimes {task : Task} (free : task.ForeignFree) :
    task.callbackRuntimes = [] := by
  induction task <;> simp_all only [Task.ForeignFree,Task.callbackRuntimes]

theorem Task.ForeignFree.callback_covers {task : Task} (free : task.ForeignFree) (ambient : List Identity) :
    task.CallbackCovers ambient := by
  induction task <;> simp_all only [Task.ForeignFree,Task.CallbackCovers]

theorem Frame.ForeignFree.callback_runtimes {frame : Frame} (free : frame.ForeignFree) :
    frame.callbackRuntimes = [] := by
  cases frame <;> simp_all only [Frame.ForeignFree,Frame.callbackRuntimes]
  exact free.callback_runtimes

theorem Frame.ForeignFree.callback_covers {frame : Frame} (free : frame.ForeignFree) (ambient : List Identity) :
    frame.CallbackCovers ambient := by
  cases frame <;> simp_all only [Frame.ForeignFree,Frame.CallbackCovers]
  exact free.callback_covers ambient

theorem FramesCallbackCovers.tail {frame : Frame} {rest : List Frame}
    (covered : FramesCallbackCovers (frame :: rest)) : FramesCallbackCovers rest := covered.2

theorem FramesCallbackCovers.suffix {leading rest : List Frame}
    (covered : FramesCallbackCovers (leading ++ rest)) : FramesCallbackCovers rest := by
  induction leading with
  | nil => exact covered
  | cons _ _ ih => exact ih covered.2

theorem FramesCallbackCovers.free_append {leading rest : List Frame}
    (free : ∀ frame ∈ leading, frame.ForeignFree) (covered : FramesCallbackCovers rest) :
    FramesCallbackCovers (leading ++ rest) := by
  induction leading with
  | nil => exact covered
  | cons frame leading ih =>
    exact ⟨(free frame List.mem_cons_self).callback_covers _,
      ih (fun frame member => free frame (List.mem_cons_of_mem _ member))⟩

theorem FreshNamedFrame.foreign_free {function : Kernel.Function} {caller : Context} {brand region : Identity} :
    ∀ frame ∈ FreshNamedFrame function caller brand region, frame.ForeignFree := by
  simp only [FreshNamedFrame]
  split <;> simp [Frame.ForeignFree]

theorem TailFrames.callback_covers {frames rest : List Frame} {activation : Identity} {caller : Context}
    {regions : List Identity} (tail : TailFrames frames activation caller regions rest)
    (covered : FramesCallbackCovers frames) : FramesCallbackCovers rest := by
  induction tail with
  | activation => exact covered.2
  | scope _ ih | label _ ih => exact ih covered.2

theorem TailFrames.callback_runtimes {frames rest : List Frame} {activation : Identity} {caller : Context}
    {regions : List Identity} (tail : TailFrames frames activation caller regions rest) :
    Foreign.AmbientRuntimes frames = Foreign.AmbientRuntimes rest := by
  induction tail <;> simp_all only [Foreign.AmbientRuntimes,List.flatMap_cons,Frame.callbackRuntimes,List.nil_append]

theorem CloseRegions.callback_runtimes {regions : List Identity} {next : Task} :
    (CloseRegions regions next).callbackRuntimes = next.callbackRuntimes := by
  unfold CloseRegions
  generalize regions.eraseDups = remaining
  induction remaining with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem CloseRegions.callback_covers {regions : List Identity} {next : Task} {ambient : List Identity} :
    (CloseRegions regions next).CallbackCovers ambient ↔ next.CallbackCovers ambient := by
  unfold CloseRegions
  generalize regions.eraseDups = remaining
  induction remaining with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem DisposesReservations.callback_runtimes {context : Context} {places : List ResolvedPlace} {next : Task} :
    (DisposesReservations context places next).callbackRuntimes = next.callbackRuntimes := by
  induction places with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem DisposesReservations.callback_covers {context : Context} {places : List ResolvedPlace} {next : Task}
    {ambient : List Identity} :
    (DisposesReservations context places next).CallbackCovers ambient ↔ next.CallbackCovers ambient := by
  induction places with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem Task.retire_fold_callback_runtimes {addresses : List Address} {next : Task} :
    (addresses.foldr (fun address task => .retire address.root task) next).callbackRuntimes = next.callbackRuntimes := by
  induction addresses with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem Task.retire_fold_callback_covers {addresses : List Address} {next : Task} {ambient : List Identity} :
    (addresses.foldr (fun address task => .retire address.root task) next).CallbackCovers ambient ↔ next.CallbackCovers ambient := by
  induction addresses with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem Relocation.frame_foreign_free {map : Relocation} {frame : Frame} (free : frame.ForeignFree) :
    (map.frame frame).ForeignFree := by
  cases frame <;> exact free

end Execution

namespace Foreign

open Kernel Execution

theorem AmbientRuntimes.free {frames : List Frame} (free : ∀ frame ∈ frames, frame.ForeignFree) :
    AmbientRuntimes frames = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  exact fun frame member => (free frame member).callback_runtimes

theorem AmbientRuntimes.append (left right : List Frame) :
    AmbientRuntimes (left ++ right) = AmbientRuntimes left ++ AmbientRuntimes right :=
  List.flatMap_append

theorem AmbientRuntimes.cons (frame : Frame) (rest : List Frame) :
    AmbientRuntimes (frame :: rest) = frame.callbackRuntimes ++ AmbientRuntimes rest := rfl

theorem AmbientRuntimes.nil : AmbientRuntimes [] = [] := rfl

theorem _root_.Glorious.Language.Execution.FreshNamedFrame.callback_runtimes
    {function : Kernel.Function} {caller : Execution.Context} {brand region : Identity} :
    AmbientRuntimes (FreshNamedFrame function caller brand region) = [] :=
  AmbientRuntimes.free FreshNamedFrame.foreign_free

theorem _root_.Glorious.Language.Execution.FramesCallbackCovers.free_append_iff {leading rest : List Frame}
    (free : ∀ frame ∈ leading, frame.ForeignFree) :
    FramesCallbackCovers (leading ++ rest) ↔ FramesCallbackCovers rest :=
  ⟨FramesCallbackCovers.suffix,FramesCallbackCovers.free_append free⟩

theorem _root_.Glorious.Language.Execution.FreshNamedFrame.callback_covers
    {function : Kernel.Function} {caller : Execution.Context} {brand region : Identity} {rest : List Frame} :
    FramesCallbackCovers (FreshNamedFrame function caller brand region ++ rest) ↔ FramesCallbackCovers rest :=
  FramesCallbackCovers.free_append_iff FreshNamedFrame.foreign_free

theorem _root_.Glorious.Language.Execution.LabelRoute.callback_covers
    {frames inner outer : List Frame} {brand region : Identity} {context : Execution.Context} {type : Term}
    (route : LabelRoute frames brand inner context region type outer) (covered : FramesCallbackCovers frames) :
    FramesCallbackCovers outer ∧ AmbientRuntimes outer = AmbientRuntimes frames := by
  obtain ⟨rfl,free,_⟩ := route
  refine ⟨covered.suffix.tail,?_⟩
  simp only [AmbientRuntimes.append,AmbientRuntimes.cons,Frame.callbackRuntimes,
    AmbientRuntimes.free free,List.nil_append]

theorem _root_.Glorious.Language.Execution.Routes.callback_covers
    {program : Kernel.Program} {before : State} {operation : DeclId} {arguments : List Term}
    {payload : List ResolvedPlace} {inner outer : List Frame} {handler : InstalledHandler} {owns : Bool} {arm : OperationArm}
    (route : Routes program before operation arguments payload inner handler owns arm outer)
    (covered : FramesCallbackCovers before.frames) :
    FramesCallbackCovers outer ∧ AmbientRuntimes outer = AmbientRuntimes before.frames := by
  refine ⟨?_,?_⟩
  · rw [route.1] at covered
    exact covered.suffix.tail
  · rw [route.1]
    simp only [AmbientRuntimes.append,AmbientRuntimes.cons,Frame.callbackRuntimes,
      AmbientRuntimes.free route.foreign_free,List.nil_append]

theorem AmbientRuntimes.map_free {map : Relocation} {frames : List Frame}
    (free : ∀ frame ∈ frames, frame.ForeignFree) : AmbientRuntimes (frames.map map.frame) = [] := by
  apply AmbientRuntimes.free
  intro frame member
  obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
  exact map.frame_foreign_free (free original originalMember)

theorem _root_.Glorious.Language.Execution.FramesCallbackCovers.map_free_append
    {map : Relocation} {leading rest : List Frame} (free : ∀ frame ∈ leading, frame.ForeignFree)
    (covered : FramesCallbackCovers rest) : FramesCallbackCovers (leading.map map.frame ++ rest) := by
  apply covered.free_append
  intro frame member
  obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
  exact map.frame_foreign_free (free original originalMember)

theorem CallbackReturnTask.callback_runtimes {session : ForeignSession} {entry : CallbackEntry} {result : Address}
    {lease : Option ReceiverLease} {next : Code} :
    (CallbackReturnTask session entry result lease next).callbackRuntimes = entry.runtime :: session.heldRuntimes := by
  cases lease <;> rfl

theorem CallbackReturnTask.callback_covers {session : ForeignSession} {entry : CallbackEntry} {result : Address}
    {lease : Option ReceiverLease} {next : Code} {ambient : List Identity} :
    (CallbackReturnTask session entry result lease next).CallbackCovers ambient ↔ ambient ⊆ entry.runtime :: session.heldRuntimes := by
  cases lease <;> rfl

/-- This invariant describes actual dynamic callback ownership. Registry
permission may be temporarily lent or consumed; the executing entry's runtime
must nevertheless stay live until its ordinary source cleanup completes. -/
structure Model.CallbacksWellFormed (model : Model) (state : State) : Prop where
  control : state.CallbackControl
  live : ∀ runtime ∈ state.callbackRuntimes,
    runtime ∈ model.runtimes state.hostState

theorem Model.CallbacksWellFormed.task {model : Model} {state : State}
    (well : model.CallbacksWellFormed state) :
    ∀ runtime ∈ state.task.callbackRuntimes, runtime ∈ model.runtimes state.hostState :=
  fun runtime member => well.live runtime (List.mem_append_left _ member)

theorem Model.CallbacksWellFormed.frames {model : Model} {state : State}
    (well : model.CallbacksWellFormed state) :
    ∀ runtime ∈ AmbientRuntimes state.frames, runtime ∈ model.runtimes state.hostState :=
  fun runtime member => well.live runtime (List.mem_append_right _ member)

theorem Model.CallbacksWellFormed.frame_runtime {model : Model} {state : State}
    {session : ForeignSession} {entry : CallbackEntry} {resultType : Term} {lease : Option ReceiverLease} {next : Code}
    (well : model.CallbacksWellFormed state)
    (frame : Frame.hostCallback session entry resultType lease next ∈ state.frames) :
    entry.runtime ∈ model.runtimes state.hostState := by
  apply well.frames
  exact List.mem_flatMap.mpr ⟨_,frame,List.mem_cons_self⟩

theorem Model.CallbacksWellFormed.pending_runtime {model : Model} {state : State}
    {session : ForeignSession} {entry : CallbackEntry} {result : Address} {next : Code}
    (well : model.CallbacksWellFormed state) (pending : state.task = .foreignCallbackReturned session entry result next) :
    entry.runtime ∈ model.runtimes state.hostState := by
  apply well.task
  simp only [pending,Task.callbackRuntimes,List.mem_cons_self]

theorem CallbackAdmission.owned_unregistered {program : Kernel.Program} {model : Model} {contract : Contract}
    {initial current : World} {session : ForeignSession} {state : List Nat} {id : Identity}
    {registration : Registration} {function : Function}
    (admitted : CallbackAdmission program model contract initial current session state id registration function)
    (owned : registration.access = .owned) : registration ∉ model.registrations state := by
  intro member
  exact admitted.owned owned registration member admitted.active ⟨rfl,rfl,Or.inl ⟨[],by simp⟩⟩

end Foreign
end Glorious.Language
