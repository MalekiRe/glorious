import GloriousLanguage.Machine

/-! Original invocation inputs and actual entry preparation share one capture
projection. The preparation proof retains ordered source coordinates while its
real lending relations may replace incoming authority with a fresh child loan. -/
namespace Glorious.Language.Execution

open Kernel

theorem ResidentCaptureInputs.formals (receiver : Address) (authority : Authority) (access : Access)
    (formals : List Local) :
    (ResidentCaptureInputs receiver authority access formals).filterMap (fun input => input.formal.resident?) = formals := by
  simp only [ResidentCaptureInputs,List.filterMap_map,Function.comp_def,InputFormal.resident?,
    List.filterMap_eq_map',List.zipIdx_map_fst]

/-- Source formal selection observes only resident locals from the common
input domain. Erased ports are checked by IncomingResources and the same
binding producer; they are not fabricated source-local declarations. -/
def EntrySource.HasFormals (function : Function) : EntrySource → Prop
  | .supplied inputs => inputs.filterMap (fun input => input.formal.resident?) = function.captures ++ function.parameters
  | .resident _ _ arguments => arguments.filterMap (fun input => input.formal.resident?) = function.parameters
  | .contextual _ _ _ _ inputs => inputs.filterMap (fun input => input.formal.resident?) = function.captures ++ function.parameters

theorem EntrySource.originalInputs_formals (source : EntrySource) (function : Function) :
    (source.originalInputs function).filterMap (fun input => input.formal.resident?) = function.captures ++ function.parameters ↔
      source.HasFormals function := by
  cases source <;>
    simp only [EntrySource.originalInputs,EntrySource.HasFormals,List.filterMap_append,
      ResidentCaptureInputs.formals,List.append_cancel_left_eq]

theorem ArgumentInputs.formals {world : World} {context : Context} {index : Nat}
    {formals : List Local} {places : List Place} {inputs : List InvocationInput}
    (selected : ArgumentInputs world context index formals places inputs) :
    inputs.filterMap (fun input => input.formal.resident?) = formals := by
  induction selected with
  | nil => rfl
  | cons _ _ _ ih => exact congrArg (List.cons _) ih

theorem CaptureInputs.formals {world : World} {receiver : Address} {authority : Authority} {access : Access}
    {formals : List Local} {inputs : List InvocationInput}
    (selected : CaptureInputs world receiver authority access formals inputs) :
    inputs.filterMap (fun input => input.formal.resident?) = formals := by
  rw [selected.1]
  exact ResidentCaptureInputs.formals receiver authority access formals

/-- Every authority-independent view is unchanged by the actual preparation
derivation. This compares real recipes and their prepared inputs; it asserts
neither a replacement execution state nor permission under the old authority. -/
theorem PreparesEntry.map_inputs {program : Kernel.Program} {context : Context} {function : Function}
    {before after : World} {source : EntrySource} {inputs : List InvocationInput}
    (prepared : PreparesEntry program context function before source inputs after)
    {α : Type} (view : InvocationInput → α)
    (authorityIndependent : ∀ origin formal storage access first second,
      view ⟨origin,formal,storage,first,access⟩ = view ⟨origin,formal,storage,second,access⟩) :
    inputs.map view = (source.originalInputs function).map view := by
  cases prepared with
  | supplied => rfl
  | resident _ _ _ captures _ =>
      rw [captures.1]
      simp only [EntrySource.originalInputs,List.map_append,ResidentCaptureInputs,List.map_map]
      congr 1
      apply List.map_congr_left
      intro entry _
      exact authorityIndependent _ _ _ _ _ _
  | contextual => rfl

/-- Entry preserves the complete ordered input coordinates. Authority is
deliberately absent: a resident capture can carry the new receiver child loan. -/
theorem PreparesEntry.input_coordinates {program : Kernel.Program} {context : Context} {function : Function}
    {before after : World} {source : EntrySource} {inputs : List InvocationInput}
    (prepared : PreparesEntry program context function before source inputs after) :
    inputs.map (fun input => (input.origin,input.formal,input.storage,input.access)) =
      (source.originalInputs function).map (fun input => (input.origin,input.formal,input.storage,input.access)) :=
  prepared.map_inputs _ (by intros; rfl)

theorem PreparesEntry.input_origins {program : Kernel.Program} {context : Context} {function : Function}
    {before after : World} {source : EntrySource} {inputs : List InvocationInput}
    (prepared : PreparesEntry program context function before source inputs after) :
    inputs.map (·.origin) = (source.originalInputs function).map (·.origin) :=
  prepared.map_inputs _ (by intros; rfl)

theorem PreparesEntry.input_formals {program : Kernel.Program} {context : Context} {function : Function}
    {before after : World} {source : EntrySource} {inputs : List InvocationInput}
    (prepared : PreparesEntry program context function before source inputs after) :
    inputs.map (·.formal) = (source.originalInputs function).map (·.formal) :=
  prepared.map_inputs _ (by intros; rfl)

theorem PreparesEntry.formals {program : Kernel.Program} {context : Context} {function : Function}
    {before after : World} {source : EntrySource} {inputs : List InvocationInput}
    (prepared : PreparesEntry program context function before source inputs after)
    (formals : source.HasFormals function) :
    inputs.filterMap (fun input => input.formal.resident?) = function.captures ++ function.parameters := by
  have preserved := congrArg (List.filterMap InputFormal.resident?) prepared.input_formals
  simp only [List.filterMap_map,Function.comp_def] at preserved
  exact preserved.trans ((source.originalInputs_formals function).mpr formals)

end Glorious.Language.Execution
