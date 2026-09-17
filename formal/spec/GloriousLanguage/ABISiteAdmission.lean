import GloriousLanguage.ABI
import GloriousLanguage.TailEntryProgress

/-! Site admission: the source inventory of proper-tail and label sites, and
the producers that turn the one executable relation into target evidence.

An admitted artifact is only usable if its target engines actually behave as the
source program demands *at the sites the source program contains*. The earlier
contract could not express that: it existentially quantified over evidence lists
whose site identities were unconstrained, so the empty list satisfied it and
nothing was required of a compiler that lowered `tail` to an ordinary call.

This module removes that freedom at the source.

* `Kernel.TailSites` and `Kernel.LabelSites` are the actual syntactic sites of a
  program, computed from `Kernel.Program.functions` by structural traversal. A
  clause that pins engine evidence to the inventory therefore cannot be met with
  the empty list.
* `ABI.TailSite.Entry`/`ABI.TailSite.Landed` and `ABI.LabelSite.Leaves` are
  source-machine predicates. Entry is the pending `tail` node in the executing
  declaration and activation; landed is the successor of the machine's own
  retiring step. Neither is a free predicate an implementation may falsify.
* `ABI.TailEvidence` and `ABI.LabelFusion` consume those predicates through
  `Engine.program`, `Engine.sourceState` and `Engine.semantics.Steps`, which
  `Engine.realizes` ties to the actual source steps.
* `SourceEngine` is the canonical engine, and `SourceEngine.tailEvidence` /
  `SourceEngine.labelFusion` discharge the evidence from the actual relation, so
  the strengthened clauses are inhabited by a concrete engine rather than merely
  consistent on paper.

Honest scope. The canonical engine is the machine itself (`sourceState` is
equality, `administrativeControl` counts live activation frames). Discharging the
same evidence for a separately implemented native engine remains that
implementation's obligation; this file supplies the source side and the exact
shape that obligation has. Lexical brand distinctness within one declaration is
supplied by `Typing.CodeType.label`'s freshness premise and is not re-derived
here from `FunctionType`. -/
namespace Glorious.Language

namespace Kernel

mutual

  /-- Every syntactic `tail` node of one body, in traversal order. -/
  def Code.tailSites (declaration : DeclId) : Code → List ABI.TailSite
    | .result _ | .abort => []
    | .tail call => [⟨declaration,.tail call⟩]
    | .bind _ _ next | .assign _ _ next | .discard _ next | .scope _ next
    | .endLoan _ next | .unsafeScope next | .closeAvailable _ next => next.tailSites declaration
    | .evaluate _ value next => value.tailSites declaration ++ next.tailSites declaration
    | .invoke _ _ next | .test _ _ _ _ next | .reserve _ _ _ next => next.tailSites declaration
    | .label _ _ _ body => body.tailSites declaration
    | .choose _ arms => arms.flatMap (Arm.tailSites declaration)
    | .handle _ computation handler =>
        computation.tailSites declaration ++ handler.tailSites declaration

  def Arm.tailSites (declaration : DeclId) : Arm → List ABI.TailSite
    | .clause _ body => body.tailSites declaration

  def OperationArm.tailSites (declaration : DeclId) : OperationArm → List ABI.TailSite
    | .clause _ _ _ _ _ body => body.tailSites declaration

  def Handler.tailSites (declaration : DeclId) : Handler → List ABI.TailSite
    | .attached _ completion operations _ =>
        completion.flatMap (Arm.tailSites declaration) ++
          operations.flatMap (OperationArm.tailSites declaration)

end

/-- The proper-tail sites of one function body. -/
def Function.tailSites (function : Function) : List ABI.TailSite :=
  function.body.tailSites function.declaration

/-- The proper-tail site inventory of a program: every `tail` node of every
function, with the declaring function it belongs to. The compiler contract pins
engine evidence to this list, so a program containing a `tail` node cannot be
admitted with no tail sites at all. -/
def TailSites (program : Program) : List ABI.TailSite :=
  program.functions.flatMap Function.tailSites

mutual

  /-- Every syntactic `label` node of one body, in traversal order. -/
  def Code.labelSites (declaration : DeclId) (activation : Identity) : Code → List ABI.LabelSite
    | .result _ | .abort | .tail _ => []
    | .bind _ _ next | .assign _ _ next | .discard _ next | .scope _ next
    | .endLoan _ next | .unsafeScope next | .closeAvailable _ next =>
        next.labelSites declaration activation
    | .evaluate _ value next =>
        value.labelSites declaration activation ++ next.labelSites declaration activation
    | .invoke _ _ next | .test _ _ _ _ next | .reserve _ _ _ next =>
        next.labelSites declaration activation
    | .label brand _ _ body =>
        ⟨declaration,brand,activation⟩ :: body.labelSites declaration activation
    | .choose _ arms => arms.flatMap (Arm.labelSites declaration activation)
    | .handle _ computation handler =>
        computation.labelSites declaration activation ++ handler.labelSites declaration activation

  def Arm.labelSites (declaration : DeclId) (activation : Identity) : Arm → List ABI.LabelSite
    | .clause _ body => body.labelSites declaration activation

  def OperationArm.labelSites (declaration : DeclId) (activation : Identity) : OperationArm → List ABI.LabelSite
    | .clause _ _ _ _ _ body => body.labelSites declaration activation

  def Handler.labelSites (declaration : DeclId) (activation : Identity) : Handler → List ABI.LabelSite
    | .attached _ completion operations _ =>
        completion.flatMap (Arm.labelSites declaration activation) ++
          operations.flatMap (OperationArm.labelSites declaration activation)

end

/-- The label sites of one function body. -/
def Function.labelSites (function : Function) : List ABI.LabelSite :=
  function.body.labelSites function.declaration function.activationRegion

/-- The label site inventory of a program: every `label` node of every function,
with its lexical brand and enclosing activation region. -/
def LabelSites (program : Program) : List ABI.LabelSite :=
  program.functions.flatMap Function.labelSites

end Kernel

namespace List

/-- A nonempty member makes the flattened traversal nonempty. -/
theorem flatMap_ne_nil_of_mem {α β : Type} {values : List α} {map : α → List β} {value : α}
    (member : value ∈ values) (nonempty : map value ≠ []) : values.flatMap map ≠ [] := by
  induction values with
  | nil => exact absurd member (fun absent => List.not_mem_nil absent)
  | cons head rest ih =>
      rw [List.flatMap_cons]
      intro empty
      have parts := List.append_eq_nil_iff.mp empty
      rcases List.mem_cons.mp member with rfl | member
      · exact nonempty parts.1
      · exact ih member parts.2

end List

namespace Kernel

/-- Every site of the inventory is a `tail` node of the function whose traversal
produced it: the inventory is read off the validated bodies, not fabricated. -/
theorem Code.mem_tailSites {declaration : DeclId} {code : Code} {site : ABI.TailSite}
    (member : site ∈ code.tailSites declaration) :
    site.function = declaration ∧ ∃ call, site.node = .tail call := by
  induction code using Code.tailSites.induct
    (motive2 := fun handler => ∀ {s : ABI.TailSite}, s ∈ handler.tailSites declaration →
      s.function = declaration ∧ ∃ call, s.node = .tail call)
    (motive3 := fun operation => ∀ {s : ABI.TailSite}, s ∈ operation.tailSites declaration →
      s.function = declaration ∧ ∃ call, s.node = .tail call)
    (motive4 := fun arm => ∀ {s : ABI.TailSite}, s ∈ arm.tailSites declaration →
      s.function = declaration ∧ ∃ call, s.node = .tail call) generalizing site with
  | case1 value => simp [Code.tailSites] at member
  | case2 => simp [Code.tailSites] at member
  | case3 call => simp only [Code.tailSites, List.mem_singleton] at member; cases member; exact ⟨rfl,⟨call,rfl⟩⟩
  | case4 _ _ next ih => simp only [Code.tailSites] at member; exact ih member
  | case5 _ _ next ih => simp only [Code.tailSites] at member; exact ih member
  | case6 _ next ih => simp only [Code.tailSites] at member; exact ih member
  | case7 _ next ih => simp only [Code.tailSites] at member; exact ih member
  | case8 _ next ih => simp only [Code.tailSites] at member; exact ih member
  | case9 next ih => simp only [Code.tailSites] at member; exact ih member
  | case10 _ next ih => simp only [Code.tailSites] at member; exact ih member
  | case11 _ _ _ ihValue ihNext =>
      simp only [Code.tailSites] at member
      rcases List.mem_append.mp member with member | member
      · exact ihValue member
      · exact ihNext member
  | case12 _ _ next ih => simp only [Code.tailSites] at member; exact ih member
  | case13 _ _ _ _ next ih => simp only [Code.tailSites] at member; exact ih member
  | case14 _ _ _ next ih => simp only [Code.tailSites] at member; exact ih member
  | case15 _ _ _ body ih => simp only [Code.tailSites] at member; exact ih member
  | case16 _ arms ihArms =>
      simp only [Code.tailSites] at member
      obtain ⟨arm, inArms, inArm⟩ := List.mem_flatMap.mp member
      exact ihArms arm inArms inArm
  | case17 _ computation handler ihComputation ihHandler =>
      simp only [Code.tailSites] at member
      rcases List.mem_append.mp member with member | member
      · exact ihComputation member
      · exact ihHandler member
  | case18 _ _ _ _ ihCompletion ihOperations =>
      rename_i s found
      simp only [Handler.tailSites] at found
      rcases List.mem_append.mp found with found | found
      · obtain ⟨arm, inArms, inArm⟩ := List.mem_flatMap.mp found
        exact ihCompletion arm inArms inArm
      · obtain ⟨operation, inOps, inOp⟩ := List.mem_flatMap.mp found
        exact ihOperations operation inOps inOp
  | case19 _ _ _ _ _ body ih =>
      rename_i s found
      simp only [OperationArm.tailSites] at found
      exact ih found
  | case20 _ body ih =>
      rename_i s found
      simp only [Arm.tailSites] at found
      exact ih found

/-- A function whose body is a `tail` node contributes exactly that site. -/
theorem Code.tailSites_self (declaration : DeclId) (call : Invocation) :
    (Code.tail call).tailSites declaration = [⟨declaration,.tail call⟩] := by
  simp only [Code.tailSites]

/-- The direct tail node is enough for a nonempty inventory. -/
theorem Function.tailSites_ne_nil {function : Function} {call : Invocation}
    (node : function.body = .tail call) : function.tailSites ≠ [] := by
  rw [Function.tailSites,node,Code.tailSites_self]
  exact List.cons_ne_nil _ _

/-- A program with a directly tail-recursive body has a nonempty site
inventory: the empty evidence list is not admissible for it. -/
theorem TailSites_ne_nil {program : Program} {function : Function} {call : Invocation}
    (member : function ∈ program.functions) (node : function.body = .tail call) :
    TailSites program ≠ [] :=
  List.flatMap_ne_nil_of_mem member (Function.tailSites_ne_nil node)

end Kernel

namespace ABI

open Kernel Execution

variable {Event Result : Type}

/-- Live call storage of a source state: the number of activation frames. A
proper-tail transfer replaces the retired activation's frame instead of stacking
another one, so this measure does not grow along a transfer. -/
def ActivationFrames : List Frame → Nat
  | [] => 0
  | .activation _ _ _ :: rest => ActivationFrames rest + 1
  | _ :: rest => ActivationFrames rest

/-- The canonical engine measure of live call control. -/
def ControlMeasure (state : Execution.State) : Nat := ActivationFrames state.frames

theorem ActivationFrames.append (first second : List Frame) :
    ActivationFrames (first ++ second) = ActivationFrames first + ActivationFrames second := by
  induction first with
  | nil => simp [ActivationFrames]
  | cons frame rest ih =>
      cases frame <;> simp only [List.cons_append,ActivationFrames,ih] <;> omega

/-- The frames a proper-tail route consumes are exactly a prefix of lexical
frames and the retiring activation frame, so the retired activation is the only
activation frame the transfer removes. -/
theorem ActivationFrames.suffix {frames : List Frame} {activation : Identity} {outer : Execution.Context}
    {regions : List Identity} {finish : List Frame}
    (route : TailFrames frames activation outer regions finish) :
    ∃ region inner, frames = inner ++ .activation outer activation region :: finish ∧
      ActivationFrames inner = 0 := by
  induction route with
  | activation => exact ⟨_,[],rfl,rfl⟩
  | scope previous ih =>
      obtain ⟨innerRegion,inner,shape,zero⟩ := ih
      exact ⟨innerRegion,_ :: inner,by rw [shape]; rfl,
        by simp only [ActivationFrames,zero]⟩
  | label previous ih =>
      obtain ⟨innerRegion,inner,shape,zero⟩ := ih
      exact ⟨innerRegion,_ :: inner,by rw [shape]; rfl,
        by simp only [ActivationFrames,zero]⟩

theorem ActivationFrames.freshNamedFrame (function : Kernel.Function) (caller : Execution.Context)
    (brand region : Identity) : ActivationFrames (FreshNamedFrame function caller brand region) = 0 := by
  cases exit : function.namedExit <;> simp [FreshNamedFrame,exit,ActivationFrames]

/-- A proper-tail step never adds live call storage. -/
theorem ControlMeasure.tail_step {program : Kernel.Program} {before after : Execution.State}
    {activation destination : Identity}
    (step : Execution.LocalStep program before (some (.tail activation destination)) after) :
    ControlMeasure after ≤ ControlMeasure before := by
  cases step <;> try (simp_all only [reduceCtorEq])
  case enterTail caller function source context entered afterWorld outer regions rest roots
      actualRunning enteredStep relinquished route selected ready lent =>
    obtain ⟨innerRegion,inner,shape,zero⟩ := ActivationFrames.suffix route
    have retained : ControlMeasure before = ActivationFrames rest + 1 := by
      simp only [ControlMeasure,shape,ActivationFrames.append,ActivationFrames,zero,Nat.zero_add]
    rw [retained]
    simp only [ControlMeasure,ActivationFrames.freshNamedFrame,ActivationFrames.append,
      ActivationFrames,Nat.zero_add]
    omega

/-- The source machine's own proper-tail request: the pending `tail` node is the
only premise, and the step is the machine's. -/
theorem TailSite.request_step {program : Kernel.Program} {before : Execution.State}
    {context : Execution.Context} {call : Kernel.Invocation}
    (pending : before.task = .run context (.tail call)) :
    Execution.LocalStep program before none
      { before with task := .apply context (context.invocation call) true } :=
  .tailRequest pending

/-- The machine's retiring step is the only producer of `Landed`. -/
theorem TailSite.landed_of_tail {program : Kernel.Program} {before landed : Execution.State}
    {activation destination : Identity}
    (step : Execution.LocalStep program before (some (.tail activation destination)) landed) :
    TailSite.Landed program landed activation :=
  ⟨before,destination,step⟩

/-- The complete source transfer: the machine's own request step, the invocation
entry, and the retiring step compose into one actual run ending at `Landed`. The
retired activation is the one the pending site executes in, derived from the
entry event rather than assumed. -/
theorem TailSite.run_to_landed {program : Kernel.Program} {host : Foreign.Model}
    {before entering landed : Execution.State} {context : Execution.Context}
    {call : Kernel.Invocation} {site : TailSite} {activation destination : Identity}
    {function : Kernel.Function} {source : EntrySource}
    (pending : before.task = .run context (.tail call)) (node : site.node = .tail call)
    (declared : ExecutingDeclaration context = some site.function)
    (invoked : ∃ declaration inputs, Execution.LocalStep program
      { before with task := .apply context (context.invocation call) true }
      (some (.call declaration inputs)) entering)
    (enteringTask : entering.task = .enter context function source true)
    (tail : Execution.LocalStep program entering (some (.tail activation destination)) landed) :
    ∃ trace, Execution.Run program host before trace landed ∧ site.Entry before activation ∧
      TailSite.Landed program landed activation := by
  obtain ⟨declaration,inputs,invoked⟩ := invoked
  have retired : activation = context.activation := by
    cases tail with
    | enterTail running entered relinquished route selected ready lent =>
      obtain ⟨sameCaller,sameFunction,sameSource,sameTail⟩ :=
        Task.enter.inj (running.symm.trans enteringTask)
      subst sameCaller
      rfl
  subst retired
  exact ⟨_,Run.silent (Or.inl (TailSite.request_step pending))
      (Run.visible (Or.inl invoked) (Run.visible (Or.inl tail) Run.refl)),
    ⟨context,call,pending,node,rfl,declared⟩,⟨entering,destination,tail⟩⟩

/-- The canonical source engine: its states are the machine's own states, its
steps are the one executable relation, and `sourceState` is equality. -/
def SourceSemantics (program : Kernel.Program) (host : Foreign.Model) :
    TransitionSystem Execution.Event Unit where
  State := Execution.State
  initial _ := False
  step before event after := Execution.Step program host before event after
  final _ _ := False
  invalid _ := False

/-- The engine an implementation must agree with at the step level: it *is* the
source machine. -/
def SourceEngine (program : Kernel.Program) (host : Foreign.Model) : Engine Execution.Event Unit where
  program := program
  host := host
  semantics := SourceSemantics program host
  observe event := some event
  descriptor := default
  backing _ := default
  home _ _ := none
  administrativeControl := ControlMeasure
  directTransfer state destination after :=
    ∃ context runtime argument inner outerContext region type outer,
      state.task = .leave context runtime argument ∧
      LabelRoute state.frames runtime inner outerContext region type outer ∧
      outerContext.activation = destination ∧
      Execution.Step program host state none after
  sourceState first second := first = second
  realizes := by
    intro before event after step implementing same
    subst same
    refine ⟨after,?_,rfl⟩
    cases event <;> simpa [SourceSemantics] using step

/-- Every actual proper-tail site is discharged by the canonical engine through
the request, callable selection and retiring steps. The first two preserve the
frames; the last replaces the activation without increasing live call frames. -/
def SourceEngine.tailEvidence (program : Kernel.Program) (host : Foreign.Model)
    (site : TailSite) : TailEvidence (SourceEngine program host) :=
  { site := site
    covered := fun source activation entry => ⟨source,rfl⟩
    transfer := by
      intro implementing source context call declaration inputs entering activation destination landed
        same entry pending invoked step
      change implementing = source at same
      subst implementing
      refine ⟨[.call declaration inputs, .tail activation destination],landed,?_,rfl,?_⟩
      · exact TransitionSystem.Steps.silent
          (show (SourceSemantics program host).step source none
            { source with task := .apply context (context.invocation call) true }
            from Or.inl (TailSite.request_step pending))
          (TransitionSystem.Steps.visible
            (show (SourceSemantics program host).step _ (some (.call declaration inputs)) entering
              from Or.inl invoked)
            (TransitionSystem.Steps.visible
              (show (SourceSemantics program host).step entering
                (some (.tail activation destination)) landed from Or.inl step)
              TransitionSystem.Steps.refl))
      · have frames : entering.frames = source.frames := by
          cases invoked <;> rfl
        have bounded := ControlMeasure.tail_step step
        change ControlMeasure landed ≤ ControlMeasure source
        simpa only [ControlMeasure,frames] using bounded }

/-- Every actual label site of a program is discharged by the canonical engine:
its brands obtain no home, and the machine's own leave step is the direct
transfer. -/
def SourceEngine.labelFusion (program : Kernel.Program) (host : Foreign.Model) :
    LabelFusion (SourceEngine program host) :=
  { sites := Kernel.LabelSites program
    noRuntimeAddress := fun implementing source site member same address value resident head => rfl
    direct := by
      intro implementing source site destination after member same leaves step
      obtain ⟨context,runtime,argument,inner,outerContext,region,type,outer,task,route,brand,
        destination_eq⟩ := leaves
      subst same
      exact ⟨after,context,runtime,argument,inner,outerContext,region,type,outer,task,route,
        destination_eq,step⟩ }

end ABI

end Glorious.Language
