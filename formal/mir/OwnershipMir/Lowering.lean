import OwnershipMir.Trace

/-! Atomic commands refine to nonempty finite MIR blocks. Field paths use the
same focus/rebuild contract as whole slots; transient registers belong to the
actual machine state throughout block execution. -/
namespace OwnershipMir

inductive Command (n : Nat) where
  | move (mode : Extract) (source target : Place n)
  | copy (source target : Place n)
  | dispose (source : Place n)

/-- Independent atomic meaning. The destination is resolved after the source
is cleared, permitting valid same-aggregate transfers without assuming a frame. -/
def Command.exec {n : Nat} (command : Command n) (state : State n) : Option (State n) :=
  match state.temp with
  | some _ => none
  | none => match command with
    | .move mode source target => do
      let origin ← source.find state.slots
      let value ← origin.selected
      let result ← mode.apply value
      let slots := source.write state.slots origin none
      let into ← target.find slots
      if vacant into.selected then
        some ⟨target.write slots into (some result), none⟩
      else none
    | .copy source target => do
      let origin ← source.find state.slots
      let value ← origin.selected
      let into ← target.find state.slots
      if vacant into.selected then
        some ⟨target.write state.slots into (some value), none⟩
      else none
    | .dispose source => do
      let origin ← source.find state.slots
      let _ ← origin.selected
      some ⟨source.write state.slots origin none, none⟩

inductive Command.Checked {n : Nat} : Context n → Command n → Context n → Prop where
  | move {context mode source target input output origin into} (empty : context.temp = none)
      (found : source.find context.slots = some origin) (selected : origin.selected = some input)
      (layout : source.layout = input.layout id) (extract : mode.Checked input output)
      (initialized : mode = .whole → input.ready)
      (destination : target.find (source.write context.slots origin none) = some into)
      (vacant : Fits output into.selected) :
      Checked context (.move mode source target)
        ⟨target.write (source.write context.slots origin none) into (some output), none⟩
  | copy {context source target shape origin into} (empty : context.temp = none)
      (found : source.find context.slots = some origin) (selected : origin.selected = some shape)
      (allowed : shape.copyable) (destination : target.find context.slots = some into)
      (vacant : Fits shape into.selected) :
      Checked context (.copy source target) ⟨target.write context.slots into (some shape), none⟩
  | dispose {context source shape origin} (empty : context.temp = none)
      (found : source.find context.slots = some origin) (selected : origin.selected = some shape)
      (layout : source.layout = shape.layout id) (allowed : shape.disposable) (exhausted : shape.shallow) :
      Checked context (.dispose source) ⟨source.write context.slots origin none, none⟩

def Command.block {n : Nat} : Command n → List (Op n)
  | .move mode source target => [.take source mode, .put target]
  | .copy source target => [.copy source, .put target]
  | .dispose source => [.take source .whole, .drop]

theorem Command.block_nonempty {n : Nat} (command : Command n) : command.block ≠ [] := by
  cases command <;> simp [Command.block]

def Command.emit {n : Nat} (command : Command n) (next : Code n (Op n)) : Code n (Op n) :=
  Block.emit command.block next

def lower {n : Nat} : Code n (Command n) → Code n (Op n)
  | .halt => .halt
  | .act command next => command.emit (lower next)
  | .branch guard yes no => .branch guard (lower yes) (lower no)
  | .loop guard body next => .loop guard (lower body) (lower next)

theorem lower_append {n : Nat} (first last : Code n (Command n)) :
    lower (first.append last) = (lower first).append (lower last) := by
  induction first with
  | halt => rfl
  | act command next ih => simp [lower, Command.emit, Code.append, ih]
  | branch guard yes no yesIH noIH => simp [lower, Code.append, yesIH, noIH]
  | loop guard body next _ nextIH => simp [lower, Code.append, nextIH]

theorem Command.Checked.lower {n : Nat} {before after final : Context n} {command : Command n}
    (checked : Command.Checked before command after) {next : Code n (Op n)}
    (tail : Code.Checked Op.Checked after next final) :
    Code.Checked Op.Checked before (command.emit next) final := by
  cases checked with
  | move empty found selected layout extract initialized destination vacant =>
    exact .act (.take empty found selected layout extract) (.act (.put rfl destination vacant) tail)
  | copy empty found selected allowed destination vacant =>
    exact .act (.copy empty found selected allowed) (.act (.put rfl destination vacant) tail)
  | dispose empty found selected layout allowed exhausted =>
    exact .act (.take empty found selected layout (.whole _)) (.act (.drop rfl allowed exhausted) tail)

theorem lower_checked {n : Nat} {before after : Context n} {source : Code n (Command n)}
    (checked : Code.Checked Command.Checked before source after) :
    Code.Checked Op.Checked before (lower source) after := by
  induction checked with
  | halt => exact .halt
  | act head tail ih => exact head.lower ih
  | branch scalar left right leftIH rightIH => exact .branch scalar leftIH rightIH
  | loop scalar body tail bodyIH tailIH => exact .loop scalar bodyIH tailIH

/-- Source semantics equals execution of the emitted finite block. -/
theorem Command.exec_eq {n : Nat} (command : Command n) (state : State n) :
    command.exec state = Block.exec Op.exec command.block state := by
  cases command <;> cases unused : state.temp <;>
    simp [Command.exec, Command.block, Block.exec, Op.exec, unused, Extract.apply, Option.bind_assoc]

/-- Positive finite simulation; no two-step shape appears in this interface. -/
theorem lower_step {n : Nat} {before after : Configuration n (Command n)}
    (step : Step Command.exec before after) :
    ∃ middle, Step Op.exec ⟨lower before.code, before.state⟩ middle ∧
      Run (Step Op.exec) middle ⟨lower after.code, after.state⟩ := by
  cases step with
  | @act command next state after executed =>
    exact Block.exec_positive command.block command.block_nonempty
      (by rwa [Command.exec_eq] at executed) (lower next)
  | @branch guard yes no state choice observed =>
    cases choice <;> exact ⟨_, .branch observed, .refl _⟩
  | @loop guard body next state choice observed =>
    cases choice
    · exact ⟨_, .loop observed, .refl _⟩
    · refine ⟨_, .loop observed, ?_⟩
      simpa [lower_append, lower] using (Run.refl (next := Step Op.exec)
        (Configuration.mk (lower (body.append (.loop guard body next))) state))

theorem lower_run {n : Nat} {before after : Configuration n (Command n)}
    (run : Run (Step Command.exec) before after) :
    Run (Step Op.exec) ⟨lower before.code, before.state⟩ ⟨lower after.code, after.state⟩ := by
  induction run with
  | refl => exact .refl _
  | step head tail ih =>
    obtain ⟨middle, first, rest⟩ := lower_step head
    exact .step first (rest.trans ih)

/-- Public vertical-slice theorem: syntactic command checking supplies MIR
admission; arbitrary physical prefixes, including half-completed transfers,
retain unique ownership and exact-resource conservation and cannot get stuck. -/
theorem compiled_ownership_safety {n : Nat} {signature : Signature}
    {before final : Context n} {source : Code n (Command n)}
    (checked : Code.Checked Command.Checked before source final) {initial : State n}
    (typed : initial.Typed signature before) (unique : initial.Unique)
    {reached : Configuration n (Op n)}
    (run : Run (Step Op.exec) ⟨lower source, initial⟩ reached) :
    Safe signature Op.Checked final reached ∧ reached.state.Unique ∧
      Conserves signature initial reached.state ∧
      (reached.code = .halt ∨ ∃ next, Step Op.exec reached next) :=
  ownership_safety ⟨before, typed, lower_checked checked⟩ unique run

/-- A source return is implemented with exactly the same slots and empty
transfer register. This is value/state correspondence, not just safety. -/
theorem compiled_return {n : Nat} {signature : Signature} {before final : Context n}
    {source : Code n (Command n)} (checked : Code.Checked Command.Checked before source final)
    {initial result : State n} (typed : initial.Typed signature before)
    (empty : final.temp = none)
    (run : Run (Step Command.exec) ⟨source, initial⟩ ⟨.halt, result⟩) :
    Run (Step Op.exec) ⟨lower source, initial⟩ ⟨.halt, result⟩ ∧
      result.Typed signature final ∧ result.temp = none ∧ Conserves signature initial result := by
  have lowered := lower_run run
  obtain ⟨⟨current, realized, remaining⟩, conserved⟩ :=
    (Safe.run (signature := signature) ⟨before, typed, lower_checked checked⟩ Op.Checked.executed lowered)
  cases remaining with
  | halt => exact ⟨lowered, realized, by simpa [empty] using realized.2, conserved⟩

/-- Ordinary source movement reads an actually initialized subtree. Internal
cleanup transfers may carry holes, but cannot masquerade as source moves. -/
theorem Command.Checked.move_ready {n : Nat} {signature : Signature} {before after : Context n}
    {source target : Place n} (checked : Command.Checked before (.move .whole source target) after)
    {state : State n} (typed : state.Typed signature before) :
    ∃ lens value, source.find state.slots = some lens ∧ lens.selected = some value ∧ value.ready := by
  cases checked with
  | move empty found selected layout extract initialized destination vacant =>
    obtain ⟨actual, actualFound, actualTyped, _⟩ := source.realized typed _ found
    obtain ⟨value, live, classified⟩ := Option.map_eq_some_iff.mp (actualTyped.trans selected)
    have ready : (value.kind signature).ready := classified.symm ▸ initialized rfl
    exact ⟨actual, value, actualFound, live, (Tree.ready_map _ _).mp ready⟩

theorem commands_trace {n : Nat} (commands : List (Command n)) {before after : State n}
    (executed : Block.exec Command.exec commands before = some after) (next : Code n (Op n)) :
    OwnershipTrace ⟨(lower (sequence commands)).append next, before⟩ ⟨next, after⟩
      (commands.flatMap fun command => command.block.map Op.event) := by
  induction commands generalizing before with
  | nil => cases Option.some.inj executed; exact .refl _
  | cons command rest ih =>
    obtain ⟨middle, head, tail⟩ := Option.bind_eq_some_iff.mp executed
    have first := Block.exec_trace command.block (by rwa [Command.exec_eq] at head) ((lower (sequence rest)).append next)
    simpa only [sequence, Block.emit, lower, Command.emit, Block.emit_append, List.flatMap_cons] using first.trans (ih tail)

end OwnershipMir
