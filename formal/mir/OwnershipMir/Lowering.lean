import OwnershipMir.Machine

/-! Atomic ownership commands lower to two MIR operations. Field paths use the
same focus/rebuild contract as whole slots; the explicit transfer register
accounts for ownership between the two physical steps. -/
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

def Command.first {n : Nat} : Command n → Op n
  | .move mode source _ => .take source mode
  | .copy source _ => .copy source
  | .dispose source => .take source .whole

def Command.last {n : Nat} : Command n → Op n
  | .move _ _ target | .copy _ target => .put target
  | .dispose _ => .drop

def Command.emit {n : Nat} (command : Command n) (next : Code n (Op n)) : Code n (Op n) :=
  .act command.first (.act command.last next)

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

/-- Equality is proved between independently defined atomic and granular
execution functions, rather than defining the source to run the compiler. -/
theorem Command.exec_eq {n : Nat} (command : Command n) (state : State n) :
    command.exec state = (command.first.exec state).bind command.last.exec := by
  cases command <;> cases unused : state.temp <;>
    simp [Command.exec, Command.first, Command.last, Op.exec, unused, Extract.apply, Option.bind_assoc]

theorem Command.exec_lower {n : Nat} {command : Command n} {before after : State n}
    (executed : command.exec before = some after) :
    ∃ middle, command.first.exec before = some middle ∧ command.last.exec middle = some after := by
  simpa only [Command.exec_eq, Option.bind_eq_some_iff] using executed

/-- Nonempty simulation: even a source loop step performs an actual MIR step.
Primitive lowering has one additional step, never an unbounded silent phase. -/
theorem lower_step {n : Nat} {before after : Configuration n (Command n)}
    (step : Step Command.exec before after) :
    ∃ middle, Step Op.exec ⟨lower before.code, before.state⟩ middle ∧
      (middle = ⟨lower after.code, after.state⟩ ∨
        Step Op.exec middle ⟨lower after.code, after.state⟩) := by
  cases step with
  | act executed =>
    obtain ⟨middle, first, last⟩ := Command.exec_lower executed
    exact ⟨_, .act first, Or.inr (.act last)⟩
  | @branch guard yes no state choice observed =>
    cases choice <;> exact ⟨_, .branch observed, Or.inl rfl⟩
  | @loop guard body next state choice observed =>
    cases choice
    · exact ⟨_, .loop observed, Or.inl rfl⟩
    · refine ⟨_, .loop observed, Or.inl ?_⟩
      simp [lower_append, lower]

theorem lower_run {n : Nat} {before after : Configuration n (Command n)}
    (run : Run Command.exec before after) :
    Run Op.exec ⟨lower before.code, before.state⟩ ⟨lower after.code, after.state⟩ := by
  induction run with
  | refl => exact .refl _
  | step head tail ih =>
    obtain ⟨middle, first, last⟩ := lower_step head
    rcases last with same | last
    · subst middle; exact .step first ih
    · exact .step first (.step last ih)

/-- Public vertical-slice theorem: syntactic command checking supplies MIR
admission; arbitrary physical prefixes, including half-completed transfers,
retain unique ownership and exact-resource conservation and cannot get stuck. -/
theorem compiled_ownership_safety {n : Nat} {signature : Signature}
    {before final : Context n} {source : Code n (Command n)}
    (checked : Code.Checked Command.Checked before source final) {initial : State n}
    (typed : initial.Typed signature before) (unique : initial.Unique)
    {reached : Configuration n (Op n)}
    (run : Run Op.exec ⟨lower source, initial⟩ reached) :
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
    (run : Run Command.exec ⟨source, initial⟩ ⟨.halt, result⟩) :
    Run Op.exec ⟨lower source, initial⟩ ⟨.halt, result⟩ ∧
      result.Typed signature final ∧ result.temp = none ∧ Conserves signature initial result := by
  have lowered := lower_run run
  obtain ⟨⟨current, realized, remaining⟩, conserved⟩ :=
    (Safe.run (signature := signature) ⟨before, typed, lower_checked checked⟩ Op.Checked.sound lowered)
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

end OwnershipMir
