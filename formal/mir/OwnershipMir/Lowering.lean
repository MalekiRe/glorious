import OwnershipMir.Machine

/-! A deliberately small ownership-command frontend, not the full source
language. Commands execute atomically on slots; MIR executes through an explicit
transfer register. The translation preserves actual values and storage holes,
not merely a resource-count approximation. -/
namespace OwnershipMir

inductive Command (n : Nat) where
  | move (source target : Fin n)
  | copy (source target : Fin n)
  | dispose (source : Fin n)

/-- Source operation meanings are independent of MIR instruction execution. -/
def Command.exec {n : Nat} : Command n → State n → Option (State n)
  | .move source target, state => match state.temp, state.slots source, state.slots target with
    | none, some value, none => some ⟨update (update state.slots source none) target (some value), none⟩
    | _, _, _ => none
  | .copy source target, state => match state.temp, state.slots source, state.slots target with
    | none, some value, none => some ⟨update state.slots target (some value), none⟩
    | _, _, _ => none
  | .dispose source, state => match state.temp, state.slots source with
    | none, some _ => some ⟨update state.slots source none, none⟩
    | _, _ => none

inductive Command.Checked {n : Nat} : Context n → Command n → Context n → Prop where
  | move {context source target kind} (empty : context.temp = none)
      (found : context.slots source = some kind) (vacant : context.slots target = none) :
      Checked context (.move source target)
        ⟨update (update context.slots source none) target (some kind), none⟩
  | copy {context source target} (empty : context.temp = none)
      (found : context.slots source = some .data) (vacant : context.slots target = none) :
      Checked context (.copy source target) ⟨update context.slots target (some .data), none⟩
  | dispose {context source kind} (empty : context.temp = none)
      (found : context.slots source = some kind) (allowed : kind ≠ .exact) :
      Checked context (.dispose source) ⟨update context.slots source none, none⟩

def Command.first {n : Nat} : Command n → Op n
  | .move source _ => .take source
  | .copy source _ => .copy source
  | .dispose source => .take source

def Command.last {n : Nat} : Command n → Op n
  | .move _ target | .copy _ target => .put target
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
  | move empty found vacant =>
    exact .act (.take empty found) (.act (.put rfl (by simp [update, vacant])) tail)
  | copy empty found vacant => exact .act (.copy empty found) (.act (.put rfl vacant) tail)
  | dispose empty found allowed => exact .act (.take empty found) (.act (.drop rfl allowed) tail)

theorem lower_checked {n : Nat} {before after : Context n} {source : Code n (Command n)}
    (checked : Code.Checked Command.Checked before source after) :
    Code.Checked Op.Checked before (lower source) after := by
  induction checked with
  | halt => exact .halt
  | act head tail ih => exact head.lower ih
  | branch scalar left right leftIH rightIH => exact .branch scalar leftIH rightIH
  | loop scalar body tail bodyIH tailIH => exact .loop scalar bodyIH tailIH

/-- Each atomic source command is implemented by exactly two actual operations.
No instruction result or post-state permission is assumed. -/
theorem Command.exec_lower {n : Nat} {command : Command n} {before after : State n}
    (executed : command.exec before = some after) :
    ∃ middle, command.first.exec before = some middle ∧ command.last.exec middle = some after := by
  cases command with
  | move source target =>
    cases temp : before.temp <;> cases live : before.slots source <;> cases vacant : before.slots target <;>
      simp [Command.exec, temp, live, vacant] at executed
    rename_i value
    cases executed
    have different : target ≠ source := by intro same; subst target; simp_all
    exact ⟨⟨update before.slots source none, some value⟩, by simp [Command.first, Op.exec, temp, live],
      by simp [Command.last, Op.exec, update, different, vacant]⟩
  | copy source target =>
    cases temp : before.temp <;> cases live : before.slots source <;> cases vacant : before.slots target <;>
      simp [Command.exec, temp, live, vacant] at executed
    rename_i value
    cases executed
    exact ⟨⟨before.slots, some value⟩, by simp [Command.first, Op.exec, temp, live],
      by simp [Command.last, Op.exec, vacant]⟩
  | dispose source =>
    cases temp : before.temp <;> cases live : before.slots source <;>
      simp [Command.exec, temp, live] at executed
    rename_i value
    cases executed
    exact ⟨⟨update before.slots source none, some value⟩, by simp [Command.first, Op.exec, temp, live], rfl⟩

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

end OwnershipMir
