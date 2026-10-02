import OwnershipMir.Adequacy

namespace OwnershipMir

def shellWeight : Cell Atom → Nat := cellMass (fun _ => 0) (fun s => if s.restriction = .exact then 1 else 0)

def State.shells {n : Nat} (state : State n) : Nat :=
  total (fun i => shellWeight (state.slots i)) + shellWeight state.temp

theorem Place.shells_write {n : Nat} (state : State n) (place : Place n) (lens : Lens Atom)
    (found : place.find state.slots = some lens) (value temp : Cell Atom) :
    (State.mk (place.write state.slots lens value) temp).shells +
        shellWeight lens.selected + shellWeight state.temp =
      state.shells + shellWeight value + shellWeight temp := by
  exact place.mass_write state lens found value temp (fun _ => 0)
    (fun s => if s.restriction = .exact then 1 else 0)

def Extract.debit : Extract → Value → Nat
  | .deconstruct, .wrap s _ => if s.restriction = .exact then 1 else 0
  | _, _ => 0

theorem Extract.shell_balance {mode : Extract} {value result : Value}
    (executed : mode.apply value = some result) :
    shellMass result + mode.debit value = shellMass value := by
  cases mode with
  | whole => cases Option.some.inj executed; simp [Extract.debit]
  | deconstruct =>
    cases value <;> simp only [Extract.apply, Option.some.injEq] at executed
    all_goals try { contradiction }
    subst result
    simp [shellMass, Tree.mass, Extract.debit, Nat.add_comm]

/-- Debit is read from the actual selected runtime shell, never supplied by
admission. Only a deconstruction instruction can discharge a positive shell. -/
def Op.shellDebit {n : Nat} : Op n → State n → Nat
  | .take p mode, state =>
    ((p.find state.slots).bind fun lens => lens.selected.map mode.debit).getD 0
  | _, _ => 0

theorem vacant_shell_zero {cell : Cell Atom} (empty : vacant cell = true) : shellWeight cell = 0 := by
  cases cell with
  | none => rfl
  | some tree => cases tree <;> simp [vacant] at empty <;> rfl

theorem Op.Checked.shell_balance {n : Nat} {signature : Signature} {before after : Context n}
    {op : Op n} (checked : Op.Checked before op after) {state next : State n}
    (typed : state.Typed signature before) (executed : op.exec state = some next) :
    next.shells + op.shellDebit state = state.shells := by
  obtain ⟨effect, _, allowed⟩ := checked.effect typed executed
  cases effect with
  | @take _ p mode actual value result actualFound live extracted unused =>
    have frame := p.shells_write state actual actualFound none (some result)
    have discharge := Extract.shell_balance extracted
    simp only [live, unused, shellWeight, cellMass] at frame
    change shellMass result + mode.debit value = shellMass value at discharge
    simp only [Op.shellDebit, actualFound, Option.bind_some, live, Option.map_some, Option.getD_some]
    change _ + mode.debit value = _
    unfold shellMass at discharge
    omega
  | @put _ p actual value actualFound live available =>
    have frame := p.shells_write state actual actualFound (some value) none
    rw [vacant_shell_zero available, live] at frame
    simp only [shellWeight, cellMass] at frame
    simp only [Op.shellDebit, Nat.add_zero]
    omega
  | @copy _ p actual value actualFound live unused =>
    have zero : shellWeight (some value) = 0 := Value.disposable_shell_zero (Tree.copyable_disposable allowed)
    simp only [Op.shellDebit, State.shells, zero, unused]
    rfl
  | @drop _ value live =>
    have zero : shellWeight (some value) = 0 := Value.disposable_shell_zero allowed
    simp only [Op.shellDebit, State.shells, live, zero]
    rfl

/-- Counts actual deconstruction events in a finite execution prefix. This is
an interpretation of the trace, not a separately maintained machine balance. -/
def Configuration.shellDebit {n : Nat} (before : Configuration n (Op n)) : Nat :=
  match before.code with
  | .act op _ => op.shellDebit before.state
  | _ => 0

inductive ShellTrace {n : Nat} : Configuration n (Op n) → Configuration n (Op n) → Nat → Prop where
  | refl (state) : ShellTrace state state 0
  | step {before middle after amount} (head : Step Op.exec before middle)
      (tail : ShellTrace middle after amount) : ShellTrace before after (before.shellDebit + amount)

theorem Safe.shell_step {n : Nat} {signature : Signature} {final : Context n}
    {before after : Configuration n (Op n)} (safe : Safe signature Op.Checked final before)
    (step : Step Op.exec before after) : after.state.shells + before.shellDebit = before.state.shells := by
  obtain ⟨context, typed, checked⟩ := safe
  cases step with
  | act executed => cases checked with
    | act head tail => exact head.shell_balance typed executed
  | branch observed => cases checked; split <;> rfl
  | loop observed => cases checked; split <;> rfl

theorem Safe.shell_run {n : Nat} {signature : Signature} {final : Context n}
    {before after : Configuration n (Op n)} (safe : Safe signature Op.Checked final before)
    (run : Run Op.exec before after) :
    ∃ amount, ShellTrace before after amount ∧ after.state.shells + amount = before.state.shells := by
  induction run with
  | refl => exact ⟨0, .refl _, Nat.add_zero _⟩
  | step head tail ih =>
    have first := safe.shell_step head
    obtain ⟨amount, trace, rest⟩ := ih (safe.step Op.Checked.sound head).1
    exact ⟨_, .step head trace, by omega⟩

private def noncopyShell (shell : Shell) : Nat := if shell.restriction = .data then 0 else 1

def State.linearShells {n : Nat} (state : State n) : Nat := state.mass (fun _ => 0) noncopyShell

private theorem copyable_linear_zero {signature : Signature} {value : Value}
    (allowed : (value.kind signature).copyable) : value.mass (fun _ => 0) noncopyShell = 0 := by
  induction value <;> simp_all [Value.kind, Tree.map, Tree.copyable, Tree.mass, noncopyShell]


private theorem extract_mass_le {mode : Extract} {value result : Value}
    (executed : mode.apply value = some result) (leaf : Atom → Nat) (shell : Shell → Nat) :
    result.mass leaf shell ≤ value.mass leaf shell := by
  cases mode with
  | whole => cases Option.some.inj executed; exact Nat.le_refl _
  | deconstruct =>
    cases value <;> simp only [Extract.apply, Option.some.injEq] at executed
    all_goals try { contradiction }
    subst result
    simp [Tree.mass]

/-- Affine shells, including fieldless shells without resource tokens, cannot
be duplicated either. The measure is another instance of the same tree fold. -/
theorem Op.Checked.linear_shells {n : Nat} {signature : Signature} {before after : Context n}
    {op : Op n} (checked : Op.Checked before op after) {state next : State n}
    (typed : state.Typed signature before) (executed : op.exec state = some next) :
    next.linearShells ≤ state.linearShells := by
  obtain ⟨effect, _, allowed⟩ := checked.effect typed executed
  cases effect with
  | @take _ p mode actual value result actualFound live extracted unused =>
    have frame := p.mass_write state actual actualFound none (some result) (fun _ => 0) noncopyShell
    have consumed := extract_mass_le extracted (fun _ => 0) noncopyShell
    simp only [live, unused, cellMass] at frame
    unfold State.linearShells
    omega
  | @put _ p actual value actualFound live available =>
    have frame := p.mass_write state actual actualFound (some value) none (fun _ => 0) noncopyShell
    rw [vacant_mass_zero _ _ available, live] at frame
    simp only [cellMass] at frame
    unfold State.linearShells
    omega
  | @copy _ p actual value actualFound live unused =>
    have zero := copyable_linear_zero allowed
    simp only [State.linearShells, State.mass, cellMass, unused, zero]
    exact Nat.le_refl _
  | drop live => simp [State.linearShells, State.mass, cellMass]

theorem Safe.linear_shells_step {n : Nat} {signature : Signature} {final : Context n}
    {before after : Configuration n (Op n)} (safe : Safe signature Op.Checked final before)
    (step : Step Op.exec before after) : after.state.linearShells ≤ before.state.linearShells := by
  obtain ⟨context, typed, checked⟩ := safe
  cases step with
  | act executed => cases checked with
    | act head tail => exact head.linear_shells typed executed
  | branch observed => split <;> exact Nat.le_refl _
  | loop observed => split <;> exact Nat.le_refl _

theorem Safe.linear_shells_run {n : Nat} {signature : Signature} {final : Context n}
    {before after : Configuration n (Op n)} (safe : Safe signature Op.Checked final before)
    (run : Run Op.exec before after) : after.state.linearShells ≤ before.state.linearShells := by
  induction run with
  | refl => exact Nat.le_refl _
  | step head tail ih =>
    exact Nat.le_trans (ih (safe.step Op.Checked.sound head).1) (safe.linear_shells_step head)

end OwnershipMir
