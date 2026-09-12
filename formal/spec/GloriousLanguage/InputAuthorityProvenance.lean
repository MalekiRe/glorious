import GloriousLanguage.Kernel

/-! Provenance of an invocation's input authorities from the readiness the
machine actually admits.

`InputsTyped` admits inputs whose authorities are recorded rows of the loan
table. That condition is not an independent assumption: it is a consequence of
the input readiness the entry already requires. A permitted address names its
rows (`Permitted.recorded`), an allocation input names the owning row it
transfers (`AllocationClaim`), and an erased port names the row its share
descends from. Only one shape is not readable from readiness alone: a storage
port handed over through a share of a guard whose carrier row is not part of
the input's readiness. That shape is named exactly, as a headed-share
condition on the handed authority, instead of being hidden in a blanket
recorded-rows hypothesis over every input. -/
namespace Glorious.Language

open Kernel

/-- A loan-headed share chain: its heads are loans, so the identity its parent
names is a row of the table. A guard is not headed this way, because recording
a guard also requires its carrier row, which readiness alone does not name. -/
def Authority.LoanHeaded : Authority → Prop
  | .owner => True
  | .loan _ => True
  | .shared backing => backing.LoanHeaded
  | .guarded _ _ => False

/-- The share chains an erased port is actually handed over through never wrap
a guard: `ClaimsStorage`/`TransfersStorageLoan` pass the caller's own claim,
which is loan-headed. Authorities outside such a chain are unconstrained. -/
def Authority.SharedHeaded : Authority → Prop
  | .owner => True
  | .loan _ => True
  | .shared backing => backing.LoanHeaded
  | .guarded _ _ => True

theorem Authority.Recorded.of_loanHeaded {authority : Authority} {loans : Table Loan} {id : Identity}
    {loan : Loan} (headed : authority.LoanHeaded) (parent : authority.parentLoan = some id)
    (found : loans.get id = some loan) : authority.Recorded loans := by
  induction authority with
  | owner => trivial
  | loan identity =>
      have same : identity = id := Option.some.inj parent
      exact ⟨loan, same.symm ▸ found⟩
  | shared backing ih => exact ih headed parent
  | guarded backing carrier _ => cases headed

/-- An allocated authority transferred as an input names the owning row of its
claim. -/
theorem AllocationClaim.recorded_loan {world : World} {address : Address} {id : Identity}
    (claim : AllocationClaim world (.loan id) address) : ∃ loan, world.loans.get id = some loan := by
  obtain ⟨owner, loan, root, domain, parent, found, _⟩ := claim
  have same : id = owner := Option.some.inj parent
  exact ⟨loan, same.symm ▸ found⟩

/-- An admitted invocation input's authority is recorded, read from the
readiness that admitted it and the actual shape of the handed share chain. -/
theorem InvocationInput.ReadyFor.recorded {program : RuntimeProgram} {world : World}
    {footprint : List Address} {input : InvocationInput}
    (ready : input.ReadyFor program world footprint) (headed : input.authority.SharedHeaded) :
    input.authority.Recorded world.loans := by
  cases input with
  | mk origin formal storage authority access =>
    cases formal with
    | resident localSlot =>
        obtain ⟨value, stored, initialized, type, handoff, permitted⟩ := ready
        exact permitted.recorded
    | storage type =>
        obtain ⟨addressType, located, permitted⟩ := ready
        exact permitted.recorded
    | allocation type =>
        obtain ⟨owned, addressType, claim, disjunction⟩ := ready
        cases disjunction with
        | inl loaned =>
            obtain ⟨identity, rfl⟩ := loaned
            exact claim.recorded_loan
        | inr guarded =>
            obtain ⟨backing, carrier, rfl, permitted⟩ := guarded
            exact permitted.recorded
    | loan type =>
        obtain ⟨owned, addressType, identity, loan, found, live, kind, referent, disjunction⟩ := ready
        cases disjunction with
        | inl loaned =>
            obtain ⟨rfl, unique⟩ := loaned
            exact ⟨loan, found⟩
        | inr shared =>
            obtain ⟨backing, rfl, parent, mode⟩ := shared
            exact Authority.Recorded.of_loanHeaded headed parent found

/-- Every input of an admitted batch has a recorded authority, derived from
its own readiness and the handed share shape. -/
theorem InvocationInputsReadyFor.recorded {program : RuntimeProgram} {world : World}
    {inputs : List InvocationInput} {footprint : List Address}
    (ready : InvocationInputsReadyFor program world footprint inputs)
    (headed : ∀ input ∈ inputs, input.authority.SharedHeaded) :
    ∀ input ∈ inputs, input.authority.Recorded world.loans :=
  fun input member => InvocationInput.ReadyFor.recorded (ready.member member) (headed input member)

end Glorious.Language
