import GloriousLanguage.Machine

/-! Historical authority provenance of the same executable control products.
Recording means that a loan identity has an actual table entry, including
after it ends. It is not liveness, permission, or a second loan inventory. -/
namespace Glorious.Language

theorem Authority.Recorded.parentLoan {authority : Authority} {loans : Table Loan} {id : Identity}
    (recorded : authority.Recorded loans) (parent : authority.parentLoan = some id) :
    ∃ loan, loans.get id = some loan := by
  induction authority with
  | owner => cases parent
  | loan identity => cases parent; exact recorded
  | shared backing ih => exact ih recorded parent

theorem Authority.Recorded.loan_bound {world : World} {authority : Authority} {id : Identity}
    (well : world.WellFormed) (recorded : authority.Recorded world.loans)
    (parent : authority.parentLoan = some id) : id < world.nextLoan := by
  obtain ⟨loan,found⟩ := recorded.parentLoan parent
  exact World.loanBounds well found

def AuthoritySupport.Recorded (authorities : List Authority) (loans : Table Loan) : Prop :=
  ∀ authority ∈ authorities, authority.Recorded loans

theorem AuthoritySupport.Recorded.mono {authorities : List Authority} {before after : Table Loan}
    (recorded : AuthoritySupport.Recorded authorities before)
    (retained : ∀ (authority : Authority), authority.Recorded before → authority.Recorded after) :
    AuthoritySupport.Recorded authorities after :=
  fun authority member => retained authority (recorded authority member)

@[simp] theorem AuthoritySupport.recorded_nil (loans : Table Loan) : Recorded [] loans := by
  simp [Recorded]

@[simp] theorem AuthoritySupport.recorded_cons {authority : Authority} {authorities : List Authority}
    {loans : Table Loan} : Recorded (authority :: authorities) loans ↔ authority.Recorded loans ∧ Recorded authorities loans := by
  simp [Recorded]

@[simp] theorem AuthoritySupport.recorded_append {left right : List Authority} {loans : Table Loan} :
    Recorded (left ++ right) loans ↔ Recorded left loans ∧ Recorded right loans := by
  simp [Recorded,or_imp,forall_and]

@[simp] theorem AuthoritySupport.recorded_map {α : Type} {items : List α}
    {authority : α → Authority} {loans : Table Loan} :
    Recorded (items.map authority) loans ↔ ∀ item ∈ items, (authority item).Recorded loans := by
  simp only [Recorded,List.mem_map]
  constructor
  · intro recorded item member
    exact recorded _ ⟨item,member,rfl⟩
  · rintro recorded current ⟨item,member,rfl⟩
    exact recorded item member

@[simp] theorem AuthoritySupport.recorded_flatMap {α : Type} {items : List α}
    {support : α → List Authority} {loans : Table Loan} :
    Recorded (items.flatMap support) loans ↔ ∀ item ∈ items, Recorded (support item) loans := by
  simp only [Recorded,List.mem_flatMap]
  constructor
  · intro recorded item member authority inside
    exact recorded authority ⟨item,member,inside⟩
  · rintro recorded authority ⟨item,member,inside⟩
    exact recorded item member authority inside

namespace Kernel

def PatternAction.authoritySupport : PatternAction → List Authority
  | .bind _ _ authority _ | .consumeShell _ authority | .dispose _ authority => [authority]

end Kernel

namespace Execution

open Kernel

def Context.authoritySupport (context : Context) : List Authority := context.environment.map Binding.authority

def InstalledHandler.authoritySupport (handler : InstalledHandler) : List Authority :=
  handler.environment.authoritySupport ++ handler.computation.authoritySupport ++ handler.outer.authoritySupport

def ForeignSession.authoritySupport (session : ForeignSession) : List Authority :=
  session.call.context.authoritySupport ++ session.exposed.map ResolvedPlace.authority

def EntrySource.authoritySupport : EntrySource → List Authority
  | .supplied inputs => inputs.map InvocationInput.authority
  | .resident receiver _ inputs => receiver.authority :: inputs.map InvocationInput.authority
  | .contextual receiver _ witness _ inputs =>
      receiver.authority :: witness.authority :: inputs.map InvocationInput.authority

def Task.authoritySupport : Task → List Authority
  | .run context _ | .atom context _ _ _ | .yield context _ | .apply context _ _ => context.authoritySupport
  | .enter context _ source _ => context.authoritySupport ++ source.authoritySupport
  | .destroy context _ authority next | .destroyFields context _ authority _ next =>
      context.authoritySupport ++ authority :: next.authoritySupport
  | .finishShell _ authority next | .transfer _ authority _ next => authority :: next.authoritySupport
  | .retire _ next | .closeRegion _ next => next.authoritySupport
  | .closeLoan loan next | .releaseLoan loan next => .loan loan :: next.authoritySupport
  | .cleanup context _ next | .cancel context _ next => context.authoritySupport ++ next.authoritySupport
  | .pattern context actions _ => context.authoritySupport ++ actions.flatMap PatternAction.authoritySupport
  | .perform context _ _ payload | .primitive context _ _ _ payload _ =>
      context.authoritySupport ++ payload.map ResolvedPlace.authority
  | .resume context _ argument _ | .leave context _ argument => context.authoritySupport ++ [argument.authority]
  | .finishClause handler _ _ _ => handler.authoritySupport
  | .foreign session _ | .foreignCallbackReturned session _ _ _ => session.authoritySupport
  | .stopped _ | .fatal _ => []

def Frame.authoritySupport : Frame → List Authority
  | .binding context _ _ | .activation context _ _ | .scope context _ _ | .label context _ _ _
  | .resumed context | .tailResume context _ => context.authoritySupport
  | .handler installed _ => installed.authoritySupport
  | .serviced installed _ clause _ | .completion installed _ clause =>
      installed.authoritySupport ++ clause.authoritySupport
  | .hook context _ authority _ loan next =>
      context.authoritySupport ++ authority :: .loan loan :: next.authoritySupport
  | .foreign _ => []
  | .hostCallback session _ _ lease _ =>
      session.authoritySupport ++ lease.toList.map (fun lease => .loan lease.loan)

def Suspension.controlAuthoritySupport (suspension : Suspension) : List Authority :=
  suspension.context.authoritySupport ++ suspension.handler.authoritySupport ++ suspension.frames.flatMap Frame.authoritySupport

end Execution
end Glorious.Language
