import GloriousLanguage.ControlAuthority
import GloriousLanguage.ActivationOrigin

/-! Address provenance of executable control. This is support of the actual
task, frames and captured control, not another environment or ownership table.
Code contains lexical places; every runtime address appears in the products
below. Resident closure fields, pointers and references remain in `World` and
are governed by its existing storage and value-typing invariants. -/
namespace Glorious.Language

namespace Kernel

def InvocationInput.rootSupport (input : InvocationInput) : List Identity := [input.storage.root]

def PatternAction.rootSupport : PatternAction → List Identity
  | .bind _ address _ _ | .consumeShell address _ | .dispose address _ => [address.root]

end Kernel

namespace Execution

open Kernel

def Context.rootSupport (context : Context) : List Identity :=
  context.environment.map (fun binding => binding.address.root)

def InstalledHandler.rootSupport (handler : InstalledHandler) : List Identity :=
  handler.environment.rootSupport ++ handler.computation.rootSupport ++ handler.outer.rootSupport

def ForeignCall.rootSupport (call : ForeignCall) : List Identity :=
  call.context.rootSupport ++ call.destination.root :: call.operands.map Address.root

def ForeignSession.rootSupport (session : ForeignSession) : List Identity :=
  session.call.rootSupport ++ session.exposed.map (fun place => place.address.root)

def EntrySource.rootSupport : EntrySource → List Identity
  | .supplied inputs => inputs.flatMap InvocationInput.rootSupport
  | .resident receiver _ inputs => receiver.address.root :: inputs.flatMap InvocationInput.rootSupport
  | .contextual receiver _ witness _ inputs =>
      receiver.address.root :: witness.address.root :: inputs.flatMap InvocationInput.rootSupport

def Task.rootSupport : Task → List Identity
  | .run context _ | .apply context _ _ => context.rootSupport
  | .atom context destination _ _ | .yield context destination => context.rootSupport ++ [destination.root]
  | .enter context _ source _ => context.rootSupport ++ source.rootSupport
  | .destroy context address _ next | .destroyFields context address _ _ next =>
      context.rootSupport ++ address.root :: next.rootSupport
  | .finishShell address _ next => address.root :: next.rootSupport
  | .retire root next => root :: next.rootSupport
  | .cleanup context roots next => context.rootSupport ++ roots ++ next.rootSupport
  | .closeRegion _ next | .closeLoan _ next | .releaseLoan _ next => next.rootSupport
  | .transfer source _ destination next => source.root :: destination.root :: next.rootSupport
  | .pattern context actions _ => context.rootSupport ++ actions.flatMap PatternAction.rootSupport
  | .perform context _ _ payload => context.rootSupport ++ payload.map (fun place => place.address.root)
  | .resume context _ argument _ | .leave context _ argument => context.rootSupport ++ [argument.address.root]
  | .cancel context _ next => context.rootSupport ++ next.rootSupport
  | .finishClause handler _ _ result => handler.rootSupport ++ [result.root]
  | .primitive context destination _ _ operands _ =>
      context.rootSupport ++ destination.root :: operands.map (fun place => place.address.root)
  | .foreign session _ => session.rootSupport
  | .foreignCallbackReturned session _ result _ => session.rootSupport ++ [result.root]
  | .stopped result => [result.root]
  | .fatal _ => []

def Frame.rootSupport : Frame → List Identity
  | .binding context destination _ => context.rootSupport ++ [destination.root]
  | .activation context _ _ | .scope context _ _ | .label context _ _ _
  | .resumed context | .tailResume context _ => context.rootSupport
  | .handler installed _ => installed.rootSupport
  | .serviced installed _ clause _ | .completion installed _ clause =>
      installed.rootSupport ++ clause.rootSupport
  | .hook context address _ handle _ next =>
      context.rootSupport ++ address.root :: handle.root :: next.rootSupport
  | .foreign _ => []
  | .hostCallback session _ _ lease _ =>
      session.rootSupport ++ (lease.toList.map (fun lease => lease.handle.root))

def Suspension.controlRootSupport (suspension : Suspension) : List Identity :=
  suspension.context.rootSupport ++ suspension.handler.rootSupport ++ suspension.frames.flatMap Frame.rootSupport

/-- Bounds are historical, not liveness assertions: a canceled or transferred
frame can retain stale addresses, but can never contain a future root identity.
Saved support uses the same immutable frontier as the actual capture inventory. -/
structure State.ControlWellFormed (state : State) : Prop where
  suspensions : state.SuspensionsWellFormed
  task : RootSupport.Below state.task.rootSupport state.world.nextRoot
  frames : RootSupport.Below (state.frames.flatMap Frame.rootSupport) state.world.nextRoot
  saved : ∀ id suspension, state.resumptions.get id = some suspension →
    RootSupport.Below suspension.controlRootSupport suspension.captureRootLimit
  taskAuthorities : AuthoritySupport.Recorded state.task.authoritySupport state.world.loans
  frameAuthorities : AuthoritySupport.Recorded (state.frames.flatMap Frame.authoritySupport) state.world.loans
  savedAuthorities : ∀ id suspension, state.resumptions.get id = some suspension →
    AuthoritySupport.Recorded suspension.controlAuthoritySupport state.world.loans
  activations : state.ActivationsWellFormed

theorem State.ControlWellFormed.saved_current {state : State} (valid : state.ControlWellFormed)
    {id : Identity} {suspension : Suspension} (found : state.resumptions.get id = some suspension) :
    RootSupport.Below suspension.controlRootSupport state.world.nextRoot :=
  (valid.saved id suspension found).mono (valid.suspensions.frontier id suspension found)

theorem State.ControlWellFormed.no_future_saved {state : State} (valid : state.ControlWellFormed)
    {id : Identity} {suspension : Suspension} (found : state.resumptions.get id = some suspension)
    {root : Identity} (future : state.world.nextRoot ≤ root) : root ∉ suspension.controlRootSupport := by
  intro member
  exact Nat.not_lt_of_ge future (valid.saved_current found root member)

/-- An old saved authority cannot anticipate a future loan identity, even
when its referenced address already exists. Ended loan records remain valid
historical evidence, but do not recover access permission. -/
theorem State.ControlWellFormed.no_future_saved_authority {state : State} (valid : state.ControlWellFormed)
    (well : state.world.WellFormed) {id loan : Identity} {suspension : Suspension}
    (found : state.resumptions.get id = some suspension) (future : state.world.nextLoan ≤ loan) :
    ∀ authority ∈ suspension.controlAuthoritySupport, authority.parentLoan ≠ some loan := by
  intro authority member parent
  exact Nat.not_lt_of_ge future ((valid.savedAuthorities id suspension found authority member).loan_bound well parent)

end Execution
end Glorious.Language
