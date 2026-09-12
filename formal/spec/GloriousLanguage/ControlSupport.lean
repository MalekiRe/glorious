import GloriousLanguage.Machine

/-! Structural authority support of the actual executable control products.
Snapshot relocation and historical provenance consume this same projection. -/
namespace Glorious.Language

def RootSupport.Below (roots : List Identity) (limit : Identity) : Prop :=
  ∀ root ∈ roots, root < limit

theorem RootSupport.Below.mono {roots : List Identity} {first last : Identity}
    (bounded : RootSupport.Below roots first) (limit : first ≤ last) : RootSupport.Below roots last :=
  fun root member => Nat.lt_of_lt_of_le (bounded root member) limit

@[simp] theorem RootSupport.below_nil (limit : Identity) : RootSupport.Below [] limit := by
  simp [Below]

@[simp] theorem RootSupport.below_cons {root : Identity} {roots : List Identity} {limit : Identity} :
    RootSupport.Below (root :: roots) limit ↔ root < limit ∧ RootSupport.Below roots limit := by
  simp [Below]

@[simp] theorem RootSupport.below_append {left right : List Identity} {limit : Identity} :
    RootSupport.Below (left ++ right) limit ↔ RootSupport.Below left limit ∧ RootSupport.Below right limit := by
  simp [Below, or_imp, forall_and]

@[simp] theorem RootSupport.below_flatMap {α : Type} {items : List α}
    {support : α → List Identity} {limit : Identity} :
    RootSupport.Below (items.flatMap support) limit ↔ ∀ item ∈ items, RootSupport.Below (support item) limit := by
  simp only [Below, List.mem_flatMap]
  constructor
  · intro bounded item member root inside
    exact bounded root ⟨item,member,inside⟩
  · rintro bounded root ⟨item,member,inside⟩
    exact bounded item member root inside


namespace Kernel

def PatternAction.authoritySupport : PatternAction → List Authority
  | .bind _ _ authority _ | .consumeShell _ authority | .dispose _ authority => [authority]

end Kernel

namespace Execution

open Kernel

def Context.authoritySupport (context : Context) : List Authority :=
  context.environment.map StorageBinding.authority ++
    context.resourceContracts.flatMap (fun contract => contract.inputs.map StorageBinding.authority)

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
  | .run context _ | .atom context _ _ _ | .yield context _ | .apply context _ _ | .stopped context _ => context.authoritySupport
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
  | .fatal _ => []

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
