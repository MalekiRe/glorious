import GloriousLanguage.OperationSignatures
import GloriousLanguage.StorageConstruction

/-! Source-derived continuation compatibility and the common empty-input
value constructor close logical handle creation. Physical allocation is a
separate successful request, never inferred from world typing alone. -/
namespace Glorious.Language.Execution

open Kernel

/-- Initialization of a continuation handle follows from its actual fresh
allocation and source/runtime type contract. No initialized post-world or
complete CreatesContinuation witness is supplied. -/
theorem CreatesContinuation.of_allocation {program : Kernel.Program} {context : Context}
    {before allocated : World} {id : Identity} {signature : Signature} {answer effects : Term}
    {quantity : Quantity} {localSlot : Local} {layout : Layout} {address : Address}
    (compatible : ContinuationBindingType program.declarations context.static id signature answer effects quantity localSlot.type)
    (allocation : Allocates program.declarations before (.localSlot context.activation context.scope) context.region
      localSlot.type layout localSlot.mutable address allocated) :
    ∃ after, CreatesContinuation program context before id signature answer effects quantity localSlot address after ∧
      NewValue program.declarations allocated address localSlot.type (.continuation id) [] after := by
  obtain ⟨after,constructed⟩ := allocation.empty_value (.continuation id)
  exact ⟨after,⟨allocated,layout,compatible,allocation,constructed⟩,constructed⟩

/-- Actual source selection supplies the continuation type, including the
converted operation components and the exact declared handler result. The
only storage premise is the successful allocation at the actual clause home. -/
theorem SelectsOperation.creates_continuation {program : Kernel.Program} {before : State}
    {handler : InstalledHandler} {id : DeclId} {arguments : List Term} {payload : List ResolvedPlace}
    {arm : OperationArm} {source : Typing.Context} {operation : OperationDefinition} {signature : Signature}
    {quantity : Quantity} {lexical localSlot : Local} {clause : Context} {withRegion initial allocated : World}
    {layout : Layout} {address : Address}
    (valid : ProgramWellFormed program.declarations)
    (selected : SelectsOperation program before.world handler id arguments payload arm)
    (armsTyped : Typing.OperationArmsType program source handler.syntaxNode.operations handler.syntaxNode.result)
    (actual : OperationInstance program id arguments operation signature)
    (quantityAt : operation.quantity = some quantity) (continuation : arm.continuation = some lexical)
    (started : StartsResumptionClause before handler lexical clause localSlot withRegion)
    (allocation : Allocates program.declarations initial (.localSlot clause.activation clause.scope) clause.region
      localSlot.type layout localSlot.mutable address allocated) :
    ∃ after, CreatesContinuation program clause initial before.nextContinuation signature
        (clause.term handler.syntaxNode.result) signature.effects quantity localSlot address after ∧
      NewValue program.declarations allocated address localSlot.type (.continuation before.nextContinuation) [] after :=
  CreatesContinuation.of_allocation
    (selected.continuation_binding_type valid armsTyped actual quantityAt continuation started) allocation

end Glorious.Language.Execution
