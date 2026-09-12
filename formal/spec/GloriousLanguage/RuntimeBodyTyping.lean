import GloriousLanguage.RuntimeCoverageEquivariance

/-! Runtime-name transport of complete source-body typing. The choose and
handler cases consume actual semantic coverage transport, including its
universally quantified typed-world obligations. -/
namespace Glorious.Language

theorem RegionPermutation.typingContext_locals (permutation : RegionPermutation) (context : Typing.Context)
    (locals : List Kernel.Local) : permutation.typingContext { context with locals := locals } =
      { permutation.typingContext context with locals := locals.map (Kernel.Local.mapTerms permutation.term) } := rfl

theorem RegionPermutation.captureLocals (permutation : RegionPermutation) (captures : List Kernel.Capture) :
    Execution.CaptureLocals (captures.map (Kernel.Capture.mapTerms permutation.term)) =
      (Execution.CaptureLocals captures).map (Kernel.Local.mapTerms permutation.term) := by
  simp only [Execution.CaptureLocals,List.map_map,Function.comp_def,Kernel.Capture.mapTerms,Kernel.Local.mapTerms]

theorem Typing.CodeType.permute {program : Kernel.Program} (valid : ProgramWellFormed program.declarations)
    (inventory : Kernel.BodyInventory program) {context : Typing.Context} {code : Kernel.Code} {result : Term}
    (typed : Typing.CodeType program context code result) (permutation : RegionPermutation) :
    Typing.CodeType program (permutation.typingContext context) (permutation.code code) (permutation.term result) := by
  refine Typing.CodeType.rec
    (motive_1 := fun context code result _ => Typing.CodeType program (permutation.typingContext context)
      (permutation.code code) (permutation.term result))
    (motive_2 := fun context arms input result _ => Typing.ArmsType program (permutation.typingContext context)
      (arms.map (Kernel.Arm.mapTerms permutation.term)) (permutation.term input) (permutation.term result))
    (motive_3 := fun context handler input result _ => Typing.HandlerType program (permutation.typingContext context)
      (handler.mapTerms permutation.term) (permutation.term input) (permutation.term result))
    (motive_4 := fun context arms input result _ => Typing.CompletionType program (permutation.typingContext context)
      (arms.map (Kernel.Arm.mapTerms permutation.term)) (permutation.term input) (permutation.term result))
    (motive_5 := fun context arms result _ => Typing.OperationArmsType program (permutation.typingContext context)
      (arms.map (Kernel.OperationArm.mapTerms permutation.term)) (permutation.term result))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed
  all_goals simp only [RegionPermutation.code,Kernel.Code.mapTerms,Kernel.Code.transformTerms,
    Kernel.Arm.mapTerms,Kernel.Arm.transformTerms,Kernel.Handler.mapTerms,Kernel.Handler.transformTerms,
    Kernel.OperationArm.mapTerms,Kernel.OperationArm.transformTerms,List.map_nil,List.map_cons]
  · intro context place actual result writable located subtype
    exact .result (located.permute valid permutation) (subtype.permute valid permutation)
  · intro context localSlot atom next result atomTyped _ ih
    rw [permutation.typingContext_bind] at ih
    exact .bind (atomTyped.permute valid inventory permutation) ih
  · intro context localSlot code next result _ _ ihCode ihNext
    rw [permutation.typingContext_bind] at ihNext
    exact .evaluate ihCode ihNext
  · intro context destination source next type writable result toType fromType _ ih
    exact .assign (toType.permute valid permutation) (fromType.permute valid permutation) ih
  · intro context place next type writable result located _ ih
    exact .discard (located.permute valid permutation) ih
  · intro context localSlot call next result invocation subtype _ ih
    rw [permutation.typingContext_bind] at ih
    exact .invoke (invocation.permute valid permutation) (subtype.permute valid permutation) ih
  · intro context call result invocation subtype
    exact .tail (invocation.permute valid permutation) (subtype.permute valid permutation)
  · intro context id body result _ ih; exact .scope ih
  · intro context brand region type body _ ih
    apply Typing.CodeType.label
    simpa only [RegionPermutation.typingContext,List.map_cons,RegionPermutation.term,Term.renameRuntimeRegions] using ih
  · intro context subject arms type writable result located coverage _ ih
    exact .choose (located.permute valid permutation) (coverage.permute valid inventory permutation) ih
  · intro context id computation handler input result instances _ coverage _ ihHandler ihCode
    refine .handler ihHandler (coverage.permute valid inventory permutation) ?_
    simpa only [RegionPermutation.typingContext,RegionPermutation.term,Term.renameRuntimeRegions,List.map_cons,List.map_nil] using ihCode
  · intro context localSlot subject pattern id next type writable bindings result carrier arguments located patternTyped carrierFound shape _ ih
    rw [permutation.typingContext_bind] at ih
    exact .test (arguments := arguments.map permutation.term) (located.permute valid permutation) (patternTyped.permute valid permutation) carrierFound
      (by simp only [Kernel.Local.mapTerms,shape,RegionPermutation.term,Term.renameRuntimeRegions]) ih
  · intro context handle next mode region type writable result located _ ih
    refine .endLoan (mode := mode) (region := permutation.term region) (type := permutation.term type) (writable := writable) ?_ ih
    simpa only [RegionPermutation.term,Term.renameRuntimeRegions] using located.permute valid permutation
  · intro context body result _ ih
    exact .unsafeAllowed ih
  · intro context place next brand region residents writable result located _ ih
    refine .closeAvailable (brand := permutation.term brand) (region := permutation.term region)
      (residents := residents.map permutation.term) (writable := writable) ?_ ih
    simpa only [RegionPermutation.term,Term.renameRuntimeRegions] using located.permute valid permutation
  · intro context localSlot brand places next types result region located shape _ ih
    rw [permutation.typingContext_bind] at ih
    refine .reserve (types := types.map permutation.term) (region := permutation.term region) ?_
      (by simp only [Kernel.Local.mapTerms,shape,RegionPermutation.term,Term.renameRuntimeRegions]) ih
    clear ih shape
    induction located with
    | nil => exact .nil
    | cons first _ ih =>
      obtain ⟨writable,located⟩ := first
      exact .cons ⟨writable,located.permute valid permutation⟩ ih
  · intro context result; exact .abort
  · intro context code result _ ih
    apply Typing.CodeType.bottom
    simpa only [RegionPermutation.term,Term.renameRuntimeRegions] using ih
  · intro context input output; exact .nil
  · intro context pattern body arms input output bindings patternTyped distinct _ _ ihBody ihArms
    refine .cons (patternTyped.permute valid permutation) ?_ ?_ ihArms
    · simpa only [List.map_map,Function.comp_def,Kernel.Local.mapTerms] using distinct
    · simpa only [RegionPermutation.typingContext,List.map_append] using ihBody
  · intro context result completion operations captures input types captureTyped _ _ ihCompletion ihOperations
    refine .attached (captureTyped.permute valid permutation) ?_ ?_
    · simpa only [RegionPermutation.typingContext,permutation.captureLocals] using ihCompletion
    · simpa only [RegionPermutation.typingContext,permutation.captureLocals] using ihOperations
  · intro context input result equal; exact .identity (equal.permute valid permutation)
  · intro context completion input result notEmpty coverage _ ih
    exact .arms (fun empty => notEmpty (List.map_eq_nil_iff.mp empty)) (coverage.permute valid inventory permutation) ih
  · intro context result; exact .nil
  · intro context id family item patterns continuation body rest result operation signature bindings output
      selected patternTyped shape _ _ ihBody ihRest
    refine .cons (signature := permutation.signature signature) (bindings := bindings.map (Kernel.Local.mapTerms permutation.term))
      (output := permutation.term output) (by simpa only [List.map_append] using selected.permute valid permutation)
      (patternTyped.permute valid permutation) ?_ ?_ ihRest
    · rcases shape with ⟨terminal,absent,outputEq⟩ | ⟨notTerminal,quantity,quantityEq,automatic | explicit⟩
      · exact Or.inl ⟨terminal,by rw [absent]; rfl,congrArg permutation.term outputEq⟩
      · exact Or.inr ⟨notTerminal,quantity,quantityEq,Or.inl ⟨by rw [automatic.1]; rfl,automatic.2.1,
          congrArg permutation.term automatic.2.2⟩⟩
      · obtain ⟨localSlot,brand,present,localType,outputEq⟩ := explicit
        exact Or.inr ⟨notTerminal,quantity,quantityEq,Or.inr ⟨localSlot.mapTerms permutation.term,brand,
          by rw [present]; rfl,by simp only [Kernel.Local.mapTerms,localType,RegionPermutation.term,Term.renameRuntimeRegions,
            RegionPermutation.signature,Signature.mapTerms],
          congrArg permutation.term outputEq⟩⟩
    · simpa only [RegionPermutation.typingContext,List.map_append,Option.toList_map] using ihBody

theorem Typing.FunctionType.permute {program : Kernel.Program} (valid : ProgramWellFormed program.declarations)
    (inventory : Kernel.BodyInventory program) {function : Kernel.Function}
    (typed : Typing.FunctionType program function) (permutation : RegionPermutation) :
    Typing.FunctionType program (permutation.function function) := by
  obtain ⟨declaration,found,parameters,distinct,captureDistinct,separate,body⟩ := typed
  refine ⟨declaration,found,?_,?_,?_,?_,?_⟩
  · simpa only [RegionPermutation.function,Kernel.Function.mapTerms,Kernel.Function.transformTerms,
      Kernel.Local.mapTerms,Signature.mapTerms,List.map_map,Function.comp_def] using congrArg (List.map permutation.term) parameters
  · simpa only [RegionPermutation.function,Kernel.Function.mapTerms,Kernel.Function.transformTerms,
      List.map_map,Function.comp_def,Kernel.Local.mapTerms] using distinct
  · simpa only [RegionPermutation.function,Kernel.Function.mapTerms,Kernel.Function.transformTerms,
      List.map_map,Function.comp_def,Kernel.Local.mapTerms] using captureDistinct
  · intro formal member capture present
    obtain ⟨original,oldMember,rfl⟩ := List.mem_map.mp member
    obtain ⟨oldCapture,oldPresent,rfl⟩ := List.mem_map.mp present
    exact separate original oldMember oldCapture oldPresent
  · have transported := body.permute valid inventory permutation
    simp only [RegionPermutation.typingContext,RegionPermutation.context] at transported
    change Typing.CodeType program
      { static := ⟨(permutation.signature function.signature).generics,(permutation.signature function.signature).constraints,
          0,declaration.header.module,false⟩
        locals := (function.captures ++ function.parameters).map (Kernel.Local.mapTerms permutation.term)
        labels := (function.namedExit.toList.map (fun id => (id,.rigid function.activationRegion .region 0,function.signature.result))).map
          (fun (id,region,type) => (id,permutation.term region,permutation.term type))
        effects := permutation.term function.signature.effects }
      (permutation.code function.body) (permutation.term function.signature.result) at transported
    simpa only [RegionPermutation.function,Kernel.Function.mapTerms,Kernel.Function.transformTerms,
      RegionPermutation.typingContext,RegionPermutation.context,RegionPermutation.binder,Signature.mapTerms,
      RegionPermutation.constraint,List.map_append,List.map_map,Function.comp_def,RegionPermutation.code,
      Kernel.Code.mapTerms,RegionPermutation.term,Term.renameRuntimeRegions,RegionPermutation.signature] using transported

end Glorious.Language
