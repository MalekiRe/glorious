import GloriousLanguage.RuntimeCoverageEquivariance

/-! Runtime-name transport of complete source-body typing. The choose and
handler cases consume actual semantic coverage transport, including its
universally quantified typed-world obligations. -/
namespace Glorious.Language

theorem RegionPermutation.typingContext_bindLocals (permutation : RegionPermutation) (context : Typing.Context)
    (locals : List Kernel.Local) : permutation.typingContext (context.bindLocals locals) =
      (permutation.typingContext context).bindLocals (locals.map (Kernel.Local.mapTerms permutation.term)) := by
  induction locals generalizing context with
  | nil => rfl
  | cons localSlot rest ih =>
    simpa only [Typing.Context.bindLocals,List.foldl_cons,List.map_cons,permutation.typingContext_bind] using
      ih (context.bind localSlot)

theorem RegionPermutation.typingContext_bindRegion (permutation : RegionPermutation) (context : Typing.Context)
    (id : Identity) : permutation.typingContext (context.bindRegion id) =
      (permutation.typingContext context).bindRegion id := rfl

theorem RegionPermutation.typingContext_bindBrand (permutation : RegionPermutation) (context : Typing.Context)
    (id : Identity) : permutation.typingContext (context.bindBrand id) =
      (permutation.typingContext context).bindBrand id := rfl

theorem RegionPermutation.local_resumptionBrand (permutation : RegionPermutation) (localSlot : Kernel.Local) :
    (localSlot.mapTerms permutation.term).resumptionBrand = localSlot.resumptionBrand := by
  cases localSlot with
  | mk id type mutable =>
    cases type <;> simp only [Kernel.Local.mapTerms,Kernel.Local.resumptionBrand,
      RegionPermutation.term,Term.renameRuntimeRegions]
    rename_i brand _ _ _ _
    cases brand <;> simp only [Term.renameRuntimeRegions]

theorem RegionPermutation.typingContext_bindResumption (permutation : RegionPermutation) (context : Typing.Context)
    (continuation : Option Kernel.Local) : permutation.typingContext (context.bindResumption continuation) =
      (permutation.typingContext context).bindResumption (continuation.map (Kernel.Local.mapTerms permutation.term)) := by
  cases continuation with
  | none => rfl
  | some localSlot =>
    simp only [Typing.Context.bindResumption,Option.map,Option.bind,permutation.local_resumptionBrand]
    cases localSlot.resumptionBrand <;> rfl

theorem Typing.TermsScoped.permute {context : Typing.Context} {terms : List Term}
    (admitted : Typing.TermsScoped context terms) (permutation : RegionPermutation) :
    Typing.TermsScoped (permutation.typingContext context) (terms.map permutation.term) := by
  intro term member
  obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
  exact (admitted original present).permute permutation

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
  · intro context place actual result writable located admitted subtype
    exact .result (located.permute valid permutation) (admitted.permute permutation) (subtype.permute valid permutation)
  · intro context localSlot atom next result atomTyped admitted _ ih
    rw [permutation.typingContext_bind] at ih
    refine .bind (atomTyped.permute valid inventory permutation) ?_ ih
    simpa only [Kernel.Local.mapTerms,Kernel.Atom.terms_mapTerms,List.map_cons] using admitted.permute permutation
  · intro context localSlot code next result _ _ ihCode ihNext
    rw [permutation.typingContext_bind] at ihNext
    exact .evaluate ihCode ihNext
  · intro context destination source next type writable result toType fromType _ ih
    exact .assign (toType.permute valid permutation) (fromType.permute valid permutation) ih
  · intro context place next type writable result located _ ih
    exact .discard (located.permute valid permutation) ih
  · intro context localSlot call next result invocation admitted subtype _ ih
    rw [permutation.typingContext_bind] at ih
    refine .invoke (invocation.permute valid permutation) ?_ (subtype.permute valid permutation) ih
    have termsEq := call.terms_mapTerms permutation.term
    change (call.transformTerms permutation.term (Signature.mapTerms permutation.term)).terms = call.terms.map permutation.term at termsEq
    simpa only [Kernel.Local.mapTerms,termsEq,List.map_cons]
      using admitted.permute permutation
  · intro context call result invocation admitted subtype
    refine .tail (invocation.permute valid permutation) ?_ (subtype.permute valid permutation)
    have termsEq := call.terms_mapTerms permutation.term
    change (call.transformTerms permutation.term (Signature.mapTerms permutation.term)).terms = call.terms.map permutation.term at termsEq
    simpa only [termsEq,List.map_cons] using admitted.permute permutation
  · intro context id body result fresh admitted _ ih
    rw [permutation.typingContext_bindRegion] at ih
    exact .scope fresh (admitted.permute permutation) ih
  · intro context brand region type body member current fresh admitted _ ih
    apply Typing.CodeType.label (context := permutation.typingContext context) member current fresh (admitted.permute permutation)
    simpa only [RegionPermutation.typingContext,Typing.Context.bindBrand,RegionPermutation.context,
      List.map_cons,RegionPermutation.term,Term.renameRuntimeRegions] using ih
  · intro context subject arms type writable result located admitted coverage _ ih
    exact .choose (located.permute valid permutation) (admitted.permute permutation) (coverage.permute valid inventory permutation) ih
  · intro context id computation handler input result instances _ admitted coverage _ ihHandler ihCode
    refine .handler ihHandler ?_ (coverage.permute valid inventory permutation) ?_
    · simpa only [List.map_cons] using admitted.permute permutation
    simpa only [RegionPermutation.typingContext,RegionPermutation.term,Term.renameRuntimeRegions,List.map_cons,List.map_nil] using ihCode
  · intro context localSlot subject pattern id next type writable bindings result carrier arguments
      located fresh admitted patternTyped carrierFound shape resultAdmitted _ ih
    rw [permutation.typingContext_bind,permutation.typingContext_bindBrand] at ih
    refine .test (arguments := arguments.map permutation.term) (located.permute valid permutation) fresh ?_
      (patternTyped.permute valid permutation) carrierFound
      (by simp only [Kernel.Local.mapTerms,shape,RegionPermutation.term,Term.renameRuntimeRegions])
      (resultAdmitted.permute permutation) ih
    simpa only [Kernel.Local.mapTerms,Kernel.Pattern.terms_mapTerms,List.map_cons,
      permutation.typingContext_bindBrand] using admitted.permute permutation
  · intro context handle next mode region type writable result located _ ih
    refine .endLoan (mode := mode) (region := permutation.term region) (type := permutation.term type) (writable := writable) ?_ ih
    simpa only [RegionPermutation.term,Term.renameRuntimeRegions] using located.permute valid permutation
  · intro context body result _ ih
    exact .unsafeAllowed ih
  · intro context place next brand region residents writable result located _ ih
    refine .closeAvailable (brand := permutation.term brand) (region := permutation.term region)
      (residents := residents.map permutation.term) (writable := writable) ?_ ih
    simpa only [RegionPermutation.term,Term.renameRuntimeRegions] using located.permute valid permutation
  · intro context localSlot brand places next types result region located fresh admitted shape _ ih
    rw [permutation.typingContext_bind,permutation.typingContext_bindBrand] at ih
    refine .reserve (types := types.map permutation.term) (region := permutation.term region) ?_
      fresh (by simpa only [List.map_cons] using admitted.permute permutation)
      (by simp only [Kernel.Local.mapTerms,shape,RegionPermutation.term,Term.renameRuntimeRegions]) ih
    clear ih shape admitted
    induction located with
    | nil => exact .nil
    | cons first _ ih =>
      obtain ⟨writable,located⟩ := first
      exact .cons ⟨writable,located.permute valid permutation⟩ ih
  · intro context result admitted; exact .abort (admitted.permute permutation)
  · intro context code result admitted _ ih
    apply Typing.CodeType.bottom (context := permutation.typingContext context) (admitted.permute permutation)
    simpa only [RegionPermutation.term,Term.renameRuntimeRegions] using ih
  · intro context input output; exact .nil
  · intro context pattern body arms input output bindings patternTyped distinct _ _ ihBody ihArms
    refine .cons (patternTyped.permute valid permutation) ?_ ?_ ihArms
    · simpa only [List.map_map,Function.comp_def,Kernel.Local.mapTerms] using distinct
    · simpa only [permutation.typingContext_bindLocals] using ihBody
  · intro context result completion operations captures input types captureTyped admitted _ _ ihCompletion ihOperations
    refine .attached (captureTyped.permute valid permutation) ?_ ?_ ?_
    · simpa only [List.map_cons,List.map_map,Function.comp_def,Kernel.Capture.mapTerms] using admitted.permute permutation
    · simpa only [RegionPermutation.typingContext,permutation.captureLocals] using ihCompletion
    · simpa only [RegionPermutation.typingContext,permutation.captureLocals] using ihOperations
  · intro context input result equal; exact .identity (equal.permute valid permutation)
  · intro context completion input result notEmpty coverage _ ih
    exact .arms (fun empty => notEmpty (List.map_eq_nil_iff.mp empty)) (coverage.permute valid inventory permutation) ih
  · intro context result; exact .nil
  · intro context id family item patterns continuation body rest result operation signature bindings output
      found selected patternTyped shape fresh admitted _ _ ihBody ihRest
    refine .cons (signature := permutation.signature signature) (bindings := bindings.map (Kernel.Local.mapTerms permutation.term))
      (output := permutation.term output) found
      (by simpa only [List.map_append,RegionPermutation.typingContext] using selected.permute valid permutation)
      (patternTyped.permute valid permutation) ?_ ?_ ?_ ?_ ihRest
    · rcases shape with ⟨terminal,absent,outputEq⟩ | ⟨notTerminal,quantity,quantityEq,automatic | explicit⟩
      · exact Or.inl ⟨terminal,by rw [absent]; rfl,congrArg permutation.term outputEq⟩
      · exact Or.inr ⟨notTerminal,quantity,quantityEq,Or.inl ⟨by rw [automatic.1]; rfl,automatic.2.1,
          congrArg permutation.term automatic.2.2⟩⟩
      · obtain ⟨localSlot,brand,present,localType,outputEq⟩ := explicit
        exact Or.inr ⟨notTerminal,quantity,quantityEq,Or.inr ⟨localSlot.mapTerms permutation.term,brand,
          by rw [present]; rfl,by simp only [Kernel.Local.mapTerms,localType,RegionPermutation.term,Term.renameRuntimeRegions,
            RegionPermutation.signature,Signature.mapTerms],
          congrArg permutation.term outputEq⟩⟩
    · intro brand selected
      apply fresh brand
      cases continuation with
      | none => exact selected
      | some localSlot =>
        simpa only [Option.map,Option.bind,permutation.local_resumptionBrand] using selected
    · simpa only [List.map_cons,List.map_map,Function.comp_def,Kernel.Local.mapTerms,Option.toList_map,
        permutation.typingContext_bindResumption] using admitted.permute permutation
    · rw [permutation.typingContext_bindLocals,permutation.typingContext_bindResumption] at ihBody
      simpa only [List.map_append,Option.toList_map] using ihBody

theorem Typing.FunctionType.permute {program : Kernel.Program} (valid : ProgramWellFormed program.declarations)
    (inventory : Kernel.BodyInventory program) {function : Kernel.Function}
    (typed : Typing.FunctionType program function) (permutation : RegionPermutation) :
    Typing.FunctionType program (permutation.function function) := by
  obtain ⟨declaration,found,parameters,distinct,captureDistinct,separate,closed,body⟩ := typed
  refine ⟨declaration,found,?_,?_,?_,?_,?_,?_⟩
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
  · intro term member
    simp only [RegionPermutation.function,Kernel.Function.mapTerms,Kernel.Function.transformTerms,
      Signature.terms_mapTerms,List.map_append,List.map_map,Function.comp_def,Kernel.Local.mapTerms] at member
    have originalMember : term ∈ (function.signature.terms ++ (function.captures ++ function.parameters).map (·.type)).map
        permutation.term := by
      simpa only [List.map_append,List.map_map,Function.comp_def] using member
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp originalMember
    exact (closed original present).permute permutation
  · have transported := body.permute valid inventory permutation
    simp only [Typing.FunctionContext,RegionPermutation.typingContext,RegionPermutation.context] at transported
    change Typing.CodeType program
      { static := ⟨(permutation.signature function.signature).generics,(permutation.signature function.signature).constraints,
          0,declaration.header.module,false,
          ⟨[function.activationRegion],function.namedExit.toList,some function.activationRegion⟩⟩
        locals := (function.captures ++ function.parameters).map (Kernel.Local.mapTerms permutation.term)
        labels := (function.namedExit.toList.map (fun id => (id,.scopedRegion function.activationRegion,function.signature.result))).map
          (fun (id,region,type) => (id,permutation.term region,permutation.term type))
        effects := permutation.term function.signature.effects }
      (permutation.code function.body) (permutation.term function.signature.result) at transported
    simpa only [RegionPermutation.function,Kernel.Function.mapTerms,Kernel.Function.transformTerms,
      Typing.FunctionContext,RegionPermutation.typingContext,RegionPermutation.context,RegionPermutation.binder,Signature.mapTerms,
      RegionPermutation.constraint,List.map_append,List.map_map,Function.comp_def,RegionPermutation.code,
      Kernel.Code.mapTerms,RegionPermutation.term,Term.renameRuntimeRegions,RegionPermutation.signature] using transported

end Glorious.Language
