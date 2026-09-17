import GloriousLanguage.ProjectionStorage
import GloriousLanguage.LiteralExecution
import GloriousLanguage.Contracts

/-! Static primitive admission and runtime dispatch select the same manifest
binding and the same recursively resolved operand addresses. -/
namespace Glorious.Language

theorem Manifest.WellFormed.binding_unique {target : TargetProfile} {manifest : Manifest}
    {left right : RuntimeBinding} (valid : manifest.WellFormed target)
    (first : left ∈ manifest.bindings) (second : right ∈ manifest.bindings)
    (identity : left.declaration = right.declaration) : left = right := by
  obtain ⟨i,hi,atLeft⟩ := List.mem_iff_getElem.mp first
  obtain ⟨j,hj,atRight⟩ := List.mem_iff_getElem.mp second
  have indexEqual : i = j := (List.getElem?_inj (by simpa using hi) valid.2.2.1).mp (by
    simp only [List.getElem?_map,List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj,
      Option.map_some,atLeft,atRight,identity])
  subst j
  exact atLeft.symm.trans atRight

theorem ProgramWellFormed.manifest {program : Program} (valid : ProgramWellFormed program) :
    program.input.manifest.WellFormed program.input.target := valid.1.1.2.2.2.2.2

namespace Execution

theorem ResolvedOperands.deterministic {world : World} {environment : Kernel.Environment}
    {places : List Kernel.Place} {left right : List ResolvedPlace}
    (first : ResolvedOperands world environment places left)
    (second : ResolvedOperands world environment places right) : left = right := by
  induction first generalizing right with
  | nil => cases second; rfl
  | @cons place entry places entries first rest ih =>
      cases second with
      | @cons _ other _ _ second remaining =>
          obtain ⟨address,authority⟩ := first.1.deterministic second.1
          have head : entry = other := by cases entry; cases other; simp_all
          rw [head,ih remaining]

theorem AtomStep.primitive_cases {program : Kernel.Program} {before after : State} {event : Option Event}
    {context : Context} {destination : Address} {id : DeclId} {arguments : List Term}
    {operands : List Kernel.Place} {next : Kernel.Code}
    (task : before.task = .atom context destination (.primitive id arguments operands) next)
    (step : AtomStep program before event after) :
    ∃ binding addresses, binding ∈ program.declarations.input.manifest.bindings ∧ binding.declaration = id ∧
      ResolvedOperands before.world context.environment operands addresses ∧
      (binding.signature.unsafeAllowed = true → context.unsafeAllowed = true) ∧
      event = none ∧ after = { before with task := .primitive context destination binding arguments addresses next } := by
  cases step <;> simp_all
  exact ⟨_,by assumption,by assumption,_,by assumption,by assumption,rfl,rfl⟩

theorem AtomStep.primitive_deterministic {program : Kernel.Program} {before left right : State}
    {firstEvent secondEvent : Option Event} {context : Context} {destination : Address}
    {id : DeclId} {arguments : List Term} {operands : List Kernel.Place} {next : Kernel.Code}
    (valid : ProgramWellFormed program.declarations)
    (task : before.task = .atom context destination (.primitive id arguments operands) next)
    (first : AtomStep program before firstEvent left) (second : AtomStep program before secondEvent right) :
    firstEvent = secondEvent ∧ left = right := by
  obtain ⟨firstBinding,firstOperands,firstMember,firstId,firstResolved,firstUnsafe,rfl,rfl⟩ := first.primitive_cases task
  obtain ⟨secondBinding,secondOperands,secondMember,secondId,secondResolved,secondUnsafe,rfl,rfl⟩ := second.primitive_cases task
  have bindingEqual := valid.manifest.binding_unique firstMember secondMember (firstId.trans secondId.symm)
  have operandsEqual := firstResolved.deterministic secondResolved
  subst secondBinding
  subst secondOperands
  exact ⟨rfl,rfl⟩

/-- Instantiated static admission supplies the actual dispatch binding and
unsafe gate. Operand resolution retains the existing shared-read capability
contract; successful scalar calculation is not assumed here. -/
theorem AtomStep.primitive_progress {program : Kernel.Program} {before : State}
    {context : Context} {typingContext : Typing.Context} {destination : Address} {id : DeclId}
    {arguments : List Term} {operands : List Kernel.Place} {addresses : List ResolvedPlace}
    {next : Kernel.Code} {result : Term}
    (task : before.task = .atom context destination (.primitive id arguments operands) next)
    (typed : Typing.AtomType program typingContext (.primitive id arguments operands) result)
    (resolved : ResolvedOperands before.world context.environment operands addresses)
    (access : typingContext.static.unsafeAllowed = context.unsafeAllowed) :
    ∃ after, AtomStep program before none after := by
  cases typed with
  | @primitive _ _ _ binding substitution signature member identity instantiated argumentKinds signatureEqual
      scalarSignature places allowed effects =>
      have unsafeEqual : signature.unsafeAllowed = binding.signature.unsafeAllowed := by
        rw [signatureEqual]
        rfl
      exact ⟨_,.primitive task member identity resolved (fun requested =>
        access ▸ allowed (unsafeEqual ▸ requested))⟩

/-- The actual atom transition retains exactly the signature selected by its
static admission. Manifest uniqueness prevents changing the primitive or its
parameter types between admission and runtime operand observation. -/
theorem AtomStep.primitive_typed {program : Kernel.Program} {before after : State} {event : Option Event}
    {context : Context} {typingContext : Typing.Context} {destination : Address} {id : DeclId}
    {arguments : List Term} {operands : List Kernel.Place} {next : Kernel.Code} {result : Term}
    (valid : ProgramWellFormed program.declarations)
    (task : before.task = .atom context destination (.primitive id arguments operands) next)
    (typed : Typing.AtomType program typingContext (.primitive id arguments operands) result)
    (step : AtomStep program before event after) :
    ∃ binding addresses substitution signature,
      after = { before with task := .primitive context destination binding arguments addresses next } ∧
      event = none ∧ Instantiates binding.signature.generics arguments substitution ∧
      signature = binding.signature.instantiate substitution ∧ signature.result = result ∧
      binding.ScalarSignature program.declarations.input.target arguments signature ∧
      ResolvedOperands before.world context.environment operands addresses ∧
      Typing.PlacesType program.declarations typingContext operands signature.parameters := by
  obtain ⟨binding,addresses,member,identity,resolved,allowed,rfl,rfl⟩ := step.primitive_cases task
  cases typed with
  | primitive typedMember typedId instantiated argumentKinds signatureEqual scalarSignature places unsafeAllowed effects =>
      have same := valid.manifest.binding_unique member typedMember (identity.trans typedId.symm)
      subst_vars
      exact ⟨_,_,_,_,rfl,rfl,instantiated,rfl,rfl,scalarSignature,resolved,places⟩

end Execution

/-- The current literal machine outcome supplies progress inside the actual
invocation boundary; static library-view realization is a separate obligation. -/
theorem Contracts.StateProgress.literal {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {before : Execution.State} {boundary : Contracts.InvocationBoundary}
    {context : Execution.Context} {destination : Address} {binding : RuntimeBinding}
    {bytes : List Nat} {next : Kernel.Code} {source : Source.Literal} {primitive : Primitive}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (inside : boundary.Inside program before)
    (task : before.task = .primitive context destination binding
      [.constantTuple (bytes.map (fun byte => .constant (.integer false (.fixed 8) (Int.ofNat byte))))] [] next)
    (admitted : binding ∈ program.declarations.input.manifest.bindings)
    (identity : binding.primitive = some primitive)
    (data : LiteralData source primitive bytes)
    (result : binding.signature.result = Execution.OctetType bytes)
    (destinationType : Execution.DestinationType before.world destination binding.signature.result) :
    Contracts.StateProgress program host function before boundary := by
  obtain ⟨after,_,step,_⟩ := Execution.PrimitiveStep.literal_typed_progress valid inventory typed
    task admitted identity data result destinationType
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨none,after,inside,
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl step))))⟩)))

/-- A nominal literal result is blocked in the whole machine, not merely in
the primitive family. Foreign dispatch cannot rescue a primitive binding. -/
theorem Execution.Step.literal_nominal_impossible {program : Kernel.Program} {host : Foreign.Model}
    {before after : Execution.State} {event : Option Event} {context : Execution.Context}
    {destination : Address} {binding : RuntimeBinding} {bytes : List Nat}
    {next : Kernel.Code} {id : DeclId} {arguments : List Term}
    (task : before.task = .primitive context destination binding
      [.constantTuple (bytes.map (fun byte => .constant (.integer false (.fixed 8) (Int.ofNat byte))))] [] next)
    (literal : binding.primitive = some .literalText ∨ binding.primitive = some .literalBytes)
    (result : binding.signature.result = .nominal id arguments)
    (step : Execution.Step program host before event after) : False := by
  rcases step with step | step | step | step | step | step
  · cases step <;> simp_all only [reduceCtorEq]
  · cases step <;> simp_all only [reduceCtorEq]
  · cases step <;> simp_all only [reduceCtorEq]
  · cases step <;> simp_all only [reduceCtorEq]
    have impossible := (Execution.Task.primitive.inj task).2.2.2.2.1
    cases impossible
  · exact Execution.PrimitiveStep.literal_nominal_impossible task literal result step
  · cases step <;> simp_all only [reduceCtorEq]
    rename_i running selected protectedInputs callTyped precondition started
    have identity := (Execution.Task.primitive.inj task).2.2.1
    have notPrimitive := selected.2.1
    simp only at notPrimitive
    rw [identity] at notPrimitive
    rcases literal with literal | literal <;> simp_all

/-- The tuple-only literal implementation cannot satisfy the real invocation
progress obligation for a nominal view. No alternative outcome hides the gap. -/
theorem Contracts.StateProgress.literal_nominal_impossible {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {before : Execution.State} {boundary : Contracts.InvocationBoundary}
    {context : Execution.Context} {destination : Address} {binding : RuntimeBinding}
    {bytes : List Nat} {next : Kernel.Code} {id : DeclId} {arguments : List Term}
    (task : before.task = .primitive context destination binding
      [.constantTuple (bytes.map (fun byte => .constant (.integer false (.fixed 8) (Int.ofNat byte))))] [] next)
    (literal : binding.primitive = some .literalText ∨ binding.primitive = some .literalBytes)
    (result : binding.signature.result = .nominal id arguments)
    (progress : Contracts.StateProgress program host function before boundary) : False := by
  rcases progress with normal | ⟨reason,fatal⟩ | awaiting | transfer | ⟨event,after,step⟩
  · obtain ⟨address,normal⟩ := normal
    cases boundary with
    | isolated => obtain ⟨context,normal⟩ := normal; simp only [task,reduceCtorEq] at normal
    | caller caller ambient => simp only [Contracts.InvocationBoundary.Normal,task,reduceCtorEq,false_and] at normal
  · simp only [task,reduceCtorEq] at fatal
  · obtain ⟨_,_,_,_,_,_,pending,_⟩ := awaiting
    simp only [task,reduceCtorEq] at pending
  · obtain ⟨_,_,⟨⟨_,pending⟩,_⟩,_⟩ := transfer
    simp only [task,reduceCtorEq] at pending
  · exact Execution.Step.literal_nominal_impossible task literal result step.2

/-- Resource admission excludes reaching the unsupported nominal literal
task. This is an obstruction to deriving admission, not an admission rule. -/
theorem Contracts.ResourceAdmissionAt.no_nominal_literal {program : Kernel.Program}
    {function : Kernel.Function} {access : Access}
    (admitted : Contracts.ResourceAdmissionAt program function access)
    {host : Foreign.Model} {inputs : List Kernel.InvocationInput} {boundary : Contracts.InvocationBoundary}
    {start before : Execution.State} {trace : List Execution.Event}
    (lawful : Foreign.Model.Lawful program host)
    (initial : Contracts.InvocationStart program host function inputs boundary start)
    (captures : ∀ input ∈ inputs, (∃ index, input.origin = .capture index) → input.access = access)
    (run : Contracts.InvocationRun program host boundary start trace before)
    {context : Execution.Context} {destination : Address} {binding : RuntimeBinding}
    {bytes : List Nat} {next : Kernel.Code} {id : DeclId} {arguments : List Term}
    (task : before.task = .primitive context destination binding
      [.constantTuple (bytes.map (fun byte => .constant (.integer false (.fixed 8) (Int.ofNat byte))))] [] next)
    (literal : binding.primitive = some .literalText ∨ binding.primitive = some .literalBytes)
    (result : binding.signature.result = .nominal id arguments) : False := by
  exact Contracts.StateProgress.literal_nominal_impossible task literal result
    (admitted host inputs boundary start trace before lawful initial captures run).1

end Glorious.Language
