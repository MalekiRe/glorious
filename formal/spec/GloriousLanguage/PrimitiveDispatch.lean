import GloriousLanguage.ProjectionStorage

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
end Glorious.Language
