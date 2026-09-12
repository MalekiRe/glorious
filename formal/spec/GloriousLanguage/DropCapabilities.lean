import GloriousLanguage.CapabilityModels
import GloriousLanguage.StorageTyping

/-! The intrinsic affine Drop bound is checked by ordinary entailment.
The semantic capability interpretation consumes that evidence, including
logical congruence and quantified elimination. Propagation through the actual
typed resident tree still requires conversion-safe structural inversion;
raw syntax-indexed inversion is not a substitute for that obligation. -/
namespace Glorious.Language

theorem Quantity.affine_request_iff {principal : Principal} :
    Quantity.Request ⟨0,some 1⟩ principal ↔ principal.MayDiscard := by
  constructor
  · intro request
    exact request.2 0 ⟨Nat.zero_le _,by simp⟩
  · intro discard
    refine ⟨⟨1,by simp [Quantity.Contains]⟩,?_⟩
    intro n contained
    have bound : n ≤ 1 := contained.2 1 rfl
    by_cases zero : n = 0
    · subst n; exact discard
    · have one : n = 1 := by omega
      simpa only [one] using Principal.once_does_not_identify_principal principal

theorem Entails.drop_capability {program : Program} {context : Context} {type : Term}
    (closed : context.assumptions = []) (entailed : Entails program context (.use type ⟨0,some 1⟩)) :
    ∃ principal, (CapabilityModel.canonical program).principal type = some principal ∧ principal.MayDiscard := by
  obtain ⟨principal,selected,allowed⟩ := entailed.valid_use_principal closed ⟨1,by simp [Quantity.Contains]⟩
  exact ⟨principal,principalOf_canonical.mp selected,Quantity.affine_request_iff.mp allowed⟩

theorem Principal.meet_restricts_left (first last : Principal) : (first.meet last).Restricts first :=
  fun n permitted => ((Principal.meet_permits first last n).mp permitted).1

theorem Principal.fields_restricts_member {principals : List Principal} {principal : Principal}
    (member : principal ∈ principals) : (Principal.fields principals).Restricts principal := by
  induction principals with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact Principal.meet_restricts_left _ _
    · intro n permitted
      exact ih member n ((Principal.meet_permits first (Principal.fields rest) n).mp permitted).2

private theorem capability_fields_member {program : Program} {fields : List Term} {principals : List Principal}
    (selected : ListRel (fun field principal => greatestCapabilities program field = some principal) fields principals)
    {field : Term} (member : field ∈ fields) :
    ∃ principal, PrincipalOf program field principal ∧ (Principal.fields principals).Restricts principal := by
  obtain ⟨principal,present,found⟩ := selected.member_left member
  exact ⟨principal,principalOf_canonical.mpr found,Principal.fields_restricts_member present⟩

/-- The selected constructor's resident fields inherit permissions from the
same canonical nominal equation, including all variants and quantity sources. -/
theorem Execution.ConstructorHead.field_capability {program : Program} {type : Term}
    {variant : Option DeclId} {fields : List Term} {head : ValueHead} {principal : Principal}
    (constructed : Execution.ConstructorHead program type variant fields head)
    (capability : PrincipalOf program type principal) {field : Term} (member : field ∈ fields) :
    ∃ selected, PrincipalOf program field selected ∧ principal.Restricts selected := by
  rcases constructed with ⟨rfl,_,_⟩ | ⟨element,sign,width,length,rfl,_,_,size,homogeneous⟩ |
    ⟨id,arguments,data,constructor,substitution,rfl,_,_,selected,instantiated,substituted⟩
  · cases principalOf_equation.mp capability with
    | tuple fields => exact capability_fields_member fields member
  · rw [homogeneous field member]
    cases principalOf_equation.mp capability with
    | emptyArray =>
      have nonempty : 0 < fields.length := List.length_pos_of_mem member
      omega
    | array _ found => exact ⟨_,principalOf_canonical.mpr found,.refl _⟩
  · cases principalOf_equation.mp capability with
    | nominal found application fieldTypes fieldCapabilities marker meet restriction _ =>
      have same := Option.some.inj (found.symm.trans selected.1)
      subst same
      have sameSubstitution := application.functional instantiated
      subst sameSubstitution
      obtain ⟨child,capability,restricts⟩ := capability_fields_member fieldCapabilities (field := field) (by
        rw [ListRel.substitutes_eq_map fieldTypes]
        rw [ListRel.substitutes_eq_map substituted] at member
        obtain ⟨original,inOriginal,rfl⟩ := List.mem_map.mp member
        obtain ⟨declaration,inConstructor,rfl⟩ := List.mem_map.mp inOriginal
        exact List.mem_map.mpr ⟨declaration.type,List.mem_map.mpr
          ⟨declaration,List.mem_flatMap.mpr ⟨constructor,selected.2.1,inConstructor⟩,rfl⟩,rfl⟩)
      refine ⟨child,capability,?_⟩
      rcases restriction with ⟨_,rfl⟩ | ⟨_,restriction⟩
      · rw [meet]
        exact (Principal.meet_restricts_left _ _).trans restricts
      · apply restriction.trans
        rw [meet]
        exact (Principal.meet_restricts_left _ _).trans restricts

/-- A resident child is checked through the actual field-typing relation.
Callable captures and ordinary aggregate fields use the same capability fact. -/
theorem Typing.ValueTyped.child_capability {program : Kernel.Program} {world : World}
    {value child : Value} {index : Nat} {principal : Principal}
    (inventory : Kernel.BodyInventory program) (typed : Typing.ValueTyped program world value)
    (capability : PrincipalOf program.declarations value.type principal)
    (found : value.fields[index]? = some (some child)) :
    Typing.ValueTyped program world child ∧
      ∃ selected, PrincipalOf program.declarations child.type selected ∧ principal.Restricts selected := by
  cases typed <;> try { simp [Value.fields] at found }
  case aggregate shape fields =>
    have childTyped := fields.get found
    exact ⟨childTyped.1,shape.field_capability capability (List.mem_of_getElem? childTyped.2)⟩
  case callable body fields =>
    have childTyped := fields.get found
    cases principalOf_equation.mp capability with
    | callable declared fieldCapabilities =>
      have captures := body.capture_types inventory declared
      exact ⟨childTyped.1,capability_fields_member fieldCapabilities
        (by rw [← captures]; exact List.mem_of_getElem? childTyped.2)⟩
  case bindings fields _ _ _ _ =>
    have childTyped := fields.get found
    cases principalOf_equation.mp capability with
    | bindings fieldCapabilities =>
      exact ⟨childTyped.1,capability_fields_member fieldCapabilities (List.mem_of_getElem? childTyped.2)⟩

theorem Typing.ValueTyped.resident_capability {program : Kernel.Program} {world : World}
    {value resident : Value} {path : List Nat} {principal : Principal}
    (inventory : Kernel.BodyInventory program) (typed : Typing.ValueTyped program world value)
    (capability : PrincipalOf program.declarations value.type principal)
    (inside : ResidentAt value path resident) :
    ∃ selected, PrincipalOf program.declarations resident.type selected ∧ principal.Restricts selected := by
  induction inside generalizing principal with
  | root => exact ⟨principal,capability,.refl _⟩
  | field found _ ih =>
    obtain ⟨childTyped,selected,childCapability,restriction⟩ := typed.child_capability inventory capability found
    obtain ⟨final,finalCapability,last⟩ := ih childTyped childCapability
    exact ⟨final,finalCapability,restriction.trans last⟩

theorem Value.Initialized.resident {value resident : Value} {path : List Nat}
    (initialized : value.Initialized) (inside : ResidentAt value path resident) : resident.Initialized := by
  induction inside with
  | root => exact initialized
  | field found _ ih =>
    apply ih
    intro path value inside
    exact initialized _ value (.field found inside)

/-- An initialized typed resident with a zero-use capability can be destroyed
at every nested owned position. Disposal is derived, not an admission input. -/
theorem Typing.ValueTyped.mayDispose {program : Kernel.Program} {world : World}
    {value : Value} {principal : Principal} (inventory : Kernel.BodyInventory program)
    (typed : Typing.ValueTyped program world value) (initialized : value.Initialized)
    (capability : PrincipalOf program.declarations value.type principal) (discard : principal.MayDiscard) :
    MayDispose program.declarations value := by
  intro path resident inside
  obtain ⟨selected,capability,restriction⟩ := typed.resident_capability inventory capability inside
  exact ⟨fun _ => ⟨selected,capability,restriction 0 discard⟩,
    fun _ _ => initialized.resident inside⟩

/-- Checked intrinsic Use evidence publishes an actual canonical answer.
An unknown principal or a positive-lower restriction cannot admit a hook. -/
theorem DropApplication.capability {program : Program} {self region : Term} {hook : DeclId}
    {arguments : List Term} {declaration : FunctionDefinition} {substitution : Substitution}
    (application : DropApplication program self region hook arguments declaration substitution) :
    ∃ principal, PrincipalOf program self principal ∧ principal.MayDiscard := by
  cases application with
  | selected _ _ _ _ _ _ _ _ bound _ =>
    obtain ⟨principal,selected,discard⟩ := bound.drop_capability rfl
    exact ⟨principal,principalOf_canonical.mpr selected,discard⟩

theorem DropApplication.known_capability {program : Program} {self region : Term} {hook : DeclId}
    {arguments : List Term} {declaration : FunctionDefinition} {substitution : Substitution}
    (application : DropApplication program self region hook arguments declaration substitution) :
    (CapabilityModel.canonical program).principal self ≠ none := by
  obtain ⟨principal,selected,_⟩ := application.capability
  rw [principalOf_canonical.mp selected]
  simp

theorem DropApplication.not_exact_restriction {program : Program} {id : DeclId} {data : DataDefinition}
    {selfArguments : List Term} {region : Term} {hook : DeclId} {arguments : List Term}
    {declaration : FunctionDefinition} {substitution : Substitution}
    (application : DropApplication program (.nominal id selfArguments) region hook arguments declaration substitution)
    (found : program.data id = some data) : data.principalRestriction ≠ some .exact := by
  intro exactRestriction
  obtain ⟨principal,capability,discard⟩ := application.capability
  cases principalOf_equation.mp capability with
  | nominal selected _ _ _ _ _ restriction _ =>
    have same := Option.some.inj (selected.symm.trans found)
    subst same
    rcases restriction with ⟨none,_⟩ | ⟨chosen,_⟩
    · simp [exactRestriction] at none
    · have exactPrincipal : principal = .exact := Option.some.inj (chosen.symm.trans exactRestriction)
      exact Principal.exact_not_discardable (exactPrincipal ▸ discard)

/-- A checked Drop application cannot hide a positive-lower resident beneath
an outer wrapper or callable capture. The contradiction uses the same typed
resident path and canonical field capabilities as actual disposal. -/
theorem DropApplication.no_exact_resident {program : Kernel.Program} {region : Term} {hook : DeclId}
    {arguments : List Term} {declaration : FunctionDefinition} {substitution : Substitution}
    {world : World} {value resident : Value} {path : List Nat}
    (inventory : Kernel.BodyInventory program)
    (application : DropApplication program.declarations value.type region hook arguments declaration substitution)
    (typed : Typing.ValueTyped program world value) (inside : ResidentAt value path resident)
    (exactCapability : PrincipalOf program.declarations resident.type .exact) : False := by
  obtain ⟨principal,capability,discard⟩ := application.capability
  obtain ⟨selected,residentCapability,restriction⟩ := typed.resident_capability inventory capability inside
  have same : selected = .exact := Option.some.inj
    ((principalOf_canonical.mp residentCapability).symm.trans (principalOf_canonical.mp exactCapability))
  exact Principal.exact_not_discardable (same ▸ restriction 0 discard)

/-- The source type-domain bound is nonvacuous before any body or world is
chosen. Its answer does not depend on the particular hook borrowing region. -/
theorem DropApplications.capability {program : Program} (admitted : DropApplications program)
    {id : DeclId} {data : DataDefinition} {hook : DeclId} {arguments : List Term} {substitution : Substitution}
    (selected : program.data id = some data) (drops : data.dropHook = some hook)
    (instantiated : Instantiates data.generics arguments substitution)
    (kinded : ∀ argument ∈ arguments, Kinding program ⟨[],[],0,data.header.module,false,{}⟩ argument argument.kind)
    (requirements : ConstraintsHold program ⟨[],[],0,data.header.module,false,{}⟩ substitution data.requirements) :
    ∃ principal, (CapabilityModel.canonical program).principal (.nominal id arguments) = some principal ∧ principal.MayDiscard := by
  obtain ⟨_,_,_,application⟩ := admitted id data hook arguments substitution (.runtimeRegion 0)
    selected drops instantiated kinded requirements .runtimeRegion
  obtain ⟨principal,capability,discard⟩ := application.capability
  exact ⟨principal,principalOf_canonical.mp capability,discard⟩

/-- Positive-lower declaration restrictions are rejected on every inhabited
admitted application domain, even when no executable invocation is supplied. -/
theorem DropApplications.not_exact_restriction {program : Program} (admitted : DropApplications program)
    {id : DeclId} {data : DataDefinition} {hook : DeclId} {arguments : List Term} {substitution : Substitution}
    (selected : program.data id = some data) (drops : data.dropHook = some hook)
    (instantiated : Instantiates data.generics arguments substitution)
    (kinded : ∀ argument ∈ arguments, Kinding program ⟨[],[],0,data.header.module,false,{}⟩ argument argument.kind)
    (requirements : ConstraintsHold program ⟨[],[],0,data.header.module,false,{}⟩ substitution data.requirements) :
    data.principalRestriction ≠ some .exact := by
  obtain ⟨_,_,_,application⟩ := admitted id data hook arguments substitution (.runtimeRegion 0)
    selected drops instantiated kinded requirements .runtimeRegion
  exact application.not_exact_restriction selected

end Glorious.Language
