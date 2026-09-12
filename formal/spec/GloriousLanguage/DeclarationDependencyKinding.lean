import GloriousLanguage.ProjectionKinding
import GloriousLanguage.CapabilityModels

/-! The capability dependencies of admitted declarations are kinded in the
same generic scopes as their signatures. Specialization uses the actual
ordered instantiation and substitution graphs already carried by the local
capability equation. -/
namespace Glorious.Language

theorem ProgramWellFormed.data_field_types {program : Program} (valid : ProgramWellFormed program)
    {id : DeclId} {data : DataDefinition} (found : program.data id = some data) :
    ∀ type ∈ (data.variants.flatMap (·.fields)).map (·.type),
      Kinding program ⟨data.generics,data.requirements,0,data.header.module,false,{}⟩ type .type := by
  have shape := (valid.2.2.2.2.1 _ (List.mem_of_find?_eq_some (Program.data_lookup found))).2.1
  intro type member
  obtain ⟨field,inFields,rfl⟩ := List.mem_map.mp member
  obtain ⟨variant,inVariants,inVariant⟩ := List.mem_flatMap.mp inFields
  exact ((shape.2.2.2.1 variant inVariants).2 field inVariant).1.1

theorem ProgramWellFormed.quantity_source {program : Program} (valid : ProgramWellFormed program)
    {id : DeclId} {data : DataDefinition} {source : Term}
    (found : program.data id = some data) (selected : data.quantitySource = some source) :
    Kinding program ⟨data.generics,data.requirements,0,data.header.module,false,{}⟩ source source.kind ∧
      (source.kind = .quantity ∨ source.kind = .type) := by
  have shape := (valid.2.2.2.2.1 _ (List.mem_of_find?_eq_some (Program.data_lookup found))).2.1
  obtain ⟨kinded,kind⟩ := shape.2.2.2.2.2.2.1 source selected
  exact ⟨kinded.1,kind⟩

theorem ProgramWellFormed.function_capture_types {program : Program} (valid : ProgramWellFormed program)
    {id : DeclId} {function : FunctionDefinition} (found : program.function id = some function) :
    ∀ type ∈ function.captures,
      Kinding program ⟨function.signature.generics,function.signature.constraints,0,function.header.module,false,{}⟩
        type .type := by
  have shape := (valid.2.2.2.2.1 _ (List.mem_of_find?_eq_some (Program.function_lookup found))).2.1
  intro type member
  exact (shape.2.2.2.2.2.2 type member).1

theorem ListRel.instantiate_kinding {program : Program} {source target : Context} {before after arguments : List Term}
    {substitution : Substitution} {kind : Kind}
    (related : ListRel (Substitutes substitution) before after)
    (templates : ∀ term ∈ before, Kinding program source term kind)
    (instantiated : Instantiates source.binders arguments substitution)
    (argumentsKinded : ∀ argument ∈ arguments, Kinding program target argument argument.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands) :
    ∀ term ∈ after, Kinding program target term kind := by
  induction related with
  | nil => simp
  | cons head _ ih =>
    intro term member
    rcases List.mem_cons.mp member with rfl | present
    · rw [head.2.1]
      exact ((templates _ List.mem_cons_self).instantiate instantiated argumentsKinded levels regions brands).1
    · exact ih (fun term present => templates term (List.mem_cons_of_mem _ present)) term present

theorem ProgramWellFormed.data_fields_specialization {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {id : DeclId} {data : DataDefinition} {arguments fields : List Term} {substitution : Substitution}
    (found : program.data id = some data) (instantiated : Instantiates data.generics arguments substitution)
    (argumentsKinded : ∀ argument ∈ arguments, Kinding program context argument argument.kind)
    (substituted : ListRel (Substitutes substitution) ((data.variants.flatMap (·.fields)).map (·.type)) fields) :
    ∀ field ∈ fields, Kinding program context field .type :=
  substituted.instantiate_kinding (valid.data_field_types found) instantiated argumentsKinded (Nat.zero_le _)
    (fun _ present => False.elim (List.not_mem_nil present))
    (fun _ present => False.elim (List.not_mem_nil present))

theorem ProgramWellFormed.quantity_source_specialization {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {id : DeclId} {data : DataDefinition} {arguments : List Term} {substitution : Substitution}
    {source value : Term} (found : program.data id = some data) (selected : data.quantitySource = some source)
    (instantiated : Instantiates data.generics arguments substitution)
    (argumentsKinded : ∀ argument ∈ arguments, Kinding program context argument argument.kind)
    (substituted : Substitutes substitution source value) :
    Kinding program context value value.kind ∧ (value.kind = .quantity ∨ value.kind = .type) := by
  obtain ⟨kinded,kind⟩ := valid.quantity_source found selected
  have actual := (kinded.instantiate instantiated argumentsKinded (Nat.zero_le _)
    (fun _ present => False.elim (List.not_mem_nil present))
    (fun _ present => False.elim (List.not_mem_nil present))).1
  rw [← substituted.2.1,substituted.1] at actual
  exact ⟨actual,substituted.1 ▸ kind⟩

/-- Callable capability and layout consume this same admitted capture
instance. An operation/function identity collision is impossible at the
actual declaration lookup, rather than treated as an empty capture list. -/
theorem CallableFields.kinding {program : Program} (valid : ProgramWellFormed program) {context : Context}
    {id : DeclId} {arguments fields : List Term}
    (kinded : Kinding program context (.callable id arguments) .type)
    (captured : CallableFields program id arguments fields) :
    ∀ field ∈ fields, Kinding program context field .type := by
  cases kinded with
  | callable found _ argumentsKinded =>
    cases captured with
    | function actual instantiated substituted =>
      obtain rfl := Option.some.inj (found.symm.trans actual)
      exact substituted.instantiate_kinding (valid.function_capture_types actual) instantiated argumentsKinded (Nat.zero_le _)
        (fun _ present => False.elim (List.not_mem_nil present))
        (fun _ present => False.elim (List.not_mem_nil present))
    | operation actual _ =>
      have impossible := (Program.function_lookup found).symm.trans (Program.operation_lookup actual)
      cases impossible

noncomputable def kindedCapabilityAssignment (program : Program) (context : Context)
    (assignment : Term → Option Principal) : Term → Option Principal := by
  classical
  exact fun term => if Kinding program context term .type then assignment term else none

/-- An actual local equation for a kinded type consults only kinded type
dependencies. Erasing every other assignment entry preserves that same
equation and its exact claimed class; no new dependency walker is introduced. -/
theorem CapabilityEquation.kinding_restrict {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {assignment : Term → Option Principal} {type : Term} {principal : Principal}
    (equation : CapabilityEquation program assignment type principal)
    (kinded : Kinding program context type .type) :
    CapabilityEquation program (kindedCapabilityAssignment program context assignment) type principal := by
  classical
  unfold kindedCapabilityAssignment
  have keep {term : Term} {claimed : Principal} (kinded : Kinding program context term .type)
      (found : assignment term = some claimed) :
      (if Kinding program context term .type then assignment term else none) = some claimed := by
    simpa only [if_pos kinded] using found
  have fields {terms : List Term} {principals : List Principal}
      (kinded : ∀ term ∈ terms, Kinding program context term .type)
      (assigned : ListRel (fun term claimed => assignment term = some claimed) terms principals) :
      ListRel (fun term claimed =>
        (if Kinding program context term .type then assignment term else none) = some claimed) terms principals := by
    induction assigned with
    | nil => exact .nil
    | cons found _ ih =>
      exact .cons (keep (kinded _ List.mem_cons_self) found)
        (ih (fun term present => kinded term (List.mem_cons_of_mem _ present)))
  cases equation with
  | unit => exact .unit
  | bottom => exact .bottom
  | scalar => exact .scalar
  | raw => exact .raw
  | shared => exact .shared
  | unique => exact .unique
  | label => exact .label
  | tuple assigned =>
    cases kinded with
    | tuple kinded => exact .tuple (fields kinded assigned)
  | emptyArray => exact .emptyArray
  | array positive assigned =>
    cases kinded with
    | array element _ => exact .array positive (keep element assigned)
  | alias found instantiated substituted assigned =>
    cases kinded with
    | alias actual _ arguments =>
      obtain rfl := Option.some.inj (found.symm.trans actual)
      have dependency := (valid.alias_specialization actual instantiated arguments).1
      rw [← substituted.2.1] at dependency
      exact .alias actual instantiated substituted (keep dependency assigned)
  | nominal found instantiated substituted assigned marked meets restricted drops =>
    cases kinded with
    | nominal actual _ arguments =>
      obtain rfl := Option.some.inj (found.symm.trans actual)
      refine .nominal actual instantiated substituted
        (fields (valid.data_fields_specialization actual instantiated arguments substituted) assigned)
        ?_ meets restricted drops
      rcases marked with none | ⟨source,value,selected,substituted,marked⟩
      · exact Or.inl none
      · refine Or.inr ⟨source,value,selected,substituted,?_⟩
        rcases marked with literal | ⟨typeKind,assigned⟩
        · exact Or.inl literal
        · have dependency := (valid.quantity_source_specialization actual selected instantiated arguments substituted).1
          rw [typeKind] at dependency
          exact Or.inr ⟨typeKind,keep dependency assigned⟩
  | callable captured assigned => exact .callable captured (fields (captured.kinding valid kinded) assigned)
  | environment assigned =>
    cases kinded with
    | environment _ _ residents => exact .environment (fields residents assigned)
  | available assigned =>
    cases kinded with
    | available brand region residents => exact .available (keep (.environment brand region residents) assigned)
  | bindings assigned =>
    cases kinded with
    | bindings _ _ residents => exact .bindings (fields residents assigned)
  | optionalContinuation => exact .optionalContinuation
  | exactContinuation positive => exact .exactContinuation positive

/-- The real structural equation is monotone on its admitted kinded domain.
The target need not retain arbitrary ill-kinded proposal entries which are
irrelevant to that equation and may cease to make sense after substitution. -/
theorem CapabilityEquation.monotone_kinded {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {first last : Term → Option Principal} {type : Term} {principal : Principal}
    (equation : CapabilityEquation program first type principal) (kinded : Kinding program context type .type)
    (related : ∀ term claimed, Kinding program context term .type → first term = some claimed →
      ∃ supported, last term = some supported ∧ claimed.Restricts supported) :
    ∃ supported, CapabilityEquation program last type supported ∧ principal.Restricts supported := by
  classical
  apply (equation.kinding_restrict valid kinded).monotone
  intro term claimed found
  by_cases admitted : Kinding program context term .type
  · exact related term claimed admitted (by simpa only [kindedCapabilityAssignment,if_pos admitted] using found)
  · simp only [kindedCapabilityAssignment,if_neg admitted] at found
    cases found

end Glorious.Language
