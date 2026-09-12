import GloriousLanguage.PredicateSubstitutionKinding
import GloriousLanguage.DefinitionalAdmission

/-! Actual published declarations supply kinded predicates to generic
instantiation, implementation selection and associated-member domains. These
are consequences of declaration admission, not independent predicate tables. -/
namespace Glorious.Language

theorem ProgramWellFormed.constraintsKinded {program : Program} (valid : ProgramWellFormed program)
    {declaration : Definition} (member : declaration ∈ program.declarations) :
    DeclarationConstraintsKinded program declaration := (valid.2.2.2.2.1 declaration member).2.2

theorem ProgramWellFormed.data_requirements {program : Program} (valid : ProgramWellFormed program)
    {id : DeclId} {data : DataDefinition} (found : program.data id = some data) :
    ∀ requirement ∈ data.requirements,
      ConstraintKinded program ⟨data.generics,data.requirements,0,data.header.module,false,{}⟩ requirement :=
  valid.constraintsKinded (List.mem_of_find?_eq_some (Program.data_lookup found))

theorem ProgramWellFormed.trait_requirements {program : Program} (valid : ProgramWellFormed program)
    {id : DeclId} {trait : TraitDefinition} (found : program.trait id = some trait) :
    ∀ requirement ∈ trait.requirements,
      ConstraintKinded program ⟨trait.generics,trait.requirements,0,trait.header.module,false,{}⟩ requirement :=
  valid.constraintsKinded (List.mem_of_find?_eq_some (Program.trait_lookup found))

theorem ProgramWellFormed.associated_requirements {program : Program} (valid : ProgramWellFormed program)
    {id traitId : DeclId} {associated : AssociatedDefinition} {trait : TraitDefinition}
    (found : program.associated id = some associated) (traitFound : program.trait traitId = some trait)
    (owner : associated.owner = traitId) :
    ((trait.generics ++ associated.generics).map (·.id)).Nodup ∧
      ∀ requirement ∈ associated.requirements,
        ConstraintKinded program ⟨trait.generics ++ associated.generics,trait.requirements ++ associated.requirements,
          0,associated.header.module,false,{}⟩ requirement := by
  have member := List.mem_of_find?_eq_some (Program.associated_lookup found)
  obtain ⟨actual,actualFound,kinded⟩ := valid.constraintsKinded member
  rw [owner,traitFound] at actualFound
  cases Option.some.inj actualFound
  have shape := (valid.2.2.2.2.1 _ member).2.1
  obtain ⟨actual,actualFound,_,distinct,_⟩ := shape
  rw [owner,traitFound] at actualFound
  cases Option.some.inj actualFound
  exact ⟨distinct,kinded⟩

theorem ProgramWellFormed.implementation_requirements {program : Program} (valid : ProgramWellFormed program)
    {implementation : ImplDefinition} (member : Definition.implementation implementation ∈ program.declarations) :
    ∀ requirement ∈ implementation.requirements,
      ConstraintKinded program ⟨implementation.generics,implementation.requirements,0,implementation.header.module,false,{}⟩ requirement :=
  valid.constraintsKinded member

theorem ProgramWellFormed.effect_requirements {program : Program} (valid : ProgramWellFormed program)
    {id : DeclId} {effect : EffectDefinition} (found : program.effect id = some effect) :
    ∀ requirement ∈ effect.requirements,
      ConstraintKinded program ⟨effect.generics,effect.requirements,0,effect.header.module,false,{}⟩ requirement :=
  valid.constraintsKinded (List.mem_of_find?_eq_some (Program.effect_lookup found))

theorem ProgramWellFormed.function_predicates {program : Program} (valid : ProgramWellFormed program)
    {id : DeclId} {function : FunctionDefinition} (found : program.function id = some function) :
    let context : Context := ⟨function.signature.generics,function.signature.constraints,0,function.header.module,false,{}⟩
    (∀ requirement ∈ function.signature.constraints, ConstraintKinded program context requirement) ∧
    ∀ relation ∈ function.invocations,
      ConstraintKinded program context (.callable relation.receiver relation.arguments relation.result relation.effects relation.unsafeAllowed) ∧
      ConstraintKinded program context (.runsIn relation.receiver relation.access relation.arguments relation.after relation.unsafeAllowed) :=
  valid.constraintsKinded (List.mem_of_find?_eq_some (Program.function_lookup found))

theorem ProgramWellFormed.operation_requirements {program : Program} (valid : ProgramWellFormed program)
    {id : DeclId} {operation : OperationDefinition} (found : program.operation id = some operation) :
    ∀ requirement ∈ operation.signature.constraints,
      ConstraintKinded program ⟨operation.signature.generics,operation.signature.constraints,0,operation.header.module,false,{}⟩ requirement :=
  valid.constraintsKinded (List.mem_of_find?_eq_some (Program.operation_lookup found))

theorem EntailsSubstitution.actual_result {program : Program} {context : Context} {substitution : Substitution}
    {requirement : Constraint} (held : EntailsSubstitution program context substitution requirement) :
    Entails program context (requirement.substitute substitution) := by
  cases held with
  | instantiated graph evidence => simpa only [graph.2] using evidence

/-- Implementation selection supplies its actual inferred generic arguments.
The admitted source requirements instantiate at those arguments, including
their nested quantified predicates, and retain the selection's evidence. -/
theorem SelectsImpl.requirements_kinded {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {trait : DeclId} {arguments : List Term} {negative : Bool}
    {implementation : ImplDefinition} {substitution : Substitution}
    (selected : SelectsImpl program context trait arguments negative implementation substitution) :
    ∀ requirement ∈ implementation.requirements,
      SubstituteConstraint substitution requirement (requirement.substitute substitution) ∧
      ConstraintKinded program context (requirement.substitute substitution) ∧
      Entails program context (requirement.substitute substitution) := by
  cases selected with
  | selected declared _ _ matched holds =>
    cases matched with
    | inferred instantiated kinded _ _ _ _ =>
      intro requirement member
      have admitted := (valid.implementation_requirements declared requirement member).instantiate instantiated kinded
        (Nat.zero_le _) (fun _ absent => False.elim (List.not_mem_nil absent))
        (fun _ absent => False.elim (List.not_mem_nil absent))
      exact ⟨admitted.1,admitted.2,(holds requirement member).actual_result⟩

/-- Both halves of the actual projection domain use source-kind admission
and one simultaneous owner/item substitution. No target predicate-kind or
capture-admissibility certificate is added to domain formation. -/
theorem ProjectionDomain.requirements_kinded {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {trait member : DeclId} {owners items : List Term}
    {associated : AssociatedDefinition} {ownerSub itemSub : Substitution}
    (domain : ProjectionDomain program context trait member owners items associated ownerSub itemSub) :
    (∀ requirement ∈ associated.requirements,
      SubstituteConstraint (ownerSub ++ itemSub) requirement (requirement.substitute (ownerSub ++ itemSub)) ∧
      ConstraintKinded program context (requirement.substitute (ownerSub ++ itemSub)) ∧
      Entails program context (requirement.substitute (ownerSub ++ itemSub))) ∧
    ∃ declaration, program.trait trait = some declaration ∧
      ∀ requirement ∈ declaration.requirements,
        SubstituteConstraint ownerSub requirement (requirement.substitute ownerSub) ∧
        ConstraintKinded program context (requirement.substitute ownerSub) ∧
        Entails program context (requirement.substitute ownerSub) := by
  cases domain with
  | valid found _ associatedFound owner ownersInstance itemsInstance kinded ownerHolds itemHolds =>
    obtain ⟨distinct,itemKinded⟩ := valid.associated_requirements associatedFound found owner
    constructor
    · intro requirement member
      have admitted := (itemKinded requirement member).instantiate
        (ownersInstance.append itemsInstance distinct) kinded
        (Nat.zero_le _) (fun _ absent => False.elim (List.not_mem_nil absent))
        (fun _ absent => False.elim (List.not_mem_nil absent))
      exact ⟨admitted.1,admitted.2,(itemHolds requirement member).actual_result⟩
    · refine ⟨_,found,?_⟩
      intro requirement member
      have admitted := (valid.trait_requirements found requirement member).instantiate ownersInstance
        (fun argument present => kinded argument (List.mem_append_left _ present))
        (Nat.zero_le _) (fun _ absent => False.elim (List.not_mem_nil absent))
        (fun _ absent => False.elim (List.not_mem_nil absent))
      exact ⟨admitted.1,admitted.2,(ownerHolds requirement member).actual_result⟩

theorem ConstraintsHold.actual_result {program : Program} {context : Context} {substitution : Substitution}
    {requirements : List Constraint} (held : ConstraintsHold program context substitution requirements)
    {requirement : Constraint} (member : requirement ∈ requirements) :
    Entails program context (requirement.substitute substitution) := by
  obtain ⟨result,graph,evidence⟩ := held requirement member
  simpa only [graph.2] using evidence

theorem WellKinded.data_requirements {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {id : DeclId} {data : DataDefinition} {arguments : List Term} {substitution : Substitution}
    (kinded : WellKinded program context (.nominal id arguments) .type)
    (found : program.data id = some data) (instantiated : Instantiates data.generics arguments substitution) :
    ∀ requirement ∈ data.requirements,
      SubstituteConstraint substitution requirement (requirement.substitute substitution) ∧
      ConstraintKinded program context (requirement.substitute substitution) ∧
      Entails program context (requirement.substitute substitution) := by
  have held := kinded.2.1 id arguments data substitution .here found instantiated
  cases kinded.1 with
  | nominal _ _ argumentsKinded =>
    intro requirement member
    have admitted := (valid.data_requirements found requirement member).instantiate instantiated argumentsKinded
      (Nat.zero_le _) (fun _ absent => False.elim (List.not_mem_nil absent))
      (fun _ absent => False.elim (List.not_mem_nil absent))
    exact ⟨admitted.1,admitted.2,held.actual_result member⟩

theorem WellKinded.effect_requirements {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {id : DeclId} {effect : EffectDefinition} {arguments : List Term} {substitution : Substitution}
    (kinded : WellKinded program context (.effect id arguments) .effect)
    (found : program.effect id = some effect) (instantiated : Instantiates effect.generics arguments substitution) :
    ∀ requirement ∈ effect.requirements,
      SubstituteConstraint substitution requirement (requirement.substitute substitution) ∧
      ConstraintKinded program context (requirement.substitute substitution) ∧
      Entails program context (requirement.substitute substitution) := by
  have held := kinded.2.2.1 id arguments effect substitution .here found instantiated
  cases kinded.1 with
  | effect _ _ argumentsKinded =>
    intro requirement member
    have admitted := (valid.effect_requirements found requirement member).instantiate instantiated argumentsKinded
      (Nat.zero_le _) (fun _ absent => False.elim (List.not_mem_nil absent))
      (fun _ absent => False.elim (List.not_mem_nil absent))
    exact ⟨admitted.1,admitted.2,held.actual_result member⟩

theorem ProgramWellFormed.function_predicates_instance {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {id : DeclId} {function : FunctionDefinition} {arguments : List Term} {substitution : Substitution}
    (found : program.function id = some function)
    (instantiated : Instantiates function.signature.generics arguments substitution)
    (kinded : ∀ argument ∈ arguments, Kinding program context argument argument.kind) :
    (∀ requirement ∈ function.signature.constraints,
      SubstituteConstraint substitution requirement (requirement.substitute substitution) ∧
      ConstraintKinded program context (requirement.substitute substitution)) ∧
    ∀ relation ∈ function.invocations,
      ConstraintKinded program context
        ((Constraint.callable relation.receiver relation.arguments relation.result relation.effects relation.unsafeAllowed).substitute substitution) ∧
      ConstraintKinded program context
        ((Constraint.runsIn relation.receiver relation.access relation.arguments relation.after relation.unsafeAllowed).substitute substitution) := by
  obtain ⟨requirements,invocations⟩ := valid.function_predicates found
  constructor
  · intro requirement member
    exact (requirements requirement member).instantiate instantiated kinded
      (Nat.zero_le _) (fun _ absent => False.elim (List.not_mem_nil absent))
      (fun _ absent => False.elim (List.not_mem_nil absent))
  · intro relation member
    have admitted := invocations relation member
    exact ⟨(admitted.1.instantiate instantiated kinded
      (Nat.zero_le _) (fun _ absent => False.elim (List.not_mem_nil absent))
      (fun _ absent => False.elim (List.not_mem_nil absent))).2,
      (admitted.2.instantiate instantiated kinded
      (Nat.zero_le _) (fun _ absent => False.elim (List.not_mem_nil absent))
      (fun _ absent => False.elim (List.not_mem_nil absent))).2⟩

theorem ProgramWellFormed.operation_requirements_instance {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {id : DeclId} {operation : OperationDefinition} {arguments : List Term} {substitution : Substitution}
    (found : program.operation id = some operation)
    (instantiated : Instantiates operation.signature.generics arguments substitution)
    (kinded : ∀ argument ∈ arguments, Kinding program context argument argument.kind) :
    ∀ requirement ∈ operation.signature.constraints,
      SubstituteConstraint substitution requirement (requirement.substitute substitution) ∧
      ConstraintKinded program context (requirement.substitute substitution) := by
  intro requirement member
  exact (valid.operation_requirements found requirement member).instantiate instantiated kinded
    (Nat.zero_le _) (fun _ absent => False.elim (List.not_mem_nil absent))
    (fun _ absent => False.elim (List.not_mem_nil absent))

end Glorious.Language
