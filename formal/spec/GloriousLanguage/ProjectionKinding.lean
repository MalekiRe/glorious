import GloriousLanguage.SubstitutionKinding
import GloriousLanguage.DefinitionalAdmission

/-! Actual alias and associated-member admission supplies kind preservation
for capture-safe specialization. Inferred arguments may remain opaque. -/
namespace Glorious.Language

theorem ProgramWellFormed.alias_body {program : Program} (valid : ProgramWellFormed program)
    {id : DeclId} {alias : AliasDefinition} (found : program.alias id = some alias) :
    Kinding program ⟨alias.generics,[],0,alias.header.module,false,{}⟩ alias.value .type := by
  have lookup : program.lookup id = some (.alias alias) := by
    unfold Program.alias at found
    cases selected : program.lookup id <;> simp only [selected] at found
    case none => cases found
    case some value => cases value <;> simp_all
  exact (valid.2.2.2.2.1 _ (List.mem_of_find?_eq_some lookup)).2.2.1

theorem ProgramWellFormed.alias_specialization {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {id : DeclId} {alias : AliasDefinition} {arguments : List Term} {substitution : Substitution}
    (found : program.alias id = some alias) (instantiated : Instantiates alias.generics arguments substitution)
    (argumentsKinded : ∀ argument ∈ arguments, Kinding program context argument argument.kind) :
    Kinding program context (alias.value.substitute substitution) .type ∧
      Substitutes substitution alias.value (alias.value.substitute substitution) :=
  (valid.alias_body found).instantiate instantiated argumentsKinded (Nat.zero_le _)
    (fun _ member => False.elim (List.not_mem_nil member))
    (fun _ member => False.elim (List.not_mem_nil member))

theorem ProgramWellFormed.default_body {program : Program} (valid : ProgramWellFormed program)
    {traitId member : DeclId} {trait : TraitDefinition} {associated : AssociatedDefinition} {body : Term}
    (traitFound : program.trait traitId = some trait) (associatedFound : program.associated member = some associated)
    (owner : associated.owner = traitId) (default : associated.defaultValue = some body) :
    ((trait.generics ++ associated.generics).map (·.id)).Nodup ∧
      Kinding program ⟨trait.generics ++ associated.generics,trait.requirements ++ associated.requirements,
        0,associated.header.module,false,{}⟩ body associated.kind := by
  have lookup : program.lookup member = some (.associated associated) := by
    unfold Program.associated at associatedFound
    cases selected : program.lookup member <;> simp only [selected] at associatedFound
    case none => cases associatedFound
    case some value => cases value <;> simp_all
  have declaration := (valid.2.2.2.2.1 _ (List.mem_of_find?_eq_some lookup)).2
  obtain ⟨actual,actualFound,_,unique,bodies⟩ := declaration
  rw [owner,traitFound] at actualFound
  cases Option.some.inj actualFound
  exact ⟨unique,(bodies body default).1⟩

theorem ProgramWellFormed.default_specialization {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {traitId member : DeclId} {trait : TraitDefinition} {associated : AssociatedDefinition}
    {body : Term} {owners items : List Term} {ownerSub itemSub : Substitution}
    (traitFound : program.trait traitId = some trait) (associatedFound : program.associated member = some associated)
    (owner : associated.owner = traitId) (default : associated.defaultValue = some body)
    (ownerInstance : Instantiates trait.generics owners ownerSub)
    (itemInstance : Instantiates associated.generics items itemSub)
    (argumentsKinded : ∀ argument ∈ owners ++ items, Kinding program context argument argument.kind) :
    Kinding program context (body.substitute (ownerSub ++ itemSub)) associated.kind ∧
      Substitutes (ownerSub ++ itemSub) body (body.substitute (ownerSub ++ itemSub)) := by
  obtain ⟨unique,kinded⟩ := valid.default_body traitFound associatedFound owner default
  exact kinded.instantiate (ownerInstance.append itemInstance unique) argumentsKinded (Nat.zero_le _)
    (fun _ member => False.elim (List.not_mem_nil member))
    (fun _ member => False.elim (List.not_mem_nil member))

theorem ProgramWellFormed.override_body {program : Program} (valid : ProgramWellFormed program)
    {implementation : ImplDefinition} {member : DeclId} {associated : AssociatedDefinition} {body : Term}
    (declared : Definition.implementation implementation ∈ program.declarations)
    (associatedFound : program.associated member = some associated) (bodyMember : (member,body) ∈ implementation.associated) :
    ((implementation.generics ++ associated.generics).map (·.id)).Nodup ∧
      ∃ requirements, Kinding program ⟨implementation.generics ++ associated.generics,
        implementation.requirements ++ requirements,0,implementation.header.module,false,{}⟩ body associated.kind := by
  have declaration := (valid.2.2.2.2.1 _ declared).2
  obtain ⟨_,trait,_,_,_,_,_,signature⟩ := declaration
  obtain ⟨_,ownerSub,_,_,_,bodies⟩ := signature
  obtain ⟨actual,requirements,found,_,_,unique,_,kinded⟩ := bodies member body bodyMember
  rw [associatedFound] at found
  cases Option.some.inj found
  exact ⟨unique,requirements,kinded.1⟩

theorem ProgramWellFormed.override_specialization {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {implementation : ImplDefinition} {member : DeclId} {associated : AssociatedDefinition}
    {body : Term} {arguments items : List Term} {implSub itemSub : Substitution}
    (declared : Definition.implementation implementation ∈ program.declarations)
    (associatedFound : program.associated member = some associated) (bodyMember : (member,body) ∈ implementation.associated)
    (implInstance : Instantiates implementation.generics arguments implSub)
    (itemInstance : Instantiates associated.generics items itemSub)
    (argumentsKinded : ∀ argument ∈ arguments ++ items, Kinding program context argument argument.kind) :
    Kinding program context (body.substitute (implSub ++ itemSub)) associated.kind ∧
      Substitutes (implSub ++ itemSub) body (body.substitute (implSub ++ itemSub)) := by
  obtain ⟨unique,requirements,kinded⟩ := valid.override_body declared associatedFound bodyMember
  exact kinded.instantiate (implInstance.append itemInstance unique) argumentsKinded (Nat.zero_le _)
    (fun _ member => False.elim (List.not_mem_nil member))
    (fun _ member => False.elim (List.not_mem_nil member))

theorem SelectsImpl.instantiates {program : Program} {context : Context} {trait : DeclId} {arguments : List Term}
    {negative : Bool} {implementation : ImplDefinition} {substitution : Substitution}
    (selected : SelectsImpl program context trait arguments negative implementation substitution) :
    ∃ values, Instantiates implementation.generics values substitution ∧
      ∀ value ∈ values, Kinding program context value value.kind := by
  cases selected with
  | selected _ _ _ matched _ =>
    cases matched with
    | matched instantiated kinded _ _ => exact ⟨_,instantiated,kinded⟩

theorem ProjectionDomain.kinding {program : Program} {context : Context} {trait member : DeclId}
    {owners items : List Term} {associated : AssociatedDefinition} {ownerSub itemSub : Substitution}
    (domain : ProjectionDomain program context trait member owners items associated ownerSub itemSub) :
    Kinding program context (.projection trait member owners items associated.kind) associated.kind := by
  cases domain with
  | valid traitFound member associatedFound owner ownerInst itemInst kinded _ _ =>
    exact .projection traitFound member associatedFound owner ownerInst itemInst kinded

/-- Every actual definitional redex and its result are well-kinded from source
admission. Neither a prospective result kind nor an eager normal form is an
extra reduction premise. This includes arbitrary kinded opaque arguments. -/
theorem DefinitionalStep.kinding {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {left right : Term} (step : DefinitionalStep program context left right) :
    Kinding program context left left.kind ∧ Kinding program context right left.kind := by
  cases step with
  | alias found instantiated arguments substituted =>
    refine ⟨.alias found instantiated arguments,?_⟩
    obtain ⟨kinded,_⟩ := valid.alias_specialization found instantiated arguments
    rw [substituted.2.1]
    exact kinded
  | projection domain selected member substituted =>
    refine ⟨domain.kinding,?_⟩
    obtain ⟨values,instantiated,kinded⟩ := selected.instantiates
    cases domain with
    | valid _ _ associatedFound _ _ itemInstance arguments _ _ =>
      have result := (valid.override_specialization selected.declaration associatedFound member
        instantiated itemInstance (by
          intro argument present
          rcases List.mem_append.mp present with present | present
          · exact kinded argument present
          · exact arguments argument (List.mem_append_right _ present))).1
      rw [substituted.2.1]
      exact result
  | defaultProjection domain _ _ default substituted =>
    refine ⟨domain.kinding,?_⟩
    cases domain with
    | valid traitFound _ associatedFound owner ownerInstance itemInstance arguments _ _ =>
      have result := (valid.default_specialization traitFound associatedFound owner default
        ownerInstance itemInstance arguments).1
      rw [substituted.2.1]
      exact result

theorem DefinitionalStep.kind_eq {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {left right : Term} (step : DefinitionalStep program context left right) :
    left.kind = right.kind := (step.kinding valid).2.term_kind.symm

end Glorious.Language
