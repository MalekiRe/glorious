import GloriousLanguage.CapabilityInversion

/-! Structural permission inversion follows the actual local equation and
converted child positions. Generic fields use the real substitution tables;
neither a second resident walker nor raw principal-equation inversion is used. -/
namespace Glorious.Language

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

private theorem converted_field_capability {program : Program} {context : Context}
    {assignment : Term → Option Principal} {expected actual : List Term} {principals : List Principal}
    (children : ListRel (DefinitionallyEqual program context) expected actual)
    (assigned : ListRel (fun field principal => assignment field = some principal) actual principals)
    (leaves : ∀ dependency claimed, assignment dependency = some claimed → CapabilityEvidence program context dependency claimed)
    {parent : Principal} (ordered : parent.Restricts (Principal.fields principals))
    {field : Term} (member : field ∈ expected) :
    ∃ principal, CapabilityEvidence program context field principal ∧ parent.Restricts principal := by
  obtain ⟨source,present,equal⟩ := children.member_left member
  obtain ⟨principal,inside,selected⟩ := assigned.member_left present
  exact ⟨principal,(leaves source principal selected).definitionallyEqual equal.symm,
    ordered.trans (Principal.fields_restricts_member inside)⟩

theorem CapabilityEvidence.closed_tuple_field {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {fields : List Term} {principal : Principal}
    (evidence : CapabilityEvidence program context (.tuple fields) principal) (closed : context.assumptions = [])
    {field : Term} (member : field ∈ fields) :
    ∃ selected, CapabilityEvidence program context field selected ∧ principal.Restricts selected := by
  obtain ⟨_,_,_,head,children,ordered,equation,leaves⟩ := evidence.closed_structural valid closed True.intro
  cases equation
  all_goals try { solve | cases head }
  case tuple assigned => exact converted_field_capability children assigned leaves ordered member

theorem CapabilityEvidence.closed_bindings_field {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {brand region : Term} {fields : List Term} {principal : Principal}
    (evidence : CapabilityEvidence program context (.bindings brand region fields) principal) (closed : context.assumptions = [])
    {field : Term} (member : field ∈ fields) :
    ∃ selected, CapabilityEvidence program context field selected ∧ principal.Restricts selected := by
  obtain ⟨_,_,_,head,children,ordered,equation,leaves⟩ := evidence.closed_structural valid closed True.intro
  cases equation
  all_goals try { solve | cases head }
  case bindings assigned =>
    cases children with
    | cons _ rest =>
      cases rest with
      | cons _ fields => exact converted_field_capability fields assigned leaves ordered member

theorem CapabilityEvidence.closed_array_element {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {element : Term} {sign : Bool} {width : Width} {length : Int} {principal : Principal}
    (evidence : CapabilityEvidence program context (.array element (.constant (.integer sign width length))) principal)
    (closed : context.assumptions = []) (positive : 0 < length) :
    ∃ selected, CapabilityEvidence program context element selected ∧ principal.Restricts selected := by
  obtain ⟨_,_,_,head,children,ordered,equation,leaves⟩ := evidence.closed_structural valid closed True.intro
  cases equation
  all_goals try { solve | cases head }
  case emptyArray =>
    have lengths := (children.at (index := 1) rfl rfl).structural_decomposition valid
      (fun _ member => by rw [closed] at member; cases member) True.intro True.intro
    have zero : length = 0 := by
      have same := lengths.1
      simp only [SameHead,Term.mapChildren,Term.constant.injEq,ScalarValue.integer.injEq] at same
      exact same.2.2
    omega
  case array _ selected =>
    exact ⟨_,(leaves _ _ selected).definitionallyEqual (children.at (index := 0) rfl rfl).symm,ordered⟩

private theorem substituted_fields_convert {program : Program} {context : Context}
    {first last : Substitution} {templates before after : List Term}
    (left : ListRel (Substitutes first) templates before) (right : ListRel (Substitutes last) templates after)
    (equal : ∀ id kind, DefinitionallyEqual program context ((first.get id).getD (.parameter id kind))
      ((last.get id).getD (.parameter id kind))) :
    ListRel (DefinitionallyEqual program context) before after := by
  induction left generalizing after with
  | nil => cases right; exact .nil
  | @cons template before templates rest firstGraph _ tail =>
    cases right with
    | cons lastGraph rest =>
      exact .cons (by
        rw [firstGraph.2.1,lastGraph.2.1]
        exact template.substitutions_convert program context equal) (tail rest)

/-- Nominal fields retain their actual declaration template and actual
instantiation. All variants and the quantity marker bound the parent; the
selected resident field is not independently re-inferred. -/
theorem CapabilityEvidence.closed_nominal_field {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {id : DeclId} {arguments : List Term} {principal : Principal}
    (evidence : CapabilityEvidence program context (.nominal id arguments) principal) (closed : context.assumptions = [])
    {data : DataDefinition} {substitution : Substitution} {template field : Term}
    (found : program.data id = some data) (instantiated : Instantiates data.generics arguments substitution)
    (member : template ∈ (data.variants.flatMap (·.fields)).map (·.type))
    (graph : Substitutes substitution template field) :
    ∃ selected, CapabilityEvidence program context field selected ∧ principal.Restricts selected := by
  obtain ⟨_,_,_,head,children,ordered,equation,leaves⟩ := evidence.closed_structural valid closed True.intro
  cases equation
  all_goals try { solve | cases head }
  case nominal sourceId sourceData sourceArguments sourceSub sourceFields sourcePrincipals marker structural
      selected sourceInst sourceGraph assigned marked meets restricted drops =>
    have identity : id = sourceId := by injection head
    subst sourceId
    obtain rfl := Option.some.inj (selected.symm.trans found)
    simp only [Term.children] at children
    have tables := instantiated.congr_values children
    rw [← sourceInst.2.2] at tables
    obtain ⟨source,present,sourceField⟩ := sourceGraph.member_left member
    obtain ⟨child,inside,capability⟩ := assigned.member_left present
    have converted : DefinitionallyEqual program context field source := by
      rw [graph.2.1,sourceField.2.1]
      exact template.substitutions_convert program context tables.substitution_getD
    have fieldOrder : structural.Restricts (Principal.fields sourcePrincipals) := by
      rw [meets]
      exact Principal.meet_restricts_left _ _
    have structureOrder : _ := restricted
    rcases structureOrder with ⟨_,rfl⟩ | ⟨_,restriction⟩
    · exact ⟨child,(leaves _ _ capability).definitionallyEqual converted.symm,
        ordered.trans (fieldOrder.trans (Principal.fields_restricts_member inside))⟩
    · exact ⟨child,(leaves _ _ capability).definitionallyEqual converted.symm,
        ordered.trans (restriction.trans (fieldOrder.trans (Principal.fields_restricts_member inside)))⟩

theorem CallableFields.closed_field_capability {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {id : DeclId} {arguments fields : List Term} {principal : Principal}
    (declared : CallableFields program id arguments fields)
    (evidence : CapabilityEvidence program context (.callable id arguments) principal) (closed : context.assumptions = [])
    {field : Term} (member : field ∈ fields) :
    ∃ selected, CapabilityEvidence program context field selected ∧ principal.Restricts selected := by
  obtain ⟨_,_,_,head,children,ordered,equation,leaves⟩ := evidence.closed_structural valid closed True.intro
  cases equation
  all_goals try { solve | cases head }
  case callable sourceId sourceArguments sourceFields sourcePrincipals sourceDeclaration assigned =>
    have identity : id = sourceId := by injection head
    subst sourceId
    cases declared with
    | operation => cases member
    | function found instantiated graph =>
      cases sourceDeclaration with
      | operation selected _ =>
        have collision := (Program.function_lookup found).symm.trans (Program.operation_lookup selected)
        cases collision
      | function selected sourceInst sourceGraph =>
        obtain rfl := Option.some.inj (found.symm.trans selected)
        simp only [Term.children] at children
        have tables := instantiated.congr_values children
        rw [← sourceInst.2.2] at tables
        exact converted_field_capability (substituted_fields_convert graph sourceGraph tables.substitution_getD)
          assigned leaves ordered member

theorem CapabilityEvidence.closed_nominal_restriction {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {id : DeclId} {arguments : List Term} {principal : Principal}
    (evidence : CapabilityEvidence program context (.nominal id arguments) principal) (closed : context.assumptions = [])
    {data : DataDefinition} {restriction : Principal} (found : program.data id = some data)
    (restricted : data.principalRestriction = some restriction) : principal.Restricts restriction := by
  obtain ⟨exposed,supported,assignment,head,children,ordered,equation,leaves⟩ := evidence.closed_structural valid closed True.intro
  cases equation
  all_goals try { solve | cases head }
  case nominal sourceId sourceData sourceArguments sourceSub sourceFields sourcePrincipals marker structural
      selected sourceInst sourceGraph assigned marked meets sourceRestricted drops =>
    have identity : id = sourceId := by injection head
    subst sourceId
    obtain rfl := Option.some.inj (selected.symm.trans found)
    rcases sourceRestricted with ⟨none,_⟩ | ⟨some,_⟩
    · rw [none] at restricted; cases restricted
    · obtain rfl := Option.some.inj (some.symm.trans restricted)
      exact ordered

theorem PrincipalOf.nominal_drop_discardable {program : Program} (valid : ProgramWellFormed program)
    {id : DeclId} {arguments : List Term} {principal : Principal}
    (capability : PrincipalOf program (.nominal id arguments) principal)
    {data : DataDefinition} {hook : DeclId} (found : program.data id = some data) (drops : data.dropHook = some hook) :
    principal.MayDiscard := by
  obtain ⟨context,closed,evidence⟩ := capability.1
  obtain ⟨_,supported,_,head,children,_,equation,leaves⟩ := evidence.closed_structural valid closed True.intro
  have sourceEvidence := equation.realize leaves
  have originalEvidence := sourceEvidence.definitionallyEqual (DefinitionallyEqual.congr head children).symm
  have upper := capability.2 supported (originalEvidence.support closed)
  apply upper 0
  cases equation
  all_goals try { solve | cases head }
  case nominal sourceId _ _ _ _ _ _ _ selected _ _ _ _ _ _ discard =>
    have identity : id = sourceId := by injection head
    subst sourceId
    obtain rfl := Option.some.inj (selected.symm.trans found)
    exact discard (by simp [drops])

end Glorious.Language
