import GloriousLanguage.RuntimeSupport

/-! Static judgments transport along a genuine runtime-region permutation.
The permutation supplies only fresh-name mathematics, never an assumed
typing, capability, layout or declaration-equivalence conclusion. -/
namespace Glorious.Language

structure RegionPermutation where
  rename : Identity → Identity
  involutive : ∀ id, rename (rename id) = id

def RegionPermutation.term (permutation : RegionPermutation) : Term → Term :=
  Term.renameRuntimeRegions permutation.rename

theorem RegionPermutation.term_def (permutation : RegionPermutation) (term : Term) :
    permutation.term term = term.renameRuntimeRegions permutation.rename := rfl

def RegionPermutation.substitution (permutation : RegionPermutation) (substitution : Substitution) : Substitution :=
  substitution.map (fun (id,value) => (id,permutation.term value))

def RegionPermutation.binder (permutation : RegionPermutation) (binder : Binder) : Binder :=
  { binder with defaultValue := binder.defaultValue.map permutation.term }

def RegionPermutation.constraint (permutation : RegionPermutation) : Constraint → Constraint :=
  Constraint.mapTerms permutation.term

def RegionPermutation.context (permutation : RegionPermutation) (context : Context) : Context :=
  { context with
    binders := context.binders.map permutation.binder
    assumptions := context.assumptions.map permutation.constraint }

theorem RegionPermutation.term_involutive (permutation : RegionPermutation) (term : Term) :
    permutation.term (permutation.term term) = term :=
  term.renameRuntimeRegions_involutive permutation.rename permutation.involutive

theorem RegionPermutation.term_injective (permutation : RegionPermutation) : Function.Injective permutation.term :=
  Term.renameRuntimeRegions_injective permutation.rename permutation.involutive

theorem RegionPermutation.term_kind (permutation : RegionPermutation) (term : Term) :
    (permutation.term term).kind = term.kind := by
  cases term <;> simp only [RegionPermutation.term,Term.renameRuntimeRegions,Term.kind]

theorem RegionPermutation.lexical_term (permutation : RegionPermutation) {term : Term}
    (lexical : term.Lexical) : permutation.term term = term := by
  have identity : permutation.term term = term.renameRuntimeRegions id :=
    term.renameRuntimeRegions_congr permutation.rename id (fun id occurs => False.elim (lexical.1 id occurs))
  exact identity.trans term.renameRuntimeRegions_id

theorem RegionPermutation.term_substitute (permutation : RegionPermutation) (substitution : Substitution) (term : Term) :
    permutation.term (term.substitute substitution) =
      (permutation.term term).substitute (permutation.substitution substitution) := by
  cases term <;> simp only [Term.substitute,RegionPermutation.term,Term.renameRuntimeRegions]
  case parameter id kind =>
    rw [RegionPermutation.substitution,Table.get_map_values]
    cases substitution.get id <;> simp only [Option.getD,Option.map,RegionPermutation.term,Term.renameRuntimeRegions]
  all_goals try rfl
  all_goals try simp only [List.map_map,Function.comp_def]
  all_goals
    congr 1
    all_goals first
    | exact permutation.term_substitute substitution _
    | apply List.map_congr_left
      intro child _
      exact permutation.term_substitute substitution child
termination_by term

theorem RegionPermutation.substitution_involutive (permutation : RegionPermutation) (substitution : Substitution) :
    permutation.substitution (permutation.substitution substitution) = substitution := by
  simp only [RegionPermutation.substitution,List.map_map,Function.comp_def,permutation.term_involutive]
  exact List.map_eq_self_of _ _ (fun _ _ => rfl)

theorem RegionPermutation.substitution_filter (permutation : RegionPermutation) (substitution : Substitution)
    (keep : Identity → Bool) :
    permutation.substitution (substitution.filter (fun entry => keep entry.1)) =
      (permutation.substitution substitution).filter (fun entry => keep entry.1) := by
  simp only [RegionPermutation.substitution,List.filter_map,Function.comp_def]

theorem RegionPermutation.binder_involutive (permutation : RegionPermutation) (binder : Binder) :
    permutation.binder (permutation.binder binder) = binder := by
  cases binder
  simp only [RegionPermutation.binder,Option.map_map,Function.comp_def,permutation.term_involutive,Option.map_id']

theorem RegionPermutation.constraint_involutive (permutation : RegionPermutation) (constraint : Constraint) :
    permutation.constraint (permutation.constraint constraint) = constraint := by
  cases constraint <;>
    simp only [RegionPermutation.constraint,Constraint.mapTerms,permutation.term_involutive,
      List.map_map,Function.comp_def,Option.map_map,Option.map_id']
  all_goals try rfl
  all_goals
    congr 1
    all_goals first
    | exact List.map_eq_self_of _ _ (fun _ _ => rfl)
    | exact List.map_eq_self_of _ _ (fun _ _ => permutation.term_involutive _)
    | exact List.map_eq_self_of _ _ (fun _ _ => permutation.binder_involutive _)
    | exact List.map_eq_self_of _ _ (fun _ _ => permutation.constraint_involutive _)
termination_by constraint

theorem RegionPermutation.context_involutive (permutation : RegionPermutation) (context : Context) :
    permutation.context (permutation.context context) = context := by
  cases context
  simp only [RegionPermutation.context,List.map_map,Function.comp_def,
    permutation.binder_involutive,permutation.constraint_involutive,List.map_id']

theorem Constraint.mapTerms_substitute (f : Term → Term) (mapped : Substitution → Substitution)
    (terms : ∀ substitution term, f (term.substitute substitution) = (f term).substitute (mapped substitution))
    (filtered : ∀ substitution (keep : Identity → Bool), mapped (substitution.filter (fun entry => keep entry.1)) =
      (mapped substitution).filter (fun entry => keep entry.1))
    (substitution : Substitution) (constraint : Constraint) :
    (constraint.substitute substitution).mapTerms f = (constraint.mapTerms f).substitute (mapped substitution) := by
  cases constraint <;>
    simp only [Constraint.mapTerms,Constraint.substitute,terms,List.map_map,Function.comp_def]
  all_goals try rfl
  case quantified binders requirements =>
    have restricted :
        (mapped substitution).filter
          (fun entry => !(binders.any (fun binder => binder.id == entry.1))) =
        mapped (substitution.filter
          (fun entry => !(binders.any (fun binder => binder.id == entry.1)))) :=
      (filtered substitution
        (fun id => !(binders.any (fun binder => binder.id == id)))).symm
    simp only [List.any_map,Function.comp_def,restricted,Option.map_map]
    congr 1
    · apply List.map_congr_left
      intro binder _
      simp only [terms]
    · apply List.map_congr_left
      intro requirement _
      exact requirement.mapTerms_substitute f mapped terms filtered _
termination_by constraint

theorem RegionPermutation.constraint_substitute (permutation : RegionPermutation)
    (substitution : Substitution) (constraint : Constraint) :
    permutation.constraint (constraint.substitute substitution) =
      (permutation.constraint constraint).substitute (permutation.substitution substitution) :=
  constraint.mapTerms_substitute permutation.term permutation.substitution permutation.term_substitute permutation.substitution_filter substitution

theorem RegionPermutation.parameter_origin (permutation : RegionPermutation) {term : Term} {id : Identity} {kind : Kind}
    (same : permutation.term term = .parameter id kind) : term = .parameter id kind := by
  cases term <;> simp only [RegionPermutation.term,Term.renameRuntimeRegions] at same <;> cases same <;> rfl

theorem RegionPermutation.parameter_occurs (permutation : RegionPermutation) {term : Term} {id : Identity} {kind : Kind}
    (occurs : Occurs (.parameter id kind) (permutation.term term)) : Occurs (.parameter id kind) term := by
  obtain ⟨original,nested,same⟩ := Term.renameRuntimeRegions_occurs_preimage permutation.rename occurs
  have originalEq := permutation.parameter_origin same
  exact originalEq ▸ nested

theorem RegionPermutation.substitutes (permutation : RegionPermutation) {substitution : Substitution} {before after : Term}
    (related : Substitutes substitution before after) :
    Substitutes (permutation.substitution substitution) (permutation.term before) (permutation.term after) := by
  refine ⟨by simpa only [permutation.term_kind] using related.1,?_,?_⟩
  · rw [related.2.1,permutation.term_substitute]
  · intro id kind value occurs found
    change Table.get (substitution.map (fun (id,term) => (id,permutation.term term))) id = some value at found
    rw [Table.get_map_values] at found
    obtain ⟨previous,selected,rfl⟩ := Option.map_eq_some_iff.mp found
    simpa only [permutation.term_kind] using related.2.2 id kind previous (permutation.parameter_occurs occurs) selected

theorem RegionPermutation.substitutes_self (permutation : RegionPermutation) {substitution : Substitution} {term : Term}
    (related : Substitutes substitution term (term.substitute substitution)) :
    Substitutes (permutation.substitution substitution) (permutation.term term)
      ((permutation.term term).substitute (permutation.substitution substitution)) := by
  simpa only [permutation.term_substitute] using permutation.substitutes related

theorem RegionPermutation.substitutes_lexical (permutation : RegionPermutation) {substitution : Substitution} {before after : Term}
    (lexical : before.Lexical) (related : Substitutes substitution before after) :
    Substitutes (permutation.substitution substitution) before (permutation.term after) := by
  simpa only [permutation.lexical_term lexical] using permutation.substitutes related

theorem RegionPermutation.substitutes_list (permutation : RegionPermutation) {substitution : Substitution} {before after : List Term}
    (related : ListRel (Substitutes substitution) before after) :
    ListRel (Substitutes (permutation.substitution substitution)) (before.map permutation.term) (after.map permutation.term) := by
  induction related with
  | nil => exact .nil
  | cons first _ ih => exact .cons (permutation.substitutes first) ih

theorem RegionPermutation.substitutes_lexical_list (permutation : RegionPermutation) {substitution : Substitution}
    {before after : List Term} (lexical : ∀ term ∈ before, term.Lexical)
    (related : ListRel (Substitutes substitution) before after) :
    ListRel (Substitutes (permutation.substitution substitution)) before (after.map permutation.term) := by
  have unchanged : before.map permutation.term = before :=
    List.map_eq_self_of _ _ (fun term member => permutation.lexical_term (lexical term member))
  simpa only [unchanged] using permutation.substitutes_list related

theorem RegionPermutation.constraint_admissible (permutation : RegionPermutation)
    {substitution : Substitution} {constraint : Constraint}
    (admissible : constraint.SubstitutionAdmissible substitution) :
    (permutation.constraint constraint).SubstitutionAdmissible (permutation.substitution substitution) := by
  cases constraint <;>
    simp only [RegionPermutation.constraint,Constraint.mapTerms,Constraint.SubstitutionAdmissible] at admissible ⊢
  all_goals try exact ⟨permutation.substitutes_self admissible.1,permutation.substitutes_self admissible.2⟩
  case use => exact permutation.substitutes_self admissible
  all_goals try {
    intro term member
    try simp only [← List.map_cons] at member
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
    exact permutation.substitutes_self (admissible original present) }
  case quantified binders requirements =>
    have restricted :
        (permutation.substitution substitution).filter
          (fun entry => !(binders.any (fun binder => binder.id == entry.1))) =
        permutation.substitution (substitution.filter
          (fun entry => !(binders.any (fun binder => binder.id == entry.1)))) :=
      (permutation.substitution_filter substitution
        (fun id => !(binders.any (fun binder => binder.id == id)))).symm
    simp only [List.any_map,Function.comp_def,restricted]
    refine ⟨?_,?_,?_⟩
    · intro entry present binder member occurs
      obtain ⟨original,inOriginal,rfl⟩ := List.mem_map.mp present
      obtain ⟨oldBinder,inBinders,rfl⟩ := List.mem_map.mp member
      exact admissible.1 original inOriginal oldBinder inBinders (permutation.parameter_occurs occurs)
    · intro binder member value found
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      obtain ⟨oldValue,selected,rfl⟩ := Option.map_eq_some_iff.mp found
      exact permutation.substitutes_self (admissible.2.1 original present oldValue selected)
    · intro requirement member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      exact permutation.constraint_admissible (admissible.2.2 original present)
termination_by constraint

theorem RegionPermutation.substitute_constraint (permutation : RegionPermutation)
    {substitution : Substitution} {before after : Constraint} (related : SubstituteConstraint substitution before after) :
    SubstituteConstraint (permutation.substitution substitution) (permutation.constraint before) (permutation.constraint after) := by
  refine ⟨permutation.constraint_admissible related.1,?_⟩
  rw [related.2,permutation.constraint_substitute]

theorem Instantiates.permute {binders : List Binder} {arguments : List Term} {substitution : Substitution}
    (instantiated : Instantiates binders arguments substitution) (permutation : RegionPermutation) :
    Instantiates binders (arguments.map permutation.term) (permutation.substitution substitution) := by
  refine ⟨instantiated.1,?_,?_⟩
  · have kinds := instantiated.2.1
    clear instantiated
    induction kinds with
    | nil => exact .nil
    | cons head _ ih => exact .cons (by simpa only [permutation.term_kind] using head) ih
  · rw [instantiated.2.2]
    simp only [RegionPermutation.substitution,List.zip_map_right]
    apply List.map_congr_left
    intro entry _
    cases entry
    rfl

theorem Instantiates.permute_binders {binders : List Binder} {arguments : List Term} {substitution : Substitution}
    (instantiated : Instantiates binders arguments substitution) (permutation : RegionPermutation) :
    Instantiates (binders.map permutation.binder) arguments substitution := by
  refine ⟨by simpa only [List.map_map,Function.comp_def,RegionPermutation.binder] using instantiated.1,?_,?_⟩
  · have kinds := instantiated.2.1
    clear instantiated
    induction kinds with
    | nil => exact .nil
    | cons head _ ih => exact .cons head ih
  · simpa only [List.map_map,Function.comp_def,RegionPermutation.binder] using instantiated.2.2

theorem CallableFields.permute {program : Program} (valid : ProgramWellFormed program)
    {id : DeclId} {arguments fields : List Term} (declared : CallableFields program id arguments fields)
    (permutation : RegionPermutation) :
    CallableFields program id (arguments.map permutation.term) (fields.map permutation.term) := by
  cases declared with
  | function found instantiated substituted =>
      have lexical := valid.lexical (List.mem_of_find?_eq_some (Program.function_lookup found))
      exact .function found (instantiated.permute permutation) (permutation.substitutes_lexical_list (by
        intro term member
        exact lexical term (by simp only [Definition.terms,List.mem_append]; exact Or.inl (Or.inr member))) substituted)
  | operation found instantiated => exact .operation found (instantiated.permute permutation)

def RegionPermutation.assignment (permutation : RegionPermutation) (assignment : Term → Option Principal) :
    Term → Option Principal := fun term => assignment (permutation.term term)

theorem RegionPermutation.assignment_at (permutation : RegionPermutation)
    (assignment : Term → Option Principal) (term : Term) :
    permutation.assignment assignment (permutation.term term) = assignment term := by
  simp only [RegionPermutation.assignment,permutation.term_involutive]

theorem RegionPermutation.assignment_fields (permutation : RegionPermutation)
    {assignment : Term → Option Principal} {fields : List Term} {principals : List Principal}
    (related : ListRel (fun field principal => assignment field = some principal) fields principals) :
    ListRel (fun field principal => permutation.assignment assignment field = some principal)
      (fields.map permutation.term) principals := by
  induction related with
  | nil => exact .nil
  | cons first _ ih => exact .cons (by simpa only [permutation.assignment_at] using first) ih

theorem Program.alias_lookup {program : Program} {id : DeclId} {declaration : AliasDefinition}
    (found : program.alias id = some declaration) : program.lookup id = some (.alias declaration) := by
  unfold Program.alias at found
  cases selected : program.lookup id <;> simp only [selected] at found
  case none => cases found
  case some value => cases value <;> simp_all

theorem CapabilityEquation.permute {program : Program} (valid : ProgramWellFormed program)
    {assignment : Term → Option Principal} {term : Term} {principal : Principal}
    (equation : CapabilityEquation program assignment term principal) (permutation : RegionPermutation) :
    CapabilityEquation program (permutation.assignment assignment) (permutation.term term) principal := by
  cases equation <;> simp only [RegionPermutation.term,Term.renameRuntimeRegions] <;>
    (try simp only [← RegionPermutation.term_def])
  case unit => exact .unit
  case bottom => exact .bottom
  case scalar => exact .scalar
  case raw => exact .raw
  case shared => exact .shared
  case unique => exact .unique
  case label => exact .label
  case tuple fields => exact .tuple (permutation.assignment_fields fields)
  case emptyArray => exact .emptyArray
  case array positive found => exact .array positive (by simpa only [permutation.assignment_at] using found)
  case alias found instantiated substituted selected =>
      have lexical := valid.lexical (List.mem_of_find?_eq_some (Program.alias_lookup found))
      exact .alias found (instantiated.permute permutation)
        (permutation.substitutes_lexical (lexical _ (by simp [Definition.terms])) substituted)
        (by simpa only [permutation.assignment_at] using selected)
  case nominal id data arguments substitution fields principals marker structural found instantiated
      substituted capabilities marked meets restricted drops =>
      have lexical := valid.lexical (List.mem_of_find?_eq_some (Program.data_lookup found))
      refine .nominal found (instantiated.permute permutation)
        (permutation.substitutes_lexical_list (fun term member => lexical term (by
          simp only [Definition.terms,List.mem_append]
          exact Or.inl (Or.inl (Or.inl member)))) substituted)
        (permutation.assignment_fields capabilities) ?_ meets restricted drops
      rcases marked with noMarker | ⟨source,value,sourceFound,sourceSub,valueKind⟩
      · exact Or.inl noMarker
      · refine Or.inr ⟨source,permutation.term value,sourceFound,
          permutation.substitutes_lexical (lexical source (by
            simp only [Definition.terms,List.mem_append]
            exact Or.inl (Or.inl (Or.inr (by simp [sourceFound]))))) sourceSub,?_⟩
        rcases valueKind with markerValue | ⟨typeKind,selected⟩
        · exact Or.inl (by rw [markerValue]; simp only [RegionPermutation.term,Term.renameRuntimeRegions])
        · exact Or.inr ⟨by simpa only [permutation.term_kind] using typeKind,
            by simpa only [permutation.assignment_at] using selected⟩
  case callable fields capabilities => exact .callable (fields.permute valid permutation) (permutation.assignment_fields capabilities)
  case environment capabilities => exact .environment (permutation.assignment_fields capabilities)
  case available selected =>
      apply CapabilityEquation.available
      simpa only [RegionPermutation.term,Term.renameRuntimeRegions] using
        (show permutation.assignment assignment (permutation.term _) = _ from
          (permutation.assignment_at assignment _).trans selected)
  case bindings capabilities => exact .bindings (permutation.assignment_fields capabilities)
  case optionalContinuation => exact .optionalContinuation
  case exactContinuation positive => exact .exactContinuation positive

theorem CapabilitySolution.permute {program : Program} (valid : ProgramWellFormed program)
    {assignment : Term → Option Principal} (solution : CapabilitySolution program assignment)
    (permutation : RegionPermutation) : CapabilitySolution program (permutation.assignment assignment) := by
  intro term principal
  constructor
  · intro selected
    have equation := ((solution (permutation.term term) principal).mp selected).permute valid permutation
    simpa only [permutation.term_involutive] using equation
  · intro equation
    have original := equation.permute valid permutation
    have identity : permutation.assignment (permutation.assignment assignment) = assignment := by
      funext term
      exact permutation.assignment_at assignment term
    rw [identity] at original
    exact (solution (permutation.term term) principal).mpr original

def CapabilityModel.permute {program : Program} (valid : ProgramWellFormed program)
    (model : CapabilityModel program) (permutation : RegionPermutation) : CapabilityModel program where
  principal := permutation.assignment model.principal
  equations := model.equations.permute valid permutation
  greatest other solution term result selected := by
    have reflected : permutation.assignment other (permutation.term term) = some result := by
      simpa only [permutation.assignment_at] using selected
    exact model.greatest (permutation.assignment other) (solution.permute valid permutation)
      (permutation.term term) result reflected

theorem PrincipalOf.permute {program : Program} (valid : ProgramWellFormed program)
    {type : Term} {principal : Principal} (capability : PrincipalOf program type principal)
    (permutation : RegionPermutation) : PrincipalOf program (permutation.term type) principal := by
  obtain ⟨model,selected⟩ := capability
  exact ⟨model.permute valid permutation,by simpa only [CapabilityModel.permute,permutation.assignment_at] using selected⟩

theorem Kinding.permute {program : Program} {context : Context} {term : Term} {kind : Kind}
    (typed : Kinding program context term kind) (permutation : RegionPermutation) :
    Kinding program (permutation.context context) (permutation.term term) kind := by
  induction typed <;> simp only [RegionPermutation.term,Term.renameRuntimeRegions] <;>
    (try simp only [← RegionPermutation.term_def])
  case quantity bounds => exact .quantity bounds
  case parameter binder member =>
      exact .parameter (binder := permutation.binder binder) (List.mem_map.mpr ⟨binder,member,rfl⟩)
  case rigid bound => exact .rigid bound
  case runtimeRegion => exact .runtimeRegion
  case runtimeBrand => exact .runtimeBrand
  case «variable» bound => exact .variable bound
  case unit => exact .unit
  case bottom => exact .bottom
  case scalar valid => exact .scalar valid
  case tuple _ ih =>
      exact .tuple (by intro term member; obtain ⟨original,present,rfl⟩ := List.mem_map.mp member; exact ih original present)
  case array _ _ element length => exact .array element length
  case reference _ _ region referent => exact .reference region referent
  case rawPointer _ referent => exact .rawPointer referent
  case nominal found instantiated _ ih =>
      exact .nominal found (instantiated.permute permutation) (by
        intro term member
        obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
        simpa only [← permutation.term_def,permutation.term_kind] using ih original present)
  case alias found instantiated _ ih =>
      exact .alias found (instantiated.permute permutation) (by
        intro term member
        obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
        simpa only [← permutation.term_def,permutation.term_kind] using ih original present)
  case callable found instantiated _ ih =>
      exact .callable found (instantiated.permute permutation) (by
        intro term member
        obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
        simpa only [← permutation.term_def,permutation.term_kind] using ih original present)
  case continuation _ _ _ _ quantity brand argument answer effects =>
      exact .continuation brand argument answer effects quantity
  case label _ _ _ brand region result => exact .label brand region result
  case environment _ _ _ brand region ih =>
      exact .environment brand region (by
        intro term member; obtain ⟨original,present,rfl⟩ := List.mem_map.mp member; exact ih original present)
  case available _ _ _ brand region ih =>
      exact .available brand region (by
        intro term member; obtain ⟨original,present,rfl⟩ := List.mem_map.mp member; exact ih original present)
  case bindings _ _ _ brand region ih =>
      exact .bindings brand region (by
        intro term member; obtain ⟨original,present,rfl⟩ := List.mem_map.mp member; exact ih original present)
  case effect found instantiated _ ih =>
      exact .effect found (instantiated.permute permutation) (by
        intro term member
        obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
        simpa only [← permutation.term_def,permutation.term_kind] using ih original present)
  case row _ _ instances tails =>
      exact .row (by intro term member; obtain ⟨original,present,rfl⟩ := List.mem_map.mp member; exact instances original present)
        (by intro term member; obtain ⟨original,present,rfl⟩ := List.mem_map.mp member; exact tails original present)
  case projection found member associated owner owners items _ ih =>
      exact .projection found member associated owner (owners.permute permutation) (items.permute permutation) (by
        intro term present
        rw [← List.map_append] at present
        obtain ⟨original,inOriginal,rfl⟩ := List.mem_map.mp present
        simpa only [← permutation.term_def,permutation.term_kind] using ih original inOriginal)
  case scalarConstant valid => exact .scalarConstant valid
  case tupleConstant _ ih =>
      exact .tupleConstant (by
        intro term member; obtain ⟨original,present,rfl⟩ := List.mem_map.mp member; exact ih original present)
  case constructorConstant found instantiated count _ ih =>
      exact .constructorConstant found (instantiated.permute permutation) (by simpa only [List.length_map] using count)
        (by intro term member; obtain ⟨original,present,rfl⟩ := List.mem_map.mp member; exact ih original present)
  case principal => exact .principal
  case static => exact .static

theorem RegionIncludes.permute {assumptions : List Constraint} {long short : Term}
    (included : RegionIncludes assumptions long short) (permutation : RegionPermutation) :
    RegionIncludes (assumptions.map permutation.constraint) (permutation.term long) (permutation.term short) := by
  induction included with
  | refl => exact .refl
  | static => simpa only [RegionPermutation.term,Term.renameRuntimeRegions] using
      (RegionIncludes.static (assumptions := assumptions.map permutation.constraint) (region := permutation.term _))
  | assumed member => exact .assumed (List.mem_map.mpr ⟨_,member,by
      simp only [RegionPermutation.constraint,Constraint.mapTerms]⟩)
  | trans _ _ first second => exact .trans first second

theorem RegionPermutation.term_children (permutation : RegionPermutation) (term : Term) :
    (permutation.term term).children = term.children.map permutation.term := by
  cases term <;> simp only [RegionPermutation.term,Term.renameRuntimeRegions,Term.children,
    List.map_cons,List.map_nil,List.map_append]

theorem RegionPermutation.term_head (permutation : RegionPermutation) (term : Term) :
    (permutation.term term).mapChildren (fun _ => .unit) = permutation.term (term.mapChildren (fun _ => .unit)) := by
  cases term <;> simp only [RegionPermutation.term,Term.renameRuntimeRegions,Term.mapChildren,
    List.map_map,Function.comp_def]
  all_goals try rfl
  all_goals congr 1
  all_goals apply List.map_congr_left
  all_goals intro child _
  all_goals simp only [Term.renameRuntimeRegions]

theorem SameHead.permute {a b : Term} (same : SameHead a b) (permutation : RegionPermutation) :
    SameHead (permutation.term a) (permutation.term b) := by
  unfold SameHead at same ⊢
  rw [permutation.term_head,permutation.term_head,same]

theorem RegionPermutation.lexical_binder (permutation : RegionPermutation) {binder : Binder}
    (lexical : ∀ term, binder.defaultValue = some term → term.Lexical) : permutation.binder binder = binder := by
  cases binder with
  | mk id name kind defaultValue =>
      cases defaultValue with
      | none => rfl
      | some term => simp only [RegionPermutation.binder,Option.map,permutation.lexical_term (lexical term rfl)]

theorem RegionPermutation.lexical_constraint (permutation : RegionPermutation) {constraint : Constraint}
    (lexical : ∀ term ∈ constraint.terms, term.Lexical) : permutation.constraint constraint = constraint := by
  cases constraint <;> simp only [RegionPermutation.constraint,Constraint.mapTerms]
  all_goals try {
    congr 1
    all_goals first
    | exact permutation.lexical_term (lexical _ (by simp [Constraint.terms]))
    | exact List.map_eq_self_of _ _ (fun term member => permutation.lexical_term (lexical term (by
        simp [Constraint.terms,member]))) }
  case quantified binders requirements =>
    congr 1
    · apply List.map_eq_self_of
      intro binder member
      apply permutation.lexical_binder
      intro term found
      exact lexical term (by
        simp only [Constraint.terms,List.mem_append,List.mem_flatMap]
        exact Or.inl ⟨binder,member,by simp [found]⟩)
    · apply List.map_eq_self_of
      intro requirement member
      exact permutation.lexical_constraint (fun term present => lexical term (by
        simp only [Constraint.terms,List.mem_append,List.mem_flatMap]
        exact Or.inr ⟨requirement,member,present⟩))
termination_by constraint

theorem RegionPermutation.substitute_lexical_constraint (permutation : RegionPermutation)
    {substitution : Substitution} {before after : Constraint} (lexical : ∀ term ∈ before.terms, term.Lexical)
    (related : SubstituteConstraint substitution before after) :
    SubstituteConstraint (permutation.substitution substitution) before (permutation.constraint after) := by
  simpa only [permutation.lexical_constraint lexical] using permutation.substitute_constraint related

theorem RegionPermutation.substitute_lexical_constraints (permutation : RegionPermutation)
    {substitution : Substitution} {before after : List Constraint}
    (lexical : ∀ constraint ∈ before, ∀ term ∈ constraint.terms, term.Lexical)
    (related : ListRel (SubstituteConstraint substitution) before after) :
    ListRel (SubstituteConstraint (permutation.substitution substitution)) before (after.map permutation.constraint) := by
  induction related with
  | nil => exact .nil
  | cons first _ ih =>
      exact .cons (permutation.substitute_lexical_constraint (lexical _ List.mem_cons_self) first)
        (ih (fun constraint member => lexical constraint (List.mem_cons_of_mem _ member)))

theorem Program.associated_lookup {program : Program} {id : DeclId} {declaration : AssociatedDefinition}
    (found : program.associated id = some declaration) : program.lookup id = some (.associated declaration) := by
  unfold Program.associated at found
  cases selected : program.lookup id <;> simp only [selected] at found
  case none => cases found
  case some value => cases value <;> simp_all

theorem SelectsImpl.declaration {program : Program} {context : Context} {trait : DeclId} {arguments : List Term}
    {negative : Bool} {implementation : ImplDefinition} {substitution : Substitution}
    (selected : SelectsImpl program context trait arguments negative implementation substitution) :
    Definition.implementation implementation ∈ program.declarations := by
  cases selected with
  | selected member _ _ _ _ _ _ _ => exact member

theorem Entails.permute {program : Program} (valid : ProgramWellFormed program) {context : Context}
    {constraint : Constraint} (entailed : Entails program context constraint) (permutation : RegionPermutation) :
    Entails program (permutation.context context) (permutation.constraint constraint) := by
  refine Entails.rec
    (motive_1 := fun a b _ => Equal program (permutation.context context) (permutation.term a) (permutation.term b))
    (motive_2 := fun trait arguments negative implementation substitution _ =>
      SelectsImpl program (permutation.context context) trait (arguments.map permutation.term) negative implementation
        (permutation.substitution substitution))
    (motive_3 := fun effect row _ => RowMember program (permutation.context context) (permutation.term effect) (permutation.term row))
    (motive_4 := fun required allowed _ => RowSubset program (permutation.context context)
      (permutation.term required) (permutation.term allowed))
    (motive_5 := fun type region _ => TypeOutlives program (permutation.context context)
      (permutation.term type) (permutation.term region))
    (motive_6 := fun constraint _ => Entails program (permutation.context context) (permutation.constraint constraint))
    (motive_7 := fun substitution constraint _ => EntailsSubstitution program (permutation.context context)
      (permutation.substitution substitution) (permutation.constraint constraint))
    (motive_8 := fun left right _ => ListRel (Equal program (permutation.context context))
      (left.map permutation.term) (right.map permutation.term))
    ?refl ?symm ?trans ?congr ?assumed ?alias ?projection ?defaultProjection ?rowPermutation ?rowFlatten
    ?rowDuplicate ?tailDuplicate ?selected ?head ?tail ?equal ?empty ?assumed_1 ?same ?trans_1 ?instances
    ?assumed_2 ?scalar ?unit ?pointer ?reference ?bottom ?tuple ?array ?nominal ?callable ?label ?environment
    ?available ?bindings ?equal_1 ?checkedCallable ?checkedRunsIn ?assumed_3 ?equality ?outlives ?typeOutlives
    ?rows ?implementation ?use ?quantified ?instantiated ?nil ?cons entailed
  all_goals intros
  all_goals
    simp only [RegionPermutation.term,Term.renameRuntimeRegions,RegionPermutation.constraint,Constraint.mapTerms,
      List.map_cons,List.map_nil,List.map_append] <;>
    (try simp only [← RegionPermutation.term_def])
  case refl => exact .refl
  case symm _ ih => exact .symm ih
  case trans _ _ first second => exact .trans first second
  case congr same _ children =>
    exact .congr (same.permute permutation) (by
      rw [permutation.term_children,permutation.term_children]
      exact children)
  case assumed member => exact .assumed (List.mem_map.mpr ⟨_,member,by
    simp only [RegionPermutation.constraint,Constraint.mapTerms]⟩)
  case alias found instantiated substituted =>
    have lexical := valid.lexical (List.mem_of_find?_eq_some (Program.alias_lookup found))
    exact .alias found (instantiated.permute permutation)
      (permutation.substitutes_lexical (lexical _ (by simp [Definition.terms])) substituted)
  case projection selected found owner member specialized instantiated substituted ih =>
    have lexical := valid.lexical selected.declaration
    exact .projection ih found owner member
      (permutation.substitutes_lexical (lexical _ (by
        simp only [Definition.terms,List.mem_append,List.mem_map]
        exact Or.inl (Or.inl (Or.inr ⟨_,member,rfl⟩)))) specialized)
      (instantiated.permute permutation) (permutation.substitutes substituted)
  case defaultProjection _ declaration ownerInstantiated found owner missing default specialized instantiated substituted ih =>
    have lexical := valid.lexical (List.mem_of_find?_eq_some (Program.associated_lookup found))
    exact .defaultProjection ih declaration (ownerInstantiated.permute permutation) found owner missing default
      (permutation.substitutes_lexical (lexical _ (by
        simp only [Definition.terms,List.mem_append]
        exact Or.inl (Or.inl (by simp [default])))) specialized)
      (instantiated.permute permutation) (permutation.substitutes substituted)
  case rowPermutation instances tails => exact .rowPermutation (instances.map _) (tails.map _)
  case rowFlatten => exact .rowFlatten
  case rowDuplicate _ ih => exact .rowDuplicate ih
  case tailDuplicate _ ih => exact .tailDuplicate ih
  case selected member trait negative instantiated substituted _ requirements _ equals entailed =>
    have lexical := valid.lexical member
    refine .selected member trait negative ?_
      (permutation.substitutes_lexical_list (fun term present => lexical term (by
        simp only [Definition.terms,List.mem_append]
        exact Or.inl (Or.inl (Or.inl present)))) substituted) equals
      (permutation.substitute_lexical_constraints (fun constraint present term nested => lexical term (by
        simp only [Definition.terms,List.mem_append,List.mem_flatMap]
        exact Or.inl (Or.inr ⟨constraint,present,nested⟩))) requirements) ?_
    · obtain ⟨values,instantiated,kinded⟩ := instantiated
      refine ⟨values.map permutation.term,instantiated.permute permutation,?_⟩
      intro term present
      obtain ⟨original,inOriginal,rfl⟩ := List.mem_map.mp present
      simpa only [permutation.term_kind] using (kinded original inOriginal).permute permutation
    · intro constraint present
      obtain ⟨original,inOriginal,rfl⟩ := List.mem_map.mp present
      exact entailed original inOriginal
  case head present _ equal => exact .head (List.mem_map.mpr ⟨_,present,rfl⟩) equal
  case tail present _ nested => exact .tail (List.mem_map.mpr ⟨_,present,rfl⟩) nested
  case equal _ _ equal nested => exact .equal equal nested
  case empty => exact .empty
  case assumed_1 member => exact .assumed (List.mem_map.mpr ⟨_,member,by
    simp only [RegionPermutation.constraint,Constraint.mapTerms]⟩)
  case same _ equal => exact .same equal
  case trans_1 _ _ first second => exact .trans first second
  case instances _ _ instances tails =>
    refine .instances ?_ ?_
    · intro term member; obtain ⟨original,present,rfl⟩ := List.mem_map.mp member; exact instances original present
    · intro term member; obtain ⟨original,present,rfl⟩ := List.mem_map.mp member; exact tails original present
  case assumed_2 member => exact .assumed (List.mem_map.mpr ⟨_,member,by
    simp only [RegionPermutation.constraint,Constraint.mapTerms]⟩)
  case scalar => exact .scalar
  case unit => exact .unit
  case pointer => exact .pointer
  case reference included => exact .reference (included.permute permutation)
  case bottom => exact .bottom
  case tuple _ fields =>
    exact .tuple (by intro term member; obtain ⟨original,present,rfl⟩ := List.mem_map.mp member; exact fields original present)
  case array _ element => exact .array element
  case nominal found instantiated substituted _ fields =>
    have lexical := valid.lexical (List.mem_of_find?_eq_some (Program.data_lookup found))
    exact .nominal found (instantiated.permute permutation)
      (permutation.substitutes_lexical_list (fun term member => lexical term (by
        simp only [Definition.terms,List.mem_append]
        exact Or.inl (Or.inl (Or.inl member)))) substituted)
      (by intro term member; obtain ⟨original,present,rfl⟩ := List.mem_map.mp member; exact fields original present)
  case callable selected _ fields =>
    exact .callable (selected.permute valid permutation)
      (by intro term member; obtain ⟨original,present,rfl⟩ := List.mem_map.mp member; exact fields original present)
  case label included => exact .label (included.permute permutation)
  case environment included _ fields =>
    exact .environment (included.permute permutation)
      (by intro term member; obtain ⟨original,present,rfl⟩ := List.mem_map.mp member; exact fields original present)
  case available _ environment =>
    exact .available (by simpa only [RegionPermutation.term,Term.renameRuntimeRegions] using environment)
  case bindings included _ fields =>
    exact .bindings (included.permute permutation)
      (by intro term member; obtain ⟨original,present,rfl⟩ := List.mem_map.mp member; exact fields original present)
  case equal_1 _ _ equal previous => exact .equal equal previous
  case checkedCallable found member receiver arguments result effects =>
    have lexical := valid.lexical (List.mem_of_find?_eq_some (Program.function_lookup found))
    have invocation : ∀ (term : Term), term ∈ _ → term.Lexical := fun term present => lexical term (by
      simp only [Definition.terms,List.mem_append,List.mem_flatMap]
      exact Or.inr ⟨_,member,present⟩)
    exact .checkedCallable found member
      (permutation.substitutes_lexical (invocation _ (by simp [InvocationRelation.terms])) receiver)
      (permutation.substitutes_lexical_list (fun term present => invocation term (by simp [InvocationRelation.terms,present])) arguments)
      (permutation.substitutes_lexical (invocation _ (by simp [InvocationRelation.terms])) result)
      (permutation.substitutes_lexical (invocation _ (by simp [InvocationRelation.terms])) effects)
  case checkedRunsIn found member receiver access arguments after =>
    have lexical := valid.lexical (List.mem_of_find?_eq_some (Program.function_lookup found))
    have invocation : ∀ (term : Term), term ∈ _ → term.Lexical := fun term present => lexical term (by
      simp only [Definition.terms,List.mem_append,List.mem_flatMap]
      exact Or.inr ⟨_,member,present⟩)
    exact .checkedRunsIn found member
      (permutation.substitutes_lexical (invocation _ (by simp [InvocationRelation.terms])) receiver)
      (permutation.substitutes_lexical (invocation _ (by simp [InvocationRelation.terms])) access)
      (permutation.substitutes_lexical_list (fun term present => invocation term (by simp [InvocationRelation.terms,present])) arguments)
      (permutation.substitutes_lexical (invocation _ (by simp [InvocationRelation.terms])) after)
  case assumed_3 member => exact .assumed (List.mem_map.mpr ⟨_,member,rfl⟩)
  case equality _ equal => exact .equality equal
  case outlives included => exact .outlives (included.permute permutation)
  case typeOutlives _ outlives => exact .typeOutlives outlives
  case rows _ subset => exact .rows subset
  case implementation _ selected => exact .implementation selected
  case use capability request => exact .use (capability.permute valid permutation) request
  case quantified binders requirements _ allInstances =>
    apply Entails.quantified
    intro values substitution instantiated kinds requirement member
    change Instantiates (binders.map permutation.binder) values substitution at instantiated
    have originalInstantiation : Instantiates binders (values.map permutation.term) (permutation.substitution substitution) := by
      have inverse : (binders.map permutation.binder).map permutation.binder = binders := by
        simp only [List.map_map,Function.comp_def,permutation.binder_involutive,List.map_id']
      simpa only [inverse] using (instantiated.permute permutation).permute_binders permutation
    have originalKinds : ∀ term ∈ values.map permutation.term, Kinding program context term term.kind := by
      intro term present
      obtain ⟨original,inOriginal,rfl⟩ := List.mem_map.mp present
      simpa only [permutation.context_involutive,permutation.term_kind] using (kinds original inOriginal).permute permutation
    obtain ⟨original,inOriginal,rfl⟩ := List.mem_map.mp member
    have transported := allInstances _ _ originalInstantiation originalKinds original inOriginal
    simpa only [permutation.substitution_involutive,RegionPermutation.constraint,RegionPermutation.term] using transported
  case instantiated substituted _ holds => exact .instantiated (permutation.substitute_constraint substituted) holds
  case nil => exact .nil
  case cons _ _ first rest => exact .cons first rest

theorem Equal.permute {program : Program} (valid : ProgramWellFormed program) {context : Context}
    {a b : Term} (equal : Equal program context a b) (permutation : RegionPermutation) :
    Equal program (permutation.context context) (permutation.term a) (permutation.term b) := by
  have transported := (Entails.equality equal).permute valid permutation
  simp only [RegionPermutation.constraint,Constraint.mapTerms] at transported
  cases transported with
  | assumed member => exact .assumed member
  | equality equal => exact equal

theorem TypeOutlives.permute {program : Program} (valid : ProgramWellFormed program) {context : Context}
    {type region : Term} (outlives : TypeOutlives program context type region) (permutation : RegionPermutation) :
    TypeOutlives program (permutation.context context) (permutation.term type) (permutation.term region) := by
  have transported := (Entails.typeOutlives outlives).permute valid permutation
  simp only [RegionPermutation.constraint,Constraint.mapTerms] at transported
  cases transported with
  | assumed member => exact .assumed member
  | typeOutlives previous => exact previous

theorem RowSubset.permute {program : Program} (valid : ProgramWellFormed program) {context : Context}
    {required allowed : Term} (subset : RowSubset program context required allowed) (permutation : RegionPermutation) :
    RowSubset program (permutation.context context) (permutation.term required) (permutation.term allowed) := by
  have transported := (Entails.rows subset).permute valid permutation
  simp only [RegionPermutation.constraint,Constraint.mapTerms] at transported
  cases transported with
  | assumed member => exact .assumed member
  | rows previous => exact previous

theorem EntailsSubstitution.permute {program : Program} (valid : ProgramWellFormed program) {context : Context}
    {substitution : Substitution} {constraint : Constraint}
    (entailed : EntailsSubstitution program context substitution constraint) (permutation : RegionPermutation) :
    EntailsSubstitution program (permutation.context context) (permutation.substitution substitution)
      (permutation.constraint constraint) := by
  cases entailed with
  | instantiated substituted holds => exact .instantiated (permutation.substitute_constraint substituted) (holds.permute valid permutation)

theorem ConstraintsHold.permute {program : Program} (valid : ProgramWellFormed program) {context : Context}
    {substitution : Substitution} {requirements : List Constraint}
    (held : ConstraintsHold program context substitution requirements)
    (lexical : ∀ constraint ∈ requirements, ∀ term ∈ constraint.terms, term.Lexical)
    (permutation : RegionPermutation) :
    ConstraintsHold program (permutation.context context) (permutation.substitution substitution) requirements := by
  intro constraint member
  obtain ⟨instantiated,substituted,entailed⟩ := held constraint member
  exact ⟨permutation.constraint instantiated,
    permutation.substitute_lexical_constraint (lexical constraint member) substituted,
    entailed.permute valid permutation⟩

theorem RegionPermutation.substitutes_variants (permutation : RegionPermutation) {substitution : Substitution}
    {variants : List VariantDefinition} {types : List (List Term)}
    (related : ListRel (fun variant types => ListRel (Substitutes substitution) (variant.fields.map (·.type)) types) variants types)
    (lexical : ∀ variant ∈ variants, ∀ field ∈ variant.fields, field.type.Lexical) :
    ListRel (fun variant types => ListRel (Substitutes (permutation.substitution substitution)) (variant.fields.map (·.type)) types)
      variants (types.map (List.map permutation.term)) := by
  induction related with
  | nil => exact .nil
  | cons first _ ih =>
      exact .cons (permutation.substitutes_lexical_list (by
        intro term present
        obtain ⟨field,member,rfl⟩ := List.mem_map.mp present
        exact lexical _ List.mem_cons_self field member) first)
        (ih (fun variant member => lexical variant (List.mem_cons_of_mem _ member)))

theorem LayoutOf.permute {program : Program} (valid : ProgramWellFormed program) {context : Context}
    {type : Term} {layout : Layout} (located : LayoutOf program context type layout) (permutation : RegionPermutation) :
    LayoutOf program (permutation.context context) (permutation.term type) layout := by
  refine LayoutOf.rec
    (motive_1 := fun type layout _ => LayoutOf program (permutation.context context) (permutation.term type) layout)
    (motive_2 := fun types layout _ => FieldsHaveLayout program (permutation.context context) (types.map permutation.term) layout)
    (motive_3 := fun type layout _ => CCompatible program (permutation.context context) (permutation.term type) layout)
    (motive_4 := fun types layouts _ => ListRel (LayoutOf program (permutation.context context)) (types.map permutation.term) layouts)
    (motive_5 := fun types layouts _ => ListRel (FieldsHaveLayout program (permutation.context context))
      (types.map (List.map permutation.term)) layouts)
    (motive_6 := fun types layouts _ => ListRel (CCompatible program (permutation.context context)) (types.map permutation.term) layouts)
    ?unit ?scalar ?reference ?pointer ?tuple ?callable ?continuation ?label ?available ?bindings ?environment
    ?array ?nominal ?transparent ?cRepresentation ?alias ?fields ?cScalar ?cPointer ?record ?enumeration
    ?cTransparent ?cAlias ?nil ?cons ?variantNil ?variantCons ?cNil ?cCons located
  all_goals intros
  all_goals simp only [RegionPermutation.term,Term.renameRuntimeRegions,List.map_cons,List.map_nil] <;>
    (try simp only [← RegionPermutation.term_def])
  case unit => exact .unit
  case scalar valid => exact .scalar valid
  case reference => exact .reference
  case pointer => exact .pointer
  case tuple _ aggregate fields => exact .tuple fields aggregate
  case callable selected _ aggregate fields => exact .callable (selected.permute valid permutation) fields aggregate
  case continuation => exact .continuation
  case label => exact .label
  case available => exact .available
  case bindings _ aggregate fields => exact .bindings fields aggregate
  case environment _ aggregate fields => exact .environment fields aggregate
  case array nonnegative bound _ array element => exact .array nonnegative bound element array
  case nominal id data arguments substitution variantTypes variantLayouts layout found representation instantiated substituted _ aggregate bound variants =>
    have lexical := valid.lexical (List.mem_of_find?_eq_some (Program.data_lookup found))
    refine .nominal found representation (instantiated.permute permutation) ?_ variants aggregate bound
    have allowed : ∀ (variant : VariantDefinition), variant ∈ data.variants → ∀ (field : FieldDefinition), field ∈ variant.fields → field.type.Lexical := by
      intro variant member field present
      exact lexical field.type (by
        simp only [Definition.terms,List.mem_append,List.mem_map,List.mem_flatMap]
        exact Or.inl (Or.inl (Or.inl ⟨field,⟨variant,member,present⟩,rfl⟩)))
    exact permutation.substitutes_variants substituted allowed
  case transparent found representation notEnum variants fields instantiated substituted _ selected nonzero others shape layouts =>
    have lexical := valid.lexical (List.mem_of_find?_eq_some (Program.data_lookup found))
    refine .transparent found representation notEnum variants fields (instantiated.permute permutation)
      (permutation.substitutes_lexical_list ?_ substituted) layouts selected nonzero others shape
    intro term member
    obtain ⟨field,present,rfl⟩ := List.mem_map.mp member
    exact lexical field.type (by
      simp only [Definition.terms,List.mem_append,List.mem_map,List.mem_flatMap]
      exact Or.inl (Or.inl (Or.inl ⟨field,⟨_,by simp [variants],fields ▸ present⟩,rfl⟩)))
  case cRepresentation found representation _ compatible =>
    exact .cRepresentation found representation (by
      simpa only [RegionPermutation.term,Term.renameRuntimeRegions] using compatible)
  case alias equal _ original => exact .alias (equal.permute valid permutation) original
  case fields _ aggregate fields => exact .fields fields aggregate
  case cScalar member alignment => exact .scalar member alignment
  case cPointer => exact .pointer
  case record found representation notEnum variants instantiated substituted _ aggregate fields =>
    have lexical := valid.lexical (List.mem_of_find?_eq_some (Program.data_lookup found))
    refine .record found representation notEnum variants (instantiated.permute permutation)
      (permutation.substitutes_lexical_list ?_ substituted) fields aggregate
    intro term member
    obtain ⟨field,present,rfl⟩ := List.mem_map.mp member
    exact lexical field.type (by
      simp only [Definition.terms,List.mem_append,List.mem_map,List.mem_flatMap]
      exact Or.inl (Or.inl (Or.inl ⟨field,⟨_,by simp [variants],present⟩,rfl⟩)))
  case enumeration found instantiated representation enumeration inhabited valid empty bound =>
    exact .enumeration found (instantiated.permute permutation) representation enumeration inhabited valid empty bound
  case cTransparent _ found representation variants instantiated substituted _ selected _ positive size alignment others located fields compatible =>
    have lexical := valid.lexical (List.mem_of_find?_eq_some (Program.data_lookup found))
    refine .transparent (by simpa only [RegionPermutation.term,Term.renameRuntimeRegions] using located)
      found representation variants (instantiated.permute permutation)
      (permutation.substitutes_lexical_list ?_ substituted) fields ?_ compatible positive size alignment others
    · intro term member
      obtain ⟨field,present,rfl⟩ := List.mem_map.mp member
      exact lexical field.type (by
        simp only [Definition.terms,List.mem_append,List.mem_map,List.mem_flatMap]
        exact Or.inl (Or.inl (Or.inl ⟨field,⟨_,by simp [variants],present⟩,rfl⟩)))
    · simp only [List.getElem?_map,selected,Option.map]
  case cAlias equal _ original => exact .alias (equal.permute valid permutation) original
  case nil => exact .nil
  case cons _ _ first rest => exact .cons first rest
  case variantNil => exact .nil
  case variantCons _ _ first rest => exact .cons first rest
  case cNil => exact .nil
  case cCons _ _ first rest => exact .cons first rest

end Glorious.Language
