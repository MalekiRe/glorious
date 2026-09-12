import GloriousLanguage.Static

/-! Constructibility of the authoritative recursive capability equations.
The proof completes their greatest semantic solution; it does not introduce
a second type traversal or assume that a capability model already exists. -/
namespace Glorious.Language

theorem Principal.Restricts.refl (principal : Principal) : principal.Restricts principal := fun _ permitted => permitted

theorem Principal.Restricts.trans {first middle last : Principal}
    (left : first.Restricts middle) (right : middle.Restricts last) : first.Restricts last :=
  fun n permitted => right n (left n permitted)

theorem Principal.Restricts.antisymm {first last : Principal}
    (left : first.Restricts last) (right : last.Restricts first) : first = last := by
  have zeroLeft := left 0
  have zeroRight := right 0
  have twoLeft := left 2
  have twoRight := right 2
  cases first <;> cases last <;> simp_all [Principal.Permits]

theorem Principal.meet_monotone {first second last final : Principal}
    (left : first.Restricts last) (right : second.Restricts final) :
    (first.meet second).Restricts (last.meet final) := by
  intro n permitted
  obtain ⟨a,b⟩ := (Principal.meet_permits _ _ _).mp permitted
  exact (Principal.meet_permits _ _ _).mpr ⟨left n a,right n b⟩

theorem Principal.fields_monotone {first last : List Principal}
    (related : ListRel Principal.Restricts first last) : (Principal.fields first).Restricts (Principal.fields last) := by
  induction related with
  | nil => exact .refl _
  | cons first _ ih => exact Principal.meet_monotone first ih

/-- Pointwise order is permission inclusion. Missing information is bottom,
not an unsupported grant of Copy or Drop. -/
def CapabilityRefines (first last : Term → Option Principal) : Prop :=
  ∀ term principal, first term = some principal →
    ∃ selected, last term = some selected ∧ principal.Restricts selected

theorem CapabilityRefines.refl (assignment : Term → Option Principal) : CapabilityRefines assignment assignment :=
  fun _ principal found => ⟨principal,found,.refl _⟩

theorem CapabilityRefines.trans {first middle last : Term → Option Principal}
    (left : CapabilityRefines first middle) (right : CapabilityRefines middle last) : CapabilityRefines first last := by
  intro term principal found
  obtain ⟨next,selected,le⟩ := left term principal found
  obtain ⟨result,selected,last⟩ := right term next selected
  exact ⟨result,selected,le.trans last⟩

theorem CapabilityRefines.antisymm {first last : Term → Option Principal}
    (left : CapabilityRefines first last) (right : CapabilityRefines last first) : first = last := by
  funext term
  cases original : first term with
  | none =>
    cases selected : last term with
    | none => rfl
    | some value => obtain ⟨_,found,_⟩ := right term value selected; simp [original] at found
  | some value =>
    obtain ⟨changed,selected,forward⟩ := left term value original
    obtain ⟨back,found,reverse⟩ := right term changed selected
    have same : back = value := Option.some.inj (found.symm.trans original)
    subst back
    exact (congrArg some (forward.antisymm reverse)).trans selected.symm

theorem CapabilityRefines.fields {first last : Term → Option Principal}
    (related : CapabilityRefines first last) {fields : List Term} {principals : List Principal}
    (typed : ListRel (fun field principal => first field = some principal) fields principals) :
    ∃ results, ListRel (fun field principal => last field = some principal) fields results ∧
      ListRel Principal.Restricts principals results := by
  induction typed with
  | nil => exact ⟨[],.nil,.nil⟩
  | @cons field principal fields principals found rest ih =>
    obtain ⟨result,selected,le⟩ := related field principal found
    obtain ⟨results,fields,ordered⟩ := ih
    exact ⟨result :: results,.cons selected fields,.cons le ordered⟩

private theorem marker_monotone {first last : Term → Option Principal}
    (related : CapabilityRefines first last) {data : DataDefinition} {substitution : Substitution} {marker : Principal}
    (marked : data.quantitySource = none ∧ marker = .duplicable ∨
      ∃ source value, data.quantitySource = some source ∧ Substitutes substitution source value ∧
        (value = .principal marker ∨ value.kind = .type ∧ first value = some marker)) :
    ∃ changed, (data.quantitySource = none ∧ changed = .duplicable ∨
      ∃ source value, data.quantitySource = some source ∧ Substitutes substitution source value ∧
        (value = .principal changed ∨ value.kind = .type ∧ last value = some changed)) ∧ marker.Restricts changed := by
  rcases marked with ⟨none,rfl⟩ | ⟨source,value,sourceAt,substituted,marked⟩
  · exact ⟨.duplicable,Or.inl ⟨none,rfl⟩,.refl _⟩
  · rcases marked with literal | ⟨kind,found⟩
    · exact ⟨marker,Or.inr ⟨source,value,sourceAt,substituted,Or.inl literal⟩,.refl _⟩
    · obtain ⟨changed,selected,le⟩ := related value marker found
      exact ⟨changed,Or.inr ⟨source,value,sourceAt,substituted,Or.inr ⟨kind,selected⟩⟩,le⟩

/-- Stronger input capabilities cannot revoke a previously justified output.
Explicit restrictions and destructor obligations use the same permission
order, including recursive nominal and quantity-source dependencies. -/
theorem CapabilityEquation.monotone {program : Program} {first last : Term → Option Principal}
    (related : CapabilityRefines first last) {term : Term} {principal : Principal}
    (equation : CapabilityEquation program first term principal) :
    ∃ result, CapabilityEquation program last term result ∧ principal.Restricts result := by
  cases equation with
  | unit => exact ⟨_,.unit,.refl _⟩
  | bottom => exact ⟨_,.bottom,.refl _⟩
  | scalar => exact ⟨_,.scalar,.refl _⟩
  | raw => exact ⟨_,.raw,.refl _⟩
  | shared => exact ⟨_,.shared,.refl _⟩
  | unique => exact ⟨_,.unique,.refl _⟩
  | label => exact ⟨_,.label,.refl _⟩
  | tuple fields =>
    obtain ⟨_,results,ordered⟩ := related.fields fields
    exact ⟨_,.tuple results,Principal.fields_monotone ordered⟩
  | emptyArray => exact ⟨_,.emptyArray,.refl _⟩
  | array positive found =>
    obtain ⟨result,selected,le⟩ := related _ _ found
    exact ⟨result,.array positive selected,le⟩
  | alias found instantiated substituted selected =>
    obtain ⟨result,selected,le⟩ := related _ _ selected
    exact ⟨result,.alias found instantiated substituted selected,le⟩
  | nominal found instantiated substituted capabilities marked meets restricted drops =>
    obtain ⟨results,fields,ordered⟩ := related.fields capabilities
    obtain ⟨marker,marked,markerOrder⟩ := marker_monotone related marked
    have structural := Principal.meet_monotone (Principal.fields_monotone ordered) markerOrder
    rw [← meets] at structural
    rcases restricted with ⟨none,rfl⟩ | ⟨restriction,permitted⟩
    · refine ⟨_,.nominal found instantiated substituted fields marked rfl (Or.inl ⟨none,rfl⟩) ?_,structural⟩
      intro drop
      exact structural 0 (drops drop)
    · exact ⟨_,.nominal found instantiated substituted fields marked rfl
        (Or.inr ⟨restriction,permitted.trans structural⟩) drops,.refl _⟩
  | callable fields capabilities =>
    obtain ⟨_,results,ordered⟩ := related.fields capabilities
    exact ⟨_,.callable fields results,Principal.fields_monotone ordered⟩
  | environment capabilities =>
    obtain ⟨_,results,ordered⟩ := related.fields capabilities
    exact ⟨_,.environment results,Principal.fields_monotone ordered⟩
  | available found =>
    obtain ⟨result,selected,le⟩ := related _ _ found
    exact ⟨result,.available selected,le⟩
  | bindings capabilities =>
    obtain ⟨_,results,ordered⟩ := related.fields capabilities
    exact ⟨_,.bindings results,Principal.fields_monotone ordered⟩
  | optionalContinuation => exact ⟨_,.optionalContinuation,.refl _⟩
  | exactContinuation positive => exact ⟨_,.exactContinuation positive,.refl _⟩

private theorem substitutions_unique {substitution : Substitution} {source : List Term} {first last : List Term}
    (left : ListRel (Substitutes substitution) source first) (right : ListRel (Substitutes substitution) source last) :
    first = last := ListRel.functional (fun _ _ _ left right => left.2.1.trans right.2.1.symm) left right

private theorem assigned_unique {assignment : Term → Option Principal} {source : List Term} {first last : List Principal}
    (left : ListRel (fun term principal => assignment term = some principal) source first)
    (right : ListRel (fun term principal => assignment term = some principal) source last) :
    first = last := ListRel.functional (fun _ _ _ left right => Option.some.inj (left.symm.trans right)) left right

private theorem callable_fields_unique {program : Program} {id : DeclId} {arguments first last : List Term}
    (left : CallableFields program id arguments first) (right : CallableFields program id arguments last) : first = last := by
  cases left with
  | function selected instantiated fields =>
    cases right with
    | function found specialized residents =>
      have same := Option.some.inj (found.symm.trans selected)
      subst same
      have same := specialized.2.2.trans instantiated.2.2.symm
      subst same
      exact substitutions_unique fields residents
    | operation found _ =>
      unfold Program.function at selected
      unfold Program.operation at found
      cases lookup : program.lookup id with
      | none => simp [lookup] at selected
      | some definition => cases definition <;> simp_all
  | operation selected _ =>
    cases right with
    | operation => rfl
    | function found _ _ =>
      unfold Program.function at found
      unfold Program.operation at selected
      cases lookup : program.lookup id with
      | none => simp [lookup] at selected
      | some definition => cases definition <;> simp_all

private theorem marker_unique {assignment : Term → Option Principal}
    {data : DataDefinition} {substitution : Substitution} {first last : Principal}
    (left : data.quantitySource = none ∧ first = .duplicable ∨
      ∃ source value, data.quantitySource = some source ∧ Substitutes substitution source value ∧
        (value = .principal first ∨ value.kind = .type ∧ assignment value = some first))
    (right : data.quantitySource = none ∧ last = .duplicable ∨
      ∃ source value, data.quantitySource = some source ∧ Substitutes substitution source value ∧
        (value = .principal last ∨ value.kind = .type ∧ assignment value = some last)) : first = last := by
  rcases left with ⟨none,rfl⟩ | ⟨source,value,selected,substituted,marked⟩
  · rcases right with ⟨_,rfl⟩ | ⟨_,_,some,_,_⟩
    · rfl
    · simp [none] at some
  · rcases right with ⟨none,_⟩ | ⟨other,changed,found,specialized,otherMarker⟩
    · simp [none] at selected
    · have same := Option.some.inj (found.symm.trans selected)
      subst other
      have same := specialized.2.1.trans substituted.2.1.symm
      subst changed
      rcases marked with literal | ⟨kind,found⟩
      · rcases otherMarker with otherLiteral | ⟨otherKind,_⟩
        · exact Term.principal.inj (literal.symm.trans otherLiteral)
        · simp [literal,Term.kind] at otherKind
      · rcases otherMarker with otherLiteral | ⟨_,selected⟩
        · simp [otherLiteral,Term.kind] at kind
        · exact Option.some.inj (found.symm.trans selected)

/-- Even malformed declaration lists cannot yield two principals: each
declaration kind is selected through the same Program.lookup, and all
instantiations use the single checked substitution graph. -/
theorem CapabilityEquation.functional {program : Program} {assignment : Term → Option Principal}
    {term : Term} {first last : Principal}
    (left : CapabilityEquation program assignment term first)
    (right : CapabilityEquation program assignment term last) : first = last := by
  cases left with
  | unit => cases right; rfl
  | bottom => cases right; rfl
  | scalar => cases right; rfl
  | raw => cases right; rfl
  | shared => cases right; rfl
  | unique => cases right; rfl
  | label => cases right; rfl
  | tuple fields =>
    cases right with
    | tuple other => exact congrArg Principal.fields (assigned_unique fields other)
  | emptyArray =>
    cases right with
    | emptyArray => rfl
    | array positive _ => omega
  | array positive selected =>
    cases right with
    | emptyArray => omega
    | array _ found => exact Option.some.inj (selected.symm.trans found)
  | alias selected instantiated substituted found =>
    cases right with
    | alias selected2 instantiated2 substituted2 found2 =>
      have same := Option.some.inj (selected2.symm.trans selected)
      subst same
      have same := instantiated2.2.2.trans instantiated.2.2.symm
      subst same
      have same := substituted2.2.1.trans substituted.2.1.symm
      subst same
      exact Option.some.inj (found.symm.trans found2)
  | nominal selected instantiated substituted capabilities marked meets restricted _ =>
    cases right with
    | nominal selected2 instantiated2 substituted2 capabilities2 marked2 meets2 restricted2 _ =>
      have same := Option.some.inj (selected2.symm.trans selected)
      subst same
      have same := instantiated2.2.2.trans instantiated.2.2.symm
      subst same
      have same := substitutions_unique substituted2 substituted
      subst same
      have same := assigned_unique capabilities2 capabilities
      subst same
      have same := marker_unique marked2 marked
      subst same
      have same := meets2.trans meets.symm
      subst same
      rcases restricted with ⟨none,rfl⟩ | ⟨some,_⟩
      · rcases restricted2 with ⟨_,rfl⟩ | ⟨some,_⟩
        · rfl
        · simp [none] at some
      · rcases restricted2 with ⟨none,_⟩ | ⟨other,_⟩
        · simp [none] at some
        · exact Option.some.inj (some.symm.trans other)
  | callable fields capabilities =>
    cases right with
    | callable otherFields otherCapabilities =>
      have same := callable_fields_unique otherFields fields
      subst same
      exact congrArg Principal.fields (assigned_unique capabilities otherCapabilities)
  | environment capabilities =>
    cases right with
    | environment other => exact congrArg Principal.fields (assigned_unique capabilities other)
  | available selected =>
    cases right with
    | available found => exact Option.some.inj (selected.symm.trans found)
  | bindings capabilities =>
    cases right with
    | bindings other => exact congrArg Principal.fields (assigned_unique capabilities other)
  | optionalContinuation =>
    cases right with
    | optionalContinuation => rfl
  | exactContinuation positive =>
    cases right with
    | exactContinuation => rfl

/-- Proof-level selection from the existing equation relation. There is no
independent reconstruction of a type's capability dependencies. -/
noncomputable def capabilityOperator (program : Program) (assignment : Term → Option Principal)
    (term : Term) : Option Principal := by
  classical
  exact if supported : ∃ principal, CapabilityEquation program assignment term principal
    then some supported.choose else none

theorem capabilityOperator_spec {program : Program} {assignment : Term → Option Principal}
    {term : Term} {principal : Principal} :
    capabilityOperator program assignment term = some principal ↔ CapabilityEquation program assignment term principal := by
  classical
  unfold capabilityOperator
  split
  next supported =>
    constructor
    · intro same
      exact (Option.some.inj same) ▸ supported.choose_spec
    · intro equation
      exact congrArg some (supported.choose_spec.functional equation)
  next absent =>
    constructor
    · intro impossible; cases impossible
    · intro equation; exact False.elim (absent ⟨principal,equation⟩)

theorem capabilityOperator_monotone {program : Program} {first last : Term → Option Principal}
    (related : CapabilityRefines first last) :
    CapabilityRefines (capabilityOperator program first) (capabilityOperator program last) := by
  intro term principal found
  obtain ⟨result,equation,order⟩ := (capabilityOperator_spec.mp found).monotone related
  exact ⟨result,capabilityOperator_spec.mpr equation,order⟩

private def capabilityPostfixed (program : Program) (assignment : Term → Option Principal) : Prop :=
  CapabilityRefines assignment (capabilityOperator program assignment)

private def capabilityCandidate (program : Program) (term : Term) (principal : Principal) : Prop :=
  ∃ assignment, capabilityPostfixed program assignment ∧ assignment term = some principal

/-- The principal order is the finite chain exact ≤ affine ≤ duplicable.
Taking the greatest supported point over all post-fixed assignments therefore
requires no finiteness assumption on recursive types or generic instances. -/
noncomputable def greatestCapabilities (program : Program) (term : Term) : Option Principal := by
  classical
  exact if capabilityCandidate program term .duplicable then some .duplicable
    else if capabilityCandidate program term .affine then some .affine
    else if capabilityCandidate program term .exact then some .exact else none

private theorem greatestCapabilities_origin {program : Program} {term : Term} {principal : Principal}
    (found : greatestCapabilities program term = some principal) : capabilityCandidate program term principal := by
  classical
  unfold greatestCapabilities at found
  split at found
  next supported => cases found; exact supported
  next =>
    split at found
    next supported => cases found; exact supported
    next =>
      split at found
      next supported => cases found; exact supported
      next => cases found

private theorem greatestCapabilities_upper {program : Program} {term : Term} {principal : Principal}
    (supported : capabilityCandidate program term principal) :
    ∃ selected, greatestCapabilities program term = some selected ∧ principal.Restricts selected := by
  classical
  unfold greatestCapabilities
  split
  next => exact ⟨_,rfl,by intro n _; trivial⟩
  next noCopy =>
    split
    next =>
      refine ⟨_,rfl,?_⟩
      cases principal with
      | duplicable => exact False.elim (noCopy supported)
      | affine => exact .refl _
      | exact => intro n one; simpa [Principal.Permits] using Nat.le_of_eq one
    next noDrop =>
      split
      next =>
        refine ⟨_,rfl,?_⟩
        cases principal with
        | duplicable => exact False.elim (noCopy supported)
        | affine => exact False.elim (noDrop supported)
        | exact => exact .refl _
      next noExact => cases principal <;> contradiction

private theorem greatestCapabilities_greatest {program : Program} {assignment : Term → Option Principal}
    (supported : capabilityPostfixed program assignment) : CapabilityRefines assignment (greatestCapabilities program) :=
  fun _ _ found => greatestCapabilities_upper ⟨assignment,supported,found⟩

private theorem greatestCapabilities_postfixed (program : Program) :
    capabilityPostfixed program (greatestCapabilities program) := by
  intro term principal found
  obtain ⟨assignment,supported,selected⟩ := greatestCapabilities_origin found
  obtain ⟨result,unfolded,first⟩ := supported term principal selected
  obtain ⟨final,unfolded,last⟩ := capabilityOperator_monotone (greatestCapabilities_greatest supported) term result unfolded
  exact ⟨final,unfolded,first.trans last⟩

theorem greatestCapabilities_fixed (program : Program) :
    greatestCapabilities program = capabilityOperator program (greatestCapabilities program) := by
  have below := greatestCapabilities_postfixed program
  have next : capabilityPostfixed program (capabilityOperator program (greatestCapabilities program)) :=
    capabilityOperator_monotone below
  exact below.antisymm (greatestCapabilities_greatest next)

/-- A greatest recursive capability model is constructible for every program.
Unsupported equations still yield None, rather than a granted permission. -/
noncomputable def CapabilityModel.canonical (program : Program) : CapabilityModel program where
  principal := greatestCapabilities program
  equations term principal := by
    constructor
    · intro selected
      apply capabilityOperator_spec.mp
      rw [← greatestCapabilities_fixed program]
      exact selected
    · intro equation
      have selected := capabilityOperator_spec.mpr equation
      rw [← greatestCapabilities_fixed program] at selected
      exact selected
  greatest other solution term result selected := by
    apply greatestCapabilities_greatest (assignment := other) ?_ term result selected
    intro term principal found
    exact ⟨principal,capabilityOperator_spec.mpr ((solution term principal).mp found),.refl _⟩

theorem CapabilityModel.exists (program : Program) : Nonempty (CapabilityModel program) := ⟨.canonical program⟩

/-- General coinduction admits a recursive proposal only when each of its
answers is justified by the actual local equations. The conclusion is an
answer of the constructed greatest model, not an assumed recursive solution. -/
theorem CapabilityModel.coinduction {program : Program} {assignment : Term → Option Principal}
    (supported : ∀ term principal, assignment term = some principal →
      ∃ selected, CapabilityEquation program assignment term selected ∧ principal.Restricts selected) :
    CapabilityRefines assignment (CapabilityModel.canonical program).principal := by
  apply greatestCapabilities_greatest
  intro term principal found
  obtain ⟨selected,equation,ordered⟩ := supported term principal found
  exact ⟨selected,capabilityOperator_spec.mpr equation,ordered⟩

theorem CapabilityModel.principal_unique {program : Program} (first last : CapabilityModel program) :
    first.principal = last.principal :=
  CapabilityRefines.antisymm
    (fun term result found => last.greatest first.principal first.equations term result found)
    (fun term result found => first.greatest last.principal last.equations term result found)

/-- The pre-existing existential semantic judgment selects exactly the
constructed greatest solution; the model is consumed by static admission. -/
theorem principalOf_canonical {program : Program} {term : Term} {principal : Principal} :
    PrincipalOf program term principal ↔ (CapabilityModel.canonical program).principal term = some principal := by
  constructor
  · rintro ⟨model,found⟩
    simpa only [model.principal_unique (.canonical program)] using found
  · intro found
    exact ⟨.canonical program,found⟩

theorem principalOf_equation {program : Program} {term : Term} {principal : Principal} :
    PrincipalOf program term principal ↔ CapabilityEquation program (greatestCapabilities program) term principal :=
  principalOf_canonical.trans ((CapabilityModel.canonical program).equations term principal)

theorem PrincipalOf.unit (program : Program) : PrincipalOf program .unit .duplicable :=
  ⟨.canonical program,((CapabilityModel.canonical program).equations _ _).mpr .unit⟩

theorem PrincipalOf.shared (program : Program) (region type : Term) :
    PrincipalOf program (.reference .shared region type) .duplicable :=
  ⟨.canonical program,((CapabilityModel.canonical program).equations _ _).mpr .shared⟩

theorem PrincipalOf.unique (program : Program) (region type : Term) :
    PrincipalOf program (.reference .unique region type) .affine :=
  ⟨.canonical program,((CapabilityModel.canonical program).equations _ _).mpr .unique⟩

end Glorious.Language
