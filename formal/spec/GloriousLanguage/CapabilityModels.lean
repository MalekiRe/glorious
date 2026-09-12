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

theorem Principal.Restricts.total (first last : Principal) : first.Restricts last ∨ last.Restricts first := by
  cases first <;> cases last <;> simp [Principal.Restricts,Principal.Permits]

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


/-- Selection in the complete logical/coinductive capability interpretation.
Absence remains unknown; a most permissive class must itself have evidence. -/
noncomputable def Principal.greatest (supported : Principal → Prop) : Option Principal := by
  classical
  exact if supported .duplicable then some .duplicable
    else if supported .affine then some .affine
    else if supported .exact then some .exact else none

theorem Principal.greatest_origin {supported : Principal → Prop} {principal : Principal}
    (found : Principal.greatest supported = some principal) : supported principal := by
  classical
  unfold Principal.greatest at found
  split at found
  next supported => cases found; exact supported
  next =>
    split at found
    next supported => cases found; exact supported
    next =>
      split at found
      next supported => cases found; exact supported
      next => cases found

theorem Principal.greatest_upper {supported : Principal → Prop} {principal : Principal}
    (evidence : supported principal) :
    ∃ selected, Principal.greatest supported = some selected ∧ principal.Restricts selected := by
  classical
  unfold Principal.greatest
  split
  next => exact ⟨_,rfl,by intro n _; trivial⟩
  next noCopy =>
    split
    next =>
      refine ⟨_,rfl,?_⟩
      cases principal with
      | duplicable => exact False.elim (noCopy evidence)
      | affine => exact .refl _
      | exact => intro n one; simpa [Principal.Permits] using Nat.le_of_eq one
    next noDrop =>
      split
      next =>
        refine ⟨_,rfl,?_⟩
        cases principal with
        | duplicable => exact False.elim (noCopy evidence)
        | affine => exact False.elim (noDrop evidence)
        | exact => exact .refl _
      next noExact => cases principal <;> contradiction

theorem Principal.greatest_spec {supported : Principal → Prop} {principal : Principal} :
    Principal.greatest supported = some principal ↔
      supported principal ∧ ∀ other, supported other → other.Restricts principal := by
  constructor
  · intro found
    refine ⟨Principal.greatest_origin found,?_⟩
    intro other evidence
    obtain ⟨selected,chosen,ordered⟩ := Principal.greatest_upper evidence
    exact Option.some.inj (chosen.symm.trans found) ▸ ordered
  · rintro ⟨evidence,maximum⟩
    obtain ⟨selected,found,ordered⟩ := Principal.greatest_upper evidence
    have same := ordered.antisymm (maximum selected (Principal.greatest_origin found))
    exact same.symm ▸ found


/-- A proposed recursive family is checked against the actual local
equations or already derived logical leaves. All leaves are finite positive
evidence; no assumed output capability or normalization oracle enters. -/
theorem CapabilityEvidence.coinduction {program : Program} {context : Context}
    {assignment : Term → Option Principal} {type : Term} {principal : Principal}
    (found : assignment type = some principal)
    (supported : ∀ term claimed, assignment term = some claimed → ∃ result,
      claimed.Restricts result ∧
        (CapabilityEquation program assignment term result ∨ CapabilityEvidence program context term result)) :
    CapabilityEvidence program context type principal := by
  apply CapabilityEvidence.structural found
  intro term claimed selected
  obtain ⟨result,ordered,equation | evidence⟩ := supported term claimed selected
  · exact .equation ordered equation
  · exact .evidence ordered evidence


theorem CapabilityEvidence.restrict {program : Program} {context : Context} {type : Term} {first last : Principal}
    (evidence : CapabilityEvidence program context type last) (restriction : first.Restricts last) :
    CapabilityEvidence program context type first := by
  classical
  apply CapabilityEvidence.structural (assignment := fun term => if term = type then some first else none)
    (by simp)
  intro term principal found
  by_cases same : term = type
  · subst term
    have equal : first = principal := by simpa using found
    subst principal
    exact .evidence restriction evidence
  · simp [same] at found

/-- Finite composition is a consequence of the same coinductive producer.
The local equation may mention the parent recursively; enlarging that one
proposal entry uses monotonicity, while every other dependency is supplied
by actual prior evidence. No second structural type walk is needed. -/
theorem CapabilityEquation.realize {program : Program} {context : Context}
    {assignment : Term → Option Principal} {type : Term} {principal : Principal}
    (equation : CapabilityEquation program assignment type principal)
    (leaves : ∀ term claimed, assignment term = some claimed → CapabilityEvidence program context term claimed) :
    CapabilityEvidence program context type principal := by
  classical
  by_cases prior : ∃ selected, assignment type = some selected ∧ principal.Restricts selected
  · obtain ⟨selected,found,ordered⟩ := prior
    exact (leaves _ _ found).restrict ordered
  · let extended : Term → Option Principal := fun term => if term = type then some principal else assignment term
    have grows : CapabilityRefines assignment extended := by
      intro term claimed found
      by_cases same : term = type
      · subst term
        refine ⟨principal,by simp [extended],?_⟩
        rcases Principal.Restricts.total claimed principal with ordered | ordered
        · exact ordered
        · exact False.elim (prior ⟨claimed,found,ordered⟩)
      · exact ⟨claimed,by simpa [extended,same] using found,.refl _⟩
    obtain ⟨supported,unfolded,ordered⟩ := equation.monotone grows
    apply CapabilityEvidence.structural (assignment := extended) (by simp [extended])
    intro term claimed found
    by_cases same : term = type
    · subst term
      have same : principal = claimed := by simpa [extended] using found
      subst claimed
      exact .equation ordered unfolded
    · exact .evidence (.refl _) (leaves term claimed (by simpa [extended,same] using found))

theorem CapabilityEvidence.support {program : Program} {context : Context} {type : Term} {principal : Principal}
    (evidence : CapabilityEvidence program context type principal) (closed : context.assumptions = []) :
    CapabilitySupport program type principal := ⟨context,closed,evidence⟩

theorem PrincipalOf.functional {program : Program} {type : Term} {first last : Principal}
    (left : PrincipalOf program type first) (right : PrincipalOf program type last) : first = last :=
  (right.2 _ left.1).antisymm (left.2 _ right.1)

/-- The greatest complete interpretation is selected from finite logical
certificates with coinductive structural components, not from raw syntax. -/
noncomputable def greatestCapabilities (program : Program) (type : Term) : Option Principal :=
  Principal.greatest (CapabilitySupport program type)

theorem greatestCapabilities_spec {program : Program} {type : Term} {principal : Principal} :
    greatestCapabilities program type = some principal ↔ PrincipalOf program type principal :=
  Principal.greatest_spec

noncomputable def CapabilityModel.canonical (program : Program) : CapabilityModel program where
  principal := greatestCapabilities program
  equations _ _ := greatestCapabilities_spec

theorem CapabilityModel.exists (program : Program) : Nonempty (CapabilityModel program) := ⟨.canonical program⟩

theorem CapabilityModel.principal_unique {program : Program} (first last : CapabilityModel program) :
    first.principal = last.principal := by
  funext type
  cases found : first.principal type with
  | none =>
    cases chosen : last.principal type with
    | none => rfl
    | some principal =>
      have same := (first.equations type principal).mpr ((last.equations type principal).mp chosen)
      simp [found] at same
  | some principal =>
    exact ((last.equations type principal).mpr ((first.equations type principal).mp found)).symm

theorem principalOf_canonical {program : Program} {type : Term} {principal : Principal} :
    PrincipalOf program type principal ↔ (CapabilityModel.canonical program).principal type = some principal :=
  greatestCapabilities_spec.symm

theorem CapabilitySupport.principal {program : Program} {type : Term} {principal : Principal}
    (supported : CapabilitySupport program type principal) :
    ∃ selected, PrincipalOf program type selected ∧ principal.Restricts selected := by
  obtain ⟨selected,found,ordered⟩ := Principal.greatest_upper supported
  exact ⟨selected,greatestCapabilities_spec.mp found,ordered⟩

theorem CapabilitySupport.mayDiscard {program : Program} {type : Term} {principal : Principal}
    (supported : CapabilitySupport program type principal) (discard : principal.MayDiscard) :
    ∃ selected, PrincipalOf program type selected ∧ selected.MayDiscard := by
  obtain ⟨selected,capability,ordered⟩ := supported.principal
  exact ⟨selected,capability,ordered 0 discard⟩

/-- A recursive proposal is dominated by the canonical semantic model when
each entry unfolds through the actual equations or finite logical evidence.
It requires no separate syntax-only fixed point or assumed model. -/
theorem CapabilityModel.coinduction {program : Program} {context : Context}
    {assignment : Term → Option Principal} (closed : context.assumptions = [])
    (supported : ∀ type principal, assignment type = some principal →
      CapabilityUnfolds program context assignment type principal) :
    CapabilityRefines assignment (CapabilityModel.canonical program).principal := by
  intro type principal found
  obtain ⟨selected,capability,ordered⟩ := (CapabilityEvidence.structural found supported).support closed |>.principal
  exact ⟨selected,principalOf_canonical.mp capability,ordered⟩

theorem CapabilitySupport.duplicable {program : Program} {type : Term}
    (supported : CapabilitySupport program type .duplicable) : PrincipalOf program type .duplicable :=
  ⟨supported,fun _ _ _ _ => trivial⟩

/-- A local equation without recursive dependencies supplies its evidence
through the same composition theorem as every recursive constructor. -/
theorem CapabilityEquation.closedEvidence {program : Program} {context : Context}
    {type : Term} {principal : Principal}
    (equation : CapabilityEquation program (fun _ => none) type principal) :
    CapabilityEvidence program context type principal :=
  equation.realize (fun _ _ found => nomatch found)

theorem PrincipalOf.unit (program : Program) : PrincipalOf program .unit .duplicable :=
  (CapabilityEquation.unit.closedEvidence (program := program) (context := { module := default })).support rfl |>.duplicable

theorem PrincipalOf.shared (program : Program) (region type : Term) :
    PrincipalOf program (.reference .shared region type) .duplicable :=
  (CapabilityEquation.shared.closedEvidence (program := program) (context := { module := default })).support rfl |>.duplicable

/-- The handle's discard permission is unconditional. Claiming its precise
canonical class also requires excluding contradictory type equalities; that
stronger rigidity theorem is not smuggled into this producer. -/
theorem PrincipalOf.unique_reference_discardable (program : Program) (region type : Term) :
    ∃ principal, PrincipalOf program (.reference .unique region type) principal ∧ principal.MayDiscard :=
  ((CapabilityEquation.unique.closedEvidence (program := program) (context := { module := default })).support rfl).mayDiscard
    (by simp [Principal.MayDiscard,Principal.Permits])

theorem CapabilityEvidence.definitionallyEqual {program : Program} {context : Context}
    {left right : Term} {principal : Principal} (evidence : CapabilityEvidence program context left principal)
    (equal : DefinitionallyEqual program context left right) : CapabilityEvidence program context right principal :=
  .equal (.definitional equal) evidence

/-- Actual alias or associated-item expansion transports permission back to
the source type. Selection, generic domains and the substituted body all come
from the existing positive expansion judgment, not a second normalizer. -/
theorem DefinitionalStep.capability {program : Program} {context : Context} {left right : Term} {principal : Principal}
    (step : DefinitionalStep program context left right) (evidence : CapabilityEvidence program context right principal) :
    CapabilityEvidence program context left principal :=
  evidence.definitionallyEqual (.symm (.step step))

theorem DefinitionalStep.closed_capability {program : Program} {context : Context}
    {left right : Term} {principal : Principal} (closed : context.assumptions = [])
    (step : DefinitionalStep program context left right) (capability : CapabilityEvidence program context right principal) :
    ∃ selected, PrincipalOf program left selected ∧ principal.Restricts selected :=
  (step.capability capability).support closed |>.principal

/-- Exact-once is the least requested class only when the interval actually
requests no other count. A bound never silently identifies a principal. -/
theorem Quantity.minimal_request {quantity : Quantity} (valid : quantity.Valid) :
    ∃ principal, quantity.Request principal ∧
      ∀ permitted, quantity.Request permitted → principal.Restricts permitted := by
  classical
  by_cases exactRequest : quantity.Request .exact
  · refine ⟨.exact,exactRequest,?_⟩
    intro permitted _ n one
    have one : n = 1 := one
    rw [one]
    exact Principal.once_does_not_identify_principal permitted
  · by_cases affineRequest : quantity.Request .affine
    · refine ⟨.affine,affineRequest,?_⟩
      intro permitted request
      cases permitted with
      | duplicable => intro _ _; trivial
      | affine => exact .refl _
      | exact => exact False.elim (exactRequest request)
    · refine ⟨.duplicable,⟨valid,by intro _ _; trivial⟩,?_⟩
      intro permitted request
      cases permitted with
      | duplicable => exact .refl _
      | affine => exact False.elim (affineRequest request)
      | exact => exact False.elim (exactRequest request)

theorem Quantity.Request.mono {quantity : Quantity} {first last : Principal}
    (request : quantity.Request first) (ordered : first.Restricts last) : quantity.Request last :=
  ⟨request.1,fun n contained => ordered n (request.2 n contained)⟩

theorem CapabilityEvidence.entails {program : Program} {context : Context} {type : Term} {principal : Principal}
    (evidence : CapabilityEvidence program context type principal) :
    Entails program context (.use type principal.quantity) :=
  .use evidence ((principal.quantity_request principal).mpr (.refl _))

theorem Entails.capabilityEvidence {program : Program} {context : Context} {type : Term} {principal : Principal}
    (entailed : Entails program context (.use type principal.quantity)) :
    CapabilityEvidence program context type principal :=
  .logical entailed principal.quantity_valid (fun other requested => (principal.quantity_request other).mp requested)

/-- Closed, admitted Use evidence publishes the greatest actual semantic
answer. This includes congruence and quantified evidence without pretending
that their types are already raw structural forms. Structural inversion of
that answer is a separate correctness theorem, not an admission assumption. -/
theorem Entails.valid_use_principal {program : Program} {context : Context} {type : Term} {quantity : Quantity}
    (closed : context.assumptions = []) (valid : quantity.Valid)
    (entailed : Entails program context (.use type quantity)) :
    ∃ principal, PrincipalOf program type principal ∧ quantity.Request principal := by
  obtain ⟨least,request,minimal⟩ := Quantity.minimal_request valid
  obtain ⟨principal,selected,ordered⟩ := (CapabilityEvidence.logical entailed valid minimal).support closed |>.principal
  exact ⟨principal,selected,request.mono ordered⟩

end Glorious.Language
