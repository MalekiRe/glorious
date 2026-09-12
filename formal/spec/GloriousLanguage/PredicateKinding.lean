import GloriousLanguage.SubstitutionKinding
import GloriousLanguage.PredicateHygiene

/-! Kinding follows lexical parameter support. In particular, a fresh predicate
binder may shadow an unused caller identity without invalidating an inserted
term; no global uniqueness assumption is imposed on unrelated contexts. -/
namespace Glorious.Language


theorem Kinding.renameParameters {program : Program} {source target : Context} {term : Term} {kind : Kind}
    (kinded : Kinding program source term kind) (rename : Identity → Identity)
    (parameters : ∀ id parameterKind, Occurs (.parameter id parameterKind) term →
      Kinding program target (.parameter (rename id) parameterKind) parameterKind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands) :
    Kinding program target (term.renameParameters rename) kind := by
  apply kinded.map_parameters (Term.renameParameters rename)
    (by intro term; cases term <;> simp only [Term.renameParameters,Term.mapChildren])
    _ levels regions brands
  simpa only [Term.renameParameters] using parameters

theorem Kinding.context_transport {program : Program} {source target : Context} {term : Term} {kind : Kind}
    (kinded : Kinding program source term kind)
    (parameters : ∀ id parameterKind, Occurs (.parameter id parameterKind) term →
      Kinding program target (.parameter id parameterKind) parameterKind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands) :
    Kinding program target term kind :=
  kinded.map_parameters id (by
    intro term
    cases term <;> simp only [id,Term.mapChildren,List.map_id]) parameters levels regions brands

theorem Kinding.bindParameters {program : Program} {context : Context} {term : Term} {kind : Kind}
    (kinded : Kinding program context term kind) (binders : List Binder)
    (fresh : ∀ binder ∈ binders, binder.id ∉ term.parameterIds) :
    Kinding program (context.bindParameters binders) term kind := by
  apply kinded.context_transport (target := context.bindParameters binders)
    _ (Nat.le_refl _) (fun _ member => member) (fun _ member => member)
  intro id parameterKind occurs
  obtain ⟨binder,member,sameId,sameKind⟩ := kinded.parameter_occurs occurs
  have retained : binder ∈ (context.bindParameters binders).binders := by
    apply List.mem_append_right
    apply List.mem_filter.mpr
    refine ⟨member,?_⟩
    change (!(binders.any (fun shadow => shadow.id == binder.id))) = true
    simp only [Bool.not_eq_true',List.any_eq_false]
    intro shadow present
    simp only [beq_iff_eq]
    intro same
    exact fresh shadow present (same.symm ▸ sameId.symm ▸ occurs.parameterIds)
  simpa only [sameId,sameKind] using Kinding.parameter (program := program) retained

theorem Constraint.parameterIds_term {constraint : Constraint} {term : Term}
    (member : term ∈ constraint.terms) {id : Identity} (present : id ∈ term.parameterIds) :
    id ∈ constraint.parameterIds :=
  List.mem_append_left _ (List.mem_flatMap.mpr ⟨term,member,present⟩)

theorem Constraint.parameterIds_binder {binders : List Binder} {requirements : List Constraint}
    {binder : Binder} (member : binder ∈ binders) :
    binder.id ∈ (Constraint.quantified binders requirements).parameterIds := by
  simp only [Constraint.parameterIds,Constraint.boundIds]
  exact List.mem_append_right _ (List.mem_append_left _ (List.mem_map.mpr ⟨binder,member,rfl⟩))

theorem Constraint.parameterIds_requirement {binders : List Binder} {requirements : List Constraint}
    {requirement : Constraint} (member : requirement ∈ requirements) {id : Identity}
    (present : id ∈ requirement.parameterIds) :
    id ∈ (Constraint.quantified binders requirements).parameterIds := by
  rcases List.mem_append.mp present with term | bound
  · obtain ⟨value,inTerms,inValue⟩ := List.mem_flatMap.mp term
    apply Constraint.parameterIds_term (term := value) _ inValue
    simp only [Constraint.terms]
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨requirement,member,inTerms⟩)
  · simp only [Constraint.parameterIds,Constraint.boundIds]
    exact List.mem_append_right _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨requirement,member,bound⟩))

/-- Alpha-renaming under a lexical binder prefix only requires injectivity on
the finite source support. Outer context names absent from that support need
not be fresh, and same-identity locals correctly mask outer declarations. -/
theorem Kinding.renameParameters_bound {program : Program} {source target : Context}
    {term : Term} {kind : Kind} {binders : List Binder} {support : List Identity}
    (kinded : Kinding program (source.bindParameters binders) term kind) (rename : Identity → Identity)
    (used : ∀ id ∈ term.parameterIds, id ∈ support)
    (bound : ∀ binder ∈ binders, binder.id ∈ support)
    (injective : ∀ left ∈ support, ∀ right ∈ support, rename left = rename right → left = right)
    (parameters : ∀ binder ∈ source.binders, binder.id ∈ support →
      Kinding program target (.parameter (rename binder.id) binder.kind) binder.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands) :
    Kinding program (target.bindParameters (binders.map (Binder.renameParameters rename)))
      (term.renameParameters rename) kind := by
  apply kinded.renameParameters
    (target := target.bindParameters (binders.map (Binder.renameParameters rename))) rename _ levels regions brands
  intro id parameterKind occurs
  obtain ⟨binder,member,sameId,sameKind⟩ := kinded.parameter_occurs occurs
  change binder ∈ binders ++ source.binders.filter _ at member
  rcases List.mem_append.mp member with inBound | outer
  · have renamed : binder.renameParameters rename ∈
        (target.bindParameters (binders.map (Binder.renameParameters rename))).binders :=
      List.mem_append_left _ (List.mem_map.mpr ⟨binder,inBound,rfl⟩)
    simpa only [Binder.renameParameters,sameId,sameKind] using Kinding.parameter (program := program) renamed
  · obtain ⟨outer,unshadowed⟩ := List.mem_filter.mp outer
    have inSupport : binder.id ∈ support := sameId.symm ▸ used id occurs.parameterIds
    have original := parameters binder outer inSupport
    have retained := original.bindParameters (binders.map (Binder.renameParameters rename)) (by
      intro renamed member
      obtain ⟨inner,present,rfl⟩ := List.mem_map.mp member
      simp only [Binder.renameParameters,Term.parameterIds,List.mem_singleton]
      intro same
      have equal := injective inner.id (bound inner present) binder.id inSupport same
      change (!(binders.any (fun inner => inner.id == binder.id))) = true at unshadowed
      simp only [Bool.not_eq_true',List.any_eq_false,beq_iff_eq] at unshadowed
      exact unshadowed inner present equal)
    simpa only [sameId,sameKind] using retained

theorem Kinding.renameParameters_supported {program : Program} {source target : Context}
    {term : Term} {kind : Kind} {support : List Identity}
    (kinded : Kinding program source term kind) (rename : Identity → Identity)
    (used : ∀ id ∈ term.parameterIds, id ∈ support)
    (parameters : ∀ binder ∈ source.binders, binder.id ∈ support →
      Kinding program target (.parameter (rename binder.id) binder.kind) binder.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands) :
    Kinding program target (term.renameParameters rename) kind := by
  apply kinded.renameParameters rename _ levels regions brands
  intro id parameterKind occurs
  obtain ⟨binder,member,sameId,sameKind⟩ := kinded.parameter_occurs occurs
  simpa only [sameId,sameKind] using parameters binder member (sameId.symm ▸ used id occurs.parameterIds)

/-- Predicate alpha-renaming respects the actual lexical binder/default
scopes. Injectivity is required only on the finite source predicate support,
not on unrelated identities in the caller context. -/
theorem ConstraintKinded.renameParameters {program : Program} {source target : Context}
    {constraint : Constraint} {support : List Identity}
    (kinded : ConstraintKinded program source constraint) (rename : Identity → Identity)
    (used : ∀ id ∈ constraint.parameterIds, id ∈ support)
    (injective : ∀ left ∈ support, ∀ right ∈ support, rename left = rename right → left = right)
    (parameters : ∀ binder ∈ source.binders, binder.id ∈ support →
      Kinding program target (.parameter (rename binder.id) binder.kind) binder.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands) :
    ConstraintKinded program target (constraint.renameParameters rename) := by
  revert used parameters levels regions brands
  induction kinded generalizing target <;> intro used parameters levels regions brands
  all_goals simp only [Constraint.renameParameters,Constraint.mapTerms]
  case equal left right =>
    exact .equal (left.renameParameters_supported rename
      (fun id member => used id (Constraint.parameterIds_term (by simp [Constraint.terms]) member)) parameters levels regions brands)
      (right.renameParameters_supported rename
        (fun id member => used id (Constraint.parameterIds_term (by simp [Constraint.terms]) member)) parameters levels regions brands)
  case outlives long short =>
    exact .outlives (long.renameParameters_supported rename
      (fun id member => used id (Constraint.parameterIds_term (by simp [Constraint.terms]) member)) parameters levels regions brands)
      (short.renameParameters_supported rename
        (fun id member => used id (Constraint.parameterIds_term (by simp [Constraint.terms]) member)) parameters levels regions brands)
  case typeOutlives type region =>
    exact .typeOutlives (type.renameParameters_supported rename
      (fun id member => used id (Constraint.parameterIds_term (by simp [Constraint.terms]) member)) parameters levels regions brands)
      (region.renameParameters_supported rename
        (fun id member => used id (Constraint.parameterIds_term (by simp [Constraint.terms]) member)) parameters levels regions brands)
  case rowIncludes allowed required =>
    exact .rowIncludes (allowed.renameParameters_supported rename
      (fun id member => used id (Constraint.parameterIds_term (by simp [Constraint.terms]) member)) parameters levels regions brands)
      (required.renameParameters_supported rename
        (fun id member => used id (Constraint.parameterIds_term (by simp [Constraint.terms]) member)) parameters levels regions brands)
  case implements found instantiated arguments =>
    have mapped := fun term member => (arguments term member).renameParameters_supported rename
      (fun id present => used id (Constraint.parameterIds_term (by simpa only [Constraint.terms] using member) present)) parameters levels regions brands
    exact .implements found (instantiated.map_kind _ (fun term member => (mapped term member).term_kind)) (by
      intro term member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      rw [(mapped original present).term_kind]
      exact mapped original present)
  case use type quantity =>
    exact .use (type.renameParameters_supported rename
      (fun id member => used id (Constraint.parameterIds_term (by simp [Constraint.terms]) member)) parameters levels regions brands) quantity
  case callable receiver arguments result effects =>
    apply ConstraintKinded.callable
      (receiver.renameParameters_supported rename
        (fun id member => used id (Constraint.parameterIds_term (by simp [Constraint.terms]) member)) parameters levels regions brands)
      _
      (result.renameParameters_supported rename
        (fun id member => used id (Constraint.parameterIds_term (by simp [Constraint.terms]) member)) parameters levels regions brands)
      (effects.renameParameters_supported rename
        (fun id member => used id (Constraint.parameterIds_term (by simp [Constraint.terms]) member)) parameters levels regions brands)
    intro term member
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
    exact (arguments original present).renameParameters_supported rename
      (fun id member => used id (Constraint.parameterIds_term (by simp [Constraint.terms,present]) member)) parameters levels regions brands
  case runsIn receiver access arguments after =>
    apply ConstraintKinded.runsIn
      (receiver.renameParameters_supported rename
        (fun id member => used id (Constraint.parameterIds_term (by simp [Constraint.terms]) member)) parameters levels regions brands)
      (access.renameParameters_supported rename
        (fun id member => used id (Constraint.parameterIds_term (by simp [Constraint.terms]) member)) parameters levels regions brands)
      _
      (after.renameParameters_supported rename
        (fun id member => used id (Constraint.parameterIds_term (by simp [Constraint.terms]) member)) parameters levels regions brands)
    intro term member
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
    exact (arguments original present).renameParameters_supported rename
      (fun id member => used id (Constraint.parameterIds_term (by simp [Constraint.terms,present]) member)) parameters levels regions brands
  case quantified binders requirements unique defaults _ ih =>
    have bound := fun (binder : Binder) (member : binder ∈ binders) => used binder.id (Constraint.parameterIds_binder member)
    apply ConstraintKinded.quantified
    · have distinct : ((binders.map Binder.id).map rename).Nodup := by
        apply List.pairwise_map.mpr
        apply List.Pairwise.imp_of_mem _ unique
        intro left right leftMember rightMember different equal
        obtain ⟨first,firstMember,rfl⟩ := List.mem_map.mp leftMember
        obtain ⟨second,secondMember,rfl⟩ := List.mem_map.mp rightMember
        exact different (injective first.id (bound first firstMember) second.id (bound second secondMember) equal)
      simpa only [List.map_map,Binder.renameParameters,Function.comp_def] using distinct
    · intro i binder value found default
      rw [List.getElem?_map] at found
      obtain ⟨original,originalFound,rfl⟩ := Option.map_eq_some_iff.mp found
      obtain ⟨originalValue,originalDefault,rfl⟩ := Option.map_eq_some_iff.mp default
      rw [← List.map_take]
      exact (defaults i original originalValue originalFound originalDefault).renameParameters_bound rename
        (fun id member => used id (Constraint.parameterIds_term (by
          simp only [Constraint.terms]
          apply List.mem_append_left
          exact List.mem_flatMap.mpr ⟨original,List.mem_of_getElem? originalFound,by simp [originalDefault]⟩) member))
        (fun binder member => bound binder (List.mem_of_mem_take member)) injective parameters levels regions brands
    · intro requirement member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      apply ih original present (target := target.bindParameters (binders.map (Binder.renameParameters rename)))
        (fun id member => used id (Constraint.parameterIds_requirement present member))
        _ levels regions brands
      intro binder member supported
      have renamed := (Kinding.parameter (program := program) member).renameParameters_bound rename
        (fun id occurs => by
          simp only [Term.parameterIds,List.mem_singleton] at occurs
          exact occurs.symm ▸ supported)
        bound injective parameters levels regions brands
      simpa only [Term.renameParameters] using renamed

end Glorious.Language
