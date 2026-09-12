import GloriousLanguage.TermScope

/-! Kind preservation for the existing source substitution operation. These
proofs do not normalize arguments, resolve projections, or invent evidence. -/
namespace Glorious.Language

theorem Kinding.term_kind {program : Program} {context : Context} {term : Term} {kind : Kind}
    (kinded : Kinding program context term kind) : term.kind = kind := by
  cases kinded <;> rfl

theorem Instantiates.map_kind {binders : List Binder} {arguments : List Term} {substitution : Substitution}
    (instantiated : Instantiates binders arguments substitution) (f : Term → Term)
    (preserves : ∀ argument ∈ arguments, (f argument).kind = argument.kind) :
    Instantiates binders (arguments.map f) ((binders.map (·.id)).zip (arguments.map f)) := by
  refine ⟨instantiated.1,?_,rfl⟩
  have related := instantiated.2.1
  clear instantiated substitution
  induction related with
  | nil => exact .nil
  | @cons binder argument binders arguments head tail ih =>
    exact .cons (head.trans (preserves argument List.mem_cons_self).symm)
      (ih (fun term member => preserves term (List.mem_cons_of_mem _ member)))

theorem Kinding.child {program : Program} {context : Context} {term child : Term} {kind : Kind}
    (kinded : Kinding program context term kind) (member : child ∈ term.children) :
    ∃ childKind, Kinding program context child childKind := by
  cases kinded <;> simp_all only [Term.children,List.mem_cons,List.mem_append,List.not_mem_nil]
  all_goals grind

theorem Kinding.parameter_occurs {program : Program} {context : Context} {term : Term} {kind : Kind}
    (kinded : Kinding program context term kind) {id : Identity} {parameterKind : Kind}
    (occurs : Occurs (.parameter id parameterKind) term) :
    ∃ binder ∈ context.binders, binder.id = id ∧ binder.kind = parameterKind := by
  induction occurs generalizing kind with
  | here => cases kinded with | parameter member => exact ⟨_,member,rfl,rfl⟩
  | child member _ ih =>
    obtain ⟨childKind,childKinded⟩ := kinded.child member
    exact ih childKinded

/-- The checked substitution graph is determined by the actual lookup kinds
at source parameter occurrences. It does not require caller terms to remain
kinded in an un-freshened, potentially capturing intermediate context. -/
theorem Kinding.substitutes_kinds {program : Program} {context : Context} {term : Term} {kind : Kind}
    (kinded : Kinding program context term kind) (substitution : Substitution)
    (parameters : ∀ binder ∈ context.binders, ∀ value,
      substitution.get binder.id = some value → value.kind = binder.kind) :
    Substitutes substitution term (term.substitute substitution) := by
  have checked : ∀ id parameterKind value, Occurs (.parameter id parameterKind) term →
      substitution.get id = some value → value.kind = parameterKind := by
    intro id parameterKind value occurs found
    obtain ⟨binder,member,sameId,sameKind⟩ := kinded.parameter_occurs occurs
    simpa only [sameKind] using parameters binder member value (sameId.symm ▸ found)
  refine ⟨?_,rfl,checked⟩
  cases term <;> simp only [Term.substitute,Term.kind]
  case parameter id parameterKind =>
    cases found : substitution.get id with
    | none => rfl
    | some value => exact (checked id parameterKind value .here found).symm

private theorem parameters_child {program : Program} {context : Context} {term child : Term}
    {f : Term → Term}
    (parameters : ∀ id kind, Occurs (.parameter id kind) term → Kinding program context (f (.parameter id kind)) kind)
    (member : child ∈ term.children) :
    ∀ id kind, Occurs (.parameter id kind) child → Kinding program context (f (.parameter id kind)) kind :=
  fun id kind occurs => parameters id kind (.child member occurs)

/-- One structural transport theorem for simultaneous substitutions, alpha
renamings and support-sensitive changes of context. Only parameters actually
occurring in the term require target evidence. -/
theorem Kinding.map_parameters {program : Program} {source target : Context} {term : Term} {kind : Kind}
    (kinded : Kinding program source term kind) (f : Term → Term)
    (shape : ∀ term, f term = match term with
      | .parameter id kind => f (.parameter id kind)
      | other => other.mapChildren f)
    (parameters : ∀ id parameterKind, Occurs (.parameter id parameterKind) term →
      Kinding program target (f (.parameter id parameterKind)) parameterKind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands) :
    Kinding program target (f term) kind := by
  revert parameters
  induction kinded <;> intro parameters
  case parameter => exact parameters _ _ .here
  all_goals rw [shape]; simp only [Term.mapChildren]
  case quantity bounds => exact .quantity bounds
  case rigid bound => exact .rigid (Nat.le_trans bound levels)
  case scopedRegion member => exact .scopedRegion (regions _ member)
  case scopedBrand member => exact .scopedBrand (brands _ member)
  case runtimeRegion => exact .runtimeRegion
  case runtimeBrand => exact .runtimeBrand
  case «variable» bound => exact .variable (Nat.le_trans bound levels)
  case unit => exact .unit
  case bottom => exact .bottom
  case scalar valid => exact .scalar valid
  case tuple _ ih =>
    apply Kinding.tuple
    intro child member
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
    exact ih original present (parameters_child parameters present)
  case array _ _ element length =>
    exact .array (element (parameters_child parameters (by simp [Term.children])))
      (length (parameters_child parameters (by simp [Term.children])))
  case reference _ _ region referent =>
    exact .reference (region (parameters_child parameters (by simp [Term.children])))
      (referent (parameters_child parameters (by simp [Term.children])))
  case rawPointer _ referent =>
    exact .rawPointer (referent (parameters_child parameters (by simp [Term.children])))
  case nominal found instantiated _ ih =>
    have arguments := fun child member => ih child member (parameters_child parameters member)
    exact .nominal found (instantiated.map_kind f (fun child member => (arguments child member).term_kind)) (by
      intro child member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      rw [(arguments original present).term_kind]
      exact arguments original present)
  case alias found instantiated _ ih =>
    have arguments := fun child member => ih child member (parameters_child parameters member)
    exact .alias found (instantiated.map_kind f (fun child member => (arguments child member).term_kind)) (by
      intro child member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      rw [(arguments original present).term_kind]
      exact arguments original present)
  case callable found instantiated _ ih =>
    have arguments := fun child member => ih child member (parameters_child parameters member)
    exact .callable found (instantiated.map_kind f (fun child member => (arguments child member).term_kind)) (by
      intro child member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      rw [(arguments original present).term_kind]
      exact arguments original present)
  case continuation _ _ _ _ quantity brand argument answer effects =>
    exact .continuation (brand (parameters_child parameters (by simp [Term.children])))
      (argument (parameters_child parameters (by simp [Term.children])))
      (answer (parameters_child parameters (by simp [Term.children])))
      (effects (parameters_child parameters (by simp [Term.children]))) quantity
  case label _ _ _ brand region result =>
    exact .label (brand (parameters_child parameters (by simp [Term.children])))
      (region (parameters_child parameters (by simp [Term.children])))
      (result (parameters_child parameters (by simp [Term.children])))
  case environment _ _ _ brand region ih =>
    apply Kinding.environment (brand (parameters_child parameters (by simp [Term.children])))
      (region (parameters_child parameters (by simp [Term.children])))
    intro child member
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
    exact ih original present (parameters_child parameters (by simpa only [Term.children,List.mem_cons] using Or.inr (Or.inr present)))
  case available _ _ _ brand region ih =>
    apply Kinding.available (brand (parameters_child parameters (by simp [Term.children])))
      (region (parameters_child parameters (by simp [Term.children])))
    intro child member
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
    exact ih original present (parameters_child parameters (by simpa only [Term.children,List.mem_cons] using Or.inr (Or.inr present)))
  case bindings _ _ _ brand region ih =>
    apply Kinding.bindings (brand (parameters_child parameters (by simp [Term.children])))
      (region (parameters_child parameters (by simp [Term.children])))
    intro child member
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
    exact ih original present (parameters_child parameters (by simpa only [Term.children,List.mem_cons] using Or.inr (Or.inr present)))
  case effect found instantiated _ ih =>
    have arguments := fun child member => ih child member (parameters_child parameters member)
    exact .effect found (instantiated.map_kind f (fun child member => (arguments child member).term_kind)) (by
      intro child member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      rw [(arguments original present).term_kind]
      exact arguments original present)
  case row _ _ instances tails =>
    apply Kinding.row
    · intro child member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      exact instances original present (parameters_child parameters (List.mem_append_left _ present))
    · intro child member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      exact tails original present (parameters_child parameters (List.mem_append_right _ present))
  case projection found member associated owner owners items _ ih =>
    have arguments := fun child member => ih child member (parameters_child parameters member)
    exact .projection found member associated owner
      (owners.map_kind f (fun child present => (arguments child (List.mem_append_left _ present)).term_kind))
      (items.map_kind f (fun child present => (arguments child (List.mem_append_right _ present)).term_kind)) (by
        intro child present
        rw [← List.map_append] at present
        obtain ⟨original,inOriginal,rfl⟩ := List.mem_map.mp present
        rw [(arguments original inOriginal).term_kind]
        exact arguments original inOriginal)
  case scalarConstant valid => exact .scalarConstant valid
  case tupleConstant _ ih =>
    apply Kinding.tupleConstant
    intro child member
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
    exact ih original present (parameters_child parameters present)
  case constructorConstant found instantiated _ count _ arguments ih =>
    have argumentKinds := fun child member => arguments child member
      (parameters_child parameters (List.mem_append_left _ member))
    exact .constructorConstant found
      (instantiated.map_kind f (fun child member => (argumentKinds child member).term_kind))
      (by
        intro child member
        obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
        rw [(argumentKinds original present).term_kind]
        exact argumentKinds original present)
      (by simpa only [List.length_map] using count)
      (by
        intro child member
        obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
        exact ih original present (parameters_child parameters (List.mem_append_right _ present)))
  case principal => exact .principal
  case static => exact .static

/-- Simultaneous source substitution needs target kinding only at the
parameters used by this term, including parameters below mixed-kind nodes. -/
theorem Kinding.substitute_supported {program : Program} {source target : Context} {term : Term} {kind : Kind}
    (kinded : Kinding program source term kind) (substitution : Substitution)
    (parameters : ∀ id parameterKind, Occurs (.parameter id parameterKind) term →
      Kinding program target ((Term.parameter id parameterKind).substitute substitution) parameterKind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands) :
    Kinding program target (term.substitute substitution) kind :=
  kinded.map_parameters _ (by intro term; cases term <;> simp only [Term.substitute,Term.mapChildren])
    parameters levels regions brands

/-- Existing instantiation consumers specialize the support-sensitive theorem
to target interpretations of every declared source parameter. -/
theorem Kinding.substitute {program : Program} {source target : Context} {term : Term} {kind : Kind}
    (kinded : Kinding program source term kind) (substitution : Substitution)
    (parameters : ∀ binder ∈ source.binders,
      Kinding program target ((Term.parameter binder.id binder.kind).substitute substitution) binder.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands) :
    Kinding program target (term.substitute substitution) kind := by
  apply kinded.substitute_supported substitution _ levels regions brands
  intro id parameterKind occurs
  obtain ⟨binder,member,sameId,sameKind⟩ := kinded.parameter_occurs occurs
  simpa only [sameId,sameKind] using parameters binder member

/-- Kinded substitution also supplies every occurrence check required by the
authoritative `Substitutes` relation, including nested mixed-kind arguments. -/
theorem Kinding.substitutes {program : Program} {source target : Context} {term : Term} {kind : Kind}
    (kinded : Kinding program source term kind) (substitution : Substitution)
    (parameters : ∀ binder ∈ source.binders,
      Kinding program target ((Term.parameter binder.id binder.kind).substitute substitution) binder.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands) :
    Substitutes substitution term (term.substitute substitution) := by
  refine ⟨kinded.term_kind.trans (kinded.substitute substitution parameters levels regions brands).term_kind.symm,rfl,?_⟩
  intro id parameterKind value occurs found
  obtain ⟨binder,member,sameId,sameKind⟩ := kinded.parameter_occurs occurs
  have typed := parameters binder member
  rw [sameId,sameKind] at typed
  simpa only [Term.substitute,found,Option.getD_some] using typed.term_kind

theorem Instantiates.binder_lookup {binders : List Binder} {arguments : List Term} {substitution : Substitution}
    (instantiated : Instantiates binders arguments substitution) {binder : Binder} (member : binder ∈ binders) :
    ∃ value ∈ arguments, binder.kind = value.kind ∧ substitution.get binder.id = some value := by
  rw [instantiated.2.2]
  have unique := instantiated.1
  have related := instantiated.2.1
  clear instantiated substitution
  induction related with
  | nil => exact False.elim (List.not_mem_nil member)
  | @cons first value binders arguments head tail ih =>
    simp only [List.map_cons,List.nodup_cons] at unique
    rcases List.mem_cons.mp member with same | present
    · subst binder
      exact ⟨value,List.mem_cons_self,head,by simp [Table.get]⟩
    · obtain ⟨argument,inArguments,kindEqual,found⟩ := ih present unique.2
      have different : first.id ≠ binder.id := by
        intro same
        exact unique.1 (same.symm ▸ List.mem_map.mpr ⟨binder,present,rfl⟩)
      exact ⟨argument,List.mem_cons_of_mem _ inArguments,kindEqual,by
        simpa [Table.get,different] using found⟩

/-- A real binder instantiation supplies the general substitution theorem's
parameter witnesses. No normal forms or resolved projections are required. -/
theorem Instantiates.kinding_parameters {program : Program} {context : Context} {binders : List Binder}
    {arguments : List Term} {substitution : Substitution}
    (instantiated : Instantiates binders arguments substitution)
    (argumentsKinded : ∀ argument ∈ arguments, Kinding program context argument argument.kind) :
    ∀ binder ∈ binders,
      Kinding program context ((Term.parameter binder.id binder.kind).substitute substitution) binder.kind := by
  intro binder member
  obtain ⟨value,present,kindEqual,found⟩ := instantiated.binder_lookup member
  simpa only [Term.substitute,found,Option.getD_some,kindEqual] using argumentsKinded value present

/-- Ordered argument lists bind two disjoint template domains simultaneously.
Values retain the caller's syntax, even if they mention the other domain's
identities; the lookup does not recursively substitute into an inserted value. -/
theorem Instantiates.append {leftBinders rightBinders : List Binder} {leftArguments rightArguments : List Term}
    {leftSub rightSub : Substitution} (left : Instantiates leftBinders leftArguments leftSub)
    (right : Instantiates rightBinders rightArguments rightSub)
    (unique : ((leftBinders ++ rightBinders).map (·.id)).Nodup) :
    Instantiates (leftBinders ++ rightBinders) (leftArguments ++ rightArguments) (leftSub ++ rightSub) := by
  refine ⟨unique,left.2.1.append right.2.1,?_⟩
  rw [left.2.2,right.2.2,List.map_append,List.zip_append]
  simpa only [List.length_map] using left.2.1.length_eq

theorem Kinding.instantiate {program : Program} {source target : Context} {term : Term} {kind : Kind}
    (kinded : Kinding program source term kind) {arguments : List Term} {substitution : Substitution}
    (instantiated : Instantiates source.binders arguments substitution)
    (argumentsKinded : ∀ argument ∈ arguments, Kinding program target argument argument.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands) :
    Kinding program target (term.substitute substitution) kind ∧
      Substitutes substitution term (term.substitute substitution) :=
  ⟨kinded.substitute substitution (instantiated.kinding_parameters argumentsKinded) levels regions brands,
    kinded.substitutes substitution (instantiated.kinding_parameters argumentsKinded) levels regions brands⟩

end Glorious.Language
