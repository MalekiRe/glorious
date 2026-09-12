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

/-- Every parameter is interpreted in the target context at its declared kind;
all other source kinding information is transported structurally. -/
theorem Kinding.substitute {program : Program} {source target : Context} {term : Term} {kind : Kind}
    (kinded : Kinding program source term kind) (substitution : Substitution)
    (parameters : ∀ binder ∈ source.binders,
      Kinding program target ((Term.parameter binder.id binder.kind).substitute substitution) binder.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands) :
    Kinding program target (term.substitute substitution) kind := by
  induction kinded <;> simp only [Term.substitute]
  case quantity bounds => exact .quantity bounds
  case parameter binder member => simpa only [Term.substitute] using parameters binder member
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
    exact .tuple (by
      intro term member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      exact ih original present)
  case array _ _ element length => exact .array element length
  case reference _ _ region referent => exact .reference region referent
  case rawPointer _ referent => exact .rawPointer referent
  case nominal found instantiated _ ih =>
    exact .nominal found (instantiated.map_kind _ (fun term member => (ih term member).term_kind)) (by
      intro term member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      rw [(ih original present).term_kind]
      exact ih original present)
  case alias found instantiated _ ih =>
    exact .alias found (instantiated.map_kind _ (fun term member => (ih term member).term_kind)) (by
      intro term member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      rw [(ih original present).term_kind]
      exact ih original present)
  case callable found instantiated _ ih =>
    exact .callable found (instantiated.map_kind _ (fun term member => (ih term member).term_kind)) (by
      intro term member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      rw [(ih original present).term_kind]
      exact ih original present)
  case continuation _ _ _ _ quantity brand argument answer effects =>
    exact .continuation brand argument answer effects quantity
  case label _ _ _ brand region result => exact .label brand region result
  case environment _ _ _ brand region ih =>
    exact .environment brand region (by
      intro term member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      exact ih original present)
  case available _ _ _ brand region ih =>
    exact .available brand region (by
      intro term member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      exact ih original present)
  case bindings _ _ _ brand region ih =>
    exact .bindings brand region (by
      intro term member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      exact ih original present)
  case effect found instantiated _ ih =>
    exact .effect found (instantiated.map_kind _ (fun term member => (ih term member).term_kind)) (by
      intro term member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      rw [(ih original present).term_kind]
      exact ih original present)
  case row _ _ instances tails =>
    exact .row (by
      intro term member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      exact instances original present) (by
      intro term member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      exact tails original present)
  case projection found member associated owner owners items _ ih =>
    exact .projection found member associated owner
      (owners.map_kind _ (fun term present => (ih term (List.mem_append_left _ present)).term_kind))
      (items.map_kind _ (fun term present => (ih term (List.mem_append_right _ present)).term_kind)) (by
        intro term present
        rw [← List.map_append] at present
        obtain ⟨original,inOriginal,rfl⟩ := List.mem_map.mp present
        rw [(ih original inOriginal).term_kind]
        exact ih original inOriginal)
  case scalarConstant valid => exact .scalarConstant valid
  case tupleConstant _ ih =>
    exact .tupleConstant (by
      intro term member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      exact ih original present)
  case constructorConstant found instantiated _ count _ arguments ih =>
    exact .constructorConstant found
      (instantiated.map_kind _ (fun term member => (arguments term member).term_kind))
      (by
        intro term member
        obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
        rw [(arguments original present).term_kind]
        exact arguments original present)
      (by simpa only [List.length_map] using count)
      (by
        intro term member
        obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
        exact ih original present)
  case principal => exact .principal
  case static => exact .static

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
