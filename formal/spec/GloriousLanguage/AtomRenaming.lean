import GloriousLanguage.UniverseTransport

/-! A concrete action on generative atoms. Lexical parameter identities,
declaration identities and every composite constructor are unchanged. The
action is shared by runtime-region permutations and universe reindexing. -/
namespace Glorious.Language

structure AtomRenaming where
  region : Identity → Identity
  rigid : Identity → Kind → Nat → Identity × Nat
  inference : Identity → Kind → Nat → Identity × Nat

def AtomRenaming.term (rename : AtomRenaming) : Term → Term
  | .runtimeRegion id => .runtimeRegion (rename.region id)
  | .rigid id kind level => .rigid (rename.rigid id kind level).1 kind (rename.rigid id kind level).2
  | .variable id kind level => .variable (rename.inference id kind level).1 kind (rename.inference id kind level).2
  | .tuple fields => .tuple (fields.map rename.term)
  | .array a b => .array (rename.term a) (rename.term b)
  | .reference mode a b => .reference mode (rename.term a) (rename.term b)
  | .rawPointer mode a => .rawPointer mode (rename.term a)
  | .nominal id arguments => .nominal id (arguments.map rename.term)
  | .alias id arguments => .alias id (arguments.map rename.term)
  | .callable id arguments => .callable id (arguments.map rename.term)
  | .continuation a b c d q => .continuation (rename.term a) (rename.term b) (rename.term c) (rename.term d) q
  | .label a b c => .label (rename.term a) (rename.term b) (rename.term c)
  | .environment a b residents => .environment (rename.term a) (rename.term b) (residents.map rename.term)
  | .available a b residents => .available (rename.term a) (rename.term b) (residents.map rename.term)
  | .bindings a b arguments => .bindings (rename.term a) (rename.term b) (arguments.map rename.term)
  | .effect id arguments => .effect id (arguments.map rename.term)
  | .row instances tails => .row (instances.map rename.term) (tails.map rename.term)
  | .projection trait member owners items kind => .projection trait member (owners.map rename.term) (items.map rename.term) kind
  | .constantTuple fields => .constantTuple (fields.map rename.term)
  | .constantConstructor id arguments fields => .constantConstructor id (arguments.map rename.term) (fields.map rename.term)
  | term => term

def AtomRenaming.substitution (rename : AtomRenaming) (substitution : Substitution) : Substitution :=
  substitution.map (fun entry => (entry.1,rename.term entry.2))

def AtomRenaming.binder (rename : AtomRenaming) (binder : Binder) : Binder :=
  { binder with defaultValue := binder.defaultValue.map rename.term }

def AtomRenaming.constraint (rename : AtomRenaming) : Constraint → Constraint :=
  Constraint.mapTerms rename.term

theorem AtomRenaming.kind (rename : AtomRenaming) (term : Term) : (rename.term term).kind = term.kind := by
  cases term <;> simp only [AtomRenaming.term,Term.kind]

theorem AtomRenaming.children (rename : AtomRenaming) (term : Term) :
    (rename.term term).children = term.children.map rename.term := by
  cases term <;> simp only [AtomRenaming.term,Term.children,List.map_cons,List.map_nil,List.map_append]

theorem AtomRenaming.head (rename : AtomRenaming) (term : Term) :
    (rename.term term).mapChildren (fun _ => .unit) = rename.term (term.mapChildren (fun _ => .unit)) := by
  cases term <;> simp only [AtomRenaming.term,Term.mapChildren,List.map_map,Function.comp_def]
  all_goals try rfl
  all_goals congr 1
  all_goals apply List.map_congr_left
  all_goals intro child _
  all_goals rfl

theorem SameHead.renameAtoms {left right : Term} (same : SameHead left right) (rename : AtomRenaming) :
    SameHead (rename.term left) (rename.term right) := by
  unfold SameHead at same ⊢
  rw [rename.head,rename.head,same]

/-- A determining child position cannot have a generative-atom head. The
actual source head therefore remains fixed while the query is renamed. -/
theorem SameHead.renameAtoms_right {left right child : Term} (same : SameHead left right) (rename : AtomRenaming)
    (member : child ∈ right.children) : SameHead left (rename.term right) := by
  unfold SameHead at same ⊢
  rw [same]
  cases right <;> simp only [Term.children,List.not_mem_nil] at member
  all_goals simp only [AtomRenaming.term,Term.mapChildren,List.map_map,Function.comp_def]

theorem AtomRenaming.parameter_origin (rename : AtomRenaming) {term : Term} {id : Identity} {kind : Kind}
    (same : rename.term term = .parameter id kind) : term = .parameter id kind := by
  cases term <;> simp only [AtomRenaming.term] at same <;> cases same <;> rfl

theorem AtomRenaming.occurs_preimage (rename : AtomRenaming) {needle term : Term}
    (occurs : Occurs needle (rename.term term)) :
    ∃ original, Occurs original term ∧ rename.term original = needle := by
  generalize renamed : rename.term term = result at occurs
  induction occurs generalizing term with
  | here => exact ⟨term,.here,renamed⟩
  | @child parent child member nested ih =>
    rw [← renamed,rename.children] at member
    obtain ⟨original,inOriginal,atChild⟩ := List.mem_map.mp member
    obtain ⟨ancestor,inside,atNeedle⟩ := ih atChild
    exact ⟨ancestor,.child inOriginal inside,atNeedle⟩

theorem AtomRenaming.parameter_occurs (rename : AtomRenaming) {term : Term} {id : Identity} {kind : Kind}
    (occurs : Occurs (.parameter id kind) (rename.term term)) : Occurs (.parameter id kind) term := by
  obtain ⟨original,nested,same⟩ := rename.occurs_preimage occurs
  exact rename.parameter_origin same ▸ nested

theorem AtomRenaming.parameterIds (rename : AtomRenaming) (term : Term) :
    (rename.term term).parameterIds = term.parameterIds := by
  cases term <;> simp only [AtomRenaming.term,Term.parameterIds,List.flatMap_map]
  all_goals try rfl
  all_goals repeat' first
    | exact AtomRenaming.parameterIds rename _
    | apply List.flatMap_congr_left
      intro child _
      exact rename.parameterIds child
    | congr 1
termination_by term

theorem AtomRenaming.renameParameters (rename : AtomRenaming) (parameters : Identity → Identity) (term : Term) :
    rename.term (term.renameParameters parameters) = (rename.term term).renameParameters parameters := by
  cases term <;> simp only [Term.renameParameters,AtomRenaming.term,List.map_map,Function.comp_def]
  all_goals try rfl
  all_goals congr 1
  all_goals first
    | exact AtomRenaming.renameParameters rename parameters _
    | apply List.map_congr_left
      intro child _
      exact rename.renameParameters parameters child
termination_by term

theorem AtomRenaming.term_substitute (rename : AtomRenaming) (substitution : Substitution) (term : Term) :
    rename.term (term.substitute substitution) = (rename.term term).substitute (rename.substitution substitution) := by
  cases term <;> simp only [Term.substitute,AtomRenaming.term]
  case parameter id kind =>
    rw [AtomRenaming.substitution,Table.get_map_values]
    cases substitution.get id <;> simp only [Option.getD,Option.map,AtomRenaming.term]
  all_goals try rfl
  all_goals try simp only [List.map_map,Function.comp_def]
  all_goals congr 1
  all_goals first
    | exact AtomRenaming.term_substitute rename substitution _
    | apply List.map_congr_left
      intro child _
      exact rename.term_substitute substitution child
termination_by term

theorem AtomRenaming.substitutes (rename : AtomRenaming) {substitution : Substitution} {before after : Term}
    (related : Substitutes substitution before after) :
    Substitutes (rename.substitution substitution) (rename.term before) (rename.term after) := by
  refine ⟨by simpa only [rename.kind] using related.1,?_,?_⟩
  · rw [related.2.1,rename.term_substitute]
  · intro id kind value occurs found
    rw [AtomRenaming.substitution,Table.get_map_values] at found
    obtain ⟨previous,selected,rfl⟩ := Option.map_eq_some_iff.mp found
    simpa only [rename.kind] using related.2.2 id kind previous (rename.parameter_occurs occurs) selected

theorem AtomRenaming.substitution_filter (rename : AtomRenaming) (substitution : Substitution) (keep : Identity → Bool) :
    rename.substitution (substitution.filter (fun entry => keep entry.1)) =
      (rename.substitution substitution).filter (fun entry => keep entry.1) := by
  simp only [AtomRenaming.substitution,List.filter_map,Function.comp_def]

theorem AtomRenaming.lookup_default (rename : AtomRenaming) (substitution : Substitution) (id : Identity) (kind : Kind) :
    ((rename.substitution substitution).get id).getD (.parameter id kind) =
      rename.term ((substitution.get id).getD (.parameter id kind)) := by
  rw [AtomRenaming.substitution,Table.get_map_values]
  cases substitution.get id <;> simp only [Option.map,Option.getD,AtomRenaming.term]

theorem AtomRenaming.constraint_parameterIds (rename : AtomRenaming) (constraint : Constraint) :
    (rename.constraint constraint).parameterIds = constraint.parameterIds := by
  simp only [AtomRenaming.constraint,Constraint.parameterIds,Constraint.terms_mapTerms,
    Constraint.boundIds_mapTerms,List.flatMap_map,rename.parameterIds]

theorem AtomRenaming.freshSeed (rename : AtomRenaming) (constraint : Constraint) (substitution : Substitution) :
    (rename.constraint constraint).freshSeed (rename.substitution substitution) = constraint.freshSeed substitution := by
  simp only [Constraint.freshSeed,rename.constraint_parameterIds,AtomRenaming.substitution,
    Substitution.parameterIds,List.flatMap_map,rename.parameterIds]

theorem AtomRenaming.constraint_renameParameters (rename : AtomRenaming) (parameters : Identity → Identity)
    (constraint : Constraint) :
    rename.constraint (constraint.renameParameters parameters) = (rename.constraint constraint).renameParameters parameters := by
  cases constraint <;> simp only [AtomRenaming.constraint,Constraint.renameParameters,Constraint.mapTerms,
    List.map_map,Function.comp_def,rename.renameParameters]
  all_goals try rfl
  case quantified binders requirements =>
    congr 1
    · apply List.map_congr_left
      intro binder _
      simp only [Binder.renameParameters,Option.map_map,Function.comp_def,rename.renameParameters]
    · apply List.map_congr_left
      intro requirement _
      exact rename.constraint_renameParameters parameters requirement
termination_by constraint

theorem AtomRenaming.constraint_substitute (rename : AtomRenaming) (substitution : Substitution) (constraint : Constraint) :
    rename.constraint (constraint.substitute substitution) =
      (rename.constraint constraint).substitute (rename.substitution substitution) := by
  cases constraint <;> simp only [AtomRenaming.constraint,Constraint.substitute,Constraint.mapTerms,
    rename.term_substitute,List.map_map,Function.comp_def]
  all_goals try rfl
  case quantified binders requirements =>
    have fresh := rename.freshSeed (.quantified binders requirements) substitution
    simp only [AtomRenaming.constraint,Constraint.mapTerms,AtomRenaming.substitution] at fresh
    have renamings (sourceBinders : List Binder) (seed : Identity) :
        Binder.freshRename (sourceBinders.map (fun binder => { binder with defaultValue := binder.defaultValue.map rename.term })) seed =
          Binder.freshRename sourceBinders seed := by
      funext id
      simp only [Binder.freshRename,List.map_map,Function.comp_def]
    simp only [fresh,renamings,List.any_map,AtomRenaming.substitution,List.filter_map,← List.map_take,
      List.map_mapIdx,List.mapIdx_map,Function.comp_def,Option.map_map,rename.renameParameters,rename.term_substitute]
    congr 1
    simp only [List.attach_map,List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro requirement _
    have commutes := rename.constraint_renameParameters
      (Binder.freshRename binders ((Constraint.quantified binders requirements).freshSeed substitution)) requirement.val
    simp only [AtomRenaming.constraint] at commutes
    rw [← commutes]
    exact rename.constraint_substitute _ (requirement.val.renameParameters _)
termination_by constraint.quantifierCount
decreasing_by
  simp only [Constraint.quantifierCount_renameParameters,Constraint.quantifierCount]
  have smaller := List.nat_le_sum_of_mem (List.mem_map_of_mem (f := Constraint.quantifierCount) requirement.property)
  omega

theorem AtomRenaming.substitutes_self (rename : AtomRenaming) {substitution : Substitution} {term : Term}
    (related : Substitutes substitution term (term.substitute substitution)) :
    Substitutes (rename.substitution substitution) (rename.term term)
      ((rename.term term).substitute (rename.substitution substitution)) := by
  simpa only [rename.term_substitute] using rename.substitutes related

theorem AtomRenaming.constraint_admissible (rename : AtomRenaming) {substitution : Substitution} {constraint : Constraint}
    (admissible : constraint.SubstitutionAdmissible substitution) :
    (rename.constraint constraint).SubstitutionAdmissible (rename.substitution substitution) := by
  cases constraint <;>
    simp only [AtomRenaming.constraint,Constraint.mapTerms,Constraint.SubstitutionAdmissible] at admissible ⊢
  all_goals try exact ⟨rename.substitutes_self admissible.1,rename.substitutes_self admissible.2⟩
  case use => exact rename.substitutes_self admissible
  all_goals try {
    intro term member
    try simp only [← List.map_cons] at member
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
    exact rename.substitutes_self (admissible original present) }
  case quantified binders requirements =>
    have restricted :
        (rename.substitution substitution).filter (fun entry => !(binders.any (fun binder => binder.id == entry.1))) =
        rename.substitution (substitution.filter (fun entry => !(binders.any (fun binder => binder.id == entry.1)))) :=
      (rename.substitution_filter substitution (fun id => !(binders.any (fun binder => binder.id == id)))).symm
    simp only [List.any_map,Function.comp_def,restricted]
    refine ⟨?_,?_⟩
    · intro index binder member value found
      simp only [List.getElem?_map] at member
      obtain ⟨original,present,rfl⟩ := Option.map_eq_some_iff.mp member
      obtain ⟨oldValue,selected,rfl⟩ := Option.map_eq_some_iff.mp found
      have mapped := rename.substitutes_self (admissible.1 index original present oldValue selected)
      rw [rename.substitution_filter substitution (fun id => !((binders.take index).any (fun binder => binder.id == id)))] at mapped
      simpa only [← List.map_take,List.any_map,Function.comp_def] using mapped
    · intro requirement member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      exact rename.constraint_admissible (admissible.2 original present)
termination_by constraint

theorem AtomRenaming.substitute_constraint (rename : AtomRenaming) {substitution : Substitution} {before after : Constraint}
    (related : SubstituteConstraint substitution before after) :
    SubstituteConstraint (rename.substitution substitution) (rename.constraint before) (rename.constraint after) := by
  exact ⟨rename.constraint_admissible related.1,by rw [related.2,rename.constraint_substitute]⟩

theorem Instantiates.renameAtoms {binders : List Binder} {arguments : List Term} {substitution : Substitution}
    (instantiated : Instantiates binders arguments substitution) (rename : AtomRenaming) :
    Instantiates binders (arguments.map rename.term) (rename.substitution substitution) := by
  refine ⟨instantiated.1,?_,?_⟩
  · have kinds := instantiated.2.1
    clear instantiated
    induction kinds with
    | nil => exact .nil
    | cons head _ ih => exact .cons (by simpa only [rename.kind] using head) ih
  · rw [instantiated.2.2]
    simp only [AtomRenaming.substitution,List.zip_map_right]
    apply List.map_congr_left
    intro entry _
    cases entry
    rfl

theorem Instantiates.renameBinders {binders : List Binder} {arguments : List Term} {substitution : Substitution}
    (instantiated : Instantiates binders arguments substitution) (rename : AtomRenaming) :
    Instantiates (binders.map rename.binder) arguments substitution := by
  refine ⟨by simpa only [List.map_map,Function.comp_def,AtomRenaming.binder] using instantiated.1,?_,?_⟩
  · have kinds := instantiated.2.1
    clear instantiated
    induction kinds with
    | nil => exact .nil
    | cons head _ ih => exact .cons head ih
  · simpa only [List.map_map,Function.comp_def,AtomRenaming.binder] using instantiated.2.2

theorem AtomRenaming.fixed_constraint (rename : AtomRenaming) {constraint : Constraint}
    (fixed : ∀ term ∈ constraint.terms, rename.term term = term) : rename.constraint constraint = constraint := by
  cases constraint <;> simp only [AtomRenaming.constraint,Constraint.mapTerms]
  all_goals try {
    congr 1
    all_goals first
    | exact fixed _ (by simp [Constraint.terms])
    | exact List.map_eq_self_of _ _ (fun term member => fixed term (by simp [Constraint.terms,member])) }
  case quantified binders requirements =>
    congr 1
    · apply List.map_eq_self_of
      intro binder member
      cases binder with
      | mk id name kind defaultValue =>
        cases defaultValue with
        | none => rfl
        | some value =>
          have kept := fixed value (by
            simp only [Constraint.terms,List.mem_append,List.mem_flatMap]
            exact Or.inl ⟨_,member,by simp⟩)
          simp only [Option.map,kept]
    · apply List.map_eq_self_of
      intro requirement member
      exact rename.fixed_constraint (fun term nested => fixed term (by
        simp only [Constraint.terms,List.mem_append,List.mem_flatMap]
        exact Or.inr ⟨requirement,member,nested⟩))
termination_by constraint

theorem AtomRenaming.substitutes_fixed (rename : AtomRenaming) {substitution : Substitution} {before after : Term}
    (fixed : rename.term before = before) (related : Substitutes substitution before after) :
    Substitutes (rename.substitution substitution) before (rename.term after) := by
  simpa only [fixed] using rename.substitutes related

theorem AtomRenaming.substitutes_fixed_list (rename : AtomRenaming) {substitution : Substitution} {before after : List Term}
    (fixed : ∀ term ∈ before, rename.term term = term) (related : ListRel (Substitutes substitution) before after) :
    ListRel (Substitutes (rename.substitution substitution)) before (after.map rename.term) := by
  induction related with
  | nil => exact .nil
  | cons head _ ih =>
    exact .cons (rename.substitutes_fixed (fixed _ List.mem_cons_self) head)
      (ih (fun term member => fixed term (List.mem_cons_of_mem _ member)))

theorem AtomRenaming.list_at (rename : AtomRenaming) {relation : Term → Term → Prop} {left right : List Term}
    (related : ∀ (index : Nat) first second, left[index]? = some first → right[index]? = some second →
      relation (rename.term first) (rename.term second)) :
    ∀ (index : Nat) first second, (left.map rename.term)[index]? = some first →
      (right.map rename.term)[index]? = some second → relation first second := by
  intro index first second leftAt rightAt
  rw [List.getElem?_map] at leftAt rightAt
  obtain ⟨a,atA,rfl⟩ := Option.map_eq_some_iff.mp leftAt
  obtain ⟨b,atB,rfl⟩ := Option.map_eq_some_iff.mp rightAt
  exact related index a b atA atB

theorem AtomRenaming.children_at (rename : AtomRenaming) {relation : Term → Term → Prop} {left right : Term}
    (related : ∀ (index : Nat) first second, left.children[index]? = some first → right.children[index]? = some second →
      relation (rename.term first) (rename.term second)) :
    ∀ (index : Nat) first second, (rename.term left).children[index]? = some first →
      (rename.term right).children[index]? = some second → relation first second := by
  rw [rename.children,rename.children]
  exact rename.list_at related

theorem RowEquivalent.renameAtoms {left right : Term} (equal : RowEquivalent left right) (rename : AtomRenaming) :
    RowEquivalent (rename.term left) (rename.term right) := by
  refine RowEquivalent.rec
    (motive_1 := fun left right _ => RowEquivalent (rename.term left) (rename.term right))
    (motive_2 := fun left right _ => ListRel RowEquivalent (left.map rename.term) (right.map rename.term))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ equal
  · intros; exact .refl
  · intro _ _ _ ih; exact .symm ih
  · intro _ _ _ _ _ first second; exact .trans first second
  · intro _ _ same _ children
    exact .congr (same.renameAtoms rename) (by simpa only [rename.children] using children)
  · intro _ _ _ _ instances tails
    simp only [AtomRenaming.term]
    exact .permutation (instances.map _) (tails.map _)
  · intros; simpa only [AtomRenaming.term,List.map_cons,List.map_append] using
      (RowEquivalent.flatten (instances := _) (tails := _) (nested := _) (nestedTails := _))
  · intro _ _ _ _ _ ih
    simp only [AtomRenaming.term,List.map_cons]
    exact .duplicate ih
  · intro _ _ _ _ _ ih
    simp only [AtomRenaming.term,List.map_cons]
    exact .tailDuplicate ih
  · exact .nil
  · intro _ _ _ _ _ _ head tail; exact .cons head tail

end Glorious.Language
