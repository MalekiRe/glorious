import GloriousLanguage.PredicateKinding
import GloriousLanguage.PredicateAlpha

/-! Kind preservation for the actual capture-avoiding predicate substitution,
including ordered defaults and recursively freshened quantified requirements.
Intermediate proof contexts retain exactly the relevant source parameters;
they are not a second source of declaration or runtime facts. -/
namespace Glorious.Language

private def renamedContext (context : Context) (support : List Identity) (rename : Identity → Identity) : Context :=
  { context with binders := (context.binders.filter (fun binder => decide (binder.id ∈ support))).map (Binder.renameParameters rename) }

private theorem renamedContext.parameter {program : Program} {context : Context} {support : List Identity}
    {binder : Binder} (rename : Identity → Identity) (member : binder ∈ context.binders)
    (supported : binder.id ∈ support) :
    Kinding program (renamedContext context support rename) (.parameter (rename binder.id) binder.kind) binder.kind := by
  have retained : binder.renameParameters rename ∈ (renamedContext context support rename).binders := by
    exact List.mem_map.mpr ⟨binder,List.mem_filter.mpr ⟨member,by simpa⟩,rfl⟩
  exact Kinding.parameter retained

private theorem Kinding.renameSupported {program : Program} {context : Context} {term : Term} {kind : Kind}
    (kinded : Kinding program context term kind) (support : List Identity) (rename : Identity → Identity)
    (used : ∀ id ∈ term.parameterIds, id ∈ support) :
    Kinding program (renamedContext context support rename) (term.renameParameters rename) kind :=
  kinded.renameParameters_supported rename used (fun _ member supported => renamedContext.parameter rename member supported)
    (Nat.le_refl _) (fun _ member => member) (fun _ member => member)

private theorem ConstraintKinded.renameSupported {program : Program} {context : Context} {constraint : Constraint}
    (kinded : ConstraintKinded program context constraint) (support : List Identity) (rename : Identity → Identity)
    (used : ∀ id ∈ constraint.parameterIds, id ∈ support)
    (injective : ∀ left ∈ support, ∀ right ∈ support, rename left = rename right → left = right) :
    ConstraintKinded program (renamedContext context support rename) (constraint.renameParameters rename) :=
  kinded.renameParameters rename used injective (fun _ member supported => renamedContext.parameter rename member supported)
    (Nat.le_refl _) (fun _ member => member) (fun _ member => member)

private theorem Table.get_filter_key {α : Type} (table : Table α) (selected : Identity → Bool) (id : Identity)
    (retained : selected id = true) :
    Table.get (table.filter (fun entry => selected entry.1)) id = table.get id := by
  induction table with
  | nil => rfl
  | cons first rest ih =>
    by_cases same : first.1 = id
    · simp [Table.get,same,retained]
    · by_cases keep : selected first.1 = true
      · simpa [Table.get,same,keep] using ih
      · simpa [Table.get,same,keep] using ih

private theorem Table.get_none_of_absent {α : Type} {table : Table α} {id : Identity}
    (absent : ∀ entry ∈ table, entry.1 ≠ id) : table.get id = none := by
  cases found : table.get id with
  | none => rfl
  | some value =>
    obtain ⟨entry,located,_⟩ := Option.map_eq_some_iff.mp found
    exact False.elim (absent entry (List.mem_of_find?_eq_some located) (by simpa using List.find?_some located))

private theorem ListRel.member_right {α β : Type} {relation : α → β → Prop} {left : List α} {right : List β}
    (related : ListRel relation left right) {value : β} (member : value ∈ right) :
    ∃ original ∈ left, relation original value := by
  induction related with
  | nil => cases member
  | @cons first last left right head _ ih =>
    rcases List.mem_cons.mp member with rfl | present
    · exact ⟨first,List.mem_cons_self,head⟩
    · obtain ⟨original,inLeft,paired⟩ := ih present
      exact ⟨original,List.mem_cons_of_mem _ inLeft,paired⟩

private theorem ListRel.take {α β : Type} {relation : α → β → Prop} {left : List α} {right : List β}
    (related : ListRel relation left right) (count : Nat) : ListRel relation (left.take count) (right.take count) := by
  induction related generalizing count with
  | nil => simp only [List.take_nil]; exact .nil
  | cons head _ ih =>
    cases count with
    | zero => exact .nil
    | succ count => exact .cons head (ih count)

private theorem ListRel.mapIdx_binders (binders : List Binder) (transform : Nat → Binder → Binder)
    (rename : Identity → Identity)
    (fields : ∀ index binder, binder ∈ binders →
      (transform index binder).id = rename binder.id ∧ (transform index binder).kind = binder.kind) :
    ListRel (fun before after => after.id = rename before.id ∧ after.kind = before.kind) binders (binders.mapIdx transform) := by
  induction binders generalizing transform with
  | nil => exact .nil
  | cons first rest ih =>
    simp only [List.mapIdx_cons]
    exact .cons (fields 0 first List.mem_cons_self)
      (ih (fun index binder => transform (index + 1) binder)
        (fun index binder member => fields (index + 1) binder (List.mem_cons_of_mem _ member)))

private theorem ListRel.imp_of_mem {α β : Type} {first second : α → β → Prop} {left : List α} {right : List β}
    (related : ListRel first left right)
    (implies : ∀ a ∈ left, ∀ b ∈ right, first a b → second a b) : ListRel second left right := by
  induction related with
  | nil => exact .nil
  | cons head _ ih =>
    exact .cons (implies _ List.mem_cons_self _ List.mem_cons_self head)
      (ih (fun a member b present => implies a (List.mem_cons_of_mem _ member) b (List.mem_cons_of_mem _ present)))

private theorem ListRel.map_eq {α β γ : Type} {relation : α → β → Prop} {left : List α} {right : List β}
    (related : ListRel relation left right) (f : α → γ) (g : β → γ)
    (equal : ∀ a b, relation a b → f a = g b) : left.map f = right.map g := by
  induction related with
  | nil => rfl
  | cons head _ ih => simp only [List.map_cons,equal _ _ head,ih]

/-- The real fresh seed excludes both keys and the entire lexical support of
all inserted caller values. Masking the source binder prefix cannot introduce
a lookup at one of the generated fresh identities. -/
private theorem fresh_lookup_none (constraint : Constraint) (substitution : Substitution)
    (binders : List Binder) {binder : Binder} (member : binder ∈ binders) :
    Table.get (substitution.filter (fun entry => !(binders.any (fun bound => bound.id == entry.1))))
      (Binder.freshRename binders (constraint.freshSeed substitution) binder.id) = none := by
  apply Table.get_none_of_absent
  intro entry present same
  have smaller := Substitution.parameter_lt_freshSeed constraint substitution
    (List.mem_flatMap.mpr ⟨entry,(List.mem_filter.mp present).1,List.mem_cons_self⟩)
  rw [same,Binder.freshRename_member member] at smaller
  exact Nat.not_lt_of_ge (Nat.le_add_right _ _) smaller

/-- Parameter evidence for the recursively renamed source context is derived
from the actual caller substitution and actual output binders. Neither an
unused caller-name freshness premise nor a post-substitution kind certificate
is required. -/
private theorem fresh_parameters {program : Program} {source target : Context}
    (constraint : Constraint) (substitution : Substitution) {binders afterBinders : List Binder}
    (paired : ListRel (fun before after =>
      after.id = Binder.freshRename binders (constraint.freshSeed substitution) before.id ∧ after.kind = before.kind)
      binders afterBinders)
    (parameters : ∀ binder ∈ source.binders,
      Kinding program target ((Term.parameter binder.id binder.kind).substitute substitution) binder.kind) :
    ∀ binder ∈ (renamedContext (source.bindParameters binders) constraint.parameterIds
      (Binder.freshRename binders (constraint.freshSeed substitution))).binders,
      Kinding program (target.bindParameters afterBinders)
        ((Term.parameter binder.id binder.kind).substitute
          (substitution.filter (fun entry => !(binders.any (fun bound => bound.id == entry.1))))) binder.kind := by
  intro renamed member
  obtain ⟨original,filtered,rfl⟩ := List.mem_map.mp member
  obtain ⟨member,supported⟩ := List.mem_filter.mp filtered
  have supported : original.id ∈ constraint.parameterIds := by simpa using supported
  change original ∈ binders ++ source.binders.filter _ at member
  rcases List.mem_append.mp member with inBound | outer
  · obtain ⟨afterBinder,afterMember,sameId,sameKind⟩ := paired.member_left inBound
    have found : afterBinder ∈ (target.bindParameters afterBinders).binders := List.mem_append_left _ afterMember
    have kinded := Kinding.parameter (program := program) found
    simp only [Binder.renameParameters,Term.substitute,fresh_lookup_none constraint substitution binders inBound,
      Option.getD_none]
    simpa only [sameId,sameKind] using kinded
  · obtain ⟨outer,unshadowed⟩ := List.mem_filter.mp outer
    change (!(binders.any (fun inner => inner.id == original.id))) = true at unshadowed
    have absent : original.id ∉ binders.map (·.id) := by
      intro present
      obtain ⟨inner,inBinders,equal⟩ := List.mem_map.mp present
      simp only [Bool.not_eq_true',List.any_eq_false,beq_iff_eq] at unshadowed
      exact unshadowed inner inBinders equal
    have lookup := Table.get_filter_key substitution
      (fun id => !(binders.any (fun inner => inner.id == id))) original.id unshadowed
    have retained := (parameters original outer).bindParameters afterBinders (by
      intro afterBinder present
      obtain ⟨inner,inBinders,sameId,_⟩ := paired.member_right present
      rw [sameId,Binder.freshRename_member inBinders]
      simp only [Term.substitute]
      cases found : substitution.get original.id with
      | none =>
        simp only [Option.getD_none,Term.parameterIds,List.mem_singleton]
        intro equal
        have smaller := Constraint.parameter_lt_freshSeed constraint substitution supported
        rw [← equal] at smaller
        exact Nat.not_lt_of_ge (Nat.le_add_right _ _) smaller
      | some value =>
        simp only [Option.getD_some]
        intro occurs
        obtain ⟨entry,located,equal⟩ := Option.map_eq_some_iff.mp found
        have smaller := Substitution.parameter_lt_freshSeed constraint substitution
          (List.mem_flatMap.mpr ⟨entry,List.mem_of_find?_eq_some located,
            List.mem_cons_of_mem _ (equal.symm ▸ occurs)⟩)
        exact Nat.not_lt_of_ge (Nat.le_add_right _ _) smaller)
    simpa only [Binder.renameParameters,Term.substitute,Binder.freshRename_not_mem absent,lookup] using retained

/-- Every kind-admitted predicate stays kind-admitted after the actual
capture-avoiding operation. This includes freshening nested binders before
inserting caller values and masking each default at its own lexical prefix. -/
theorem ConstraintKinded.substitute {program : Program} {source target : Context} {constraint : Constraint}
    (kinded : ConstraintKinded program source constraint) (substitution : Substitution)
    (parameters : ∀ binder ∈ source.binders,
      Kinding program target ((Term.parameter binder.id binder.kind).substitute substitution) binder.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands) :
    ConstraintKinded program target (constraint.substitute substitution) := by
  cases kinded <;> simp only [Constraint.substitute]
  case equal left right =>
    exact .equal (left.substitute substitution parameters levels regions brands)
      (right.substitute substitution parameters levels regions brands)
  case outlives long short =>
    exact .outlives (long.substitute substitution parameters levels regions brands)
      (short.substitute substitution parameters levels regions brands)
  case typeOutlives type region =>
    exact .typeOutlives (type.substitute substitution parameters levels regions brands)
      (region.substitute substitution parameters levels regions brands)
  case rowIncludes allowed required =>
    exact .rowIncludes (allowed.substitute substitution parameters levels regions brands)
      (required.substitute substitution parameters levels regions brands)
  case implements found instantiated arguments =>
    have mapped := fun term member => (arguments term member).substitute substitution parameters levels regions brands
    exact .implements found (instantiated.map_kind _ (fun term member => (mapped term member).term_kind)) (by
      intro term member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      rw [(mapped original present).term_kind]
      exact mapped original present)
  case use quantity type => exact .use (type.substitute substitution parameters levels regions brands) quantity
  case callable receiver arguments result effects =>
    apply ConstraintKinded.callable (receiver.substitute substitution parameters levels regions brands)
      _ (result.substitute substitution parameters levels regions brands)
      (effects.substitute substitution parameters levels regions brands)
    intro term member
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
    exact (arguments original present).substitute substitution parameters levels regions brands
  case runsIn receiver access arguments after =>
    apply ConstraintKinded.runsIn (receiver.substitute substitution parameters levels regions brands)
      (access.substitute substitution parameters levels regions brands)
      _ (after.substitute substitution parameters levels regions brands)
    intro term member
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
    exact (arguments original present).substitute substitution parameters levels regions brands
  case quantified binders requirements unique defaults requirementsKinded =>
    let predicate := Constraint.quantified binders requirements
    let seed := predicate.freshSeed substitution
    let rename := Binder.freshRename binders seed
    let transform := fun (index : Nat) (binder : Binder) => { binder with
      id := rename binder.id
      defaultValue := binder.defaultValue.map (fun (value : Term) =>
        (value.renameParameters (Binder.freshRename (binders.take index) seed)).substitute
          (substitution.filter (fun entry => !((binders.take index).any (fun binder => binder.id == entry.1))))) }
    let afterBinders := binders.mapIdx transform
    have paired : ListRel (fun before after => after.id = rename before.id ∧ after.kind = before.kind) binders afterBinders :=
      ListRel.mapIdx_binders binders transform rename (fun _ _ _ => ⟨rfl,rfl⟩)
    apply ConstraintKinded.quantified
    · have identities := paired.map_eq (fun binder => rename binder.id) Binder.id (fun _ _ related => related.1.symm)
      rw [← identities]
      have distinct : ((binders.map Binder.id).map rename).Nodup := by
        apply List.pairwise_map.mpr
        apply List.Pairwise.imp_of_mem _ unique
        intro left right leftMember rightMember different equal
        obtain ⟨first,firstMember,rfl⟩ := List.mem_map.mp leftMember
        obtain ⟨second,secondMember,rfl⟩ := List.mem_map.mp rightMember
        exact different (Binder.freshRename_injective_on firstMember secondMember equal)
      simpa only [List.map_map,Function.comp_def] using distinct
    · intro index binder value found default
      change afterBinders[index]? = some binder at found
      rw [List.getElem?_mapIdx] at found
      obtain ⟨original,originalFound,rfl⟩ := Option.map_eq_some_iff.mp found
      obtain ⟨originalValue,originalDefault,rfl⟩ := Option.map_eq_some_iff.mp default
      have prefixPair : ListRel (fun before after =>
          after.id = Binder.freshRename (binders.take index) seed before.id ∧ after.kind = before.kind)
          (binders.take index) (afterBinders.take index) := by
        apply (paired.take index).imp_of_mem
        intro before present after _ related
        refine ⟨?_,related.2⟩
        rw [related.1]
        simp only [rename,Binder.freshRename_member (List.mem_of_mem_take present),Binder.freshRename_member present]
      have renamed := (defaults index original originalValue originalFound originalDefault).renameSupported
        predicate.parameterIds (Binder.freshRename (binders.take index) seed) (by
          intro id member
          apply Constraint.parameterIds_term (term := originalValue) _ member
          simp only [predicate,Constraint.terms]
          exact List.mem_append_left _ (List.mem_flatMap.mpr
            ⟨original,List.mem_of_getElem? originalFound,by simp [originalDefault]⟩))
      exact renamed.substitute _ (fresh_parameters predicate substitution prefixPair parameters) levels regions brands
    · intro requirement member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      have renamed := (requirementsKinded original.val original.property).renameSupported predicate.parameterIds rename
        (fun id member => Constraint.parameterIds_requirement original.property member)
        (fun left leftMember right rightMember equal => Binder.freshRename_below_injective binders seed
          (predicate.parameter_lt_freshSeed substitution leftMember)
          (predicate.parameter_lt_freshSeed substitution rightMember) equal)
      have smaller : original.val.quantifierCount < predicate.quantifierCount := by
        have bound := List.nat_le_sum_of_mem (List.mem_map.mpr ⟨_,original.property,rfl⟩ :
          original.val.quantifierCount ∈ requirements.map Constraint.quantifierCount)
        simp only [predicate,Constraint.quantifierCount]
        omega
      exact renamed.substitute _ (fresh_parameters predicate substitution paired parameters) levels regions brands
termination_by constraint.quantifierCount
decreasing_by
  subst_vars
  simpa only [Constraint.quantifierCount_renameParameters] using smaller

private theorem masked_parameter_kinds {context : Context} (substitution : Substitution) (binders : List Binder)
    (parameters : ∀ binder ∈ context.binders, ∀ value,
      substitution.get binder.id = some value → value.kind = binder.kind) :
    ∀ binder ∈ (context.bindParameters binders).binders, ∀ value,
      Table.get (substitution.filter (fun entry => !(binders.any (fun bound => bound.id == entry.1)))) binder.id = some value →
        value.kind = binder.kind := by
  intro binder member value found
  change binder ∈ binders ++ context.binders.filter _ at member
  rcases List.mem_append.mp member with inBound | outer
  · have absent : Table.get (substitution.filter (fun entry => !(binders.any (fun bound => bound.id == entry.1)))) binder.id = none := by
      apply Table.get_none_of_absent
      intro entry present same
      have retained := (List.mem_filter.mp present).2
      simp only [Bool.not_eq_true',List.any_eq_false,beq_iff_eq] at retained
      exact retained binder inBound same.symm
    rw [absent] at found
    cases found
  · obtain ⟨member,unshadowed⟩ := List.mem_filter.mp outer
    have lookup := Table.get_filter_key substitution
      (fun id => !(binders.any (fun bound => bound.id == id))) binder.id unshadowed
    rw [lookup] at found
    exact parameters binder member value found

/-- The graph's recursive kind checks are derived under the same full-body
and ordered-default masks as the actual operation. Capture avoidance itself
is supplied by freshening, not by rejecting colliding caller names. -/
theorem ConstraintKinded.substitutionAdmissible {program : Program} {context : Context} {constraint : Constraint}
    (kinded : ConstraintKinded program context constraint) (substitution : Substitution)
    (parameters : ∀ binder ∈ context.binders, ∀ value,
      substitution.get binder.id = some value → value.kind = binder.kind) :
    constraint.SubstitutionAdmissible substitution := by
  revert parameters
  induction kinded generalizing substitution <;> intro parameters
  all_goals simp only [Constraint.SubstitutionAdmissible]
  case equal left right => exact ⟨left.substitutes_kinds substitution parameters,right.substitutes_kinds substitution parameters⟩
  case outlives long short => exact ⟨long.substitutes_kinds substitution parameters,short.substitutes_kinds substitution parameters⟩
  case typeOutlives type region => exact ⟨type.substitutes_kinds substitution parameters,region.substitutes_kinds substitution parameters⟩
  case rowIncludes allowed required => exact ⟨allowed.substitutes_kinds substitution parameters,required.substitutes_kinds substitution parameters⟩
  case implements _ _ arguments => exact fun term member => (arguments term member).substitutes_kinds substitution parameters
  case use type _ => exact type.substitutes_kinds substitution parameters
  case callable receiver arguments result effects =>
    intro term member
    rcases List.mem_cons.mp member with rfl | member
    · exact receiver.substitutes_kinds substitution parameters
    rcases List.mem_cons.mp member with rfl | member
    · exact result.substitutes_kinds substitution parameters
    rcases List.mem_cons.mp member with rfl | member
    · exact effects.substitutes_kinds substitution parameters
    exact (arguments term member).substitutes_kinds substitution parameters
  case runsIn receiver access arguments after =>
    intro term member
    rcases List.mem_cons.mp member with rfl | member
    · exact receiver.substitutes_kinds substitution parameters
    rcases List.mem_cons.mp member with rfl | member
    · exact access.substitutes_kinds substitution parameters
    rcases List.mem_cons.mp member with rfl | member
    · exact after.substitutes_kinds substitution parameters
    exact (arguments term member).substitutes_kinds substitution parameters
  case quantified binders _ _ defaults _ ih =>
    constructor
    · intro index binder found value default
      exact (defaults index binder value found default).substitutes_kinds _
        (masked_parameter_kinds substitution (binders.take index) parameters)
    · intro requirement member
      exact ih requirement member _ (masked_parameter_kinds substitution binders parameters)

/-- A real source kinding derivation and caller parameter interpretations
produce both the authoritative substitution graph and the kinding of its
actual hygienic result. -/
theorem ConstraintKinded.substitutes {program : Program} {source target : Context} {constraint : Constraint}
    (kinded : ConstraintKinded program source constraint) (substitution : Substitution)
    (parameters : ∀ binder ∈ source.binders,
      Kinding program target ((Term.parameter binder.id binder.kind).substitute substitution) binder.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands) :
    SubstituteConstraint substitution constraint (constraint.substitute substitution) ∧
      ConstraintKinded program target (constraint.substitute substitution) := by
  refine ⟨⟨kinded.substitutionAdmissible substitution ?_,rfl⟩,
    kinded.substitute substitution parameters levels regions brands⟩
  intro binder member value found
  have typed := parameters binder member
  simpa only [Term.substitute,found,Option.getD_some] using typed.term_kind

theorem ConstraintKinded.instantiate {program : Program} {source target : Context} {constraint : Constraint}
    (kinded : ConstraintKinded program source constraint) {arguments : List Term} {substitution : Substitution}
    (instantiated : Instantiates source.binders arguments substitution)
    (argumentsKinded : ∀ argument ∈ arguments, Kinding program target argument argument.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands) :
    SubstituteConstraint substitution constraint (constraint.substitute substitution) ∧
      ConstraintKinded program target (constraint.substitute substitution) :=
  kinded.substitutes substitution (instantiated.kinding_parameters argumentsKinded) levels regions brands

/-- Universal elimination uses its source predicate admission and the real
ordered binder instance. Free outer parameters remain in the caller context;
only locally bound parameters are replaced by the supplied values. -/
theorem ConstraintKinded.quantified_instance {program : Program} {context : Context}
    {binders : List Binder} {requirements : List Constraint} {arguments : List Term}
    {substitution : Substitution} {requirement : Constraint}
    (kinded : ConstraintKinded program context (.quantified binders requirements))
    (instantiated : Instantiates binders arguments substitution)
    (argumentsKinded : ∀ argument ∈ arguments, Kinding program context argument argument.kind)
    (member : requirement ∈ requirements) :
    SubstituteConstraint substitution requirement (requirement.substitute substitution) ∧
      ConstraintKinded program context (requirement.substitute substitution) := by
  cases kinded with
  | quantified _ _ requirementsKinded =>
    apply (requirementsKinded requirement member).substitutes (target := context) substitution _ (Nat.le_refl _)
      (fun _ member => member) (fun _ member => member)
    intro binder present
    change binder ∈ binders ++ context.binders.filter _ at present
    rcases List.mem_append.mp present with inBound | outer
    · exact instantiated.kinding_parameters argumentsKinded binder inBound
    · obtain ⟨outer,unshadowed⟩ := List.mem_filter.mp outer
      have absent : substitution.get binder.id = none := by
        apply Table.get_none_of_absent
        intro entry present equal
        rw [instantiated.2.2] at present
        obtain ⟨inner,inBinders,same⟩ := List.mem_map.mp (List.of_mem_zip present).1
        change (!(binders.any (fun inner => inner.id == binder.id))) = true at unshadowed
        simp only [Bool.not_eq_true',List.any_eq_false,beq_iff_eq] at unshadowed
        exact unshadowed inner inBinders (same.trans equal)
      simpa only [Term.substitute,absent,Option.getD_none] using Kinding.parameter (program := program) outer

end Glorious.Language
