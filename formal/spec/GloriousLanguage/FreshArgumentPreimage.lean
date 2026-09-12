import GloriousLanguage.FreshAtomSpecialization

/-! Every caller-kinded argument has a fresh-rigid inspection preimage, even
when its parameters, scoped regions and scoped brands are absent from the
inspection context. Three disjoint arithmetic tags retain their identities;
decoding consumes only the actual caller binder and scope domains. -/
namespace Glorious.Language

namespace FreshArgumentPreimage

noncomputable def replacement (context : Context) (id : Identity) (kind : Kind) : Term :=
  open Classical in
  if id % 3 = 0 ∧ ∃ binder ∈ context.binders, binder.id = id / 3 ∧ binder.kind = kind then
    .parameter (id / 3) kind
  else if id % 3 = 1 ∧ kind = .region ∧ id / 3 ∈ context.scope.regions then
    .scopedRegion (id / 3)
  else if id % 3 = 2 ∧ kind = .brand ∧ id / 3 ∈ context.scope.brands then
    .scopedBrand (id / 3)
  else .rigid id kind context.universeLevel

theorem replacement_kinded (program : Program) (context : Context) (id : Identity) (kind : Kind) :
    Kinding program context (replacement context id kind) kind := by
  unfold replacement
  split
  · rename_i selected
    obtain ⟨binder,member,sameId,sameKind⟩ := selected.2
    simpa only [sameId,sameKind] using Kinding.parameter (program := program) member
  · split
    · rename_i selected
      rw [selected.2.1]
      exact .scopedRegion selected.2.2
    · split
      · rename_i selected
        rw [selected.2.1]
        exact .scopedBrand selected.2.2
      · exact .rigid (Nat.le_refl _)

theorem replacement_kind (context : Context) (id : Identity) (kind : Kind) :
    (replacement context id kind).kind = kind := by
  unfold replacement
  split
  · rfl
  · split
    · rename_i selected
      exact selected.2.1.symm
    · split
      · rename_i selected
        exact selected.2.1.symm
      · rfl

noncomputable def specialization (context : Context) : FreshAtomSpecialization where
  cutoff := context.universeLevel
  rigid := replacement context
  rigid_kind := replacement_kind context

theorem admitted (program : Program) (context : Context) : (specialization context).Admitted program context :=
  ⟨rfl,replacement_kinded program context⟩

theorem replacement_parameter {context : Context} {id : Identity} {kind : Kind}
    (present : ∃ binder ∈ context.binders, binder.id = id ∧ binder.kind = kind) :
    replacement context (3 * id) kind = .parameter id kind := by
  have quotient : 3 * id / 3 = id := by simp only [Identity] at *; omega
  have remainder : 3 * id % 3 = 0 := by simp only [Identity] at *; omega
  unfold replacement
  rw [if_pos (by simpa only [quotient,remainder,true_and] using present),quotient]

theorem replacement_region {context : Context} {id : Identity} (present : id ∈ context.scope.regions) :
    replacement context (3 * id + 1) .region = .scopedRegion id := by
  have quotient : (3 * id + 1) / 3 = id := by simp only [Identity] at *; omega
  have remainder : (3 * id + 1) % 3 = 1 := by simp only [Identity] at *; omega
  simp only [replacement,remainder,Nat.one_ne_zero,false_and,if_false,quotient,
    true_and,if_pos present]

theorem replacement_brand {context : Context} {id : Identity} (present : id ∈ context.scope.brands) :
    replacement context (3 * id + 2) .brand = .scopedBrand id := by
  have quotient : (3 * id + 2) / 3 = id := by simp only [Identity] at *; omega
  have remainder : (3 * id + 2) % 3 = 2 := by simp only [Identity] at *; omega
  simp only [replacement,remainder,show ¬(2 : Nat) = 0 by decide,show ¬(2 : Nat) = 1 by decide,
    false_and,if_false,quotient,true_and,if_pos present]

def term (level : Nat) : Term → Term
  | .parameter id kind => .rigid (3 * id) kind level
  | .scopedRegion id => .rigid (3 * id + 1) .region level
  | .scopedBrand id => .rigid (3 * id + 2) .brand level
  | .tuple fields => .tuple (fields.map (term level))
  | .array a b => .array (term level a) (term level b)
  | .reference mode a b => .reference mode (term level a) (term level b)
  | .rawPointer mode a => .rawPointer mode (term level a)
  | .nominal id arguments => .nominal id (arguments.map (term level))
  | .alias id arguments => .alias id (arguments.map (term level))
  | .callable id arguments => .callable id (arguments.map (term level))
  | .continuation a b c d q => .continuation (term level a) (term level b) (term level c) (term level d) q
  | .label a b c => .label (term level a) (term level b) (term level c)
  | .environment a b residents => .environment (term level a) (term level b) (residents.map (term level))
  | .available a b residents => .available (term level a) (term level b) (residents.map (term level))
  | .bindings a b arguments => .bindings (term level a) (term level b) (arguments.map (term level))
  | .effect id arguments => .effect id (arguments.map (term level))
  | .row instances tails => .row (instances.map (term level)) (tails.map (term level))
  | .projection trait member owners items kind => .projection trait member (owners.map (term level)) (items.map (term level)) kind
  | .constantTuple fields => .constantTuple (fields.map (term level))
  | .constantConstructor id arguments fields => .constantConstructor id (arguments.map (term level)) (fields.map (term level))
  | other => other

theorem shape (level : Nat) (value : Term) : term level value = match value with
    | .parameter id kind => term level (.parameter id kind)
    | .rigid id kind atomLevel => term level (.rigid id kind atomLevel)
    | .variable id kind atomLevel => term level (.variable id kind atomLevel)
    | .runtimeRegion id => term level (.runtimeRegion id)
    | .scopedRegion id => term level (.scopedRegion id)
    | .scopedBrand id => term level (.scopedBrand id)
    | other => other.mapChildren (term level) := by
  cases value <;> simp only [term,Term.mapChildren]

theorem kind (level : Nat) (value : Term) : (term level value).kind = value.kind := by
  cases value <;> simp only [term,Term.kind]

theorem kinded {program : Program} {caller source : Context} {value : Term} {kind : Kind}
    (typed : Kinding program caller value kind) {level : Nat} (bounded : level ≤ source.universeLevel)
    (higher : caller.universeLevel ≤ source.universeLevel) : Kinding program source (term level value) kind := by
  apply typed.map_scoped_atoms (term level) (shape level)
  intro atom occurs
  cases atom <;> try exact True.intro
  case parameter => simpa only [term] using Kinding.rigid (program := program) bounded
  case scopedRegion => simpa only [term] using Kinding.rigid (program := program) bounded
  case scopedBrand => simpa only [term] using Kinding.rigid (program := program) bounded
  case rigid => simpa only [term] using Kinding.rigid (program := program) (Nat.le_trans (typed.rigid_level occurs) higher)
  case «variable» => simpa only [term] using Kinding.variable (program := program) (Nat.le_trans (typed.variable_level occurs) higher)
  case runtimeRegion => simpa only [term] using Kinding.runtimeRegion (program := program)

theorem roundtrip {program : Program} {context : Context} {value : Term} {kind : Kind}
    (typed : Kinding program context value kind) {level : Nat} (fresh : context.universeLevel < level) :
    (specialization context).term (term level value) = value := by
  have children : ∀ child ∈ value.children, (specialization context).term (term level child) = child := by
    intro child member
    obtain ⟨childKind,childTyped⟩ := typed.child member
    exact roundtrip childTyped fresh
  cases value
  case parameter id parameterKind =>
    simp only [term,FreshAtomSpecialization.term,specialization,if_pos fresh]
    exact replacement_parameter (typed.parameter_occurs .here)
  case scopedRegion id =>
    simp only [term,FreshAtomSpecialization.term,specialization,if_pos fresh]
    exact replacement_region (typed.scoped.1 id .here)
  case scopedBrand id =>
    simp only [term,FreshAtomSpecialization.term,specialization,if_pos fresh]
    exact replacement_brand (typed.scoped.2 id .here)
  case rigid => simpa only [term] using (specialization context).fixed rfl typed
  case «variable» => simpa only [term] using (specialization context).fixed rfl typed
  all_goals simp only [term,FreshAtomSpecialization.term,List.map_map,Function.comp_def]
  all_goals try rfl
  all_goals simp only [Term.children,List.mem_append,List.mem_cons,List.not_mem_nil] at children
  all_goals congr 1
  all_goals first
  | apply List.map_eq_self_of
    intro child member
    exact children child (by simp [member])
  | exact children _ (by simp)
termination_by value
decreasing_by exact Term.child_sizeOf member

/-- The inverse has no lexical parameters. This follows from the same
kinding transport into an empty binder domain, not a second syntax walk. -/
theorem no_parameters {program : Program} {context : Context} {value : Term} {kind : Kind}
    (typed : Kinding program context value kind) (level : Nat) :
    ∀ id parameterKind, ¬ Occurs (.parameter id parameterKind) (term level value) := by
  have closed : Kinding program
      { context with binders := [], universeLevel := max level context.universeLevel }
      (term level value) kind := kinded typed (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  intro id parameterKind occurs
  obtain ⟨binder,member,_,_⟩ := closed.parameter_occurs occurs
  exact List.not_mem_nil member

/-- Concrete contravariant quantifier domain transport. No relation between
source and caller binders or scopes is required; the fresh source universe
alone supplies parameter-free preimages of all caller-kinded terms. -/
theorem preimage {program : Program} {caller source : Context} {value : Term} {kind : Kind}
    (typed : Kinding program caller value kind) (higher : caller.universeLevel < source.universeLevel) :
    ∃ original, Kinding program source original kind ∧
      (specialization caller).term original = value ∧
      ∀ id parameterKind, ¬ Occurs (.parameter id parameterKind) original :=
  ⟨term source.universeLevel value,kinded typed (Nat.le_refl _) (Nat.le_of_lt higher),
    roundtrip typed higher,no_parameters typed _⟩

end FreshArgumentPreimage
end Glorious.Language
