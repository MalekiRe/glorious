import GloriousLanguage.StorageTyping
import GloriousLanguage.TermScope

/-! Runtime relocation acts on generic arguments, not on immutable lexical
declarations. These laws connect the existing kinded substitution operation
to that action; no second instantiation relation is introduced. -/
namespace Glorious.Language

theorem ProgramWellFormed.lexical {program : Program} (valid : ProgramWellFormed program)
    {definition : Definition} (member : definition ∈ program.declarations) : definition.Lexical :=
  (valid.2.2.2.2.1 definition member).1.1

theorem ProgramWellFormed.field_lexical {program : Program} (valid : ProgramWellFormed program)
    {data : DataDefinition} {variant : VariantDefinition} {field : FieldDefinition}
    (found : program.data data.header.id = some data) (constructor : variant ∈ data.variants)
    (member : field ∈ variant.fields) : field.type.Lexical := by
  apply valid.lexical (List.mem_of_find?_eq_some (Program.data_lookup found))
  simp only [Definition.terms,List.mem_append,List.mem_map,List.mem_flatMap]
  exact Or.inl (Or.inl (Or.inl ⟨field,⟨variant,constructor,member⟩,rfl⟩))

namespace Execution

def Relocation.substitution (map : Relocation) (substitution : Substitution) : Substitution :=
  substitution.map (fun (id,value) => (id,map.term value))

theorem Relocation.term_kind (map : Relocation) (term : Term) :
    (map.term term).kind = term.kind := by
  cases term <;> simp only [Relocation.term,Term.renameRuntimeRegions,Term.kind]

theorem Relocation.term_children (map : Relocation) (term : Term) :
    (map.term term).children = term.children.map map.term := by
  cases term <;> simp only [Relocation.term,Term.renameRuntimeRegions,Term.children,List.map_cons,List.map_nil,List.map_append]

theorem Relocation.lexical_term (map : Relocation) (term : Term) (lexical : term.Lexical) :
    map.term term = term := by
  cases term <;> simp only [Relocation.term,Term.renameRuntimeRegions]
  case runtimeRegion id => exact False.elim (lexical.1 id .here)
  all_goals try rfl
  all_goals
    congr 1
    all_goals first
    | apply List.map_eq_self_of
      intro child member
      exact map.lexical_term child (lexical.child (by simp [Term.children,member]))
    | exact map.lexical_term _ (lexical.child (by simp [Term.children]))
termination_by term

theorem Relocation.occurs_preimage (map : Relocation) {needle term : Term}
    (occurs : Occurs needle (map.term term)) :
    ∃ original, Occurs original term ∧ map.term original = needle := by
  generalize renamed : map.term term = result at occurs
  induction occurs generalizing term with
  | here => exact ⟨term,.here,renamed⟩
  | @child parent child member nested ih =>
      rw [← renamed,map.term_children] at member
      obtain ⟨original,inOriginal,atChild⟩ := List.mem_map.mp member
      obtain ⟨ancestor,inside,atNeedle⟩ := ih atChild
      exact ⟨ancestor,.child inOriginal inside,atNeedle⟩

theorem Relocation.term_eq_parameter (map : Relocation) {term : Term} {id : Identity} {kind : Kind}
    (same : map.term term = .parameter id kind) : term = .parameter id kind := by
  cases term <;> simp only [Relocation.term,Term.renameRuntimeRegions] at same <;> cases same <;> rfl

theorem Relocation.term_substitute (map : Relocation) (substitution : Substitution) (term : Term) :
    map.term (term.substitute substitution) =
      (map.term term).substitute (map.substitution substitution) := by
  cases term <;> simp only [Term.substitute,Relocation.term,Term.renameRuntimeRegions]
  case parameter id kind =>
    rw [Relocation.substitution,Table.get_map_values]
    cases substitution.get id <;> simp only [Option.getD,Option.map,Relocation.term,Term.renameRuntimeRegions]
  all_goals try rfl
  all_goals try simp only [List.map_map,Function.comp_def]
  all_goals
    congr 1
    all_goals first
    | exact map.term_substitute substitution _
    | apply List.map_congr_left
      intro term member
      exact map.term_substitute substitution term
termination_by term

theorem Relocation.substitutes (map : Relocation) {substitution : Substitution} {before after : Term}
    (related : Substitutes substitution before after) :
    Substitutes (map.substitution substitution) (map.term before) (map.term after) := by
  refine ⟨by simpa only [map.term_kind] using related.1,?_,?_⟩
  · rw [related.2.1,map.term_substitute]
  · intro id kind value occurs found
    obtain ⟨original,nested,atParameter⟩ := map.occurs_preimage occurs
    have originalEq := map.term_eq_parameter atParameter
    subst original
    change Table.get (substitution.map (fun (id,term) => (id,map.term term))) id = some value at found
    rw [Table.get_map_values] at found
    obtain ⟨previous,selected,rfl⟩ := Option.map_eq_some_iff.mp found
    simpa only [map.term_kind] using related.2.2 id kind previous nested selected

theorem Relocation.substitutes_lexical (map : Relocation) {substitution : Substitution} {before after : Term}
    (lexical : before.Lexical) (related : Substitutes substitution before after) :
    Substitutes (map.substitution substitution) before (map.term after) := by
  simpa only [map.lexical_term before lexical] using map.substitutes related

theorem Relocation.substitutes_list (map : Relocation) {substitution : Substitution} {before after : List Term}
    (lexical : ∀ term ∈ before, term.Lexical) (related : ListRel (Substitutes substitution) before after) :
    ListRel (Substitutes (map.substitution substitution)) before (after.map map.term) := by
  induction related with
  | nil => exact .nil
  | cons first rest ih =>
      exact .cons (map.substitutes_lexical (lexical _ List.mem_cons_self) first)
        (ih (fun term member => lexical term (List.mem_cons_of_mem _ member)))

theorem Instantiates.relocate {binders : List Binder} {arguments : List Term} {substitution : Substitution}
    (instantiated : Instantiates binders arguments substitution) (map : Relocation) :
    Instantiates binders (arguments.map map.term) (map.substitution substitution) := by
  refine ⟨instantiated.1,?_,?_⟩
  · have kinds := instantiated.2.1
    clear instantiated
    induction kinds with
    | nil => exact .nil
    | cons head _ ih => exact .cons (by simpa only [map.term_kind] using head) ih
  · rw [instantiated.2.2]
    simp only [Relocation.substitution,List.zip_map_right]
    apply List.map_congr_left
    intro entry _
    cases entry
    rfl

theorem CallableFields.relocate {program : Program} (valid : ProgramWellFormed program)
    {id : DeclId} {arguments fields : List Term}
    (declared : CallableFields program id arguments fields) (map : Relocation) :
    CallableFields program id (arguments.map map.term) (fields.map map.term) := by
  cases declared with
  | function found instantiated substituted =>
      have lexical := valid.lexical (List.mem_of_find?_eq_some (Program.function_lookup found))
      exact .function found (Instantiates.relocate instantiated map) (map.substitutes_list (by
        intro term member
        exact lexical term (by simp only [Definition.terms,List.mem_append]; exact Or.inl (Or.inr member))) substituted)
  | operation found instantiated => exact .operation found (Instantiates.relocate instantiated map)

theorem ConstructorHead.relocate {program : Program} (valid : ProgramWellFormed program)
    {type : Term} {variant : Option DeclId} {fields : List Term} {head : ValueHead}
    (constructed : ConstructorHead program type variant fields head) (map : Relocation) :
    ConstructorHead program (map.term type) variant (fields.map map.term) head := by
  rcases constructed with ⟨rfl,rfl,rfl⟩ | ⟨element,sign,width,length,rfl,rfl,rfl,count,homogeneous⟩ |
    ⟨id,arguments,data,constructor,substitution,rfl,rfl,rfl,selected,instantiated,substituted⟩
  · exact Or.inl ⟨by simp only [Relocation.term,Term.renameRuntimeRegions],rfl,rfl⟩
  · refine Or.inr (Or.inl ⟨map.term element,sign,width,length,by simp only [Relocation.term,Term.renameRuntimeRegions],rfl,rfl,
      by simpa only [List.length_map] using count,?_⟩)
    intro field member
    obtain ⟨original,inOriginal,rfl⟩ := List.mem_map.mp member
    exact congrArg map.term (homogeneous original inOriginal)
  · refine Or.inr (Or.inr ⟨id,arguments.map map.term,data,constructor,map.substitution substitution,
      by simp only [Relocation.term,Term.renameRuntimeRegions],rfl,rfl,selected,Instantiates.relocate instantiated map,?_⟩)
    apply map.substitutes_list _ substituted
    intro term member
    obtain ⟨field,inFields,rfl⟩ := List.mem_map.mp member
    exact valid.field_lexical selected.1 selected.2.1 inFields

end Execution
end Glorious.Language
