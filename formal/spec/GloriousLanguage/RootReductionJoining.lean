import GloriousLanguage.DefinitionalCoherence

/-! The root/root critical-pair boundary reduces to joining the actual inferred
generic tables. Alias instantiation, GAT arguments, declaration identity, and
override/default exclusivity introduce no further joining obligation. This
module does not identify those generic joins with coherence's convertibility
witness and does not infer global confluence from local peaks. -/
namespace Glorious.Language

/-- A relation on the actual inferred generic tables propagates through every
root/root case whenever it composes through simultaneous substitution. The
relation may retain development information beyond a final common reduct. -/
theorem DefinitionalStep.root_related {program : Program} (valid : ProgramWellFormed program)
    {relation : Term → Term → Prop}
    {context : Context} {source left right : Term}
    (first : DefinitionalStep program context source left)
    (second : DefinitionalStep program context source right)
    (reflexive : ∀ term, relation term term)
    (substitutions : ∀ (term : Term) (first second : Substitution),
      ListRel (fun left right => left.1 = right.1 ∧ relation left.2 right.2) first second →
      relation (term.substitute first) (term.substitute second))
    (bindings : ∀ trait arguments first second firstSub secondSub,
      SelectsImpl program context trait arguments false first firstSub →
      SelectsImpl program context trait arguments false second secondSub →
      ListRel (fun left right => left.1 = right.1 ∧ relation left.2 right.2) firstSub secondSub) :
    relation left right := by
  have sameTable (substitution : Substitution) :
      ListRel (fun left right => left.1 = right.1 ∧ relation left.2 right.2) substitution substitution := by
    simpa only [List.map_id] using ListRel.maps substitution id id (fun _ _ => And.intro rfl (reflexive _))
  cases first with
  | alias found instantiated _ graph =>
    cases second with
    | alias otherFound otherInstantiated _ otherGraph =>
      obtain rfl := Option.some.inj (found.symm.trans otherFound)
      have tables := instantiated.2.2.trans otherInstantiated.2.2.symm
      rw [graph.2.1,otherGraph.2.1,tables]
      exact reflexive _
  | @projection _ _ _ _ _ associated _ _ _ _ _ _ domain selected bodyMember graph =>
    generalize sourceKind : associated.kind = kind at second
    cases second with
    | projection otherDomain otherSelected otherMember otherGraph =>
      obtain ⟨rfl,_,rfl⟩ := domain.unique otherDomain
      have joined := bindings _ _ _ _ _ _ selected otherSelected
      have declared := selected.declaration
      obtain rfl := selected.implementation_unique valid otherSelected
      obtain rfl := List.pair_value_unique (valid.associated_members_unique declared) bodyMember otherMember
      rw [graph.2.1,otherGraph.2.1]
      exact substitutions _ _ _ (joined.append (sameTable _))
    | defaultProjection _ otherSelected absent _ _ =>
      obtain rfl := selected.implementation_unique valid otherSelected
      exact False.elim (absent _ bodyMember)
  | @defaultProjection _ _ _ _ _ associated _ _ _ _ _ _ domain selected absent default graph =>
    generalize sourceKind : associated.kind = kind at second
    cases second with
    | projection _ otherSelected bodyMember _ =>
      obtain rfl := selected.implementation_unique valid otherSelected
      exact False.elim (absent _ bodyMember)
    | defaultProjection otherDomain _ _ otherDefault otherGraph =>
      obtain ⟨rfl,rfl,rfl⟩ := domain.unique otherDomain
      obtain rfl := Option.some.inj (default.symm.trans otherDefault)
      rw [graph.2.1,otherGraph.2.1]
      exact reflexive _

/-- Every pair of actual root expansions joins once its simultaneously
selected generic tables join. Only positive joining is propagated to bodies;
the declaration-identity consequence of coherence is used separately. -/
theorem DefinitionalStep.root_join {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {source left right : Term}
    (first : DefinitionalStep program context source left)
    (second : DefinitionalStep program context source right)
    (bindings : ∀ trait arguments first second firstSub secondSub,
      SelectsImpl program context trait arguments false first firstSub →
      SelectsImpl program context trait arguments false second secondSub →
      SubstitutionsJoinable program context firstSub secondSub) :
    DefinitionallyJoinable program context left right :=
  first.root_related valid second (fun term => ⟨term,.refl,.refl⟩)
    (fun term _ _ joined => SubstitutionsJoinable.substitute joined term) bindings

end Glorious.Language
