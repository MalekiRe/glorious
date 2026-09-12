import GloriousLanguage.ScopedAtomTransport
import GloriousLanguage.SourceInterpretation

/-! Reading a source typing context at its actual runtime image.

The runtime context `Execution.Context.static` is the assumption-free physical
context `⟨[],[],0,module,unsafeAllowed,{}⟩`, so the runtime image of a source
context is *derived* from what an actual invocation provides: the actual scope
decoding that closes the two executable lexical atoms, the actual kinding domain
of the decoded terms, and the actual reading of the source context's own logical
evidence (its lexical assumptions and the declaration requirements its
implementation selections consume) at the runtime image. `ScopeReading` below is
that evidence; it is indexed by the actual source context the invocation entered,
so it is not a law about arbitrary contexts and no `SourceInterpreted` or
`ProjectionStepConversion` obligation is supplied in its place.

This module proves the ordered-constructor and declaration-fixedness facts the
image consumes. The definitional-step image itself - including the alias
expansions *and* the associated projection/defaultProjection steps, whose runtime
derivations are rebuilt from the transported `ProjectionDomain`, `SelectsImpl`,
`MatchesImplHead` and substitution graph - is stated as the remaining obligation
at the end of the file. -/
namespace Glorious.Language

set_option linter.unusedSimpArgs false in
/-- The scope map is a homomorphism on ordered constructors, including at the
two executable lexical atoms it closes. -/
theorem ScopeInstantiation.head (scope : ScopeInstantiation) (term : Term) :
    (scope.term term).mapChildren (fun _ => .unit) = scope.term (term.mapChildren (fun _ => .unit)) := by
  cases term <;> simp only [Term.mapChildren,ScopeInstantiation.term]
  case scopedRegion id => cases h : scope.regions.get id <;> simp only [Option.map,Option.getD] <;> try rfl
  case scopedBrand id => cases h : scope.brands.get id <;> simp only [Option.map,Option.getD] <;> try rfl
  all_goals (try simp only [ScopeInstantiation.term,List.map_map,List.map_append,Function.comp_def]) <;> try rfl

set_option linter.unusedSimpArgs false in
/-- The ordered children of a decoded term are the decoded children. -/
theorem ScopeInstantiation.children (scope : ScopeInstantiation) (term : Term) :
    (scope.term term).children = term.children.map scope.term := by
  cases term <;> simp only [Term.children,ScopeInstantiation.term]
  case scopedRegion id => cases h : scope.regions.get id <;> simp only [Option.map,Option.getD] <;> try rfl
  case scopedBrand id => cases h : scope.brands.get id <;> simp only [Option.map,Option.getD] <;> try rfl
  all_goals (try simp only [List.map_append,List.map_map,Function.comp_def,ScopeInstantiation.term]) <;> try rfl

/-- Same-head source terms keep the same head at the runtime image: both sides
are decoded by the same constructor-preserving atom action. -/
theorem SameHead.scopedAtoms {scope : ScopeInstantiation} {left right : Term} (same : SameHead left right) :
    SameHead (scope.term left) (scope.term right) := by
  unfold SameHead at same ⊢
  rw [ScopeInstantiation.head,ScopeInstantiation.head,same]

/-- A declared storage type has a determining child position only at a
non-atomic head, so the determining head itself is retained while the query is
decoded. -/
theorem SameHead.scopedAtoms_right {scope : ScopeInstantiation} {left right child : Term}
    (same : SameHead left right) (member : child ∈ right.children) : SameHead left (scope.term right) := by
  unfold SameHead at same ⊢
  rw [same]
  cases right <;> simp only [Term.children,List.not_mem_nil] at member
  all_goals
    try simp only [ScopeInstantiation.term,Term.mapChildren,List.map_map,Function.comp_def] <;> rfl

/-- A declaration's own terms are scope-closed, so the actual scope decoding
fixes them: the runtime image of a program template is the template. -/
theorem ProgramWellFormed.declaration_fixed {program : Program} (valid : ProgramWellFormed program)
    {scope : ScopeInstantiation} {declaration : Definition} (member : declaration ∈ program.declarations) :
    ∀ term ∈ declaration.terms, scope.term term = term :=
  fun term present => ScopeInstantiation.term_fixed scope term (valid.scopeClosed member term present)

namespace Typing

/-- The evidence an actual invocation supplies for reading one source context at
its runtime image. It is indexed by the actual source context, so it is not a law
about arbitrary contexts: `entails` is the reading of the context's own logical
evidence, `substitution` the reading of the declaration requirements its
implementation selections consume, and `kinding` the kinding domain of the
decoded terms. -/
structure ScopeReading (program : Program) (source : Language.Context)
    (context : Execution.Context) : Prop where
  entails : ∀ {constraint : Constraint}, Entails program source constraint →
    Entails program context.static (constraint.mapTerms context.instantiation.term)
  substitution : ∀ {substitution : Substitution} {requirement : Constraint},
    EntailsSubstitution program source substitution requirement →
      EntailsSubstitution program context.static
        (substitution.map (fun entry => (entry.1,context.instantiation.term entry.2))) requirement
  kinding : ∀ {term : Term} {kind : Kind}, Kinding program source term kind →
    Kinding program context.static (context.instantiation.term term) kind

namespace ScopeReading

variable {program : Program} {source : Language.Context} {context : Execution.Context}

/-- The runtime closing context carries no assumptions, so any logical equality
read there is definitional. -/
theorem static_assumptions : context.static.assumptions = [] := rfl

/-- The actual scope decoding of the invocation is the runtime context's own
instantiation. -/
theorem decodes (term : Term) : context.term term = context.instantiation.term term := rfl

/-- The source logical equality of the actual context is read at the image. -/
theorem equal_of_entails (reading : ScopeReading program source context) {left right : Term}
    (held : Entails program source (.equal left right)) :
    DefinitionallyEqual program context.static (context.instantiation.term left)
      (context.instantiation.term right) :=
  Entails.closed_definitional_equal
    (by simpa only [Constraint.mapTerms] using reading.entails held) rfl

/-- The source lexical assumption of the actual context is read at the image. -/
theorem equal_of_member (reading : ScopeReading program source context) {left right : Term}
    (member : Constraint.equal left right ∈ source.assumptions) :
    DefinitionallyEqual program context.static (context.instantiation.term left)
      (context.instantiation.term right) :=
  Entails.closed_definitional_equal
    (by simpa only [Constraint.mapTerms] using reading.entails (.assumed member)) rfl

/-! ### The scoped image of the mutual static block

One joint elimination of the static block reads every ordered constructor, row
and definitional step at the runtime image. The alias expansions decode through
`stepImage_alias`; the associated projection/defaultProjection steps rebuild
their runtime `ProjectionDomain`, `SelectsImpl`, `MatchesImplHead`,
`InfersHeadArgument`/`InfersHeadParameter` and substitution graph, so no
`ProjectionStepConversion` law is assumed; the context's own assumptions are read
through `entails` and the declaration requirements through `substitution`. -/
set_option linter.unusedSimpArgs false in
theorem equalImage (valid : ProgramWellFormed program) (reading : ScopeReading program source context)
    {left right : Term} (equal : Equal program source left right) :
    Equal program context.static (context.instantiation.term left)
      (context.instantiation.term right) := by
  revert reading
  refine Equal.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun c l r _ => ScopeReading program c context →
      Equal program context.static (context.instantiation.term l) (context.instantiation.term r))
    (motive_4 := fun c trait arguments negative implementation substitution _ => ScopeReading program c context →
      SelectsImpl program context.static trait (arguments.map context.instantiation.term) negative implementation
        (substitution.map (fun entry => (entry.1,context.instantiation.term entry.2))))
    (motive_5 := fun _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ => True)
    (motive_8 := fun _ _ _ => True)
    (motive_9 := fun _ _ _ _ => True)
    (motive_10 := fun c l r _ => ScopeReading program c context →
      DefinitionallyEqual program context.static (context.instantiation.term l)
        (context.instantiation.term r))
    (motive_11 := fun c l r _ => ScopeReading program c context →
      DefinitionallyEqual program context.static (context.instantiation.term l)
        (context.instantiation.term r))
    (motive_12 := fun _ _ _ _ => True)
    (motive_13 := fun c implementation arguments substitution _ => ScopeReading program c context →
      Definition.implementation implementation ∈ program.declarations →
      MatchesImplHead program context.static implementation (arguments.map context.instantiation.term)
        (substitution.map (fun entry => (entry.1,context.instantiation.term entry.2))))
    (motive_14 := fun c trait member owners items associated ownerSub itemSub _ => ScopeReading program c context →
      ProjectionDomain program context.static trait member (owners.map context.instantiation.term)
        (items.map context.instantiation.term) associated
        (ownerSub.map (fun entry => (entry.1,context.instantiation.term entry.2)))
        (itemSub.map (fun entry => (entry.1,context.instantiation.term entry.2))))
    (motive_15 := fun sourceContext c binder template query value _ => ScopeReading program c context →
      InfersHeadParameter program sourceContext context.static binder template
        (context.instantiation.term query) (context.instantiation.term value))
    (motive_16 := fun c implementation arguments binder value _ => ScopeReading program c context →
      InfersHeadArgument program context.static implementation
        (arguments.map context.instantiation.term) binder (context.instantiation.term value))
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intro _ _ reading; exact .refl)
    (by
      intro _ _ _ proof ih reading
      exact (ih reading).symm)
    (by
      intro _ _ _ _ first second ihFirst ihSecond reading
      exact (ihFirst reading).trans (ihSecond reading))
    (by
      intro _ _ _ same children ihChildren reading
      exact (ScopeInstantiation.scopedHomomorphism context.instantiation).congr_relation
        (fun _ => Equal.refl)
        (fun same children => Equal.congr same children) same
        (ListRel.of_at same.children_length
          (fun index first second firstAt secondAt => ihChildren index first second firstAt secondAt reading)))
    (by
      intro _ _ _ member reading
      exact .entailed (by simpa only [Constraint.mapTerms] using reading.entails (.assumed member)))
    (by
      intro _ _ _ held _ reading
      exact .entailed (by simpa only [Constraint.mapTerms] using reading.entails held))
    (by
      intro _ _ _ converted ih reading
      exact .definitional (ih reading))
    (by
      intro _ _ _ _ _ inner ih reading
      simpa only [ScopeInstantiation.term,List.map_cons] using (Equal.rowDuplicate (ih reading)))
    (by
      intro _ _ _ _ _ inner ih reading
      simpa only [ScopeInstantiation.term,List.map_cons] using (Equal.tailDuplicate (ih reading)))
    (by
      intro _ _ _ _ _ _ member traitEq negativeEq head requirements ihHead ihRequirements reading
      refine .selected member traitEq negativeEq (ihHead reading member) ?_
      intro requirement present
      exact reading.substitution (requirements requirement present))
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by
      intro _ _ _ _ _ _ found instantiated kinded graph reading
      exact ScopeInstantiation.ScopeInstantiation.stepImage_alias valid found instantiated graph
        (fun argument present => by
          obtain ⟨original,inArguments,rfl⟩ := List.mem_map.mp present
          simpa only [ScopeInstantiation.term_kind] using reading.kinding (kinded original inArguments)))
    (by
      intro _ trait memberId owners items associated _ itemSub implementation implSub body value
        domain selected pairMember substituted ihDomain ihSelected reading
      have assoc : body ∈ implementation.associated.map Prod.snd :=
        List.mem_map.mpr ⟨(memberId, body), pairMember, rfl⟩
      have implementationMember : Definition.implementation implementation ∈ program.declarations := by
        cases selected with
        | selected members _ _ _ _ => exact members
      have fixedBody : context.instantiation.term body = body :=
        ProgramWellFormed.declaration_fixed valid implementationMember body (by
          rw [Definition.terms]
          exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ assoc)))
      have graph' : Substitutes
          (implSub.map (fun e => (e.1, context.instantiation.term e.2)) ++
            itemSub.map (fun e => (e.1, context.instantiation.term e.2))) body
          (context.instantiation.term value) := by
        simpa only [List.map_append] using ScopeInstantiation.substitute_values context.instantiation
          (implSub ++ itemSub) body value substituted fixedBody
      have step := DefinitionalStep.projection (ihDomain reading) (ihSelected reading) pairMember graph'
      simpa only [ScopeInstantiation.term] using DefinitionallyEqual.step step)
    (by
      intro _ trait memberId owners items associated ownerSub itemSub implementation implSub rawBody value
        domain selected absent default substituted ihDomain ihSelected reading
      have foundAssociated : program.associated memberId = some associated := by cases domain; assumption
      have fixedBody : context.instantiation.term rawBody = rawBody :=
        ProgramWellFormed.declaration_fixed valid
          (List.mem_of_find?_eq_some (Program.associated_lookup foundAssociated)) rawBody
          (by simp only [Definition.terms,List.mem_append]; exact Or.inl (by simp [default]))
      have graph' : Substitutes
          (ownerSub.map (fun e => (e.1, context.instantiation.term e.2)) ++
            itemSub.map (fun e => (e.1, context.instantiation.term e.2))) rawBody
          (context.instantiation.term value) := by
        simpa only [List.map_append] using ScopeInstantiation.substitute_values context.instantiation
          (ownerSub ++ itemSub) rawBody value substituted fixedBody
      have step := DefinitionalStep.defaultProjection (ihDomain reading) (ihSelected reading) absent default
        graph'
      simpa only [ScopeInstantiation.term] using DefinitionallyEqual.step step)
    (by intro _ _ reading; exact .refl)
    (by
      intro _ _ _ proof ih reading
      exact (ih reading).symm)
    (by
      intro _ _ _ _ first second ihFirst ihSecond reading
      exact (ihFirst reading).trans (ihSecond reading))
    (by
      intro _ _ _ same children ihChildren reading
      exact DefinitionallyEqual.congr (SameHead.scopedAtoms same)
        (ListRel.of_at
          (by rw [ScopeInstantiation.children,ScopeInstantiation.children,List.length_map,List.length_map]
              exact same.children_length)
          (fun index first second firstAt secondAt => by
            rw [ScopeInstantiation.children,List.getElem?_map] at firstAt secondAt
            obtain ⟨first₀,firstAt₀,rfl⟩ := Option.map_eq_some_iff.mp firstAt
            obtain ⟨second₀,secondAt₀,rfl⟩ := Option.map_eq_some_iff.mp secondAt
            exact ihChildren index first₀ second₀ firstAt₀ secondAt₀ reading)))
    (by
      intro _ _ _ step ih reading
      exact ih reading)
    (by
      intro _ _ _ equivalent reading
      exact .row (ScopeInstantiation.rowEquivalent_term context.instantiation equivalent))
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by intros; exact True.intro)
    (by
      intro _ implementation arguments _ _ _ instantiated kinded graph lengths de inferred ihDe ihInferred
        reading member
      have lexical := valid.scopeClosed member
      have fixedArguments : ∀ term ∈ implementation.arguments, context.instantiation.term term = term :=
        fun term present => ScopeInstantiation.term_fixed context.instantiation term
          (lexical term (by
            simp [Definition.terms,present]))
      refine .inferred
        (instantiated.map_values context.instantiation.term
          (fun value _ => ScopeInstantiation.term_kind context.instantiation value)) ?_
        (ScopeInstantiation.substitutes_values context.instantiation graph fixedArguments)
        (by rw [List.length_map,List.length_map]; exact lengths) ?_ ?_
      · intro value present
        obtain ⟨original,inValues,rfl⟩ := List.mem_map.mp present
        simpa only [ScopeInstantiation.term_kind] using reading.kinding (kinded original inValues)
      · intro index first second firstAt secondAt
        rw [List.getElem?_map] at firstAt secondAt
        obtain ⟨left,leftAt,rfl⟩ := Option.map_eq_some_iff.mp firstAt
        obtain ⟨right,rightAt,rfl⟩ := Option.map_eq_some_iff.mp secondAt
        exact ihDe index left right leftAt rightAt reading
      · intro index binder value binderAt valueAt
        rw [List.getElem?_map] at valueAt
        obtain ⟨original,originalAt,rfl⟩ := Option.map_eq_some_iff.mp valueAt
        exact ihInferred index binder original binderAt originalAt reading)
    (by
      intro _ _ _ _ _ _ _ ownerSub itemSub found member associatedFound ownerEq ownerInst itemInst kinded
        ownerReqs itemReqs ihOwnerReqs ihItemReqs reading
      refine .valid found member associatedFound ownerEq
        (ownerInst.map_values context.instantiation.term
          (fun value _ => ScopeInstantiation.term_kind context.instantiation value))
        (itemInst.map_values context.instantiation.term
          (fun value _ => ScopeInstantiation.term_kind context.instantiation value)) ?_ ?_ ?_
      · intro argument present
        rw [List.mem_append] at present
        rcases present with present | present
        · obtain ⟨original,inOwners,rfl⟩ := List.mem_map.mp present
          simpa only [ScopeInstantiation.term_kind] using
            reading.kinding (kinded original (by rw [List.mem_append]; exact Or.inl inOwners))
        · obtain ⟨original,inItems,rfl⟩ := List.mem_map.mp present
          simpa only [ScopeInstantiation.term_kind] using
            reading.kinding (kinded original (by rw [List.mem_append]; exact Or.inr inItems))
      · intro requirement present
        exact reading.substitution (ownerReqs requirement present)
      · intro requirement present
        simpa only [List.map_append] using reading.substitution (itemReqs requirement present))
    (by
      intro _ _ _ _ same reading
      exact .parameter (by rw [ScopeInstantiation.term_kind]; exact same))
    (by
      intro _ _ _ _ _ _ _ _ _ structural same templateAt queryAt inferred ihInferred reading
      exact .child structural (SameHead.scopedAtoms_right same (List.mem_of_getElem? queryAt))
        templateAt (by rw [ScopeInstantiation.children,List.getElem?_map,queryAt]; rfl)
        (ihInferred reading))
    (by
      intro _ _ _ _ _ _ _ reduction inferred _ ihInferred reading
      exact .sourceReduction reduction (ihInferred reading))
    (by
      intro _ _ _ _ _ _ _ equal origin ihEqual ihOrigin reading
      exact .queryConversion (ihEqual reading) (ihOrigin reading))
    (by
      intro _ _ _ _ _ _ _ _ templateAt queryAt inferred ihInferred reading
      exact .argument templateAt (by rw [List.getElem?_map,queryAt]; rfl) (ihInferred reading))
    equal

/-- The runtime closing law of the actual source context, derived from the
invocation's own evidence: the source context's logical equality is read at its
actual runtime image, so the place and transfer consumers take `ScopeReading`
rather than an assumed interpretation. -/
theorem conversionClosed (valid : ProgramWellFormed program) (reading : ScopeReading program source context) :
    Typing.SourceConversionClosed program source context :=
  fun _left _right equal => (equalImage valid reading equal).closed_definitional rfl

/-- Producer for the actual invocation reading. The evidence is exactly what an
invocation provides: the decoding fixes the source context's own constraints and
substitution tables and its kinding domain (the callee's declared templates are
fixed by the decoding), the runtime kinding domain corresponds to the source
one, and the context's lexical assumptions are discharged at the image. The
reading is then *derived* by the actual assumption cut - never assumed. -/
theorem of_cut {program : Program} {source : Language.Context} {context : Execution.Context}
    (kinds : ∀ term kind, Kinding program source term kind ↔ Kinding program context.static term kind)
    (constraints : ∀ (constraint : Constraint),
      Constraint.mapTerms context.instantiation.term constraint = constraint)
    (substitutions : ∀ (substitution : Substitution),
      substitution.map (fun entry => (entry.1, context.instantiation.term entry.2)) = substitution)
    (terms : ∀ term, context.instantiation.term term = term)
    (discharged : ∀ constraint ∈ source.assumptions, Entails program context.static constraint) :
    ScopeReading program source context where
  entails := fun held => (constraints _) ▸ held.cut kinds discharged
  substitution := fun held => (substitutions _) ▸ held.cut kinds discharged
  kinding := fun kinded => (terms _) ▸ (kinds _ _).mp kinded

end ScopeReading
end Typing
end Glorious.Language
