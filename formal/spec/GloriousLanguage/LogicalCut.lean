import GloriousLanguage.PredicateComposition
import GloriousLanguage.ClosedDefinitionalEquality

/-! Assumption cut for the actual mutual static semantics. A universal
predicate keeps its exact argument domain; changing that domain is a separate
parametricity obligation, not implicit weakening of universal evidence. -/
namespace Glorious.Language

private abbrev CutResult (program : Program) (source : Context) (judgment : Context → Prop) : Prop :=
  ∀ target : Context,
    (∀ term kind, Kinding program source term kind ↔ Kinding program target term kind) →
    (∀ constraint ∈ source.assumptions, Entails program target constraint) → judgment target

/-- Actual derived assumptions may replace lexical assumptions without
changing the kinding domain. The induction includes finite capability leaves,
implementation selection and both contexts of head-origin evidence. -/
theorem Entails.cut {program : Program} {source target : Context} {constraint : Constraint}
    (held : Entails program source constraint)
    (kinds : ∀ term kind, Kinding program source term kind ↔ Kinding program target term kind)
    (assumptions : ∀ requirement ∈ source.assumptions, Entails program target requirement) :
    Entails program target constraint := by
  refine Entails.rec
    (motive_1 := fun source type principal _ => CutResult program source (fun target => CapabilityEvidence program target type principal))
    (motive_2 := fun source assignment type principal _ => CutResult program source (fun target => CapabilityUnfolds program target assignment type principal))
    (motive_3 := fun source left right _ => CutResult program source (fun target => Equal program target left right))
    (motive_4 := fun source trait arguments negative implementation substitution _ =>
      CutResult program source (fun target => SelectsImpl program target trait arguments negative implementation substitution))
    (motive_5 := fun source effect row _ => CutResult program source (fun target => RowMember program target effect row))
    (motive_6 := fun source required allowed _ => CutResult program source (fun target => RowSubset program target required allowed))
    (motive_7 := fun source type region _ => CutResult program source (fun target => TypeOutlives program target type region))
    (motive_8 := fun source constraint _ => CutResult program source (fun target => Entails program target constraint))
    (motive_9 := fun source substitution constraint _ =>
      CutResult program source (fun target => EntailsSubstitution program target substitution constraint))
    (motive_10 := fun source left right _ => CutResult program source (fun target => DefinitionalStep program target left right))
    (motive_11 := fun source left right _ => CutResult program source (fun target => DefinitionallyEqual program target left right))
    (motive_12 := fun source left right _ => CutResult program source (fun target => DefinitionalReduction program target left right))
    (motive_13 := fun source implementation arguments substitution _ =>
      CutResult program source (fun target => MatchesImplHead program target implementation arguments substitution))
    (motive_14 := fun source trait member owners items associated ownerSub itemSub _ =>
      CutResult program source (fun target => ProjectionDomain program target trait member owners items associated ownerSub itemSub))
    (motive_15 := fun sourceContext source binder template query value _ =>
      CutResult program source (fun target => InfersHeadParameter program sourceContext target binder template query value))
    (motive_16 := fun source implementation arguments binder value _ =>
      CutResult program source (fun target => InfersHeadArgument program target implementation arguments binder value))
    ?structural ?logical ?capEqual ?equation ?evidence
    ?refl ?symm ?trans ?congrChildren ?assumed ?entailed ?definitional
    ?rowDuplicate ?tailDuplicate ?selected ?head ?tail ?equal_1 ?empty ?assumed_1 ?same ?trans_1 ?instances ?entailed_1
    ?assumed_2 ?scalar ?unit ?pointer ?reference ?bottom ?tuple ?array ?nominal ?callable ?label ?environment
    ?available ?bindings ?equal_2 ?entailed_2 ?checkedCallable ?checkedRunsIn ?assumed_3 ?congrSubstitution ?equality
    ?outlivesRefl ?outlivesStatic ?outlivesTrans ?typeOutlives
    ?rows ?implementation ?use ?quantified ?quantifiedInstance ?instantiated
    ?alias ?projection ?defaultProjection
    ?refl_1 ?symm_1 ?trans_2 ?congrChildren_1 ?step ?row
    ?refl_2 ?step_1 ?trans_3 ?congrChildren_2 ?row_1
    ?inferred ?valid ?parameter ?child ?sourceReduction ?queryConversion ?argument held target kinds assumptions
  all_goals dsimp only [CutResult]
  all_goals intros
  case structural _ _ _ assignment found _ unfolded target kinds assumptions =>
    exact .structural found (fun term principal selected => unfolded term principal selected target kinds assumptions)
  case logical _ _ _ _ _ admitted lower ih target kinds assumptions => exact .logical (ih target kinds assumptions) admitted lower
  case capEqual _ _ _ _ _ _ equal evidence target kinds assumptions =>
    exact .equal (equal target kinds assumptions) (evidence target kinds assumptions)
  case equation _ _ _ _ _ restriction equation target kinds assumptions => exact .equation restriction equation
  case evidence _ _ _ _ _ restriction _ ih target kinds assumptions => exact .evidence restriction (ih target kinds assumptions)
  case refl => exact .refl
  case symm _ _ _ _ ih target kinds assumptions => exact .symm (ih target kinds assumptions)
  case trans _ _ _ _ _ _ first second target kinds assumptions => exact .trans (first target kinds assumptions) (second target kinds assumptions)
  case congrChildren _ _ _ same _ children target kinds assumptions =>
    exact .congrChildren same (fun index first second leftAt rightAt => children index first second leftAt rightAt target kinds assumptions)
  case assumed _ _ _ member target kinds assumptions => exact .entailed (assumptions _ member)
  case entailed _ _ _ _ ih target kinds assumptions => exact .entailed (ih target kinds assumptions)
  case definitional _ _ _ _ ih target kinds assumptions => exact .definitional (ih target kinds assumptions)
  case rowDuplicate _ _ _ _ _ _ ih target kinds assumptions => exact .rowDuplicate (ih target kinds assumptions)
  case tailDuplicate _ _ _ _ _ _ ih target kinds assumptions => exact .tailDuplicate (ih target kinds assumptions)
  case selected _ _ _ _ _ _ declared trait negative _ _ head requirements target kinds assumptions =>
    exact .selected declared trait negative (head target kinds assumptions)
      (fun requirement member => requirements requirement member target kinds assumptions)
  case head _ _ _ _ _ member _ ih target kinds assumptions => exact .head member (ih target kinds assumptions)
  case tail _ _ _ _ _ member _ ih target kinds assumptions => exact .tail member (ih target kinds assumptions)
  case equal_1 _ _ _ _ _ _ first second target kinds assumptions => exact .equal (first target kinds assumptions) (second target kinds assumptions)
  case empty => exact .empty
  case assumed_1 _ _ _ member target kinds assumptions => exact .entailed (assumptions _ member)
  case same _ _ _ _ ih target kinds assumptions => exact .same (ih target kinds assumptions)
  case trans_1 _ _ _ _ _ _ first second target kinds assumptions => exact .trans (first target kinds assumptions) (second target kinds assumptions)
  case instances _ _ _ _ _ _ fields tails target kinds assumptions =>
    exact .instances (fun term member => fields term member target kinds assumptions)
      (fun term member => tails term member target kinds assumptions)
  case entailed_1 _ _ _ _ ih target kinds assumptions => exact .entailed (ih target kinds assumptions)
  case assumed_2 _ _ _ member target kinds assumptions => exact .entailed (assumptions _ member)
  case scalar => exact .scalar
  case unit => exact .unit
  case pointer => exact .pointer
  case reference _ _ _ _ _ _ ih target kinds assumptions => exact .reference (ih target kinds assumptions)
  case bottom => exact .bottom
  case tuple _ _ _ _ fields target kinds assumptions => exact .tuple (fun term member => fields term member target kinds assumptions)
  case array _ _ _ _ _ ih target kinds assumptions => exact .array (ih target kinds assumptions)
  case nominal _ _ _ _ _ _ _ found instantiated substituted _ fields target kinds assumptions =>
    exact .nominal found instantiated substituted (fun term member => fields term member target kinds assumptions)
  case callable _ _ _ _ _ declared _ fields target kinds assumptions =>
    exact .callable declared (fun term member => fields term member target kinds assumptions)
  case label _ _ _ _ _ _ ih target kinds assumptions => exact .label (ih target kinds assumptions)
  case environment _ _ _ _ _ _ _ outlives fields target kinds assumptions =>
    exact .environment (outlives target kinds assumptions) (fun term member => fields term member target kinds assumptions)
  case available _ _ _ _ _ _ ih target kinds assumptions => exact .available (ih target kinds assumptions)
  case bindings _ _ _ _ _ _ _ outlives fields target kinds assumptions =>
    exact .bindings (outlives target kinds assumptions) (fun term member => fields term member target kinds assumptions)
  case equal_2 _ _ _ _ _ _ first second target kinds assumptions => exact .equal (first target kinds assumptions) (second target kinds assumptions)
  case entailed_2 _ _ _ _ ih target kinds assumptions => exact .entailed (ih target kinds assumptions)
  case checkedCallable _ _ _ _ _ _ _ _ found member receiver arguments result effects target kinds assumptions =>
    exact .checkedCallable found member receiver arguments result effects
  case checkedRunsIn _ _ _ _ _ _ _ _ found member receiver access arguments after target kinds assumptions =>
    exact .checkedRunsIn found member receiver access arguments after
  case assumed_3 _ _ member target kinds assumptions => exact assumptions _ member
  case congrSubstitution _ _ _ _ _ _ _ before after _ equal held target kinds assumptions =>
    exact .congrSubstitution (fun id kind => equal id kind target kinds assumptions) before after (held target kinds assumptions)
  case equality _ _ _ _ ih target kinds assumptions => exact .equality (ih target kinds assumptions)
  case outlivesRefl => exact .outlivesRefl
  case outlivesStatic => exact .outlivesStatic
  case outlivesTrans _ _ _ _ _ _ first second target kinds assumptions =>
    exact .outlivesTrans (first target kinds assumptions) (second target kinds assumptions)
  case typeOutlives _ _ _ _ ih target kinds assumptions => exact .typeOutlives (ih target kinds assumptions)
  case rows _ _ _ _ ih target kinds assumptions => exact .rows (ih target kinds assumptions)
  case implementation _ _ _ _ _ _ _ ih target kinds assumptions => exact .implementation (ih target kinds assumptions)
  case use _ _ _ _ _ requested ih target kinds assumptions => exact .use (ih target kinds assumptions) requested
  case quantified _ _ _ _ instances target kinds assumptions =>
    exact .quantified (fun values substitution instantiated typed requirement member =>
      instances values substitution instantiated (fun term present => (kinds term term.kind).mpr (typed term present))
        requirement member target kinds assumptions)
  case quantifiedInstance _ _ _ _ _ _ _ _ instantiated typed member graph ih target kinds assumptions =>
    exact .quantifiedInstance (ih target kinds assumptions) instantiated
      (fun term present => (kinds term term.kind).mp (typed term present)) member graph
  case instantiated _ _ _ _ graph _ ih target kinds assumptions => exact .instantiated graph (ih target kinds assumptions)
  case alias _ _ _ _ _ _ found instantiated typed graph target kinds assumptions =>
    exact .alias found instantiated (fun term present => (kinds term term.kind).mp (typed term present)) graph
  case projection _ _ _ _ _ _ _ _ _ _ _ _ _ _ member graph domain selected target kinds assumptions =>
    exact .projection (domain target kinds assumptions) (selected target kinds assumptions) member graph
  case defaultProjection _ _ _ _ _ _ _ _ _ _ _ _ _ _ absent default graph domain selected target kinds assumptions =>
    exact .defaultProjection (domain target kinds assumptions) (selected target kinds assumptions) absent default graph
  case refl_1 => exact .refl
  case symm_1 _ _ _ _ ih target kinds assumptions => exact .symm (ih target kinds assumptions)
  case trans_2 _ _ _ _ _ _ first second target kinds assumptions => exact .trans (first target kinds assumptions) (second target kinds assumptions)
  case congrChildren_1 _ _ _ same _ children target kinds assumptions =>
    exact .congrChildren same (fun index first second leftAt rightAt => children index first second leftAt rightAt target kinds assumptions)
  case step _ _ _ _ ih target kinds assumptions => exact .step (ih target kinds assumptions)
  case row _ _ _ equivalent target kinds assumptions => exact .row equivalent
  case refl_2 => exact .refl
  case step_1 _ _ _ _ ih target kinds assumptions => exact .step (ih target kinds assumptions)
  case trans_3 _ _ _ _ _ _ first second target kinds assumptions => exact .trans (first target kinds assumptions) (second target kinds assumptions)
  case congrChildren_2 _ _ _ same _ children target kinds assumptions =>
    exact .congrChildren same (fun index first second leftAt rightAt => children index first second leftAt rightAt target kinds assumptions)
  case row_1 _ _ _ equivalent target kinds assumptions => exact .row equivalent
  case inferred _ _ _ _ _ _ instantiated typed graph lengths _ _ head origins target kinds assumptions =>
    exact .inferred instantiated (fun term present => (kinds term term.kind).mp (typed term present)) graph lengths
      (fun index first second leftAt rightAt => head index first second leftAt rightAt target kinds assumptions)
      (fun index binder value binderAt valueAt => origins index binder value binderAt valueAt target kinds assumptions)
  case valid _ _ _ _ _ _ _ _ _ found member associated owner owners items typed _ _ ownerIH itemIH target kinds assumptions =>
    exact .valid found member associated owner owners items
      (fun term present => (kinds term term.kind).mp (typed term present))
      (fun requirement member => ownerIH requirement member target kinds assumptions)
      (fun requirement member => itemIH requirement member target kinds assumptions)
  case parameter _ _ _ _ same target kinds assumptions => exact .parameter same
  case child _ _ _ _ _ _ _ _ _ structural same leftAt rightAt _ ih target kinds assumptions =>
    exact .child structural same leftAt rightAt (ih target kinds assumptions)
  case sourceReduction _ _ _ _ _ _ _ reduction _ _ ih target kinds assumptions =>
    exact .sourceReduction reduction (ih target kinds assumptions)
  case queryConversion _ _ _ _ _ _ _ _ _ equal origin target kinds assumptions =>
    exact .queryConversion (equal target kinds assumptions) (origin target kinds assumptions)
  case argument _ _ _ _ _ _ _ _ leftAt rightAt _ ih target kinds assumptions =>
    exact .argument leftAt rightAt (ih target kinds assumptions)

theorem Equal.cut {program : Program} {source target : Context} {left right : Term}
    (equal : Equal program source left right)
    (kinds : ∀ term kind, Kinding program source term kind ↔ Kinding program target term kind)
    (assumptions : ∀ requirement ∈ source.assumptions, Entails program target requirement) :
    Equal program target left right := .entailed ((Entails.equality equal).cut kinds assumptions)

theorem EntailsSubstitution.cut {program : Program} {source target : Context} {substitution : Substitution} {constraint : Constraint}
    (held : EntailsSubstitution program source substitution constraint)
    (kinds : ∀ term kind, Kinding program source term kind ↔ Kinding program target term kind)
    (assumptions : ∀ requirement ∈ source.assumptions, Entails program target requirement) :
    EntailsSubstitution program target substitution constraint := by
  cases held with
  | instantiated graph held => exact .instantiated graph (held.cut kinds assumptions)

theorem CapabilityEvidence.cut {program : Program} {source target : Context} {type : Term} {principal : Principal}
    (evidence : CapabilityEvidence program source type principal)
    (kinds : ∀ term kind, Kinding program source term kind ↔ Kinding program target term kind)
    (assumptions : ∀ requirement ∈ source.assumptions, Entails program target requirement) :
    CapabilityEvidence program target type principal :=
  .logical ((Entails.use evidence ((principal.quantity_request principal).mpr (.refl principal))).cut kinds assumptions)
    principal.quantity_valid (fun permitted request => (principal.quantity_request permitted).mp request)

theorem RowSubset.cut {program : Program} {source target : Context} {required allowed : Term}
    (subset : RowSubset program source required allowed)
    (kinds : ∀ term kind, Kinding program source term kind ↔ Kinding program target term kind)
    (assumptions : ∀ requirement ∈ source.assumptions, Entails program target requirement) :
    RowSubset program target required allowed := .entailed ((Entails.rows subset).cut kinds assumptions)

theorem TypeOutlives.cut {program : Program} {source target : Context} {type region : Term}
    (outlives : TypeOutlives program source type region)
    (kinds : ∀ term kind, Kinding program source term kind ↔ Kinding program target term kind)
    (assumptions : ∀ requirement ∈ source.assumptions, Entails program target requirement) :
    TypeOutlives program target type region := .entailed ((Entails.typeOutlives outlives).cut kinds assumptions)

/-- Assumptions, module ownership and unsafe permission do not change the
source kinding domain. This derives the domain condition of cut from the
actual context fields instead of requiring a separate term classifier. -/
theorem Kinding.context_same_domain {program : Program} {source target : Context} {term : Term} {kind : Kind}
    (typed : Kinding program source term kind) (binders : source.binders = target.binders)
    (levels : source.universeLevel = target.universeLevel) (scope : source.scope = target.scope) :
    Kinding program target term kind := by
  apply typed.context_transport
  · intro id kind occurs
    obtain ⟨binder,member,sameId,sameKind⟩ := typed.parameter_occurs occurs
    have present : binder ∈ target.binders := binders ▸ member
    simpa only [sameId,sameKind] using (Kinding.parameter (program := program) present)
  · exact Nat.le_of_eq levels
  · intro id member
    simpa only [scope] using member
  · intro id member
    simpa only [scope] using member

theorem Entails.cut_same_domain {program : Program} {source target : Context} {constraint : Constraint}
    (held : Entails program source constraint) (binders : source.binders = target.binders)
    (levels : source.universeLevel = target.universeLevel) (scope : source.scope = target.scope)
    (assumptions : ∀ requirement ∈ source.assumptions, Entails program target requirement) :
    Entails program target constraint :=
  held.cut (fun _ _ => ⟨fun typed => typed.context_same_domain binders levels scope,
    fun typed => typed.context_same_domain binders.symm levels.symm scope.symm⟩) assumptions

theorem Equal.cut_same_domain {program : Program} {source target : Context} {left right : Term}
    (equal : Equal program source left right) (binders : source.binders = target.binders)
    (levels : source.universeLevel = target.universeLevel) (scope : source.scope = target.scope)
    (assumptions : ∀ requirement ∈ source.assumptions, Entails program target requirement) :
    Equal program target left right :=
  .entailed ((Entails.equality equal).cut_same_domain binders levels scope assumptions)

/-- Discharging all lexical predicates into an assumption-free context
leaves only definitional equality. Quantified and capability assumptions are
discharged by the same cut proof, never erased syntactically. -/
theorem Equal.discharge_definitional {program : Program} {context : Context} {left right : Term}
    (equal : Equal program context left right)
    (assumptions : ∀ requirement ∈ context.assumptions,
      Entails program { context with assumptions := [] } requirement) :
    DefinitionallyEqual program { context with assumptions := [] } left right :=
  (equal.cut_same_domain (target := { context with assumptions := [] }) rfl rfl rfl assumptions).closed_definitional rfl

end Glorious.Language
