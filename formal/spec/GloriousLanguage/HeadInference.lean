import GloriousLanguage.ProjectionKinding

/-! Finite generic origins are consumed by actual implementation matching.
Query conversion transports the existing origin without replacing its source
template by an associated result that still needs that origin to be selected. -/
namespace Glorious.Language

theorem InfersHeadArgument.congr_query {program : Program} {context : Context} {implementation : ImplDefinition}
    {before after : List Term} {binder : Binder} {value : Term}
    (inferred : InfersHeadArgument program context implementation before binder value)
    (equal : ListRel (DefinitionallyEqual program context) before after) :
    InfersHeadArgument program context implementation after binder value := by
  cases inferred with
  | @argument _ _ _ _ _ template query index sourceAt queryAt origin =>
    cases afterAt : after[index]? with
    | none =>
      have beyond := List.getElem?_eq_none_iff.mp afterAt
      have beforeBound := (List.getElem?_eq_some_iff.mp queryAt).1
      have lengths := equal.length_eq
      omega
    | some actual =>
      exact .argument sourceAt afterAt (.queryConversion (equal.at queryAt afterAt).symm origin)

theorem ProgramWellFormed.implementation_head_determined {program : Program} (valid : ProgramWellFormed program)
    {implementation : ImplDefinition} (declared : Definition.implementation implementation ∈ program.declarations) :
    ImplementationHeadDetermined program implementation := by
  obtain ⟨_,_,_,_,_,_,_,signature⟩ := (valid.2.2.2.2.1 _ declared).2.1
  exact signature.2.1

/-- A direct generic head really obtains its value from the actual query;
this producer has no solution-uniqueness or normal-form premise. -/
theorem InfersHeadArgument.direct {program : Program} {context : Context} {implementation : ImplDefinition}
    {arguments : List Term} {binder : Binder} {value : Term} {index : Nat}
    (sourceAt : implementation.arguments[index]? = some (.parameter binder.id binder.kind))
    (queryAt : arguments[index]? = some value) (kind : value.kind = binder.kind) :
    InfersHeadArgument program context implementation arguments binder value :=
  .argument sourceAt queryAt (.parameter kind)

end Glorious.Language
