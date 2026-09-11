import Glorious.Semantics.Model

namespace Glorious.Semantics

abbrev Substitution := List (Id × Term)

def substitute : Nat → Substitution → Term → Check Term
  | 0, _, _ => reject .resourceLimit "substitution depth exhausted"
  | fuel + 1, substitutions, term =>
    match term with
    | .param id _ => return (lookup id substitutions).getD term
    | _ => term.mapChildrenM (substitute fuel substitutions)

def bindArguments (binders : List Binder) (arguments : List Term) : Check Substitution := do
  require (binders.length == arguments.length) .kindMismatch "generic argument arity differs"
  (binders.zip arguments).mapM fun (binder, argument) => do
    require (binder.kind == argument.kind) .kindMismatch s!"generic argument {binder.name} has the wrong kind"
    return (binder.id, argument)

structure ProjectionEvidence where
  traitDecl : DeclId
  member : DeclId
  arguments : List Term
  value : Term
  deriving Repr

structure MetaCell where
  id : Id
  kind : Kind
  level : Nat
  solution : Option Term := none
  deriving Repr

structure Inference where
  nextId : Id := 0
  level : Nat := 0
  cells : List MetaCell := []
  obligations : List Constraint := []
  assumptions : List Constraint := []
  projections : List ProjectionEvidence := []
  deriving Repr

abbrev InferM := StateT Inference Check

def freshMeta (kind : Kind) : InferM Term := do
  let state ← get
  let id := state.nextId
  set { state with nextId := id + 1, cells := ⟨id, kind, state.level, none⟩ :: state.cells }
  return .meta id kind state.level

def freshRigid (kind : Kind) : InferM Term := do
  let state ← get
  let id := state.nextId
  set { state with nextId := id + 1 }
  return .rigid id kind state.level

def defer (obligation : Constraint) : InferM Unit :=
  modify fun state => { state with obligations := state.obligations ++ [obligation] }

def walkTerm : Nat → Term → Check (List Term)
  | 0, _ => reject .resourceLimit "semantic term traversal exhausted"
  | fuel + 1, term => do
    let children ← term.children.mapM (walkTerm fuel)
    return term :: children.flatten

def normalize (program : Program) (state : Inference) : Nat → List Term → Term → Check Term
  | 0, _, _ => reject .resourceLimit "normalization depth exhausted"
  | fuel + 1, active, term => do
    require (!(active.contains term)) .recursiveNormalization "cyclic alias or associated projection"
    match term with
    | .meta id kind level =>
      let cell ← getRequired (state.cells.find? (fun c => c.id == id)) .missingEvidence "unknown inference cell"
      require (cell.kind == kind && cell.level == level) .malformedCore "stale inference cell identity"
      match cell.solution with
      | none => return term
      | some solution => normalize program state fuel (term :: active) solution
    | .alias declaration arguments =>
      let aliasDecl ← getRequired (program.aliases.find? (fun a => a.header.id == declaration))
        .unknownName "unknown type alias"
      let arguments ← arguments.mapM (normalize program state fuel active)
      let substitutions ← bindArguments aliasDecl.generics arguments
      let value ← substitute fuel substitutions aliasDecl.value
      normalize program state fuel (term :: active) value
    | .projection traitDecl member arguments kind =>
      let arguments ← arguments.mapM (normalize program state fuel active)
      let candidates := state.projections.filter fun p =>
        p.traitDecl == traitDecl && p.member == member && p.arguments == arguments
      match candidates with
      | [] => return .projection traitDecl member arguments kind
      | [evidence] =>
        require (evidence.value.kind == kind) .kindMismatch "associated evidence has the wrong kind"
        normalize program state fuel (term :: active) evidence.value
      | _ => reject .coherence "contradictory associated evidence"
    | .row instances tails =>
      let instances ← instances.mapM (normalize program state fuel active)
      let tails ← tails.mapM (normalize program state fuel active)
      for effectInstance in instances do
        require (effectInstance.kind == .effect) .kindMismatch "effect row contains a non-instance"
      let (instances, tails) ← tails.foldlM (init := (instances, [])) fun (known, openTerms) tail => do
        match tail with
        | .row more nested => return (known ++ more, openTerms ++ nested)
        | _ =>
          require (tail.kind == .row) .kindMismatch "row tail has the wrong kind"
          return (known, openTerms ++ [tail])
      return .row instances.eraseDups tails.eraseDups
    | _ => term.mapChildrenM (normalize program state fuel active)

def zonk (program : Program) (term : Term) : InferM Term := do
  normalize program (← get) program.limits.normalization [] term

def assignMeta (program : Program) (id : Id) (kind : Kind) (level : Nat)
    (value : Term) : InferM Unit := do
  let value ← zonk program value
  if value == .meta id kind level then return
  require (kind == value.kind) .kindMismatch "inference assignment changes kind"
  let terms ← walkTerm program.limits.normalization value
  require (!(terms.any fun t => match t with | .meta other .. => other == id | _ => false))
    .occursCheck "infinite inferred type or row"
  require (!(terms.any fun t => match t with
    | .rigid _ _ level | .meta _ _ level => level > level
    | _ => false)) .universeLeak "higher-ranked region or brand escapes its binder"
  let state ← get
  let cell ← getRequired (state.cells.find? (fun c => c.id == id)) .missingEvidence "unregistered inference variable"
  require (cell.solution.isNone && cell.kind == kind && cell.level == level)
    .malformedCore "attempt to overwrite solved or stale inference evidence"
  set { state with cells := state.cells.map (fun (c : MetaCell) =>
    if c.id == id then { c with solution := some value } else c) }

def sameTermHead (a b : Term) : Bool :=
  match a, b with
  | .unit, .unit | .bottom, .bottom | .staticRegion, .staticRegion => true
  | .scalar a, .scalar b => a == b
  | .tuple a, .tuple b | .constantTuple a, .constantTuple b => a.length == b.length
  | .array .., .array .. => true
  | .reference a .., .reference b .. | .rawPointer a .., .rawPointer b .. => a == b
  | .nominal a xs, .nominal b ys | .callable a xs, .callable b ys
  | .effect a xs, .effect b ys => a == b && xs.length == ys.length
  | .continuation a .., .continuation b .. => a == b
  | .label .., .label .. | .environment .., .environment .. | .available .., .available .. => true
  | .bindings _ _ a, .bindings _ _ b => a.length == b.length
  | .projection ta ma aa ka, .projection tb mb ab kb => ta == tb && ma == mb && ka == kb && aa.length == ab.length
  | .constant a, .constant b => a == b
  | .constantConstructor a ga fa, .constantConstructor b gb fb =>
    a == b && ga.length == gb.length && fa.length == fb.length
  | .param a ka, .param b kb => a == b && ka == kb
  | .rigid a ka ua, .rigid b kb ub => a == b && ka == kb && ua == ub
  | _, _ => false

def unify (program : Program) : Nat → Term → Term → InferM Unit
  | 0, _, _ => reject .resourceLimit "type/effect unification exhausted"
  | fuel + 1, left, right => do
    let left ← zonk program left
    let right ← zonk program right
    if left == right then return
    require (left.kind == right.kind) .kindMismatch "cannot equate distinct generic kinds"
    match left, right with
    | .meta id k u, t | t, .meta id k u => assignMeta program id k u t
    | .row li lt, .row ri rt =>
      let lOnly := li.filter (fun e => !ri.contains e)
      let rOnly := ri.filter (fun e => !li.contains e)
      if lOnly.isEmpty && rOnly.isEmpty && lt == rt then return
      match lt, rt with
      | [], [] => reject .typeMismatch "closed effect rows differ"
      | [.meta id k u], [] =>
        require lOnly.isEmpty .typeMismatch "explicit effect instance absent from the other row"
        assignMeta program id k u (.row rOnly [])
      | [], [.meta id k u] =>
        require rOnly.isEmpty .typeMismatch "explicit effect instance absent from the other row"
        assignMeta program id k u (.row lOnly [])
      | _, _ => reject .ambiguous "effect union has no uniquely determined split"
    | .projection .., _ | _, .projection .. => defer (.equal left right)
    | _, _ =>
      require (sameTermHead left right) .typeMismatch s!"incompatible semantic terms: {repr left}, {repr right}"
      for (a, b) in left.children.zip right.children do unify program fuel a b

def unifyTypes (program : Program) (left right : Term) : InferM Unit :=
  unify program program.limits.solving left right

def substituteConstraint (fuel : Nat) (substitutions : Substitution) : Constraint → Check Constraint
  | .named path args negative => return .named path (← args.mapM (substitute fuel substitutions)) negative
  | .equal a b => return .equal (← substitute fuel substitutions a) (← substitute fuel substitutions b)
  | .outlives a b => return .outlives (← substitute fuel substitutions a) (← substitute fuel substitutions b)
  | .rowIncludes a b => return .rowIncludes (← substitute fuel substitutions a) (← substitute fuel substitutions b)
  | .implements d args negative => return .implements d (← args.mapM (substitute fuel substitutions)) negative
  | .use t q => return .use (← substitute fuel substitutions t) q
  | .callable r a o e u =>
    return .callable (← substitute fuel substitutions r)
      (← substitute fuel substitutions a) (← substitute fuel substitutions o) (← substitute fuel substitutions e) u
  | .runsIn r a args after u =>
    return .runsIn (← substitute fuel substitutions r)
      (← substitute fuel substitutions a) (← substitute fuel substitutions args) (← substitute fuel substitutions after) u
  | .higherRanked binders obligations => do
    let substitutions := substitutions.filter fun (id, _) => !binders.any (fun b => b.id == id)
    let obligations ← match fuel with
      | 0 => reject .resourceLimit "higher-ranked substitution exhausted"
      | n + 1 => obligations.mapM (substituteConstraint n substitutions)
    return .higherRanked binders obligations

def substituteSignature (fuel : Nat) (substitutions : Substitution) (signature : Signature) : Check Signature := do
  return { signature with
    generics := signature.generics.filter (fun b => !(substitutions.any (fun p => p.1 == b.id)))
    arguments := ← signature.arguments.mapM (substitute fuel substitutions)
    output := ← substitute fuel substitutions signature.output
    effects := ← substitute fuel substitutions signature.effects
    constraints := ← signature.constraints.mapM (substituteConstraint fuel substitutions) }

/-- Explicit positional arguments constrain only ordinary type parameters;
    all remaining kinds follow their own defaults or fresh inference cells. -/
def instantiate (program : Program) (binders : List Binder) (explicitTypes : List Term) : InferM Substitution := do
  require (explicitTypes.all (fun t => t.kind == .type)) .kindMismatch "explicit type prefix contains a different kind"
  require (explicitTypes.length ≤ (binders.filter (fun b => b.kind == .type)).length)
    .kindMismatch "too many explicit type arguments"
  let (substitutions, remaining) ← binders.foldlM (init := ([], explicitTypes)) fun (subs, explicit) binder => do
    let (argument, rest) ← match binder.kind, explicit with
      | .type, value :: rest => pure (value, rest)
      | _, _ =>
        match binder.defaultValue with
        | some defaultValue => do
          let value ← substitute program.limits.normalization subs defaultValue
          pure (value, explicit)
        | none => do pure (← freshMeta binder.kind, explicit)
    return (subs ++ [(binder.id, argument)], rest)
  require remaining.isEmpty .kindMismatch "unused explicit generic arguments"
  return substitutions

def regionOutlives (fuel : Nat) (assumptions : List Constraint) (long short : Term) : Check Bool := do
  if long == short || long == .staticRegion then return true
  match fuel with
  | 0 => reject .resourceLimit "outlives closure exhausted"
  | n + 1 =>
    let successors := assumptions.filterMap fun c => match c with
      | .outlives a b => if a == long then some b else none
      | _ => none
    let results ← successors.mapM (fun next => regionOutlives n
      (assumptions.filter (fun c => match c with | .outlives a _ => a != long | _ => true)) next short)
    return results.any id

def guaranteeFromBounds (type : Term) (assumptions : List Constraint) : Check Principal := do
  let requests := assumptions.filterMap fun c => match c with
    | .use t q => if t == type then some q else none
    | _ => none
  let candidates := [Principal.duplicable, .affine, .exact].filter fun p =>
    requests.all fun q => match q.upper with
      | none => p == .duplicable
      | some upper => q.lower ≤ upper &&
        (match p with | .duplicable => true | .affine => upper ≤ 1 | .exact => q.lower == 1 && upper == 1)
  require (!candidates.isEmpty) .typeMismatch "inconsistent ownership quantity constraints"
  return Principal.residents candidates

/-- Greatest-capability fixed point on the finite three-class lattice. Unknown
    generic evidence is narrowed to what *all* possible principal classes allow.
    A nominal cycle refers to the current approximation, not infinite layout. -/
def deriveUseStep (program : Program) (state : Inference) (approximation : List (Term × Principal)) :
    Nat → Term → Check Principal
  | 0, _ => reject .resourceLimit "ownership capability derivation exhausted"
  | fuel + 1, original => do
    let type ← normalize program state fuel [] original
    match type with
    | .unit | .scalar .. | .rawPointer .. | .reference .shared .. | .label .. => return .duplicable
    | .bottom => return .duplicable
    | .reference .unique .. => return .affine
    | .tuple fields => return Principal.residents (← fields.mapM (deriveUseStep program state approximation fuel))
    | .array element (.constant (.integer _ _ length)) =>
      require (length ≥ 0) .invalidLayout "negative array length"
      if length == 0 then return .duplicable
      deriveUseStep program state approximation fuel element
    | .nominal declaration arguments =>
      match lookup type approximation with
      | some value => return value
      | none =>
        let data ← getRequired (program.dataType declaration) .unknownName "unknown nominal type"
        let subs ← bindArguments data.generics arguments
        let fields ← data.variants.flatMap (·.fields) |>.mapM (fun f => substitute fuel subs f.type)
        let marker ← data.quantityMarker.mapM (substitute fuel subs)
        let approximation := (type, Principal.duplicable) :: approximation
        let available ← (fields ++ marker.toList).mapM (deriveUseStep program state approximation fuel)
        let structural := Principal.residents available
        match data.principalRestriction with
        | none => return structural
        | some declared =>
          require (declared.meet structural == declared) .illegalCopy "principal declaration widens structural ownership"
          return declared
    | .param .. | .meta .. | .projection .. | .rigid .. => guaranteeFromBounds type state.assumptions
    | .array .. => reject .missingEvidence "array resident count has not normalized"
    | .callable .. | .continuation .. | .environment .. | .available .. | .bindings .. =>
      guaranteeFromBounds type state.assumptions
    | _ => reject .kindMismatch "non-type in ownership derivation"

def deriveUse (program : Program) (state : Inference) (type : Term) : Check Principal := do
  let terms ← walkTerm program.limits.normalization type
  let nominalRoots := (type :: terms).filter (fun t => match t with | .nominal .. => true | _ => false) |>.eraseDups
  let initial := nominalRoots.map (fun t => (t, Principal.duplicable))
  let rec iterate : Nat → List (Term × Principal) → Check Principal
    | 0, _ => reject .resourceLimit "recursive ownership fixed point exhausted"
    | n + 1, current => do
      let next ← current.mapM fun (t, old) => do
        let value ← deriveUseStep program state (current.filter (fun p => p.1 != t)) program.limits.normalization t
        return (t, old.meet value)
      if next == current then deriveUseStep program state next program.limits.normalization type
      else iterate n next
  iterate program.limits.solving initial

end Glorious.Semantics
