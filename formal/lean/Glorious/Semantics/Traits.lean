import Glorious.Semantics.Resolve

namespace Glorious.Semantics

structure SelectedImpl where
  declaration : ImplDecl
  substitution : Substitution
  inference : Inference
  deriving Repr

def equalConstraint (a b : Constraint) : Bool :=
  match a, b with
  | .equal a b, .equal c d | .outlives a b, .outlives c d
  | .rowIncludes a b, .rowIncludes c d => a == c && b == d
  | .implements d args n, .implements e other m => d == e && args == other && n == m
  | .use t q, .use u r => t == u && q.lower == r.lower && q.upper == r.upper
  | .callable r a o e u, .callable s b p f v => r == s && a == b && o == p && e == f && u == v
  | .runsIn r a args after u, .runsIn s b bs post v => r == s && a == b && args == bs && after == post && u == v
  | _, _ => false

def receiverType : Term → Term × Option ReceiverMode
  | .reference .shared _ value => (value, some .shared)
  | .reference .unique _ value => (value, some .unique)
  | value => (value, some .owned)

def callableSignature (program : Program) (receiver : Term) : InferM Signature := do
  let receiver ← zonk program receiver
  let (valueType, requestedMode) := receiverType receiver
  match valueType with
  | .callable declaration arguments =>
    let function ← getRequired (program.function declaration) .missingEvidence "unknown nominal callable identity"
    let subs ← bindArguments function.signature.generics arguments
    let signature ← substituteSignature program.limits.normalization subs function.signature
    match signature.receiver, requestedMode with
    | some .owned, some .shared | some .owned, some .unique | some .unique, some .shared =>
      reject .missingEvidence "receiver form does not support invocation"
    | _, _ => pure ()
    return signature
  | .label _ _ output => return { arguments := [output], output := .bottom }
  | .continuation _ argument output effects => return { arguments := [argument], output, effects }
  | _ =>
    let state ← get
    let evidence := state.assumptions.filterMap fun c => match c with
      | .callable actual (.tuple args) output effects unsafeCall =>
        if actual == receiver then some ({ arguments := args, output, effects, unsafeCall } : Signature) else none
      | _ => none
    match evidence with
    | [signature] => return signature
    | [] => reject .missingEvidence "Fn evidence is required for this exact receiver"
    | _ => reject .ambiguous "multiple incompatible callable contracts"

def solveRowInclusion (program : Program) (allowed required : Term) : InferM Unit := do
  let allowed ← zonk program allowed
  let required ← zonk program required
  match allowed, required with
  | .row ai cursor, .row ri rt =>
    let known := ri.all (fun effectInstance => ai.contains effectInstance)
    let tails := rt.all (fun tail => cursor.contains tail)
    if known && tails then return
    let state ← get
    if state.assumptions.any (equalConstraint (.rowIncludes allowed required)) then return
    match cursor with
    | [.meta id kind level] =>
      let remainder := ri.filter (fun effectInstance => !ai.contains effectInstance)
      assignMeta program id kind level (.row remainder rt)
    | _ => reject .missingEffect "required effect instances are not included in the permitted row"
  | _, _ =>
    let state ← get
    require (allowed == required || state.assumptions.any (equalConstraint (.rowIncludes allowed required)))
      .missingEvidence "unresolved effect-row inclusion"

mutual
  def solveConstraint (program : Program) : Nat → List Constraint → Constraint → InferM Unit
    | 0, _, _ => reject .resourceLimit "trait or constraint proof search exhausted"
    | fuel + 1, active, obligation => do
      let state ← get
      if state.assumptions.any (equalConstraint obligation) then return
      require (!(active.any (equalConstraint obligation))) .missingEvidence "recursive user trait obligations do not prove themselves"
      let active := obligation :: active
      match obligation with
      | .equal a b =>
        let a ← zonk program a
        let b ← zonk program b
        for term in [a, b] do
          match term with
          | .projection traitDecl _ arguments _ => solveConstraint program fuel active (.implements traitDecl arguments false)
          | _ => pure ()
        unify program fuel a b
        let left ← zonk program a
        let right ← zonk program b
        require (left == right) .missingEvidence "associated equality remains unproved"
      | .outlives long short =>
        let long ← zonk program long
        let short ← zonk program short
        require (long.kind == .region && short.kind == .region) .kindMismatch "outlives requires regions"
        let result ← regionOutlives fuel (← get).assumptions long short
        require result .escapingReference "required outlives relation is not established"
      | .rowIncludes allowed required => solveRowInclusion program allowed required
      | .use type quantity =>
        let capability ← deriveUse program (← get) type
        let valid := match quantity.upper with
          | none => capability == .duplicable
          | some upper => quantity.lower ≤ upper &&
            match capability with
            | .duplicable => true
            | .affine => upper ≤ 1
            | .exact => quantity.lower == 1 && upper == 1
        require valid .missingEvidence "requested use interval is not permitted by the type's principal class"
      | .implements traitDecl arguments negative =>
        let arguments ← arguments.mapM (zonk program)
        let selected ← selectImpl program fuel active traitDecl arguments negative
        set selected.inference
        let values ← selected.declaration.associated.mapM fun (member, value) => do
          pure (⟨traitDecl, member, arguments,
            ← substitute program.limits.normalization selected.substitution value⟩ : ProjectionEvidence)
        modify fun s => { s with projections := s.projections ++ values,
          assumptions := .implements traitDecl arguments negative :: s.assumptions }
        let trait ← getRequired (program.traitDecl traitDecl) .unknownName "unknown trait declaration"
        let traitSubs ← bindArguments trait.generics arguments
        for supertrait in trait.supertraits do
          solveConstraint program fuel active (← substituteConstraint fuel traitSubs supertrait)
      | .callable receiver arguments output effects unsafeAllowed =>
        let signature ← callableSignature program receiver
        require (!signature.unsafeCall || unsafeAllowed) .unsafeOperation "unsafe callable does not satisfy a safe Fn bound"
        unify program fuel arguments (.tuple signature.arguments)
        unify program fuel output signature.output
        unify program fuel effects signature.effects
        for requirement in signature.constraints do solveConstraint program fuel active requirement
      | .runsIn receiver access arguments after unsafeAllowed =>
        let signature ← callableSignature program receiver
        require (!signature.unsafeCall || unsafeAllowed) .unsafeOperation "unsafe callable does not satisfy a safe RunsIn bound"
        unify program fuel arguments (.tuple signature.arguments)
        let access ← zonk program access
        let after ← zonk program after
        match access with
        | .reference _ region environment =>
          match environment with
          | .environment _ scope =>
            solveConstraint program fuel active (.outlives scope region)
            unify program fuel after environment
          | _ => reject .kindMismatch "RunsIn borrowed access requires a sealed environment"
        | .environment .. =>
          require (after.kind == .type) .kindMismatch "RunsIn post-environment is not a type"
        | _ => reject .missingEvidence "RunsIn requires exact checked environment access"
        -- The resource transition is checked against the emitted invocation by
        -- Analyze; this type-level check is not a fabricated control summary.
      | .higherRanked binders obligations =>
        let before ← get
        modify fun s => { s with level := s.level + 1 }
        let substitutions ← binders.mapM fun binder => do pure (binder.id, ← freshRigid binder.kind)
        for requirement in obligations do
          solveConstraint program fuel active (← substituteConstraint fuel substitutions requirement)
        let after ← get
        for cell in after.cells.filter (fun c => c.level ≤ before.level) do
          match cell.solution with
          | none => pure ()
          | some value =>
            let terms ← walkTerm fuel value
            require (!(terms.any fun t => match t with | .rigid _ _ u => u > before.level | _ => false))
              .universeLeak "higher-ranked proof leaked a rigid placeholder"
        modify fun s => { s with level := before.level, assumptions := before.assumptions }

  def selectImpl (program : Program) (fuel : Nat) (active : List Constraint)
      (traitDecl : DeclId) (arguments : List Term) (negative : Bool) : InferM SelectedImpl := do
    match fuel with
    | 0 => reject .resourceLimit "implementation selection exhausted"
    | remaining + 1 =>
      let initial ← get
      let candidates := program.implementations.filter (fun i => i.traitDecl == traitDecl)
      let attempts := candidates.map fun implementation => do
        let action : InferM Substitution := do
          let substitutions ← instantiate program implementation.generics []
          let head ← implementation.arguments.mapM (substitute program.limits.normalization substitutions)
          require (head.length == arguments.length) .kindMismatch "implementation head arity differs"
          for (left, right) in head.zip arguments do unify program remaining left right
          for requirement in implementation.requirements do
            solveConstraint program remaining active (← substituteConstraint remaining substitutions requirement)
          return substitutions
        (action.run initial).map (fun (subs, inference) => (⟨implementation, subs, inference⟩ : SelectedImpl))
      let successes := attempts.filterMap (fun result => result.toOption)
      let limits := attempts.filterMap fun result => match result with
        | .error d => if d.problem == .resourceLimit then some d else none
        | _ => none
      require limits.isEmpty .resourceLimit "an implementation candidate exhausted proof search; uniqueness is unknown"
      match successes with
      | [selected] =>
        require (selected.declaration.negative == negative) .missingEvidence "explicit trait exclusion contradicts the requested relation"
        return selected
      | [] => reject .missingEvidence "no coherent implementation proves the requested trait fact"
      | _ => reject .coherence "multiple applicable implementations"
end

def solvePending (program : Program) : InferM Unit := do
  let pending := (← get).obligations
  modify fun state => { state with obligations := [] }
  for obligation in pending do solveConstraint program program.limits.solving [] obligation
  require (← get).obligations.isEmpty .missingEvidence "constraint solving left deferred proof obligations"

def subtype (program : Program) (source target : Term) : InferM Unit := do
  let source ← zonk program source
  let target ← zonk program target
  if source == .bottom then return
  match source, target with
  | .reference sourceMode sourceRegion sourceType, .reference targetMode targetRegion targetType =>
    require (sourceMode == targetMode || (sourceMode == .unique && targetMode == .shared))
      .typeMismatch "a shared reference cannot supply unique access"
    solveConstraint program program.limits.solving [] (.outlives sourceRegion targetRegion)
    -- Invariant unique referents and exact brands never participate in a
    -- size-based or nominally unrelated coercion.
    unifyTypes program sourceType targetType
  | _, _ => unifyTypes program source target

def implHeadsOverlap (program : Program) (a b : ImplDecl) : Check Bool := do
  if a.traitDecl != b.traitDecl then return false
  let action : InferM Unit := do
    let sa ← instantiate program a.generics []
    let sb ← instantiate program b.generics []
    let aa ← a.arguments.mapM (substitute program.limits.normalization sa)
    let bb ← b.arguments.mapM (substitute program.limits.normalization sb)
    require (aa.length == bb.length) .kindMismatch "implementation arity differs"
    for (left, right) in aa.zip bb do unifyTypes program left right
  match action.run {} with
  | .ok _ => return true
  | .error problem =>
    if problem.problem == .resourceLimit || problem.problem == .missingEvidence || problem.problem == .ambiguous then
      .error problem
    else return false

def validateCoherence (program : Program) : Check Unit := do
  for implementation in program.implementations do
    let trait ← getRequired (program.traitDecl implementation.traitDecl) .unknownName "implementation names an unknown trait"
    require (!trait.sealed) .coherence "source cannot implement a sealed intrinsic relation" implementation.header.span
    require (!trait.unsafeContract || implementation.unsafeImpl) .unsafeOperation "unsafe trait requires an unsafe implementation"
    let self ← getRequired implementation.arguments.head? .kindMismatch "trait implementation has no self argument"
    let self ← normalize program {} program.limits.normalization [] self
    let localSelf := match self with
      | .nominal declaration _ => declaration.packageId == implementation.header.id.packageId
      | _ => false
    require (trait.header.id.packageId == implementation.header.id.packageId || localSelf)
      .coherence "orphan implementation: neither trait nor outer nominal self is local" implementation.header.span
    require (unique (implementation.associated.map Prod.fst)) .duplicate "duplicate associated definition"
    require (unique (implementation.methods.map Prod.fst)) .duplicate "duplicate trait method definition"
    for other in program.implementations do
      if implementation.header.id != other.header.id then
        require (!(← implHeadsOverlap program implementation other)) .coherence
          "overlapping implementation heads, including aliases; no specialization preference is permitted"

end Glorious.Semantics
