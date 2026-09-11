import Glorious.Semantics.Analyze

namespace Glorious.Semantics

structure SpecializationKey where
  declaration : DeclId
  arguments : List Term
  deriving BEq, DecidableEq, Repr

structure Specialization where
  key : SpecializationKey
  identity : DeclId
  deriving Repr

def mapSignatureTerms (f : Term → Check Term) (signature : Signature) : Check Signature := do
  return { signature with arguments := ← signature.arguments.mapM f,
    output := ← f signature.output, effects := ← f signature.effects }

def mapCallTerms (f : Term → Check Term) (call : CallSite) : Check CallSite := do
  return { call with signature := ← mapSignatureTerms f call.signature,
    inputs := ← call.inputs.mapM (fun input => do return { input with expected := ← f input.expected }) }

def mapPatternTerms (fuel : Nat) (f : Term → Check Term) (pattern : CheckedPattern) : Check CheckedPattern := do
  match fuel with
  | 0 => reject .resourceLimit "pattern specialization exhausted"
  | fuel + 1 =>
    match pattern with
    | .wildcard type => return .wildcard (← f type)
    | .binder id name type => return .binder id name (← f type)
    | .constructor type key fields => return .constructor (← f type) key (← fields.mapM (mapPatternTerms fuel f))

def mapPatternBindingTerms (f : Term → Check Term) (binding : PatternBinding) : Check PatternBinding := do
  return { binding with slot.type := ← f binding.slot.type,
    borrowed := ← binding.borrowed.mapM (fun (mode, region) => do return (mode, ← f region)) }

def mapCoreOpTerms (fuel : Nat) (f : Term → Check Term) (operation : CoreOp) : Check CoreOp := do
  match operation with
  | .declare slot => return .declare { slot with type := ← f slot.type }
  | .constant dst value => return .constant dst (← f value)
  | .closure dst function args captures materialized => return .closure dst function (← args.mapM f)
      (← captures.mapM (fun capture => do return { capture with type := ← f capture.type })) materialized
  | .borrow dst mode region source => return .borrow dst mode (← f region) source
  | .invoke dst call => return .invoke dst (← mapCallTerms f call)
  | .perform dst op args payload signature => return .perform dst op (← args.mapM f) payload (← mapSignatureTerms f signature)
  | .deconstruct src pattern bindings => return .deconstruct src (← mapPatternTerms fuel f pattern)
      (← bindings.mapM (mapPatternBindingTerms f))
  | .test dst src pattern positive negative => return .test dst src (← mapPatternTerms fuel f pattern) (← f positive) (← f negative)
  | .machine dst binding arguments signature permission => return .machine dst binding arguments (← mapSignatureTerms f signature) permission
  | operation => return operation

def mapCoreTerms (fuel : Nat) (f : Term → Check Term) (core : Core) : Check Core := do
  match fuel with
  | 0 => reject .resourceLimit "typed Core specialization exhausted"
  | fuel + 1 =>
    match core with
    | .result place => return .result place
    | .step operation next => return .step (← mapCoreOpTerms fuel f operation) (← mapCoreTerms fuel f next)
    | .bind destination computation next => return .bind { destination with type := ← f destination.type }
        (← mapCoreTerms fuel f computation) (← mapCoreTerms fuel f next)
    | .scoped scope body => return .scoped scope (← mapCoreTerms fuel f body)
    | .cases subject clauses => return .cases subject (← clauses.mapM fun (.clause pattern bindings body) => do
        return .clause (← mapPatternTerms fuel f pattern) (← bindings.mapM (mapPatternBindingTerms f)) (← mapCoreTerms fuel f body))
    | .label identity brand region type body => return .label identity (← f brand) (← f region) (← f type) (← mapCoreTerms fuel f body)
    | .handle identity body clauses => return .handle identity (← mapCoreTerms fuel f body) (← clauses.mapM fun clause => do
        match clause with
        | .completion pattern bindings body => return .completion (← mapPatternTerms fuel f pattern)
            (← bindings.mapM (mapPatternBindingTerms f)) (← mapCoreTerms fuel f body)
        | .operation op effectInstance patterns bindings k policy body => return .operation op (← effectInstance.mapM f)
            (← patterns.mapM (mapPatternTerms fuel f)) (← bindings.mapM (mapPatternBindingTerms f))
            (← k.mapM (fun slot => do return { slot with type := ← f slot.type })) policy (← mapCoreTerms fuel f body))
    | .tail call => return .tail (← mapCallTerms f call)
    | .leave brand payload => return .leave (← f brand) payload
    | .fatal reason => return .fatal reason

def coreCallableKeys : Nat → Core → Check (List SpecializationKey)
  | 0, _ => reject .resourceLimit "specialization dependency projection exhausted"
  | fuel + 1, core => do
    match core with
    | .step operation next =>
      let own := match operation with | .closure _ function arguments _ _ => [⟨function, arguments⟩] | _ => []
      return own ++ (← coreCallableKeys fuel next)
    | .bind _ a b => return (← coreCallableKeys fuel a) ++ (← coreCallableKeys fuel b)
    | .scoped _ body | .label _ _ _ _ body => coreCallableKeys fuel body
    | .cases _ clauses => return (← clauses.mapM (fun (.clause _ _ body) => coreCallableKeys fuel body)).flatten
    | .handle _ body clauses => return (← coreCallableKeys fuel body) ++ (← clauses.mapM (fun clause => match clause with
        | .completion _ _ body | .operation _ _ _ _ _ _ body => coreCallableKeys fuel body)).flatten
    | _ => return []

def rewriteSpecializedType (fuel : Nat) (specializations : List Specialization) (type : Term) : Check Term := do
  match fuel with
  | 0 => reject .resourceLimit "specialized identity rewriting exhausted"
  | fuel + 1 =>
    match type with
    | .callable declaration arguments =>
      match specializations.find? (fun s => s.key == ⟨declaration, arguments⟩) with
      | some specialization => return .callable specialization.identity []
      | none => return .callable declaration arguments
    | _ => type.mapChildrenM (rewriteSpecializedType fuel specializations)

def rewriteSpecializedCore (fuel : Nat) (specializations : List Specialization) (core : Core) : Check Core := do
  let core ← mapCoreTerms fuel (rewriteSpecializedType fuel specializations) core
  let rec rewrite : Nat → Core → Check Core
    | 0, _ => reject .resourceLimit "specialized callable lowering exhausted"
    | fuel + 1, core =>
      match core with
      | .step (.closure dst function arguments captures materialized) next => do
        let selected := specializations.find? (fun s => s.key == ⟨function, arguments⟩)
        return .step (.closure dst (selected.map (·.identity) |>.getD function)
          (if selected.isSome then [] else arguments) captures materialized) (← rewrite fuel next)
      | .step operation next => return .step operation (← rewrite fuel next)
      | .bind slot a b => return .bind slot (← rewrite fuel a) (← rewrite fuel b)
      | .scoped scope body => return .scoped scope (← rewrite fuel body)
      | .label id brand region type body => return .label id brand region type (← rewrite fuel body)
      | .cases subject clauses => return .cases subject (← clauses.mapM (fun (.clause p bs body) => return .clause p bs (← rewrite fuel body)))
      | .handle id body clauses => return .handle id (← rewrite fuel body) (← clauses.mapM (fun clause => match clause with
          | .completion p bs body => return .completion p bs (← rewrite fuel body)
          | .operation op args ps bs k q body => return .operation op args ps bs k q (← rewrite fuel body)))
      | _ => return core
  rewrite fuel core

def monomorphize (program : CoreProgram) (roots : List SpecializationKey) : Check CoreProgram := do
  let initialId := 1 + program.source.functions.foldl (fun id f => max id f.header.id.localId) 0
  let rec expand : Nat → List SpecializationKey → List Specialization → List CoreFunction → Check (List Specialization × List CoreFunction)
    | 0, _, _, _ => reject .resourceLimit "runtime specialization worklist exhausted"
    | _, [], selected, functions => return (selected, functions)
    | fuel + 1, key :: rest, selected, functions => do
      if selected.any (fun s => s.key == key) then expand fuel rest selected functions else
        match program.function key.declaration with
        | none =>
          require ((program.source.constructor key.declaration).isSome || (program.source.operation key.declaration).isSome ||
            (program.source.function key.declaration).isSome) .missingEvidence "runtime callable dependency is absent"
          expand fuel rest selected functions
        | some function =>
          let subs ← bindArguments function.signature.generics key.arguments
          let normalizeTerm := fun term => do
            let term ← substitute program.source.limits.normalization subs term
            normalize program.source program.inference program.source.limits.normalization [] term
          let body ← mapCoreTerms program.source.limits.elaboration normalizeTerm function.body
          let signature ← substituteSignature program.source.limits.normalization subs function.signature
          let signature ← mapSignatureTerms normalizeTerm signature
          for type in signature.output :: signature.effects :: signature.arguments do
            require (closedTerm program.source.limits.normalization type) .missingEvidence "runtime specialization retains an inference variable or generic parameter"
          let identity : DeclId := if key.arguments.isEmpty then key.declaration else ⟨key.declaration.packageId, initialId + selected.length⟩
          let parameters ← function.parameters.mapM (fun slot => do return { slot with type := ← normalizeTerm slot.type })
          let captures ← function.captures.mapM (fun capture => do return { capture with type := ← normalizeTerm capture.type })
          let specialized := { function with declaration := identity, signature := { signature with generics := [] }, parameters, captures, body }
          let dependencies ← coreCallableKeys program.source.limits.elaboration body
          expand fuel (rest ++ dependencies) (selected ++ [⟨key, identity⟩]) (functions ++ [specialized])
  let (selected, functions) ← expand program.source.limits.solving roots [] []
  let rewrite := rewriteSpecializedType program.source.limits.normalization selected
  let functions ← functions.mapM fun function => do
    return { function with signature := ← mapSignatureTerms rewrite function.signature,
      parameters := ← function.parameters.mapM (fun slot => do return { slot with type := ← rewrite slot.type }),
      captures := ← function.captures.mapM (fun capture => do return { capture with type := ← rewrite capture.type }),
      body := ← rewriteSpecializedCore program.source.limits.elaboration selected function.body }
  let declarations := functions.map fun function =>
    ({ header := ⟨function.declaration, ⟨function.declaration.packageId, []⟩,
        s!"specialization#{function.declaration.localId}", .private, function.span⟩,
      signature := function.signature,
      parameters := function.parameters.map (fun slot => ⟨slot.id, s!"p{slot.id}", some slot.type, slot.mutable⟩),
      body := none } : FunctionDecl)
  return { program with functions, source.functions :=
    program.source.functions.filter (fun f => !(functions.any (fun core => core.declaration == f.header.id))) ++ declarations }

end Glorious.Semantics
