import GloriousLanguage.Origins

/-! The source-to-kernel boundary uses executable parameter plans, exact
capture contexts and AST child positions. These are not a source soundness
proof or a claim that all synthetic/desugared origins are complete. -/
namespace Glorious.Language.SourceChecks

open Kernel Elaboration

example {program : Kernel.Program} {context sources locals names plans}
    (checked : Parameters program context sources locals names plans) :
    plans.map Prod.fst = locals := checked.formals

example (first second x y : Local) (body : Code) :
    parameterPrologue [(first,.bind x),(second,.bind y)] body =
      .choose ⟨first.id,[]⟩ [.clause (.bind x)
        (.choose ⟨second.id,[]⟩ [.clause (.bind y) body])] := rfl

example {program : Kernel.Program} {context localSlot locals names plans} :
    ¬ Parameters program context [] (localSlot :: locals) names plans := by
  intro impossible
  cases impossible

example {outer inner : Elaboration.Context} {sources captures localSlot}
    (extended : ExtendsWithCaptures outer inner sources captures)
    (resident : localSlot ∈ inner.typed.locals) : localSlot ∈ captures := by
  subst inner
  exact resident

example (context : Elaboration.Context) (function : Function) :
    (FunctionContext context function).typed.static.unsafeAllowed = false := rfl

example (context : Elaboration.Context) (function : Function) :
    (FunctionContext context function).typed.static.scope.currentRegion = some function.activationRegion := rfl

example {program : Kernel.Program} {context source signature function arguments captures}
    (checked : Closure program context source signature function arguments captures) :
    Instance program function.declaration arguments function := checked.instance

example (formal : Local) (pattern : Pattern) (body : Code) :
    parameterPrologue ((some formal).toList.zip [pattern]) body =
      .choose ⟨formal.id,[]⟩ [.clause pattern body] := rfl

private def referenceTemplate : Function :=
  { declaration := default
    captures := [⟨4,.reference .shared (.parameter 7 .region) .unit,false⟩]
    parameters := []
    signature := ⟨[⟨7,"captured_region",.region,none⟩],[],
      .reference .shared (.parameter 7 .region) .unit,.row [] [],[],false⟩
    body := .bind ⟨5,.reference .shared (.parameter 7 .region) .unit,false⟩
      (.borrow ⟨4,[.dereference]⟩ .shared (.parameter 7 .region)) (.result ⟨5,[]⟩)
    activationRegion := 7
    namedExit := none }

/-- The capture type, signature and executable borrow use the same ordinary
substitution; the callee's numerically identical lexical region cannot capture
the already concrete caller lifetime. -/
example :
    let instantiated := referenceTemplate.instantiate [(7,.runtimeRegion 7)]
    (instantiated.captures.map Local.type = [.reference .shared (.runtimeRegion 7) .unit]) ∧
    instantiated.signature.result = .reference .shared (.runtimeRegion 7) .unit ∧
    instantiated.body = .bind ⟨5,.reference .shared (.runtimeRegion 7) .unit,false⟩
      (.borrow ⟨4,[.dereference]⟩ .shared (.runtimeRegion 7)) (.result ⟨5,[]⟩) ∧
    (instantiated.entryScope 100 200).term instantiated.signature.result =
      .reference .shared (.runtimeRegion 7) .unit := by
  simp [referenceTemplate, Function.instantiate, Function.transformTerms, Local.mapTerms, Signature.instantiate,
    Code.instantiate, Code.transformTerms, Atom.mapTerms, Term.substitute, Table.get, ScopeInstantiation.term]

example (function : Function) (region brand : Identity) :
    (function.entryScope region brand).term (.scopedRegion function.activationRegion) =
      .runtimeRegion region := by
  simp [Function.entryScope, ScopeInstantiation.term, Table.get]

example (context : Typing.Context) (callee argument : Local) (code : Code) :
    argument ∈ (BindingContext (context.bind callee) [⟨argument,code⟩]).locals := by
  simp [BindingContext, Typing.Context.bind]

private def head : Source.FunctionHead := default
private def nested : Source.Expr := .function head .unit
private def source : Source.Declaration := .function head (some (.block
  [.discard .unit] (some (.call (.name ["f"] [] []) [nested]))))
private def context : Elaboration.Context := { typed := default, origin := ⟨7,[0]⟩ }

example : Source.NodeAt [source]
    ((((context.child 0).child 1).child 1).origin.node) (.expression nested) := by
  refine ⟨0,[0,1,1],source,rfl,rfl,?_⟩
  exact .child rfl (.child rfl (.child rfl .here))

example : (((context.child 0).child 1).child 1).origin ≠
    (((context.child 0).child 1).child 0).origin := by
  decide

end Glorious.Language.SourceChecks
