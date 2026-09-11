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

example (context : Elaboration.Context) (signature : Signature) (locals : List Local) :
    (FunctionContext context signature locals).typed.static.unsafeAllowed = false := rfl

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
