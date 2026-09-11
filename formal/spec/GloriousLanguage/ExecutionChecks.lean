import GloriousLanguage.Effects

namespace Glorious.Language.ExecutionChecks

open Kernel Execution

private def root : Address := ⟨0,0,[]⟩

/-- Reverse field cleanup remains postorder; a consumed outer shell cannot
be disposed before the nested fields whose ownership it still contains. -/
example {program : Language.Program} {world : World} :
    PatternPlan program world root .owner .owned (.tuple [.wildcard,.tuple [.wildcard]])
      ⟨[.consumeShell root .owner,.consumeShell (root.child 1) .owner],[],
        [.dispose ((root.child 1).child 0) .owner,.dispose (root.child 1) .owner,
          .dispose (root.child 0) .owner,.dispose root .owner]⟩ := by
  have leaf := @PatternPlan.wildcardOwned program world ((root.child 1).child 0) .owner
  have nested := PatternPlan.aggregate (access := .owned) (pattern := .tuple [.wildcard])
    (Or.inl rfl) (PatternPlans.cons (index := 0) leaf PatternPlans.nil)
  have first := @PatternPlan.wildcardOwned program world (root.child 0) .owner
  have fields := PatternPlans.cons (index := 0) first (PatternPlans.cons (index := 1) nested PatternPlans.nil)
  exact PatternPlan.aggregate (Or.inl rfl) fields

example {state : State} {id suspension}
    (found : state.resumptions.get id = some suspension) (active : suspension.active = true) :
    ¬ ClauseSettled state (some id) := by
  rintro ⟨other, selected, _, inactive⟩
  have same := Option.some.inj (found.symm.trans selected)
  subst other
  simp_all

example {program : Kernel.Program} (world : World) (handler : InstalledHandler) (value : Address) :
    EffectStep program { world := world, task := .finishClause handler false none value }
      none { world := world, task := .yield handler.environment value } := by
  exact EffectStep.finishedLentClause rfl trivial

example (context : Execution.Context) (destination : Address) (binding : RuntimeBinding)
    (operands : List Address) (state : List Nat) (next : Code) :
    ¬ SnapshotFrame (.hostCallback context destination binding operands state next) := by
  exact fun impossible => impossible

example (program : Kernel.Program) (world : World) (operation : DeclId)
    (arguments : List Term) (payload : List Address) (context : Execution.Context) (destination : Address)
    (binding : RuntimeBinding) (operands : List Address) (state : List Nat) (next : Code) :
    ¬ Bypasses program world operation arguments payload (.hostCallback context destination binding operands state next) := by
  exact fun impossible => impossible

end Glorious.Language.ExecutionChecks
