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

example (map : Relocation) (pointer : RawPointer) (raw : pointer.allocation = none) :
    map.pointer pointer = pointer := by simp [Relocation.pointer, raw]

example (map : Relocation) (pointer : RawPointer) (id : Identity)
    (external : id ∉ map.roots) (origin : pointer.allocation = some id) :
    map.pointer pointer = pointer := by simp [Relocation.pointer, origin, external]

example (map : Relocation) (pointer : RawPointer) (id base : Identity)
    (selected : id ∈ map.roots) (origin : pointer.allocation = some id)
    (physical : map.physical.get id = some base) :
    (map.pointer pointer).address = base+pointer.offset ∧
    (map.pointer pointer).allocation = some (map.root id) := by
  simp [Relocation.pointer, origin, selected, physical]

example (map : Relocation) (id base : Identity) (root : Root)
    (physical : map.physical.get id = some base) : (map.rootValue id root).base = base := by
  simp [Relocation.rootValue, physical]

example (outer inner : Execution.Context) :
    TailFrames [.scope inner 30 30,.scope inner 20 20,.activation outer 4 10] 4 outer [30,20,10] [] :=
  .scope (.scope .activation)

example (next : Task) : CloseRegions [30,20,30,10] next =
    .closeRegion 30 (.closeRegion 20 (.closeRegion 10 next)) := by rfl

end Glorious.Language.ExecutionChecks
