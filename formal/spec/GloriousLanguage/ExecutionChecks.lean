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
    (arguments : List Term) (payload : List ResolvedPlace) (context : Execution.Context) (destination : Address)
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

private def scopes : ScopeInstantiation := ⟨[(7,70)],[(7,.label 80)]⟩

example : scopes.term (.label (.rigid 7 .brand 0) (.rigid 7 .region 0) .unit) =
    .label (.runtimeBrand (.label 80)) (.runtimeRegion 70) .unit := by
  simp [scopes, ScopeInstantiation.term, Table.get]

/-- Caller-provided concrete identities cannot be captured by identically
numbered names in a callee's lexical namespace. -/
example : scopes.term (.reference .shared (.runtimeRegion 7)
    (.label (.runtimeBrand (.label 7)) (.runtimeRegion 7) .unit)) =
    .reference .shared (.runtimeRegion 7) (.label (.runtimeBrand (.label 7)) (.runtimeRegion 7) .unit) := by
  simp [ScopeInstantiation.term]

example (id : Identity) : Term.runtimeBrand (.label id) ≠ .runtimeBrand (.resumption id) := by
  intro impossible
  cases impossible

example (id : Identity) : Term.runtimeBrand (.resumption id) ≠ .runtimeBrand (.proof id) := by
  intro impossible
  cases impossible

example (id : Identity) : Closed (.runtimeRegion id) := by
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · intro a b c occurs
    cases occurs with | child member _ => simp [Term.children] at member
  · intro a b occurs
    cases occurs with | child member _ => simp [Term.children] at member
  · intro a b c d e occurs
    cases occurs with | child member _ => simp [Term.children] at member
  · intro a b occurs
    cases occurs with | child member _ => simp [Term.children] at member
  · intro a b c occurs
    cases occurs with | child member _ => simp [Term.children] at member

example (map : Relocation) (id level : Identity) :
    map.term (.rigid id .region level) = .rigid id .region level := by
  simp [Relocation.term]

example (map : Relocation) (id : Identity) :
    map.term (.runtimeRegion id) = .runtimeRegion (map.region id) := by simp [Relocation.term]

example (context : Execution.Context) (map : Relocation) :
    (map.context context).instantiation.regions =
      context.instantiation.regions.map (fun (lexical,runtime) => (lexical,map.region runtime)) := rfl

/-- The borrow step uses the explicit reference region, irrespective of the
current innermost allocation region. -/
example {program : Kernel.Program} {world after : World} {context : Execution.Context}
    {place : Place} {mode : Mutability} {region : Identity} {source destination : Address}
    {authority : Authority} {next : Code}
    (resolved : ResolvesPlace world context.environment place source authority)
    (borrowed : Borrows program.declarations world authority mode region source destination after) :
    AtomStep program { world := world, task := .atom context destination (.borrow place mode (.runtimeRegion region)) next }
      (some (.borrow source world.nextLoan))
      { world := after, task := .run context next } :=
  .borrow rfl resolved borrowed

example {program : Kernel.Program} {world : World} {context : Execution.Context}
    {place : Place} {mode : Mutability} {lexical : Identity} {destination : Address}
    {next : Code} {event : Option Event} {after : State} :
    ¬ AtomStep program { world := world, task := .atom context destination (.borrow place mode (.rigid lexical .region 0)) next }
      event after := by
  intro impossible
  cases impossible <;> simp_all

example {program : Kernel.Program} {world : World} {context : Execution.Context}
    {lexical : Identity} {destination : Address} {next : Code} {event : Option Event} {after : State} :
    ¬ AtomStep program { world := world, task := .atom context destination (.label (.rigid lexical .brand 0)) next }
      event after := by
  intro impossible
  cases impossible <;> simp_all

end Glorious.Language.ExecutionChecks
