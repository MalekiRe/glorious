import OwnershipMir.CallOwnership

namespace OwnershipMir

theorem State.declared_without_temp {n : Nat} {declarations : Declarations} {signature : Signature}
    {state : State n} (valid : state.Declared declarations signature) :
    (State.mk state.slots none).Declared declarations signature :=
  ⟨valid.1, by intro tree impossible; cases impossible⟩

theorem Safe.declared_step {n : Nat} {α : Type} {signature : Signature} {declarations : Declarations}
    {rule : Context n → α → Context n → Prop} {exec : α → State n → Option (State n)}
    {final : Context n} {before after : Configuration n α} (safe : Safe signature rule final before)
    (preserves : ∀ {before after op state next}, rule before op after → state.Typed signature before →
      state.Declared declarations signature → exec op state = some next → next.Declared declarations signature)
    (valid : before.state.Declared declarations signature) (step : Step exec before after) :
    after.state.Declared declarations signature := by
  obtain ⟨current, typed, checked⟩ := safe
  cases step with
  | act executed => cases checked with | act head tail => exact preserves head typed valid executed
  | branch => exact valid
  | loop => exact valid

def Store.Declared {n : Nat} (declarations : Declarations) (signature : Signature) (store : Store n Atom) : Prop :=
  (∀ r slots, store.region r = some slots → ∀ i, Cell.Declared declarations (Atom.kind signature) (slots i)) ∧
    Cell.Declared declarations (Atom.kind signature) store.temp

theorem Store.Declared.replace {n : Nat} {declarations : Declarations} {signature : Signature}
    {store : Store n Atom} (valid : store.Declared declarations signature) (identity : Nat)
    {slots : Region n Atom} {temp : Cell Atom} (localValid : (State.mk slots temp).Declared declarations signature) :
    (store.replace identity slots temp).Declared declarations signature := by
  refine ⟨?_, localValid.2⟩
  intro r actual live
  by_cases same : r = identity
  · subst r
    have bound : identity < store.regions.length := by simpa [Store.replace] using Store.region_bound live
    cases Option.some.inj ((Store.replace_same bound slots temp).symm.trans live)
    exact localValid.1
  · exact valid.1 r actual ((Store.replace_other _ _ _ _ _ same).symm.trans live)

theorem Store.Declared.allocate {n : Nat} {declarations : Declarations} {signature : Signature}
    {store : Store n Atom} (valid : store.Declared declarations signature) {slots : Region n Atom}
    (localValid : (State.mk slots none).Declared declarations signature) :
    (store.allocate slots).Declared declarations signature := by
  refine ⟨?_, by intro tree impossible; cases impossible⟩
  intro r actual live
  have bound : r < store.regions.length + 1 := by simpa [Store.allocate] using Store.region_bound live
  by_cases same : r = store.regions.length
  · subst r
    cases Option.some.inj ((Store.allocate_fresh store slots).symm.trans live)
    exact localValid.1
  · exact valid.1 r actual ((Store.allocate_old (by omega) slots).symm.trans live)

theorem Store.Declared.retire {n : Nat} {declarations : Declarations} {signature : Signature}
    {store : Store n Atom} (valid : store.Declared declarations signature) (identity : Nat) :
    (store.retire identity).Declared declarations signature := by
  refine ⟨?_, valid.2⟩
  intro r actual live
  by_cases same : r = identity
  · subst r; rw [Store.retire_same] at live; cases live
  · exact valid.1 r actual ((Store.retire_other _ _ _ same).symm.trans live)

namespace Calls

/-- The invariant covers every live region in the unified store. -/
def Configuration.Declared {n : Nat} (declarations : Declarations) (signature : Signature)
    (config : Configuration n) : Prop := config.store.Declared declarations signature


theorem argument_declared {n : Nat} {declarations : Declarations} {signature : Signature} {value : Value}
    (valid : Layout.Declared declarations (value.layout (Atom.kind signature))) :
    (State.mk (argumentSlots value) none : State (n + 1)).Declared declarations signature := by
  refine ⟨?_, by intro tree impossible; cases impossible⟩
  intro i
  refine Fin.cases ?_ (fun _ => ?_) i
  · intro tree same; cases same; exact valid
  · intro tree impossible; cases impossible

theorem Instruction.Checked.preserves_declarations {n : Nat} {program : Program n} {module : Module}
    {signature : Signature} {before after : Context (n + 1)} {instruction : Instruction n}
    (checked : Instruction.Checked program module before instruction after) {state next : State (n + 1)}
    (typed : state.Typed signature before) (valid : state.Declared program.declarations signature)
    (executed : instruction.exec state = some next) : next.Declared program.declarations signature := by
  cases checked with
  | operation checked => exact checked.preserves_declarations typed valid executed
  | call => cases executed

theorem Safe.declared_step {n : Nat} {program : Program n} {signature : Signature} {final : Context (n + 1)}
    {before after : Configuration n} (safe : Safe program signature final before)
    (valid : before.Declared program.declarations signature) (step : Transition program before after) :
    after.Declared program.declarations signature := by
  cases step with
  | operation live step =>
    cases safe with
    | body found typed checked retained =>
      cases Option.some.inj (live.symm.trans found)
      exact valid.replace _ (OwnershipMir.Safe.declared_step ⟨_, typed, checked⟩
        (fun checked typed valid executed => checked.preserves_declarations typed valid executed)
        ⟨valid.1 _ _ live, valid.2⟩ step)
  | enter resolved resident => exact valid.allocate (argument_declared (valid.2 _ resident))
  | @handoff cleanup store active frame stack caller slots live installed =>
    cases safe with
    | body activeLive typed checked retained =>
      cases checked
      cases retained with
      | cons older callerLive resident returned put next outer release =>
        cases Option.some.inj (live.symm.trans callerLive)
        exact valid.replace _ (put.preserves_declarations (state := ⟨caller, store.temp⟩)
          ⟨resident, typed.2.trans returned⟩ ⟨valid.1 _ _ live, valid.2⟩ installed)
  | clean live step =>
    cases safe with
    | cleaning found typed checked retained =>
      cases Option.some.inj (live.symm.trans found)
      exact valid.replace _ (OwnershipMir.Safe.declared_step ⟨_, typed, checked⟩
        (fun checked typed valid executed => checked.preserves_declarations typed valid executed)
        ⟨valid.1 _ _ live, valid.2⟩ step)
  | retire empty register => exact valid.retire _


theorem Safe.declared_run {n : Nat} {program : Program n} {signature : Signature} {final : Context (n + 1)}
    (functions : program.Checked) {before after : Configuration n} (safe : Safe program signature final before)
    (valid : before.Declared program.declarations signature) (run : Run (Transition program) before after) :
    after.Declared program.declarations signature := by
  induction run with
  | refl => exact valid
  | step head tail ih => exact ih (safe.preservation functions head) (safe.declared_step valid head)

/-- Existing activation transitions preserve immutable loan origins even while
moving values, allocating regions, returning, and retiring empty storage. This
is not reference-validity preservation: that additionally needs admission of
all accesses and lifetime-safe cleanup. -/
theorem Transition.loans {n : Nat} {program : Program n} {before after : Configuration n}
    (step : Transition program before after) : after.store.loans = before.store.loans := by
  cases step <;> rfl

theorem Run.loans {n : Nat} {program : Program n} {before after : Configuration n}
    (run : Run (Transition program) before after) : after.store.loans = before.store.loans := by
  induction run with
  | refl => rfl
  | step head tail ih => exact ih.trans head.loans

theorem Run.loan_graph {n : Nat} {program : Program n} {before after : Configuration n}
    (run : Run (Transition program) before after) (graph : before.store.LoanGraph) : after.store.LoanGraph := by
  simpa only [Store.LoanGraph, Run.loans run] using graph

theorem Run.loan_ancestry {n : Nat} {program : Program n} {before after : Configuration n}
    (run : Run (Transition program) before after) (parent child : Nat) :
    after.store.Ancestor parent child ↔ before.store.Ancestor parent child :=
  Store.ancestor_iff_of_loans_eq (Run.loans run) parent child


theorem enter_contains {n : Nat} {store : Store (n + 1) Atom} {argument : Value}
    (register : store.temp = some argument) (atom : Atom) :
    (store.allocate (argumentSlots argument)).Contains atom ↔ store.Contains atom := by
  have onlyArgument : ∀ root value, argumentSlots (n := n) argument root = some value → value = argument := by
    intro root
    refine Fin.cases ?_ (fun i => ?_) root
    · intro value found; exact (Option.some.inj found).symm
    · intro value found; cases found
  constructor
  · rintro (⟨value, impossible, _⟩ | ⟨region, slots, root, value, live, resident, contains⟩)
    · cases impossible
    · by_cases fresh : region = store.regions.length
      · subst region
        cases Option.some.inj ((store.allocate_fresh (argumentSlots argument)).symm.trans live)
        cases onlyArgument root value resident
        exact Or.inl ⟨argument, register, contains⟩
      · have bound := Store.region_bound live
        have old : region < store.regions.length := by
          simp only [Store.allocate, List.length_append, List.length_singleton] at bound
          omega
        exact Or.inr ⟨region, slots, root, value,
          (Store.allocate_old old (argumentSlots argument)).symm.trans live, resident, contains⟩
  · rintro (⟨value, resident, contains⟩ | ⟨region, slots, root, value, live, resident, contains⟩)
    · cases Option.some.inj (register.symm.trans resident)
      exact Or.inr ⟨store.regions.length, argumentSlots argument, 0, argument,
        store.allocate_fresh (argumentSlots argument), rfl, contains⟩
    · exact Or.inr ⟨region, slots, root, value,
        (Store.allocate_old (Store.region_bound live) (argumentSlots argument)).trans live, resident, contains⟩

theorem enter_borrow_invariant {n : Nat} {store : Store (n + 1) Atom} {signature : Signature} {argument : Value}
    (valid : store.BorrowInvariant signature) (register : store.temp = some argument) :
    (store.allocate (argumentSlots argument)).BorrowInvariant signature ∧
      ∀ via mode address, (store.allocate (argumentSlots argument)).Permitted via mode address ↔
        store.Permitted via mode address := by
  let after := store.allocate (argumentSlots (n := n) argument)
  have handles : ∀ identity, after.HasHandle identity ↔ store.HasHandle identity := by
    intro identity; simp only [Store.HasHandle, after, enter_contains register]
  have ancestry := Store.ancestor_iff_of_loans_eq (before := after) (after := store) rfl
  have active : ∀ identity, after.Active identity ↔ store.Active identity := by
    intro identity; simp only [Store.Active, handles, ancestry]
  change after.BorrowInvariant signature ∧ ∀ via mode address, after.Permitted via mode address ↔ store.Permitted via mode address
  constructor
  · refine ⟨valid.graph, ?_, ?_, ?_⟩
    · intro identity mode target contains
      obtain ⟨loan, found, modeEq, targetEq, lens, value, focused, selected, typed⟩ :=
        valid.references identity mode target ((enter_contains register _).mp contains)
      obtain ⟨slots, live, located⟩ := Option.bind_eq_some_iff.mp focused
      refine ⟨loan, found, modeEq, targetEq, lens, value, ?_, selected, typed⟩
      unfold Store.find
      change ((store.allocate (argumentSlots argument)).region loan.referent.region).bind _ = some lens
      rw [Store.allocate_old (Store.region_bound live) _, live]
      exact located
    · intro left first right last firstFound firstActive lastFound lastActive overlap
      simpa only [ancestry] using valid.compatible left first right last firstFound ((active _).mp firstActive)
        lastFound ((active _).mp lastActive) overlap
    · intro identity
      change (store.allocate _).mass _ _ ≤ 1
      rw [enter_mass store argument register]
      exact valid.unique identity
  · intro via mode address
    simp only [Store.Permitted, handles, active, ancestry]
    rfl


theorem entry_borrow_safe {n : Nat} {program : Program n} {signature : Signature}
    {store : Store (n + 1) Atom} {identity active : Nat} {function : Function n} {argument : Value}
    (destination : Place (n + 1)) (next : Body n) (cleanup : Code (n + 1) (Op (n + 1))) (stack : List (Frame n))
    (selected : program identity = some function) (register : store.temp = some argument)
    (valid : store.BorrowInvariant signature) :
    ∃ after, Transition program ⟨.body (.act (.call identity destination) next) cleanup, store, active, stack⟩ after ∧
      after.store.BorrowInvariant signature ∧ after.active = store.regions.length ∧
      after.stack = ⟨active, next, cleanup, destination⟩ :: stack ∧
      (∀ via mode address, after.store.Permitted via mode address ↔ store.Permitted via mode address) := by
  obtain ⟨preserved, permissions⟩ := enter_borrow_invariant valid register
  exact ⟨⟨.body function.body function.cleanup, store.allocate (argumentSlots argument), store.regions.length,
      ⟨active, next, cleanup, destination⟩ :: stack⟩,
    .enter selected register, preserved, rfl, rfl, permissions⟩


end Calls
end OwnershipMir
