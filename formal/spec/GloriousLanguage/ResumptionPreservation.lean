import GloriousLanguage.PointerPreservation
import GloriousLanguage.Contracts

/-! The whole-machine resumption budget invariant and trace accounting.
The transition classification below is derived from the real `Step`, never
used as an alternative execution relation or an assumed output invariant. -/
namespace Glorious.Language

theorem Quantity.SurfaceResumption.bound {quantity : Quantity} {upper : Nat}
    (surface : quantity.SurfaceResumption) (bound : quantity.upper = some upper) :
    0 < upper ∧ quantity.lower ≤ upper := by
  rcases surface with rfl | ⟨_,positive,_,rfl⟩ <;> simp_all <;> omega

namespace Execution

theorem Suspension.Accounted.used_bound {suspension : Suspension} {upper : Nat}
    (accounted : suspension.Accounted) (bound : suspension.quantity.upper = some upper) : suspension.used ≤ upper := by
  cases active : suspension.active with
  | false => exact (accounted.settled active).2.2 upper bound
  | true =>
      have equal := Option.some.inj (bound.symm.trans (accounted.active active).2)
      exact equal ▸ Nat.le_add_left _ _

theorem Suspension.Accounted.obligation {suspension : Suspension}
    (accounted : suspension.Accounted) (active : suspension.active = true) : ActiveObligation suspension :=
  ⟨active,accounted.original,accounted.quantity,(accounted.active active).2⟩

/-- Exact projection of the only state mutations that affect suspension
budgets. The untouched case excludes budget events as well as table changes. -/
inductive ResumptionChange : State → Option Event → State → Prop where
  | unchanged {before after event} : after.resumptions = before.resumptions →
      after.nextContinuation = before.nextContinuation →
      (∀ id last, event ≠ some (.replay id last)) → (∀ id, event ≠ some (.cancel id)) →
      (∀ id, event ≠ some (.suspend id)) →
      ResumptionChange before event after
  | create {before after suspension} : suspension.identity = before.nextContinuation →
      suspension.original = true → suspension.active = true → suspension.used = 0 →
      suspension.quantity.SurfaceResumption → suspension.quantity.upper = some suspension.remaining →
      after.resumptions = before.resumptions.set before.nextContinuation suspension →
      after.nextContinuation = before.nextContinuation+1 → ResumptionChange before (some (.suspend before.nextContinuation)) after
  | last {before after id suspension} : before.resumptions.get id = some suspension →
      ActiveObligation suspension → suspension.remaining = 1 →
      after.resumptions = before.resumptions.set id { suspension with remaining := 0, used := suspension.used+1, active := false } →
      after.nextContinuation = before.nextContinuation → ResumptionChange before (some (.replay id true)) after
  | copy {before after id suspension} : before.resumptions.get id = some suspension →
      ActiveObligation suspension → 1 < suspension.remaining →
      after.resumptions = before.resumptions.set id { suspension with remaining := suspension.remaining-1, used := suspension.used+1 } →
      after.nextContinuation = before.nextContinuation → ResumptionChange before (some (.replay id false)) after
  | cancel {before after id suspension} : before.resumptions.get id = some suspension →
      ActiveObligation suspension → suspension.quantity.lower = 0 →
      after.resumptions = before.resumptions.set id { suspension with remaining := 0, active := false } →
      after.nextContinuation = before.nextContinuation → ResumptionChange before (some (.cancel id)) after

theorem EffectStep.resumption_change {program : Kernel.Program} {before after : State} {event : Option Event}
    (step : EffectStep program before event after) : ResumptionChange before event after := by
  cases step
  all_goals first
    | exact .unchanged rfl rfl (by intros; simp) (by intros; simp) (by intros; simp)
    | skip
  case suspend =>
    rename_i permission _ _ _ suspension
    subst suspension
    refine ResumptionChange.create ?_ ?_ ?_ ?_ ?_ ?_ rfl rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact permission.1
    · assumption
  case suspendTailArm =>
    rename_i permission _ _ suspension
    subst suspension
    refine ResumptionChange.create ?_ ?_ ?_ ?_ ?_ ?_ rfl rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact permission.1
    · assumption
  case resumeLast =>
    rename_i found active remaining _ _
    exact .last found active remaining rfl rfl
  case resumeCopy =>
    rename_i found active remaining copied _
    exact .copy found active remaining rfl (by rw [copied.result])
  case cancel =>
    rename_i found active optional _
    exact .cancel found active optional rfl rfl

theorem Step.resumption_change {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {event : Option Event} (step : Step program host before event after) :
    ResumptionChange before event after := by
  rcases step with localStep | atom | effect | control | primitive | foreign
  · cases localStep <;> exact .unchanged rfl rfl (by intros; simp) (by intros; simp) (by intros; simp)
  · cases atom <;> exact .unchanged rfl rfl
      (by intros; simp <;> split <;> (try split) <;> simp)
      (by intros; simp <;> split <;> (try split) <;> simp)
      (by intros; simp <;> split <;> (try split) <;> simp)
  · exact effect.resumption_change
  · cases control <;> exact .unchanged rfl rfl (by intros; simp) (by intros; simp) (by intros; simp)
  · cases primitive <;> exact .unchanged rfl rfl (by intros; simp) (by intros; simp) (by intros; simp)
  · cases foreign <;> exact .unchanged rfl rfl (by intros; simp) (by intros; simp) (by intros; simp)

theorem State.ResumptionsAccounted.empty {state : State} (empty : state.resumptions = []) : state.ResumptionsAccounted := by
  constructor
  · simp [empty,Table.Unique]
  all_goals intros; simp [empty,Table.get] at *

theorem State.SuspensionsWellFormed.empty {state : State} (empty : state.resumptions = [])
    (homes : ∀ rootId root id, state.world.roots.get rootId = some root →
      root.home = .suspended id → id < state.nextContinuation) : state.SuspensionsWellFormed := by
  refine ⟨State.ResumptionsAccounted.empty empty,?_,?_,?_,homes⟩
  all_goals intros; simp [empty,Table.get] at *

theorem State.ResumptionsAccounted.transport {before after : State} (valid : before.ResumptionsAccounted)
    (table : after.resumptions = before.resumptions) (counter : before.nextContinuation ≤ after.nextContinuation) :
    after.ResumptionsAccounted := by
  refine ⟨by simpa [table] using valid.unique,?_,?_,?_⟩
  · intro id suspension found
    exact valid.identity id suspension (by simpa [table] using found)
  · intro id suspension found
    exact Nat.lt_of_lt_of_le (valid.fresh id suspension (by simpa [table] using found)) counter
  · intro id suspension found
    exact valid.accounted id suspension (by simpa [table] using found)

theorem State.ResumptionsAccounted.set {before after : State} {id : Identity} {suspension : Suspension}
    (valid : before.ResumptionsAccounted) (accounted : suspension.Accounted) (identity : suspension.identity = id)
    (fresh : id < after.nextContinuation) (counter : before.nextContinuation ≤ after.nextContinuation)
    (table : after.resumptions = before.resumptions.set id suspension) : after.ResumptionsAccounted := by
  refine ⟨by rw [table]; exact valid.unique.set _ _,?_,?_,?_⟩
  · intro target actual found
    rw [table] at found
    by_cases same : target = id
    · subst target
      rw [Table.get_set] at found
      cases found
      exact identity
    · exact valid.identity target actual (by simpa [Table.get_set_other _ _ _ _ same] using found)
  · intro target actual found
    rw [table] at found
    by_cases same : target = id
    · exact same ▸ fresh
    · exact Nat.lt_of_lt_of_le (valid.fresh target actual (by simpa [Table.get_set_other _ _ _ _ same] using found)) counter
  · intro target actual found
    rw [table] at found
    by_cases same : target = id
    · subst target
      rw [Table.get_set] at found
      cases found
      exact accounted
    · exact valid.accounted target actual (by simpa [Table.get_set_other _ _ _ _ same] using found)

theorem ActiveObligation.last_accounted {suspension : Suspension} (active : ActiveObligation suspension)
    (remaining : suspension.remaining = 1) :
    Suspension.Accounted { suspension with remaining := 0, used := suspension.used+1, active := false } := by
  refine ⟨active.2.1,active.2.2.1,by simp,?_⟩
  intro _
  refine ⟨rfl,?_,?_⟩
  · have lower := (active.2.2.1.bound active.2.2.2).2
    dsimp
    omega
  · intro upper bound
    have equal := Option.some.inj (bound.symm.trans active.2.2.2)
    dsimp at equal ⊢
    omega

theorem ActiveObligation.copy_accounted {suspension : Suspension} (active : ActiveObligation suspension)
    (remaining : 1 < suspension.remaining) :
    Suspension.Accounted { suspension with remaining := suspension.remaining-1, used := suspension.used+1 } := by
  refine ⟨active.2.1,active.2.2.1,?_,?_⟩
  · intro _
    refine ⟨by dsimp; omega,?_⟩
    dsimp
    rw [active.2.2.2]
    congr 1
    omega
  · simp [active.1]

theorem ActiveObligation.cancel_accounted {suspension : Suspension} (active : ActiveObligation suspension)
    (optional : suspension.quantity.lower = 0) :
    Suspension.Accounted { suspension with remaining := 0, active := false } := by
  refine ⟨active.2.1,active.2.2.1,by simp,?_⟩
  intro _
  refine ⟨rfl,by simp [optional],?_⟩
  intro upper bound
  have equal := Option.some.inj (bound.symm.trans active.2.2.2)
  dsimp at equal ⊢
  omega

theorem ResumptionChange.accounted {before after : State} {event : Option Event}
    (change : ResumptionChange before event after) (valid : before.ResumptionsAccounted) : after.ResumptionsAccounted := by
  cases change with
  | unchanged table counter _ _ _ => exact valid.transport table (Nat.le_of_eq counter.symm)
  | create identity original active used surface bound table counter =>
      apply valid.set (id := before.nextContinuation) ?_ identity
        (by rw [counter]; exact Nat.lt_succ_self _) (by rw [counter]; exact Nat.le_succ _) table
      refine ⟨original,surface,?_,?_⟩
      · intro _
        exact ⟨(surface.bound bound).1,by simpa [used] using bound⟩
      · simp [active]
  | last found active remaining table counter =>
      have identity := valid.identity _ _ found
      exact valid.set (active.last_accounted remaining) identity
        (by simpa [counter] using valid.fresh _ _ found) (Nat.le_of_eq counter.symm) table
  | copy found active remaining table counter =>
      have identity := valid.identity _ _ found
      exact valid.set (active.copy_accounted remaining) identity
        (by simpa [counter] using valid.fresh _ _ found) (Nat.le_of_eq counter.symm) table
  | cancel found active optional table counter =>
      have identity := valid.identity _ _ found
      exact valid.set (active.cancel_accounted optional) identity
        (by simpa [counter] using valid.fresh _ _ found) (Nat.le_of_eq counter.symm) table

theorem Step.resumptions_accounted {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {event : Option Event} (step : Step program host before event after)
    (valid : before.ResumptionsAccounted) : after.ResumptionsAccounted := step.resumption_change.accounted valid

theorem Run.resumptions_accounted {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event} (run : Run program host before trace after)
    (valid : before.ResumptionsAccounted) : after.ResumptionsAccounted := by
  induction run with
  | refl => exact valid
  | silent step _ ih | visible step _ ih => exact ih (step.resumptions_accounted valid)

def ReplayEvent (id : Identity) : Option Event → Nat
  | some (.replay target _) => if target = id then 1 else 0
  | _ => 0

def ReplayCount (id : Identity) : List Event → Nat
  | [] => 0
  | event :: trace => ReplayEvent id (some event) + ReplayCount id trace

/-- A read-only projection of the actual suspension table, not a second
counter. Newly created identities start at zero; absent identities have no
uses. The execution trace below is proved to agree with this projection. -/
def State.resumptionUses (state : State) (id : Identity) : Nat :=
  ((state.resumptions.get id).map Suspension.used).getD 0

theorem ReplayEvent.absent {id : Identity} {event : Option Event}
    (absent : ∀ target last, event ≠ some (.replay target last)) : ReplayEvent id event = 0 := by
  cases event with
  | none => rfl
  | some event => cases event <;> try rfl
                  exact False.elim (absent _ _ rfl)

theorem State.ResumptionsAccounted.fresh_none {state : State} (valid : state.ResumptionsAccounted) :
    state.resumptions.get state.nextContinuation = none := by
  cases found : state.resumptions.get state.nextContinuation with
  | none => rfl
  | some suspension => exact False.elim (Nat.lt_irrefl _ (valid.fresh _ _ found))

theorem ResumptionChange.uses {before after : State} {event : Option Event}
    (change : ResumptionChange before event after) (valid : before.ResumptionsAccounted) (id : Identity) :
    after.resumptionUses id = before.resumptionUses id + ReplayEvent id event := by
  cases change with
  | unchanged table _ absent _ _ => simp [State.resumptionUses,table,ReplayEvent.absent absent]
  | create _ _ _ used _ _ table _ =>
      by_cases same : id = before.nextContinuation
      · subst id
        simp [State.resumptionUses,table,Table.get_set,valid.fresh_none,used,ReplayEvent]
      · simp [State.resumptionUses,table,Table.get_set_other _ _ _ _ same,ReplayEvent]
  | @last _ target suspension found _ _ table _ =>
      by_cases same : id = target
      · subst target
        simp [State.resumptionUses,table,Table.get_set,found,ReplayEvent]
      · simp [State.resumptionUses,table,Table.get_set_other _ _ _ _ same,ReplayEvent,Ne.symm same]
  | @copy _ target suspension found _ _ table _ =>
      by_cases same : id = target
      · subst target
        simp [State.resumptionUses,table,Table.get_set,found,ReplayEvent]
      · simp [State.resumptionUses,table,Table.get_set_other _ _ _ _ same,ReplayEvent,Ne.symm same]
  | @cancel _ target suspension found _ _ table _ =>
      by_cases same : id = target
      · subst target
        simp [State.resumptionUses,table,Table.get_set,found,ReplayEvent]
      · simp [State.resumptionUses,table,Table.get_set_other _ _ _ _ same,ReplayEvent]

/-- Existing suspension contracts are immutable even when aliases consume
their budget, a copy is replayed, or the original is canceled. Freshness is
essential: a new suspension cannot overwrite an older logical obligation. -/
theorem ResumptionChange.retains_metadata {before after : State} {event : Option Event} {id : Identity} {suspension : Suspension}
    (change : ResumptionChange before event after) (valid : before.ResumptionsAccounted)
    (found : before.resumptions.get id = some suspension) :
    ∃ current, after.resumptions.get id = some current ∧ current.quantity = suspension.quantity ∧
      current.roots = suspension.roots ∧ current.homes = suspension.homes ∧
      current.captureRootLimit = suspension.captureRootLimit ∧
      current.context = suspension.context ∧ current.handler = suspension.handler ∧ current.frames = suspension.frames ∧
      (suspension.active = false → current.active = false) := by
  cases change with
  | unchanged table _ _ _ _ => exact ⟨suspension,by simpa [table] using found,rfl,rfl,rfl,rfl,rfl,rfl,rfl,fun inactive => inactive⟩
  | create _ _ _ _ _ _ table _ =>
      have different := Nat.ne_of_lt (valid.fresh _ _ found)
      exact ⟨suspension,by simpa [table,Table.get_set_other _ _ _ _ different] using found,rfl,rfl,rfl,rfl,rfl,rfl,rfl,fun inactive => inactive⟩
  | @last _ target original previous active _ table _ =>
      by_cases same : id = target
      · subst target
        have equal := Option.some.inj (found.symm.trans previous)
        subst original
        exact ⟨{ suspension with remaining := 0, used := suspension.used+1, active := false },
          by rw [table,Table.get_set],rfl,rfl,rfl,rfl,rfl,rfl,rfl,fun _ => rfl⟩
      · exact ⟨suspension,by simpa [table,Table.get_set_other _ _ _ _ same] using found,rfl,rfl,rfl,rfl,rfl,rfl,rfl,fun inactive => inactive⟩
  | @copy _ target original previous active _ table _ =>
      by_cases same : id = target
      · subst target
        have equal := Option.some.inj (found.symm.trans previous)
        subst original
        exact ⟨{ suspension with remaining := suspension.remaining-1, used := suspension.used+1 },
          by rw [table,Table.get_set],rfl,rfl,rfl,rfl,rfl,rfl,rfl,fun inactive => inactive⟩
      · exact ⟨suspension,by simpa [table,Table.get_set_other _ _ _ _ same] using found,rfl,rfl,rfl,rfl,rfl,rfl,rfl,fun inactive => inactive⟩
  | @cancel _ target original previous _ _ table _ =>
      by_cases same : id = target
      · subst target
        have equal := Option.some.inj (found.symm.trans previous)
        subst original
        exact ⟨{ suspension with remaining := 0, active := false },
          by rw [table,Table.get_set],rfl,rfl,rfl,rfl,rfl,rfl,rfl,fun _ => rfl⟩
      · exact ⟨suspension,by simpa [table,Table.get_set_other _ _ _ _ same] using found,rfl,rfl,rfl,rfl,rfl,rfl,rfl,fun inactive => inactive⟩

theorem ResumptionChange.retains {before after : State} {event : Option Event} {id : Identity} {suspension : Suspension}
    (change : ResumptionChange before event after) (valid : before.ResumptionsAccounted)
    (found : before.resumptions.get id = some suspension) :
    ∃ current, after.resumptions.get id = some current ∧ current.quantity = suspension.quantity ∧
      (suspension.active = false → current.active = false) := by
  obtain ⟨current,present,quantity,_,_,_,_,_,_,inactive⟩ := change.retains_metadata valid found
  exact ⟨current,present,quantity,inactive⟩

theorem Run.resumption_uses {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event} (run : Run program host before trace after)
    (valid : before.ResumptionsAccounted) (id : Identity) :
    after.resumptionUses id = before.resumptionUses id + ReplayCount id trace := by
  induction run with
  | refl => simp [ReplayCount]
  | silent step _ ih =>
      have first := step.resumption_change.uses valid id
      have rest := ih (step.resumptions_accounted valid)
      simpa [first,ReplayEvent] using rest
  | visible step _ ih =>
      have first := step.resumption_change.uses valid id
      have rest := ih (step.resumptions_accounted valid)
      simpa [first,ReplayCount,Nat.add_assoc] using rest

theorem Run.retains_metadata {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event} {id : Identity} {suspension : Suspension}
    (run : Run program host before trace after) (valid : before.ResumptionsAccounted)
    (found : before.resumptions.get id = some suspension) :
    ∃ current, after.resumptions.get id = some current ∧ current.quantity = suspension.quantity ∧
      current.roots = suspension.roots ∧ current.homes = suspension.homes ∧
      current.captureRootLimit = suspension.captureRootLimit ∧
      current.context = suspension.context ∧ current.handler = suspension.handler ∧ current.frames = suspension.frames ∧
      (suspension.active = false → current.active = false) := by
  induction run generalizing suspension with
  | refl => exact ⟨suspension,found,rfl,rfl,rfl,rfl,rfl,rfl,rfl,fun inactive => inactive⟩
  | silent step _ ih | visible step _ ih =>
      obtain ⟨middle,present,quantity,roots,homes,limit,context,handler,frames,settled⟩ := step.resumption_change.retains_metadata valid found
      obtain ⟨current,present,quantity',roots',homes',limit',context',handler',frames',settled'⟩ := ih (step.resumptions_accounted valid) present
      exact ⟨current,present,quantity'.trans quantity,roots'.trans roots,homes'.trans homes,limit'.trans limit,
        context'.trans context,handler'.trans handler,frames'.trans frames,fun inactive => settled' (settled inactive)⟩

theorem Run.retains_resumption {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event} {id : Identity} {suspension : Suspension}
    (run : Run program host before trace after) (valid : before.ResumptionsAccounted)
    (found : before.resumptions.get id = some suspension) :
    ∃ current, after.resumptions.get id = some current ∧ current.quantity = suspension.quantity ∧
      (suspension.active = false → current.active = false) := by
  obtain ⟨current,present,quantity,_,_,_,_,_,_,inactive⟩ := run.retains_metadata valid found
  exact ⟨current,present,quantity,inactive⟩

/-- The saved invocation origin is unchanged; only its quantitative lifecycle
fields may advance. This consumes the existing metadata-preservation producer. -/
theorem Run.retains_origin {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event} {id : Identity} {suspension : Suspension}
    (run : Run program host before trace after) (valid : before.ResumptionsAccounted)
    (found : before.resumptions.get id = some suspension) :
    ∃ current, after.resumptions.get id = some current ∧
      current = { suspension with remaining := current.remaining, used := current.used, active := current.active } := by
  obtain ⟨current,present,quantity,roots,homes,limit,context,handler,frames,_⟩ := run.retains_metadata valid found
  have after := run.resumptions_accounted valid
  have identity := (after.identity id current present).trans (valid.identity id suspension found).symm
  have original := (after.accounted id current present).original.trans (valid.accounted id suspension found).original.symm
  refine ⟨current,present,?_⟩
  cases current
  cases suspension
  simp_all

/-- A bound on every logical suspension, including those created during the
run. Replaying through aliases counts against the same identity. -/
theorem Run.replay_budget {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event} {id : Identity} {suspension : Suspension} {upper : Nat}
    (run : Run program host before trace after) (valid : before.ResumptionsAccounted)
    (found : after.resumptions.get id = some suspension) (bound : suspension.quantity.upper = some upper) :
    before.resumptionUses id + ReplayCount id trace ≤ upper := by
  have counted := run.resumption_uses valid id
  have budget := ((run.resumptions_accounted valid).accounted id suspension found).used_bound bound
  have uses : suspension.used = before.resumptionUses id + ReplayCount id trace := by
    simpa [State.resumptionUses,found] using counted
  exact uses ▸ budget

theorem Run.settled_replay_quantity {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event} {id : Identity} {suspension : Suspension}
    (run : Run program host before trace after) (valid : before.ResumptionsAccounted)
    (found : after.resumptions.get id = some suspension) (settled : suspension.active = false) :
    suspension.quantity.Contains (before.resumptionUses id + ReplayCount id trace) := by
  have counted := run.resumption_uses valid id
  have quantity := ((run.resumptions_accounted valid).accounted id suspension found).settled settled
  have uses : suspension.used = before.resumptionUses id + ReplayCount id trace := by
    simpa [State.resumptionUses,found] using counted
  exact uses ▸ quantity.2

theorem ResumptionChange.replay_active {before after : State} {id : Identity} {last : Bool}
    (change : ResumptionChange before (some (.replay id last)) after) :
    ∃ suspension, before.resumptions.get id = some suspension ∧ suspension.active = true := by
  cases change with
  | unchanged _ _ absent _ _ => exact False.elim (absent id last rfl)
  | last found active _ _ _ | copy found active _ _ _ => exact ⟨_,found,active.1⟩

theorem ResumptionChange.cancel_optional {before after : State} {id : Identity}
    (change : ResumptionChange before (some (.cancel id)) after) :
    ∃ suspension, before.resumptions.get id = some suspension ∧ suspension.quantity.lower = 0 := by
  cases change with
  | unchanged _ _ _ absent _ => exact False.elim (absent id rfl)
  | cancel found _ optional _ _ => exact ⟨_,found,optional⟩

/-- Every actual suspend event creates the very next continuation identity.
The unchanged projection cannot masquerade as a suspension event. -/
theorem ResumptionChange.suspend_created {before after : State} {id : Identity}
    (change : ResumptionChange before (some (.suspend id)) after) :
    id = before.nextContinuation ∧ ∃ suspension,
      after.resumptions.get id = some suspension ∧ suspension.identity = id ∧
      suspension.original = true ∧ suspension.active = true ∧ suspension.used = 0 := by
  cases change with
  | unchanged _ _ _ _ absent => exact False.elim (absent id rfl)
  | create identity original active used _ _ table _ =>
    exact ⟨rfl,_,by rw [table,Table.get_set],identity,original,active,used⟩

theorem ResumptionChange.cancel_started {before after : State} {id : Identity}
    (change : ResumptionChange before (some (.cancel id)) after) :
    ∃ suspension, before.resumptions.get id = some suspension ∧ suspension.active = true ∧
      suspension.quantity.lower = 0 ∧
      after.resumptions.get id = some { suspension with remaining := 0, active := false } := by
  cases change with
  | unchanged _ _ _ absent _ => exact False.elim (absent id rfl)
  | cancel found active optional table _ => exact ⟨_,found,active.1,optional,by rw [table,Table.get_set]⟩

theorem ResumptionChange.spent_no_replay {before after : State} {event : Option Event} {id : Identity} {suspension : Suspension}
    (change : ResumptionChange before event after) (found : before.resumptions.get id = some suspension)
    (spent : suspension.active = false) : ReplayEvent id event = 0 := by
  cases event with
  | none => rfl
  | some event =>
      cases event <;> try rfl
      rename_i target last
      by_cases same : target = id
      · subst target
        obtain ⟨current,present,active⟩ := change.replay_active
        have equal := Option.some.inj (found.symm.trans present)
        subst current
        simp [spent] at active
      · simp [ReplayEvent,same]

theorem ResumptionChange.exact_no_cancel {before after : State} {event : Option Event} {id : Identity} {suspension : Suspension}
    (change : ResumptionChange before event after) (found : before.resumptions.get id = some suspension)
    (positive : 0 < suspension.quantity.lower) : event ≠ some (.cancel id) := by
  intro same
  rw [same] at change
  obtain ⟨current,present,optional⟩ := change.cancel_optional
  have equal := Option.some.inj (found.symm.trans present)
  subst current
  simp [optional] at positive

theorem Run.spent_no_replay {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event} {id : Identity} {suspension : Suspension}
    (run : Run program host before trace after) (valid : before.ResumptionsAccounted)
    (found : before.resumptions.get id = some suspension) (spent : suspension.active = false) : ReplayCount id trace = 0 := by
  induction run generalizing suspension with
  | refl => rfl
  | silent step _ ih =>
      obtain ⟨middle,present,_,inactive⟩ := step.resumption_change.retains valid found
      exact ih (step.resumptions_accounted valid) present (inactive spent)
  | visible step _ ih =>
      have first := step.resumption_change.spent_no_replay found spent
      obtain ⟨middle,present,_,inactive⟩ := step.resumption_change.retains valid found
      have rest := ih (step.resumptions_accounted valid) present (inactive spent)
      simp [ReplayCount,first,rest]

theorem Run.exact_no_cancel {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event} {id : Identity} {suspension : Suspension}
    (run : Run program host before trace after) (valid : before.ResumptionsAccounted)
    (found : before.resumptions.get id = some suspension) (positive : 0 < suspension.quantity.lower) :
    Event.cancel id ∉ trace := by
  induction run generalizing suspension with
  | refl => simp
  | silent step _ ih =>
      obtain ⟨middle,present,quantity,_⟩ := step.resumption_change.retains valid found
      exact ih (step.resumptions_accounted valid) present (by simpa [quantity] using positive)
  | visible step _ ih =>
      have first := step.resumption_change.exact_no_cancel found positive
      obtain ⟨middle,present,quantity,_⟩ := step.resumption_change.retains valid found
      have rest := ih (step.resumptions_accounted valid) present (by simpa [quantity] using positive)
      intro member
      rcases List.mem_cons.mp member with same | inside
      · exact first (congrArg some same.symm)
      · exact rest inside

theorem Run.of_step {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {event : Option Event} (step : Step program host before event after) :
    Run program host before event.toList after := by
  cases event with
  | none => exact .silent step .refl
  | some event => exact .visible step .refl

theorem Run.prefix {program : Kernel.Program} {host : Foreign.Model}
    {states : Nat → State} {events : Nat → Option Event}
    (steps : ∀ n, Step program host (states n) (events n) (states (n+1))) (length : Nat) :
    Run program host (states 0) ((List.range length).filterMap events) (states length) := by
  induction length with
  | zero => exact .refl
  | succ length ih =>
      have combined := ih.append (Run.of_step (steps length))
      cases atEvent : events length <;>
        simpa [List.range_succ,List.filterMap_append,List.filterMap_cons,atEvent] using combined

end Execution

namespace Contracts

open Execution

theorem InvocationStart.resumptions_accounted {program : Kernel.Program} {host : Foreign.Model} {function : Kernel.Function}
    {inputs : List Kernel.InvocationInput} {state : State} {boundary : InvocationBoundary} (initial : InvocationStart program host function inputs boundary state) :
    state.ResumptionsAccounted := initial.2.2.1.suspensions.budgets

/-- The control invariant is constructible for arbitrary fresh invocations;
it does not require an execution-safety certificate or a successful run. -/
theorem InitialInvocation.of_empty_resumptions {program : Kernel.Program} {host : Foreign.Model} {function : Kernel.Function}
    {inputs : List Kernel.InvocationInput} {state : State} {caller : Execution.Context}
    (inputsTyped : InputsTyped program inputs state.world) (functionInputs : FunctionInputs function inputs)
    (registry : host.AuthoritiesRecorded state.world state.hostState)
    (empty : state.resumptions = [])
    (homes : ∀ rootId root id, state.world.roots.get rootId = some root →
      root.home = .suspended id → id < state.nextContinuation)
    (task : state.task = .enter caller function (.supplied inputs) false)
    (callerBounds : ∀ binding ∈ caller.environment, binding.address.root < state.world.nextRoot)
    (callerAuthorities : ∀ binding ∈ caller.environment, binding.authority.Recorded state.world.loans)
    (frames : state.frames = []) (region : caller.region ∈ state.world.liveRegions)
    (activation : caller.activation < state.nextActivation)
    (activationHomes : state.world.ActivationsBelow state.nextActivation)
    (allowed : function.signature.unsafeAllowed = true → caller.unsafeAllowed = true) :
    InitialInvocation program host function inputs state := by
  apply InvocationStart.isolated inputsTyped functionInputs ?_ registry task frames region allowed
  refine ⟨State.SuspensionsWellFormed.empty empty homes,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [task]
    apply RootSupport.below_append.mpr
    constructor
    · intro root member
      obtain ⟨binding,present,rfl⟩ := List.mem_map.mp member
      exact callerBounds binding present
    · rw [EntrySource.rootSupport,RootSupport.below_flatMap]
      intro input member
      obtain ⟨value,stored,_⟩ := inputsTyped.2.2.1 input member
      obtain ⟨root,found,_⟩ := Option.bind_eq_some_iff.mp stored
      exact RootSupport.below_cons.mpr
        ⟨World.root_bound inputsTyped.1.1 (World.root_found found).1,RootSupport.below_nil _⟩
  · simp [frames]
  · intros
    simp_all [Table.get]
  · rw [task]
    apply AuthoritySupport.recorded_append.mpr
    constructor
    · exact AuthoritySupport.recorded_map.mpr callerAuthorities
    · rw [EntrySource.authoritySupport,AuthoritySupport.recorded_map]
      intro input member
      obtain ⟨_,_,_,_,permission⟩ := inputsTyped.2.2.1 input member
      exact permission.recorded
  · simp [frames]
  · intros
    simp_all [Table.get]

  · refine ⟨activationHomes,?_,?_,?_⟩
    · simpa only [task,Task.activationSupport,RootSupport.below_cons,RootSupport.below_nil,and_true] using activation
    · simp [frames]
    · intros
      simp_all [Table.get]

/-- The actual invocation contract supplies the initial control invariant;
all finite-run budget and settlement conclusions are derived by preservation,
independently of `ResourceAdmission` and of host/world typing assumptions. -/
theorem InvocationStart.resumption_safety {program : Kernel.Program} {host : Foreign.Model} {function : Kernel.Function}
    {inputs : List Kernel.InvocationInput} {before after : State} {trace : List Event}
    {boundary : InvocationBoundary} (initial : InvocationStart program host function inputs boundary before) (run : Run program host before trace after) :
    after.ResumptionsAccounted ∧ ∀ id suspension, after.resumptions.get id = some suspension →
      (∀ upper, suspension.quantity.upper = some upper → before.resumptionUses id + ReplayCount id trace ≤ upper) ∧
      (suspension.active = false → suspension.quantity.Contains (before.resumptionUses id + ReplayCount id trace)) := by
  refine ⟨run.resumptions_accounted initial.resumptions_accounted,?_⟩
  intro id suspension found
  exact ⟨fun _ bound => run.replay_budget initial.resumptions_accounted found bound,
    fun inactive => run.settled_replay_quantity initial.resumptions_accounted found inactive⟩

/-- Divergence cannot reset a finite resumption budget: the same invariant
and trace bound hold at every finite prefix of an infinite execution. -/
theorem Diverges.resumption_safety {program : Kernel.Program} {host : Foreign.Model} {function : Kernel.Function}
    {inputs : List Kernel.InvocationInput} {states : Nat → State} {events : Nat → Option Event}
    (diverges : Diverges program host function inputs states events) (length : Nat) :
    (states length).ResumptionsAccounted ∧ ∀ id suspension, (states length).resumptions.get id = some suspension →
      ∀ upper, suspension.quantity.upper = some upper →
        (states 0).resumptionUses id + ReplayCount id ((List.range length).filterMap events) ≤ upper := by
  obtain ⟨boundary,initial,steps⟩ := diverges
  have safe := initial.resumption_safety (InvocationRun.prefix steps length).execution
  exact ⟨safe.1,fun id suspension found => (safe.2 id suspension found).1⟩

end Contracts
end Glorious.Language
