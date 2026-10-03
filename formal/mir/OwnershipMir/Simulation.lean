import OwnershipMir.Execution

namespace OwnershipMir.PositiveSimulation

variable {σ τ : Type} {source : σ → σ → Prop} {target : τ → τ → Prop}
  {f : σ → τ} {P S : σ → Prop} {T : τ → Prop}

/-- Each source step performs at least one target step, followed by a finite run. -/
theorem run
    (forward : ∀ {s s'}, source s s' → ∃ middle, target (f s) middle ∧ Run target middle (f s'))
    {s s' : σ} (execution : Run source s s') : Run target (f s) (f s') := by
  induction execution with
  | refl => exact .refl _
  | step head _ ih =>
    obtain ⟨middle, first, rest⟩ := forward head
    exact .step first (rest.trans ih)

private theorem accessible_of_terminal_run
    (deterministic : ∀ {s x y}, target s x → target s y → x = y)
    {before after : τ} (execution : Run target before after)
    (stopped : ∀ state, ¬ target after state) :
    Acc (fun child parent => target parent child) before := by
  induction execution with
  | refl => exact Acc.intro _ (fun state step => False.elim (stopped state step))
  | step head _ ih =>
    exact Acc.intro _ (fun _ step => deterministic head step ▸ ih stopped)

/-- Positivity is essential: a source transition strictly descends target
accessibility even when its implementation contains multiple target steps. -/
private theorem accessible_pullback
    (forward : ∀ {s s'}, source s s' → ∃ middle, target (f s) middle ∧ Run target middle (f s'))
    {t : τ} (accessible : Acc (fun child parent => target parent child) t) :
    ∀ s, Run target t (f s) → Acc (fun child parent => source parent child) s := by
  induction accessible with
  | intro t _ ih =>
    intro s path
    cases path with
    | refl =>
      refine Acc.intro s ?_
      intro s' step
      obtain ⟨middle, first, rest⟩ := forward step
      exact ih middle first s' rest
    | step head tail => exact ih _ head s tail

private theorem terminal_of_accessible
    (preserves : ∀ {s s'}, P s → source s s' → P s')
    (progress : ∀ s, P s → S s ∨ ∃ s', source s s')
    {s : σ} (accessible : Acc (fun child parent => source parent child) s)
    (valid : P s) : ∃ s', Run source s s' ∧ S s' := by
  induction accessible with
  | intro s _ ih =>
    obtain terminal | ⟨s', step⟩ := progress s valid
    · exact ⟨s, .refl _, terminal⟩
    · obtain ⟨last, rest, terminal⟩ := ih s' step (preserves valid step)
      exact ⟨last, .step step rest, terminal⟩

/-- A finite target execution to a terminal state reflects to a source terminal
execution with exactly the same mapped endpoint. No reverse simulation or
assumption that target execution eventually reaches a source boundary is used. -/
theorem terminal_reflection
    (preserves : ∀ {s s'}, P s → source s s' → P s')
    (progress : ∀ s, P s → S s ∨ ∃ s', source s s')
    (forward : ∀ {s s'}, source s s' → ∃ middle, target (f s) middle ∧ Run target middle (f s'))
    (deterministic : ∀ {s x y}, target s x → target s y → x = y)
    (terminal : ∀ s, S s ↔ T (f s))
    (stopped : ∀ {t}, T t → ∀ after, ¬ target t after)
    {s : σ} {t : τ} (valid : P s) (execution : Run target (f s) t) (done : T t) :
    ∃ s', Run source s s' ∧ S s' ∧ f s' = t := by
  have accessible := accessible_of_terminal_run (target := target) deterministic execution (stopped done)
  have sourceAccessible := accessible_pullback (source := source) (target := target) forward accessible s (.refl _)
  obtain ⟨s', sourceRun, sourceDone⟩ := terminal_of_accessible (source := source) preserves progress sourceAccessible valid
  refine ⟨s', sourceRun, sourceDone, ?_⟩
  exact (run (source := source) (target := target) forward sourceRun).terminal_unique execution deterministic
    (stopped ((terminal s').mp sourceDone)) (stopped done)

private theorem invariant_run
    (preserves : ∀ {s s'}, P s → source s s' → P s')
    {s s' : σ} (execution : Run source s s') (valid : P s) : P s' := by
  induction execution with
  | refl => exact valid
  | step head _ ih => exact ih (preserves valid head)

/-- Divergence means an actual infinite trace on both sides. Target progress is
required at every target-reachable state, including intermediate states of a
multi-step implementation; source-boundary progress alone does not suffice. -/
theorem diverges_iff
    (preserves : ∀ {s s'}, P s → source s s' → P s')
    (progress : ∀ s, P s → S s ∨ ∃ s', source s s')
    (forward : ∀ {s s'}, source s s' → ∃ middle, target (f s) middle ∧ Run target middle (f s'))
    (deterministic : ∀ {s x y}, target s x → target s y → x = y)
    (sourceDeterministic : ∀ {s x y}, source s x → source s y → x = y)
    (terminal : ∀ s, S s ↔ T (f s))
    (stopped : ∀ {t}, T t → ∀ after, ¬ target t after)
    {s : σ} (valid : P s)
    (targetProgress : ∀ t, Run target (f s) t → T t ∨ ∃ t', target t t') :
    Diverges source s ↔ Diverges target (f s) := by
  constructor
  · intro infinite
    apply diverges_of_progress
    intro t reachable
    obtain done | advances := targetProgress t reachable
    · obtain ⟨s', sourceRun, sourceDone, _⟩ :=
        terminal_reflection (source := source) (target := target) preserves progress forward deterministic terminal stopped valid reachable done
      have sourceStopped : ∀ after, ¬ source s' after := by
        intro after step
        obtain ⟨middle, first, _⟩ := forward step
        exact stopped ((terminal s').mp sourceDone) middle first
      exact False.elim (sourceRun.excludes_divergence sourceDeterministic sourceStopped infinite)
    · exact advances
  · intro infinite
    apply diverges_of_progress
    intro s' reachable
    obtain done | advances := progress s' (invariant_run (source := source) preserves reachable valid)
    · exact False.elim ((run (source := source) (target := target) forward reachable).excludes_divergence deterministic
        (stopped ((terminal s').mp done)) infinite)
    · exact advances

end OwnershipMir.PositiveSimulation
