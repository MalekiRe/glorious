module

public import Glorious.Typing.Safety

/-!
# A cell lives as long as its scope

Two things together show that a program checked with the region rules never
reads or writes a released cell.

The first is about the machine alone, whatever the program: every cell whose
scope is on the stack, or among the frames a resumption captured, is live, and
no two scopes are for the same cell. A scope is pushed with a fresh cell, a
cell is released only when its scope is removed, and frames move between the
stack and the store without being copied.

The second is about typing: the regions a typed stack grants the code on top of
it are cells whose scopes are on that stack. Code reads and writes only through
references whose region it was granted.
-/

@[expose] public section

namespace Glorious.Typing

open Core

variable {Δ : Ctx}

/-! ## Scopes own their cells -/

/-- Whether a frame is the scope of cell `a`: one if so. -/
def ownFrame (a : Nat) : Frame → Nat
  | .cell b => if b = a then 1 else 0
  | .lend _ _ _ => 0
  | .call _ _ => 0
  | .handler _ _ => 0
  | .label _ => 0
  | .guard _ _ => 0
  | .yield _ => 0
  | .exit _ _ => 0

/-- How many frames of a stack are the scope of cell `a`. -/
def ownStack (a : Nat) : List Frame → Nat
  | [] => 0
  | fr :: st => ownFrame a fr + ownStack a st

theorem ownStack_append (a : Nat) : ∀ (x y : List Frame),
    ownStack a (x ++ y) = ownStack a x + ownStack a y
  | [], y => by simp [ownStack]
  | fr :: x, y => by simp [ownStack, ownStack_append a x y, Nat.add_assoc]

/-- A cell holds a value: it has not been released. -/
def Live (cells : Cells) (a : Nat) : Prop := ∃ v, cells[a]? = some (some v)

/-- Every cell with a scope on the stack `st`, or among the frames of a
resumption in the store, is live, and has only that one scope. -/
def OwnsAt (st : List Frame) (store : Store Frame) : Prop :=
  ∀ a, ownStack a st + osum (ownStack a) store.conts ≤ 1
    ∧ (0 < ownStack a st + osum (ownStack a) store.conts → Live store.cells a)

def Owns (s : State) : Prop := OwnsAt s.stack s.store

/-- A stack and store with the same scopes and at least the same live cells. -/
theorem OwnsAt.of_le {st st' : List Frame} {store store' : Store Frame} (h : OwnsAt st store)
    (hc : ∀ a, ownStack a st' + osum (ownStack a) store'.conts
      ≤ ownStack a st + osum (ownStack a) store.conts)
    (hl : ∀ a, Live store.cells a → Live store'.cells a) : OwnsAt st' store' := by
  intro a
  obtain ⟨h1, h2⟩ := h a
  have := hc a
  exact ⟨by omega, fun hp => hl a (h2 (by omega))⟩

/-- Removing a frame without releasing anything. -/
theorem OwnsAt.drop {fr : Frame} {st : List Frame} {store : Store Frame}
    (h : OwnsAt (fr :: st) store) : OwnsAt st store :=
  h.of_le (fun a => by simp only [ownStack]; omega) (fun _ hl => hl)

/-- Pushing a frame that is not a cell's scope. -/
theorem OwnsAt.push {fr : Frame} {st : List Frame} {store : Store Frame} (h : OwnsAt st store)
    (h0 : ∀ a, ownFrame a fr = 0) : OwnsAt (fr :: st) store :=
  h.of_le (fun a => by simp only [ownStack, h0 a]; omega) (fun _ hl => hl)

/-- The label counter is no part of it. -/
theorem OwnsAt.labels {st : List Frame} {conts : Conts Frame} {labels labels' : Nat}
    {cells : Cells} (h : OwnsAt st ⟨conts, labels, cells⟩) : OwnsAt st ⟨conts, labels', cells⟩ :=
  h

/-- Removing the scope of a cell and releasing the cell. -/
theorem OwnsAt.release {a : Nat} {st : List Frame} {store : Store Frame}
    (h : OwnsAt (.cell a :: st) store) : OwnsAt st (store.release a) := by
  intro b
  obtain ⟨h1, h2⟩ := h b
  simp only [ownStack, ownFrame] at h1 h2
  refine ⟨by show ownStack b st + osum (ownStack b) store.conts ≤ 1; omega, fun hp => ?_⟩
  have hp' : 0 < ownStack b st + osum (ownStack b) store.conts := hp
  have hne : a ≠ b := by
    intro e
    subst e
    simp at h1
    omega
  obtain ⟨v, hv⟩ := h2 (by omega)
  refine ⟨v, ?_⟩
  show (store.cells.setIfInBounds a none)[b]? = some (some v)
  rw [Array.getElem?_setIfInBounds_ne hne]
  exact hv

/-- Pushing the scope of a new cell. -/
theorem OwnsAt.alloc {st : List Frame} {store : Store Frame} (h : OwnsAt st store) (v : Value) :
    OwnsAt (.cell store.cells.size :: st) (store.alloc v) := by
  intro b
  obtain ⟨h1, h2⟩ := h b
  by_cases hb : store.cells.size = b
  · subst hb
    have hz : ownStack store.cells.size st + osum (ownStack store.cells.size) store.conts
        = 0 := by
      cases hn : ownStack store.cells.size st + osum (ownStack store.cells.size) store.conts
        with
      | zero => rfl
      | succ k =>
        obtain ⟨w, hw⟩ := h2 (by omega)
        have := (Array.getElem?_eq_some_iff.mp hw).1
        omega
    refine ⟨?_, fun _ => ⟨v, ?_⟩⟩
    · show ownFrame _ (Frame.cell store.cells.size) + ownStack _ st
        + osum (ownStack _) store.conts ≤ 1
      simp only [ownFrame, ↓reduceIte]
      omega
    · show (store.cells.push (some v))[store.cells.size]? = some (some v)
      simp
  · refine ⟨?_, fun hp => ?_⟩
    · show ownFrame b (Frame.cell store.cells.size) + ownStack b st
        + osum (ownStack b) store.conts ≤ 1
      simp only [ownFrame, hb, ↓reduceIte]
      omega
    · have hp' : 0 < ownFrame b (Frame.cell store.cells.size) + ownStack b st
          + osum (ownStack b) store.conts := hp
      simp only [ownFrame, hb, ↓reduceIte] at hp'
      obtain ⟨w, hw⟩ := h2 (by omega)
      refine ⟨w, ?_⟩
      show (store.cells.push (some v))[b]? = some (some w)
      have hlt := (Array.getElem?_eq_some_iff.mp hw).1
      rw [Array.getElem?_push_lt hlt]
      rw [Array.getElem?_eq_getElem hlt] at hw
      exact hw

theorem callFn_next {p : Program} {fn : Nat} {captures vs : List Value} {st : List Frame}
    {store : Store Frame} {s' : State} (h : callFn p fn captures vs st store = .next s') :
    s'.stack = st ∧ s'.store = store := by
  simp only [callFn] at h
  split at h
  · cases h
    exact ⟨rfl, rfl⟩
  · cases h

/-- Delivering a value and leaving for a target keep every scope's cell live.
Proved together, as the two are defined together. -/
theorem deliver_leave_owns (p : Program) : ∀ (st : List Frame) {store : Store Frame},
    OwnsAt st store →
    (∀ {v : Value} {s' : State}, deliver p v st store = .next s' → Owns s')
    ∧ (∀ {target : Target} {after : After} {s' : State},
        leave p target after st store = .next s' → Owns s') := by
  intro st
  induction st with
  | nil =>
    intro store _
    refine ⟨fun h => ?_, fun h => ?_⟩
    · simp [deliver] at h
    · simp [leave] at h
  | cons fr st ih =>
    intro store ho
    refine ⟨@fun v s' h => ?_, @fun target after s' h => ?_⟩
    · cases fr with
      | call env body =>
        simp only [deliver, Step.next.injEq] at h
        subst h
        exact ho.drop
      | handler id hd =>
        simp only [deliver] at h
        obtain ⟨h1, h2⟩ := callFn_next h
        show OwnsAt s'.stack s'.store
        rw [h1, h2]
        exact ho.drop
      | label id =>
        simp only [deliver] at h
        exact (ih ho.drop).1 h
      | guard fn captures =>
        simp only [deliver] at h
        obtain ⟨h1, h2⟩ := callFn_next h
        show OwnsAt s'.stack s'.store
        rw [h1, h2]
        exact ho.drop.push (fun _ => rfl)
      | cell a =>
        simp only [deliver] at h
        exact (ih ho.release).1 h
      | lend uniq a b =>
        simp only [deliver] at h
        exact (ih ho.drop).1 h
      | yield w =>
        simp only [deliver] at h
        exact (ih ho.drop).1 h
      | exit t af =>
        simp only [deliver] at h
        exact (ih ho.drop).2 h
    · by_cases ht : fr.isTarget target = true
      · cases after with
        | yield w =>
          simp only [leave, ht, ↓reduceIte] at h
          exact (ih ho.drop).1 h
        | invoke fn captures args =>
          simp only [leave, ht, ↓reduceIte] at h
          obtain ⟨h1, h2⟩ := callFn_next h
          show OwnsAt s'.stack s'.store
          rw [h1, h2]
          exact ho.drop
      · cases fr with
        | guard fn captures =>
          simp only [leave, ht] at h
          obtain ⟨h1, h2⟩ := callFn_next h
          show OwnsAt s'.stack s'.store
          rw [h1, h2]
          exact ho.drop.push (fun _ => rfl)
        | cell a =>
          simp only [leave, ht] at h
          exact (ih ho.release).2 h
        | lend uniq a b =>
          simp only [leave, ht] at h
          exact (ih ho.drop).2 h
        | call env body =>
          simp only [leave, ht] at h
          exact (ih ho.drop).2 h
        | handler id hd =>
          simp only [leave, ht] at h
          exact (ih ho.drop).2 h
        | label id =>
          simp only [leave, ht] at h
          exact (ih ho.drop).2 h
        | yield w =>
          simp only [leave, ht] at h
          exact (ih ho.drop).2 h
        | exit t af =>
          simp only [leave, ht] at h
          exact (ih ho.drop).2 h

theorem takeCont_spec {α : Type} : ∀ {cs : List (Option α)} {id : Nat} {x : α}
    {cs' : List (Option α)}, takeCont cs id = some (x, cs') →
    cs[id]? = some (some x) ∧ cs' = cs.set id none
  | [], _, _, _, h => by simp [takeCont] at h
  | c :: cs, 0, x, cs', h => by
    cases c with
    | none => simp [takeCont] at h
    | some y =>
      simp [takeCont] at h
      obtain ⟨rfl, rfl⟩ := h
      simp
  | c :: cs, id + 1, x, cs', h => by
    simp only [takeCont] at h
    split at h
    · rename_i y cs'' hr
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨h1, h2⟩ := takeCont_spec hr
      simp [h1, h2]
    · cases h

/-- Putting a resumption's frames back on the stack. -/
theorem OwnsAt.resume {st seg : List Frame} {conts : Conts Frame} {labels : Nat}
    {cells : Cells} {id : Nat} (h : OwnsAt st ⟨conts, labels, cells⟩)
    (hk : conts[id]? = some (some seg)) :
    OwnsAt (seg ++ st) ⟨conts.set id none, labels, cells⟩ :=
  h.of_le (fun a => by
    have := osum_set (ownStack a) conts id none (some seg) hk
    simp only [oweight] at this
    show ownStack a (seg ++ st) + osum (ownStack a) (conts.set id none)
      ≤ ownStack a st + osum (ownStack a) conts
    rw [ownStack_append]
    omega) (fun _ hl => hl)

theorem apply_owns {p : Program} {c : Callee} {st : List Frame} {store : Store Frame}
    {s' : State} (ho : OwnsAt st store) (h : apply p c st store = .next s') : Owns s' := by
  cases c with
  | fn fn captures vs =>
    obtain ⟨h1, h2⟩ := callFn_next h
    show OwnsAt s'.stack s'.store
    rw [h1, h2]
    exact ho
  | cont id v =>
    obtain ⟨conts, labels, cells⟩ := store
    simp only [apply] at h
    split at h
    · rename_i seg conts' hr
      obtain ⟨hk, rfl⟩ := takeCont_spec hr
      exact (deliver_leave_owns p _ (ho.resume hk)).1 h
    · cases h
  | label id v =>
    simp only [apply] at h
    split at h
    · exact (deliver_leave_owns p _ ho).2 h
    · cases h

theorem live_set {cells : Cells} {a b : Nat} {x : Value} (h : Live cells a) :
    Live (cells.setIfInBounds b (some x)) a := by
  obtain ⟨w, hw⟩ := h
  by_cases hb : b = a
  · subst hb
    exact ⟨x, by rw [Array.getElem?_setIfInBounds_self_of_lt (Array.getElem?_eq_some_iff.mp hw).1]⟩
  · exact ⟨w, by rw [Array.getElem?_setIfInBounds_ne hb]; exact hw⟩

/-- A memory operation leaves the cells as they are or sets one of them. -/
theorem mem_cells {op : MemOp} {cells cells' : Cells} {vs : List Value} {r : Value}
    (h : op.eval cells vs = some (r, cells')) :
    cells' = cells ∨ ∃ a x, cells' = cells.setIfInBounds a (some x) := by
  unfold MemOp.eval at h
  split at h
  · split at h
    · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨_, _, _, rfl⟩ := h
      exact .inl rfl
    · cases h
  · split at h
    · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨_, _, _, rfl⟩ := h
      exact .inr ⟨_, _, rfl⟩
    · cases h
  · split at h
    · split at h
      · cases h
        exact .inr ⟨_, _, rfl⟩
      · cases h
    · cases h
  · split at h
    · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨_, _, _, rfl⟩ := h
      exact .inl rfl
    · cases h
  · split at h
    · cases h
      exact .inl rfl
    · cases h
  · split at h
    · cases h
      exact .inl rfl
    · cases h
  · cases h

/-- A memory operation releases nothing. -/
theorem mem_live {op : MemOp} {cells cells' : Cells} {vs : List Value} {r : Value}
    (h : op.eval cells vs = some (r, cells')) : ∀ a, Live cells a → Live cells' a := by
  intro a hl
  rcases mem_cells h with rfl | ⟨_, _, rfl⟩
  · exact hl
  · exact live_set hl

/-- **Every step of the machine keeps every scope's cell live.** Nothing here
depends on the program being typed. -/
theorem step_owns {p : Program} {s s' : State} (ho : Owns s) (h : step p s = .next s') :
    Owns s' := by
  obtain ⟨tm, env, stack, store⟩ := s
  obtain ⟨conts, labels, cells⟩ := store
  have ho' : OwnsAt stack ⟨conts, labels, cells⟩ := ho
  cases tm with
  | ret a =>
    simp only [step] at h
    split at h
    · cases h
    · exact (deliver_leave_owns p _ ho').1 h
  | let_ rhs body =>
    simp only [step] at h
    split at h
    · cases h
    · cases h
      exact ho'
  | call f args body =>
    simp only [step] at h
    split at h
    · cases h
    · exact apply_owns (ho'.push (fun _ => rfl)) h
  | tail f args =>
    simp only [step] at h
    split at h
    · cases h
    · exact apply_owns ho' h
  | handle ret ops captures thunk body =>
    simp only [step] at h
    split at h
    · exact apply_owns (((ho'.push (fr := .call env body) (fun _ => rfl)).push
        (fun _ => rfl)).labels) h
    · cases h
  | handleTail ret ops captures thunk =>
    simp only [step] at h
    split at h
    · exact apply_owns ((ho'.push (fun _ => rfl)).labels) h
    · cases h
  | raise op args =>
    simp only [step] at h
    split at h
    · cases h
    · split at h
      · cases h
      · exact (deliver_leave_owns p _ ho').2 h
  | perform op args body =>
    simp only [step] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i vs _ d hfind
        obtain ⟨h1, h2⟩ := callFn_next h
        show OwnsAt s'.stack s'.store
        rw [h1, h2]
        refine ho'.of_le (fun a => ?_) (fun _ hl => hl)
        have hsplit := congrArg (ownStack a) (findHandler_split hfind)
        simp only [ownStack_append, ownStack, ownFrame] at hsplit
        show ownStack a d.below + osum (ownStack a)
            (conts ++ [some (.call env body :: d.above ++ [.handler d.id d.handler])])
          ≤ ownStack a stack + osum (ownStack a) conts
        simp only [osum_append, osum, ownStack, ownFrame, ownStack_append]
        omega
  | label thunk body =>
    simp only [step] at h
    split at h
    · cases h
    · exact apply_owns (((ho'.push (fr := .call env body) (fun _ => rfl)).push
        (fun _ => rfl)).labels) h
  | labelTail thunk =>
    simp only [step] at h
    split at h
    · cases h
    · exact apply_owns ((ho'.push (fun _ => rfl)).labels) h
  | guard cleanup thunk body =>
    simp only [step] at h
    split at h
    · exact apply_owns ((ho'.push (fr := .call env body) (fun _ => rfl)).push (fun _ => rfl)) h
    · cases h
  | guardTail cleanup thunk =>
    simp only [step] at h
    split at h
    · exact apply_owns (ho'.push (fun _ => rfl)) h
    · cases h
  | cancel k body =>
    simp only [step] at h
    split at h
    · exact apply_owns (c := .fn _ [] _) (ho'.push (fr := .call env body) (fun _ => rfl)) h
    split at h
    · cases h
    · cases h
      exact ho'
    · split at h
      · rename_i seg conts' hr
        obtain ⟨hk, rfl⟩ := takeCont_spec hr
        refine (deliver_leave_owns p _ ?_).2 h
        have hbase : OwnsAt (.yield Value.unit :: .label labels :: .call env body :: stack)
            ⟨conts, labels, cells⟩ :=
          ((ho'.push (fr := .call env body) (fun _ => rfl)).push (fun _ => rfl)).push
            (fun _ => rfl)
        exact (hbase.resume hk).labels
      · cases h
  | cell init thunk body =>
    simp only [step] at h
    split at h
    · exact apply_owns (st := .cell cells.size :: .call env body :: stack)
        (OwnsAt.alloc (st := .call env body :: stack) (store := ⟨conts, labels, cells⟩)
          (ho'.push (fun _ => rfl)) _) h
    · cases h
  | cellTail init thunk =>
    simp only [step] at h
    split at h
    · exact apply_owns (st := .cell cells.size :: stack)
        (OwnsAt.alloc (store := ⟨conts, labels, cells⟩) ho' _) h
    · cases h
  | lend uniq r thunk pre post body =>
    simp only [step] at h
    split at h
    · cases h
    · exact apply_owns (((ho'.push (fr := .call env body) (fun _ => rfl)).push
        (fun _ => rfl)).labels) h
  | mem op args body =>
    simp only [step] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i vs _ r cells' hev
        cases h
        exact ho'.of_le (fun _ => Nat.le_refl _) (mem_live hev)
  | host id args body => simp [step] at h

/-- A host operation touches neither the stack nor the store. -/
theorem stepIO_owns {p : Program} {c c' : Config} (ho : Owns c.state)
    (h : stepIO p c = .next c') : Owns c'.state := by
  obtain ⟨⟨tm, env, stack, store⟩, w⟩ := c
  by_cases hh : ∃ id args body, tm = .host id args body
  · obtain ⟨id, args, body, rfl⟩ := hh
    simp only [stepIO] at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases h
        exact ho
  · have hnh : ∀ id args body, tm ≠ .host id args body :=
      fun id args body e => hh ⟨id, args, body, e⟩
    rw [stepIO_eq_lift hnh] at h
    cases hr : step p ⟨tm, env, stack, store⟩ with
    | next s' =>
      rw [hr] at h
      cases h
      exact step_owns ho hr
    | halt v => rw [hr] at h; cases h
    | stuck => rw [hr] at h; cases h

theorem owns_init (p : Program) : Owns (init p) := fun a => by
  simp [init, ownStack, osum, Live]

/-- Every scope's cell is live in every state a program reaches. -/
theorem run_owns {p : Program} : ∀ (n : Nat) {c c' : Config}, Owns c.state →
    Machine.run (stepIO p) n c = .next c' → Owns c'.state := by
  intro n
  induction n with
  | zero =>
    intro c c' ho h
    cases h
    exact ho
  | succ n ih =>
    intro c c' ho h
    rw [Machine.run_succ] at h
    cases hr : stepIO p c with
    | next c₁ =>
      rw [hr, Step.bind_next] at h
      exact ih (stepIO_owns ho hr) h
    | halt r => rw [hr, Step.bind_halt] at h; cases h
    | stuck => rw [hr] at h; cases h

/-! ## What a typed stack grants -/

theorem ownStack_cons_pos {a : Nat} {st : List Frame} (fr : Frame) (h : 0 < ownStack a st) :
    0 < ownStack a (fr :: st) := by
  simp only [ownStack]
  omega

/-- What the scope of a borrow grants. -/
theorem mem_lent {uniq : Bool} {ρ : Rgn} {b : Nat} {ϕ : List Rgn} {x : Rgn} :
    x ∈ lent uniq ρ b ϕ ↔ x = .loan b ∨ (uniq = true ∧ x = .wr (.loan b))
      ∨ (x ∈ Rgn.flat ϕ ∧ x ∉ (Rgn.wr ρ).parts ∧ (uniq = true → x ∉ ρ.parts) ∧ x ≠ .loan b
        ∧ x ≠ .wr (.loan b)) := by
  cases uniq <;> simp [lent, and_assoc]

/-- A cell is of a region through one of the region's places. -/
theorem OnCell.part {S : StoreTy} {r : Rgn} {a : Nat} (h : OnCell S r a) :
    ∃ y, y ∈ r.parts ∧ OnCell S y a := by
  obtain ⟨y, hy, hc⟩ := h
  exact ⟨y, hy, y, Rgn.self_mem_parts (Rgn.mem_parts_atom hy), hc⟩

theorem OnCell.not_lab {S : StoreTy} {id a : Nat} : ¬ OnCell S (.lab id) a := by
  rintro ⟨y, hy, hc⟩
  simp only [Rgn.parts, List.mem_singleton] at hy
  subst hy
  rcases hc with hc | ⟨_, hc, _⟩ <;> cases hc

theorem OnCell.not_wr {S : StoreTy} {r : Rgn} {a : Nat} : ¬ OnCell S (.wr r) a := by
  rintro ⟨y, hy, hc⟩
  simp only [Rgn.parts, List.mem_map] at hy
  obtain ⟨z, _, rfl⟩ := hy
  rcases hc with hc | ⟨_, hc, _⟩ <;> cases hc

theorem OnCell.loan_eq {S : StoreTy} {a a' b : Nat} (h : OnCell S (.loan b) a)
    (hl : S.loans b = some a') : a = a' := by
  obtain ⟨y, hy, hc⟩ := h
  simp only [Rgn.parts, List.mem_singleton] at hy
  subst hy
  rcases hc with h | ⟨b', h, hl'⟩
  · cases h
  · cases h
    rw [hl] at hl'
    exact (Option.some.inj hl').symm

theorem OnCell.cell_eq {S : StoreTy} {a a' : Nat} (h : OnCell S (.cell a') a) : a = a' := by
  obtain ⟨y, hy, hc⟩ := h
  simp only [Rgn.parts, List.mem_singleton] at hy
  subst hy
  rcases hc with h | ⟨b', h, _⟩
  · cases h
    rfl
  · cases h

/-- A place a typed stack grants, to read or to write, that is of a cell has
that cell's scope on the stack: the cell's own region is granted by the scope,
and a borrow's by the scope of the borrow, which was made where the region
borrowed from was granted. -/
theorem StackOk.onCell {S : StoreTy} {st : List Frame} {τ : Ty} {ε : Row} {ϕ : List Rgn}
    (hR : Δ.regions) (h : StackOk Δ S st τ ε ϕ) :
    ∀ x a, (x ∈ Rgn.flat ϕ ∨ .wr x ∈ Rgn.flat ϕ) → OnCell S x a → 0 < ownStack a st := by
  induction h with
  | nil => intro x a hx; rcases hx with hx | hx <;> cases hx
  | call _ _ _ _ _ ih => exact fun x a hx hc => ownStack_cons_pos _ (ih x a hx hc)
  | handler _ _ _ hsub _ ih =>
    exact fun x a hx hc => ownStack_cons_pos _ (ih x a (hx.imp (hsub _) (hsub _)) hc)
  | @label id st τ ε ϕ _ _ ih =>
    intro x a hx hc
    rw [Rgn.flat_cons_atom rfl] at hx
    rcases hx with hx | hx
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact absurd hc OnCell.not_lab
      · exact ownStack_cons_pos _ (ih x a (.inl hx) hc)
    · rcases List.mem_cons.mp hx with hx | hx
      · cases hx
      · exact ownStack_cons_pos _ (ih x a (.inr hx) hc)
  | guard _ _ _ ih => exact fun x a hx hc => ownStack_cons_pos _ (ih x a hx hc)
  | @cell b st σ τ ε ϕ _ _ ih =>
    intro x a hx hc
    have hself : x = .cell b → 0 < ownStack a (.cell b :: st) := by
      rintro rfl
      cases hc.cell_eq
      simp only [ownStack, ownFrame, ↓reduceIte]
      omega
    rw [Rgn.flat_cons_atom rfl, Rgn.flat_cons_atom rfl] at hx
    rcases hx with hx | hx
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hself rfl
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact absurd hc OnCell.not_wr
        · exact ownStack_cons_pos _ (ih x a (.inl hx) hc)
    · rcases List.mem_cons.mp hx with hx | hx
      · cases hx
      · rcases List.mem_cons.mp hx with hx | hx
        · exact hself (Rgn.wr.inj hx)
        · exact ownStack_cons_pos _ (ih x a (.inr hx) hc)
  | @lend uniq a' b st τ ε ϕ ρ hl _ hon hρ _ _ ih =>
    intro x a hx hc
    have hself : x = .loan b → 0 < ownStack a (.lend uniq a' b :: st) := by
      rintro rfl
      cases hc.loan_eq hl
      obtain ⟨y, hy, hyc⟩ := hon.part
      exact ownStack_cons_pos _ (ih y a' (.inl (hρ y hy)) hyc)
    rw [flat_lent] at hx
    rcases hx with hx | hx
    · rcases mem_lent.mp hx with rfl | ⟨_, rfl⟩ | ⟨hx, _⟩
      · exact hself rfl
      · exact absurd hc OnCell.not_wr
      · exact ownStack_cons_pos _ (ih x a (.inl hx) hc)
    · rcases mem_lent.mp hx with hx | ⟨_, hx⟩ | ⟨hx, _⟩
      · cases hx
      · exact hself (Rgn.wr.inj hx)
      · exact ownStack_cons_pos _ (ih x a (.inr hx) hc)
  | @lendLoose uniq a' b st τ ε ϕ _ hl hon _ ih =>
    intro x a hx hc
    have hself : x = .loan b → 0 < ownStack a (.lend uniq a' b :: st) := by
      rintro rfl
      cases hc.loan_eq hl
      obtain ⟨ρ, hon', hρ⟩ := hon hR
      obtain ⟨y, hy, hyc⟩ := hon'.part
      exact ownStack_cons_pos _ (ih y a' (.inl (hρ y hy)) hyc)
    rw [Rgn.flat_cons_atom rfl, Rgn.flat_cons_atom rfl] at hx
    rcases hx with hx | hx
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hself rfl
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact absurd hc OnCell.not_wr
        · exact ownStack_cons_pos _ (ih x a (.inl hx) hc)
    · rcases List.mem_cons.mp hx with hx | hx
      · cases hx
      · rcases List.mem_cons.mp hx with hx | hx
        · exact hself (Rgn.wr.inj hx)
        · exact ownStack_cons_pos _ (ih x a (.inr hx) hc)
  | yield _ _ ih => exact fun x a hx hc => ownStack_cons_pos _ (ih x a hx hc)
  | exit _ _ _ ih => exact fun x a hx hc => ownStack_cons_pos _ (ih x a hx hc)
  | never _ ih => exact ih

/-- A label's region is granted only by a stack its scope is on. -/
theorem StackOk.labelled {S : StoreTy} {st : List Frame} {τ : Ty} {ε : Row} {ϕ : List Rgn}
    (h : StackOk Δ S st τ ε ϕ) : ∀ id, .lab id ∈ Rgn.flat ϕ → Frame.label id ∈ st := by
  induction h with
  | nil => intro id hr; cases hr
  | call _ _ _ _ _ ih => exact fun id hr => List.mem_cons_of_mem _ (ih id hr)
  | handler _ _ _ hsub _ ih => exact fun id hr => List.mem_cons_of_mem _ (ih id (hsub _ hr))
  | label _ _ ih =>
    intro id hr
    rw [Rgn.flat_cons_atom rfl] at hr
    rcases List.mem_cons.mp hr with h | hr
    · cases h
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih id hr)
  | guard _ _ _ ih => exact fun id hr => List.mem_cons_of_mem _ (ih id hr)
  | cell _ _ ih =>
    intro id hr
    rw [Rgn.flat_cons_atom rfl, Rgn.flat_cons_atom rfl] at hr
    rcases List.mem_cons.mp hr with h | hr
    · cases h
    · rcases List.mem_cons.mp hr with h | hr
      · cases h
      · exact List.mem_cons_of_mem _ (ih id hr)
  | lend _ _ _ _ _ _ ih =>
    intro id hr
    rw [flat_lent] at hr
    rcases mem_lent.mp hr with h | ⟨_, h⟩ | ⟨hr, _⟩
    · cases h
    · cases h
    · exact List.mem_cons_of_mem _ (ih id hr)
  | lendLoose _ _ _ _ ih =>
    intro id hr
    rw [Rgn.flat_cons_atom rfl, Rgn.flat_cons_atom rfl] at hr
    rcases List.mem_cons.mp hr with h | hr
    · cases h
    · rcases List.mem_cons.mp hr with h | hr
      · cases h
      · exact List.mem_cons_of_mem _ (ih id hr)
  | yield _ _ ih => exact fun id hr => List.mem_cons_of_mem _ (ih id hr)
  | exit _ _ _ ih => exact fun id hr => List.mem_cons_of_mem _ (ih id hr)
  | never _ ih => exact ih

/-- A released cell is about to be read or written. -/
def Freed (s : State) : Prop :=
  ∃ op args body a b path vs, s.tm = .mem op args body
    ∧ evalAtoms s.env args = some (.ref a b path :: vs) ∧ s.store.cells[a]? = some none

/-- Under the region rules, a typed state in which every scope's cell is live
is not about to read or write a released cell: the reference it goes through
has a region the code was granted, which is a cell with a scope on the stack. -/
theorem TypedAt.not_freed {S : StoreTy} {s : State} (hR : Δ.regions) (ht : TypedAt Δ S s)
    (ho : Owns s) : ¬ Freed s := by
  rintro ⟨op, args, body, a, tag, pth, vs, htm, hev, hnone⟩
  obtain @⟨tm, env, stack, store, Γ, τ, ε, ε', ϕ, ϕ', henv, hty, hle, hsub, hst, hs⟩ := ht
  simp only at htm hev hnone
  subst htm
  have key : ∀ {x : Atom} {r : Rgn} {σ : Ty}, HasAtom Γ x (.ref r σ) → Grants ϕ r →
      ∀ {w : Value}, x.eval env = some w → w = .ref a tag pth → False := by
    intro x r σ hx hr w hw hwa
    obtain ⟨v, hv, hvt⟩ := atom_ok henv hx
    rw [hw] at hv
    cases hv
    subst hwa
    obtain ⟨b, _, _, _, hb, _, _, hreg, _⟩ := hvt.ref_inv
    cases hb
    obtain ⟨y, hy, hyc⟩ := (hreg hR).part
    have hpos := hst.onCell hR y a (.inl (hsub _ (hr y hy))) hyc
    obtain ⟨u, hu⟩ := ((ho a).2 (by
      show 0 < ownStack a stack + osum (ownStack a) store.conts
      omega))
    rw [hu] at hnone
    cases hnone
  cases hty with
  | @load _ x _ r σ _ _ ha hr _ _ =>
    cases hx : Atom.eval env x with
    | none => simp [evalAtoms, hx] at hev
    | some w =>
      simp [evalAtoms, hx] at hev
      exact key ha (hr hR) hx hev.1
  | @tag _ x path _ r σ _ _ _ ha hr _ _ =>
    cases hx : Atom.eval env x with
    | none => simp [evalAtoms, hx] at hev
    | some w =>
      cases hp : evalAtoms env path with
      | none => simp [evalAtoms, hx, hp] at hev
      | some ws =>
        simp [evalAtoms, hx, hp] at hev
        exact key ha (hr hR) hx hev.1
  | @focus _ x i _ r σ _ _ _ ha hr _ _ =>
    cases hx : Atom.eval env x with
    | none => simp [evalAtoms, hx] at hev
    | some w =>
      have hi : (Atom.int (i : Int)).eval env = some (.int i) := rfl
      simp [evalAtoms, hx, hi] at hev
      exact key ha (hr hR) hx hev.1
  | @focusIn _ x i built _ r σ _ _ _ _ ha hr _ _ _ =>
    cases hx : Atom.eval env x with
    | none => simp [evalAtoms, hx] at hev
    | some w =>
      have hi : (Atom.int (i : Int)).eval env = some (.int i) := rfl
      have hb : (Atom.int (built : Int)).eval env = some (.int built) := rfl
      simp [evalAtoms, hx, hi, hb] at hev
      exact key ha (hr hR) hx hev.1
  | @focusAt _ x ix _ r σ _ _ _ ha _ hr _ _ =>
    cases hx : Atom.eval env x with
    | none => simp [evalAtoms, hx] at hev
    | some w =>
      cases hi : Atom.eval env ix with
      | none => simp [evalAtoms, hx, hi] at hev
      | some w' =>
        simp [evalAtoms, hx, hi] at hev
        exact key ha (hr hR) hx hev.1
  | @store _ x y _ r σ _ _ hform _ _ =>
    have ha := hform.ref
    have hr := hform.region
    cases hx : Atom.eval env x with
    | none => simp [evalAtoms, hx] at hev
    | some w =>
      cases hy : Atom.eval env y with
      | none => simp [evalAtoms, hx, hy] at hev
      | some w' =>
        simp [evalAtoms, hx, hy] at hev
        exact key ha (hr hR) hx hev.1
  | @swap _ x y _ r σ _ _ hform _ _ =>
    have ha := hform.ref
    have hr := hform.region
    cases hx : Atom.eval env x with
    | none => simp [evalAtoms, hx] at hev
    | some w =>
      cases hy : Atom.eval env y with
      | none => simp [evalAtoms, hx, hy] at hev
      | some w' =>
        simp [evalAtoms, hx, hy] at hev
        exact key ha (hr hR) hx hev.1

/-! ## A label is applied only inside its scope -/

theorem findLabel_mem {id : Nat} : ∀ {st : List Frame}, Frame.label id ∈ st →
    findLabel Frame.asLabel id st ≠ none
  | [], h => by cases h
  | fr :: st, h => by
    by_cases hfr : fr.asLabel = some id
    · simp [findLabel, hfr]
    · have hm : Frame.label id ∈ st := by
        rcases List.mem_cons.mp h with rfl | hm
        · exact absurd rfl hfr
        · exact hm
      cases hrest : findLabel Frame.asLabel id st with
      | none => exact absurd hrest (findLabel_mem hm)
      | some x => simp [findLabel, hfr, hrest]

/-- A label is about to be applied whose scope is not on the stack. -/
def Dead (s : State) : Prop :=
  ∃ f id, calleeAtom s.tm = some f ∧ f.eval s.env = some (.label id)
    ∧ findLabel Frame.asLabel id s.stack = none

/-- Under the region rules, a typed state is not about to apply a label
outside its scope: the label's type says applying it touches the scope's
region, which the code was granted only if the scope is on the stack. -/
theorem TypedAt.not_dead {S : StoreTy} {s : State} (hR : Δ.regions) (ht : TypedAt Δ S s) :
    ¬ Dead s := by
  rintro ⟨f, id, hcallee, hev, hnone⟩
  obtain @⟨tm, env, stack, store, Γ, τ, ε, ε', ϕ, ϕ', henv, hty, hle, hsub, hst, hs⟩ := ht
  simp only at hcallee hev hnone
  -- The callable applied is the label, so it binds no region and its type
  -- says it touches the label's.
  have isLabel : ∀ {x : Atom} {n : Nat} {Ps : List Ty} {σ : Ty} {εf : Row} {once : Bool}
      {fenv : Option (List Ty)} {acc : List Rgn}, x = f →
      HasAtom Γ x (.fn n Ps σ εf once fenv acc) → n = 0 ∧ .lab id ∈ acc := by
    intro x n Ps σ εf once fenv acc hx hf
    subst hx
    obtain ⟨v, hv, hvt⟩ := atom_ok henv hf
    rw [hev] at hv
    cases hv
    rcases hvt.fn_inv with ⟨_, _, _, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨id', _, h, hn, _, _, hreg⟩
    · cases h
    · cases h
    · cases h
      exact ⟨hn, hreg hR⟩
  -- A granted label has its scope on the stack.
  have found : .lab id ∈ Rgn.flat ϕ → False := by
    intro hin
    exact findLabel_mem (hst.labelled _ (hsub _ hin)) hnone
  have opened : ∀ {n : Nat} {rs : List Rgn} {acc : List Rgn}, n = 0 → rs.length = n →
      .lab id ∈ acc → Sub (acc.map (Rgn.openAt 0 rs)) ϕ → False := by
    intro n rs acc hn hrs hin hacc
    subst hn
    have hnil : rs = [] := List.eq_nil_of_length_eq_zero hrs
    subst hnil
    exact found (hacc _ (Rgn.mem_flat.mpr
      ⟨_, List.mem_map.mpr ⟨_, hin, Rgn.openAt_nil 0 _⟩, List.mem_singleton_self _⟩))
  have scoped' : ∀ {n : Nat} {acc : List Rgn}, n = 0 → (Δ.regions → n = 1 ∧ True) → False := by
    intro n acc hn hreg
    have := (hreg hR).1
    omega
  cases hty with
  | ret _ => cases hcallee
  | let_ _ _ _ => cases hcallee
  | call hform _ _ =>
    have hf := hform.callee
    have hn := hform.len
    have hacc := hform.touches
    cases hcallee
    obtain ⟨h0, hin⟩ := isLabel rfl hf
    exact opened h0 hn hin hacc
  | tail hform _ _ =>
    have hf := hform.callee
    have hn := hform.len
    have hacc := hform.touches
    cases hcallee
    obtain ⟨h0, hin⟩ := isLabel rfl hf
    exact opened h0 hn hin hacc
  | callNever hform _ _ =>
    have hf := hform.callee
    have hn := hform.len
    have hacc := hform.touches
    cases hcallee
    obtain ⟨h0, hin⟩ := isLabel rfl hf
    exact opened h0 hn hin hacc
  | tailNever hform _ =>
    have hf := hform.callee
    have hn := hform.len
    have hacc := hform.touches
    cases hcallee
    obtain ⟨h0, hin⟩ := isLabel rfl hf
    exact opened h0 hn hin hacc
  | handle _ _ _ => cases hcallee
  | handleTail _ => cases hcallee
  | raise _ _ _ _ => cases hcallee
  | perform _ _ _ _ _ => cases hcallee
  | label hform _ _ =>
    have hthunk := hform.thunk
    have hreg := hform.region
    cases hcallee
    exact scoped' (acc := []) (isLabel rfl hthunk).1 (fun h => ⟨(hreg h).1, trivial⟩)
  | labelTail hform =>
    have hthunk := hform.thunk
    have hreg := hform.region
    cases hcallee
    exact scoped' (acc := []) (isLabel rfl hthunk).1 (fun h => ⟨(hreg h).1, trivial⟩)
  | guard _ _ _ => cases hcallee
  | guardTail _ _ => cases hcallee
  | cancel hk _ hacc _ _ _ =>
    cases hcallee
    exact found (hacc _ (Rgn.mem_flat.mpr ⟨_, (isLabel rfl hk).2, List.mem_singleton_self _⟩) rfl)
  | cell hform _ _ =>
    have hthunk := hform.thunk
    have hreg := hform.region
    cases hcallee
    exact scoped' (acc := []) (isLabel rfl hthunk).1 (fun h => ⟨(hreg h).1, trivial⟩)
  | cellTail hform _ =>
    have hthunk := hform.thunk
    have hreg := hform.region
    cases hcallee
    exact scoped' (acc := []) (isLabel rfl hthunk).1 (fun h => ⟨(hreg h).1, trivial⟩)
  | lend hform _ _ =>
    have hthunk := hform.thunk
    have hacc := hform.touches
    cases hcallee
    obtain ⟨h0, hin⟩ := isLabel rfl hthunk
    rcases hacc _ hin with ⟨h1, _⟩ | ⟨_, hmem, _⟩
    · omega
    · exact found (hmem _ (List.mem_singleton_self _))
  | load _ _ _ _ => cases hcallee
  | tag _ _ _ _ => cases hcallee
  | focus _ _ _ _ => cases hcallee
  | focusAt _ _ _ _ _ => cases hcallee
  | focusIn _ _ _ _ _ => cases hcallee
  | store _ _ _ => cases hcallee
  | swap _ _ _ => cases hcallee
  | write _ _ => cases hcallee
  | read _ => cases hcallee

/-- Every state a well-typed program reaches is well typed. -/
theorem run_typed {p : Program} (hp : ProgramOk Δ p) : ∀ (n : Nat) {c c' : Config},
    Typed Δ c.state → Machine.run (stepIO p) n c = .next c' → Typed Δ c'.state := by
  intro n
  induction n with
  | zero =>
    intro c c' ht h
    cases h
    exact ht
  | succ n ih =>
    intro c c' ht h
    rw [Machine.run_succ] at h
    have hstep := stepIO_ok hp ht
    cases hr : stepIO p c with
    | next c₁ =>
      rw [hr] at hstep
      rw [hr, Step.bind_next] at h
      exact ih hstep.1 h
    | halt r => rw [hr, Step.bind_halt] at h; cases h
    | stuck => rw [hr] at h; cases h

/--
**Borrow safety.** A program accepted with the region rules never reaches a
state about to read or write a released cell: every reference it reads or
writes through is to a cell whose scope is still on the stack.
-/
theorem borrow_safety {p : Program} (hp : ProgramOk Δ p) (hR : Δ.regions) (input : List Int)
    {c : Config} (h : Machine.Reaches (stepIO p) (initIO p input) c) : ¬ Freed c.state := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨S, ht⟩ := run_typed hp n (c := initIO p input) (typed_init hp) hn
  exact ht.not_freed hR (run_owns n (c := initIO p input) (owns_init p) hn)

/--
**Label safety.** Nor does it reach a state about to apply a label whose scope
has ended.
-/
theorem label_safety {p : Program} (hp : ProgramOk Δ p) (hR : Δ.regions) (input : List Int)
    {c : Config} (h : Machine.Reaches (stepIO p) (initIO p input) c) : ¬ Dead c.state := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨S, ht⟩ := run_typed hp n (c := initIO p input) (typed_init hp) hn
  exact ht.not_dead hR

/-- So when such a program goes wrong, the fault is neither a use of a released
cell nor a label applied after its scope ended. -/
theorem scoped_safety {p : Program} (hp : ProgramOk Δ p) (hR : Δ.regions) (input : List Int)
    (h : GoesWrong p input) :
    ∃ c, Machine.Reaches (stepIO p) (initIO p input) c ∧ stepIO p c = .stuck
      ∧ Fault c.state ∧ ¬ Freed c.state ∧ ¬ Dead c.state := by
  obtain ⟨c, hreach, hstuck, hf⟩ := type_safety hp input h
  exact ⟨c, hreach, hstuck, hf, borrow_safety hp hR input hreach, label_safety hp hR input hreach⟩

/-- An intrinsic has no result: arithmetic whose result does not fit, a
division by zero, an array read at a place that is not there. -/
def Overflow (s : State) : Prop :=
  ∃ q args body vs, s.tm = .let_ (.prim q args) body
    ∧ evalAtoms s.env args = some vs ∧ q.eval vs = none

/-- A part of a value is about to be read or written through a reference, and
it is not there: a place past the end of an array. Or a reference is asked for
to a place below zero. -/
def Absent (s : State) : Prop :=
  (∃ op args body a b path vs v, s.tm = .mem op args body
    ∧ evalAtoms s.env args = some (.ref a b path :: vs)
    ∧ s.store.cells[a]? = some (some v) ∧ v.part path = none)
  ∨ (∃ args body a b path i, s.tm = .mem .focus args body
    ∧ evalAtoms s.env args = some [.ref a b path, .int i] ∧ i < 0)

/-- Of the faults, those of something not fitting or not being there are the
ones that are none of the other three. -/
theorem Fault.overflow_of {s : State} (hf : Fault s) (h1 : ¬ Resumed s) (h2 : ¬ Freed s)
    (h3 : ¬ Dead s) : Overflow s ∨ Absent s := by
  cases hf with
  | overflow hargs hq => exact .inl ⟨_, _, _, _, rfl, hargs, hq⟩
  | absent hev hget hf => exact .inr (.inl ⟨_, _, _, _, _, _, _, _, rfl, hev, hget, hf⟩)
  | below hev hi => exact .inr (.inr ⟨_, _, _, _, _, _, rfl, hev, hi⟩)
  | freed hev hget => exact absurd ⟨_, _, _, _, _, _, _, rfl, hev, hget⟩ h2
  | resumed hc hev hget => exact absurd ⟨_, _, hc, hev, hget⟩ h1
  | dead hc hev hnone => exact absurd ⟨_, _, hc, hev, hnone⟩ h3

/--
**Soundness.** A program accepted with the ownership rules and the region
rules goes wrong in two ways only: an arithmetic result does not fit, or a part
of a value is not there, a place past the end of an array. It uses no
resumption twice, no cell after it was released, and no label after its scope
ended.
-/
theorem sound_safety {p : Program} (hp : ProgramOk Δ p) (hD : DupSound Δ) (hR : Δ.regions)
    (input : List Int) (h : GoesWrong p input) :
    ∃ c, Machine.Reaches (stepIO p) (initIO p input) c ∧ stepIO p c = .stuck
      ∧ (Overflow c.state ∨ Absent c.state) := by
  obtain ⟨c, hreach, hstuck, hf, hres⟩ := owned_safety hp hD input h
  exact ⟨c, hreach, hstuck, hf.overflow_of hres (borrow_safety hp hR input hreach)
    (label_safety hp hR input hreach)⟩

end Glorious.Typing
