module

public import Glorious.Typing.Cells

/-!
# A lent cell is used only through the borrow

A program checked with the rules for borrows never uses a reference it may
not: while a cell is lent for writing nothing reads or writes it but through
that borrow, while it is lent for reading nothing writes it, and no borrow is
used after its scope ended.

Nothing in the machine enforces this. A reference carries the identity of the
borrow it is, and the scope of a borrow is a frame on the stack, but reading
and writing ignore both. What the theorem says is that the stack of a checked
program is always one on which the use about to happen is permitted, by a
reading of the stack that involves no types: `allowed`.

The proof is about what a typed stack grants. A scope that lends a region
takes it away from the code above it and grants the borrow's region instead;
so among the regions granted, one that may be written is the only one of its
cell. Code uses a reference only if it was granted the reference's region.

A scope that a resumption captured would not be on the stack, and `allowed`
would not see it. There is none: the callable a borrow's scope runs performs
no operation it does not handle itself, so the frames a resumption captures
never include the scope, and no handler runs while a borrow is set aside.
-/

@[expose] public section

namespace Glorious.Typing

open Core

variable {Δ : Ctx}

/-- Whether the operation changes the cell. -/
def writes : MemOp → Bool
  | .load => false
  | .store => true
  | .swap => true
  | .tag => false
  | .focus => false

/-- Whether the reference to cell `a` that is borrow `b`, or the cell's own
reference if `b` is `0`, may be used on this stack: to write if `write`, and
otherwise to read. The scopes of the borrows of the cell are gone through from
the newest. A borrow's own scope lets it read, and write if it is a borrow for
writing. A newer borrow's scope lets an older reference read, if the newer
borrow is for reading, and nothing else. The cell's own reference has no
scope, being older than every borrow; a borrow that has none is out of scope. -/
def allowed (a b : Nat) (write : Bool) : List Frame → Bool
  | [] => b == 0
  | .lend uniq a' b' :: st =>
    if a' = a then
      if b' = b then uniq || !write else !uniq && !write && allowed a b write st
    else allowed a b write st
  | _ :: st => allowed a b write st

/-- A reference is about to be used that may not be: a cell is about to be
read, written or lent through a reference that a newer borrow in scope
excludes, or through a borrow whose scope has ended. -/
def Aliased (s : State) : Prop :=
  (∃ op args body a b path vs, s.tm = .mem op args body
      ∧ evalAtoms s.env args = some (.ref a b path :: vs)
      ∧ allowed a b (writes op) s.stack = false)
    ∨ (∃ uniq r thunk pre post body a b path, s.tm = .lend uniq r thunk pre post body
      ∧ r.eval s.env = some (.ref a b path) ∧ allowed a b uniq s.stack = false)

/-- The scope of a borrow is among the frames a resumption captured: the borrow
is set aside, and code outside its scope can run before it is taken up again. -/
def Suspended (s : State) : Prop :=
  ∃ (k : Nat) (seg : List Frame) (uniq : Bool) (a b : Nat),
    s.store.conts[k]? = some (some seg) ∧ Frame.lend uniq a b ∈ seg

/-- What a typed stack's grants say of borrows. A place that may be written
is the only granted place of its cell. A granted place's reference may be used
to read, and to write if writing the place was granted. And the own reference
of a cell with no scope on the stack is excluded by nothing. -/
def Excl (S : StoreTy) (st : List Frame) (ϕ : List Rgn) : Prop :=
  (∀ ρ r a, .wr ρ ∈ Rgn.flat ϕ → OnCell S ρ a → r ∈ Rgn.flat ϕ → OnCell S r a → r = ρ)
    ∧ (∀ r a b, r ∈ Rgn.flat ϕ → Tagged S r a b → allowed a b false st = true)
    ∧ (∀ r a b, .wr r ∈ Rgn.flat ϕ → Tagged S r a b → allowed a b true st = true)
    ∧ (∀ a w, ownStack a st = 0 → allowed a 0 w st = true)

theorem Excl.sub {S : StoreTy} {st : List Frame} {ϕ Φ : List Rgn} (h : Excl S st ϕ)
    (hsub : Sub Φ ϕ) : Excl S st Φ :=
  ⟨fun ρ r a hw hρ hr hra => h.1 ρ r a (hsub _ hw) hρ (hsub _ hr) hra,
    fun r a b hr ht => h.2.1 r a b (hsub _ hr) ht,
    fun r a b hw ht => h.2.2.1 r a b (hsub _ hw) ht, h.2.2.2⟩

/-- A frame that is no scope of a cell or a borrow changes nothing. -/
theorem Excl.skip {S : StoreTy} {st : List Frame} {ϕ : List Rgn} (h : Excl S st ϕ) (fr : Frame)
    (hfr : ∀ a b w, allowed a b w (fr :: st) = allowed a b w st) (hof : ∀ a, ownFrame a fr = 0) :
    Excl S (fr :: st) ϕ :=
  ⟨h.1, fun r a b hr ht => by rw [hfr]; exact h.2.1 r a b hr ht,
    fun r a b hw ht => by rw [hfr]; exact h.2.2.1 r a b hw ht,
    fun a w h0 => by
      rw [hfr]
      refine h.2.2.2 a w ?_
      simp only [ownStack, hof] at h0
      omega⟩

/-- Nor does granting a place that is of no cell. -/
theorem Excl.inert {S : StoreTy} {st : List Frame} {ϕ : List Rgn} (h : Excl S st ϕ) {x : Rgn}
    (hxa : x.atom = true) (hx : ∀ a, ¬ OnCell S x a) (hw : ∀ y, x ≠ .wr y) :
    Excl S st (x :: ϕ) := by
  refine ⟨fun ρ r a hwρ hρ hr hra => ?_, fun r a b hr ht => ?_, fun r a b hwr ht => ?_, h.2.2.2⟩
  · rw [Rgn.flat_cons_atom hxa] at hwρ hr
    rcases List.mem_cons.mp hwρ with he | hwρ
    · exact absurd he.symm (hw ρ)
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact absurd hra (hx a)
      · exact h.1 ρ r a hwρ hρ hr hra
  · rw [Rgn.flat_cons_atom hxa] at hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact absurd ht.onCell (hx a)
    · exact h.2.1 r a b hr ht
  · rw [Rgn.flat_cons_atom hxa] at hwr
    rcases List.mem_cons.mp hwr with he | hwr
    · exact absurd he.symm (hw r)
    · exact h.2.2.1 r a b hwr ht

theorem Tagged.part {S : StoreTy} {r : Rgn} {a b : Nat} (h : Tagged S r a b) :
    ∃ y, y ∈ r.parts ∧ Tagged S y a b := by
  obtain ⟨y, hy, ht⟩ := h
  exact ⟨y, hy, y, Rgn.self_mem_parts (Rgn.mem_parts_atom hy), ht⟩

theorem Tagged.cell_inv {S : StoreTy} {c a b : Nat} (h : Tagged S (.cell c) a b) :
    c = a ∧ b = 0 := by
  obtain ⟨y, hy, ht⟩ := h
  simp only [Rgn.parts, List.mem_singleton] at hy
  subst hy
  rcases ht with ⟨he, hb⟩ | ⟨he, _⟩
  · cases he
    exact ⟨rfl, hb⟩
  · cases he

theorem Tagged.loan_inv {S : StoreTy} {b' a b : Nat} (h : Tagged S (.loan b') a b) :
    b' = b ∧ S.loans b = some a := by
  obtain ⟨y, hy, ht⟩ := h
  simp only [Rgn.parts, List.mem_singleton] at hy
  subst hy
  rcases ht with ⟨he, _⟩ | ⟨he, hl⟩
  · cases he
  · cases he
    exact ⟨rfl, hl⟩

theorem Tagged.not_wr {S : StoreTy} {r : Rgn} {a b : Nat} : ¬ Tagged S (.wr r) a b :=
  fun h => OnCell.not_wr h.onCell

/-- **What a typed stack grants excludes what was lent.** -/
theorem StackOk.exclusive {S : StoreTy} {st : List Frame} {τ : Ty} {ε : Row} {ϕ : List Rgn}
    (hR : Δ.regions) (hL : Δ.loans) (h : StackOk Δ S st τ ε ϕ) :
    (∀ a, ownStack a st ≤ 1) → Excl S st ϕ := by
  induction h with
  | nil =>
    intro _
    exact ⟨fun _ _ _ h => (by cases h), fun _ _ _ h => (by cases h), fun _ _ _ h => (by cases h),
      fun _ _ _ => rfl⟩
  | call _ _ _ _ _ ih =>
    intro hown
    exact (ih fun a => Nat.le_trans (Nat.le_add_left _ _) (hown a)).skip _
      (fun _ _ _ => rfl) (fun _ => rfl)
  | handler _ _ _ hΦ _ ih =>
    intro hown
    exact ((ih fun a => Nat.le_trans (Nat.le_add_left _ _) (hown a)).sub hΦ).skip _
      (fun _ _ _ => rfl) (fun _ => rfl)
  | label _ _ ih =>
    intro hown
    exact ((ih fun a => Nat.le_trans (Nat.le_add_left _ _) (hown a)).skip _
      (fun _ _ _ => rfl) (fun _ => rfl)).inert rfl (fun _ hc => OnCell.not_lab hc)
      (fun y h => by cases h)
  | guard _ _ _ ih =>
    intro hown
    exact (ih fun a => Nat.le_trans (Nat.le_add_left _ _) (hown a)).skip _
      (fun _ _ _ => rfl) (fun _ => rfl)
  | @cell c st σ τ ε ϕ _ hst ih =>
    intro hown
    have E := ih fun a => Nat.le_trans (Nat.le_add_left _ _) (hown a)
    have h0 : ownStack c st = 0 := by
      have := hown c
      simp only [ownStack, ownFrame, ↓reduceIte] at this
      omega
    -- Nothing granted below the scope is of its cell.
    have hN : ∀ x, (x ∈ Rgn.flat ϕ ∨ .wr x ∈ Rgn.flat ϕ) → ¬ OnCell S x c := fun x hx hc => by
      have := hst.onCell hR x c hx hc
      omega
    have hskip : ∀ a b w, allowed a b w (.cell c :: st) = allowed a b w st := fun _ _ _ => rfl
    have hfl : Rgn.flat (.cell c :: .wr (.cell c) :: ϕ) = .cell c :: .wr (.cell c) :: Rgn.flat ϕ := by
      rw [Rgn.flat_cons_atom rfl, Rgn.flat_cons_atom rfl]
    refine ⟨fun ρ r a hw hρ hr hra => ?_, fun r a b hr ht => ?_, fun r a b hw ht => ?_,
      fun a w hz => ?_⟩
    · rw [hfl] at hw hr
      rcases List.mem_cons.mp hw with he | hw
      · cases he
      · rcases List.mem_cons.mp hw with he | hw
        · cases he
          cases hρ.cell_eq
          rcases List.mem_cons.mp hr with rfl | hr
          · rfl
          · rcases List.mem_cons.mp hr with rfl | hr
            · exact absurd hra OnCell.not_wr
            · exact absurd hra (hN r (.inl hr))
        · rcases List.mem_cons.mp hr with rfl | hr
          · cases hra.cell_eq
            exact absurd hρ (hN ρ (.inr hw))
          · rcases List.mem_cons.mp hr with rfl | hr
            · exact absurd hra OnCell.not_wr
            · exact E.1 ρ r a hw hρ hr hra
    · rw [hskip]
      rw [hfl] at hr
      rcases List.mem_cons.mp hr with rfl | hr
      · obtain ⟨rfl, rfl⟩ := ht.cell_inv
        exact E.2.2.2 _ false h0
      · rcases List.mem_cons.mp hr with rfl | hr
        · exact absurd ht Tagged.not_wr
        · exact E.2.1 r a b hr ht
    · rw [hskip]
      rw [hfl] at hw
      rcases List.mem_cons.mp hw with he | hw
      · cases he
      · rcases List.mem_cons.mp hw with he | hw
        · cases he
          obtain ⟨rfl, rfl⟩ := ht.cell_inv
          exact E.2.2.2 _ true h0
        · exact E.2.2.1 r a b hw ht
    · rw [hskip]
      refine E.2.2.2 a w ?_
      simp only [ownStack] at hz
      omega
  | @lend u c b' st τ ε ϕ ρ hl hb hon hρ hw hst ih =>
    intro hown
    have E := ih fun a => Nat.le_trans (Nat.le_add_left _ _) (hown a)
    -- The place of what was lent that is of the cell.
    obtain ⟨ρ₀, hρ₀, hon₀⟩ := hon.part
    have hρ₀ϕ : ρ₀ ∈ Rgn.flat ϕ := hρ ρ₀ hρ₀
    have hwρ₀ : u = true → .wr ρ₀ ∈ Rgn.flat ϕ := fun hu =>
      hw hu (.wr ρ₀) (List.mem_map.mpr ⟨ρ₀, hρ₀, rfl⟩)
    have hwmem : .wr ρ₀ ∈ (Rgn.wr ρ).parts := List.mem_map.mpr ⟨ρ₀, hρ₀, rfl⟩
    refine ⟨fun ρ₁ r a hw₁ hρ₁ hr hra => ?_, fun r a b hr ht => ?_, fun r a b hwr ht => ?_,
      fun a w hz => ?_⟩
    · rw [flat_lent] at hw₁ hr
      rcases mem_lent.mp hw₁ with he | ⟨hu, he⟩ | ⟨hw₁, hne, _⟩
      · cases he
      · cases he
        cases hρ₁.loan_eq hl
        rcases mem_lent.mp hr with rfl | ⟨_, rfl⟩ | ⟨hr, _, hne', _⟩
        · rfl
        · exact absurd hra OnCell.not_wr
        · have := E.1 ρ₀ r c (hwρ₀ hu) hon₀ hr hra
          subst this
          exact absurd hρ₀ (hne' hu)
      · rcases mem_lent.mp hr with rfl | ⟨_, rfl⟩ | ⟨hr, _⟩
        · cases hra.loan_eq hl
          have := E.1 ρ₁ ρ₀ c hw₁ hρ₁ hρ₀ϕ hon₀
          subst this
          exact absurd hwmem hne
        · exact absurd hra OnCell.not_wr
        · exact E.1 ρ₁ r a hw₁ hρ₁ hr hra
    · rw [flat_lent] at hr
      rcases mem_lent.mp hr with rfl | ⟨_, rfl⟩ | ⟨hrϕ, _, hne, hnl, _⟩
      · obtain ⟨rfl, hl'⟩ := ht.loan_inv
        rw [hl] at hl'
        cases hl'
        simp [allowed]
      · exact absurd ht Tagged.not_wr
      · by_cases hca : c = a
        · subst hca
          have hbb : b' ≠ b := by
            rintro rfl
            obtain ⟨y, hy, hyt⟩ := ht
            have hyr : y = r := by
              have := Rgn.atom_parts (Rgn.atom_of_mem_flat hrϕ)
              rw [this] at hy
              exact List.mem_singleton.mp hy
            subst hyr
            rcases hyt with ⟨_, h0⟩ | ⟨he, _⟩
            · omega
            · exact hnl he
          have hu : u = false := by
            cases u with
            | false => rfl
            | true =>
              have := E.1 ρ₀ r c (hwρ₀ rfl) hon₀ hrϕ ht.onCell
              subst this
              exact absurd hρ₀ (hne rfl)
          simp [allowed, hbb, hu, E.2.1 r c b hrϕ ht]
        · simp [allowed, hca, E.2.1 r a b hrϕ ht]
    · rw [flat_lent] at hwr
      rcases mem_lent.mp hwr with he | ⟨hu, he⟩ | ⟨hwr, hne, _⟩
      · cases he
      · cases he
        obtain ⟨rfl, hl'⟩ := ht.loan_inv
        rw [hl] at hl'
        cases hl'
        simp [allowed, hu]
      · by_cases hca : c = a
        · subst hca
          have := E.1 r ρ₀ c hwr ht.onCell hρ₀ϕ hon₀
          subst this
          exact absurd hwmem hne
        · simp [allowed, hca, E.2.2.1 r a b hwr ht]
    · by_cases hca : c = a
      · subst hca
        have := hst.onCell hR ρ₀ c (.inl hρ₀ϕ) hon₀
        simp only [ownStack, ownFrame] at hz
        omega
      · simp only [allowed, hca, ↓reduceIte]
        refine E.2.2.2 a w ?_
        simp only [ownStack, ownFrame] at hz
        omega
  | lendLoose hn _ _ _ _ => exact absurd ⟨hR, hL⟩ hn
  | yield _ _ ih =>
    intro hown
    exact (ih fun a => Nat.le_trans (Nat.le_add_left _ _) (hown a)).skip _
      (fun _ _ _ => rfl) (fun _ => rfl)
  | exit _ _ _ ih =>
    intro hown
    exact (ih fun a => Nat.le_trans (Nat.le_add_left _ _) (hown a)).skip _
      (fun _ _ _ => rfl) (fun _ => rfl)
  | never _ ih => exact ih

/-- Under the region rules and the rules for borrows, a typed state in which
no cell has two scopes is not about to use a reference it may not: the
reference has a region the code was granted, and to write, one it was granted
to write. -/
theorem TypedAt.not_aliased {S : StoreTy} {s : State} (hR : Δ.regions) (hL : Δ.loans)
    (ht : TypedAt Δ S s) (ho : Owns s) : ¬ Aliased s := by
  obtain @⟨tm, env, stack, store, Γ, τ, ε, ε', ϕ, ϕ', henv, hty, hle, hsub, hst, hs⟩ := ht
  have hown : ∀ a, ownStack a stack ≤ 1 := fun a => by
    have : ownStack a stack + osum (ownStack a) store.conts ≤ 1 := (ho a).1
    omega
  obtain ⟨_, hread, hwrite, _⟩ := hst.exclusive hR hL hown
  have key : ∀ {x : Atom} {r : Rgn} {σ : Ty} {a b : Nat} {pth : List PathStep},
      HasAtom Γ x (.ref r σ) → x.eval env = some (.ref a b pth) → Tagged S r a b := by
    intro x r σ a b pth hx hw
    obtain ⟨v, hv, hvt⟩ := atom_ok henv hx
    rw [hw] at hv
    cases hv
    obtain ⟨a', b', _, _, he, _, _, _, htag⟩ := hvt.ref_inv
    cases he
    exact htag hR hL
  -- Through the place of the region the reference is of.
  have rd : ∀ {r : Rgn} {a b : Nat}, Grants ϕ r → Tagged S r a b → allowed a b false stack = true := by
    intro r a b hg ht
    obtain ⟨y, hy, hyt⟩ := ht.part
    exact hread y a b (hsub _ (hg y hy)) hyt
  have wrt : ∀ {r : Rgn} {a b : Nat}, Grants ϕ (.wr r) → Tagged S r a b →
      allowed a b true stack = true := by
    intro r a b hg ht
    obtain ⟨y, hy, hyt⟩ := ht.part
    exact hwrite y a b (hsub _ (hg (.wr y) (List.mem_map.mpr ⟨y, hy, rfl⟩))) hyt
  rintro (⟨op, args, body, a, b, pth, vs, htm, hev, hno⟩
    | ⟨uniq, r, thunk, pre, post, body, a, b, pth, htm, hev, hno⟩)
  · simp only at htm hev hno
    subst htm
    cases hty with
    | @load _ x _ r σ _ _ ha hr _ _ =>
      cases hx : Atom.eval env x with
      | none => simp [evalAtoms, hx] at hev
      | some w =>
        simp [evalAtoms, hx] at hev
        rw [hev.1] at hx
        have := rd (hr hR) (key ha hx)
        simp [writes, this] at hno
    | @tag _ x path _ r σ _ _ _ ha hr _ _ =>
      cases hx : Atom.eval env x with
      | none => simp [evalAtoms, hx] at hev
      | some w =>
        cases hp : evalAtoms env path with
        | none => simp [evalAtoms, hx, hp] at hev
        | some ws =>
          simp [evalAtoms, hx, hp] at hev
          rw [hev.1] at hx
          have := rd (hr hR) (key ha hx)
          simp [writes, this] at hno
    | @focus _ x i _ r σ _ _ _ ha hr _ _ =>
      cases hx : Atom.eval env x with
      | none => simp [evalAtoms, hx] at hev
      | some w =>
        have hi : (Atom.int (i : Int)).eval env = some (.int i) := rfl
        simp [evalAtoms, hx, hi] at hev
        rw [hev.1] at hx
        have := rd (hr hR) (key ha hx)
        simp [writes, this] at hno
    | @focusIn _ x i built _ r σ _ _ _ _ ha hr _ _ _ =>
      cases hx : Atom.eval env x with
      | none => simp [evalAtoms, hx] at hev
      | some w =>
        have hi : (Atom.int (i : Int)).eval env = some (.int i) := rfl
        have hb : (Atom.int (built : Int)).eval env = some (.int built) := rfl
        simp [evalAtoms, hx, hi, hb] at hev
        rw [hev.1] at hx
        have := rd (hr hR) (key ha hx)
        simp [writes, this] at hno
    | @focusAt _ x ix _ r σ _ _ _ ha _ hr _ _ =>
      cases hx : Atom.eval env x with
      | none => simp [evalAtoms, hx] at hev
      | some w =>
        cases hi : Atom.eval env ix with
        | none => simp [evalAtoms, hx, hi] at hev
        | some w' =>
          simp [evalAtoms, hx, hi] at hev
          rw [hev.1] at hx
          have := rd (hr hR) (key ha hx)
          simp [writes, this] at hno
    | @store _ x y _ r σ _ _ hform _ _ =>
      cases hx : Atom.eval env x with
      | none => simp [evalAtoms, hx] at hev
      | some w =>
        cases hy : Atom.eval env y with
        | none => simp [evalAtoms, hx, hy] at hev
        | some w' =>
          simp [evalAtoms, hx, hy] at hev
          rw [hev.1] at hx
          have := wrt (hform.write hL) (key hform.ref hx)
          simp [writes, this] at hno
    | @swap _ x y _ r σ _ _ hform _ _ =>
      cases hx : Atom.eval env x with
      | none => simp [evalAtoms, hx] at hev
      | some w =>
        cases hy : Atom.eval env y with
        | none => simp [evalAtoms, hx, hy] at hev
        | some w' =>
          simp [evalAtoms, hx, hy] at hev
          rw [hev.1] at hx
          have := wrt (hform.write hL) (key hform.ref hx)
          simp [writes, this] at hno
  · simp only at htm hev hno
    subst htm
    cases hty with
    | lend hform _ _ =>
      have htag := key hform.ref hev
      cases uniq with
      | false =>
        have := rd (hform.region hR) htag
        simp [this] at hno
      | true =>
        have := wrt ((hform.loan hL).2.2.1 rfl) htag
        simp [this] at hno

/-- Under the same rules no resumption of a typed state captured the scope of a
borrow. -/
theorem TypedAt.not_suspended {S : StoreTy} {s : State} (hR : Δ.regions) (hL : Δ.loans)
    (ht : TypedAt Δ S s) : ¬ Suspended s := by
  obtain @⟨tm, env, stack, store, Γ, τ, ε, ε', ϕ, ϕ', henv, hty, hle, hsub, hst, hs⟩ := ht
  rintro ⟨k, seg, uniq, a, b, hk, hm⟩
  exact hs.quiet ⟨hR, hL⟩ k seg hk uniq a b hm

/--
**Exclusive borrows.** A program accepted with the region rules and the rules
for borrows never reaches a state about to use a reference it may not. Whenever
it reads a cell, every borrow of the cell newer than the reference it reads
through is for reading; whenever it writes one, or lends it for writing, there
is no newer borrow, and the reference is the cell's own or a borrow for
writing; and every borrow it uses is still in scope. Nor is the scope of a
borrow ever set aside in a resumption: every borrow there is, is on the stack.
-/
theorem exclusive_safety {p : Program} (hp : ProgramOk Δ p) (hR : Δ.regions) (hL : Δ.loans)
    (input : List Int) {c : Config} (h : Machine.Reaches (stepIO p) (initIO p input) c) :
    ¬ Aliased c.state ∧ ¬ Suspended c.state := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨S, ht⟩ := run_typed hp n (c := initIO p input) (typed_init hp) hn
  exact ⟨ht.not_aliased hR hL (run_owns n (c := initIO p input) (owns_init p) hn),
    ht.not_suspended hR hL⟩

end Glorious.Typing
