import OwnershipMir.LoanMutation

namespace OwnershipMir

private theorem total_member_le {n : Nat} (f : Fin n → Nat) (i : Fin n) : f i ≤ total f := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [total]; omega
    · have bound := ih (fun k => f k.succ) j
      simp only [total]; omega

private theorem sum_map_member_le {α : Type} (f : α → Nat) {items : List α} {item : α}
    (member : item ∈ items) : f item ≤ (items.map f).sum := by
  induction items with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with same | member
    · subst item; simp only [List.map_cons, List.sum_cons]; omega
    · have bound := ih member
      simp only [List.map_cons, List.sum_cons]; omega

theorem Tree.Contains.mass_le {α : Type} {tree : Tree α} {atom : α} (contains : tree.Contains atom)
    (leaf : α → Nat) (shell : Shell → Nat) : leaf atom ≤ tree.mass leaf shell := by
  induction contains with
  | leaf => exact Nat.le_refl _
  | left member ih => simp only [Tree.mass]; omega
  | right member ih => simp only [Tree.mass]; omega
  | body member ih => simp only [Tree.mass]; omega

theorem Store.Contains.mass_le {n : Nat} {store : Store n Atom} {atom : Atom} (contains : store.Contains atom)
    (leaf : Atom → Nat) (shell : Shell → Nat) : leaf atom ≤ store.mass leaf shell := by
  rcases contains with ⟨value, register, member⟩ | ⟨region, slots, root, value, live, resident, member⟩
  · have bound := member.mass_le leaf shell
    simp only [Store.mass, register, cellMass]; omega
  · have selected := member.mass_le leaf shell
    have rootBound := total_member_le (fun i => cellMass leaf shell (slots i)) root
    rw [resident] at rootBound
    have regionMember : some slots ∈ store.regions :=
      List.mem_iff_getElem?.mpr ⟨region, Option.join_eq_some_iff.mp live⟩
    have regionBound := sum_map_member_le (fun entry : Option (Region n Atom) => match entry with
      | none => 0
      | some roots => total (fun i => cellMass leaf shell (roots i))) regionMember
    unfold Store.mass
    dsimp only [cellMass] at rootBound regionBound ⊢
    apply Nat.le_trans (Nat.le_trans selected (Nat.le_trans rootBound regionBound))
    apply Nat.le_trans ?_ (Nat.le_add_right _ _)
    apply Nat.le_of_eq
    apply congrArg List.sum
    apply congrArg (fun f => store.regions.map f)
    funext entry
    cases entry <;> rfl

/-- Exact physical conservation implies preservation of the resident atom set,
including shared aliases. No additional alias table or reference walker is
maintained by execution. -/
theorem Store.contains_iff_of_mass_eq {n : Nat} {before after : Store n Atom}
    (mass : ∀ leaf shell, after.mass leaf shell = before.mass leaf shell) (atom : Atom) :
    after.Contains atom ↔ before.Contains atom := by
  classical
  have forward : ∀ {a b : Store n Atom},
      (∀ leaf shell, a.mass leaf shell = b.mass leaf shell) → a.Contains atom → b.Contains atom := by
    intro a b conserved contains
    by_cases missing : b.Contains atom
    · exact missing
    apply False.elim
    have empty : b.mass (fun item => if item = atom then 1 else 0) (fun _ => 0) = 0 := by
      apply Store.mass_zero_of_atoms
      intro item present
      by_cases same : item = atom
      · subst item; exact False.elim (missing present)
      · exact if_neg same
    have present := contains.mass_le (fun item => if item = atom then 1 else 0) (fun _ => 0)
    rw [conserved, empty] at present
    simp at present
  exact ⟨forward mass, forward (fun leaf shell => (mass leaf shell).symm)⟩

theorem Address.Within.trans {n : Nat} {a b c : Address n}
    (ab : a.Within b) (bc : b.Within c) : a.Within c :=
  ⟨ab.1.trans bc.1, ab.2.1.trans bc.2.1, bc.2.2.trans ab.2.2⟩

theorem Store.Ancestor.within {n : Nat} {store : Store n Atom}
    (graph : store.LoanGraph) {ancestor child : Nat} (related : store.Ancestor ancestor child)
    {origin loan : Loan n} (first : store.loans[ancestor]? = some origin)
    (last : store.loans[child]? = some loan) : loan.referent.Within origin.referent := by
  induction related generalizing loan with
  | refl => cases Option.some.inj (first.symm.trans last); exact Address.within_refl _
  | parent found link earlier ih =>
    cases Option.some.inj (found.symm.trans last)
    obtain ⟨_, parent, parentFound, within, _⟩ := graph _ _ found _ link
    exact within.trans (ih parentFound)

theorem Store.Permitted.unique_overlap_within {n : Nat} {store : Store n Atom}
    (graph : store.LoanGraph) {via : Option Nat} {address : Address n}
    (permission : store.Permitted via .unique address) {identity : Nat} {loan : Loan n}
    (found : store.loans[identity]? = some loan) (active : store.Active identity)
    (overlap : address.Overlaps loan.referent) : address.Within loan.referent := by
  rcases permission.2 identity loan found active overlap with shared | ⟨parent, same, ancestor⟩
  · cases shared.1
  · have authorized := permission.1
    rw [same] at authorized
    obtain ⟨origin, originFound, _, within, _⟩ := authorized
    exact within.trans (ancestor.within graph found originFound)

/-- A declared hole retains the layout of the extracted field. -/
theorem focus_rebuild_layout {α : Type} (kind : α → AtomType)
    {path : List Direction} {layout : Layout} {tree : Tree α} {lens : Lens α}
    (found : focus path layout (some tree) = some lens)
    (selected : (lens.selected.getD (.hole layout)).layout kind = layout)
    {replacement : Cell α} (typed : (replacement.getD (.hole layout)).layout kind = layout) :
    ((lens.rebuild replacement).getD (.hole layout)).layout kind = tree.layout kind := by
  induction path generalizing tree lens with
  | nil => cases Option.some.inj found; exact typed.trans selected.symm
  | cons direction path ih =>
    cases direction <;> cases tree <;> simp only [focus] at found
    all_goals try contradiction
    all_goals
      obtain ⟨sub, focused, rfl⟩ := Option.map_eq_some_iff.mp found
      simp only [Option.getD_some, Tree.layout]
      rw [ih focused selected]

/-- A permitted write can change an enclosing referent, or a disjoint field,
but never overwrite a strict descendant referent. Exact layout replacement
therefore preserves every query allowed by that pre-state path relation. -/
theorem focus_frame_layout {α : Type} (kind : α → AtomType)
    {path query : List Direction} {layout queryLayout : Layout} {cell : Cell α}
    {write read : Lens α} {original replacement : Tree α}
    (writing : focus path layout cell = some write)
    (selected : (write.selected.getD (.hole layout)).layout kind = layout)
    (replacementType : replacement.layout kind = layout)
    (reading : focus query queryLayout cell = some read) (resident : read.selected = some original)
    (originalType : original.layout kind = queryLayout)
    (allowed : path.IsPrefix query → query.IsPrefix path) :
    ∃ after value, focus query queryLayout (write.rebuild (some replacement)) = some after ∧
      after.selected = some value ∧ value.layout kind = queryLayout := by
  induction query generalizing path cell write read original with
  | nil =>
    cases Option.some.inj reading
    change cell = some original at resident
    subst cell
    obtain ⟨changed, present⟩ := focus_rebuild_present writing replacement
    have unchanged := focus_rebuild_layout kind writing selected (replacement := some replacement) replacementType
    rw [present] at unchanged
    exact ⟨⟨some changed, id⟩, changed, by simp [focus, present], rfl, unchanged.trans originalType⟩
  | cons direction query ih =>
    cases path with
    | nil =>
      have impossible := List.prefix_nil.mp (allowed List.nil_prefix)
      cases impossible
    | cons step path =>
      cases cell with
      | none => cases step <;> simp [focus] at writing
      | some tree =>
        cases step <;> cases direction <;> cases tree <;> simp only [focus] at writing reading
        all_goals try contradiction
        all_goals
          obtain ⟨sub, focused, rfl⟩ := Option.map_eq_some_iff.mp writing
          obtain ⟨subQuery, qfocused, rfl⟩ := Option.map_eq_some_iff.mp reading
        all_goals first
          | (simp only [focus, qfocused, Option.map_some]; exact ⟨_, original, rfl, resident, originalType⟩)
          | (obtain ⟨changed, present⟩ := focus_rebuild_present focused replacement
             obtain ⟨after, value, located, nowResident, typed⟩ := ih focused selected qfocused resident originalType
               (by intro nested; exact (List.prefix_cons_inj _).mp (allowed ((List.prefix_cons_inj _).mpr nested)))
             rw [present] at located
             simp only [focus, present, Option.getD_some, located, Option.map_some]
             exact ⟨_, value, rfl, nowResident, typed⟩)


theorem Store.Referent.replaceLoan {n : Nat} {store : Store n Atom} {signature : Signature}
    {writing reading : Loan n} {identity : Nat} {via : Option Nat} {slots : Region n Atom} {lens : Lens Atom}
    (graph : store.LoanGraph) (permission : store.Permitted via .unique writing.referent)
    (origin : store.loans[identity]? = some reading) (active : store.Active identity)
    (referent : store.Referent signature reading)
    (live : store.region writing.referent.region = some slots)
    (focused : (writing.referent.place writing.target).find slots = some lens)
    (selected : (lens.selected.getD (.hole writing.target)).layout (Atom.kind signature) = writing.target)
    (value : Value) (typed : value.layout (Atom.kind signature) = writing.target) (temp : Cell Atom) :
    (store.replaceLoan writing slots lens value temp).Referent signature reading := by
  obtain ⟨read, original, found, resident, originalType⟩ := referent
  obtain ⟨roots, originalLive, readingFocus⟩ := Option.bind_eq_some_iff.mp found
  by_cases sameRegion : reading.referent.region = writing.referent.region
  · have sameRoots := Option.some.inj ((sameRegion ▸ originalLive).symm.trans live)
    subst roots
    by_cases sameRoot : reading.referent.root = writing.referent.root
    · have allowed : writing.referent.path.IsPrefix reading.referent.path →
          reading.referent.path.IsPrefix writing.referent.path := by
        intro nested
        exact (permission.unique_overlap_within graph origin active (Or.inr ⟨sameRegion, sameRoot, nested⟩)).2.2
      have query : focus reading.referent.path reading.target (slots writing.referent.root) = some read := by
        simpa only [Place.find, Address.place, sameRoot] using readingFocus
      obtain ⟨after, changed, located, nowResident, changedType⟩ :=
        focus_frame_layout (Atom.kind signature) focused selected typed query resident originalType allowed
      refine ⟨after, changed, ?_, nowResident, changedType⟩
      unfold Store.find Store.replaceLoan
      rw [sameRegion, Store.replace_same (Store.region_bound live)]
      simpa [Place.find, Place.write, Address.place, sameRoot] using located
    · refine ⟨read, original, ?_, resident, originalType⟩
      unfold Store.find Store.replaceLoan
      rw [sameRegion, Store.replace_same (Store.region_bound live)]
      simpa [Place.find, Place.write, Address.place, update, sameRoot] using readingFocus
  · refine ⟨read, original, ?_, resident, originalType⟩
    unfold Store.find Store.replaceLoan
    rw [Store.replace_other _ _ _ _ _ sameRegion, originalLive]
    exact readingFocus

/-- The pre-state permission and the existing physical balance equation frame
all live references. In particular, the proof does not assume post-state
reference validity or remove overlapping ancestor loans. -/
theorem Store.BorrowInvariant.replaceLoan {n : Nat} {store : Store n Atom} {signature : Signature}
    (valid : store.BorrowInvariant signature) {loan : Loan n} {via : Option Nat}
    {slots : Region n Atom} {lens : Lens Atom}
    (permission : store.Permitted via .unique loan.referent)
    (live : store.region loan.referent.region = some slots)
    (focused : (loan.referent.place loan.target).find slots = some lens)
    (selected : (lens.selected.getD (.hole loan.target)).layout (Atom.kind signature) = loan.target)
    (value : Value) (typed : value.layout (Atom.kind signature) = loan.target) (temp : Cell Atom)
    (balance : ∀ leaf shell, cellMass leaf shell lens.selected + cellMass leaf shell store.temp =
      cellMass leaf shell (some value) + cellMass leaf shell temp) :
    (store.replaceLoan loan slots lens value temp).BorrowInvariant signature ∧
      ∀ authority mode address, (store.replaceLoan loan slots lens value temp).Permitted authority mode address ↔
        store.Permitted authority mode address := by
  let after := store.replaceLoan loan slots lens value temp
  have mass : ∀ leaf shell, after.mass leaf shell = store.mass leaf shell := by
    intro leaf shell
    have replaced := store.replaceLoan_mass live focused value temp leaf shell
    have same := balance leaf shell
    change (store.replaceLoan loan slots lens value temp).mass leaf shell = _
    omega
  have contains := Store.contains_iff_of_mass_eq mass
  have handles : ∀ id, after.HasHandle id ↔ store.HasHandle id := by
    intro id; simp only [Store.HasHandle, contains]
  have ancestry := Store.ancestor_iff_of_loans_eq (before := after) (after := store) rfl
  have active : ∀ id, after.Active id ↔ store.Active id := by
    intro id; simp only [Store.Active, handles, ancestry]
  change after.BorrowInvariant signature ∧ ∀ authority mode address, after.Permitted authority mode address ↔ _
  constructor
  · refine ⟨valid.graph, ?_, ?_, ?_⟩
    · intro id mode target member
      have oldMember := (contains _).mp member
      obtain ⟨reading, origin, modeEq, targetEq, referent⟩ := valid.references id mode target oldMember
      exact ⟨reading, origin, modeEq, targetEq, referent.replaceLoan valid.graph permission origin
        (Store.hasHandle_active ⟨mode, target, oldMember⟩) live focused selected value typed temp⟩
    · intro first left second right leftFound leftActive rightFound rightActive overlaps
      simpa only [ancestry] using valid.compatible first left second right leftFound ((active _).mp leftActive)
        rightFound ((active _).mp rightActive) overlaps
    · intro resource; change after.mass _ _ ≤ 1; rw [mass]; exact valid.unique resource
  · intro authority mode address
    simp only [Store.Permitted, handles, active, ancestry]
    rfl


/-- Authorized movement preserves the complete borrow invariant. The referent
remains present with its exact layout, but cannot pass initialized-loan admission
until a subsequent write restores it. -/
theorem MoveLoanReady.progress {n : Nat} {store : Store n Atom} {signature : Signature} {identity : Nat}
    (valid : store.BorrowInvariant signature) (ready : MoveLoanReady store identity) :
    ∃ after loan value, store.moveLoan identity = some after ∧ after.temp = some value ∧
      value.layout (Atom.kind signature) = loan.target ∧ value.ready ∧ after.Referent signature loan ∧
      after.BorrowInvariant signature ∧ ¬ after.LoanReady identity ∧
      (∀ authority mode address, after.Permitted authority mode address ↔ store.Permitted authority mode address) ∧
      ∀ leaf shell, after.mass leaf shell = store.mass leaf shell := by
  obtain ⟨loan, lens, value, origin, focused, selected, initialized⟩ := ready.initialized
  have permission := ready.permission loan origin
  obtain ⟨_, _, handle, _⟩ := permission.1
  obtain ⟨mode, target, contains⟩ := handle
  obtain ⟨sameLoan, sameOrigin, _, _, otherLens, otherValue, otherFocus, otherSelected, typed⟩ :=
    valid.references identity mode target contains
  cases Option.some.inj (origin.symm.trans sameOrigin)
  cases Option.some.inj (focused.symm.trans otherFocus)
  cases Option.some.inj (selected.symm.trans otherSelected)
  obtain ⟨slots, live, located⟩ := Option.bind_eq_some_iff.mp focused
  let after := store.replaceLoan loan slots lens (.hole loan.target) (some value)
  obtain ⟨afterLens, found, hole, _⟩ := store.replaceLoan_find live located (.hole loan.target) (some value)
  have mass : ∀ leaf shell, after.mass leaf shell = store.mass leaf shell :=
    store.moveLoan_mass live located selected ready.empty
  have framed := valid.replaceLoan permission live located (by simpa [selected] using typed)
    (.hole loan.target) rfl (some value) (by intro leaf shell; simp [selected, ready.empty, cellMass, Tree.mass])
  refine ⟨after, loan, value, ?_, rfl, typed, initialized,
    ⟨afterLens, .hole loan.target, found, hole, rfl⟩, framed.1, ?_, framed.2, mass⟩
  · simp [Store.moveLoan, origin, live, located, selected, ready.empty, after]
  · rintro ⟨other, queried, resident, otherOrigin, queriedAt, residentAt, isReady⟩
    have sameOrigin : after.loans[identity]? = some loan := origin
    cases Option.some.inj (sameOrigin.symm.trans otherOrigin)
    cases Option.some.inj (found.symm.trans queriedAt)
    cases Option.some.inj (hole.symm.trans residentAt)
    exact isReady

structure WriteLoanReady {n : Nat} (store : Store n Atom) (signature : Signature) (identity : Nat) : Prop where
  hole : ∃ loan lens, store.loans[identity]? = some loan ∧ store.find loan.referent loan.target = some lens ∧
    lens.selected = some (.hole loan.target)
  resident : ∃ value, store.temp = some value
  typed : ∀ loan value, store.loans[identity]? = some loan → store.temp = some value →
    value.layout (Atom.kind signature) = loan.target ∧ value.ready
  permission : ∀ loan, store.loans[identity]? = some loan → store.Permitted (some identity) .unique loan.referent

theorem WriteLoanReady.progress {n : Nat} {store : Store n Atom} {signature : Signature} {identity : Nat}
    (valid : store.BorrowInvariant signature) (ready : WriteLoanReady store signature identity) :
    ∃ after, store.writeLoan identity = some after ∧ after.temp = none ∧
      after.BorrowInvariant signature ∧ after.LoanReady identity ∧
      (∀ authority mode address, after.Permitted authority mode address ↔ store.Permitted authority mode address) ∧
      ∀ leaf shell, after.mass leaf shell = store.mass leaf shell := by
  obtain ⟨loan, lens, origin, focused, hole⟩ := ready.hole
  obtain ⟨value, resident⟩ := ready.resident
  obtain ⟨typed, initialized⟩ := ready.typed loan value origin resident
  obtain ⟨slots, live, located⟩ := Option.bind_eq_some_iff.mp focused
  let after := store.replaceLoan loan slots lens value none
  have framed := valid.replaceLoan (ready.permission loan origin) live located (by simp [hole, Tree.layout])
    value typed none (by intro leaf shell; simp [hole, resident, cellMass, Tree.mass])
  obtain ⟨result, found, selected, _⟩ := store.replaceLoan_find live located value none
  refine ⟨after, ?_, rfl, framed.1, ⟨loan, result, value, origin, found, selected, initialized⟩, framed.2, ?_⟩
  · simp [Store.writeLoan, origin, live, located, resident, hole, vacant, after]
  · intro leaf shell
    have mass := store.replaceLoan_mass live located value none leaf shell
    simpa [after, hole, resident, cellMass, Tree.mass] using mass


end OwnershipMir
