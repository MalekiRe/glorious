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
    have unchanged := focus_rebuild_layout kind _ _ writing (some replacement)
      (by intro shape same; simpa only [same, Option.getD_some] using replacementType.trans selected.symm) original rfl
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


/-- Fully initialized replacement may change payloads and owner identities,
but preserves the exact typing of every physical region. Temporary holes do
not satisfy this theorem's readiness premises. -/
theorem Store.replaceLoan_regionKinds {n : Nat} {store : Store n Atom} {signature : Signature}
    {loan : Loan n} {slots : Region n Atom} {lens : Lens Atom} {original value : Value}
    (live : store.region loan.referent.region = some slots)
    (focused : (loan.referent.place loan.target).find slots = some lens)
    (resident : lens.selected = some original) (oldReady : original.ready) (newReady : value.ready)
    (sameLayout : value.layout (Atom.kind signature) = original.layout (Atom.kind signature)) (temp : Cell Atom) :
    ∀ region, (store.replaceLoan loan slots lens value temp).regionKinds signature region =
      store.regionKinds signature region := by
  have classified := Tree.ready_map_eq_of_layout_eq (Atom.kind signature) newReady oldReady sameLayout
  have rebuilt := focus_rebuild_map_congr (Atom.kind signature) focused
    (first := some value) (second := lens.selected) (by simp [cellMap, resident, classified])
  rw [focus_rebuild _ _ _ _ focused] at rebuilt
  intro region
  by_cases sameRegion : region = loan.referent.region
  · subst region
    unfold Store.regionKinds Store.replaceLoan
    rw [Store.replace_same (Store.region_bound live), live]
    apply congrArg some
    funext root
    by_cases sameRoot : root = loan.referent.root
    · subst root
      simp only [Place.write, Address.place, update_same]
      exact rebuilt
    · simp [Place.write, Address.place, update, sameRoot]
  · unfold Store.regionKinds Store.replaceLoan
    rw [Store.replace_other _ _ _ _ _ sameRegion]


theorem Store.Permitted.owner_disjoint {n : Nat} {store : Store n Atom} {address : Address n}
    (permission : store.Permitted none .unique address) {identity : Nat} {loan : Loan n}
    (origin : store.loans[identity]? = some loan) (active : store.Active identity) :
    ¬ address.Overlaps loan.referent := by
  intro overlap
  rcases permission.2 identity loan origin active overlap with shared | ⟨parent, impossible, _⟩
  · cases shared.1
  · cases impossible

theorem Store.find_write_disjoint {n : Nat} {store : Store n Atom} {region : Nat}
    {place : Place n} {slots : Region n Atom} {write read : Lens Atom} {address : Address n} {layout : Layout}
    (live : store.region region = some slots) (writing : place.find slots = some write)
    (reading : store.find address layout = some read)
    (apart : ¬ (Address.mk region place.root place.path).Overlaps address) (value temp : Cell Atom) :
    ∃ after, (store.replace region (place.write slots write value) temp).find address layout = some after ∧
      after.selected = read.selected := by
  obtain ⟨roots, originalLive, queried⟩ := Option.bind_eq_some_iff.mp reading
  by_cases sameRegion : address.region = region
  · have sameRoots := Option.some.inj ((sameRegion ▸ originalLive).symm.trans live)
    subst roots
    by_cases sameRoot : address.root = place.root
    · have paths : ¬ place.path.IsPrefix address.path ∧ ¬ address.path.IsPrefix place.path :=
        ⟨fun nested => apart (Or.inr ⟨sameRegion, sameRoot, nested⟩),
         fun nested => apart (Or.inl ⟨sameRegion.symm, sameRoot.symm, nested⟩)⟩
      have focused : focus address.path layout (slots place.root) = some read := by
        simpa only [Place.find, Address.place, sameRoot] using queried
      obtain ⟨after, found, selected⟩ := focus_disjoint writing focused paths value
      refine ⟨after, ?_, selected⟩
      unfold Store.find
      rw [sameRegion, Store.replace_same (Store.region_bound live)]
      simpa [Place.find, Place.write, Address.place, sameRoot] using found
    · refine ⟨read, ?_, rfl⟩
      unfold Store.find
      rw [sameRegion, Store.replace_same (Store.region_bound live)]
      simpa [Place.find, Place.write, Address.place, update, sameRoot] using queried
  · refine ⟨read, ?_, rfl⟩
    unfold Store.find
    rw [Store.replace_other _ _ _ _ _ sameRegion, originalLive]
    exact queried

/-- One owner-access permission frames live loans across actual take/put
updates, including whole-root removal. It permits disjoint borrowed fields
rather than banning all loans in the updated root. -/
theorem Store.Referent.owner_write {n : Nat} {store : Store n Atom} {signature : Signature}
    {region : Nat} {place : Place n} {slots : Region n Atom} {lens : Lens Atom}
    {identity : Nat} {loan : Loan n} (referent : store.Referent signature loan)
    (permission : store.Permitted none .unique ⟨region, place.root, place.path⟩)
    (origin : store.loans[identity]? = some loan) (active : store.Active identity)
    (live : store.region region = some slots) (writing : place.find slots = some lens) (value temp : Cell Atom) :
    (store.replace region (place.write slots lens value) temp).Referent signature loan := by
  obtain ⟨read, original, queried, selected, typed⟩ := referent
  obtain ⟨after, found, unchanged⟩ := store.find_write_disjoint live writing queried
    (permission.owner_disjoint origin active) value temp
  exact ⟨after, original, found, unchanged.trans selected, typed⟩

/-- Ordinary owner accesses use the same pre-state permission relation as
borrowing and dereference. This is not yet derived by shape-only admission. -/
def Op.OwnerPermitted {n : Nat} (store : Store n Atom) (region : Nat) : Op n → Prop
  | .take place _ | .put place => store.Permitted none .unique ⟨region, place.root, place.path⟩
  | .copy place => store.Permitted none .shared ⟨region, place.root, place.path⟩
  | .drop => True

theorem Op.Effect.preserves_referent {n : Nat} {store : Store n Atom} {signature : Signature}
    {region : Nat} {slots : Region n Atom} {op : Op n} {after : State n}
    (effect : op.Effect ⟨slots, store.temp⟩ after) (permission : op.OwnerPermitted store region)
    (live : store.region region = some slots) {identity : Nat} {loan : Loan n}
    (origin : store.loans[identity]? = some loan) (active : store.Active identity)
    (referent : store.Referent signature loan) :
    (store.replace region after.slots after.temp).Referent signature loan := by
  have unchanged := congrArg (fun result : Store n Atom => result.regions) (Store.replace_self live)
  have regions : ∀ temp, (store.replace region slots temp).regions = store.regions := by
    intro temp
    exact unchanged
  cases effect with
  | take found selected extracted empty => exact referent.owner_write permission origin active live found _ _
  | put found selected available => exact referent.owner_write permission origin active live found _ _
  | copy found selected empty =>
    simpa only [Store.Referent, Store.find, Store.region, regions] using referent
  | drop selected =>
    simpa only [Store.Referent, Store.find, Store.region, regions] using referent


theorem Extract.atom_mass {mode : Extract} {value result : Value}
    (executed : mode.apply value = some result) (leaf : Atom → Nat) :
    result.mass leaf (fun _ => 0) = value.mass leaf (fun _ => 0) := by
  cases mode with
  | whole => cases Option.some.inj executed; rfl
  | deconstruct =>
    cases value <;> simp only [Extract.apply, Option.some.injEq] at executed
    all_goals try contradiction
    subst result
    simp [Tree.mass]

/-- Actual ordinary effects cannot manufacture new resident atoms. Copying
may duplicate an existing shared handle, so this is zero preservation, not a
false universal nonincrease claim. -/
theorem Op.Effect.zero_atom_mass {n : Nat} {store : Store n Atom} {region : Nat}
    {slots : Region n Atom} {op : Op n} {after : State n}
    (effect : op.Effect ⟨slots, store.temp⟩ after) (live : store.region region = some slots)
    (leaf : Atom → Nat) (zero : store.mass leaf (fun _ => 0) = 0) :
    (store.replace region after.slots after.temp).mass leaf (fun _ => 0) = 0 := by
  have across := Store.replace_mass_state live after leaf (fun _ => 0)
  rw [zero] at across
  cases effect with
  | @take _ place mode lens value result found selected extracted empty =>
    dsimp only at *
    have within := place.mass_write ⟨slots, store.temp⟩ lens found none (some result) leaf (fun _ => 0)
    have same := Extract.atom_mass extracted leaf
    dsimp only at within
    simp only [selected, empty, cellMass] at within
    rw [empty] at across
    omega
  | @put _ place lens value found resident available =>
    dsimp only at *
    have within := place.mass_write ⟨slots, store.temp⟩ lens found (some value) none leaf (fun _ => 0)
    have vacant := vacant_mass_zero leaf (fun _ => 0) available
    dsimp only at within
    dsimp only [cellMass] at vacant
    simp only [resident, cellMass] at within
    rw [resident] at across
    omega
  | @copy _ place lens value found selected empty =>
    dsimp only at *
    have copied : value.mass leaf (fun _ => 0) = 0 := by
      apply Tree.mass_zero_of_atoms
      intro atom member
      obtain ⟨whole, stored, inside⟩ := focus_contains found selected member
      have contained : store.Contains atom := Or.inr ⟨region, slots, place.root, whole, live, stored, inside⟩
      have bound := contained.mass_le leaf (fun _ => 0)
      omega
    have same : (State.mk slots (some value)).mass leaf (fun _ => 0) =
        (State.mk slots store.temp).mass leaf (fun _ => 0) := by simp [State.mass, empty, cellMass, copied]
    omega
  | drop resident =>
    dsimp only at *
    have lower : (State.mk slots none).mass leaf (fun _ => 0) ≤
        (State.mk slots store.temp).mass leaf (fun _ => 0) := by simp [State.mass, cellMass]
    omega

theorem Op.Effect.no_new_atoms {n : Nat} {store : Store n Atom} {region : Nat}
    {slots : Region n Atom} {op : Op n} {after : State n}
    (effect : op.Effect ⟨slots, store.temp⟩ after) (live : store.region region = some slots)
    {atom : Atom} (present : (store.replace region after.slots after.temp).Contains atom) : store.Contains atom := by
  classical
  by_cases member : store.Contains atom
  · exact member
  apply False.elim
  have zero : store.mass (fun item => if item = atom then 1 else 0) (fun _ => 0) = 0 := by
    apply Store.mass_zero_of_atoms
    intro item contained
    by_cases same : item = atom
    · subst item; exact False.elim (member contained)
    · exact if_neg same
  have afterZero := effect.zero_atom_mass live _ zero
  have positive := present.mass_le (fun item => if item = atom then 1 else 0) (fun _ => 0)
  rw [afterZero, if_pos rfl] at positive
  omega


theorem Op.Effect.borrow_preservation {n : Nat} {store : Store n Atom} {signature : Signature}
    {region : Nat} {slots : Region n Atom} {op : Op n} {after : State n}
    (effect : op.Effect ⟨slots, store.temp⟩ after) (allowed : effect.ConservationAllowed signature)
    (permission : op.OwnerPermitted store region) (live : store.region region = some slots)
    (valid : store.BorrowInvariant signature) :
    (store.replace region after.slots after.temp).BorrowInvariant signature ∧
      ∀ mode address, store.Permitted none mode address →
        (store.replace region after.slots after.temp).Permitted none mode address := by
  let next := store.replace region after.slots after.temp
  have ancestry := Store.ancestor_iff_of_loans_eq (before := store.replace region after.slots after.temp) (after := store) rfl
  have active : ∀ id, next.Active id → store.Active id := by
    rintro id ⟨handle, ⟨mode, target, member⟩, ancestor⟩
    exact ⟨handle, ⟨mode, target, effect.no_new_atoms live member⟩, (ancestry _ _).mp ancestor⟩
  refine ⟨⟨valid.graph, ?_, ?_, ?_⟩, ?_⟩
  · intro id mode target member
    have oldMember := effect.no_new_atoms live member
    obtain ⟨loan, origin, modeEq, targetEq, referent⟩ := valid.references id mode target oldMember
    exact ⟨loan, origin, modeEq, targetEq, effect.preserves_referent permission live origin
      (Store.hasHandle_active ⟨mode, target, oldMember⟩) referent⟩
  · intro first left second right leftFound leftActive rightFound rightActive overlap
    simpa only [ancestry] using valid.compatible first left second right leftFound (active _ leftActive)
      rightFound (active _ rightActive) overlap
  · intro resource
    have balance := Store.replace_mass_state live after (Atom.weight resource) (fun _ => 0)
    have bound := (effect.conserves allowed).bounded resource
    have unique := valid.unique resource
    change after.mass (Atom.weight resource) (fun _ => 0) ≤
      (State.mk slots store.temp).mass (Atom.weight resource) (fun _ => 0) at bound
    change store.mass (Atom.weight resource) (fun _ => 0) ≤ 1 at unique
    change next.mass (Atom.weight resource) (fun _ => 0) ≤ 1
    dsimp only [next]
    omega
  · intro mode address authorized
    refine ⟨trivial, ?_⟩
    intro id loan origin remaining overlap
    rcases authorized.2 id loan origin (active _ remaining) overlap with shared | ⟨parent, impossible, _⟩
    · exact Or.inl shared
    · cases impossible

/-- Existing shape admission constructs the actual effect and its resource
legality; the same pre-state owner permissions then preserve the complete
physical borrow invariant. Deriving these permissions from source remains a
separate obligation, not a post-state assumption in this theorem. -/
theorem Op.Checked.borrow_progress {n : Nat} {authority : Authority} {signature : Signature}
    {store : Store n Atom} {region : Nat} {slots : Region n Atom} {before after : Context n} {op : Op n}
    (checked : Op.Checked authority before op after) (typed : (State.mk slots store.temp).Typed signature before)
    (live : store.region region = some slots) (valid : store.BorrowInvariant signature)
    (permission : op.OwnerPermitted store region) :
    ∃ result, op.exec ⟨slots, store.temp⟩ = some result ∧ result.Typed signature after ∧
      (store.replace region result.slots result.temp).BorrowInvariant signature ∧
      ∀ mode address, store.Permitted none mode address →
        (store.replace region result.slots result.temp).Permitted none mode address := by
  obtain ⟨result, effect, realized, legal⟩ := checked.realize typed
  obtain ⟨preserved, permissions⟩ := effect.borrow_preservation legal.conservationAllowed permission live valid
  exact ⟨result, effect.exec, realized, preserved, permissions⟩


end OwnershipMir
