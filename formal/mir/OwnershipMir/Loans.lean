import OwnershipMir.Store
import OwnershipMir.Places

namespace OwnershipMir

inductive Tree.Contains {α : Type} (atom : α) : Tree α → Prop where
  | leaf : Contains atom (.leaf atom)
  | left {l r} : Contains atom l → Contains atom (.pair l r)
  | right {l r} : Contains atom r → Contains atom (.pair l r)
  | body {s b} : Contains atom b → Contains atom (.wrap s b)

def Store.Contains {n : Nat} {α : Type} (store : Store n α) (atom : α) : Prop :=
  (∃ value, store.temp = some value ∧ value.Contains atom) ∨
    ∃ region slots root value, store.region region = some slots ∧ slots root = some value ∧ value.Contains atom

def Store.HasHandle {n : Nat} (store : Store n Atom) (identity : Nat) : Prop :=
  ∃ mode target, store.Contains (.reference identity mode target)

/-- Ancestry follows immutable entries of the same store's loan table. -/
inductive Store.Ancestor {n : Nat} (store : Store n Atom) : Nat → Nat → Prop where
  | refl (identity) : Ancestor store identity identity
  | parent {ancestor parent child loan} (found : store.loans[child]? = some loan)
      (link : loan.parent = some parent) (earlier : Ancestor store ancestor parent) :
      Ancestor store ancestor child

/-- A child keeps its ancestors live even after an ancestor handle is gone. -/
def Store.Active {n : Nat} (store : Store n Atom) (identity : Nat) : Prop :=
  ∃ handle, store.HasHandle handle ∧ store.Ancestor identity handle

def BorrowMode.Allows (mode requested : BorrowMode) : Prop :=
  requested = .shared ∨ mode = .unique

def Store.LoanGraph {n : Nat} (store : Store n Atom) : Prop :=
  ∀ (identity : Nat) (loan : Loan n), store.loans[identity]? = some loan → ∀ parent, loan.parent = some parent →
    parent < identity ∧ ∃ origin : Loan n, store.loans[parent]? = some origin ∧
      loan.referent.Within origin.referent ∧ origin.mode.Allows loan.mode

/-- A permission check is entirely pre-state. Shared overlap is allowed;
conflicting active descendants freeze parent access, not parent existence. -/
def Store.Permitted {n : Nat} (store : Store n Atom) (via : Option Nat)
    (requested : BorrowMode) (address : Address n) : Prop :=
  (match via with
    | none => True
    | some identity => ∃ loan, store.loans[identity]? = some loan ∧ store.HasHandle identity ∧
        address.Within loan.referent ∧ loan.mode.Allows requested) ∧
  ∀ identity loan, store.loans[identity]? = some loan → store.Active identity →
    address.Overlaps loan.referent →
      (requested = .shared ∧ loan.mode = .shared) ∨
        ∃ parent, via = some parent ∧ store.Ancestor identity parent

def Address.place {n : Nat} (address : Address n) (layout : Layout) : Place n :=
  ⟨address.root, address.path, layout⟩

/-- Resolve through the existing focus. No independent referent traversal. -/
def Store.find {n : Nat} {α : Type} (store : Store n α) (address : Address n)
    (layout : Layout) : Option (Lens α) := do
  let slots ← store.region address.region
  (address.place layout).find slots

def Store.Referent {n : Nat} (store : Store n Atom) (signature : Signature) (loan : Loan n) : Prop :=
  ∃ lens value, store.find loan.referent loan.target = some lens ∧ lens.selected = some value ∧
    value.layout (Atom.kind signature) = loan.target

/-- Holes preserve layout but do not permit moving or ending their handle. -/
def Store.LoanReady {n : Nat} (store : Store n Atom) (identity : Nat) : Prop :=
  ∃ loan lens value, store.loans[identity]? = some loan ∧
    store.find loan.referent loan.target = some lens ∧ lens.selected = some value ∧ value.ready

def Store.ReferencesValid {n : Nat} (store : Store n Atom) (signature : Signature) : Prop :=
  ∀ identity mode target, store.Contains (.reference identity mode target) →
    ∃ loan, store.loans[identity]? = some loan ∧ loan.mode = mode ∧ loan.target = target ∧
      store.Referent signature loan

def Store.LoanCompatible {n : Nat} (store : Store n Atom) : Prop :=
  ∀ first left second right,
    store.loans[first]? = some left → store.Active first →
    store.loans[second]? = some right → store.Active second → left.referent.Overlaps right.referent →
      (left.mode = .shared ∧ right.mode = .shared) ∨
        store.Ancestor first second ∨ store.Ancestor second first

/-- Issuance appends one immutable origin and installs the actual fresh handle. -/
def Store.issue {n : Nat} (store : Store n Atom) (loan : Loan n) : Store n Atom :=
  {store with loans := store.loans ++ [loan], temp := some (.leaf (.reference store.loans.length loan.mode loan.target))}

/-- Raw borrowing locates a resident and requires a vacant transfer register.
Permissions and target typing are admission obligations, not execution guards. -/
def Store.borrow {n : Nat} (store : Store n Atom) (loan : Loan n) : Option (Store n Atom) := do
  let lens ← store.find loan.referent loan.target
  let _ ← lens.selected
  match store.temp with
  | none => some (store.issue loan)
  | some _ => none

structure BorrowReady {n : Nat} (store : Store n Atom) (signature : Signature) (loan : Loan n) : Prop where
  empty : store.temp = none
  referent : store.Referent signature loan
  ready : ∀ lens value, store.find loan.referent loan.target = some lens → lens.selected = some value → value.ready
  permission : store.Permitted loan.parent loan.mode loan.referent

@[simp] theorem Store.issue_region {n : Nat} (store : Store n Atom) (loan : Loan n) (region : Nat) :
    (store.issue loan).region region = store.region region := rfl

@[simp] theorem Store.issue_fresh {n : Nat} (store : Store n Atom) (loan : Loan n) :
    (store.issue loan).loans[store.loans.length]? = some loan := by simp [issue]

theorem Store.issue_old {n : Nat} {store : Store n Atom} {identity : Nat}
    (bound : identity < store.loans.length) (loan : Loan n) :
    (store.issue loan).loans[identity]? = store.loans[identity]? := by
  simp [issue, List.getElem?_append_left bound]

theorem Store.Ancestor.trans {n : Nat} {store : Store n Atom} {first middle last : Nat}
    (left : store.Ancestor first middle) (right : store.Ancestor middle last) : store.Ancestor first last := by
  induction right with
  | refl => exact left
  | parent found link earlier ih => exact .parent found link ih

theorem Store.Ancestor.le {n : Nat} {store : Store n Atom} (graph : store.LoanGraph)
    {first last : Nat} (ancestor : store.Ancestor first last) : first ≤ last := by
  induction ancestor with
  | refl => exact Nat.le_refl _
  | parent found link earlier ih => exact Nat.le_trans ih (Nat.le_of_lt (graph _ _ found _ link).1)

theorem Store.hasHandle_active {n : Nat} {store : Store n Atom} {identity : Nat}
    (handle : store.HasHandle identity) : store.Active identity := ⟨identity, handle, .refl _⟩

theorem Store.Permitted.parent_before {n : Nat} {store : Store n Atom} {loan : Loan n}
    (permission : store.Permitted loan.parent loan.mode loan.referent) {parent : Nat}
    (link : loan.parent = some parent) : parent < store.loans.length := by
  have source := permission.1
  rw [link] at source
  obtain ⟨origin, found, _⟩ := source
  exact List.getElem?_eq_some_iff.mp found |>.1

theorem Store.issue_graph {n : Nat} {store : Store n Atom} (graph : store.LoanGraph) (loan : Loan n)
    (permission : store.Permitted loan.parent loan.mode loan.referent) : (store.issue loan).LoanGraph := by
  intro identity actual found parent link
  have bound : identity < store.loans.length + 1 := by
    simpa [issue] using (List.getElem?_eq_some_iff.mp found).1
  by_cases fresh : identity = store.loans.length
  · subst identity
    cases Option.some.inj ((store.issue_fresh loan).symm.trans found)
    have source := permission.1
    rw [link] at source
    obtain ⟨origin, selected, active, inside, mode⟩ := source
    have older := permission.parent_before link
    exact ⟨older, origin, (store.issue_old older loan).trans selected, inside, mode⟩
  · have older : identity < store.loans.length := by omega
    have selected := (store.issue_old older loan).symm.trans found
    obtain ⟨parentBound, origin, originFound, inside, mode⟩ := graph identity actual selected parent link
    exact ⟨parentBound, origin, (store.issue_old (Nat.lt_trans parentBound older) loan).trans originFound, inside, mode⟩

theorem BorrowReady.progress {n : Nat} {store : Store n Atom} {signature : Signature} {loan : Loan n}
    (ready : BorrowReady store signature loan) : store.borrow loan = some (store.issue loan) := by
  obtain ⟨lens, value, found, resident, _⟩ := ready.referent
  simp [Store.borrow, found, resident, ready.empty]

theorem Store.ReferencesValid.handle_bound {n : Nat} {store : Store n Atom} {signature : Signature}
    (valid : store.ReferencesValid signature) {identity : Nat} (handle : store.HasHandle identity) :
    identity < store.loans.length := by
  obtain ⟨mode, target, contains⟩ := handle
  obtain ⟨loan, found, _⟩ := valid identity mode target contains
  exact (List.getElem?_eq_some_iff.mp found).1

theorem Store.Contains.issue_iff {n : Nat} {store : Store n Atom} (loan : Loan n)
    (empty : store.temp = none) (atom : Atom) :
    (store.issue loan).Contains atom ↔ store.Contains atom ∨ atom = .reference store.loans.length loan.mode loan.target := by
  constructor
  · rintro (⟨value, stored, inside⟩ | ⟨region, slots, root, value, live, stored, inside⟩)
    · cases Option.some.inj stored
      cases inside
      exact Or.inr rfl
    · exact Or.inl (Or.inr ⟨region, slots, root, value, live, stored, inside⟩)
  · rintro ((⟨value, stored, inside⟩ | ⟨region, slots, root, value, live, stored, inside⟩) | rfl)
    · rw [empty] at stored; cases stored
    · exact Or.inr ⟨region, slots, root, value, live, stored, inside⟩
    · exact Or.inl ⟨_, rfl, .leaf⟩

theorem Store.HasHandle.issue_iff {n : Nat} {store : Store n Atom} (loan : Loan n)
    (empty : store.temp = none) (identity : Nat) :
    (store.issue loan).HasHandle identity ↔ store.HasHandle identity ∨ identity = store.loans.length := by
  constructor
  · rintro ⟨mode, target, contains⟩
    rcases (Store.Contains.issue_iff loan empty _).mp contains with old | same
    · exact Or.inl ⟨mode, target, old⟩
    · cases same; exact Or.inr rfl
  · rintro (⟨mode, target, old⟩ | rfl)
    · exact ⟨mode, target, (Store.Contains.issue_iff loan empty _).mpr (Or.inl old)⟩
    · exact ⟨loan.mode, loan.target, (Store.Contains.issue_iff loan empty _).mpr (Or.inr rfl)⟩

theorem Store.Ancestor.issue {n : Nat} {store : Store n Atom} {first last : Nat}
    (ancestor : store.Ancestor first last) (loan : Loan n) : (store.issue loan).Ancestor first last := by
  induction ancestor with
  | refl => exact .refl _
  | parent found link earlier ih =>
    exact .parent ((store.issue_old (List.getElem?_eq_some_iff.mp found).1 loan).trans found) link ih

theorem Store.Ancestor.before_issue {n : Nat} {store : Store n Atom} {loan : Loan n}
    (graph : (store.issue loan).LoanGraph) {first last : Nat}
    (ancestor : (store.issue loan).Ancestor first last) (bound : last < store.loans.length) :
    store.Ancestor first last := by
  induction ancestor with
  | refl => exact .refl _
  | parent found link earlier ih =>
    have smaller := (graph _ _ found _ link).1
    exact .parent ((store.issue_old bound loan).symm.trans found) link (ih (Nat.lt_trans smaller bound))

theorem Store.Active.issue_iff {n : Nat} {store : Store n Atom} {signature : Signature}
    (valid : store.ReferencesValid signature) (graph : store.LoanGraph) (loan : Loan n)
    (empty : store.temp = none) (permission : store.Permitted loan.parent loan.mode loan.referent) (identity : Nat) :
    (store.issue loan).Active identity ↔ store.Active identity ∨ identity = store.loans.length := by
  have newGraph := store.issue_graph graph loan permission
  constructor
  · rintro ⟨handle, contains, ancestor⟩
    rcases (Store.HasHandle.issue_iff loan empty handle).mp contains with old | rfl
    · exact Or.inl ⟨handle, old, ancestor.before_issue newGraph (valid.handle_bound old)⟩
    · cases ancestor with
      | refl => exact Or.inr rfl
      | parent found link earlier =>
        cases Option.some.inj ((store.issue_fresh loan).symm.trans found)
        have oldAncestor := earlier.before_issue newGraph (permission.parent_before link)
        have source := permission.1
        rw [link] at source
        obtain ⟨_, _, witness, _⟩ := source
        exact Or.inl ⟨_, witness, oldAncestor⟩
  · rintro (⟨root, resident, ancestor⟩ | rfl)
    · exact ⟨root, (Store.HasHandle.issue_iff loan empty root).mpr (Or.inl resident), ancestor.issue loan⟩
    · exact Store.hasHandle_active ((Store.HasHandle.issue_iff loan empty _).mpr (Or.inr rfl))

theorem Store.issue_references {n : Nat} {store : Store n Atom} {signature : Signature}
    (valid : store.ReferencesValid signature) (loan : Loan n) (empty : store.temp = none)
    (referent : store.Referent signature loan) : (store.issue loan).ReferencesValid signature := by
  intro identity mode target contains
  rcases (Store.Contains.issue_iff loan empty _).mp contains with old | same
  · obtain ⟨origin, found, modeEq, targetEq, lens, value, focused, resident, typed⟩ := valid identity mode target old
    exact ⟨origin, (store.issue_old (List.getElem?_eq_some_iff.mp found).1 loan).trans found,
      modeEq, targetEq, lens, value, focused, resident, typed⟩
  · cases same
    exact ⟨loan, store.issue_fresh loan, rfl, rfl, referent⟩

theorem Address.Overlaps.symm {n : Nat} {first last : Address n} (overlap : first.Overlaps last) : last.Overlaps first :=
  Or.symm overlap

theorem Store.Active.bound {n : Nat} {store : Store n Atom} {signature : Signature}
    (valid : store.ReferencesValid signature) (graph : store.LoanGraph) {identity : Nat}
    (active : store.Active identity) : identity < store.loans.length := by
  obtain ⟨handle, resident, ancestor⟩ := active
  exact Nat.lt_of_le_of_lt (ancestor.le graph) (valid.handle_bound resident)


theorem Store.issue_compatible {n : Nat} {store : Store n Atom} {signature : Signature}
    (valid : store.ReferencesValid signature) (graph : store.LoanGraph) (compatible : store.LoanCompatible)
    (loan : Loan n) (empty : store.temp = none) (permission : store.Permitted loan.parent loan.mode loan.referent) :
    (store.issue loan).LoanCompatible := by
  have newOld : ∀ identity origin, store.loans[identity]? = some origin → store.Active identity →
      loan.referent.Overlaps origin.referent →
      (loan.mode = .shared ∧ origin.mode = .shared) ∨ (store.issue loan).Ancestor identity store.loans.length := by
    intro identity origin found active overlaps
    rcases permission.2 identity origin found active overlaps with shared | ⟨parent, link, ancestor⟩
    · exact Or.inl shared
    · exact Or.inr (.parent (store.issue_fresh loan) link (ancestor.issue loan))
  intro first left second right leftFound leftActive rightFound rightActive overlap
  rcases (Store.Active.issue_iff valid graph loan empty permission first).mp leftActive with leftOld | leftFresh
  · have leftBound := leftOld.bound valid graph
    have leftSelected := (store.issue_old leftBound loan).symm.trans leftFound
    rcases (Store.Active.issue_iff valid graph loan empty permission second).mp rightActive with rightOld | rightFresh
    · have rightBound := rightOld.bound valid graph
      have rightSelected := (store.issue_old rightBound loan).symm.trans rightFound
      rcases compatible first left second right leftSelected leftOld rightSelected rightOld overlap with shared | forward | reverse
      · exact Or.inl shared
      · exact Or.inr (Or.inl (forward.issue loan))
      · exact Or.inr (Or.inr (reverse.issue loan))
    · subst second
      cases Option.some.inj ((store.issue_fresh loan).symm.trans rightFound)
      rcases newOld first left leftSelected leftOld overlap.symm with shared | ancestor
      · exact Or.inl shared.symm
      · exact Or.inr (Or.inl ancestor)
  · subst first
    cases Option.some.inj ((store.issue_fresh loan).symm.trans leftFound)
    rcases (Store.Active.issue_iff valid graph loan empty permission second).mp rightActive with rightOld | rightFresh
    · have rightBound := rightOld.bound valid graph
      have rightSelected := (store.issue_old rightBound loan).symm.trans rightFound
      rcases newOld second right rightSelected rightOld overlap with shared | ancestor
      · exact Or.inl shared
      · exact Or.inr (Or.inr ancestor)
    · subst second; exact Or.inr (Or.inl (.refl _))


theorem Tree.mass_zero_of_atoms {α : Type} (value : Tree α) (leaf : α → Nat)
    (zero : ∀ atom, value.Contains atom → leaf atom = 0) : value.mass leaf (fun _ => 0) = 0 := by
  induction value with
  | hole => rfl
  | nil => rfl
  | leaf atom => exact zero atom .leaf
  | pair left right leftIH rightIH =>
    simp only [Tree.mass, leftIH (fun atom inside => zero atom (.left inside)),
      rightIH (fun atom inside => zero atom (.right inside)), Nat.add_zero]
  | wrap shell body ih => simpa only [Tree.mass, Nat.zero_add] using ih (fun atom inside => zero atom (.body inside))

theorem Store.mass_zero_of_atoms {n : Nat} {store : Store n Atom} (leaf : Atom → Nat)
    (zero : ∀ atom, store.Contains atom → leaf atom = 0) : store.mass leaf (fun _ => 0) = 0 := by
  have register : cellMass leaf (fun _ => 0) store.temp = 0 := by
    cases found : store.temp with
    | none => rfl
    | some value => exact value.mass_zero_of_atoms leaf (fun atom inside => zero atom (Or.inl ⟨value, found, inside⟩))
  have totalZero : ∀ {m : Nat} (values : Fin m → Nat), (∀ i, values i = 0) → total values = 0 := by
    intro m
    induction m with
    | zero => intro values allZero; rfl
    | succ m ih => intro values allZero; rw [total, ih _ (fun i => allZero i.succ), allZero, Nat.add_zero]
  have regions : ∀ (region : Option (Region n Atom)), region ∈ store.regions →
      (match region with | none => 0 | some slots => total (n := n) (fun i => cellMass leaf (fun _ => 0) (slots i))) = 0 := by
    intro region member
    cases region with
    | none => rfl
    | some slots =>
      obtain ⟨identity, found⟩ := List.mem_iff_getElem?.mp member
      have live : store.region identity = some slots := by simp [Store.region, found]
      apply totalZero
      intro root
      cases resident : slots root with
      | none => rfl
      | some value => exact value.mass_zero_of_atoms leaf (fun atom inside => zero atom (Or.inr ⟨identity, slots, root, value, live, resident, inside⟩))
  have sumZero : ∀ {α : Type} (items : List α) (measure : α → Nat),
      (∀ item ∈ items, measure item = 0) → (items.map measure).sum = 0 := by
    intro α items measure
    induction items with
    | nil => intro allZero; rfl
    | cons head tail ih =>
      intro allZero
      simp only [List.map_cons, List.sum_cons, allZero head (List.mem_cons_self),
        ih (fun item member => allZero item (List.mem_cons_of_mem _ member)), Nat.add_zero]
  unfold Store.mass
  rw [register, Nat.add_zero]
  apply sumZero
  intro region member
  cases region with
  | none => rfl
  | some slots => exact regions (some slots) member

theorem Store.ReferencesValid.fresh_zero {n : Nat} {store : Store n Atom} {signature : Signature}
    (valid : store.ReferencesValid signature) : store.count (.loan store.loans.length) = 0 := by
  apply Store.mass_zero_of_atoms
  intro atom contains
  cases atom with
  | data => rfl
  | owner => rfl
  | reference identity mode target =>
    have bound := valid.handle_bound ⟨mode, target, contains⟩
    cases mode with
    | shared => rfl
    | unique => simp [Atom.weight, Nat.ne_of_gt bound]

theorem Store.issue_mass {n : Nat} {store : Store n Atom} (loan : Loan n) (empty : store.temp = none)
    (leaf : Atom → Nat) (shell : Shell → Nat) :
    (store.issue loan).mass leaf shell = store.mass leaf shell + leaf (.reference store.loans.length loan.mode loan.target) := by
  simp [issue, mass, cellMass, Tree.mass, empty]

theorem Store.issue_unique {n : Nat} {store : Store n Atom} {signature : Signature}
    (valid : store.ReferencesValid signature) (unique : store.Unique) (loan : Loan n) (empty : store.temp = none) :
    (store.issue loan).Unique := by
  intro identity
  change (store.issue loan).mass _ _ ≤ 1
  rw [store.issue_mass loan empty]
  cases loan.mode with
  | shared => exact unique identity
  | unique =>
    by_cases same : identity = .loan store.loans.length
    · subst identity
      have fresh := valid.fresh_zero
      change store.mass (Atom.weight (.loan store.loans.length)) (fun _ => 0) = 0 at fresh
      rw [fresh]
      simp [Atom.weight]
    · simpa only [Store.count, Atom.weight, if_neg same, Nat.add_zero] using unique identity

/-- This is the runtime loan invariant; source admission must establish and
preserve it alongside shape typing, not replace it with a handle annotation. -/
structure Store.BorrowInvariant {n : Nat} (store : Store n Atom) (signature : Signature) : Prop where
  graph : store.LoanGraph
  references : store.ReferencesValid signature
  compatible : store.LoanCompatible
  unique : store.Unique

/-- Actual issuance, initialization, freshness, and the complete loan invariant
are derived from before-state obligations. No successful run or post-state
permission is an admission premise. -/
theorem BorrowReady.sound {n : Nat} {store : Store n Atom} {signature : Signature} {loan : Loan n}
    (valid : store.BorrowInvariant signature) (ready : BorrowReady store signature loan) :
    ∃ after, store.borrow loan = some after ∧ after.BorrowInvariant signature ∧
      after.loans[store.loans.length]? = some loan ∧ after.LoanReady store.loans.length ∧
      after.temp = some (.leaf (.reference store.loans.length loan.mode loan.target)) := by
  refine ⟨store.issue loan, ready.progress, ⟨store.issue_graph valid.graph loan ready.permission,
    store.issue_references valid.references loan ready.empty ready.referent,
    store.issue_compatible valid.references valid.graph valid.compatible loan ready.empty ready.permission,
    store.issue_unique valid.references valid.unique loan ready.empty⟩, store.issue_fresh loan, ?_, rfl⟩
  obtain ⟨lens, value, found, resident, typed⟩ := ready.referent
  exact ⟨loan, lens, value, store.issue_fresh loan, found, resident, ready.ready lens value found resident⟩


theorem Address.within_refl {n : Nat} (address : Address n) : address.Within address :=
  ⟨rfl, rfl, ⟨[], by simp⟩⟩

theorem BorrowReady.parent_suspended {n : Nat} {store : Store n Atom} {signature : Signature} {loan : Loan n}
    (valid : store.BorrowInvariant signature) (ready : BorrowReady store signature loan) {parent : Nat}
    (link : loan.parent = some parent) (requested : BorrowMode)
    (conflict : requested = .unique ∨ loan.mode = .unique) :
    ¬ (store.issue loan).Permitted (some parent) requested loan.referent := by
  intro permitted
  have active := Store.hasHandle_active ((Store.HasHandle.issue_iff loan ready.empty _).mpr (Or.inr rfl))
  rcases permitted.2 _ loan (store.issue_fresh loan) active (Or.inl loan.referent.within_refl) with
    shared | ⟨ancestor, same, older⟩
  · rcases conflict with requestedUnique | loanUnique
    · cases requestedUnique.symm.trans shared.1
    · cases loanUnique.symm.trans shared.2
  · cases Option.some.inj same
    have parentBound := ready.permission.parent_before link
    have impossible := older.le (store.issue_graph valid.graph loan ready.permission)
    omega

theorem BorrowReady.owner_excluded {n : Nat} {store : Store n Atom} {signature : Signature} {loan : Loan n}
    (ready : BorrowReady store signature loan) (requested : BorrowMode)
    (conflict : requested = .unique ∨ loan.mode = .unique) :
    ¬ (store.issue loan).Permitted none requested loan.referent := by
  intro permitted
  have active := Store.hasHandle_active ((Store.HasHandle.issue_iff loan ready.empty _).mpr (Or.inr rfl))
  rcases permitted.2 _ loan (store.issue_fresh loan) active (Or.inl loan.referent.within_refl) with
    shared | ⟨ancestor, impossible, _⟩
  · rcases conflict with requestedUnique | loanUnique
    · cases requestedUnique.symm.trans shared.1
    · cases loanUnique.symm.trans shared.2
  · cases impossible

theorem Store.ReferencesValid.referent_live {n : Nat} {store : Store n Atom} {signature : Signature}
    (valid : store.ReferencesValid signature) {identity : Nat} {mode : BorrowMode} {target : Layout}
    (handle : store.Contains (.reference identity mode target)) {loan : Loan n}
    (found : store.loans[identity]? = some loan) : ∃ slots, store.region loan.referent.region = some slots := by
  obtain ⟨actual, selected, _, _, lens, value, focused, _⟩ := valid identity mode target handle
  cases Option.some.inj (found.symm.trans selected)
  obtain ⟨slots, live, _⟩ := Option.bind_eq_some_iff.mp focused
  exact ⟨slots, live⟩

/-- A retained or returned handle into the retired region cannot satisfy the
reference invariant, regardless of the spelling of its declared lifetime. -/
theorem Store.retire_reference_invalid {n : Nat} {store : Store n Atom} {signature : Signature}
    {region identity : Nat} {mode : BorrowMode} {target : Layout} {loan : Loan n}
    (handle : (store.retire region).Contains (.reference identity mode target))
    (found : store.loans[identity]? = some loan) (retiring : loan.referent.region = region) :
    ¬ (store.retire region).ReferencesValid signature := by
  intro valid
  obtain ⟨slots, live⟩ := valid.referent_live handle found
  rw [retiring, Store.retire_same] at live
  cases live


theorem focus_contains {α : Type} {path : List Direction} {layout : Layout} {cell : Cell α}
    {lens : Lens α} {value : Tree α} {atom : α} (found : focus path layout cell = some lens)
    (selected : lens.selected = some value) (contains : value.Contains atom) :
    ∃ whole, cell = some whole ∧ whole.Contains atom := by
  induction path generalizing cell lens with
  | nil => cases Option.some.inj found; exact ⟨value, selected, contains⟩
  | cons direction path ih =>
    cases cell with
    | none => cases direction <;> simp [focus] at found
    | some tree =>
      cases direction <;> cases tree <;> simp only [focus] at found
      all_goals try contradiction
      all_goals obtain ⟨inside, focused, rfl⟩ := Option.map_eq_some_iff.mp found
      · obtain ⟨whole, same, member⟩ := ih focused selected
        cases Option.some.inj same
        exact ⟨_, rfl, .left member⟩
      · obtain ⟨whole, same, member⟩ := ih focused selected
        cases Option.some.inj same
        exact ⟨_, rfl, .right member⟩
      · obtain ⟨whole, same, member⟩ := ih focused selected
        cases Option.some.inj same
        exact ⟨_, rfl, .body member⟩

theorem Store.find_contains {n : Nat} {store : Store n Atom} {address : Address n} {layout : Layout}
    {lens : Lens Atom} {value : Value} {atom : Atom}
    (found : store.find address layout = some lens) (selected : lens.selected = some value)
    (contains : value.Contains atom) : store.Contains atom := by
  obtain ⟨slots, live, focused⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨whole, resident, member⟩ := focus_contains focused selected contains
  exact Or.inr ⟨address.region, slots, address.root, whole, live, resident, member⟩

/-- Dereference selects the immutable origin, then the same physical focus used
by ordinary places. Copy and permission obligations belong to admission. -/
def Store.readLoan {n : Nat} (store : Store n Atom) (identity : Nat) : Option (Store n Atom) := do
  let loan ← store.loans[identity]?
  let lens ← store.find loan.referent loan.target
  let value ← lens.selected
  match store.temp with
  | none => some {store with temp := some value}
  | some _ => none

structure ReadLoanReady {n : Nat} (store : Store n Atom) (signature : Signature) (identity : Nat) : Prop where
  empty : store.temp = none
  handle : store.HasHandle identity
  permission : ∀ loan, store.loans[identity]? = some loan → store.Permitted (some identity) .shared loan.referent
  copyable : ∀ loan lens value, store.loans[identity]? = some loan →
    store.find loan.referent loan.target = some lens → lens.selected = some value → (Value.kind signature value).copyable

/-- Installing an already-resident copy changes multiplicity, but not the set
of resident atoms or the loans kept alive by them. -/
theorem Store.copy_contains_iff {n : Nat} {store : Store n Atom} {value : Value}
    (empty : store.temp = none) (resident : ∀ atom, value.Contains atom → store.Contains atom) (atom : Atom) :
    ({store with temp := some value} : Store n Atom).Contains atom ↔ store.Contains atom := by
  constructor
  · rintro (⟨other, same, member⟩ | member)
    · cases Option.some.inj same; exact resident atom member
    · exact Or.inr member
  · rintro (⟨other, same, member⟩ | member)
    · rw [empty] at same; cases same
    · exact Or.inr member

theorem Store.Ancestor.of_loans_eq {n : Nat} {before after : Store n Atom}
    (same : before.loans = after.loans) {parent child : Nat} (ancestor : before.Ancestor parent child) :
    after.Ancestor parent child := by
  induction ancestor with
  | refl => exact .refl _
  | parent found link earlier ih => exact .parent (same ▸ found) link ih

theorem Store.ancestor_iff_of_loans_eq {n : Nat} {before after : Store n Atom}
    (same : before.loans = after.loans) (parent child : Nat) :
    before.Ancestor parent child ↔ after.Ancestor parent child :=
  ⟨Store.Ancestor.of_loans_eq same, Store.Ancestor.of_loans_eq same.symm⟩


theorem ReadLoanReady.sound {n : Nat} {store : Store n Atom} {signature : Signature} {identity : Nat}
    (valid : store.BorrowInvariant signature) (ready : ReadLoanReady store signature identity) :
    ∃ after loan value, store.readLoan identity = some after ∧ after.BorrowInvariant signature ∧
      store.loans[identity]? = some loan ∧ after.temp = some value ∧
      value.layout (Atom.kind signature) = loan.target ∧ value.ready ∧
      (∀ resource, after.count resource = store.count resource) ∧
      (∀ via mode address, after.Permitted via mode address ↔ store.Permitted via mode address) ∧
      store.Permitted (some identity) .shared loan.referent := by
  obtain ⟨mode, target, handle⟩ := ready.handle
  obtain ⟨loan, selected, _, _, lens, value, focused, resident, typed⟩ := valid.references identity mode target handle
  have copying := ready.copyable loan lens value selected focused resident
  have atoms := Store.copy_contains_iff ready.empty (fun atom member => Store.find_contains focused resident member)
  let after : Store n Atom := {store with temp := some value}
  have handles : ∀ id, after.HasHandle id ↔ store.HasHandle id := by
    intro id; simp only [Store.HasHandle, after, atoms]
  have active : ∀ id, after.Active id ↔ store.Active id := by
    intro id
    simp only [Store.Active, handles, Store.ancestor_iff_of_loans_eq (before := after) (after := store) rfl]
  have counts : ∀ resource, after.count resource = store.count resource := by
    intro resource
    have zero := Value.copyable_zero copying resource
    change _ = store.mass (Atom.weight resource) (fun _ => 0)
    simp only [after, Store.count, Store.mass, cellMass, ready.empty, Nat.add_zero]
    exact Nat.add_eq_left.mpr zero
  have preserved : after.BorrowInvariant signature := by
    refine ⟨valid.graph, ?_, ?_, ?_⟩
    · intro id mode target contains
      obtain ⟨origin, found, modeEq, targetEq, referent⟩ := valid.references id mode target ((atoms _).mp contains)
      exact ⟨origin, found, modeEq, targetEq, referent⟩
    · intro left first right last firstFound firstActive lastFound lastActive overlaps
      simpa only [Store.ancestor_iff_of_loans_eq (before := after) (after := store) rfl] using
        valid.compatible left first right last firstFound ((active _).mp firstActive)
          lastFound ((active _).mp lastActive) overlaps
    · intro resource; rw [counts]; exact valid.unique resource
  refine ⟨after, loan, value, ?_, preserved, selected, rfl, typed, ?_, counts, ?_, ready.permission loan selected⟩
  · simp [Store.readLoan, selected, focused, resident, ready.empty, after]
  · simpa only [Value.kind, Tree.ready_map] using Tree.copyable_ready copying
  · intro via mode address
    simp only [Store.Permitted, handles, active, Store.ancestor_iff_of_loans_eq (before := after) (after := store) rfl]
    rfl


theorem focus_none_selected {α : Type} {path : List Direction} {layout : Layout} {lens : Lens α}
    (found : focus path layout none = some lens) : lens.selected = none := by
  cases path with
  | nil => cases Option.some.inj found; rfl
  | cons direction rest => cases direction <;> simp [focus] at found

theorem Store.Referent.outside_empty {n : Nat} {store : Store n Atom} {signature : Signature}
    {loan : Loan n} (referent : store.Referent signature loan) {region : Nat}
    (empty : store.region region = some (fun _ => none)) : loan.referent.region ≠ region := by
  intro same
  obtain ⟨lens, value, found, selected, _⟩ := referent
  change ((store.region loan.referent.region).bind fun slots => focus loan.referent.path loan.target (slots loan.referent.root)) = some lens at found
  rw [same, empty] at found
  have missing := focus_none_selected found
  rw [selected] at missing
  cases missing

theorem Store.retire_empty_contains {n : Nat} {store : Store n Atom} {region : Nat}
    (empty : store.region region = some (fun _ => none)) (atom : Atom) :
    (store.retire region).Contains atom ↔ store.Contains atom := by
  constructor
  · rintro (register | ⟨other, slots, root, value, live, resident, member⟩)
    · exact Or.inl register
    · have different : other ≠ region := by
        intro same; subst other; rw [Store.retire_same] at live; cases live
      exact Or.inr ⟨other, slots, root, value, (store.retire_other region other different).symm.trans live, resident, member⟩
  · rintro (register | ⟨other, slots, root, value, live, resident, member⟩)
    · exact Or.inl register
    · have different : other ≠ region := by
        intro same; subst other
        cases Option.some.inj (empty.symm.trans live)
        cases resident
      exact Or.inr ⟨other, slots, root, value, (store.retire_other region other different).trans live, resident, member⟩

theorem Store.retire_empty_permissions {n : Nat} {store : Store n Atom} {region : Nat}
    (empty : store.region region = some (fun _ => none)) (via : Option Nat) (mode : BorrowMode) (address : Address n) :
    (store.retire region).Permitted via mode address ↔ store.Permitted via mode address := by
  have handles : ∀ identity, (store.retire region).HasHandle identity ↔ store.HasHandle identity := by
    intro identity; simp only [Store.HasHandle, store.retire_empty_contains empty]
  have ancestry := Store.ancestor_iff_of_loans_eq (before := store.retire region) (after := store) rfl
  have active : ∀ identity, (store.retire region).Active identity ↔ store.Active identity := by
    intro identity; simp only [Store.Active, handles, ancestry]
  simp only [Store.Permitted, handles, active, ancestry]
  rfl

/-- Empty retirement needs no assumed future reference validity or separate
escape table: before-state referent validity excludes every surviving handle
into the already-empty region. Cleanup must preserve that validity first. -/
theorem Store.BorrowInvariant.retire_empty {n : Nat} {store : Store n Atom} {signature : Signature}
    (valid : store.BorrowInvariant signature) {region : Nat}
    (empty : store.region region = some (fun _ => none)) : (store.retire region).BorrowInvariant signature := by
  have handles : ∀ identity, (store.retire region).HasHandle identity ↔ store.HasHandle identity := by
    intro identity; simp only [Store.HasHandle, store.retire_empty_contains empty]
  have ancestry := Store.ancestor_iff_of_loans_eq (before := store.retire region) (after := store) rfl
  have active : ∀ identity, (store.retire region).Active identity ↔ store.Active identity := by
    intro identity; simp only [Store.Active, handles, ancestry]
  refine ⟨valid.graph, ?_, ?_, ?_⟩
  · intro identity mode target contains
    obtain ⟨loan, found, modeEq, targetEq, referent⟩ :=
      valid.references identity mode target ((store.retire_empty_contains empty _).mp contains)
    have different := referent.outside_empty empty
    obtain ⟨lens, value, focused, selected, typed⟩ := referent
    refine ⟨loan, found, modeEq, targetEq, lens, value, ?_, selected, typed⟩
    unfold Store.find
    rw [Store.retire_other _ _ _ different]
    exact focused
  · intro left first right last firstFound firstActive lastFound lastActive overlap
    simpa only [ancestry] using valid.compatible left first right last firstFound ((active _).mp firstActive)
      lastFound ((active _).mp lastActive) overlap
  · intro identity
    have conserved := store.retire_mass empty (Atom.weight identity) (fun _ => 0)
    change (store.retire region).mass _ _ ≤ 1
    have bound := valid.unique identity
    change store.mass (Atom.weight identity) (fun _ => 0) ≤ 1 at bound
    omega


theorem Store.clearTemp_contains {n : Nat} {store : Store n Atom} {atom : Atom}
    (contains : ({store with temp := none} : Store n Atom).Contains atom) : store.Contains atom := by
  rcases contains with ⟨value, impossible, _⟩ | resident
  · cases impossible
  · exact Or.inr resident

/-- Last use is physical: an origin remains active exactly when some handle
in surviving region storage keeps it or a descendant alive. Dropping a shared
alias does not end a loan while another alias survives. -/
theorem Store.clearTemp_active_iff {n : Nat} (store : Store n Atom) (identity : Nat) :
    ({store with temp := none} : Store n Atom).Active identity ↔
      ∃ handle mode target region slots root value,
        store.region region = some slots ∧ slots root = some value ∧
        value.Contains (.reference handle mode target) ∧ store.Ancestor identity handle := by
  constructor
  · rintro ⟨handle, ⟨mode, target, contains⟩, ancestor⟩
    rcases contains with ⟨value, impossible, _⟩ | ⟨region, slots, root, value, live, selected, member⟩
    · cases impossible
    · exact ⟨handle, mode, target, region, slots, root, value, live, selected, member,
        ancestor.of_loans_eq (before := {store with temp := none}) (after := store) rfl⟩
  · rintro ⟨handle, mode, target, region, slots, root, value, live, selected, member, ancestor⟩
    exact ⟨handle, ⟨mode, target, Or.inr ⟨region, slots, root, value, live, selected, member⟩⟩,
      ancestor.of_loans_eq (before := store) (after := {store with temp := none}) rfl⟩

theorem Store.BorrowInvariant.clearTemp {n : Nat} {store : Store n Atom} {signature : Signature}
    (valid : store.BorrowInvariant signature) : ({store with temp := none} : Store n Atom).BorrowInvariant signature := by
  let after : Store n Atom := {store with temp := none}
  have active : ∀ identity, after.Active identity → store.Active identity := by
    rintro identity ⟨handle, ⟨mode, target, contains⟩, ancestor⟩
    exact ⟨handle, ⟨mode, target, Store.clearTemp_contains contains⟩, ancestor.of_loans_eq (before := after) (after := store) rfl⟩
  change after.BorrowInvariant signature
  refine ⟨valid.graph, ?_, ?_, ?_⟩
  · intro identity mode target contains
    exact valid.references identity mode target (Store.clearTemp_contains contains)
  · intro left first right last firstFound firstActive lastFound lastActive overlaps
    rcases valid.compatible left first right last firstFound (active _ firstActive)
      lastFound (active _ lastActive) overlaps with shared | forward | reverse
    · exact Or.inl shared
    · exact Or.inr (Or.inl (forward.of_loans_eq (before := store) (after := after) rfl))
    · exact Or.inr (Or.inr (reverse.of_loans_eq (before := store) (after := after) rfl))
  · intro identity
    have bound := valid.unique identity
    change store.mass _ _ ≤ 1 at bound
    change after.mass _ _ ≤ 1
    simp only [after, Store.mass, cellMass, Nat.add_zero] at *
    omega

/-- If no surviving stored handle keeps an overlapping origin alive, ending
the register's handles restores owner access. The premise inspects only the
before-store's region residents and immutable ancestry, not a future permission. -/
theorem Store.clearTemp_owner_permission {n : Nat} {store : Store n Atom} (requested : BorrowMode) (address : Address n)
    (lastUse : ∀ identity loan handle mode target region slots root value,
      store.loans[identity]? = some loan → store.region region = some slots → slots root = some value →
      value.Contains (.reference handle mode target) → store.Ancestor identity handle →
      address.Overlaps loan.referent → requested = .shared ∧ loan.mode = .shared) :
    ({store with temp := none} : Store n Atom).Permitted none requested address := by
  refine ⟨True.intro, ?_⟩
  intro identity loan found active overlap
  obtain ⟨handle, mode, target, region, slots, root, value, live, selected, member, ancestor⟩ :=
    (store.clearTemp_active_iff identity).mp active
  exact Or.inl (lastUse identity loan handle mode target region slots root value found live selected member ancestor overlap)


end OwnershipMir
