import Std

/-! Language-independent mathematical vocabulary. No compiler implementation,
source-library algorithm, or axiom asserting semantic correctness is imported. -/
namespace Glorious.Language

abbrev Identity := Nat

structure DeclId where
  package : Identity
  serial : Identity
  deriving DecidableEq, BEq, Repr, Inhabited

structure ModuleId where
  package : Identity
  path : List String
  deriving DecidableEq, BEq, Repr, Inhabited

structure Span where
  file : Identity
  start : Nat
  stop : Nat
  deriving DecidableEq, BEq, Repr, Inhabited

inductive Access where
  | shared | unique | owned
  deriving DecidableEq, BEq, Repr, Inhabited

inductive Mutability where
  | shared | unique
  deriving DecidableEq, BEq, Repr, Inhabited

inductive Principal where
  | duplicable | affine | exact
  deriving DecidableEq, BEq, Repr, Inhabited

def Principal.Permits : Principal → Nat → Prop
  | .duplicable, _ => True
  | .affine, n => n ≤ 1
  | .exact, n => n = 1

def Principal.Restricts (a b : Principal) : Prop := ∀ n, a.Permits n → b.Permits n
def Principal.MayDiscard (p : Principal) : Prop := p.Permits 0
def Principal.MayCopy (p : Principal) : Prop := p = .duplicable

def Principal.meet : Principal → Principal → Principal
  | .exact, _ | _, .exact => .exact
  | .affine, _ | _, .affine => .affine
  | _, _ => .duplicable

def Principal.fields (ps : List Principal) : Principal := ps.foldr meet .duplicable

theorem Principal.meet_permits (a b : Principal) (n : Nat) :
    (a.meet b).Permits n ↔ a.Permits n ∧ b.Permits n := by
  cases a <;> cases b <;> simp [meet, Permits] <;> omega

theorem Principal.exact_not_discardable : ¬ Principal.exact.MayDiscard := by
  simp [MayDiscard, Permits]

theorem Principal.once_does_not_identify_principal (p : Principal) : p.Permits 1 := by
  cases p <;> simp [Permits]

structure Quantity where
  lower : Nat
  upper : Option Nat
  deriving DecidableEq, BEq, Repr, Inhabited

def Quantity.Contains (q : Quantity) (n : Nat) : Prop :=
  q.lower ≤ n ∧ ∀ maximum, q.upper = some maximum → n ≤ maximum

def Quantity.Valid (q : Quantity) : Prop := ∃ n, q.Contains n
def Quantity.Request (q : Quantity) (p : Principal) : Prop :=
  q.Valid ∧ ∀ n, q.Contains n → p.Permits n

def Quantity.sequence (a b : Quantity) : Quantity :=
  ⟨a.lower + b.lower, match a.upper, b.upper with
    | some x, some y => some (x + y)
    | _, _ => none⟩

def Quantity.alternative (a b : Quantity) : Quantity :=
  ⟨min a.lower b.lower, match a.upper, b.upper with
    | some x, some y => some (max x y)
    | _, _ => none⟩

def Quantity.SurfaceOrdinary (q : Quantity) : Prop :=
  q = ⟨0, none⟩ ∨ q = ⟨0, some 1⟩ ∨ q = ⟨1, some 1⟩

def Quantity.SurfaceResumption (q : Quantity) : Prop :=
  q = ⟨0, some 1⟩ ∨ ∃ n, 0 < n ∧ n < 2^32 ∧ q = ⟨n, some n⟩

theorem Quantity.sequence_contains {a b : Quantity} {m n : Nat}
    (left : a.Contains m) (right : b.Contains n) : (a.sequence b).Contains (m + n) := by
  rcases a with ⟨al, au⟩
  rcases b with ⟨bl, bu⟩
  cases au <;> cases bu <;> simp_all [Contains, sequence] <;> omega

variable {α β : Type}

inductive ListRel (relation : α → β → Prop) : List α → List β → Prop where
  | nil : ListRel relation [] []
  | cons {a b as bs} : relation a b → ListRel relation as bs →
      ListRel relation (a :: as) (b :: bs)

theorem ListRel.length_eq {relation : α → β → Prop} {as : List α} {bs : List β}
    (related : ListRel relation as bs) : as.length = bs.length := by
  induction related with
  | nil => rfl
  | cons _ _ ih => simpa using congrArg Nat.succ ih

theorem ListRel.append {relation : α → β → Prop} {as cs : List α} {bs ds : List β}
    (left : ListRel relation as bs) (right : ListRel relation cs ds) :
    ListRel relation (as ++ cs) (bs ++ ds) := by
  induction left with
  | nil => exact right
  | cons head _ ih => exact .cons head ih

theorem ListRel.functional {α β : Type} {relation : α → β → Prop} {left : List α} {first second : List β}
    (functional : ∀ a b c, relation a b → relation a c → b = c)
    (a : ListRel relation left first) (b : ListRel relation left second) : first = second := by
  induction a generalizing second with
  | nil => cases b; rfl
  | cons head tail ih =>
      cases b with
      | cons other rest => simp only [functional _ _ _ head other,ih rest]

abbrev Table (α : Type) := List (Identity × α)

def Table.get (table : Table α) (key : Identity) : Option α :=
  (table.find? (fun entry => entry.1 == key)).map Prod.snd

def Table.erase (table : Table α) (key : Identity) : Table α :=
  table.filter (fun entry => entry.1 != key)

def Table.set (table : Table α) (key : Identity) (value : α) : Table α :=
  (key, value) :: table.erase key

def Table.Unique (table : Table α) : Prop := (table.map Prod.fst).Nodup

theorem Table.get_set (table : Table α) (key : Identity) (value : α) :
    (table.set key value).get key = some value := by
  simp [set, get]

theorem Table.get_set_other (table : Table α) (key other : Identity) (value : α)
    (different : other ≠ key) : (table.set key value).get other = table.get other := by
  induction table with
  | nil => simp [set, erase, get, Ne.symm different]
  | cons entry rest ih =>
    rcases entry with ⟨id, resident⟩
    by_cases equalKey : id = key
    · subst id
      simpa [set, erase, get, different, Ne.symm different] using ih
    · by_cases equalOther : id = other
      · subst id; simp [set, erase, get, different, Ne.symm different]
      · simpa [set, erase, get, equalKey, equalOther, different, Ne.symm different] using ih

inductive Failure where
  | lexical | syntaxNode | name | ambiguous | privacy | kind | type | coherence
  | unresolved | unavailableBody | unsupportedRepresentation
  | ownership | initialization | borrow | escaping | unsafeContract
  | effect | resumption | tail | target | importContract
  deriving DecidableEq, BEq, Repr, Inhabited

inductive Limit where
  | source | staticProof | normalization | layout | memory | execution
  deriving DecidableEq, BEq, Repr, Inhabited

inductive Fatal where
  | abort | invalidMemory | invalidValue | arithmetic | hostContract | resource | internal
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Missing static evidence and mathematical infinity are different notions. -/
inductive Knowledge (α : Type) where
  | known (value : α)
  | unknown (reason : Failure)

structure TransitionSystem (Event Result : Type) where
  State : Type
  initial : State → Prop
  step : State → Option Event → State → Prop
  final : State → Result → Prop
  invalid : State → Prop

variable {Event Result : Type}

namespace TransitionSystem

inductive Steps (system : TransitionSystem Event Result) :
    system.State → List Event → system.State → Prop where
  | refl {state} : Steps system state [] state
  | silent {a b c trace} : system.step a none b → Steps system b trace c → Steps system a trace c
  | visible {a b c event trace} : system.step a (some event) b → Steps system b trace c →
      Steps system a (event :: trace) c

def Reachable (system : TransitionSystem Event Result) (state : system.State) : Prop :=
  ∃ start trace, system.initial start ∧ system.Steps start trace state

def Prefix (system : TransitionSystem Event Result) (trace : List Event) : Prop :=
  ∃ start finish, system.initial start ∧ system.Steps start trace finish

def Returns (system : TransitionSystem Event Result) (trace : List Event) (result : Result) : Prop :=
  ∃ start finish, system.initial start ∧ system.Steps start trace finish ∧ system.final finish result

def Infinite (system : TransitionSystem Event Result) (events : Nat → Option Event) : Prop :=
  ∃ states : Nat → system.State,
    system.initial (states 0) ∧ ∀ n, system.step (states n) (events n) (states (n + 1))

def Safe (system : TransitionSystem Event Result) : Prop :=
  ∀ state, system.Reachable state → ¬ system.invalid state ∧
    ((∃ result, system.final state result) ∨ ∃ event next, system.step state event next)

theorem Steps.trans {system : TransitionSystem Event Result} {a b c : system.State}
    {left right : List Event} (first : system.Steps a left b) (second : system.Steps b right c) :
    system.Steps a (left ++ right) c := by
  induction first with
  | refl => exact second
  | silent step _ ih => exact .silent step (ih second)
  | visible step _ ih => exact .visible step (ih second)

end TransitionSystem

def SameObservations (left right : Nat → Option Event) : Prop :=
  ∀ trace : List Event,
    (∃ count, (List.range count).filterMap left = trace) ↔
    (∃ count, (List.range count).filterMap right = trace)

structure Preserves (source target : TransitionSystem Event Result) : Prop where
  prefixes : ∀ trace, source.Prefix trace ↔ target.Prefix trace
  results : ∀ trace result, source.Returns trace result ↔ target.Returns trace result
  divergence : ∀ events, source.Infinite events →
    ∃ matching, target.Infinite matching ∧ SameObservations events matching
  noNewDivergence : ∀ events, target.Infinite events →
    ∃ matching, source.Infinite matching ∧ SameObservations matching events
  safety : source.Safe → target.Safe

theorem Preserves.refl (system : TransitionSystem Event Result) : Preserves system system where
  prefixes _ := Iff.rfl
  results _ _ := Iff.rfl
  divergence events h := ⟨events, h, fun _ => Iff.rfl⟩
  noNewDivergence events h := ⟨events, h, fun _ => Iff.rfl⟩
  safety := id

theorem Preserves.trans {a b c : TransitionSystem Event Result}
    (first : Preserves a b) (second : Preserves b c) : Preserves a c where
  prefixes trace := (first.prefixes trace).trans (second.prefixes trace)
  results trace result := (first.results trace result).trans (second.results trace result)
  divergence events h := by
    obtain ⟨middle, run, equal⟩ := first.divergence events h
    obtain ⟨finish, run', equal'⟩ := second.divergence middle run
    exact ⟨finish, run', fun trace => (equal trace).trans (equal' trace)⟩
  noNewDivergence events h := by
    obtain ⟨middle, run, equal⟩ := second.noNewDivergence events h
    obtain ⟨start, run', equal'⟩ := first.noNewDivergence middle run
    exact ⟨start, run', fun trace => (equal' trace).trans (equal trace)⟩
  safety h := second.safety (first.safety h)

end Glorious.Language
