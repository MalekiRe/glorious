import Std

/-! Language-independent mathematical vocabulary. No compiler implementation,
source-library algorithm, or axiom asserting semantic correctness is imported. -/
universe u

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

/-- The full interval of a class, as opposed to an arbitrary request that
the class may satisfy. Logical transport of capability evidence uses this
whole interval so an exact-once request cannot be mistaken for Copy. -/
def Principal.quantity : Principal → Quantity
  | .duplicable => ⟨0,none⟩
  | .affine => ⟨0,some 1⟩
  | .exact => ⟨1,some 1⟩

theorem Principal.quantity_contains (principal : Principal) (n : Nat) :
    principal.quantity.Contains n ↔ principal.Permits n := by
  cases principal <;> simp [Principal.quantity,Quantity.Contains,Principal.Permits] <;> omega

theorem Principal.quantity_valid (principal : Principal) : principal.quantity.Valid :=
  ⟨1,(principal.quantity_contains 1).mpr (Principal.once_does_not_identify_principal principal)⟩

theorem Principal.quantity_request (first last : Principal) :
    first.quantity.Request last ↔ first.Restricts last := by
  constructor
  · intro request n permitted
    exact request.2 n ((first.quantity_contains n).mpr permitted)
  · intro ordered
    exact ⟨first.quantity_valid,fun n contained => ordered n ((first.quantity_contains n).mp contained)⟩

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

theorem ListRel.member_left {α β : Type} {relation : α → β → Prop} {left : List α} {right : List β}
    (related : ListRel relation left right) {value : α} (member : value ∈ left) :
    ∃ result ∈ right, relation value result := by
  induction related with
  | nil => cases member
  | @cons first last left right head _ ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨last,List.mem_cons_self,head⟩
    · obtain ⟨result,present,paired⟩ := ih member
      exact ⟨result,List.mem_cons_of_mem _ present,paired⟩

theorem ListRel.append {relation : α → β → Prop} {as cs : List α} {bs ds : List β}
    (left : ListRel relation as bs) (right : ListRel relation cs ds) :
    ListRel relation (as ++ cs) (bs ++ ds) := by
  induction left with
  | nil => exact right
  | cons head _ ih => exact .cons head ih

theorem ListRel.maps {α β γ : Type} {relation : β → γ → Prop} (values : List α) (left : α → β) (right : α → γ)
    (related : ∀ value ∈ values, relation (left value) (right value)) :
    ListRel relation (values.map left) (values.map right) := by
  induction values with
  | nil => exact .nil
  | cons value values ih =>
      exact .cons (related value (by simp)) (ih (fun member present => related member (by simp [present])))

theorem ListRel.imp {α β : Type} {first second : α → β → Prop} {left : List α} {right : List β}
    (related : ListRel first left right) (implies : ∀ a b, first a b → second a b) :
    ListRel second left right := by
  induction related with
  | nil => exact .nil
  | cons head _ ih => exact .cons (implies _ _ head) ih

theorem ListRel.filter {α β : Type} {relation : α → β → Prop} {left : List α} {right : List β}
    (related : ListRel relation left right) (p : α → Bool) (q : β → Bool)
    (agrees : ∀ a b, relation a b → p a = q b) :
    ListRel relation (left.filter p) (right.filter q) := by
  induction related with
  | nil => exact .nil
  | cons head _ ih =>
    simp only [List.filter_cons,← agrees _ _ head]
    split
    · exact .cons head ih
    · exact ih

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

theorem Table.mem_of_get {α : Type} {table : Table α} {id : Identity} {value : α}
    (found : table.get id = some value) : (id,value) ∈ table := by
  induction table with
  | nil => simp [Table.get] at found
  | cons entry rest ih =>
      rcases entry with ⟨key,resident⟩
      by_cases same : key = id
      · subst key
        have equal : resident = value := by simpa [Table.get] using found
        subst resident
        exact List.mem_cons_self
      · have later : Table.get rest id = some value := by simpa [Table.get,same] using found
        exact List.mem_cons_of_mem _ (ih later)

theorem Table.get_map_values {α β : Type} (table : Table α) (function : α → β) (key : Identity) :
    Table.get (table.map (fun entry => (entry.1,function entry.2))) key = (table.get key).map function := by
  simp [Table.get,Function.comp_def]

theorem List.flatMap_congr_left {α β : Type} {values : List α} {first second : α → List β}
    (agree : ∀ value ∈ values, first value = second value) : values.flatMap first = values.flatMap second := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    simp only [List.flatMap_cons,agree value List.mem_cons_self,
      ih (fun value member => agree value (List.mem_cons_of_mem _ member))]

theorem List.map_mapIdx {α β γ : Type} (f : β → γ) (g : Nat → α → β) (values : List α) :
    (values.mapIdx g).map f = values.mapIdx (fun index value => f (g index value)) := by
  apply List.ext_getElem?
  intro index
  simp only [List.getElem?_map,List.getElem?_mapIdx,Option.map_map,Function.comp_def]

theorem List.mapIdx_map {α β γ : Type} (f : Nat → β → γ) (g : α → β) (values : List α) :
    (values.map g).mapIdx f = values.mapIdx (fun index value => f index (g value)) := by
  apply List.ext_getElem?
  intro index
  simp only [List.getElem?_map,List.getElem?_mapIdx,Option.map_map,Function.comp_def]

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

/-- A finite execution segment with at least one transition. The explicit first
transition distinguishes genuine silent progress from zero-step stuttering. -/
def PositiveSteps (system : TransitionSystem Event Result)
    (start : system.State) (trace : List Event) (finish : system.State) : Prop :=
  ∃ event middle suffix, system.step start event middle ∧ system.Steps middle suffix finish ∧
    trace = event.toList ++ suffix
/-- A weak path is either true stuttering or contains a real transition. -/
theorem Steps.zero_or_positive {system : TransitionSystem Event Result} {start finish : system.State}
    {trace : List Event} (steps : system.Steps start trace finish) :
    (start = finish ∧ trace = []) ∨ system.PositiveSteps start trace finish := by
  cases steps with
  | refl => exact Or.inl ⟨rfl,rfl⟩
  | silent step rest =>
      refine Or.inr ⟨none,_,_,step,rest,?_⟩
      simp
  | visible step rest =>
      refine Or.inr ⟨some _,_,_,step,rest,?_⟩
      simp
/-- Forget the fact that a weak path was known to contain a transition. -/
theorem PositiveSteps.toSteps {system : TransitionSystem Event Result} {start finish : system.State}
    {trace : List Event} (positive : system.PositiveSteps start trace finish) :
    system.Steps start trace finish := by
  rcases positive with ⟨event,middle,suffix,step,rest,traceEq⟩
  cases event with
  | none => simpa [traceEq] using (TransitionSystem.Steps.silent step rest)
  | some event => simpa [traceEq] using (TransitionSystem.Steps.visible step rest)

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

def ObservedPrefix (stream : Nat → Option Event) (count : Nat) : List Event :=
  (List.range count).filterMap stream

theorem ObservedPrefix.succ (stream : Nat → Option Event) (count : Nat) :
    ObservedPrefix stream (count + 1) = ObservedPrefix stream count ++ (stream count).toList := by
  simp [ObservedPrefix,List.range_succ,List.filterMap_append,List.filterMap,Option.toList]
  rfl

theorem ObservedPrefix.eq_of_silent (stream : Nat → Option Event)
    {first last : Nat} (ordered : first ≤ last)
    (silent : ∀ index, first ≤ index → index < last → stream index = none) :
    ObservedPrefix stream last = ObservedPrefix stream first := by
  induction ordered with
  | refl => rfl
  | @step last ordered ih =>
    rw [ObservedPrefix.succ,ih (fun index firstLe hlt => silent index firstLe (by omega))]
    have eventNone := silent last (by omega) (by omega)
    simp [eventNone]

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
/-- A local weak bisimulation contract. Nonempty matches preserve observations
exactly; zero-transition matches are paired with a strict rank decrease on the
side that stutters. Terminal observations may be reached after finite silent
epilogues, and target invalidity reflects to the source. -/

structure WeakRefinement (source target : TransitionSystem Event Result)
    (related : source.State → target.State → Prop) : Type (u + 1) where
  Rank : Type u
  decrease : Rank → Rank → Prop
  wellFounded : WellFounded decrease
  rank : source.State → target.State → Rank
  initialForward : ∀ sourceStart, source.initial sourceStart →
    ∃ targetStart, target.initial targetStart ∧ related sourceStart targetStart
  initialBackward : ∀ targetStart, target.initial targetStart →
    ∃ sourceStart, source.initial sourceStart ∧ related sourceStart targetStart
  forwardStep : ∀ {sourceStart event sourceNext targetStart}, related sourceStart targetStart →
    source.step sourceStart event sourceNext →
      (∃ targetNext, target.PositiveSteps targetStart event.toList targetNext ∧ related sourceNext targetNext) ∨
      (event = none ∧ related sourceNext targetStart ∧ decrease (rank sourceNext targetStart) (rank sourceStart targetStart))
  backwardStep : ∀ {sourceStart targetStart event targetNext}, related sourceStart targetStart →
    target.step targetStart event targetNext →
      (∃ sourceNext, source.PositiveSteps sourceStart event.toList sourceNext ∧ related sourceNext targetNext) ∨
      (event = none ∧ related sourceStart targetNext ∧ decrease (rank sourceStart targetNext) (rank sourceStart targetStart))
  finalForward : ∀ {sourceEnd targetStart result}, related sourceEnd targetStart → source.final sourceEnd result →
    ∃ targetEnd, target.Steps targetStart [] targetEnd ∧ related sourceEnd targetEnd ∧ target.final targetEnd result
  finalBackward : ∀ {sourceStart targetEnd result}, related sourceStart targetEnd → target.final targetEnd result →
    ∃ sourceEnd, source.Steps sourceStart [] sourceEnd ∧ related sourceEnd targetEnd ∧ source.final sourceEnd result
  invalidReflection : ∀ {sourceState targetState}, related sourceState targetState →
    target.invalid targetState → source.invalid sourceState
namespace WeakRefinement

variable {source target : TransitionSystem Event Result}
variable {related : source.State → target.State → Prop}
structure ForwardChunk
    (states : Nat → source.State) (events : Nat → Option Event)
    (startIndex : Nat) (targetStart : target.State) where
  matchedIndex : Nat
  targetEnd : target.State
  targetPath : target.PositiveSteps targetStart (events matchedIndex).toList targetEnd
  endpointRelated : related (states (matchedIndex + 1)) targetEnd
  skippedSilent : ∀ index, startIndex ≤ index → index < matchedIndex → events index = none
  startBound : startIndex ≤ matchedIndex

theorem seekForwardChunk (Rank : Type u) (decrease : Rank → Rank → Prop)
    (wellFounded : WellFounded decrease) (rank : source.State → target.State → Rank)
    (advance : ∀ {a event b c}, related a c → source.step a event b →
      (∃ d, target.PositiveSteps c event.toList d ∧ related b d) ∨
      (event = none ∧ related b c ∧ decrease (rank b c) (rank a c)))
    (states : Nat → source.State) (events : Nat → Option Event)
    (steps : ∀ index, source.step (states index) (events index) (states (index + 1))) :
    ∀ index targetStart, related (states index) targetStart →
      Nonempty (ForwardChunk (related := related) states events index targetStart) := by
  let motive : Rank → Prop := fun measure =>
    ∀ index targetStart, rank (states index) targetStart = measure →
      related (states index) targetStart →
      Nonempty (ForwardChunk (related := related) states events index targetStart)
  have descend : ∀ measure, motive measure := fun measure =>
    wellFounded.induction measure (fun measure ih => by
      intro index targetStart rankEq relation
      rcases advance relation (steps index) with matched | stutter
      · obtain ⟨targetEnd,targetPath,endpointRelated⟩ := matched
        exact ⟨⟨index,targetEnd,targetPath,endpointRelated,
          (by intro k hk hlt; omega),Nat.le_refl _⟩⟩
      · obtain ⟨eventNone,nextRelated,rankDecrease⟩ := stutter
        have nextRank : decrease (rank (states (index + 1)) targetStart) measure := by
          rw [← rankEq]
          exact rankDecrease
        obtain ⟨chunk⟩ := ih (rank (states (index + 1)) targetStart) nextRank
          (index + 1) targetStart rfl nextRelated
        exact ⟨⟨chunk.matchedIndex,chunk.targetEnd,chunk.targetPath,chunk.endpointRelated,
          (by
            intro k hk hlt
            by_cases atStart : k = index
            · subst k; exact eventNone
            · exact chunk.skippedSilent k (by omega) (by omega)),
          Nat.le_trans (Nat.le_succ index) chunk.startBound⟩⟩)
  intro index targetStart relation
  exact descend (rank (states index) targetStart) index targetStart rfl relation

abbrev ChunkBoundary (states : Nat → source.State)
    (related : source.State → target.State → Prop) :=
  Σ index : Nat, { targetState : target.State // related (states index) targetState }

noncomputable def chooseForwardChunk
    {states : Nat → source.State} {events : Nat → Option Event}
    (chunks : ∀ index targetStart, related (states index) targetStart →
      Nonempty (ForwardChunk (related := related) states events index targetStart))
    (boundary : ChunkBoundary states related) :
    ForwardChunk (related := related) states events boundary.1 boundary.2.1 :=
  Classical.choice (chunks boundary.1 boundary.2.1 boundary.2.2)

noncomputable def forwardChunkBoundaries
    {states : Nat → source.State} {events : Nat → Option Event}
    (chunks : ∀ index targetStart, related (states index) targetStart →
      Nonempty (ForwardChunk (related := related) states events index targetStart))
    (targetStart : target.State) (initialRelation : related (states 0) targetStart) :
    Nat → ChunkBoundary states related
  | 0 => ⟨0,targetStart,initialRelation⟩
  | n+1 =>
      let chunk := chooseForwardChunk chunks (forwardChunkBoundaries chunks targetStart initialRelation n)
      ⟨chunk.matchedIndex+1,chunk.targetEnd,chunk.endpointRelated⟩

theorem forwardSteps (refinement : WeakRefinement source target related)
    {sourceStart sourceEnd : source.State} {trace : List Event}
    (steps : source.Steps sourceStart trace sourceEnd) :
    ∀ targetStart, related sourceStart targetStart →
      ∃ targetEnd, target.Steps targetStart trace targetEnd ∧ related sourceEnd targetEnd := by
  induction steps with
  | refl =>
    intro targetStart relation
    exact ⟨targetStart,TransitionSystem.Steps.refl,relation⟩
  | silent step rest ih =>
    intro targetStart relation
    rcases refinement.forwardStep relation step with matched | stutter
    · obtain ⟨next,path,nextRelation⟩ := matched
      obtain ⟨finish,restPath,finishRelation⟩ := ih next nextRelation
      refine ⟨finish,?_,finishRelation⟩
      simpa using (path.toSteps.trans restPath)
    · exact ih targetStart stutter.2.1
  | visible step rest ih =>
    intro targetStart relation
    rcases refinement.forwardStep relation step with matched | stutter
    · obtain ⟨next,path,nextRelation⟩ := matched
      obtain ⟨finish,restPath,finishRelation⟩ := ih next nextRelation
      refine ⟨finish,?_,finishRelation⟩
      simpa using (path.toSteps.trans restPath)
    · rcases stutter with ⟨impossible,_,_⟩
      simp at impossible

theorem backwardSteps (refinement : WeakRefinement source target related)
    {targetStart targetEnd : target.State} {trace : List Event}
    (steps : target.Steps targetStart trace targetEnd) :
    ∀ sourceStart, related sourceStart targetStart →
      ∃ sourceEnd, source.Steps sourceStart trace sourceEnd ∧ related sourceEnd targetEnd := by
  induction steps with
  | refl =>
    intro sourceStart relation
    exact ⟨sourceStart,TransitionSystem.Steps.refl,relation⟩
  | silent step rest ih =>
    intro sourceStart relation
    rcases refinement.backwardStep relation step with matched | stutter
    · obtain ⟨next,path,nextRelation⟩ := matched
      obtain ⟨finish,restPath,finishRelation⟩ := ih next nextRelation
      refine ⟨finish,?_,finishRelation⟩
      simpa using (path.toSteps.trans restPath)
    · exact ih sourceStart stutter.2.1
  | visible step rest ih =>
    intro sourceStart relation
    rcases refinement.backwardStep relation step with matched | stutter
    · obtain ⟨next,path,nextRelation⟩ := matched
      obtain ⟨finish,restPath,finishRelation⟩ := ih next nextRelation
      refine ⟨finish,?_,finishRelation⟩
      simpa using (path.toSteps.trans restPath)
    · rcases stutter with ⟨impossible,_,_⟩
      simp at impossible

/- Safety closure lemmas continue in the weak-refinement namespace. -/

theorem backwardReachable {source target : TransitionSystem Event Result}
    {related : source.State → target.State → Prop}
    (refinement : WeakRefinement source target related) {targetState : target.State}
    (reachable : target.Reachable targetState) :
    ∃ sourceState, source.Reachable sourceState ∧ related sourceState targetState := by
  obtain ⟨targetStart,trace,targetInitial,path⟩ := reachable
  obtain ⟨sourceStart,sourceInitial,relation⟩ := refinement.initialBackward targetStart targetInitial
  obtain ⟨sourceEnd,sourcePath,endRelation⟩ := refinement.backwardSteps path sourceStart relation
  exact ⟨sourceEnd,⟨sourceStart,trace,sourceInitial,sourcePath⟩,endRelation⟩

theorem safeAt {source target : TransitionSystem Event Result}
    {related : source.State → target.State → Prop}
    (refinement : WeakRefinement source target related) (sourceSafe : source.Safe) :
    ∀ sourceState targetState, related sourceState targetState → source.Reachable sourceState →
      (∃ result, target.final targetState result) ∨
      ∃ event next, target.step targetState event next := by
  let motive : refinement.Rank → Prop := fun measure =>
    ∀ sourceState targetState, refinement.rank sourceState targetState = measure →
      related sourceState targetState → source.Reachable sourceState →
      (∃ result, target.final targetState result) ∨
      ∃ event next, target.step targetState event next
  have descend : ∀ measure, motive measure := fun measure =>
    refinement.wellFounded.induction measure (fun measure ih => by
      intro sourceState targetState rankEq relation reachable
      obtain ⟨_,sourceCanContinue⟩ := sourceSafe sourceState reachable
      rcases sourceCanContinue with sourceFinal | sourceStep
      · obtain ⟨result,sourceFinal⟩ := sourceFinal
        obtain ⟨targetEnd,silent,endRelation,targetFinal⟩ :=
          refinement.finalForward relation sourceFinal
        rcases silent.zero_or_positive with zero | positive
        · left
          rcases zero with ⟨same,_⟩
          exact ⟨result,by simpa [same] using targetFinal⟩
        · right
          rcases positive with ⟨event,next,_,step,_,_⟩
          exact ⟨event,next,step⟩
      · obtain ⟨event,next,step⟩ := sourceStep
        rcases refinement.forwardStep relation step with matched | stutter
        · right
          obtain ⟨targetNext,path,_⟩ := matched
          rcases path with ⟨event',middle,suffix,targetStep,_,_⟩
          exact ⟨event',middle,targetStep⟩
        · rcases stutter with ⟨eventNone,nextRelation,rankDecrease⟩
          have nextReach : source.Reachable next := by
            obtain ⟨initial,trace,initialProof,path⟩ := reachable
            have one : source.Steps sourceState event.toList next := by
              cases event with
              | none => exact .silent step TransitionSystem.Steps.refl
              | some event => exact .visible step TransitionSystem.Steps.refl
            exact ⟨initial,trace ++ event.toList,initialProof,by simpa using path.trans one⟩
          have nextRank : refinement.decrease (refinement.rank next targetState) measure := by
            rw [← rankEq]
            exact rankDecrease
          exact ih (refinement.rank next targetState) nextRank next targetState rfl nextRelation nextReach)
  intro sourceState targetState relation reachable
  exact descend (refinement.rank sourceState targetState) sourceState targetState rfl relation reachable

theorem safety {source target : TransitionSystem Event Result}
    {related : source.State → target.State → Prop}
    (refinement : WeakRefinement source target related) : source.Safe → target.Safe := by
  intro sourceSafe targetState reachable
  obtain ⟨sourceState,sourceReachable,relation⟩ := refinement.backwardReachable reachable
  have sourceFacts := sourceSafe sourceState sourceReachable
  constructor
  · intro invalid
    exact sourceFacts.1 (refinement.invalidReflection relation invalid)
  · exact refinement.safeAt sourceSafe sourceState targetState relation sourceReachable

end WeakRefinement

/- End weak-refinement namespace. -/

theorem WeakRefinement.prefixes {source target : TransitionSystem Event Result}
    {related : source.State → target.State → Prop}
    (refinement : WeakRefinement source target related) (trace : List Event) :
    source.Prefix trace ↔ target.Prefix trace := by
  constructor
  · rintro ⟨sourceStart,sourceEnd,initial,steps⟩
    obtain ⟨targetStart,targetInitial,relation⟩ := refinement.initialForward sourceStart initial
    obtain ⟨targetEnd,targetSteps,_⟩ := refinement.forwardSteps steps targetStart relation
    exact ⟨targetStart,targetEnd,targetInitial,targetSteps⟩
  · rintro ⟨targetStart,targetEnd,initial,steps⟩
    obtain ⟨sourceStart,sourceInitial,relation⟩ := refinement.initialBackward targetStart initial
    obtain ⟨sourceEnd,sourceSteps,_⟩ := refinement.backwardSteps steps sourceStart relation
    exact ⟨sourceStart,sourceEnd,sourceInitial,sourceSteps⟩

theorem WeakRefinement.results {source target : TransitionSystem Event Result}
    {related : source.State → target.State → Prop}
    (refinement : WeakRefinement source target related) (trace : List Event) (result : Result) :
    source.Returns trace result ↔ target.Returns trace result := by
  constructor
  · rintro ⟨sourceStart,sourceEnd,initial,steps,final⟩
    obtain ⟨targetStart,targetInitial,relation⟩ := refinement.initialForward sourceStart initial
    obtain ⟨targetMid,path,midRelation⟩ := refinement.forwardSteps steps targetStart relation
    obtain ⟨targetEnd,silent,endRelation,targetFinal⟩ := refinement.finalForward midRelation final
    exact ⟨targetStart,targetEnd,targetInitial,by simpa using path.trans silent,targetFinal⟩
  · rintro ⟨targetStart,targetEnd,initial,steps,final⟩
    obtain ⟨sourceStart,sourceInitial,relation⟩ := refinement.initialBackward targetStart initial
    obtain ⟨sourceMid,path,midRelation⟩ := refinement.backwardSteps steps sourceStart relation
    obtain ⟨sourceEnd,silent,endRelation,sourceFinal⟩ := refinement.finalBackward midRelation final
    exact ⟨sourceStart,sourceEnd,sourceInitial,by simpa using path.trans silent,sourceFinal⟩
theorem WeakRefinement.reachableForward {source target : TransitionSystem Event Result}
    {related : source.State → target.State → Prop}
    (refinement : WeakRefinement source target related) {sourceState : source.State}
    (reachable : source.Reachable sourceState) :
    ∃ targetState, target.Reachable targetState ∧ related sourceState targetState := by
  obtain ⟨sourceStart,trace,initial,path⟩ := reachable
  obtain ⟨targetStart,targetInitial,relation⟩ := refinement.initialForward sourceStart initial
  obtain ⟨targetState,targetPath,endRelation⟩ := refinement.forwardSteps path targetStart relation
  exact ⟨targetState,⟨targetStart,trace,targetInitial,targetPath⟩,endRelation⟩

theorem WeakRefinement.reachableBackward {source target : TransitionSystem Event Result}
    {related : source.State → target.State → Prop}
    (refinement : WeakRefinement source target related) {targetState : target.State}
    (reachable : target.Reachable targetState) :
    ∃ sourceState, source.Reachable sourceState ∧ related sourceState targetState :=
  refinement.backwardReachable reachable

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


theorem ObservedPrefix.take (stream : Nat → Option Event) (count size : Nat) :
    ∃ stop, stop ≤ count ∧ ObservedPrefix stream stop = (ObservedPrefix stream count).take size := by
  induction count with
  | zero => exact ⟨0,Nat.le_refl _,by simp [ObservedPrefix]⟩
  | succ count ih =>
      by_cases small : size ≤ (ObservedPrefix stream count).length
      · obtain ⟨stop,bound,observed⟩ := ih
        exact ⟨stop,Nat.le_trans bound (Nat.le_succ _),by
          rw [ObservedPrefix.succ,List.take_append_of_le_length small]; exact observed⟩
      · refine ⟨count+1,Nat.le_refl _,?_⟩
        apply (List.take_of_length_le ?_).symm
        rw [ObservedPrefix.succ,List.length_append]
        cases stream count <;> simp only [Option.toList,List.length_nil,List.length_cons] <;> omega

theorem ObservedPrefix.mono (stream : Nat → Option Event) {first last : Nat} (ordered : first ≤ last) :
    ∃ suffix, ObservedPrefix stream last = ObservedPrefix stream first ++ suffix := by
  induction ordered with
  | refl => exact ⟨[],by simp⟩
  | @step last ordered ih =>
      obtain ⟨suffix,same⟩ := ih
      exact ⟨suffix ++ (stream last).toList,by rw [ObservedPrefix.succ,same,List.append_assoc]⟩

theorem SameObservations.of_cofinal {left right : Nat → Option Event}
    (forward : ∀ count, ∃ first last, count ≤ first ∧ ObservedPrefix left first = ObservedPrefix right last)
    (backward : ∀ count, ∃ first last, count ≤ last ∧ ObservedPrefix left first = ObservedPrefix right last) :
    SameObservations left right := by
  have direction (a b : Nat → Option Event)
      (cofinal : ∀ count, ∃ first last, count ≤ first ∧ ObservedPrefix a first = ObservedPrefix b last)
      (trace : List Event) (observed : ∃ count, ObservedPrefix a count = trace) :
      ∃ count, ObservedPrefix b count = trace := by
    obtain ⟨count,rfl⟩ := observed
    obtain ⟨first,last,bound,same⟩ := cofinal count
    obtain ⟨suffix,extended⟩ := ObservedPrefix.mono a bound
    obtain ⟨stop,_,taken⟩ := ObservedPrefix.take b last (ObservedPrefix a count).length
    refine ⟨stop,?_⟩
    rw [taken,← same,extended,List.take_left]
  intro trace
  exact ⟨direction left right forward trace,
    direction right left (fun count => by
      obtain ⟨first,last,bound,same⟩ := backward count
      exact ⟨last,first,bound,same.symm⟩) trace⟩

namespace TransitionSystem

/-- A finite path retaining silent steps, for stitching genuine infinite runs. -/
structure TimedPath (system : TransitionSystem Event Result) (start : system.State)
    (trace : List Event) (finish : system.State) where
  length : Nat
  states : Nat → system.State
  events : Nat → Option Event
  first : states 0 = start
  last : states length = finish
  steps : ∀ index, index < length → system.step (states index) (events index) (states (index+1))
  observed : ObservedPrefix events length = trace

def TimedPath.prepend {system : TransitionSystem Event Result} {start middle finish : system.State}
    {event : Option Event} {trace : List Event} (step : system.step start event middle)
    (path : TimedPath system middle trace finish) : TimedPath system start (event.toList ++ trace) finish where
  length := path.length + 1
  states := fun index => match index with | 0 => start | n+1 => path.states n
  events := fun index => match index with | 0 => event | n+1 => path.events n
  first := rfl
  last := path.last
  steps := by
    intro index bound
    cases index with
    | zero => simpa only [path.first] using step
    | succ index => exact path.steps index (by omega)
  observed := by
    have shift (count : Nat) :
        ObservedPrefix (fun index => match index with | 0 => event | n+1 => path.events n) (count+1) =
          event.toList ++ ObservedPrefix path.events count := by
      induction count with
      | zero => cases event <;> simp [ObservedPrefix]
      | succ count ih => rw [ObservedPrefix.succ,ih,ObservedPrefix.succ,List.append_assoc]
    rw [shift,path.observed]

theorem Steps.timed {system : TransitionSystem Event Result} {start finish : system.State}
    {trace : List Event} (path : system.Steps start trace finish) :
    Nonempty (TimedPath system start trace finish) := by
  induction path with
  | @refl state => exact ⟨⟨0,fun _ => state,fun _ => none,rfl,rfl,by omega,rfl⟩⟩
  | silent step _ ih =>
      obtain ⟨path⟩ := ih
      exact ⟨path.prepend step⟩
  | visible step _ ih =>
      obtain ⟨path⟩ := ih
      exact ⟨path.prepend step⟩

theorem PositiveSteps.timed {system : TransitionSystem Event Result} {start finish : system.State}
    {trace : List Event} (positive : system.PositiveSteps start trace finish) :
    ∃ path : TimedPath system start trace finish, 0 < path.length := by
  obtain ⟨event,middle,suffix,step,rest,rfl⟩ := positive
  obtain ⟨path⟩ := rest.timed
  exact ⟨path.prepend step,Nat.zero_lt_succ _⟩


/-- Positive finite segments, with endpoints shared by adjacent segments. -/
structure Segments (system : TransitionSystem Event Result) where
  points : Nat → system.State
  traces : Nat → List Event
  paths : ∀ n, TimedPath system (points n) (traces n) (points (n+1))
  positive : ∀ n, 0 < (paths n).length

namespace Segments
variable {system : TransitionSystem Event Result} (segments : Segments system)

def cut : Nat → Nat
  | 0 => 0
  | n+1 => cut n + (segments.paths n).length

theorem cut_mono {first last : Nat} (bound : first ≤ last) : segments.cut first ≤ segments.cut last := by
  induction bound with
  | refl => exact Nat.le_refl _
  | step _ ih => simp only [cut]; omega

theorem cut_bound (n : Nat) : n ≤ segments.cut n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih => have positive := segments.positive n; simp only [cut]; omega

theorem covers (n : Nat) : ∃ k, segments.cut k ≤ n ∧ n < segments.cut (k+1) := by
  induction n with
  | zero => exact ⟨0,Nat.le_refl _,by simpa only [cut,Nat.zero_add] using segments.positive 0⟩
  | succ n ih =>
      obtain ⟨k,lower,upper⟩ := ih
      by_cases inside : n+1 < segments.cut (k+1)
      · exact ⟨k,by omega,inside⟩
      · refine ⟨k+1,by omega,?_⟩
        have positive := segments.positive (k+1)
        simp only [cut]
        simp only [cut] at upper inside
        omega

noncomputable def index (n : Nat) : Nat := Classical.choose (segments.covers n)

theorem index_bounds (n : Nat) : segments.cut (segments.index n) ≤ n ∧ n < segments.cut (segments.index n + 1) :=
  Classical.choose_spec (segments.covers n)

theorem index_eq {n k : Nat} (lower : segments.cut k ≤ n) (upper : n < segments.cut (k+1)) :
    segments.index n = k := by
  obtain ⟨lo,hi⟩ := segments.index_bounds n
  by_cases less : segments.index n < k
  · have ordered := segments.cut_mono (show segments.index n + 1 ≤ k by omega)
    omega
  · by_cases greater : k < segments.index n
    · have ordered := segments.cut_mono (show k+1 ≤ segments.index n by omega)
      omega
    · omega

noncomputable def states (n : Nat) : system.State :=
  (segments.paths (segments.index n)).states (n - segments.cut (segments.index n))
noncomputable def events (n : Nat) : Option Event :=
  (segments.paths (segments.index n)).events (n - segments.cut (segments.index n))

theorem index_cut_add (k offset : Nat) (bound : offset < (segments.paths k).length) :
    segments.index (segments.cut k + offset) = k :=
  segments.index_eq (by omega) (by simp only [cut]; omega)

theorem state_cut (k : Nat) : segments.states (segments.cut k) = segments.points k := by
  have index := segments.index_cut_add k 0 (segments.positive k)
  simp only [Nat.add_zero] at index
  unfold states
  rw [index,Nat.sub_self]
  exact (segments.paths k).first

theorem state_cut_add (k offset : Nat) (bound : offset ≤ (segments.paths k).length) :
    segments.states (segments.cut k + offset) = (segments.paths k).states offset := by
  by_cases inside : offset < (segments.paths k).length
  · unfold states
    rw [segments.index_cut_add k offset inside,Nat.add_sub_cancel_left]
  · have last : offset = (segments.paths k).length := by omega
    subst offset
    rw [← cut,segments.state_cut,(segments.paths k).last]

theorem event_cut_add (k offset : Nat) (bound : offset < (segments.paths k).length) :
    segments.events (segments.cut k + offset) = (segments.paths k).events offset := by
  unfold events
  rw [segments.index_cut_add k offset bound,Nat.add_sub_cancel_left]

theorem step (n : Nat) : system.step (segments.states n) (segments.events n) (segments.states (n+1)) := by
  obtain ⟨lower,upper⟩ := segments.index_bounds n
  let k := segments.index n
  let offset := n - segments.cut k
  have inside : offset < (segments.paths k).length := by
    dsimp [offset,k]
    simp only [cut] at upper
    omega
  have same : n = segments.cut k + offset := by dsimp [k,offset]; omega
  rw [same,segments.state_cut_add k offset (by omega),segments.event_cut_add k offset inside]
  rw [Nat.add_assoc,segments.state_cut_add k (offset+1) (by omega)]
  exact (segments.paths k).steps offset inside

theorem observed_segment (k count : Nat) (bound : count ≤ (segments.paths k).length) :
    ObservedPrefix segments.events (segments.cut k + count) =
      ObservedPrefix segments.events (segments.cut k) ++ ObservedPrefix (segments.paths k).events count := by
  induction count with
  | zero => simp [ObservedPrefix]
  | succ count ih =>
      rw [← Nat.add_assoc,ObservedPrefix.succ,ih (by omega),
        segments.event_cut_add k count (by omega),ObservedPrefix.succ,List.append_assoc]

theorem observed_cut_succ (k : Nat) :
    ObservedPrefix segments.events (segments.cut (k+1)) =
      ObservedPrefix segments.events (segments.cut k) ++ segments.traces k := by
  rw [cut,segments.observed_segment k (segments.paths k).length (Nat.le_refl _),(segments.paths k).observed]

theorem infinite (initial : system.initial (segments.points 0)) : system.Infinite segments.events := by
  refine ⟨segments.states,?_,segments.step⟩
  have first := segments.state_cut 0
  exact first ▸ initial

end Segments

end TransitionSystem


theorem ObservedPrefix.silent_interval (events : Nat → Option Event) {start finish : Nat}
    (bound : start ≤ finish) (silent : ∀ n, start ≤ n → n < finish → events n = none) :
    ObservedPrefix events finish = ObservedPrefix events start := by
  induction bound with
  | refl => rfl
  | @step finish bound ih =>
      rw [ObservedPrefix.succ,silent finish bound (Nat.lt_succ_self _)]
      simp only [Option.toList_none,List.append_nil]
      exact ih (fun n lo hi => silent n lo (by omega))

namespace WeakRefinement
variable {source target : TransitionSystem Event Result}
variable {related : source.State → target.State → Prop}

theorem infinite_from_chunks
    (states : Nat → source.State) (events : Nat → Option Event)
    (chunks : ∀ index targetStart, related (states index) targetStart →
      Nonempty (ForwardChunk (related := related) states events index targetStart))
    (targetStart : target.State) (initial : target.initial targetStart)
    (initialRelation : related (states 0) targetStart) :
    ∃ other, target.Infinite other ∧ SameObservations events other := by
  classical
  let boundaries := forwardChunkBoundaries chunks targetStart initialRelation
  let chunk := fun k => chooseForwardChunk chunks (boundaries k)
  let paths := fun k => Classical.choose (chunk k).targetPath.timed
  let segments : TransitionSystem.Segments target := {
    points := fun k => (boundaries k).2.1
    traces := fun k => (events (chunk k).matchedIndex).toList
    paths := paths
    positive := fun k => Classical.choose_spec (chunk k).targetPath.timed }
  have bound : ∀ k, k ≤ (boundaries k).1 := by
    intro k
    induction k with
    | zero => exact Nat.le_refl _
    | succ k ih =>
        change k+1 ≤ (chunk k).matchedIndex+1
        have start := (chunk k).startBound
        omega
  have equal : ∀ k, ObservedPrefix events (boundaries k).1 =
      ObservedPrefix segments.events (segments.cut k) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        change ObservedPrefix events ((chunk k).matchedIndex+1) = _
        rw [ObservedPrefix.succ,
          ObservedPrefix.silent_interval events (chunk k).startBound (chunk k).skippedSilent,
          segments.observed_cut_succ,← ih]
  refine ⟨segments.events,segments.infinite initial,?_⟩
  exact SameObservations.of_cofinal
    (fun count => ⟨(boundaries count).1,segments.cut count,bound count,equal count⟩)
    (fun count => ⟨(boundaries count).1,segments.cut count,segments.cut_bound count,equal count⟩)

theorem infiniteForward (refinement : WeakRefinement source target related)
    {events : Nat → Option Event} (run : source.Infinite events) :
    ∃ other, target.Infinite other ∧ SameObservations events other := by
  obtain ⟨states,initial,steps⟩ := run
  obtain ⟨targetStart,targetInitial,relation⟩ := refinement.initialForward (states 0) initial
  exact infinite_from_chunks states events
    (seekForwardChunk refinement.Rank refinement.decrease refinement.wellFounded refinement.rank
      refinement.forwardStep states events steps) targetStart targetInitial relation

theorem infiniteBackward (refinement : WeakRefinement source target related)
    {events : Nat → Option Event} (run : target.Infinite events) :
    ∃ other, source.Infinite other ∧ SameObservations events other := by
  obtain ⟨states,initial,steps⟩ := run
  obtain ⟨sourceStart,sourceInitial,relation⟩ := refinement.initialBackward (states 0) initial
  exact infinite_from_chunks (related := fun targetState sourceState => related sourceState targetState)
    states events
    (seekForwardChunk refinement.Rank refinement.decrease refinement.wellFounded
      (fun targetState sourceState => refinement.rank sourceState targetState)
      refinement.backwardStep states events steps) sourceStart sourceInitial relation

theorem preserves (refinement : WeakRefinement source target related) : Preserves source target where
  prefixes := refinement.prefixes
  results := refinement.results
  divergence _ run := refinement.infiniteForward run
  noNewDivergence _ run := by
    obtain ⟨other,infinite,equal⟩ := refinement.infiniteBackward run
    exact ⟨other,infinite,fun trace => (equal trace).symm⟩
  safety := refinement.safety

end WeakRefinement

end Glorious.Language
