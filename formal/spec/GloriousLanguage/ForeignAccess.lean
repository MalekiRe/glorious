import GloriousLanguage.Primitives

/-! Host storage authority follows the ordinary logical projection resolver
and raw-pointer provenance. Numeric identity, a writable-contract predicate,
and an unsafe call flag cannot introduce access to an unrelated source root. -/
namespace Glorious.Language.Foreign

open Kernel Execution Memory

/-- A host can project and dereference an exposed place through the same
authority producer used by source places. Raw pointers add only their actual
provenance-backed allocation/external location, with the pointer's mode. -/
inductive Reachable (program : Language.Program) (world : World)
    (seeds : ResolvedPlace → Prop) : ResolvedPlace → Prop where
  | seed {place} : seeds place → Reachable program world seeds place
  | project {place projections address authority} : Reachable program world seeds place →
      ResolvesProjections world [] place.address place.authority projections address authority →
      Reachable program world seeds ⟨address,authority⟩
  | pointer {place value mode type pointer address} : Reachable program world seeds place →
      world.Stores place.address value → value.Initialized →
      Permitted world place.authority .shared place.address →
      value.type = .rawPointer mode type → value.head = .pointer pointer →
      PointsTo program world pointer address type →
      Reachable program world seeds ⟨address,if mode = .shared then .shared .owner else .owner⟩

def _root_.Glorious.Language.Execution.ForeignSession.known (session : ForeignSession) : List ResolvedPlace :=
  session.call.operands.map (fun address => ⟨address,.owner⟩) ++ session.exposed

/-- Nested callback re-entry sees the actual enclosing host sessions. No
source frame environment or invocation-cleanup handle is in this projection. -/
def AmbientExposed (frames : List Frame) : List ResolvedPlace :=
  frames.flatMap fun frame => match frame with
    | .hostCallback session _ _ _ _ => session.known
    | _ => []

/-- The host receives exactly the runtime obligations retained by actual
callback and hook continuations on the current control stack. -/
def AmbientRuntimes (frames : List Frame) : List Identity :=
  frames.flatMap Frame.callbackRuntimes

/-- Publish only roots allocated during one uninterrupted host mutation
chunk. Allocations made later by source callbacks are outside this interval. -/
def FreshExposed (before after : World) : List ResolvedPlace :=
  after.roots.filterMap fun (id,root) =>
    if before.nextRoot ≤ id ∧ root.live = true then
      some ⟨⟨id,root.generation,[]⟩,.owner⟩ else none

def _root_.Glorious.Language.Execution.ForeignSession.advance (session : ForeignSession) (before after : World)
    (state : List Nat) : ForeignSession :=
  { session with state, exposed := session.exposed ++ FreshExposed before after }

def _root_.Glorious.Language.Execution.ForeignSession.returned (session : ForeignSession) (result : Address)
    (state : List Nat) : ForeignSession :=
  { session with state, exposed := ⟨result,.owner⟩ :: session.exposed }

/-- An actual stored pointer may be inspected or have its address changed
without discarding its allocation provenance. Owning an exposed external or
allocation root also permits constructing that root's real address. -/
def PointerAccess (program : Language.Program) (world : World)
    (reachable : ResolvedPlace → Prop) (mode : Mutability) (pointer : RawPointer) : Prop :=
  pointer.Origin world ∧
  ((pointer.allocation = none ∧ pointer.domain = none) ∨
    (∃ place value original storedMode type,
      reachable place ∧ world.Stores place.address value ∧ value.Initialized ∧
      Permitted world place.authority .shared place.address ∧
      value.type = .rawPointer storedMode type ∧ value.head = .pointer original ∧
      (mode = .unique → storedMode = .unique) ∧
      (pointer = original ∨ WithAddress program world original pointer.address pointer)) ∨
    ∃ place root domain,
      reachable place ∧ place.address.fields = [] ∧
      Permitted world place.authority (if mode = .shared then .shared else .unique) place.address ∧
      world.root place.address = some root ∧
      (root.home = .allocation domain ∨ root.home = .external domain) ∧
      pointer.allocation = some place.address.root ∧ pointer.generation = place.address.generation ∧
      pointer.domain = some domain)

/-- Permissions supplied to the existing mutation constructors. The foreign
protocol supplies the origins; this record never substitutes for storage
typing, alias permission, raw-range checks or the actual storage transition. -/
structure AuthorityPolicy where
  place : World → ResolvedPlace → Prop
  write : World → Address → Prop
  pointer : World → Mutability → RawPointer → Prop
  home : Home → Identity → Prop
  domain : Identity → Prop

end Glorious.Language.Foreign
