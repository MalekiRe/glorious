import GloriousLanguage.Primitives

/-! Host storage authority follows the common invocation resource inputs and
ordinary logical projection resolver. Numeric identity, pointer provenance, a writable-contract predicate,
and an unsafe call flag cannot introduce access to an unrelated source root. -/
namespace Glorious.Language.Foreign

open Kernel Execution Memory

/-- A host can project and dereference an exposed place through the same
authority producer used by source places. Reading pointer bits does not extend
this domain: a pointee obligation must already have been handed to the host. -/
inductive Reachable (program : Language.Program) (world : World)
    (seeds : ResolvedPlace → Prop) : ResolvedPlace → Prop where
  | seed {place} : seeds place → Reachable program world seeds place
  | project {place projections address authority} : Reachable program world seeds place →
      ResolvesProjections world [] place.address place.authority projections address authority →
      Reachable program world seeds ⟨address,authority⟩
  | subplace {place address} : Reachable program world seeds place → place.address.Prefix address →
      world.Located address → Reachable program world seeds ⟨address,place.authority⟩

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

/-- The actual ordered transaction publishes these handoffs. A post-world
root/loan scan cannot reconstruct them or decide their recipient. -/
structure ProducedResource where
  recipient : ClaimCustody
  place : ResolvedPlace
  deriving Repr, Inhabited

def _root_.Glorious.Language.Execution.ForeignSession.advance (session : ForeignSession)
    (produced : List ProducedResource) (state : List Nat) : ForeignSession :=
  { session with state, exposed := session.exposed ++ produced.filterMap fun resource =>
      if resource.recipient = .host session.call.destination.root then some resource.place else none }

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
  custody : ClaimCustody

end Glorious.Language.Foreign
