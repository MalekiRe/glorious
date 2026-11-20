module

/-!
# Where a value is

A cache keyed by the object a value is, rather than by the value: the same
object asked again is found without looking at what it holds.
-/

@[expose] public section

namespace Glorious

@[noinline] unsafe def addrOfImpl {α : Type} (a : α) : USize := ptrAddrUnsafe a

/-- Where a value is in memory: the same for the same object. Only a key of a
cache that keeps the object, so that no other comes to be there. -/
@[implemented_by addrOfImpl] def addrOf {α : Type} (a : α) : USize := let _ := a; 0

end Glorious
