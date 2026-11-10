import Glorious.Proof.Correct

/-!
# Non-vacuity witnesses

`compile_correct` would hold trivially if the Core semantics gave no program a
meaning. These programs between them use every construct, and the kernel checks
that both machines run each to the same result.
-/

namespace Glorious.Witness

/--
Recursion, an integer branch and a nested pattern.
```
sum(0, acc)             = acc
sum(n, acc)             = tail sum(n - 1, acc + n)
first(Pair(Some(x), _)) = x
first(Pair(None,    _)) = 0
main                    = tail first(Pair(Some(sum(4, 0)), 9))
```
`Pair` has tag 0; `Some` has tag 0 and `None` tag 1.
-/
def patterns : Core.Program where
  fns := [
    ⟨[ ⟨[.int 0, .wild], .ret (.var 1)⟩,
       ⟨[.wild, .wild],
          .let_ (.prim .intSub [.var 0, .int 1]) <|
          .let_ (.prim .intAdd [.var 1, .var 0]) <|
          .let_ (.closure 0 []) <|
          .tail (.var 4) [.var 2, .var 3]⟩ ]⟩,
    ⟨[ ⟨[.ctor 0 [.ctor 0 [.bind], .wild]], .ret (.var 1)⟩,
       ⟨[.ctor 0 [.ctor 1 [], .wild]], .ret (.int 0)⟩ ]⟩
  ]
  main :=
    .let_ (.closure 0 []) <|
    .call (.var 0) [.int 4, .int 0] <|
    .let_ (.construct 0 [.var 1]) <|
    .let_ (.construct 0 [.var 2, .int 9]) <|
    .let_ (.closure 1 []) <|
    .tail (.var 4) [.var 3]

theorem patterns_core : Core.Halts patterns [] ⟨.int 10, ⟨[], []⟩⟩ := ⟨40, rfl⟩

theorem patterns_bytecode : Bytecode.Halts (compile patterns) [] ⟨.int 10, ⟨[], []⟩⟩ :=
  ⟨80, rfl⟩

/--
A resumptive operation `Ask` (0) and a terminal operation `Fail` (1).
```
worker()        = let a = Ask(1) in let b = Ask(a) in a + b
guarded[w]()    = handle w()       { r => r;      Fail(e)   => e + 1 }
asking[g]()     = let r = handle g() { r => r * 2;  Ask(x, k) => tail k(x + 10) }
                  in Fail(r)
main            = handle asking[guarded[worker]]() { r => r; Fail(e) => e + 1 }
```
`Ask` is performed under a `Fail` handler that does not handle it, so the
captured continuation includes that handler. Each `Ask` is resumed once: `a` is
11, `b` is 21, the completion clause doubles 32 to 64, and the final `Fail(64)`
abandons its continuation and is handled by the outermost handler, giving 65.
-/
def effects : Core.Program where
  fns := [
    -- 0: worker
    ⟨[ ⟨[], .perform 0 [.int 1] <| .perform 0 [.var 0] <|
              .let_ (.prim .intAdd [.var 0, .var 1]) <| .ret (.var 2)⟩ ]⟩,
    -- 1: the `Ask` arm, receiving the payload and the resumption
    ⟨[ ⟨[.wild, .wild], .let_ (.prim .intAdd [.var 0, .int 10]) <| .tail (.var 1) [.var 2]⟩ ]⟩,
    -- 2: completion clause that doubles
    ⟨[ ⟨[.wild], .let_ (.prim .intMul [.var 0, .int 2]) <| .ret (.var 1)⟩ ]⟩,
    -- 3: identity completion clause
    ⟨[ ⟨[.wild], .ret (.var 0)⟩ ]⟩,
    -- 4: the `Fail` arm
    ⟨[ ⟨[.wild], .let_ (.prim .intAdd [.var 0, .int 1]) <| .ret (.var 1)⟩ ]⟩,
    -- 5: guarded, capturing the worker
    ⟨[ ⟨[], .handle 3 [(1, 4)] [] (.var 0) <| .ret (.var 1)⟩ ]⟩,
    -- 6: asking, capturing guarded
    ⟨[ ⟨[], .handle 2 [(0, 1)] [] (.var 0) <| .raise 1 [.var 1]⟩ ]⟩
  ]
  main :=
    .let_ (.closure 0 []) <|
    .let_ (.closure 5 [.var 0]) <|
    .let_ (.closure 6 [.var 1]) <|
    .handle 3 [(1, 4)] [] (.var 2) <|
    .ret (.var 3)

theorem effects_core : Core.Halts effects [] ⟨.int 65, ⟨[], []⟩⟩ := ⟨60, rfl⟩

theorem effects_bytecode : Bytecode.Halts (compile effects) [] ⟨.int 65, ⟨[], []⟩⟩ :=
  ⟨60, rfl⟩

/-- Resuming the same resumption twice has no meaning: resumptions are one-shot.
```
main = handle (() => Ask(1))() { r => r; Ask(x, k) => let _ = k(x) in tail k(x) }
```
-/
def resumeTwice : Core.Program where
  fns := [
    ⟨[ ⟨[], .perform 0 [.int 1] <| .ret (.var 0)⟩ ]⟩,
    ⟨[ ⟨[.wild, .wild], .call (.var 1) [.var 0] <| .tail (.var 1) [.var 0]⟩ ]⟩,
    ⟨[ ⟨[.wild], .ret (.var 0)⟩ ]⟩
  ]
  main :=
    .let_ (.closure 0 []) <|
    .handle 2 [(0, 1)] [] (.var 0) <|
    .ret (.var 1)

theorem resumeTwice_goesWrong : Core.GoesWrong resumeTwice [] := ⟨20, rfl⟩

/--
A label scope left early from inside a nested call, and one that ends normally.
```
check[l](3)  = tail l(3 * 100)
check[l](x)  = x
body(l)      = let c = check[l] in c(1) + c(3) + c(5)
seven(l)     = 7
main         = (label body) + (label seven)
```
`c(3)` leaves the first scope with 300, abandoning the rest of `body`.
-/
def labels : Core.Program where
  fns := [
    ⟨[ ⟨[.int 3], .let_ (.prim .intMul [.var 0, .int 100]) <| .tail (.var 1) [.var 2]⟩,
       ⟨[.wild], .ret (.var 0)⟩ ]⟩,
    ⟨[ ⟨[.wild],
          .let_ (.closure 0 [.var 0]) <|
          .call (.var 1) [.int 1] <|
          .call (.var 1) [.int 3] <|
          .call (.var 1) [.int 5] <|
          .let_ (.prim .intAdd [.var 2, .var 3]) <|
          .let_ (.prim .intAdd [.var 5, .var 4]) <|
          .ret (.var 6)⟩ ]⟩,
    ⟨[ ⟨[.wild], .ret (.int 7)⟩ ]⟩
  ]
  main :=
    .let_ (.closure 1 []) <|
    .label (.var 0) <|
    .let_ (.closure 2 []) <|
    .label (.var 2) <|
    .let_ (.prim .intAdd [.var 1, .var 3]) <|
    .ret (.var 4)

theorem labels_core : Core.Halts labels [] ⟨.int 307, ⟨[], []⟩⟩ := ⟨40, rfl⟩

theorem labels_bytecode : Bytecode.Halts (compile labels) [] ⟨.int 307, ⟨[], []⟩⟩ :=
  ⟨40, rfl⟩

/-- A label used after its scope has ended has no meaning.
```
main = let l = label (l => l) in tail l(1)
```
-/
def escapedLabel : Core.Program where
  fns := [ ⟨[ ⟨[.wild], .ret (.var 0)⟩ ]⟩ ]
  main :=
    .let_ (.closure 0 []) <|
    .label (.var 0) <|
    .tail (.var 1) [.int 1]

theorem escapedLabel_goesWrong : Core.GoesWrong escapedLabel [] := ⟨20, rfl⟩

/--
Reading and writing through the host.
```
main = let (_, a) = read() in let (_, b) = read() in write(a + b); write(a * b); a + b
```
With input `3, 4, 5` the program writes 7 then 12, returns 7 and leaves 5 unread.
-/
def io : Core.Program where
  fns := []
  main :=
    .host 1 [] <|
    .let_ (.place ⟨0, [1]⟩) <|
    .host 1 [] <|
    .let_ (.place ⟨2, [1]⟩) <|
    .let_ (.prim .intAdd [.var 1, .var 3]) <|
    .let_ (.prim .intMul [.var 1, .var 3]) <|
    .host 0 [.var 4] <|
    .host 0 [.var 5] <|
    .ret (.var 4)

theorem io_core : Core.Halts io [3, 4, 5] ⟨.int 7, ⟨[5], [.int 7, .int 12]⟩⟩ := ⟨20, rfl⟩

theorem io_bytecode :
    Bytecode.Halts (compile io) [3, 4, 5] ⟨.int 7, ⟨[5], [.int 7, .int 12]⟩⟩ := ⟨20, rfl⟩

/--
Cleanup on an abandoning exit.
```
guarded() = guard { write(1) } { Fail(7) }
main      = handle guarded() { r => r; Fail(e) => write(e); e }
```
The terminal operation abandons the guarded computation. Its cleanup writes 1
before the handler's arm writes 7.
-/
def cleanup : Core.Program where
  fns := [
    ⟨[ ⟨[], .host 0 [.int 1] <| .ret (.var 0)⟩ ]⟩,
    ⟨[ ⟨[], .raise 0 [.int 7]⟩ ]⟩,
    ⟨[ ⟨[.wild], .ret (.var 0)⟩ ]⟩,
    ⟨[ ⟨[.wild], .host 0 [.var 0] <| .ret (.var 0)⟩ ]⟩,
    ⟨[ ⟨[], .let_ (.closure 0 []) <| .let_ (.closure 1 []) <| .guardTail (.var 0) (.var 1)⟩ ]⟩
  ]
  main :=
    .let_ (.closure 4 []) <|
    .handle 2 [(0, 3)] [] (.var 0) <|
    .ret (.var 1)

theorem cleanup_core : Core.Halts cleanup [] ⟨.int 7, ⟨[], [.int 1, .int 7]⟩⟩ := ⟨30, rfl⟩

theorem cleanup_bytecode :
    Bytecode.Halts (compile cleanup) [] ⟨.int 7, ⟨[], [.int 1, .int 7]⟩⟩ := ⟨30, rfl⟩

/--
Memory: allocate a cell, write it, read it, release it.
```
main = let r = alloc(1) in store(r, 5); let v = load(r) in free(r); v
```
-/
def memory : Core.Program where
  fns := []
  main :=
    .mem .alloc [.int 1] <|
    .mem .store [.var 0, .int 5] <|
    .mem .load [.var 0] <|
    .mem .free [.var 0] <|
    .ret (.var 2)

theorem memory_core : Core.Halts memory [] ⟨.int 5, ⟨[], []⟩⟩ := ⟨10, rfl⟩

theorem memory_bytecode : Bytecode.Halts (compile memory) [] ⟨.int 5, ⟨[], []⟩⟩ := ⟨10, rfl⟩

/-- Reading a cell after it has been released has no meaning. -/
def useAfterFree : Core.Program where
  fns := []
  main :=
    .mem .alloc [.int 1] <|
    .mem .free [.var 0] <|
    .mem .load [.var 0] <|
    .ret (.var 2)

theorem useAfterFree_goesWrong : Core.GoesWrong useAfterFree [] := ⟨10, rfl⟩

end Glorious.Witness
