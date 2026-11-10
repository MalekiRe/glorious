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

theorem patterns_core : Core.Halts patterns (.int 10) := ⟨40, rfl⟩

theorem patterns_bytecode : Bytecode.Halts (compile patterns) (.int 10) := ⟨80, rfl⟩

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

theorem effects_core : Core.Halts effects (.int 65) := ⟨60, rfl⟩

theorem effects_bytecode : Bytecode.Halts (compile effects) (.int 65) := ⟨60, rfl⟩

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

theorem resumeTwice_goesWrong : Core.GoesWrong resumeTwice := ⟨20, rfl⟩

end Glorious.Witness
