import Glorious.Proof.Correct

/-!
# Non-vacuity witness

`compile_correct` would hold trivially if the Core semantics gave no program a
meaning. This file exhibits one program using every construct, including a
recursive callable that branches on its argument and a nested pattern, and
checks in the kernel that both machines run it to the same result.
-/

namespace Glorious.Witness

/--
```
sum(0, acc)        = acc
sum(n, acc)        = tail sum(n - 1, acc + n)
first(Pair(Some(x), _)) = x
first(Pair(None,    _)) = 0
main               = tail first(Pair(Some(sum(4, 0)), 9))
```
`Pair` has tag 0; `Some` has tag 0 and `None` tag 1.
-/
def program : Core.Program where
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

theorem core_halts : Core.Halts program (.int 10) := ⟨40, rfl⟩

theorem bytecode_halts : Bytecode.Halts (compile program) (.int 10) := ⟨80, rfl⟩

end Glorious.Witness
