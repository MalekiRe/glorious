import Glorious.Proof.Correct

/-!
# Non-vacuity witness

`compile_correct` would hold trivially if the Core semantics gave no program a
meaning. This file exhibits one program using every construct, and checks in
the kernel that both machines run it to the same result.
-/

namespace Glorious.Witness

open Core (Tm)

/--
```
add1(x)        = x + 1
twice[f](x)    = tail f(f(x))
main           = let p = (twice[add1](5), 9) in p.0
```
-/
def program : Core.Program where
  fns := [
    ⟨1, .let_ (.prim .intAdd [.var 0, .int 1]) (.ret (.var 1))⟩,
    ⟨1, .call (.var 0) [.var 1] (.tail (.var 0) [.var 2])⟩
  ]
  main :=
    .let_ (.closure 0 []) <|
    .let_ (.closure 1 [.var 0]) <|
    .call (.var 1) [.int 5] <|
    .let_ (.construct 0 [.var 2, .int 9]) <|
    .let_ (.project (.var 3) 0) <|
    .ret (.var 4)

theorem core_halts : Core.Halts program (.int 7) := ⟨12, rfl⟩

theorem bytecode_halts : Bytecode.Halts (compile program) (.int 7) := ⟨12, rfl⟩

end Glorious.Witness
