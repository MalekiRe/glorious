import Lake
open Lake DSL

/-- `lake build -Kquick=1 glorious`: the C that Lean writes is compiled with
the cheap code generator, for trying a change: the largest files then take
half the time or less, and the compiler that comes out runs at a little over
half the speed. Frame pointers are kept, so that `perf record -g` can say
who calls what. Without it, the build is the one to use. -/
def quickArgs : Array String :=
  if (get_config? quick).isSome then
    #["-O1", "-mllvm", "-fast-isel", "-mllvm", "-optimize-regalloc=0", "-fno-omit-frame-pointer"]
  else #[]

package glorious where
  version := v!"0.1.0"
  moreLeanArgs := #["-DwarningAsError=true", "-DautoImplicit=false"]
  moreLeancArgs := quickArgs

@[default_target]
lean_lib Glorious

@[default_target]
lean_exe glorious where
  root := `Main
