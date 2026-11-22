import Lake
open Lake DSL

/-- `lake build -R -Kfast=1 glorious`: the C is not optimized at all, for
editing the compiler: a change to its largest files is built in seconds, and
the compiler that comes out runs slower still. `lake build -R -Kquick=1 glorious`: the C that Lean writes is compiled with
the cheap code generator, for trying a change: the largest files then take
half the time or less, and the compiler that comes out runs at a little over
half the speed. Frame pointers are kept, so that `perf record -g` can say
who calls what. `-Kprof=1`: the build as it is, with frame pointers kept, for
a profile that says where the time of the compiler as it is goes (one of the
quick build is of a compiler whose loops are slower than they are). Without it, the build is the one to use (`lake build -R
glorious` after a quick one: `-R` is what has the option read again). -/
def quickArgs : Array String :=
  if (get_config? fast).isSome then #["-O0", "-fno-omit-frame-pointer"]
  else if (get_config? quick).isSome then
    #["-O1", "-mllvm", "-fast-isel", "-mllvm", "-optimize-regalloc=0", "-fno-omit-frame-pointer"]
  else if (get_config? prof).isSome then #["-fno-omit-frame-pointer"]
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
