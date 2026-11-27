module

/-!
# Where a compile spends its time

`GLORIOUS_TRACE` set, each stage a compile goes through is timed, nested
stages inside the stages they are part of, and `report` writes them out when
the compile is done: what each took, and how many times it ran. Unset, a
stage is only the computation it times.

`timed` can be used in pure code: the compiler is strict, so the stage is
computed between the two readings of the clock. Stages that run on threads
of their own are each timed on theirs; what they add up to can then be more
than the time that passed.
-/

@[expose] public section

namespace Glorious.Trace

/-- One stage that ran: its name, how deep inside others, and its time. -/
structure Span where
  name : String
  depth : Nat
  nanos : Nat

initialize enabled : Bool ← do pure (← IO.getEnv "GLORIOUS_TRACE").isSome
/-- `GLORIOUS_TRACE=groups`: each group of functions named on standard error as
its check starts, to see where a compile that does not end is. -/
initialize groupsTraced : Bool ← do pure ((← IO.getEnv "GLORIOUS_TRACE") == some "groups")
/-- `GLORIOUS_TRACE=types`: a program's Core and the signatures `Typer` found
for it, on standard error. -/
initialize typesTraced : Bool ← do pure ((← IO.getEnv "GLORIOUS_TRACE") == some "types")

initialize spans : IO.Ref (Array Span) ← IO.mkRef #[]
initialize depth : IO.Ref Nat ← IO.mkRef 0

/-- Time an action. -/
def timedIO {α : Type} (name : String) (act : IO α) (said : Bool := true) : IO α := do
  if groupsTraced && said then
    let t0 ← IO.monoNanosNow
    IO.eprintln s!"stage {name}..."
    let r ← act
    IO.eprintln s!"stage {name}: {((← IO.monoNanosNow) - t0) / 1000000} ms"
    return r
  if !enabled then return ← act
  let d ← depth.get
  depth.set (d + 1)
  let t0 ← IO.monoNanosNow
  let r ← act
  let t1 ← IO.monoNanosNow
  depth.set d
  spans.modify (·.push ⟨name, d, t1 - t0⟩)
  pure r

@[noinline] unsafe def timedImpl {α : Type} (name : String) (f : Unit → α) : α :=
  if !enabled then f () else
  match unsafeBaseIO (timedIO name (IO.lazyPure f) (said := false)).toBaseIO with
  | .ok r => r
  | .error _ => f ()

@[noinline] unsafe def clockImpl {β : Type} (x : β) : Nat × β :=
  if !enabled then (0, x) else
  match unsafeBaseIO (do
    depth.modify (· + 1)
    IO.monoNanosNow : IO Nat).toBaseIO with
  | .ok t => (t, x)
  | .error _ => (0, x)

/-- The clock, read before `x` is used again: a stage that `span` ends
starts here. Unlike `timed`, nothing holds what the stage computes from
while it runs: a state passed through it stays the only one, and is changed
in place, as it is untraced. -/
@[implemented_by clockImpl] def clock {β : Type} (x : β) : Nat × β := (0, x)

@[noinline] unsafe def spanImpl {β : Type} (name : String) (t0 : Nat) (x : β) : β :=
  if !enabled then x else
  match unsafeBaseIO (do
    let t1 ← IO.monoNanosNow
    depth.modify (· - 1)
    let d ← depth.get
    spans.modify (·.push ⟨name, d, t1 - t0⟩) : IO Unit).toBaseIO with
  | _ => x

/-- The stage that started at `clock`'s `t0` ends with `x` computed. -/
@[implemented_by spanImpl] def span {β : Type} (_name : String) (_t0 : Nat) (x : β) : β := x

/-- Time a computation. -/
@[implemented_by timedImpl] def timed {α : Type} (name : String) (f : Unit → α) : α := f ()

@[noinline] unsafe def saidImpl {α : Type} (name : String) (f : Unit → α) : α :=
  if !groupsTraced then f () else
  let io : IO α := do
    let t0 ← IO.monoNanosNow
    let r ← IO.lazyPure f
    let t1 ← IO.monoNanosNow
    IO.eprintln s!"  {name}: {(t1 - t0) / 1000000} ms"
    pure r
  match unsafeBaseIO io.toBaseIO with
  | Except.ok r => r
  | Except.error _ => f ()

/-- Time a computation and say it at once, under `GLORIOUS_TRACE=groups`. -/
@[implemented_by saidImpl] def said {α : Type} (name : String) (f : Unit → α) : α := f ()

/-- Write out what was timed: each stage under the one it was part of, in
the order they ended; and then, for each name, its total and how many times
it ran. -/
def report : IO Unit := do
  if !enabled then return
  let all ← spans.get
  let err ← IO.getStderr
  let ms := fun (n : Nat) =>
    let tenths := n / 100000
    s!"{tenths / 10}.{tenths % 10} ms"
  err.putStrLn "-- stages, innermost first (four levels deep) --"
  for s in all do
    if s.depth < 4 then
      err.putStrLn s!"{String.ofList (List.replicate (2 * s.depth) ' ')}{s.name}: {ms s.nanos}"
  err.putStrLn "-- totals --"
  let mut totals : Array (String × Nat × Nat) := #[]
  for s in all do
    match totals.findIdx? (·.1 == s.name) with
    | some i => totals := totals.modify i fun (n, t, c) => (n, t + s.nanos, c + 1)
    | none => totals := totals.push (s.name, s.nanos, 1)
  for (n, t, c) in totals.qsort (fun a b => a.2.1 > b.2.1) do
    err.putStrLn s!"{n}: {ms t}{if c > 1 then s!" ({c} times)" else ""}"
  spans.set #[]

end Glorious.Trace
