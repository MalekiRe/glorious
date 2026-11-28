module

public import Glorious.Lay
public import Glorious.Lower.Types

/-!
# The layout of a Core type

What a value of a type is in memory (`Lay`), from its type as the
types have it: Rust's layout. What a program asks of a type's size and
alignment (`size_of<T>()`, `align_of<T>()`) and what it writes to memory
and reads back (`repr_store`, `repr_load`) are this layout, of the type
at each copy (`FnSig.targs`).

- `Int` is 8 bytes with a sign, a scalar its bits' bytes (`Ty.scalar`).
- A tuple, or a type of one constructor, is its fields one after another,
  each at its alignment; a type of several constructors is a tag byte and
  then the fields of the one it is, from after the tag.
- A reference is an address.
- What is not bytes yet is held by the machine (`Lay.held`): a callable (16
  bytes, as `Layout` says), and a type that holds itself where it does (8).
-/

@[expose] public section

namespace Glorious.Lower

/-- The declared types a value of a type holds within its bytes, `seen` those
already found. -/
partial def heldWithin (C : Types) (seen : List (Nat × List Ty)) : Ty → List (Nat × List Ty)
  | .tuple fs => fs.foldl (heldWithin C) seen
  | .data name args =>
    if seen.contains (name, args) then seen
    else match findData C.datas name args with
      | some ctors => ctors.foldl (fun s (_, fs) => fs.foldl (heldWithin C) s) ((name, args) :: seen)
      | none => seen
  | _ => seen

/-- Whether a value of the declared type would hold one of itself in its bytes:
held by the machine wherever it is, so that a reference to one is to the same
bytes whatever it is reached through. -/
def holdsItself (C : Types) (name : Nat) (args : List Ty) : Bool :=
  match findData C.datas name args with
  | some ctors => (ctors.foldl (fun s (_, fs) => fs.foldl (heldWithin C) s) []).contains (name, args)
  | none => false

/-- What the lowering has worked out of types, each once: a type's layout,
and whether a declared type at its arguments holds itself. -/
structure LayCache where
  lays : Std.HashMap Ty Laid := {}
  holds : Std.HashMap (Nat × List Ty) Bool := {}

/-- Why a program is not lowered, or what it is lowered to; with what was
worked out of types on the way. -/
abbrev L := StateT LayCache (Except String)

/-- `holdsItself`, worked out once for each declared type at its arguments. -/
def holdsM (C : Types) (name : Nat) (args : List Ty) : L Bool := do
  if let some h := (← get).holds[(name, args)]? then return h
  let h := holdsItself C name args
  modify fun c => { c with holds := c.holds.insert (name, args) h }
  pure h

/-- The layout of a type, each worked out once. (A declared type that holds
itself is held by the machine; one that does not reaches no cycle, so each
is a matter of its name and arguments alone.) -/
partial def layOf (C : Types) (t : Ty) : L Laid := do
  if let some l := (← get).lays[t]? then return l
  let l ← match t with
    | .int => pure ⟨.int 8 true, 8, 8⟩
    | .scalar b => let n := b.natAbs / 8; pure ⟨.int n (0 < b), n, n⟩
    | .tuple fs =>
      let (at_, size, align) := placeFields 0 (← fs.mapM (layOf C))
      pure ⟨.fields 0 at_, alignUp size align, align⟩
    | .data name args =>
      -- (A `[T; N]`: its elements one after another, inline.)
      if name == fixedName then
        match args with
        | [t, .data len []] =>
          let n := len - lenBase
          let e ← layOf C t
          let (at_, size, align) := placeFields 0 (List.replicate n e)
          pure ⟨.fields (fixedBase + n) at_, alignUp size align, align⟩
        | _ => pure ⟨.held, 8, 8⟩
      else if name == anyName || (← holdsM C name args) then pure ⟨.held, 8, 8⟩
      else
        match findData C.datas name args with
        | some [(tag, fs)] =>
          let (at_, size, align) := placeFields 0 (← fs.mapM (layOf C))
          pure ⟨.fields tag at_, alignUp size align, align⟩
        | some ctors =>
          let each ← ctors.mapM fun (tag, fs) => do pure (tag, placeFields 1 (← fs.mapM (layOf C)))
          let size := each.foldl (fun s (_, (_, sz, _)) => max s sz) 1
          let align := each.foldl (fun a (_, (_, _, al)) => max a al) 1
          pure ⟨.tagged (each.map fun (tag, (at_, _, _)) => (tag, at_)), alignUp size align, align⟩
        | none => pure ⟨.held, 8, 8⟩
    | .fn .. => pure ⟨.held, 16, 8⟩
    | .ref _ => pure ⟨.addr, 8, 8⟩
    | .never => pure ⟨.nothing, 0, 1⟩
  modify fun c => { c with lays := c.lays.insert t l }
  pure l

end Glorious.Lower
