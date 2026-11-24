module

public import Glorious.Lay
public import Glorious.Typing.Checker
public import Glorious.Typing.Certify

/-!
# The layout of a Core type

What a value of a type is in memory (`Lay`), from its type as the
certificate has it: Rust's layout, as the library's `Layout` writes it out
for a type from its declaration (`Syntax.Flat.writeLayouts`), so that the
two say the same size of every type.

- `Int` is 8 bytes with a sign, a scalar its bits' bytes (`Ty.scalar`).
- A tuple, or a type of one constructor, is its fields one after another,
  each at its alignment; a type of several constructors is a tag byte and
  then the fields of the one it is, from after the tag.
- A reference is an address.
- What is not bytes yet is held by the machine (`Lay.held`): a callable (16
  bytes, as `Layout` says), an array (24), and a type that holds itself
  where it does (8).
-/

@[expose] public section

namespace Glorious.Lower

open Typing

/-- The declared types a value of a type holds within its bytes, `seen` those
already found. -/
partial def heldWithin (C : Cert) (seen : List (Nat × List Ty)) : Ty → List (Nat × List Ty)
  | .tuple fs => fs.foldl (heldWithin C) seen
  | .data name args =>
    if name == arrayName || seen.contains (name, args) then seen
    else match findData C.datas name args with
      | some ctors => ctors.foldl (fun s (_, fs) => fs.foldl (heldWithin C) s) ((name, args) :: seen)
      | none => seen
  | _ => seen

/-- Whether a value of the declared type would hold one of itself in its bytes:
held by the machine wherever it is, so that a reference to one is to the same
bytes whatever it is reached through. -/
def holdsItself (C : Cert) (name : Nat) (args : List Ty) : Bool :=
  match findData C.datas name args with
  | some ctors => (ctors.foldl (fun s (_, fs) => fs.foldl (heldWithin C) s) []).contains (name, args)
  | none => false

/-- The layout of a type, `seen` the declared types it is inside of. -/
partial def layOf (C : Cert) (seen : List (Nat × List Ty)) : Ty → Laid
  | .int => ⟨.int 8 true, 8, 8⟩
  | .scalar b =>
    let n := b.natAbs / 8
    ⟨.int n (0 < b), n, n⟩
  | .tuple fs =>
    let (at_, size, align) := placeFields 0 (fs.map (layOf C seen))
    ⟨.fields 0 at_, alignUp size align, align⟩
  | .data name args =>
    if name == arrayName then ⟨.held, 24, 8⟩
    -- (A `[T; N]`: its elements one after another, inline.)
    else if name == fixedName then
      match args with
      | [t, .data len []] =>
        let n := len - lenBase
        let (at_, size, align) := placeFields 0 (List.replicate n (layOf C seen t))
        ⟨.fields (fixedBase + n) at_, alignUp size align, align⟩
      | _ => ⟨.held, 8, 8⟩
    else if name == anyName then ⟨.held, 8, 8⟩
    else if seen.contains (name, args) || holdsItself C name args then ⟨.held, 8, 8⟩
    else
      match findData C.datas name args with
      | some [(tag, fs)] =>
        let (at_, size, align) := placeFields 0 (fs.map (layOf C ((name, args) :: seen)))
        ⟨.fields tag at_, alignUp size align, align⟩
      | some ctors =>
        let each := ctors.map fun (tag, fs) => (tag, placeFields 1 (fs.map (layOf C ((name, args) :: seen))))
        let size := each.foldl (fun s (_, (_, sz, _)) => max s sz) 1
        let align := each.foldl (fun a (_, (_, _, al)) => max a al) 1
        ⟨.tagged (each.map fun (tag, (at_, _, _)) => (tag, at_)), alignUp size align, align⟩
      | none => ⟨.held, 8, 8⟩
  | .fn .. => ⟨.held, 16, 8⟩
  | .ref _ _ => ⟨.addr, 8, 8⟩
  | .never => ⟨.nothing, 0, 1⟩

end Glorious.Lower
