module

public import Glorious.Syntax.Ast

/-!
# The prelude

Written in Glorious, in the files of `library/prelude/`, read when the
compiler is built (`include_str`), as the library's are (`Glorious.Std`); what
is written out for each scalar type and array length is written here. None
of these names is known to the compiler: conditionals,
matching, boolean operators, arithmetic operators and loops are ordinary
functions over the kernel.

Arithmetic and comparison are traits, which the checker resolves. A program
run without the checker has no traits, so for it there is a second prelude in
which the operators are `Int`'s alone.
-/

public section

namespace Glorious.Prelude

private def core : String := include_str "../library/prelude/core.glorious"

/-- The machine's operations, each with its type. -/
private def intrinsics : String := include_str "../library/prelude/intrinsics.glorious"

/-- The operators as traits, with what `Int` has of them. -/
private def operators : String := include_str "../library/prelude/operators.glorious"

/-- The operators of `Int` alone: for a program that is not checked. -/
private def intOperators : String := include_str "../library/prelude/int_operators.glorious"

private def world : String := include_str "../library/prelude/world.glorious"

/-- What a type of whole numbers has: `Int`'s operations, each result asked to
fit the type's width; and the way in from an `Int`, which asks the same. A
type of 64 bits or more computes within 128, so that a result too large for
it is seen to be. -/
private def wholeNumber (t : String) (width : Int) : String :=
  let wide := width.natAbs ≥ 64
  let op := fun (prim : String) =>
    "{ " ++ s!"{t}_of(int_fit({prim}({t}_bits(a), {t}_bits(b)), {width}))" ++ " }"
  let add := if wide then "wide_add" else "int_add"
  let sub := if wide then "wide_sub" else "int_sub"
  let mul := if wide then "wide_mul" else "int_mul"
  let test := fun (e : String) => "{ " ++ e ++ " }"
  s!"
impl Add for {t} \{ fn +(a: {t}, b: {t}) -> {t} {op add} }
impl Sub for {t} \{ fn -(a: {t}, b: {t}) -> {t} {op sub} }
impl Mul for {t} \{ fn *(a: {t}, b: {t}) -> {t} {op mul} }
impl Div for {t} \{ fn /(a: {t}, b: {t}) -> {t} {op "int_div"} }
impl Rem for {t} \{ fn %(a: {t}, b: {t}) -> {t} {op "int_rem"} }
impl Neg for {t} \{ fn negate(a: {t}) -> {t} {test s!"{t}_of(int_fit(wide_sub(0, {t}_bits(a)), {width}))"} }
impl Eq for {t} \{ fn ==(a: {t}, b: {t}) -> Bool {test s!"bool(int_eq({t}_bits(a), {t}_bits(b)))"} }
impl Ord for {t} \{ fn <(a: {t}, b: {t}) -> Bool {test s!"bool(int_lt({t}_bits(a), {t}_bits(b)))"} }
impl Bits for {t} \{
    fn bit_and(a: {t}, b: {t}) -> {t} {test s!"{t}_of(int_and({t}_bits(a), {t}_bits(b)))"}
    fn bit_or(a: {t}, b: {t}) -> {t} {test s!"{t}_of(int_or({t}_bits(a), {t}_bits(b)))"}
    fn bit_xor(a: {t}, b: {t}) -> {t} {test s!"{t}_of(int_xor({t}_bits(a), {t}_bits(b)))"}
    fn shl(a: {t}, n: Int) -> {t} {test s!"{t}_of(int_fit(int_shl({t}_bits(a), n), {width}))"}
    fn shr(a: {t}, n: Int) -> {t} {test s!"{t}_of(int_shr({t}_bits(a), n))"}
}
impl ToInt for {t} \{ fn int(x: {t}) -> Int {test s!"int_fit({t}_bits(x), 64)"} }
impl Whole for {t} \{
    fn whole(x: {t}) -> i128 {test s!"i128_of({t}_bits(x))"}
    fn of_whole(n: i128) -> {t} {test s!"{t}_of(int_fit(i128_bits(n), {width}))"}
}
impl Show for {t} \{ fn show(x: {t}) -> Str {test s!"show_whole({t}_bits(x))"} }
fn {t}(n: Int) -> {t} {test s!"{t}_of(int_fit(n, {width}))"}
"

/-- 128 bits without a sign: held as the same bits with one, so its
arithmetic and its order are the machine's operations that read them so. -/
private def unsigned128 : String :=
  let t := "u128"
  let op := fun (prim : String) => "{ " ++ s!"{t}_of({prim}({t}_bits(a), {t}_bits(b)))" ++ " }"
  let test := fun (e : String) => "{ " ++ e ++ " }"
  s!"
impl Add for {t} \{ fn +(a: {t}, b: {t}) -> {t} {op "uw_add"} }
impl Sub for {t} \{ fn -(a: {t}, b: {t}) -> {t} {op "uw_sub"} }
impl Mul for {t} \{ fn *(a: {t}, b: {t}) -> {t} {op "uw_mul"} }
impl Div for {t} \{ fn /(a: {t}, b: {t}) -> {t} {op "uw_div"} }
impl Rem for {t} \{ fn %(a: {t}, b: {t}) -> {t} {op "uw_rem"} }
impl Eq for {t} \{ fn ==(a: {t}, b: {t}) -> Bool {test s!"bool(int_eq({t}_bits(a), {t}_bits(b)))"} }
impl Ord for {t} \{ fn <(a: {t}, b: {t}) -> Bool {test s!"bool(uw_lt({t}_bits(a), {t}_bits(b)))"} }
impl Bits for {t} \{
    fn bit_and(a: {t}, b: {t}) -> {t} {op "int_and"}
    fn bit_or(a: {t}, b: {t}) -> {t} {op "int_or"}
    fn bit_xor(a: {t}, b: {t}) -> {t} {op "int_xor"}
    fn shl(a: {t}, n: Int) -> {t} {test s!"{t}_of(uw_shl({t}_bits(a), n))"}
    fn shr(a: {t}, n: Int) -> {t} {test s!"{t}_of(uw_shr({t}_bits(a), n))"}
}
impl ToInt for {t} \{ fn int(x: {t}) -> Int {test s!"int_fit({t}_bits(x), -63)"} }
impl Whole for {t} \{
    fn whole(x: {t}) -> i128 {test s!"i128_of(int_fit({t}_bits(x), -127))"}
    fn of_whole(n: i128) -> {t} {test s!"{t}_of(int_fit(i128_bits(n), -127))"}
}
impl Show for {t} \{ fn show(x: {t}) -> Str {test s!"unsigned_digits({t}_bits(x), StrEnd)"} }
fn {t}(n: Int) -> {t} {test s!"{t}_of(int_fit(n, -63))"}
"

/-- Each scalar type's way in from the `Int` it is held as, and out. -/
private def casts : String :=
  String.join (Syntax.scalars.map fun (t, _) =>
    s!"#[intrinsic] fn {t}_of(n: Int) -> {t};\n#[intrinsic] fn {t}_bits(x: {t}) -> Int;\n")

/-- Each scalar type in memory (`Repr`): its bits, so many of them, with a
sign where the type has one. -/
private def scalarReprs : String :=
  String.join (Syntax.scalars.map fun (t, w) =>
    let width : Int := w.getD (if t == "f64" then -64 else -32)
    s!"impl Repr for {t} \{ unsafe fn repr_store(at: usize, value: {t}) \{ ptr_write(at, {width}, {t}_bits(value)) } unsafe fn repr_load(at: usize) -> {t} \{ {t}_of(ptr_read(at, {width})) } }\n")

/-- The scalar types: what each has. -/
private def scalars : String :=
  (include_str "../library/prelude/scalars.glorious") ++ String.join ((Syntax.scalars.filterMap fun (t, width) => width.map fun w =>
    if w == -128 then unsigned128 else wholeNumber t w))

/-- A `[T; N]` as a tuple of its elements, for each length up to eight: what
`let [a, b, c] = xs` takes `xs` apart with. Written out for each length,
since a length is a type and a tuple of so many is another. -/
private def fixedElements : String :=
  let number := fun (n : Nat) =>
    let rec bits (fuel k : Nat) : String :=
      match fuel, k with
      | _, 0 => "Z"
      | 0, _ => "Z"
      | fuel + 1, k => (if k % 2 == 0 then "B0<" else "B1<") ++ bits fuel (k / 2) ++ ">"
    bits 64 n
  let one := fun (n : Nat) =>
    let places := List.range n
    let tuple := fun (xs : List String) => match xs with
      | [] => "()"
      | [x] => s!"({x},)"
      | xs => s!"({", ".intercalate xs})"
    -- (The last element comes off first.)
    let pops := places.reverse.map fun i =>
      s!"let (r{i}, x{i}) = arr_pop({if i + 1 == n then "a.0" else s!"r{i + 1}"}, 0); "
    s!"impl<T> Elements for Fixed<T, {number n}> \{
    type Each = {tuple (places.map fun _ => "T")};
    fn elements(a: Fixed<T, {number n}>) -> {tuple (places.map fun _ => "T")} \{ {String.join pops}{tuple (places.map fun i => s!"x{i}")} }
}
"
  "
// A `[T; N]` as a tuple of its elements: `let [a, b, c] = xs`.
trait Elements { type Each; fn elements(Self) -> Each }
" ++ String.join ((List.range 9).map one)


private def layouts : String := include_str "../library/prelude/layouts.glorious"

def source : String := intrinsics ++ casts ++ core ++ operators ++ scalars ++ world ++ fixedElements ++ layouts ++ scalarReprs

/-- The prelude of a program run without the checker. -/
def unchecked : String := intrinsics ++ casts ++ core ++ intOperators ++ world


end Glorious.Prelude
