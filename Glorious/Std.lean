module

public import Glorious.Syntax.Ast

/-!
# The standard library

What a program has beyond the prelude, written in the language: the module
`std` and the modules in it, each a file of `library/` read when the
compiler is built (`include_str`; the lakefile has the directory an input
of this module). A program that names `std` has it as a module of its own,
as though those files were beside it. What is written out for each scalar
or each length is written here.
-/

public section

namespace Glorious.Std

/-- `Reflect` for each whole-number scalar: described as its number, set from
a text within its range. -/
private def reflectWhole (t : String) (width : Int) : String :=
  let bits := width.natAbs
  let (lo, hi) : Int × Int := if width < 0 then (0, (2 : Int) ^ bits - 1) else (-((2 : Int) ^ (bits - 1)), (2 : Int) ^ (bits - 1) - 1)
  let lit := fun (n : Int) => if n < 0 then s!"(0 - {-n})" else toString n
  -- (Of one as wide as `Int` or wider: any whole number `Int` holds.)
  let range := if bits >= 64 then "reflect_whole_any(text)" else s!"reflect_whole(text, {lit lo}, {lit hi})"
  s!"impl Reflect for {t} \{
    const INFO: TypeInfo = TypeInfo \{ name: \"{t}\", kind: KindWhole, public: true, variants: Vec::new() };
    fn describe_as(v: &{t}, all: Bool, token: Unchecked) -> Described \{ WholeValue({t}_bits(*v)) }
    fn set_from(v: &mut {t}, path: &str, text: &str, all: Bool, token: Unchecked) -> Result<Described, String> \{
        match({range}) \{ Ok(n) => *v = {t}_of(n); Ok(WholeValue(n)), Err(e) => Err(String::from(e)) }
    }
}
"

private def reflectScalars : String :=
  String.join (Syntax.scalars.filterMap fun (t, w) => w.map (reflectWhole t ·))

private def tupleHeader : String := include_str "../library/std/tuple.glorious"

/-- `std::tuple`: tuples and functions of any length through one form. What
is written for each length is written here, for up to sixteen, so that what a
program writes is written once. -/
private def tupleText : String :=
  let names := ["A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M", "N", "O", "P"]
  let tuple := fun (xs : List String) => match xs with
    | [] => "()"
    | [x] => s!"({x},)"
    | xs => s!"({", ".intercalate xs})"
  let nested := fun (xs : List String) => xs.foldr (fun x rest => s!"({x}, {rest})") "()"
  let one := fun (n : Nat) =>
    let ps := names.take n
    let generics := if ps.isEmpty then "" else s!"<{", ".intercalate ps}>"
    let places := List.range n
    s!"impl{generics} Tuple for {tuple ps} \{
    type Nested = {nested ps};
    fn nest(t: {tuple ps}) -> {nested ps} \{ {nested (places.map fun i => s!"t.{i}")} }
    fn flat(n: {nested ps}) -> {tuple ps} \{ match(n) \{ {nested (places.map (s!"x{·}"))} => {tuple (places.map (s!"x{·}"))} } }
}
impl<{", ".intercalate (ps ++ ["R"])}> Callable for fn({", ".intercalate ps}) -> R \{
    type Args = {nested ps};
    type Output = R;
    fn call_with(f: &fn({", ".intercalate ps}) -> R, args: {nested ps}) -> R \{ match(args) \{ {nested (places.map (s!"x{·}"))} => (*f)({", ".intercalate (places.map (s!"x{·}"))}) } }
}
impl<{", ".intercalate (ps ++ ["TX"])}> Push<TX> for {tuple ps} \{
    type Out = {tuple (ps ++ ["TX"])};
    fn push(t: {tuple ps}, x: TX) -> {tuple (ps ++ ["TX"])} \{ {tuple (places.map (s!"t.{·}") ++ ["x"])} }
}
impl<{", ".intercalate (ps ++ ["TX"])}> Prepend<TX> for {tuple ps} \{
    type Out = {tuple ("TX" :: ps)};
    fn prepend(x: TX, t: {tuple ps}) -> {tuple ("TX" :: ps)} \{ {tuple ("x" :: places.map (s!"t.{·}"))} }
}
{if n == 0 then "" else s!"impl{generics} SplitFirst for {tuple ps} \{
    type First = {ps.headD "A"};
    type Rest = {tuple ps.tail};
    fn split_first(t: {tuple ps}) -> ({ps.headD "A"}, {tuple ps.tail}) \{ (t.0, {tuple ((places.drop 1).map (s!"t.{·}"))}) }
}
"}impl<{", ".intercalate (ps ++ ["TO", "TF"])}> Apply<TF, TO> for {tuple ps} where TF: Fn<{tuple ps}, Output = TO> \{
    fn apply_parts(f: &TF, t: {tuple ps}) -> TO \{ (*f)({", ".intercalate (places.map (s!"t.{·}"))}) }
}
impl<{", ".intercalate (ps ++ ["TO", "TF"])}> ApplyWaiting<TF, TO> for {tuple ps} where TF: Fn<{tuple ps}, Output = TO, Effects = \{std::thread::Threads}> \{
    fn apply_parts_waiting(f: &TF, t: {tuple ps}) -> TO / \{std::thread::Threads} \{ (*f)({", ".intercalate (places.map (s!"t.{·}"))}) }
}
"
  tupleHeader ++ String.join ((List.range 17).map one)

/-- The texts of the library, each with the module it is. -/
def texts : List (List String × String) :=
  [(["std"], include_str "../library/std.glorious"),
   (["std", "option"], include_str "../library/std/option.glorious"),
   (["std", "result"], include_str "../library/std/result.glorious"),
   (["std", "cmp"], include_str "../library/std/cmp.glorious"),
   (["std", "int"], include_str "../library/std/int.glorious"),
   (["std", "char"], include_str "../library/std/char.glorious"),
   (["std", "vec"], include_str "../library/std/vec.glorious"),
   (["std", "text"], include_str "../library/std/text.glorious"),
   (["std", "map"], include_str "../library/std/map.glorious"),
   (["std", "set"], include_str "../library/std/set.glorious"),
   (["std", "iter"], include_str "../library/std/iter.glorious"),
   (["std", "c"], include_str "../library/std/c.glorious"),
   (["std", "fmt"], include_str "../library/std/fmt.glorious"),
   (["std", "stream"], include_str "../library/std/stream.glorious"),
   (["std", "value"], include_str "../library/std/value.glorious"),
   (["std", "generator"], include_str "../library/std/generator.glorious"),
   (["std", "bytes"], include_str "../library/std/bytes.glorious"),
   (["std", "error"], include_str "../library/std/error.glorious"),
   (["std", "index"], include_str "../library/std/index.glorious"),
   (["std", "budget"], include_str "../library/std/budget.glorious"),
   (["std", "parse"], include_str "../library/std/parse.glorious"),
   (["std", "graph"], include_str "../library/std/graph.glorious"),
   (["std", "source"], include_str "../library/std/source.glorious"),
   (["std", "boxed"], include_str "../library/std/boxed.glorious"),
   (["std", "task"], include_str "../library/std/task.glorious"),
   (["std", "path"], include_str "../library/std/path.glorious"),
   (["std", "future"], include_str "../library/std/future.glorious"),
   (["std", "thread"], include_str "../library/std/thread.glorious"),
   (["std", "any"], include_str "../library/std/any.glorious"),
   (["alloc", "boxed"], include_str "../library/alloc/boxed.glorious"),
   (["std", "iterator"], include_str "../library/std/iterator.glorious"),
   (["std", "slice"], include_str "../library/std/slice.glorious"),
   (["std", "collections"], include_str "../library/std/collections.glorious"),
   (["std", "host"], include_str "../library/std/host.glorious"),
   (["std", "hash"], include_str "../library/std/hash.glorious"),
   -- The names the library specification gives its modules (1.2): the same
   -- declarations, under `core`, `alloc` and more of `std`.
   (["std", "io"], include_str "../library/std/io.glorious"),
   (["std", "fs"], include_str "../library/std/fs.glorious"),
   (["std", "env"], include_str "../library/std/env.glorious"),
   (["std", "time"], include_str "../library/std/time.glorious"),
   (["std", "random"], include_str "../library/std/random.glorious"),
   (["std", "tuple"], tupleText),
   (["std", "ffi"], include_str "../library/std/ffi.glorious"),
   (["std", "ptr"], include_str "../library/std/ptr.glorious"),
   (["std", "reflect"], (include_str "../library/std/reflect.glorious") ++ reflectScalars),
   (["core"], include_str "../library/core.glorious"),
   (["core", "value"], include_str "../library/core/value.glorious"),
   (["core", "option"], include_str "../library/core/option.glorious"),
   (["core", "result"], include_str "../library/core/result.glorious"),
   (["core", "cmp"], include_str "../library/core/cmp.glorious"),
   (["core", "num"], include_str "../library/core/num.glorious"),
   (["core", "char"], include_str "../library/core/char.glorious"),
   (["core", "iter"], include_str "../library/core/iter.glorious"),
   (["core", "slice"], include_str "../library/core/slice.glorious"),
   (["core", "hash"], include_str "../library/core/hash.glorious"),
   (["alloc"], include_str "../library/alloc.glorious"),
   (["alloc", "fmt"], include_str "../library/alloc/fmt.glorious"),
   (["alloc", "vec"], include_str "../library/alloc/vec.glorious"),
   (["alloc", "string"], include_str "../library/alloc/string.glorious"),
   (["alloc", "collections"], include_str "../library/alloc/collections.glorious"),
   (["alloc", "collections", "map"], include_str "../library/alloc/collections/map.glorious"),
   (["alloc", "collections", "set"], include_str "../library/alloc/collections/set.glorious"),
   -- (A text added to the library goes last: the places of those before it
   -- are in what is compiled of every program that names the library.)
   (["std", "fingerprint"], include_str "../library/std/fingerprint.glorious"),
   (["std", "diagnostic"], include_str "../library/std/diagnostic.glorious"),
   (["alloc", "fingerprint"], include_str "../library/alloc/fingerprint.glorious")]

end Glorious.Std
