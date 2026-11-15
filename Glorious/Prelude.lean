module

public import Glorious.Syntax.Ast

/-!
# The prelude

Written in Glorious. None of these names is known to the compiler: conditionals,
matching, boolean operators, arithmetic operators and loops are ordinary
functions over the kernel.

Arithmetic and comparison are traits, which the checker resolves. A program
run without the checker has no traits, so for it there is a second prelude in
which the operators are `Int`'s alone.
-/

public section

namespace Glorious.Prelude

private def core : String := r#"
enum Result<T, E> { Ok(T), Err(E) }

// Truth is success. `Option<T>` is `Result<T, ()>` and `Bool` is `Option<()>`.
type Option<T> = Result<T, ()>;
type Bool = Result<(), ()>;
let Some: fn(_) -> Result<_, ()> = Ok;
let None = Err(());
let true: Result<(), ()> = Ok(());
let false: Result<(), ()> = Err(());

// Matching is applying a pattern callable.
fn match(subject, arms) { tail arms(subject) }

// `if` gives the result of its body on success, and gives the body what the
// test found: nothing, for a comparison; for `value is Pattern`, what the
// pattern's names stand for, which a block then has under those names. On
// failure it gives the body back: it was not run, so whatever it captured is
// still there to be used.
fn if(condition, body) {
    match(condition) {
        Ok(found) => Ok(body(found)),
        Err(_) => Err(body)
    }
}

// `else` unwraps success, and on failure gives what failed to its fallback. A
// fallback written as a plain block after an `if` is thereby given the body
// that was not run, and runs in its place.
infixr 1 else
fn else(value, fallback) {
    match(value) {
        Ok(result) => result,
        Err(failure) => tail fallback(failure)
    }
}

// Any failure can be forgotten: a `Result` is an `Option` wherever one is
// expected, and what failed is dropped.
coerce option
fn option(value) {
    match(value) {
        Ok(result) => Ok(result),
        Err(_) => None
    }
}

// The right operands of `and` and `or` are callables, run only when needed.
// That of `and` is given what the left one found, as the body of an `if` is.
infixl 3 and
fn and(left, right) {
    match(left) {
        Ok(found) => tail right(found),
        Err(error) => Err(error)
    }
}

// `or` gives what failed to its right operand, as `else` does: after an `if`
// that is the body that was not run, and a plain block runs in its place. So
// `if(a) { .. } or { if(b) { .. } } else { .. }` is a chain of alternatives
// over what the first body captured.
infixl 2 or
fn or(left, right) {
    match(left) {
        Ok(value) => Ok(value),
        Err(failure) => tail right(failure)
    }
}

prefix 8 not
fn not(value) {
    match(value) {
        Ok(payload) => Err(payload),
        Err(payload) => Ok(payload)
    }
}

"#

/-- The operators as traits, with what `Int` has of them. -/
private def operators : String := r#"
// Arithmetic and comparison are traits, so that every type of number has
// them; `Int` and the scalar types do, below.
infixl 6 +
infixl 6 -
infixl 7 *
infixl 7 /
infixl 7 %
trait Add { fn +(Self, Self) -> Self }
trait Sub { fn -(Self, Self) -> Self }
trait Mul { fn *(Self, Self) -> Self }
trait Div { fn /(Self, Self) -> Self }
trait Rem { fn %(Self, Self) -> Self }
// `-` before a value is `negate`; between two it is the `-` above.
prefix 9 - = negate
trait Neg { fn negate(Self) -> Self }
// The bits of a whole number; `shl` and `shr` move them up and down.
trait Bits {
    fn bit_and(Self, Self) -> Self
    fn bit_or(Self, Self) -> Self
    fn bit_xor(Self, Self) -> Self
    fn shl(Self, Int) -> Self
    fn shr(Self, Int) -> Self
}

fn bool {
    0 => false,
    _ => true
}

infix 4 <
infix 4 >
infix 4 <=
infix 4 >=
infix 4 ==
infix 4 !=
// A type says what `==` and `<` are; the rest follow, unless it says them too.
trait Eq {
    fn ==(Self, Self) -> Bool
    fn !=(a: Self, b: Self) -> Bool { not (a == b) }
}
trait Ord: Eq {
    fn <(Self, Self) -> Bool
    fn >(a: Self, b: Self) -> Bool { b < a }
    fn <=(a: Self, b: Self) -> Bool { not (b < a) }
    fn >=(a: Self, b: Self) -> Bool { not (a < b) }
}

impl Add for Int { fn +(a, b) { int_add(a, b) } }
impl Sub for Int { fn -(a, b) { int_sub(a, b) } }
impl Mul for Int { fn *(a, b) { int_mul(a, b) } }
impl Div for Int { fn /(a, b) { int_fit(int_div(a, b), 64) } }
impl Rem for Int { fn %(a, b) { int_rem(a, b) } }
impl Neg for Int { fn negate(a) { int_sub(0, a) } }
impl Bits for Int {
    fn bit_and(a, b) { int_and(a, b) }
    fn bit_or(a, b) { int_or(a, b) }
    fn bit_xor(a, b) { int_xor(a, b) }
    fn shl(a, n) { int_fit(int_shl(a, n), 64) }
    fn shr(a, n) { int_shr(a, n) }
}
impl Eq for Int {
    fn ==(a, b) { bool(int_eq(a, b)) }
    fn !=(a, b) { not bool(int_eq(a, b)) }
}
impl Ord for Int {
    fn <(a, b) { bool(int_lt(a, b)) }
    fn >(a, b) { bool(int_lt(b, a)) }
    fn <=(a, b) { not bool(int_lt(b, a)) }
    fn >=(a, b) { not bool(int_lt(a, b)) }
}

"#

/-- The operators of `Int` alone: for a program that is not checked. -/
private def intOperators : String := r#"
infixl 6 +
infixl 6 -
infixl 7 *
infixl 7 /
infixl 7 %
fn +(a, b) { int_add(a, b) }
fn -(a, b) { int_sub(a, b) }
fn *(a, b) { int_mul(a, b) }
fn /(a, b) { int_div(a, b) }
fn %(a, b) { int_rem(a, b) }
prefix 9 - = negate
fn negate(a) { int_sub(0, a) }
fn bit_and(a, b) { int_and(a, b) }
fn bit_or(a, b) { int_or(a, b) }
fn bit_xor(a, b) { int_xor(a, b) }
fn shl(a, n) { int_fit(int_shl(a, n), 64) }
fn shr(a, n) { int_shr(a, n) }

fn bool {
    0 => false,
    _ => true
}

infix 4 <
infix 4 >
infix 4 <=
infix 4 >=
infix 4 ==
infix 4 !=
fn <(a, b) { bool(int_lt(a, b)) }
fn >(a, b) { bool(int_lt(b, a)) }
fn <=(a, b) { not bool(int_lt(b, a)) }
fn >=(a, b) { not bool(int_lt(a, b)) }
fn ==(a, b) { bool(int_eq(a, b)) }
fn !=(a, b) { not bool(int_eq(a, b)) }

"#

private def world : String := r#"
// The outside world.
fn print(value) { host_write(value) }

fn read() {
    match(host_read()) {
        (1, value) => Some(value),
        _ => None
    }
}

// Loops: a handler for `break` and `continue` around a body run again by a tail call.
effect LoopControl<B> {
    break(B) -> !,
    continue() -> !
}

fn loop(body) {
    handle body() {
        _ => tail loop(body),
        break(value) => value,
        continue() => tail loop(body)
    }
}

// Leaving for a label with a value: out of a function, `return(v, @f)`, or
// out of a scope, `break_at(v, @outer)`. A label is where to go; these are
// functions like any other.
fn return<T, L>(value: T, target: L) -> ! where L: Label<T> {
    target(value)
}

fn break_at<T, L>(value: T, target: L) -> ! where L: Label<T> {
    target(value)
}

// A loop that hands its state on: each turn gives the state for the next, or
// what the loop gives.
enum LoopStep<S, B> { Continue(S), Break(B) }

fn loop_state(initial, body) {
    match(body(initial)) {
        Continue(next) => tail loop_state(next, body),
        Break(value) => value
    }
}

// The body so many times.
fn repeat_n(count: Int, body) {
    match(int_lt(0, count)) {
        0 => (),
        _ => body(); tail repeat_n(int_sub(count, 1), body)
    }
}

fn while(condition, body) {
    loop {
        match(condition()) {
            Ok(found) => body(found),
            Err(_) => break(())
        }
    }
}
"#

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
impl Add for {t} \{ fn +(a, b) {op add} }
impl Sub for {t} \{ fn -(a, b) {op sub} }
impl Mul for {t} \{ fn *(a, b) {op mul} }
impl Div for {t} \{ fn /(a, b) {op "int_div"} }
impl Rem for {t} \{ fn %(a, b) {op "int_rem"} }
impl Neg for {t} \{ fn negate(a) {test s!"{t}_of(int_fit(wide_sub(0, {t}_bits(a)), {width}))"} }
impl Eq for {t} \{ fn ==(a, b) {test s!"bool(int_eq({t}_bits(a), {t}_bits(b)))"} }
impl Ord for {t} \{ fn <(a, b) {test s!"bool(int_lt({t}_bits(a), {t}_bits(b)))"} }
impl Bits for {t} \{
    fn bit_and(a, b) {test s!"{t}_of(int_and({t}_bits(a), {t}_bits(b)))"}
    fn bit_or(a, b) {test s!"{t}_of(int_or({t}_bits(a), {t}_bits(b)))"}
    fn bit_xor(a, b) {test s!"{t}_of(int_xor({t}_bits(a), {t}_bits(b)))"}
    fn shl(a, n) {test s!"{t}_of(int_fit(int_shl({t}_bits(a), n), {width}))"}
    fn shr(a, n) {test s!"{t}_of(int_shr({t}_bits(a), n))"}
}
impl ToInt for {t} \{ fn int(x) {test s!"int_fit({t}_bits(x), 64)"} }
impl Whole for {t} \{
    fn whole(x) {test s!"i128_of({t}_bits(x))"}
    fn of_whole(n) {test s!"{t}_of(int_fit(i128_bits(n), {width}))"}
}
impl Show for {t} \{ fn show(x) {test s!"show_whole({t}_bits(x))"} }
fn {t}(n: Int) -> {t} {test s!"{t}_of(int_fit(n, {width}))"}
"

/-- 128 bits without a sign: held as the same bits with one, so its
arithmetic and its order are the machine's operations that read them so. -/
private def unsigned128 : String :=
  let t := "u128"
  let op := fun (prim : String) => "{ " ++ s!"{t}_of({prim}({t}_bits(a), {t}_bits(b)))" ++ " }"
  let test := fun (e : String) => "{ " ++ e ++ " }"
  s!"
impl Add for {t} \{ fn +(a, b) {op "uw_add"} }
impl Sub for {t} \{ fn -(a, b) {op "uw_sub"} }
impl Mul for {t} \{ fn *(a, b) {op "uw_mul"} }
impl Div for {t} \{ fn /(a, b) {op "uw_div"} }
impl Rem for {t} \{ fn %(a, b) {op "uw_rem"} }
impl Eq for {t} \{ fn ==(a, b) {test s!"bool(int_eq({t}_bits(a), {t}_bits(b)))"} }
impl Ord for {t} \{ fn <(a, b) {test s!"bool(uw_lt({t}_bits(a), {t}_bits(b)))"} }
impl Bits for {t} \{
    fn bit_and(a, b) {op "int_and"}
    fn bit_or(a, b) {op "int_or"}
    fn bit_xor(a, b) {op "int_xor"}
    fn shl(a, n) {test s!"{t}_of(uw_shl({t}_bits(a), n))"}
    fn shr(a, n) {test s!"{t}_of(uw_shr({t}_bits(a), n))"}
}
impl ToInt for {t} \{ fn int(x) {test s!"int_fit({t}_bits(x), -63)"} }
impl Whole for {t} \{
    fn whole(x) {test s!"i128_of(int_fit({t}_bits(x), -127))"}
    fn of_whole(n) {test s!"{t}_of(int_fit(i128_bits(n), -127))"}
}
impl Show for {t} \{ fn show(x) {test s!"unsigned_digits({t}_bits(x), StrEnd)"} }
fn {t}(n: Int) -> {t} {test s!"{t}_of(int_fit(n, -63))"}
"

/-- The scalar types: what each has. -/
private def scalars : String :=
  r#"
// Every scalar type is held as an `Int`: `i8_bits(x)` is that `Int` and
// `i8_of(n)` the `i8` an `Int` is, neither doing anything. What follows says
// what each type's operations are. A result that does not fit its type has no
// meaning: the program stops.
type i64 = Int;

// The `Int` a whole number or a character is; of a floating point number,
// what is before its point.
trait ToInt { fn int(Self) -> Int }
impl ToInt for Int { fn int(x) { x } }

// A whole number of one type as one of another, `let b: u8 = to(n)`, if it
// fits: through the widest type, which holds every value but the upper half
// of `u128`.
trait Whole {
    fn whole(Self) -> i128
    fn of_whole(i128) -> Self
}
impl Whole for Int {
    fn whole(x) { i128_of(x) }
    fn of_whole(n) { int_fit(i128_bits(n), 64) }
}
impl Whole for char {
    fn whole(c) { i128_of(char_bits(c)) }
    fn of_whole(n) { char(int_fit(i128_bits(n), 64)) else { '\u{FFFD}' } }
}
fn to(x) { of_whole(whole(x)) }

// One type made from another: `impl From<Meters> for Feet`.
trait From<T> { fn from(T) -> Self }

// Text: the characters, one after another.
enum Str { StrEnd, StrChar(char, Str) }

infixr 5 ++
fn ++(a, b) {
    match(a) {
        StrEnd => b,
        StrChar(c, rest) => StrChar(c, rest ++ b)
    }
}

fn length(text) {
    match(text) {
        StrEnd => 0,
        StrChar(_, rest) => int_add(1, length(rest))
    }
}

impl Eq for Str {
    fn ==(a, b) {
        match((a, b)) {
            (StrEnd, StrEnd) => true,
            (StrChar(c, x), StrChar(d, y)) =>
                match(int_eq(char_bits(c), char_bits(d))) { 0 => false, _ => x == y },
            _ => false
        }
    }
}

// A value as text.
trait Show { fn show(Self) -> Str }
impl Show for Str { fn show(text) { text } }
impl Show for char { fn show(c) { StrChar(c, StrEnd) } }

// How numbers are written as text. Only what is `pub` is the prelude's.
mod number_text {
    // The digits of a number that is not positive, the first first, before `rest`.
    pub fn digits_before(n, rest) {
        let digit = char_of(int_sub(48, int_rem(n, 10)));
        match(int_div(n, 10)) {
            0 => StrChar(digit, rest),
            more => tail digits_before(more, StrChar(digit, rest))
        }
    }

    // A floating point number as text: the fewest digits that give it back.
    // `wide` is the bits of the number without its sign, as 64 bits; `held` is
    // what the digits must give back, and with `single` that is asked of the 32
    // bits they are brought back to.
    fn float_shortest(wide, held, single, p) {
        let digits = f64_digits(wide, p);
        let exp10 = f64_exp10(wide, p);
        let back = f64_of_decimal(digits, exp10);
        let got = match(single) { 0 => back, _ => f64_narrow(back, 0) };
        match(int_eq(got, held)) {
            0 => tail float_shortest(wide, held, single, int_add(p, 1)),
            _ => (digits, exp10)
        }
    }

    fn zeros(count, rest) {
        match(count) {
            0 => rest,
            _ => StrChar('0', zeros(int_sub(count, 1), rest))
        }
    }

    // The digits with a point after the first `before` of them.
    fn point_after(digits, before) {
        match(before) {
            0 => StrChar('.', digits),
            _ => match(digits) {
                StrChar(c, rest) => StrChar(c, point_after(rest, int_sub(before, 1))),
                StrEnd => StrEnd
            }
        }
    }

    fn float_scientific(digits, exponent) {
        match(digits) {
            StrChar(c, StrEnd) => StrChar(c, StrChar('e', show(exponent))),
            StrChar(c, rest) => StrChar(c, StrChar('.', rest ++ StrChar('e', show(exponent)))),
            StrEnd => StrEnd
        }
    }

    // `exp10` is the power of ten of the last digit, `first` that of the first.
    fn float_placed(digits, exp10, first) {
        match(int_add(int_lt(first, -5), int_lt(16, first))) {
            0 => match(int_lt(exp10, 0)) {
                0 => digits ++ zeros(exp10, ".0"),
                _ => match(int_lt(first, 0)) {
                    0 => point_after(digits, int_add(first, 1)),
                    _ => StrChar('0', StrChar('.', zeros(int_sub(-1, first), digits)))
                }
            },
            _ => float_scientific(digits, first)
        }
    }

    // The digits of 128 bits read without a sign.
    pub fn unsigned_digits(n, rest) {
        let digit = char_of(int_add(48, uw_rem(n, 10)));
        match(uw_div(n, 10)) {
            0 => StrChar(digit, rest),
            more => tail unsigned_digits(more, StrChar(digit, rest))
        }
    }

    pub fn float_text(negative, wide, held, single, infinite) {
        let sign = match(negative) { 0 => "", _ => "-" };
        match(f64_eq(wide, wide)) {
            0 => "NaN",
            _ => match(int_eq(held, infinite)) {
                0 => match(held) {
                    0 => sign ++ "0.0",
                    _ =>
                        let (digits, exp10) = float_shortest(wide, held, single, 1);
                        let text = digits_before(int_sub(0, digits), StrEnd);
                        sign ++ float_placed(text, exp10, int_add(exp10, int_sub(length(text), 1)))
                },
                _ => sign ++ "inf"
            }
        }
    }
}
use number_text::{digits_before, float_text, unsigned_digits};

// A whole number of any width as text.
fn show_whole(n) {
    match(int_lt(n, 0)) {
        0 => digits_before(wide_sub(0, n), StrEnd),
        _ => StrChar('-', digits_before(n, StrEnd))
    }
}

impl Show for Int { fn show(n) { show_whole(n) } }

// A tuple and a `Result` as text, if their parts are. Truth is `Ok(())`.
impl Show for () { fn show(u) { "()" } }
impl<A, B> Show for (A, B) where A: Show, B: Show {
    fn show(p) { match(p) { (a, b) => "(" ++ show(a) ++ ", " ++ show(b) ++ ")" } }
}
impl<A, B, C> Show for (A, B, C) where A: Show, B: Show, C: Show {
    fn show(p) { match(p) { (a, b, c) => "(" ++ show(a) ++ ", " ++ show(b) ++ ", " ++ show(c) ++ ")" } }
}
impl<T, E> Show for Result<T, E> where T: Show, E: Show {
    fn show(r) {
        match(r) {
            Ok(value) => "Ok(" ++ show(value) ++ ")",
            Err(error) => "Err(" ++ show(error) ++ ")"
        }
    }
}
// Truth, `Result<(), ()>`, as `true` and `false` (preferred, as the more
// particular implementation, over the one of every `Result`).
impl Show for Result<(), ()> {
    fn show(b) { match(b) { Ok(_) => "true", Err(_) => "false" } }
}

// An array: its elements, one after another. The machines build its values
// and read a place of one in a step; the constructor written here builds
// none, and says only that an array holds values of the one type. An array
// is a value: changing one makes another.
struct Array<T>(T)

// An address, with what is said to be there: `*const T` and `*mut T`. To
// have one says nothing of what is at the address; reading and writing
// there is unsafe, and the library's to give.
struct Ptr<T>(usize)
struct PtrMut<T>(usize)

fn ptr_at<T>(address: usize) -> *const T { Ptr(address) }
fn ptr_mut_at<T>(address: usize) -> *mut T { PtrMut(address) }
fn ptr_address<T>(p: *const T) -> usize { p.0 }
fn ptr_mut_address<T>(p: *mut T) -> usize { p.0 }
fn ptr_const<T>(p: *mut T) -> *const T { Ptr(p.0) }

// `a[i]` is `index(a, i)`, and `a[i] = v` makes `a` be `index_set(a, i, v)`.
// A place that is not there has no meaning: the program stops.
trait Index {
    type Elem;
    fn index(Self, Int) -> Elem
    fn index_set(Self, Int, Elem) -> Self
}
impl<T> Index for Array<T> {
    type Elem = T;
    fn index(a, i) { arr_get(a, i) }
    fn index_set(a, i, v) { arr_set(a, i, v) }
}

trait Len { fn len(Self) -> Int }
impl<T> Len for Array<T> { fn len(a) { arr_len(a, 0) } }
impl Len for Str { fn len(text) { length(text) } }

// What `[a, b]` and `[x; n]` are made with.
fn array_empty() { arr_new() }
fn array_repeat(x, n) { repeat_onto(x, n, arr_new()) }
fn repeat_onto(x, n, out) {
    match(int_lt(0, n)) {
        0 => out,
        _ => tail repeat_onto(x, int_sub(n, 1), arr_push(out, x))
    }
}

fn push(a, v) { arr_push(a, v) }

// Whole numbers as types, for how long a `[T; N]` is: the bits from the
// lowest, `B1<B0<B1<Z>>>` for five. What number a type stands for is its
// `VALUE`.
struct Z
struct B0<N>
struct B1<N>
trait Known { const VALUE: Int; }
impl Known for Z { const VALUE: Int = 0; }
impl<N> Known for B0<N> where N: Known { const VALUE: Int = int_mul(2, N::VALUE); }
impl<N> Known for B1<N> where N: Known { const VALUE: Int = int_add(int_mul(2, N::VALUE), 1); }

// `[T; N]`: an array of exactly `N` elements.
struct Fixed<T, N>(Array<T>)
impl<T, N> Index for Fixed<T, N> {
    type Elem = T;
    fn index(a, i) { arr_get(a.0, i) }
    fn index_set(a, i, v) { Fixed(arr_set(a.0, i, v)) }
}
impl<T, N> Len for Fixed<T, N> where N: Known { fn len(a) { N::VALUE } }
// Its elements as an array that can grow.
fn to_array<T, N>(a: Fixed<T, N>) -> Array<T> { a.0 }
// `N` of one value.
fn fixed_repeat<T, N>(x: T) -> Fixed<T, N> where N: Known { Fixed(array_repeat(x, N::VALUE)) }

// What `[a, b, c]` is in a program that has arrays of a fixed length: an
// array, or one of exactly three. Where nothing says which, an array.
trait Literal<T, N> { fn of_items(Array<T>) -> Self }
#[fallback] impl<T, N> Literal<T, N> for Array<T> { fn of_items(items) { items } }
impl<T, N> Literal<T, N> for Fixed<T, N> { fn of_items(items) { Fixed(items) } }
fn array_literal<N, T, A>(items: Array<T>) -> A where A: Literal<T, N> {
    <A as Literal<T, N>>::of_items(items)
}

// What `[first, ..rest]` in a pattern is read with: whether an array has so
// many elements, and the array without its first or its last.
enum ArrayRest<T> { RestFits(Array<T>), RestShort(Array<T>) }
fn rest_fits<T>(a: Array<T>, n: Int) -> ArrayRest<T> {
    match(int_lt(arr_len_at(&a), n)) { 0 => RestFits(a), _ => RestShort(a) }
}
fn rest_last<T>(a: Array<T>) -> (Array<T>, T) { arr_pop(a, 0) }
// Where no array comes: the clauses were shown to cover every shorter one.
fn rest_unreached<T, R>(a: Array<T>) -> R { match(int_div(1, 0)) { _ => tail rest_unreached(a) } }
fn rest_first<T>(a: Array<T>) -> (T, Array<T>) {
    let (turned, first) = arr_pop(rest_turn(a, arr_new()), 0);
    (first, rest_turn(turned, arr_new()))
}
fn rest_turn<T>(from: Array<T>, onto: Array<T>) -> Array<T> {
    match(from) {
        [] => onto,
        some => tail rest_turn_one(arr_pop(some, 0), onto)
    }
}
fn rest_turn_one<T>(popped: (Array<T>, T), onto: Array<T>) -> Array<T> {
    match(popped) { (shorter, x) => tail rest_turn(shorter, arr_push(onto, x)) }
}

// The array without its last element, and that element; nothing if it is empty.
fn pop(a) {
    match(a) {
        [] => None,
        some => Some(arr_pop(some, 0))
    }
}

// The element at a place, if the place is there.
fn get(a, i) {
    match(int_mul(int_lt(-1, i), int_lt(i, arr_len(a, 0)))) {
        0 => None,
        _ => Some(arr_get(a, i))
    }
}

// How many elements the array a reference points to has.
fn len_at<T>(a: &Array<T>) -> Int { arr_len_at(a) }

// The element at a place, by reference, if the place is there.
fn element<T>(a: &Array<T>, i: Int) -> Option<&T> {
    match(int_mul(int_lt(-1, i), int_lt(i, arr_len_at(a)))) {
        0 => None,
        _ => Some(arr_at(a, i))
    }
}

// `&a[i]` and `&mut a[i]`: the element where it is. A place that is not
// there has no meaning: the program stops, as it does for `a[i]`.
// What holds elements in order: one borrowed in place, to read or to write
// through. `&a[i]` and `a[i] = v` are of these.
trait Indexed {
    type Element;
    fn element_at(&Self, Int) -> &Element
    fn size_at(&Self) -> Int
}
trait IndexedMut: Indexed {
    fn place_at(Int, &mut Self) -> &mut Self::Element
}
impl<T> Indexed for Array<T> {
    type Element = T;
    fn element_at(a, i) { arr_at(a, i) }
    fn size_at(a) { arr_len_at(a) }
}
impl<T> IndexedMut for Array<T> { fn place_at(i, a) { arr_at(a, i) } }
impl<T, N> Indexed for Fixed<T, N> {
    type Element = T;
    fn element_at(a, i) { arr_at(&a.0, i) }
    fn size_at(a) { arr_len_at(&a.0) }
}
impl<T, N> IndexedMut for Fixed<T, N> { fn place_at(i, a) { arr_at(&mut a.0, i) } }
// A reference to one is one: `a[i]` of an `a: &mut [T]` is of what it is to.
impl<'a, A> Indexed for &'a A where A: Indexed {
    type Element = A::Element;
    fn element_at(r, i) { element_at(*r, i) }
    fn size_at(r) { size_at(*r) }
}
impl<'a, A> Indexed for &'a mut A where A: Indexed {
    type Element = A::Element;
    fn element_at(r, i) { element_at(&*(*r), i) }
    fn size_at(r) { size_at(&*(*r)) }
}
impl<'a, A> IndexedMut for &'a mut A where A: IndexedMut {
    fn place_at(i, r) { place_at(i, &mut *(*r)) }
}
// How many a reference's elements are, as `len` of what it is to.
impl<'a, A> Len for &'a A where A: Indexed { fn len(r) { size_at(r) } }
impl<'a, A> Len for &'a mut A where A: Indexed { fn len(r) { size_at(&*r) } }

// `a[i]` of a reference to an array: the element, read through it. (`a[i] =
// v` writes through it where it is, as of a variable's array.)
impl<'a, A> Index for &'a A where A: Indexed {
    type Elem = A::Element;
    fn index(r, i) { *element_at(r, i) }
    fn index_set(r, i, v) { r }
}
impl<'a, A> Index for &'a mut A where A: Indexed {
    type Elem = A::Element;
    fn index(r, i) { *element_at(&*r, i) }
    fn index_set(r, i, v) { r }
}

// The same to write through.
fn element_mut<T>(a: &mut Array<T>, i: Int) -> Option<&mut T> {
    match(int_mul(int_lt(-1, i), int_lt(i, arr_len_at(&*a)))) {
        0 => None,
        _ => Some(arr_at(a, i))
    }
}

// An array put back where a reference points, after it was taken out with
// `replace` to be changed, an empty one left in its place. The empty one is
// written over: it holds nothing, so nothing is lost, whatever an element is.
// Unsafe, since that is for whoever calls it to have seen to: an array that
// was not taken out would be lost with all it holds.
unsafe fn restore_at<T>(a: &mut Array<T>, items: Array<T>) { overwrite(a, items) }

// An element added to the array a reference points to.
fn push_at<T>(a: &mut Array<T>, x: T) {
    let more = push(replace(a, array_empty()), x);
    unsafe { restore_at(a, more) }
}

// The last element taken off it, if it has one.
fn pop_at<T>(a: &mut Array<T>) -> Option<T> {
    match(pop(replace(a, array_empty()))) {
        Some((rest, last)) => unsafe { restore_at(a, rest) }; Some(last),
        None => None
    }
}

// The elements from one place up to, not including, another.
fn slice(a, from, to) { slice_onto(a, from, to, array_empty()) }
fn slice_onto(a, i, to, out) {
    match(int_lt(i, to)) {
        0 => out,
        _ => tail slice_onto(a, int_add(i, 1), to, push(out, index(a, i)))
    }
}

// A text as its characters, and characters as a text.
fn chars(text) { chars_onto(text, array_empty()) }
fn chars_onto(text, out) {
    match(text) {
        StrEnd => out,
        StrChar(c, rest) => tail chars_onto(rest, push(out, c))
    }
}
fn text(a) { text_before(a, len(a), StrEnd) }
fn text_before(a, i, rest) {
    match(i) {
        0 => rest,
        _ => tail text_before(a, int_sub(i, 1), StrChar(index(a, int_sub(i, 1)), rest))
    }
}

// `f(f(f(init, a[0]), a[1]), ..)`.
fn fold(a, init, f) { fold_from(a, arr_len(a, 0), 0, init, f) }
fn fold_from(a, n, i, acc, f) {
    match(int_lt(i, n)) {
        0 => acc,
        _ => tail fold_from(a, n, int_add(i, 1), f(acc, arr_get(a, i)), f)
    }
}
fn each(a, f) { fold(a, (), fn(done, x) { f(x) }) }

impl<T> Show for Array<T> where T: Show {
    fn show(a) {
        "[" ++ fold(a, "", fn(text, x) {
            match(text) {
                StrEnd => show(x),
                _ => text ++ ", " ++ show(x)
            }
        }) ++ "]"
    }
}

// Write a value as text.
fn say(value) { host_write(show(value)) }

// A value owned anew, from one read through a reference (the library
// specification's §3.1): of what is copied as it is read, the copy; of a
// tuple, a `Result` or an array, each part's.
trait Clone { fn clone(value: &Self) -> Self }
impl Clone for Int { fn clone(v) { *v } }
impl Clone for Str { fn clone(v) { *v } }
impl Clone for char { fn clone(v) { *v } }
impl Clone for () { fn clone(v) { () } }
impl<A, B> Clone for (A, B) where A: Clone, B: Clone { fn clone(p) { (clone(&p.0), clone(&p.1)) } }
impl<A, B, C> Clone for (A, B, C) where A: Clone, B: Clone, C: Clone {
    fn clone(p) { (clone(&p.0), clone(&p.1), clone(&p.2)) }
}
impl<T, E> Clone for Result<T, E> where T: Clone, E: Clone {
    fn clone(r) { match(r) { &Ok(v) => Ok(clone(v)), &Err(e) => Err(clone(e)) } }
}
impl<T> Clone for Array<T> where T: Clone { fn clone(a) { clone_onto(a, 0, arr_new()) } }
fn clone_onto<T: Clone>(a: &Array<T>, i: Int, out: Array<T>) -> Array<T> {
    if(i < arr_len_at(a)) { tail clone_onto(a, i + 1, arr_push(out, clone(arr_at(a, i)))) } else { out }
}

// Of a result: what `Ok` holds, or else leaving for the label with the error
// (`try(r, @f)` in a function that gives a `Result`); the same with the
// error made another first; leaving with an error unless a condition holds;
// and of an option, what `Some` holds or else leaving with what a fallback
// gives. (The library specification's §6. There is no `?`.)
fn try<T, E, R, L>(value: Result<T, E>, target: L) -> T where L: Label<Result<R, E>> {
    match(value) { Ok(v) => v, Err(e) => target(Err(e)) }
}
fn try_map_error<T, E, D, R, L>(value: Result<T, E>, target: L, map_error) -> T where L: Label<Result<R, D>> {
    match(value) { Ok(v) => v, Err(e) => target(Err(map_error(e))) }
}
fn ensure<R, E, L>(condition: Result<(), ()>, target: L, make_error) where L: Label<Result<R, E>> {
    match(condition) { Ok(_) => (), Err(_) => target(Err(make_error())) }
}
fn some_or_leave<T, R, L>(value: Result<T, ()>, target: L, fallback) -> T where L: Label<R> {
    match(value) { Ok(v) => v, Err(_) => target(fallback()) }
}

// Stopping: what is said is written, and the program stops there, with no
// cleanup run (the library specification's §6.1).
fn abort<T>(message: Str) -> T { host_write(message); arr_get(arr_new(), 0) }
fn unreachable<T>(message: Str) -> T { abort(message) }
// What an `Option<&T>` points to, copied: what a match of a reference's
// insides with patterns of a value is given (`Check.inferCall`).
fn copied_ref<T: Copy, E>(r: Result<&T, E>) -> Result<T, E> { match(r) { Ok(x) => Ok(*x), Err(e) => Err(e) } }
// What a value is shown as, `x.to_string()`.
fn to_string<T: Show>(value: T) -> Str { show(value) }
// What an `Option` or a `Result` has, asked of it as a value's own: `o.map(f)`.
// (An `Option<T>` is a `Result<T, ()>`, so each is both's.)
impl<T, E> Result<T, E> {
    fn is_some(&self) -> Bool { match(self) { &Ok(_) => true, &Err(_) => false } }
    fn is_none(&self) -> Bool { match(self) { &Ok(_) => false, &Err(_) => true } }
    fn is_ok(&self) -> Bool { match(self) { &Ok(_) => true, &Err(_) => false } }
    fn is_err(&self) -> Bool { match(self) { &Ok(_) => false, &Err(_) => true } }
    fn unwrap(self) -> T { match(self) { Ok(x) => x, Err(_) => abort("unwrap of nothing") } }
    fn expect(self, message: Str) -> T { match(self) { Ok(x) => x, Err(_) => abort(message) } }
    fn unwrap_or(self, other: T) -> T { match(self) { Ok(x) => x, Err(_) => other } }
    fn unwrap_or_else(self, other) -> T { match(self) { Ok(x) => x, Err(e) => other(e) } }
    fn map(self, f) { match(self) { Ok(x) => Ok(f(x)), Err(e) => Err(e) } }
    fn map_err(self, f) { match(self) { Ok(x) => Ok(x), Err(e) => Err(f(e)) } }
    fn and_then(self, f) { match(self) { Ok(x) => f(x), Err(e) => Err(e) } }
    fn or_else(self, f) { match(self) { Ok(x) => Ok(x), Err(e) => f(e) } }
    fn ok_or<D>(self, error: D) -> Result<T, D> { match(self) { Ok(x) => Ok(x), Err(_) => Err(error) } }
    fn ok(self) -> Option<T> { match(self) { Ok(x) => Some(x), Err(_) => None } }
    fn filter(self, keep: for<'a> fn(&'a T) -> Bool) -> Result<T, ()> {
        match(self) { Ok(x) => if(keep(&x)) { Ok(x) } else { Err(()) }, Err(_) => Err(()) }
    }
}
fn assert(condition: Result<(), ()>) { match(condition) { Ok(_) => (), Err(_) => abort("assertion failed") } }
fn assert_message(condition: Result<(), ()>, message: Str) { match(condition) { Ok(_) => (), Err(_) => abort(message) } }
fn assert_eq<T>(left: &T, right: &T) where T: Eq, T: Show {
    match(*left == *right) { Ok(_) => (), Err(_) => abort(show(*left) ++ " is not " ++ show(*right)) }
}
fn assert_ne<T>(left: &T, right: &T) where T: Eq, T: Show {
    match(*left == *right) { Ok(_) => abort(show(*left) ++ " is what it should not be"), Err(_) => () }
}


// Values made of values that can be compared can be compared.
impl Eq for () { fn ==(a, b) { true } }
impl<A, B> Eq for (A, B) where A: Eq, B: Eq {
    fn ==(x, y) { match((x, y)) { ((a, b), (c, d)) => a == c and { b == d } } }
}
impl<A, B, C> Eq for (A, B, C) where A: Eq, B: Eq, C: Eq {
    fn ==(x, y) { match((x, y)) { ((a, b, c), (d, e, f)) => a == d and { b == e } and { c == f } } }
}
impl<T, E> Eq for Result<T, E> where T: Eq, E: Eq {
    fn ==(x, y) {
        match((x, y)) {
            (Ok(a), Ok(b)) => a == b,
            (Err(a), Err(b)) => a == b,
            _ => false
        }
    }
}
impl<T> Eq for Array<T> where T: Eq {
    fn ==(a, b) {
        match(int_eq(len(a), len(b))) { 0 => false, _ => same_from(a, b, 0) }
    }
}
fn same_from<T>(a: Array<T>, b: Array<T>, i: Int) -> Bool where T: Eq {
    match(int_lt(i, len(a))) {
        0 => true,
        _ => match(index(a, i) == index(b, i)) { Ok(_) => tail same_from(a, b, int_add(i, 1)), Err(_) => false }
    }
}

// Pairs in order: by the first, and then by the second. Texts as in a
// dictionary of character codes.
impl<A, B> Ord for (A, B) where A: Ord, B: Ord {
    fn <(x, y) { match((x, y)) { ((a, b), (c, d)) => a < c or { a == c and { b < d } } } }
}
impl Ord for Str {
    fn <(a, b) {
        match((a, b)) {
            (_, StrEnd) => false,
            (StrEnd, _) => true,
            (StrChar(c, x), StrChar(d, y)) =>
                match(int_lt(char_bits(c), char_bits(d))) {
                    0 => match(int_eq(char_bits(c), char_bits(d))) { 0 => false, _ => x < y },
                    _ => true
                }
        }
    }
}

// A character is its code: any but the codes kept for pairs, up to 10FFFF.
impl Eq for char { fn ==(a, b) { bool(int_eq(char_bits(a), char_bits(b))) } }
impl Ord for char { fn <(a, b) { bool(int_lt(char_bits(a), char_bits(b))) } }
impl ToInt for char { fn int(c) { char_bits(c) } }
fn char(code: Int) -> Option<char> {
    match(int_add(int_lt(code, 0), int_add(int_lt(1114111, code),
            int_mul(int_lt(55295, code), int_lt(code, 57344))))) {
        0 => Some(char_of(code)),
        _ => None
    }
}

// Floating point. `f64_add` and the rest take and give the bits.
impl Add for f64 { fn +(a, b) { f64_of(f64_add(f64_bits(a), f64_bits(b))) } }
impl Sub for f64 { fn -(a, b) { f64_of(f64_sub(f64_bits(a), f64_bits(b))) } }
impl Mul for f64 { fn *(a, b) { f64_of(f64_mul(f64_bits(a), f64_bits(b))) } }
impl Div for f64 { fn /(a, b) { f64_of(f64_div(f64_bits(a), f64_bits(b))) } }
// Not `0.0 - a`, which is `0.0` where this is `-0.0`.
impl Neg for f64 { fn negate(a) { f64_of(f64_sub(-9223372036854775808, f64_bits(a))) } }
impl Eq for f64 {
    fn ==(a, b) { bool(f64_eq(f64_bits(a), f64_bits(b))) }
    fn !=(a, b) { not bool(f64_eq(f64_bits(a), f64_bits(b))) }
}
// Not one from another by `not`: nothing is smaller than a NaN, or larger.
impl Ord for f64 {
    fn <(a, b) { bool(f64_lt(f64_bits(a), f64_bits(b))) }
    fn >(a, b) { bool(f64_lt(f64_bits(b), f64_bits(a))) }
    fn <=(a, b) { bool(int_add(f64_lt(f64_bits(a), f64_bits(b)), f64_eq(f64_bits(a), f64_bits(b)))) }
    fn >=(a, b) { bool(int_add(f64_lt(f64_bits(b), f64_bits(a)), f64_eq(f64_bits(a), f64_bits(b)))) }
}
impl ToInt for f64 { fn int(x) { f64_to_int(f64_bits(x), 0) } }

// What a floating point number has beside arithmetic. `round` is to the
// nearest whole number, a half to the even one.
trait Real {
    fn sqrt(Self) -> Self
    fn floor(Self) -> Self
    fn ceil(Self) -> Self
    fn trunc(Self) -> Self
    fn round(Self) -> Self
}
// How far from zero, as a value of the same type.
trait Abs { fn abs(Self) -> Self }
impl Abs for Int { fn abs(n) { match(int_lt(n, 0)) { 0 => n, _ => int_sub(0, n) } } }
impl Abs for f64 { fn abs(x) { f64_of(int_and(f64_bits(x), 9223372036854775807)) } }
impl Abs for f32 { fn abs(x) { narrow(abs(widen(x))) } }
impl Real for f64 {
    fn sqrt(x) { f64_of(f64_sqrt(f64_bits(x), 0)) }
    fn floor(x) { f64_of(f64_round(f64_bits(x), 0)) }
    fn ceil(x) { f64_of(f64_round(f64_bits(x), 1)) }
    fn trunc(x) { f64_of(f64_round(f64_bits(x), 2)) }
    fn round(x) { f64_of(f64_round(f64_bits(x), 3)) }
}
fn f64(n: Int) -> f64 { f64_of(f64_of_int(n, 0)) }

// A 32-bit number is computed with as a 64-bit one and the result brought
// back to the nearest it can hold, which is the nearest to the true result.
fn widen(x: f32) -> f64 { f64_of(f64_widen(f32_bits(x), 0)) }
fn narrow(x: f64) -> f32 { f32_of(f64_narrow(f64_bits(x), 0)) }
impl Add for f32 { fn +(a, b) { narrow(widen(a) + widen(b)) } }
impl Sub for f32 { fn -(a, b) { narrow(widen(a) - widen(b)) } }
impl Mul for f32 { fn *(a, b) { narrow(widen(a) * widen(b)) } }
impl Div for f32 { fn /(a, b) { narrow(widen(a) / widen(b)) } }
impl Neg for f32 { fn negate(a) { narrow(negate(widen(a))) } }
impl Eq for f32 {
    fn ==(a, b) { widen(a) == widen(b) }
    fn !=(a, b) { widen(a) != widen(b) }
}
impl Ord for f32 {
    fn <(a, b) { widen(a) < widen(b) }
    fn >(a, b) { widen(a) > widen(b) }
    fn <=(a, b) { widen(a) <= widen(b) }
    fn >=(a, b) { widen(a) >= widen(b) }
}
impl ToInt for f32 { fn int(x) { int(widen(x)) } }
impl Real for f32 {
    fn sqrt(x) { narrow(sqrt(widen(x))) }
    fn floor(x) { narrow(floor(widen(x))) }
    fn ceil(x) { narrow(ceil(widen(x))) }
    fn trunc(x) { narrow(trunc(widen(x))) }
    fn round(x) { narrow(round(widen(x))) }
}
fn f32(n: Int) -> f32 { narrow(f64(n)) }

impl Show for f64 {
    fn show(x) {
        let bits = f64_bits(x);
        match(int_lt(bits, 0)) {
            0 => float_text(0, bits, bits, 0, 9218868437227405312),
            _ =>
                let rest = int_sub(bits, -9223372036854775808);
                float_text(1, rest, rest, 0, 9218868437227405312)
        }
    }
}

impl Show for f32 {
    fn show(x) {
        let bits = f32_bits(x);
        match(int_lt(bits, 2147483648)) {
            0 =>
                let rest = int_sub(bits, 2147483648);
                float_text(1, f64_widen(rest, 0), rest, 1, 2139095040),
            _ => float_text(0, f64_widen(bits, 0), bits, 1, 2139095040)
        }
    }
}
"# ++ String.join ((Syntax.scalars.filterMap fun (t, width) => width.map fun w =>
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
    fn elements(a) \{ {String.join pops}{tuple (places.map fun i => s!"x{i}")} }
}
"
  "
// A `[T; N]` as a tuple of its elements: `let [a, b, c] = xs`.
trait Elements { type Each; fn elements(Self) -> Each }
" ++ String.join ((List.range 9).map one)

def source : String := core ++ operators ++ scalars ++ world ++ fixedElements

/-- The prelude of a program run without the checker. -/
def unchecked : String := core ++ intOperators ++ world


end Glorious.Prelude
