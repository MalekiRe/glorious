import Glorious.Syntax.Ast

/-!
# The prelude

Written in Glorious. None of these names is known to the compiler: conditionals,
matching, boolean operators, arithmetic operators and loops are ordinary
functions over the kernel.

Arithmetic and comparison are traits, which the checker resolves. A program
run without the checker has no traits, so for it there is a second prelude in
which the operators are `Int`'s alone.
-/

namespace Glorious.Prelude

private def core : String := r#"
enum Result<T, E> { Ok(T), Err(E) }

// Truth is success. `Option<T>` is `Result<T, ()>` and `Bool` is `Option<()>`.
type Option<T> = Result<T, ()>;
type Bool = Result<(), ()>;
let Some = Ok;
let None = Err(());
let true = Ok(());
let false = Err(());

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
trait Eq {
    fn ==(Self, Self) -> Bool
    fn !=(Self, Self) -> Bool
}
trait Ord {
    fn <(Self, Self) -> Bool
    fn >(Self, Self) -> Bool
    fn <=(Self, Self) -> Bool
    fn >=(Self, Self) -> Bool
}

impl Add for Int { fn +(a, b) { int_add(a, b) } }
impl Sub for Int { fn -(a, b) { int_sub(a, b) } }
impl Mul for Int { fn *(a, b) { int_mul(a, b) } }
impl Div for Int { fn /(a, b) { int_div(a, b) } }
impl Rem for Int { fn %(a, b) { int_rem(a, b) } }
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
fit the type's width; and the way in from an `Int`, which asks the same. -/
private def wholeNumber (t : String) (width : Int) : String :=
  let op := fun (prim : String) =>
    "{ " ++ s!"{t}_of(int_fit({prim}({t}_bits(a), {t}_bits(b)), {width}))" ++ " }"
  let test := fun (e : String) => "{ " ++ e ++ " }"
  s!"
impl Add for {t} \{ fn +(a, b) {op "int_add"} }
impl Sub for {t} \{ fn -(a, b) {op "int_sub"} }
impl Mul for {t} \{ fn *(a, b) {op "int_mul"} }
impl Div for {t} \{ fn /(a, b) {op "int_div"} }
impl Rem for {t} \{ fn %(a, b) {op "int_rem"} }
impl Eq for {t} \{
    fn ==(a, b) {test s!"bool(int_eq({t}_bits(a), {t}_bits(b)))"}
    fn !=(a, b) {test s!"not bool(int_eq({t}_bits(a), {t}_bits(b)))"}
}
impl Ord for {t} \{
    fn <(a, b) {test s!"bool(int_lt({t}_bits(a), {t}_bits(b)))"}
    fn >(a, b) {test s!"bool(int_lt({t}_bits(b), {t}_bits(a)))"}
    fn <=(a, b) {test s!"not bool(int_lt({t}_bits(b), {t}_bits(a)))"}
    fn >=(a, b) {test s!"not bool(int_lt({t}_bits(a), {t}_bits(b)))"}
}
impl ToInt for {t} \{ fn int(x) {test s!"{t}_bits(x)"} }
impl Show for {t} \{ fn show(x) {test s!"show({t}_bits(x))"} }
fn {t}(n: Int) -> {t} {test s!"{t}_of(int_fit(n, {width}))"}
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
    fn !=(a, b) { not (a == b) }
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
use number_text::{digits_before, float_text};

impl Show for Int {
    fn show(n) {
        match(int_lt(n, 0)) {
            0 => digits_before(int_sub(0, n), StrEnd),
            _ => StrChar('-', digits_before(n, StrEnd))
        }
    }
}

// Write a value as text.
fn say(value) { host_write(show(value)) }

// A character is its code: any but the codes kept for pairs, up to 10FFFF.
impl Eq for char {
    fn ==(a, b) { bool(int_eq(char_bits(a), char_bits(b))) }
    fn !=(a, b) { not bool(int_eq(char_bits(a), char_bits(b))) }
}
impl Ord for char {
    fn <(a, b) { bool(int_lt(char_bits(a), char_bits(b))) }
    fn >(a, b) { bool(int_lt(char_bits(b), char_bits(a))) }
    fn <=(a, b) { not bool(int_lt(char_bits(b), char_bits(a))) }
    fn >=(a, b) { not bool(int_lt(char_bits(a), char_bits(b))) }
}
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
fn f64(n: Int) -> f64 { f64_of(f64_of_int(n, 0)) }

// A 32-bit number is computed with as a 64-bit one and the result brought
// back to the nearest it can hold, which is the nearest to the true result.
fn widen(x: f32) -> f64 { f64_of(f64_widen(f32_bits(x), 0)) }
fn narrow(x: f64) -> f32 { f32_of(f64_narrow(f64_bits(x), 0)) }
impl Add for f32 { fn +(a, b) { narrow(widen(a) + widen(b)) } }
impl Sub for f32 { fn -(a, b) { narrow(widen(a) - widen(b)) } }
impl Mul for f32 { fn *(a, b) { narrow(widen(a) * widen(b)) } }
impl Div for f32 { fn /(a, b) { narrow(widen(a) / widen(b)) } }
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
"# ++ String.join ((Syntax.scalars.filterMap fun (t, width) => width.map fun w => wholeNumber t w))

def source : String := core ++ operators ++ scalars ++ world

/-- The prelude of a program run without the checker. -/
def unchecked : String := core ++ intOperators ++ world


end Glorious.Prelude
