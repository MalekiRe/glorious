/-!
# The standard library

What a program has beyond the prelude, written in the language: the module
`std` and the modules in it. A program that names `std` has it as a module of
its own, as though the texts here were files beside it.
-/

namespace Glorious.Std

private def root : String := r#"// The standard library: what is not in the prelude. A module is brought in
// by its name: `use std::vec::sort;`.
pub mod option;
pub mod result;
pub mod cmp;
pub mod int;
pub mod char;
pub mod vec;
pub mod text;
pub mod map;
pub mod set;
pub mod iter;
pub mod c;
pub mod fmt;
pub mod iterator;
pub mod slice;
pub mod collections;
pub mod host;
pub mod hash;
pub mod io;
pub mod fs;
pub mod env;
pub mod time;
pub mod random;
pub mod ffi;
"#

private def optionText : String := r#"// An `Option<T>` is a `Result<T, ()>`: `Some(x)` or `None`.

pub fn is_some(o) { match(o) { Some(_) => true, None => false } }
pub fn is_none(o) { match(o) { Some(_) => false, None => true } }

// What is there, or a value to use instead.
pub fn unwrap_or(o, other) { match(o) { Some(x) => x, None => other } }

// What is there, or what a callable gives.
pub fn unwrap_or_else(o, other) { match(o) { Some(x) => x, None => other() } }

pub fn map(o, f) { match(o) { Some(x) => Some(f(x)), None => None } }

// `f` of what is there, which may itself be nothing.
pub fn and_then(o, f) { match(o) { Some(x) => f(x), None => None } }

// What is there if `keep` says so.
pub fn filter(o, keep) {
    match(o) {
        Some(x) => if(keep(x)) { Some(x) } else { None },
        None => None
    }
}

// The first that is there.
pub fn or_else(o, other) { match(o) { Some(x) => Some(x), None => other() } }

// Both, if both are there.
pub fn zip(a, b) {
    match(a) {
        Some(x) => match(b) { Some(y) => Some((x, y)), None => None },
        None => None
    }
}

// A `Result` that fails with `error` where there was nothing.
pub fn ok_or(o, error) { match(o) { Some(x) => Ok(x), None => Err(error) } }

pub fn fold(o, init, f) { match(o) { Some(x) => f(init, x), None => init } }

// What is there, where it is: looked at or changed without being taken.
pub fn as_ref<'a, T>(o: &'a Option<T>) -> Option<&'a T> {
    match(o) { &Some(x) => Some(x), &None => None }
}
pub fn as_mut<'a, T>(o: &'a mut Option<T>) -> Option<&'a mut T> {
    match(o) { &mut Some(x) => Some(x), &mut None => None }
}

// What is there, taken; nothing is left.
pub fn take<T>(o: &mut Option<T>) -> Option<T> { replace(o, None) }
"#

private def resultText : String := r#"// `Result<T, E>`: `Ok(value)` or `Err(error)`.

pub fn is_ok(r) { match(r) { Ok(_) => true, Err(_) => false } }
pub fn is_err(r) { match(r) { Ok(_) => false, Err(_) => true } }

pub fn unwrap_or(r, other) { match(r) { Ok(x) => x, Err(_) => other } }
pub fn unwrap_or_else(r, other) { match(r) { Ok(x) => x, Err(e) => other(e) } }

pub fn map(r, f) { match(r) { Ok(x) => Ok(f(x)), Err(e) => Err(e) } }
pub fn map_err(r, f) { match(r) { Ok(x) => Ok(x), Err(e) => Err(f(e)) } }

// `f` of what succeeded, which may itself fail.
pub fn and_then(r, f) { match(r) { Ok(x) => f(x), Err(e) => Err(e) } }

// What succeeded, or what `f` makes of the failure.
pub fn or_else(r, f) { match(r) { Ok(x) => Ok(x), Err(e) => f(e) } }

// The value, forgetting why there is none.
pub fn ok(r) { match(r) { Ok(x) => Some(x), Err(_) => None } }

// The failure, if it failed.
pub fn err(r) { match(r) { Ok(_) => None, Err(e) => Some(e) } }

// What succeeded or failed, where it is.
pub fn as_ref<'a, T, E>(r: &'a Result<T, E>) -> Result<&'a T, &'a E> {
    match(r) { &Ok(x) => Ok(x), &Err(e) => Err(e) }
}
pub fn as_mut<'a, T, E>(r: &'a mut Result<T, E>) -> Result<&'a mut T, &'a mut E> {
    match(r) { &mut Ok(x) => Ok(x), &mut Err(e) => Err(e) }
}
"#

private def cmpText : String := r#"// Putting values in order.

pub enum Ordering { Less, Equal, Greater }

// How `a` stands to `b`.
pub fn compare(a, b) {
    if(a < b) { Less } else { if(a == b) { Equal } else { Greater } }
}

pub fn min(a, b) { if(b < a) { b } else { a } }
pub fn max(a, b) { if(b < a) { a } else { b } }

// `x`, kept between `low` and `high`.
pub fn clamp(x, low, high) { if(x < low) { low } else { if(high < x) { high } else { x } } }

// The order the other way round.
pub fn reverse(o) { match(o) { Less => Greater, Equal => Equal, Greater => Less } }

// This order, or where it says equal, another.
pub fn then(o, other) { match(o) { Equal => other, _ => o } }

pub fn is_less(o) { match(o) { Less => true, _ => false } }
pub fn is_equal(o) { match(o) { Equal => true, _ => false } }
pub fn is_greater(o) { match(o) { Greater => true, _ => false } }
"#

private def intText : String := r#"// Whole numbers.

pub fn abs(n: Int) -> Int { if(n < 0) { 0 - n } else { n } }

// -1, 0 or 1: the sign of a number.
pub fn signum(n: Int) -> Int { if(n < 0) { 0 - 1 } else { if(n == 0) { 0 } else { 1 } } }

pub fn is_even(n: Int) -> Bool { n % 2 == 0 }
pub fn is_odd(n: Int) -> Bool { n % 2 != 0 }

// `base` multiplied by itself `exponent` times; `exponent` is not negative.
pub fn pow(base: Int, exponent: Int) -> Int { pow_onto(base, exponent, 1) }
fn pow_onto(base: Int, exponent: Int, acc: Int) -> Int {
    if(exponent <= 0) { acc } else {
        if(exponent % 2 == 0) { tail pow_onto(base * base, exponent / 2, acc) }
        else { tail pow_onto(base, exponent - 1, acc * base) }
    }
}

// The greatest number that divides both; never negative.
pub fn gcd(a: Int, b: Int) -> Int { if(b == 0) { abs(a) } else { tail gcd(b, a % b) } }

// The least number both divide; never negative.
pub fn lcm(a: Int, b: Int) -> Int { if(a == 0 or { b == 0 }) { 0 } else { abs(a / gcd(a, b) * b) } }

// The quotient rounded down, and what is left, which has the sign of `b`.
pub fn div_floor(a: Int, b: Int) -> Int {
    let q = a / b;
    if(a % b != 0 and { (a < 0) != (b < 0) }) { q - 1 } else { q }
}
pub fn mod_floor(a: Int, b: Int) -> Int { a - div_floor(a, b) * b }

// The digits of a number that is not negative, the first first.
pub fn digits(n: Int) -> [Int] { if(n < 10) { [n] } else { push(digits(n / 10), n % 10) } }

// The whole root: the greatest `r` with `r * r <= n`, for `n` not negative.
pub fn sqrt(n: Int) -> Int { if(n < 2) { n } else { sqrt_from(n, n) } }
fn sqrt_from(n: Int, guess: Int) -> Int {
    let next = (guess + n / guess) / 2;
    if(next >= guess) { guess } else { tail sqrt_from(n, next) }
}
"#

private def charText : String := r#"// Characters. What is said of letters and digits here is said of ASCII.

pub fn code(c: char) -> Int { int(c) }

pub fn is_digit(c: char) -> Bool { '0' <= c and { c <= '9' } }
pub fn is_lower(c: char) -> Bool { 'a' <= c and { c <= 'z' } }
pub fn is_upper(c: char) -> Bool { 'A' <= c and { c <= 'Z' } }
pub fn is_alpha(c: char) -> Bool { is_lower(c) or { is_upper(c) } }
pub fn is_alphanumeric(c: char) -> Bool { is_alpha(c) or { is_digit(c) } }
pub fn is_space(c: char) -> Bool {
    c == ' ' or { c == '\n' } or { c == '\t' } or { c == '\r' }
}

// The number a digit stands for.
pub fn digit(c: char) -> Option<Int> { if(is_digit(c)) { Some(int(c) - int('0')) } else { None } }

// The digit that stands for a number from 0 to 9.
pub fn of_digit(n: Int) -> Option<char> { if(0 <= n and { n <= 9 }) { char(int('0') + n) } else { None } }

pub fn to_upper(c: char) -> char { if(is_lower(c)) { char(int(c) - 32) else { c } } else { c } }
pub fn to_lower(c: char) -> char { if(is_upper(c)) { char(int(c) + 32) else { c } } else { c } }
"#

private def vecText : String := r#"// Arrays: `[T]`. Nothing here changes an array it is given; each gives a new one.

pub fn is_empty(a) { len(a) == 0 }

pub fn first(a) { get(a, 0) }
pub fn last(a) { get(a, len(a) - 1) }

// The numbers from `from` up to, not including, `to`.
pub fn range(from: Int, to: Int) -> [Int] { range_onto(from, to, []) }
fn range_onto(i: Int, to: Int, out: [Int]) -> [Int] {
    if(i < to) { tail range_onto(i + 1, to, push(out, i)) } else { out }
}

// `n` elements, the one at each place what `f` gives for the place.
pub fn from_fn(n: Int, f) { from_fn_onto(n, f, 0, []) }
fn from_fn_onto(n: Int, f, i: Int, out) {
    if(i < n) { tail from_fn_onto(n, f, i + 1, push(out, f(i))) } else { out }
}

pub fn map(a, f) { fold(a, [], fn(out, x) { push(out, f(x)) }) }

// The elements `keep` says yes to.
pub fn filter(a, keep) { fold(a, [], fn(out, x) { if(keep(x)) { push(out, x) } else { out } }) }

// Each element with its place.
pub fn enumerate(a) { from_fn(len(a), { i => (i, a[i]) }) }

pub fn reverse(a) { from_fn(len(a), { i => a[len(a) - 1 - i] }) }

// One array after another.
pub fn append(a, b) { fold(b, a, fn(out, x) { push(out, x) }) }

// The arrays of an array, one after another.
pub fn concat(parts) { fold(parts, [], fn(out, part) { append(out, part) }) }

// The first `n` elements, and the rest.
pub fn take(a, n: Int) { slice(a, 0, if(n < len(a)) { n } else { len(a) }) }
pub fn drop(a, n: Int) { slice(a, if(n < len(a)) { n } else { len(a) }, len(a)) }

// Pairs of the elements at the same places, as many as the shorter has.
pub fn zip(a, b) { from_fn(if(len(a) < len(b)) { len(a) } else { len(b) }, { i => (a[i], b[i]) }) }

// The place of the first element `wanted` says yes to.
pub fn position(a, wanted) { position_from(a, wanted, 0) }
fn position_from(a, wanted, i: Int) -> Option<Int> {
    if(i < len(a)) {
        if(wanted(a[i])) { Some(i) } else { tail position_from(a, wanted, i + 1) }
    } else { None }
}

// The first element `wanted` says yes to.
pub fn find(a, wanted) { match(position(a, wanted)) { Some(i) => Some(a[i]), None => None } }

pub fn any(a, wanted) { match(position(a, wanted)) { Some(_) => true, None => false } }
pub fn all(a, wanted) { not any(a, { x => not wanted(x) }) }
pub fn contains(a, x) { any(a, { y => y == x }) }

// How many elements `wanted` says yes to.
pub fn count(a, wanted) { fold(a, 0, fn(n, x) { if(wanted(x)) { n + 1 } else { n } }) }

pub fn sum(a) { fold(a, 0, fn(total, x) { total + x }) }
pub fn product(a) { fold(a, 1, fn(total, x) { total * x }) }

// The least and the greatest, if there is any element.
pub fn minimum(a) {
    if(len(a) == 0) { None } else { Some(fold(a, a[0], fn(m, x) { if(x < m) { x } else { m } })) }
}
pub fn maximum(a) {
    if(len(a) == 0) { None } else { Some(fold(a, a[0], fn(m, x) { if(m < x) { x } else { m } })) }
}

// The array with the elements at two places changed over.
pub fn swap(a, i: Int, j: Int) {
    let x = a[i];
    let y = a[j];
    index_set(index_set(a, i, y), j, x)
}

// The elements in order, by `<`. Elements that are equal stay as they were
// to each other.
pub fn sort(a) { sort_by(a, fn(x, y) { x < y }) }

// The elements in the order `before` gives: `before(x, y)` says `x` comes
// before `y`.
pub fn sort_by(a, before) {
    if(len(a) < 2) { a } else {
        let half = len(a) / 2;
        merge(sort_by(slice(a, 0, half), before), sort_by(slice(a, half, len(a)), before), before)
    }
}

// Two arrays in order as one in order.
fn merge(a, b, before) { merge_from(a, b, before, 0, 0, []) }
fn merge_from(a, b, before, i: Int, j: Int, out) {
    if(i < len(a)) {
        if(j < len(b)) {
            if(before(b[j], a[i])) { tail merge_from(a, b, before, i, j + 1, push(out, b[j])) }
            else { tail merge_from(a, b, before, i + 1, j, push(out, a[i])) }
        } else { tail merge_from(a, b, before, i + 1, j, push(out, a[i])) }
    } else {
        if(j < len(b)) { tail merge_from(a, b, before, i, j + 1, push(out, b[j])) } else { out }
    }
}

// Where `x` is in an array in order, or where it would go.
pub fn binary_search(a, x) -> Result<Int, Int> { search_in(a, x, 0, len(a)) }
fn search_in(a, x, low: Int, high: Int) -> Result<Int, Int> {
    if(low < high) {
        let mid = low + (high - low) / 2;
        if(a[mid] < x) { tail search_in(a, x, mid + 1, high) }
        else { if(x < a[mid]) { tail search_in(a, x, low, mid) } else { Ok(mid) } }
    } else { Err(low) }
}

// The array without an element that is equal to the one before it.
pub fn dedup(a) {
    fold(a, [], fn(out, x) {
        if(len(out) == 0) { push(out, x) } else {
            if(out[len(out) - 1] == x) { out } else { push(out, x) }
        }
    })
}

// `f(f(init, a0, b0), a1, b1)` and so on, of an array of pairs.
pub fn fold_pairs(pairs, init, f) { fold(pairs, init, fn(acc, pair) { match(pair) { (a, b) => f(acc, a, b) } }) }

// How long an array is (the prelude's `len`, of arrays alone).
pub fn len_of<T>(a: [T]) -> Int { len(a) }

// A growable array changed where it is, in the shape the library
// specification gives it (15): functions of the type, `&mut Self` to change
// one, `Option<&T>` to look at an element. Sizes and places are `Int`.
use std::slice::{Slice, SliceIter};

pub struct Vec<T> { items: [T] }

// The last `n` elements of an array taken off, last first, and what is left.
fn taken_off<T>(a: [T], n: Int, off: [T]) -> ([T], [T]) {
    if(n <= 0) { (a, off) } else {
        match(pop(a)) {
            Some((rest, last)) => tail taken_off(rest, n - 1, push(off, last)),
            None => ([], off)
        }
    }
}

// The elements of one array onto another, last first.
fn turned<T>(from: [T], onto: [T]) -> [T] {
    match(pop(from)) {
        Some((rest, last)) => tail turned(rest, push(onto, last)),
        None => onto
    }
}

// What was taken off, put back in the order it had.
fn put_back<T>(a: [T], off: [T]) -> [T] {
    match(pop(off)) {
        Some((rest, next)) => tail put_back(push(a, next), rest),
        None => a
    }
}

impl<T> Vec<T> {
    pub fn new() -> Self { Self { items: [] } }
    pub fn with_capacity(capacity: Int) -> Self { Self { items: [] } }
    pub fn from_array(items: [T]) -> Self { Self { items: items } }
    pub fn into_array(value: Self) -> [T] { match(value) { Vec { items } => items } }
    pub fn len(value: &Self) -> Int { len_at(&value.items) }
    pub fn is_empty(value: &Self) -> Bool { len_at(&value.items) == 0 }
    pub fn get<'a>(value: &'a Self, index: Int) -> Option<&'a T> { element(&value.items, index) }
    pub fn get_mut<'a>(value: &'a mut Self, index: Int) -> Option<&'a mut T> {
        element_mut(&mut value.items, index)
    }
    pub fn first<'a>(value: &'a Self) -> Option<&'a T> { element(&value.items, 0) }
    pub fn last<'a>(value: &'a Self) -> Option<&'a T> {
        element(&value.items, len_at(&value.items) - 1)
    }
    pub fn push(value: &mut Self, item: T) {
        let items = &mut value.items;
        *items = push(replace(items, []), item);
    }
    pub fn pop(value: &mut Self) -> Option<T> {
        let items = &mut value.items;
        match(pop(replace(items, []))) {
            Some((rest, last)) => *items = rest; Some(last),
            None => None
        }
    }
    // The item put at a place, what was there and after it moving up; the
    // item given back if there is no such place.
    pub fn insert(value: &mut Self, index: Int, item: T) -> Result<(), T> {
        let items = &mut value.items;
        let n = len_at(&*items);
        if(index < 0) { Err(item) } else {
            if(index > n) { Err(item) } else {
                match(taken_off(replace(items, []), n - index, [])) {
                    (before, off) => *items = put_back(push(before, item), off); Ok(())
                }
            }
        }
    }
    // The element at a place taken out, what was after it moving down.
    pub fn remove(value: &mut Self, index: Int) -> Option<T> {
        let items = &mut value.items;
        let n = len_at(&*items);
        if(index < 0) { None } else {
            if(index >= n) { None } else {
                match(taken_off(replace(items, []), n - index - 1, [])) {
                    (upto, off) => match(pop(upto)) {
                        Some((before, taken)) => *items = put_back(before, off); Some(taken),
                        None => None
                    }
                }
            }
        }
    }
    // Everything of another put after what is here.
    pub fn append(value: &mut Self, source: Self) {
        let items = &mut value.items;
        match(source) { Vec { items: more } => *items = put_back(replace(items, []), turned(more, [])) }
    }
    pub fn reverse(value: &mut Self) {
        let items = &mut value.items;
        *items = turned(replace(items, []), []);
    }
    // Only so many kept: the rest are let go.
    pub fn truncate(value: &mut Self, length: Int) {
        let items = &mut value.items;
        let n = len_at(&*items);
        *items = taken_off(replace(items, []), n - length, []).0;
    }
    pub fn clear(value: &mut Self) {
        let items = &mut value.items;
        *items = [];
    }
    // The elements as a slice: looked at where they are.
    pub fn as_slice<'a>(value: &'a Self) -> Slice<'a, T> { Slice::of(&value.items) }
    // The elements one after another, by reference.
    pub fn iter<'a>(value: &'a Self) -> SliceIter<'a, T> { Slice::iter(&Slice::of(&value.items)) }
}
"#

private def textText : String := r#"// Texts: `Str`.

use std::vec;

pub fn is_empty(text: Str) -> Bool { match(text) { StrEnd => true, _ => false } }

pub fn reverse(text: Str) -> Str { reverse_onto(text, "") }
fn reverse_onto(text: Str, out: Str) -> Str {
    match(text) { StrEnd => out, StrChar(c, rest) => tail reverse_onto(rest, StrChar(c, out)) }
}

// Does a text begin, end, or have somewhere in it, another?
pub fn starts_with(text: Str, start: Str) -> Bool {
    match((text, start)) {
        (_, StrEnd) => true,
        (StrChar(c, rest), StrChar(d, more)) => if(c == d) { starts_with(rest, more) } else { false },
        _ => false
    }
}
pub fn ends_with(text: Str, end: Str) -> Bool { starts_with(reverse(text), reverse(end)) }
pub fn contains(text: Str, part: Str) -> Bool { match(find(text, part)) { Some(_) => true, None => false } }

// Where a part of a text first begins.
pub fn find(text: Str, part: Str) -> Option<Int> { find_from(text, part, 0) }
fn find_from(text: Str, part: Str, at: Int) -> Option<Int> {
    if(starts_with(text, part)) { Some(at) } else {
        match(text) { StrEnd => None, StrChar(_, rest) => tail find_from(rest, part, at + 1) }
    }
}

// The first `n` characters, and the rest.
pub fn take(text: Str, n: Int) -> Str {
    if(n <= 0) { "" } else { match(text) { StrEnd => "", StrChar(c, rest) => StrChar(c, take(rest, n - 1)) } }
}
pub fn drop(text: Str, n: Int) -> Str {
    if(n <= 0) { text } else { match(text) { StrEnd => "", StrChar(_, rest) => tail drop(rest, n - 1) } }
}

pub fn char_at(text: Str, i: Int) -> Option<char> {
    match(text) { StrEnd => None, StrChar(c, rest) => if(i == 0) { Some(c) } else { tail char_at(rest, i - 1) } }
}

pub fn map(text: Str, f) -> Str {
    match(text) { StrEnd => "", StrChar(c, rest) => StrChar(f(c), map(rest, f)) }
}
pub fn to_upper(text: Str) -> Str { map(text, std::char::to_upper) }
pub fn to_lower(text: Str) -> Str { map(text, std::char::to_lower) }

// The text without the spaces at its ends.
pub fn trim(text: Str) -> Str { reverse(trim_start(reverse(trim_start(text)))) }
pub fn trim_start(text: Str) -> Str {
    match(text) {
        StrEnd => "",
        StrChar(c, rest) => if(std::char::is_space(c)) { tail trim_start(rest) } else { text }
    }
}

// The parts of a text between each two of a character.
pub fn split(text: Str, at: char) -> [Str] { split_onto(text, at, "", []) }
fn split_onto(text: Str, at: char, part: Str, out: [Str]) -> [Str] {
    match(text) {
        StrEnd => push(out, reverse(part)),
        StrChar(c, rest) =>
            if(c == at) { tail split_onto(rest, at, "", push(out, reverse(part))) }
            else { tail split_onto(rest, at, StrChar(c, part), out) }
    }
}
pub fn lines(text: Str) -> [Str] { split(text, '\n') }

// The words of a text: what is between its spaces.
pub fn words(text: Str) -> [Str] { vec::filter(split(map(text, { c => if(std::char::is_space(c)) { ' ' } else { c } }), ' '), { w => not is_empty(w) }) }

// Texts one after another, with another between each two.
pub fn join(parts: [Str], between: Str) -> Str {
    fold(parts, "", fn(out, part) { if(is_empty(out)) { part } else { out ++ between ++ part } })
}
pub fn concat(parts: [Str]) -> Str { fold(parts, "", fn(out, part) { out ++ part }) }

pub fn repeat(text: Str, n: Int) -> Str { if(n <= 0) { "" } else { text ++ repeat(text, n - 1) } }

// The whole number a text writes, if it writes one: digits, perhaps after `-`.
pub fn parse_int(text: Str) -> Option<Int> {
    match(text) {
        StrChar('-', rest) => match(digits_value(rest, 0, 0)) { Some(n) => Some(0 - n), None => None },
        _ => digits_value(text, 0, 0)
    }
}
fn digits_value(text: Str, seen: Int, value: Int) -> Option<Int> {
    match(text) {
        StrEnd => if(seen > 0) { Some(value) } else { None },
        StrChar(c, rest) => match(std::char::digit(c)) {
            Some(d) => tail digits_value(rest, seen + 1, value * 10 + d),
            None => None
        }
    }
}

// A text put to a width with a character before it, or after it.
pub fn pad_start(text: Str, width: Int, with: char) -> Str {
    if(length(text) < width) { tail pad_start(StrChar(with, text), width, with) } else { text }
}
pub fn pad_end(text: Str, width: Int, with: char) -> Str {
    reverse(pad_start(reverse(text), width, with))
}

// A text as bytes: each character as UTF-8 has it.
pub fn utf8(text: Str) -> [u8] { utf8_onto(text, []) }
fn utf8_onto(text: Str, out: [u8]) -> [u8] {
    match(text) {
        StrEnd => out,
        StrChar(c, rest) => tail utf8_onto(rest, encode(int(c), out))
    }
}
fn byte(n: Int) -> u8 { u8(n) }
fn encode(code: Int, out: [u8]) -> [u8] {
    if(code < 128) { push(out, byte(code)) } else {
        if(code < 2048) { push(push(out, byte(192 + code / 64)), byte(128 + code % 64)) } else {
            if(code < 65536) {
                push(push(push(out, byte(224 + code / 4096)), byte(128 + code / 64 % 64)), byte(128 + code % 64))
            } else {
                push(push(push(push(out, byte(240 + code / 262144)), byte(128 + code / 4096 % 64)),
                    byte(128 + code / 64 % 64)), byte(128 + code % 64))
            }
        }
    }
}

// The text some bytes are, if they are UTF-8.
pub fn from_utf8(bytes: [u8]) -> Option<Str> { decode(bytes, len(bytes), "") }
// Read from the end, so that the text is built from its last character back.
fn decode(bytes: [u8], end: Int, out: Str) -> Option<Str> {
    if(end == 0) { Some(out) } else {
        let last = int(bytes[end - 1]);
        if(last < 128) { tail decode_one(bytes, end - 1, last, out) } else {
            if(end < 2) { None } else {
                let b1 = int(bytes[end - 2]);
                if(b1 >= 192) { tail decode_one(bytes, end - 2, (b1 - 192) * 64 + (last - 128), out) } else {
                    if(end < 3) { None } else {
                        let b2 = int(bytes[end - 3]);
                        if(b2 >= 224) {
                            tail decode_one(bytes, end - 3, ((b2 - 224) * 64 + (b1 - 128)) * 64 + (last - 128), out)
                        } else {
                            if(end < 4) { None } else {
                                let b3 = int(bytes[end - 4]);
                                tail decode_one(bytes, end - 4,
                                    (((b3 - 240) * 64 + (b2 - 128)) * 64 + (b1 - 128)) * 64 + (last - 128), out)
                            }
                        }
                    }
                }
            }
        }
    }
}
fn decode_one(bytes: [u8], end: Int, code: Int, out: Str) -> Option<Str> {
    match(char(code)) { Some(c) => tail decode(bytes, end, StrChar(c, out)), None => None }
}

// An owned text that grows where it is, in the shape the library
// specification gives it (13): its bytes, which are UTF-8.
pub struct String { bytes: [u8] }

fn bytes_onto(a: [u8], b: [u8], i: Int) -> [u8] {
    if(i >= len(b)) { a } else { tail bytes_onto(push(a, b[i]), b, i + 1) }
}

impl String {
    pub fn new() -> Self { Self { bytes: [] } }
    pub fn from_str(text: Str) -> Self { Self { bytes: utf8(text) } }
    pub fn from_utf8(bytes: [u8]) -> Result<Self, [u8]> {
        match(from_utf8(bytes)) { Some(_) => Ok(Self { bytes: bytes }), None => Err(bytes) }
    }
    pub fn into_bytes(value: Self) -> [u8] { match(value) { String { bytes } => bytes } }
    // The text as a value of its own.
    pub fn to_str(value: &Self) -> Str {
        match(from_utf8(value.bytes)) { Some(text) => text, None => "" }
    }
    // How many bytes.
    pub fn len(value: &Self) -> Int { len_at(&value.bytes) }
    pub fn is_empty(value: &Self) -> Bool { len_at(&value.bytes) == 0 }
    pub fn push_str(value: &mut Self, text: Str) {
        let bytes = &mut value.bytes;
        *bytes = bytes_onto(replace(bytes, []), utf8(text), 0);
    }
    pub fn push(value: &mut Self, c: char) { String::push_str(value, show(c)) }
    pub fn clear(value: &mut Self) {
        let bytes = &mut value.bytes;
        *bytes = [];
    }
}
"#

private def mapText : String := r#"// A map from keys to values, the keys kept in order: a tree that stays
// balanced, so finding, adding and taking away go through as many keys as the
// number of keys has bits. A key is a type with `<`.

enum Node<K, V> { Leaf, Branch(Node<K, V>, K, V, Node<K, V>, Int) }

pub struct Map<K, V>(Node<K, V>)

pub fn new() { Map(Leaf) }

fn height(n) { match(n) { Leaf => 0, Branch(_, _, _, _, h) => h } }

fn branch(l, k, v, r) {
    let hl = height(l);
    let hr = height(r);
    Branch(l, k, v, r, 1 + (if(hl < hr) { hr } else { hl }))
}

// A tree with these parts, turned if one side is two deeper than the other.
fn balance(l, k, v, r) {
    let hl = height(l);
    let hr = height(r);
    if(hl > hr + 1) {
        match(l) {
            Branch(ll, lk, lv, lr, _) =>
                if(height(ll) >= height(lr)) { branch(ll, lk, lv, branch(lr, k, v, r)) }
                else {
                    match(lr) {
                        Branch(lrl, lrk, lrv, lrr, _) =>
                            branch(branch(ll, lk, lv, lrl), lrk, lrv, branch(lrr, k, v, r)),
                        Leaf => branch(l, k, v, r)
                    }
                },
            Leaf => branch(l, k, v, r)
        }
    } else {
        if(hr > hl + 1) {
            match(r) {
                Branch(rl, rk, rv, rr, _) =>
                    if(height(rr) >= height(rl)) { branch(branch(l, k, v, rl), rk, rv, rr) }
                    else {
                        match(rl) {
                            Branch(rll, rlk, rlv, rlr, _) =>
                                branch(branch(l, k, v, rll), rlk, rlv, branch(rlr, rk, rv, rr)),
                            Leaf => branch(l, k, v, r)
                        }
                    },
                Leaf => branch(l, k, v, r)
            }
        } else { branch(l, k, v, r) }
    }
}

fn put(n, key, value) {
    match(n) {
        Leaf => Branch(Leaf, key, value, Leaf, 1),
        Branch(l, k, v, r, h) =>
            if(key < k) { balance(put(l, key, value), k, v, r) }
            else { if(k < key) { balance(l, k, v, put(r, key, value)) } else { Branch(l, key, value, r, h) } }
    }
}

// The map with `key` standing for `value`, whatever it stood for.
pub fn insert(m, key, value) { match(m) { Map(n) => Map(put(n, key, value)) } }

fn look(n, key) {
    match(n) {
        Leaf => None,
        Branch(l, k, v, r, _) =>
            if(key < k) { tail look(l, key) } else { if(k < key) { tail look(r, key) } else { Some(v) } }
    }
}

// What `key` stands for.
pub fn get(m, key) { match(m) { Map(n) => look(n, key) } }

// What a key stands for, where it is in the tree.
fn look_ref<'a, K, V>(n: &'a Node<K, V>, key: K) -> Option<&'a V> where K: Ord {
    match(n) {
        &Leaf => None,
        &Branch(l, k, v, r, _) =>
            if(key < *k) { tail look_ref(l, key) }
            else { if(*k < key) { tail look_ref(r, key) } else { Some(v) } }
    }
}

fn look_mut<'a, K, V>(n: &'a mut Node<K, V>, key: K) -> Option<&'a mut V> where K: Ord {
    match(n) {
        &mut Leaf => None,
        &mut Branch(l, k, v, r, _) =>
            if(key < *k) { tail look_mut(l, key) }
            else { if(*k < key) { tail look_mut(r, key) } else { Some(v) } }
    }
}

// The same map looked into and changed where it is, in the shape the library
// specification gives its maps (17).
impl<K, V> Map<K, V> {
    pub fn get_ref<'a>(m: &'a Self, key: K) -> Option<&'a V> where K: Ord { look_ref(&m.0, key) }
    pub fn get_mut<'a>(m: &'a mut Self, key: K) -> Option<&'a mut V> where K: Ord {
        look_mut(&mut m.0, key)
    }
}

pub fn contains_key(m, key) { match(get(m, key)) { Some(_) => true, None => false } }

// The least key of a tree that is not empty, what it stands for, and the rest.
fn take_least(l, k, v, r) {
    match(l) {
        Leaf => (k, v, r),
        Branch(ll, lk, lv, lr, _) =>
            match(take_least(ll, lk, lv, lr)) { (mk, mv, rest) => (mk, mv, balance(rest, k, v, r)) }
    }
}

fn cut(n, key) {
    match(n) {
        Leaf => Leaf,
        Branch(l, k, v, r, _) =>
            if(key < k) { balance(cut(l, key), k, v, r) }
            else {
                if(k < key) { balance(l, k, v, cut(r, key)) }
                else {
                    match(r) {
                        Leaf => l,
                        Branch(rl, rk, rv, rr, _) =>
                            match(take_least(rl, rk, rv, rr)) { (mk, mv, rest) => balance(l, mk, mv, rest) }
                    }
                }
            }
    }
}

// The map without `key`.
pub fn remove(m, key) { match(m) { Map(n) => Map(cut(n, key)) } }

fn walk(n, init, f) {
    match(n) {
        Leaf => init,
        Branch(l, k, v, r, _) => walk(r, f(walk(l, init, f), k, v), f)
    }
}

// `f(f(init, k0, v0), k1, v1)` and so on, the keys in order.
pub fn fold(m, init, f) { match(m) { Map(n) => walk(n, init, f) } }

pub fn len(m) { fold(m, 0, fn(n, k, v) { n + 1 }) }
pub fn is_empty(m) { match(m) { Map(Leaf) => true, _ => false } }

pub fn keys(m) { fold(m, [], fn(out, k, v) { push(out, k) }) }
pub fn values(m) { fold(m, [], fn(out, k, v) { push(out, v) }) }
pub fn entries(m) { fold(m, [], fn(out, k, v) { push(out, (k, v)) }) }

// The map of an array of keys with what each stands for; a later one wins.
pub fn from(pairs) { std::vec::fold_pairs(pairs, new(), fn(m, k, v) { insert(m, k, v) }) }

// The map with `key` standing for what `f` makes of what it stood for.
pub fn update(m, key, f) { insert(m, key, f(get(m, key))) }

// The least and the greatest key, each with what it stands for.
pub fn least(m) { match(entries(m)) { es => std::vec::first(es) } }
pub fn greatest(m) { match(entries(m)) { es => std::vec::last(es) } }
"#

private def setText : String := r#"// A set of values kept in order: a map from each to nothing.

use std::map;
use std::map::Map;

pub struct Set<T>(Map<T, ()>)

pub fn new() { Set(map::new()) }

pub fn insert(s, x) { match(s) { Set(m) => Set(map::insert(m, x, ())) } }
pub fn remove(s, x) { match(s) { Set(m) => Set(map::remove(m, x)) } }
pub fn contains(s, x) { match(s) { Set(m) => map::contains_key(m, x) } }
pub fn len(s) { match(s) { Set(m) => map::len(m) } }
pub fn is_empty(s) { match(s) { Set(m) => map::is_empty(m) } }

// The values, in order.
pub fn to_array(s) { match(s) { Set(m) => map::keys(m) } }

// The set of the values of an array.
pub fn from(a) { fold(a, new(), fn(s, x) { insert(s, x) }) }

pub fn fold_set(s, init, f) { match(s) { Set(m) => map::fold(m, init, fn(acc, k, v) { f(acc, k) }) } }

// What is in either, in both, and in the first but not the second.
pub fn union(a, b) { fold_set(b, a, fn(s, x) { insert(s, x) }) }
pub fn intersection(a, b) { fold_set(a, new(), fn(s, x) { if(contains(b, x)) { insert(s, x) } else { s } }) }
pub fn difference(a, b) { fold_set(b, a, fn(s, x) { remove(s, x) }) }
pub fn is_subset(a, b) { fold_set(a, true, fn(ok, x) { ok and { contains(b, x) } }) }
"#

private def iterText : String := r#"// Values one at a time, each made when it is asked for. An `Iter<T>` is asked
// with `next`, which gives the next value and what is left.

pub struct Iter<T>(fn() -> Option<(T, Iter<T>)>)

pub fn next(it) { match(it) { Iter(step) => step() } }

pub fn empty() { Iter({ None }) }

// The numbers from `from` up to, not including, `to`.
pub fn range(from: Int, to: Int) -> Iter<Int> {
    Iter({ if(from < to) { Some((from, range(from + 1, to))) } else { None } })
}

// `seed`, `f(seed)`, `f(f(seed))`, without end.
pub fn iterate(seed, f) { Iter({ Some((seed, iterate(f(seed), f))) }) }

pub fn repeat(x) { Iter({ Some((x, repeat(x))) }) }

// The elements of an array.
pub fn of(a) { of_from(a, 0) }
fn of_from(a, i: Int) { Iter({ if(i < len(a)) { Some((a[i], of_from(a, i + 1))) } else { None } }) }

pub fn map(it, f) {
    Iter({ match(next(it)) { Some((x, rest)) => Some((f(x), map(rest, f))), None => None } })
}

pub fn filter(it, keep) { Iter({ filter_next(it, keep) }) }
fn filter_next(it, keep) {
    match(next(it)) {
        Some((x, rest)) => if(keep(x)) { Some((x, filter(rest, keep))) } else { tail filter_next(rest, keep) },
        None => None
    }
}

// The first `n`, and what is after them.
pub fn take(it, n: Int) {
    Iter({ if(n <= 0) { None } else { match(next(it)) { Some((x, rest)) => Some((x, take(rest, n - 1))), None => None } } })
}
pub fn skip(it, n: Int) {
    if(n <= 0) { it } else { match(next(it)) { Some((_, rest)) => tail skip(rest, n - 1), None => empty() } }
}

// The values while `keep` says yes.
pub fn take_while(it, keep) {
    Iter({ match(next(it)) {
        Some((x, rest)) => if(keep(x)) { Some((x, take_while(rest, keep))) } else { None },
        None => None
    } })
}

// One after another.
pub fn chain(a, b) {
    Iter({ match(next(a)) { Some((x, rest)) => Some((x, chain(rest, b))), None => next(b) } })
}

// Pairs, as many as the shorter gives.
pub fn zip(a, b) {
    Iter({ match(next(a)) {
        Some((x, ra)) => match(next(b)) { Some((y, rb)) => Some(((x, y), zip(ra, rb))), None => None },
        None => None
    } })
}

// Each value with how many came before it.
pub fn enumerate(it) { zip(iterate(0, { n => n + 1 }), it) }

// `f(f(init, x0), x1)` and so on, of every value.
pub fn fold(it, init, f) {
    match(next(it)) { Some((x, rest)) => tail fold(rest, f(init, x), f), None => init }
}

pub fn collect(it) { fold(it, [], fn(out, x) { push(out, x) }) }
pub fn count(it) { fold(it, 0, fn(n, x) { n + 1 }) }
pub fn sum(it) { fold(it, 0, fn(total, x) { total + x }) }
pub fn each(it, f) { fold(it, (), fn(done, x) { f(x) }) }

// The first value `wanted` says yes to.
pub fn find(it, wanted) {
    match(next(it)) {
        Some((x, rest)) => if(wanted(x)) { Some(x) } else { tail find(rest, wanted) },
        None => None
    }
}
pub fn any(it, wanted) { match(find(it, wanted)) { Some(_) => true, None => false } }
pub fn all(it, wanted) { not any(it, { x => not wanted(x) }) }
"#

private def hostText : String := r#"// What a program asks of the machine it runs on: the console, files, the
// environment, clocks, chance. Each is an effect, so that a program's type
// says what it may ask for and whoever runs it decides what it gets.
// `run_host` answers them all with the operating system, through C: it is
// the one place here that is unsafe, and it has no meaning on the proved
// machines.

use std::c::{malloc, free, c_string, text_at, write_bytes, read_byte};
use std::text::{utf8, from_utf8};

// Why the operating system refused: its number for the reason.
pub struct IoError { pub code: Int }

pub effect Console {
    write_stdout(bytes: [u8]) -> Result<Int, IoError>
    write_stderr(bytes: [u8]) -> Result<Int, IoError>
    read_stdin(most: Int) -> Result<[u8], IoError>
}
pub effect FileRead {
    read_file(path: Str) -> Result<[u8], IoError>
}
pub effect FileWrite {
    write_file(path: Str, bytes: [u8]) -> Result<(), IoError>
    write_file_atomic(path: Str, bytes: [u8]) -> Result<(), IoError>
}
pub effect Diagnostic {
    write_diagnostic(text: Str) -> Result<(), IoError>
}
pub effect ProcessEnvironment {
    env(name: Str) -> Result<Option<Str>, IoError>
    current_dir() -> Result<Str, IoError>
}
pub effect ProcessArgs {
    args() -> Result<[Str], IoError>
}
pub effect Clock {
    now() -> Int
    monotonic() -> Int
}
pub effect Entropy {
    random_bytes(n: Int) -> Result<[u8], IoError>
}

extern "C" {
    fn open(path: usize, flags: i32, mode: i32) -> i32;
    fn close(fd: i32) -> i32;
    fn read(fd: i32, buf: usize, n: usize) -> isize;
    fn write(fd: i32, buf: usize, n: usize) -> isize;
    fn rename(from: usize, to: usize) -> i32;
    fn getenv(name: usize) -> usize;
    fn getcwd(buf: usize, n: usize) -> usize;
    fn clock_gettime(clock: i32, at: usize) -> i32;
    fn getrandom(buf: usize, n: usize, flags: u32) -> isize;
    fn __errno_location() -> usize;
}

unsafe fn refused() -> IoError { IoError { code: ptr_read(__errno_location(), 32) } }

// Every byte written, or why not.
unsafe fn write_all(fd: i32, bytes: [u8]) -> Result<Int, IoError> {
    let n = len(bytes);
    let at = malloc(usize(n + 1));
    write_bytes(at, bytes);
    let done = write_on(fd, at, n, 0);
    free(at);
    done
}
unsafe fn write_on(fd: i32, at: usize, n: Int, sent: Int) -> Result<Int, IoError> {
    if(sent >= n) { Ok(n) } else {
        let k = int(write(fd, at + usize(sent), usize(n - sent)));
        if(k < 0) { Err(refused()) } else { tail write_on(fd, at, n, sent + k) }
    }
}

unsafe fn bytes_at(out: [u8], at: usize, n: Int) -> [u8] {
    if(n <= 0) { out } else { tail bytes_at(push(out, read_byte(at)), at + 1usize, n - 1) }
}

// What can be read now, at most so many bytes: none at the end.
unsafe fn read_some(fd: i32, most: Int) -> Result<[u8], IoError> {
    let room = if(most < 1) { 1 } else { most };
    let buf = malloc(usize(room));
    let k = int(read(fd, buf, usize(room)));
    let got = if(k < 0) { Err(refused()) } else { Ok(bytes_at([], buf, k)) };
    free(buf);
    got
}

// Everything there is to read.
unsafe fn read_all(fd: i32, buf: usize, out: [u8]) -> Result<[u8], IoError> {
    let k = int(read(fd, buf, 65536usize));
    if(k < 0) { Err(refused()) } else {
        if(k == 0) { Ok(out) } else { tail read_all(fd, buf, bytes_at(out, buf, k)) }
    }
}

unsafe fn read_path(path: Str) -> Result<[u8], IoError> {
    let p = c_string(path);
    let fd = open(p, 0i32, 0i32);
    free(p);
    if(fd < 0i32) { Err(refused()) } else {
        let buf = malloc(65536usize);
        let got = read_all(fd, buf, []);
        free(buf);
        close(fd);
        got
    }
}

// Made if it is not there, emptied if it is, readable by all and writable
// by its owner.
unsafe fn write_path(path: Str, bytes: [u8]) -> Result<(), IoError> {
    let p = c_string(path);
    let fd = open(p, 577i32, 420i32);
    free(p);
    if(fd < 0i32) { Err(refused()) } else {
        let done = write_all(fd, bytes);
        close(fd);
        match(done) { Ok(_) => Ok(()), Err(e) => Err(e) }
    }
}

// Written beside the file and then given its name, so that the name is
// never that of half a file.
unsafe fn write_path_atomic(path: Str, bytes: [u8]) -> Result<(), IoError> {
    let beside = path ++ ".writing";
    match(write_path(beside, bytes)) {
        Err(e) => Err(e),
        Ok(_) =>
            let from = c_string(beside);
            let to = c_string(path);
            let moved = rename(from, to);
            free(from);
            free(to);
            if(moved < 0i32) { Err(refused()) } else { Ok(()) }
    }
}

unsafe fn look_up(name: Str) -> Result<Option<Str>, IoError> {
    let n = c_string(name);
    let at = getenv(n);
    free(n);
    if(at == 0usize) { Ok(None) } else {
        match(text_at(at)) { Some(text) => Ok(Some(text)), None => Err(IoError { code: 84 }) }
    }
}

unsafe fn where_now() -> Result<Str, IoError> {
    let buf = malloc(4096usize);
    let at = getcwd(buf, 4096usize);
    let got = if(at == 0usize) { Err(refused()) } else {
        match(text_at(buf)) { Some(text) => Ok(text), None => Err(IoError { code: 84 }) }
    };
    free(buf);
    got
}

// The texts between zeros.
fn between_zeros(bytes: [u8], i: Int, word: [u8], out: [Str]) -> [Str] {
    if(i >= len(bytes)) { out } else {
        if(int(bytes[i]) == 0) {
            let text = match(from_utf8(word)) { Some(t) => t, None => "" };
            tail between_zeros(bytes, i + 1, [], push(out, text))
        } else { tail between_zeros(bytes, i + 1, push(word, bytes[i]), out) }
    }
}

// What the process was started with, as the operating system has it.
unsafe fn arguments() -> Result<[Str], IoError> {
    match(read_path("/proc/self/cmdline")) {
        Ok(bytes) => Ok(between_zeros(bytes, 0, [], [])),
        Err(e) => Err(e)
    }
}

// Nanoseconds on one of the operating system's clocks.
unsafe fn clock(which: i32) -> Int {
    let at = malloc(16usize);
    clock_gettime(which, at);
    let nanos = ptr_read(at, 64) * 1000000000 + ptr_read(at + 8usize, 64);
    free(at);
    nanos
}

unsafe fn chance(n: Int) -> Result<[u8], IoError> {
    let room = if(n < 1) { 1 } else { n };
    let buf = malloc(usize(room));
    let k = int(getrandom(buf, usize(n), 0u32));
    let got = if(k < n) { Err(refused()) } else { Ok(bytes_at([], buf, n)) };
    free(buf);
    got
}

// Run a computation with the operating system answering what it asks for.
pub fn run_host(main) {
    handle(main()) {
        write_stdout(bytes, k) => k(unsafe { write_all(1i32, bytes) }),
        write_stderr(bytes, k) => k(unsafe { write_all(2i32, bytes) }),
        read_stdin(most, k) => k(unsafe { read_some(0i32, most) }),
        read_file(path, k) => k(unsafe { read_path(path) }),
        write_file(path, bytes, k) => k(unsafe { write_path(path, bytes) }),
        write_file_atomic(path, bytes, k) => k(unsafe { write_path_atomic(path, bytes) }),
        write_diagnostic(text, k) => k(unsafe {
            match(write_all(2i32, utf8(text ++ "\n"))) { Ok(_) => Ok(()), Err(e) => Err(e) }
        }),
        env(name, k) => k(unsafe { look_up(name) }),
        current_dir(k) => k(unsafe { where_now() }),
        args(k) => k(unsafe { arguments() }),
        now(k) => k(unsafe { clock(0i32) }),
        monotonic(k) => k(unsafe { clock(1i32) }),
        random_bytes(n, k) => k(unsafe { chance(n) }),
        x => x
    }
}

// A text on standard output, and the same with a line's end.
pub fn print(text: Str) { write_stdout(utf8(text)); () }
pub fn println(text: Str) { print(text ++ "\n") }
pub fn eprintln(text: Str) { write_stderr(utf8(text ++ "\n")); () }

// A file as text, if it is UTF-8.
pub fn read_text(path: Str) -> Result<Str, IoError> {
    match(read_file(path)) {
        Ok(bytes) => match(from_utf8(bytes)) { Some(text) => Ok(text), None => Err(IoError { code: 84 }) },
        Err(e) => Err(e)
    }
}
pub fn write_text(path: Str, text: Str) -> Result<(), IoError> { write_file(path, utf8(text)) }

// The next line of standard input without its end, or nothing at the end.
pub fn read_line() -> Option<Str> { line_from([], false) }
fn line_from(line: [u8], any: Bool) -> Option<Str> {
    match(read_stdin(1)) {
        Err(_) => None,
        Ok(bytes) =>
            if(len(bytes) == 0) {
                if(any) { from_utf8(line) } else { None }
            } else {
                if(int(bytes[0]) == 10) { from_utf8(line) } else { tail line_from(push(line, bytes[0]), true) }
            }
    }
}
"#

private def collectionsText : String := r#"// Queues and heaps: collections changed where they are, through a `&mut`
// reference, in the shape the library specification gives them (16).

use std::vec::{swap};

// A queue with two ends. What is at the front is kept turned round, so that
// both ends are the ends of an array: putting and taking at either end takes
// time that does not grow with the queue, counted over many of them.
pub struct VecDeque<T> { front: [T], back: [T] }

// The elements of one array onto another, last first.
fn turned<T>(from: [T], onto: [T]) -> [T] {
    match(pop(from)) {
        Some((rest, last)) => tail turned(rest, push(onto, last)),
        None => onto
    }
}

impl<T> VecDeque<T> {
    pub fn new() -> Self { Self { front: [], back: [] } }
    pub fn from_vec(items: [T]) -> Self { Self { front: [], back: items } }
    pub fn into_vec(value: Self) -> [T] {
        match(value) { VecDeque { front, back } => turned(turned(back, []), turned(front, [])) }
    }
    pub fn len(value: &Self) -> Int { len_at(&value.front) + len_at(&value.back) }
    pub fn is_empty(value: &Self) -> Bool { VecDeque::len(value) == 0 }
    pub fn push_back(value: &mut Self, item: T) {
        let back = &mut value.back;
        *back = push(replace(back, []), item);
    }
    pub fn push_front(value: &mut Self, item: T) {
        let front = &mut value.front;
        *front = push(replace(front, []), item);
    }
    pub fn pop_front(value: &mut Self) -> Option<T> {
        // With nothing kept at the front, what is at the back is turned
        // round to be it.
        let front = &mut value.front;
        let back = &mut value.back;
        let ready = if(len_at(&*front) == 0) { turned(replace(back, []), []) } else { replace(front, []) };
        match(pop(ready)) {
            Some((rest, first)) => *front = rest; Some(first),
            None => None
        }
    }
    pub fn pop_back(value: &mut Self) -> Option<T> {
        let front = &mut value.front;
        let back = &mut value.back;
        let ready = if(len_at(&*back) == 0) { turned(replace(front, []), []) } else { replace(back, []) };
        match(pop(ready)) {
            Some((rest, last)) => *back = rest; Some(last),
            None => None
        }
    }
    // The element so far from the front, by reference.
    pub fn get<'a>(value: &'a Self, index: Int) -> Option<&'a T> {
        let ahead = len_at(&value.front);
        if(index < ahead) { element(&value.front, ahead - 1 - index) } else { element(&value.back, index - ahead) }
    }
    pub fn front<'a>(value: &'a Self) -> Option<&'a T> { VecDeque::get(value, 0) }
    pub fn back<'a>(value: &'a Self) -> Option<&'a T> { VecDeque::get(value, VecDeque::len(value) - 1) }
}

// A heap: the greatest element is the one taken. Its elements are compared
// and moved by copying, so they are of a type used any number of times.
pub struct BinaryHeap<T> { items: [T] }

// The element at `i` moved up to where nothing above it is smaller.
fn risen<T>(a: [T], i: Int) -> [T] where T: Ord {
    if(i == 0) { a } else {
        let parent = (i - 1) / 2;
        if(a[parent] < a[i]) { tail risen(swap(a, parent, i), parent) } else { a }
    }
}

// The element at `i` moved down to where nothing below it is greater.
fn sunk<T>(a: [T], i: Int, n: Int) -> [T] where T: Ord {
    let left = 2 * i + 1;
    let right = left + 1;
    let over_left = if(left < n) { if(a[i] < a[left]) { left } else { i } } else { i };
    let most = if(right < n) { if(a[over_left] < a[right]) { right } else { over_left } } else { over_left };
    if(most == i) { a } else { tail sunk(swap(a, i, most), most, n) }
}

fn heaped<T>(a: [T], i: Int) -> [T] where T: Ord {
    if(i < 0) { a } else { let n = len(a); tail heaped(sunk(a, i, n), i - 1) }
}

fn drained<T>(a: [T], out: [T]) -> [T] where T: Ord {
    let n = len(a);
    if(n == 0) { out } else {
        let top = a[0];
        let moved = swap(a, 0, n - 1);
        match(pop(moved)) {
            Some((rest, _)) => tail drained(sunk(rest, 0, n - 1), push(out, top)),
            None => out
        }
    }
}

impl<T> BinaryHeap<T> {
    pub fn new() -> Self { Self { items: [] } }
    pub fn from_vec(items: [T]) -> Self where T: Ord { let n = len(items); Self { items: heaped(items, n / 2) } }
    pub fn into_vec(value: Self) -> [T] { match(value) { BinaryHeap { items } => items } }
    // Greatest first.
    pub fn into_sorted_vec(value: Self) -> [T] where T: Ord { match(value) { BinaryHeap { items } => drained(items, []) } }
    pub fn len(value: &Self) -> Int { len_at(&value.items) }
    pub fn is_empty(value: &Self) -> Bool { len_at(&value.items) == 0 }
    pub fn peek<'a>(value: &'a Self) -> Option<&'a T> { element(&value.items, 0) }
    pub fn push(value: &mut Self, item: T) where T: Ord {
        let items = &mut value.items;
        let with = push(replace(items, []), item);
        let n = len(with);
        *items = risen(with, n - 1);
    }
    pub fn pop(value: &mut Self) -> Option<T> where T: Ord {
        let items = &mut value.items;
        let all = replace(items, []);
        let n = len(all);
        if(n == 0) { None } else {
            match(pop(swap(all, 0, n - 1))) {
                Some((rest, top)) => *items = sunk(rest, 0, n - 1); Some(top),
                None => None
            }
        }
    }
}
"#

private def iteratorText : String := r#"// One value at a time, asked for through a `&mut` reference: the shape the
// library specification gives iteration (18). What is iterated says what its
// values are (`Item`); what uses them is a function over anything iterated.

pub trait Iterator {
    type Item;
    fn next(&mut Self) -> Option<Self::Item>;
}

// The whole numbers from one up to, not including, another.
pub struct Range { at: Int, end: Int }
pub fn range(from: Int, to: Int) -> Range { Range { at: from, end: to } }
impl Iterator for Range {
    type Item = Int;
    fn next(r) { if(r.at < r.end) { let v = r.at; r.at = v + 1; Some(v) } else { None } }
}

fn turned<T>(from: [T], onto: [T]) -> [T] {
    match(pop(from)) {
        Some((rest, last)) => tail turned(rest, push(onto, last)),
        None => onto
    }
}

// The elements of an array, each given away, first to last.
pub struct IntoIter<T> { rest: [T] }
pub fn into_iter<T>(items: [T]) -> IntoIter<T> { IntoIter { rest: turned(items, []) } }
impl<T> Iterator for IntoIter<T> {
    type Item = T;
    fn next(it) {
        let rest = &mut it.rest;
        match(pop(replace(rest, []))) {
            Some((left, x)) => *rest = left; Some(x),
            None => None
        }
    }
}

// Every value, folded into one.
pub fn fold<I: Iterator, A>(it: &mut I, acc: A, f: fn(A, I::Item) -> A) -> A {
    match(next(it)) {
        Some(x) => tail fold(it, f(acc, x), f),
        None => acc
    }
}

// Something done with every value.
pub fn for_each<I: Iterator>(it: &mut I, f: fn(I::Item) -> ()) {
    match(next(it)) {
        Some(x) => f(x); tail for_each(it, f),
        None => ()
    }
}

// How many values are left; they are let go.
pub fn count<I: Iterator>(it: &mut I) -> Int { count_from(it, 0) }
fn count_from<I: Iterator>(it: &mut I, n: Int) -> Int {
    match(next(it)) {
        Some(_) => tail count_from(it, n + 1),
        None => n
    }
}

// The values left, as an array.
pub fn collect<I: Iterator>(it: &mut I) -> [I::Item] { collect_onto(it, []) }
fn collect_onto<I: Iterator>(it: &mut I, out: [I::Item]) -> [I::Item] {
    match(next(it)) {
        Some(x) => tail collect_onto(it, push(out, x)),
        None => out
    }
}

// What a function makes of each value, as an array.
pub fn map_collect<I: Iterator, B>(it: &mut I, f: fn(I::Item) -> B) -> [B] { map_onto(it, f, []) }
fn map_onto<I: Iterator, B>(it: &mut I, f: fn(I::Item) -> B, out: [B]) -> [B] {
    match(next(it)) {
        Some(x) => tail map_onto(it, f, push(out, f(x))),
        None => out
    }
}

// Iterators made from iterators. Each is a type of its own that holds the
// one it reads from, and gives a value only when asked: nothing is done
// until something is asked for. `A` is what the inner iterator gives; the
// implementation says so in its conditions.

// Each value, changed by a function.
pub struct Map<I, A, B> { inner: I, f: fn(A) -> B }
impl<I, A, B> Iterator for Map<I, A, B> where I: Iterator<Item = A> {
    type Item = B;
    fn next(it) {
        match(next(&mut it.inner)) {
            Some(x) => Some((it.f)(x)),
            None => None
        }
    }
}
pub fn map<I: Iterator, B>(it: I, f: fn(I::Item) -> B) -> Map<I, I::Item, B> {
    Map { inner: it, f: f }
}

// The values a test passes.
pub struct Filter<I, A> { inner: I, keep: for<'a> fn(&'a A) -> Bool }
impl<I, A> Iterator for Filter<I, A> where I: Iterator<Item = A> {
    type Item = A;
    fn next(it) {
        match(next(&mut it.inner)) {
            Some(x) => if((it.keep)(&x)) { Some(x) } else { next(it) },
            None => None
        }
    }
}
pub fn filter<I: Iterator>(it: I, keep: for<'a> fn(&'a I::Item) -> Bool) -> Filter<I, I::Item> {
    Filter { inner: it, keep: keep }
}

// The first so many values.
pub struct Take<I, A> { inner: I, left: Int }
impl<I, A> Iterator for Take<I, A> where I: Iterator<Item = A> {
    type Item = A;
    fn next(it) {
        if(it.left <= 0) { None } else {
            it.left = it.left - 1;
            next(&mut it.inner)
        }
    }
}
pub fn take<I: Iterator>(it: I, n: Int) -> Take<I, I::Item> {
    Take { inner: it, left: n }
}

// All but the first so many values.
pub struct Skip<I, A> { inner: I, left: Int }
impl<I, A> Iterator for Skip<I, A> where I: Iterator<Item = A> {
    type Item = A;
    fn next(it) {
        if(it.left <= 0) { next(&mut it.inner) } else {
            it.left = it.left - 1;
            match(next(&mut it.inner)) {
                Some(_) => next(it),
                None => None
            }
        }
    }
}
pub fn skip<I: Iterator>(it: I, n: Int) -> Skip<I, I::Item> {
    Skip { inner: it, left: n }
}

// Each value with its place, counted from zero.
pub struct Enumerate<I, A> { inner: I, at: Int }
impl<I, A> Iterator for Enumerate<I, A> where I: Iterator<Item = A> {
    type Item = (Int, A);
    fn next(it) {
        match(next(&mut it.inner)) {
            Some(x) =>
                let i = it.at;
                it.at = i + 1;
                Some((i, x)),
            None => None
        }
    }
}
pub fn enumerate<I: Iterator>(it: I) -> Enumerate<I, I::Item> {
    Enumerate { inner: it, at: 0 }
}

// The values of two iterators in pairs, for as long as both have one.
pub struct Zip<I, J, A, B> { left: I, right: J }
impl<I, J, A, B> Iterator for Zip<I, J, A, B> where I: Iterator<Item = A>, J: Iterator<Item = B> {
    type Item = (A, B);
    fn next(it) {
        match(next(&mut it.left)) {
            Some(a) => match(next(&mut it.right)) {
                Some(b) => Some((a, b)),
                None => None
            },
            None => None
        }
    }
}
pub fn zip<I: Iterator, J: Iterator>(a: I, b: J) -> Zip<I, J, I::Item, J::Item> {
    Zip { left: a, right: b }
}

// The values of one iterator, then those of another.
pub struct Chain<I, J, A> { first: I, second: J }
impl<I, J, A> Iterator for Chain<I, J, A> where I: Iterator<Item = A>, J: Iterator<Item = A> {
    type Item = A;
    fn next(it) {
        match(next(&mut it.first)) {
            Some(x) => Some(x),
            None => next(&mut it.second)
        }
    }
}
pub fn chain<I: Iterator, J: Iterator<Item = I::Item>>(a: I, b: J) -> Chain<I, J, I::Item> {
    Chain { first: a, second: b }
}

// The first value a test passes, if one does; those before it are let go.
pub fn find<I: Iterator>(it: &mut I, wanted: for<'a> fn(&'a I::Item) -> Bool) -> Option<I::Item> {
    match(next(it)) {
        Some(x) => if(wanted(&x)) { Some(x) } else { tail find(it, wanted) },
        None => None
    }
}

// The first thing a function makes of a value, where it makes anything; the
// values before that are let go.
pub fn find_map<I: Iterator, B>(it: &mut I, f: fn(I::Item) -> Option<B>) -> Option<B> {
    match(next(it)) {
        Some(x) => match(f(x)) {
            Some(found) => Some(found),
            None => tail find_map(it, f)
        },
        None => None
    }
}

// The value so many further on.
pub fn nth<I: Iterator>(it: &mut I, n: Int) -> Option<I::Item> {
    match(next(it)) {
        Some(x) => if(n <= 0) { Some(x) } else { tail nth(it, n - 1) },
        None => None
    }
}
"#

private def sliceText : String := r#"// A stretch of an array, borrowed: the array is not copied, and an element is
// looked at where it is. The shape the library specification gives a slice
// (14); places and lengths are `Int`.

use std::iterator::{Iterator};

pub struct Slice<'a, T> { items: &'a [T], from: Int, to: Int }

impl<'a, T> Slice<'a, T> {
    // The whole of an array.
    pub fn of(items: &'a [T]) -> Self { Self { items: items, from: 0, to: len_at(items) } }
    pub fn len(s: &Self) -> Int { s.to - s.from }
    pub fn is_empty(s: &Self) -> Bool { s.to == s.from }
    pub fn get(s: &Self, i: Int) -> Option<&'a T> {
        if(i < 0) { None } else {
            if(s.from + i < s.to) { element(s.items, s.from + i) } else { None }
        }
    }
    pub fn first(s: &Self) -> Option<&'a T> { Slice::get(s, 0) }
    pub fn last(s: &Self) -> Option<&'a T> { Slice::get(s, s.to - s.from - 1) }
    // The stretch from one place of this one up to, not including, another.
    pub fn sub(s: &Self, from: Int, to: Int) -> Option<Slice<'a, T>> {
        if(from < 0) { None } else {
            if(to < from) { None } else {
                if(s.from + to > s.to) { None } else {
                    Some(Slice { items: s.items, from: s.from + from, to: s.from + to })
                }
            }
        }
    }
    // What is before a place, and what is from it on.
    pub fn split_at(s: &Self, mid: Int) -> Option<(Slice<'a, T>, Slice<'a, T>)> {
        match(Slice::sub(s, 0, mid)) {
            Some(before) => match(Slice::sub(s, mid, s.to - s.from)) {
                Some(after) => Some((before, after)),
                None => None
            },
            None => None
        }
    }
    pub fn iter(s: &Self) -> SliceIter<'a, T> { SliceIter { items: s.items, at: s.from, end: s.to } }
}

// The elements of a slice by reference, first to last.
pub struct SliceIter<'a, T> { items: &'a [T], at: Int, end: Int }

impl<'a, T> Iterator for SliceIter<'a, T> {
    type Item = &'a T;
    fn next(it) {
        if(it.at < it.end) { let i = it.at; it.at = i + 1; element(it.items, i) } else { None }
    }
}
"#

private def fmtText : String := r#"// Text built up piece by piece into a sink the caller owns: the shape the
// library specification gives formatting (21). A type says how it is written
// by implementing `Display`.

use std::text::{String, is_empty};

pub enum FormatError { OutputLimit, InvalidIndent }

// The sink: the text so far, how deep the indentation is, how wide a step of
// it is, and whether the line being written has nothing on it yet.
pub struct Formatter { text: String, depth: Int, width: Int, fresh: Bool }

pub trait Display {
    fn fmt(&Self, &mut Formatter);
}

fn spaces(n: Int, out: Str) -> Str {
    if(n <= 0) { out } else { tail spaces(n - 1, " " ++ out) }
}

// A text with what would end or break a quoted text written out.
fn escaped(text: Str) -> Str {
    match(text) {
        StrEnd => "",
        StrChar(c, rest) =>
            let piece = match(int(c)) {
                34 => "\\\"",
                92 => "\\\\",
                10 => "\\n",
                _ => show(c)
            };
            piece ++ escaped(rest)
    }
}

impl Formatter {
    pub fn new() -> Self { Self { text: String::new(), depth: 0, width: 4, fresh: true } }
    // Indentation is written before the first thing on a line, not on a
    // line that stays empty.
    pub fn write_str(value: &mut Self, text: Str) {
        let starts = if(value.fresh) { not(is_empty(text)) } else { false };
        let before = if(starts) { spaces(value.depth * value.width, "") } else { "" };
        value.fresh = if(starts) { false } else { value.fresh };
        String::push_str(&mut value.text, before ++ text);
    }
    pub fn write_char(value: &mut Self, character: char) { Formatter::write_str(value, show(character)) }
    pub fn newline(value: &mut Self) {
        String::push_str(&mut value.text, "\n");
        value.fresh = true;
    }
    pub fn indent(value: &mut Self) -> Result<(), FormatError> {
        value.depth = value.depth + 1;
        Ok(())
    }
    pub fn dedent(value: &mut Self) -> Result<(), FormatError> {
        let depth = value.depth;
        value.depth = if(depth > 0) { depth - 1 } else { 0 };
        if(depth > 0) { Ok(()) } else { Err(InvalidIndent) }
    }
    pub fn quoted(value: &mut Self, text: Str) { Formatter::write_str(value, "\"" ++ escaped(text) ++ "\"") }
    pub fn display<T: Display>(value: &mut Self, item: &T) { fmt(item, value) }
    pub fn finish(value: Self) -> Result<String, FormatError> {
        match(value) { Formatter { text, depth, width, fresh } => Ok(text) }
    }
}

// What a value is written as.
pub fn format<T: Display>(value: &T) -> String {
    let mut out = Formatter::new();
    fmt(value, &mut out);
    match(out) { Formatter { text, depth, width, fresh } => text }
}

impl Display for Int { fn fmt(n, out) { Formatter::write_str(out, show(*n)) } }
impl Display for Str { fn fmt(text, out) { Formatter::write_str(out, *text) } }
impl Display for char { fn fmt(c, out) { Formatter::write_char(out, *c) } }
impl Display for String { fn fmt(text, out) { Formatter::write_str(out, String::to_str(text)) } }
"#

private def cText : String := r#"// What C has: its memory, and texts as it writes them. Everything here is
// unsafe: an address is whatever a program says it is.

// C's names for its types, as they are on x86-64 Linux.
pub type c_char = i8;
pub type c_schar = i8;
pub type c_uchar = u8;
pub type c_short = i16;
pub type c_ushort = u16;
pub type c_int = i32;
pub type c_uint = u32;
pub type c_long = i64;
pub type c_ulong = u64;
pub type c_longlong = i64;
pub type c_ulonglong = u64;
pub type c_size_t = usize;
pub type c_ssize_t = isize;
pub type c_float = f32;
pub type c_double = f64;

pub extern "C" {
    fn malloc(n: usize) -> usize;
    fn free(p: usize);
    fn strlen(s: usize) -> usize;
}

// One byte at an address, read and written.
pub unsafe fn read_byte(at: usize) -> u8 { u8(ptr_read(at, -8)) }
pub unsafe fn write_byte(at: usize, b: u8) { ptr_write(at, 8, int(b)) }

// The bytes of an array at an address, one after another.
pub unsafe fn write_bytes(at: usize, bytes: [u8]) { write_from(at, bytes, 0) }
unsafe fn write_from(at: usize, bytes: [u8], i: Int) {
    if(i < len(bytes)) { write_byte(at, bytes[i]); tail write_from(at + 1usize, bytes, i + 1) } else { () }
}

// So many bytes from an address.
pub unsafe fn read_bytes(at: usize, n: Int) -> [u8] { read_onto(at, n, []) }
unsafe fn read_onto(at: usize, n: Int, out: [u8]) -> [u8] {
    if(n <= 0) { out } else { tail read_onto(at + 1usize, n - 1, push(out, read_byte(at))) }
}

// A text as C has it: its bytes and a zero after them, in memory that is the
// caller's to `free`.
pub unsafe fn c_string(text: Str) -> usize {
    let bytes = std::text::utf8(text);
    let at = malloc(usize(len(bytes) + 1));
    write_bytes(at, push(bytes, 0u8));
    at
}

// The text C has at an address: the bytes up to a zero, if they are UTF-8.
pub unsafe fn text_at(at: usize) -> Option<Str> { std::text::from_utf8(read_bytes(at, int(strlen(at)))) }
"#

private def hash : String := r#"// Hashing, and a map and a set that find a key in a step or two: an array of
// buckets, each the keys whose hash falls there, doubled when it fills.

// A whole number for a value: equal values have equal numbers.
pub trait Hash { fn hash(Self) -> Int }

// Mixing, kept within what `Int` holds: a multiply and a fold of the high
// bits into the low ones.
fn mix(h: Int) -> Int {
    let m = int_and(wide_mul(int_and(h, 4294967295), 2654435761), 9223372036854775807);
    int_xor(m, int_shr(m, 29))
}
pub fn combine(a: Int, b: Int) -> Int { mix(int_xor(mix(a), int_add(int_and(b, 4611686018427387903), 1))) }

impl Hash for Int { fn hash(n) { mix(int_and(n, 9223372036854775807)) } }
impl Hash for char { fn hash(c) { mix(int(c)) } }
impl Hash for () { fn hash(u) { 7 } }
impl Hash for Str {
    fn hash(text) { hash_text(text, 5381) }
}
fn hash_text(text: Str, h: Int) -> Int {
    match(text) { StrEnd => h, StrChar(c, rest) => tail hash_text(rest, combine(h, int(c))) }
}
impl<A, B> Hash for (A, B) where A: Hash, B: Hash {
    fn hash(p) { match(p) { (a, b) => combine(hash(a), hash(b)) } }
}
impl<T> Hash for Array<T> where T: Hash {
    fn hash(a) { fold(a, 17, fn(h, x) { combine(h, hash(x)) }) }
}

// A map: its buckets, and how many keys it has.
pub struct HashMap<K, V>([[(K, V)]], Int)

pub fn new() { HashMap([[]; 8], 0) }

pub fn len(m) { match(m) { HashMap(_, n) => n } }
pub fn is_empty(m) { len(m) == 0 }

fn bucket_of(key, buckets) -> Int { int_rem(hash(key), std::vec::len_of(buckets)) }

// What `key` stands for.
pub fn get(m, key) {
    match(m) {
        HashMap(buckets, _) => in_bucket(buckets[bucket_of(key, buckets)], key, 0)
    }
}
fn in_bucket(bucket, key, i: Int) {
    if(i < std::vec::len_of(bucket)) {
        match(bucket[i]) { (k, v) => if(k == key) { Some(v) } else { tail in_bucket(bucket, key, i + 1) } }
    } else { None }
}

pub fn contains_key(m, key) { match(get(m, key)) { Some(_) => true, None => false } }

// Where `key` is in a bucket.
fn place_in(bucket, key, i: Int) -> Option<Int> {
    if(i < std::vec::len_of(bucket)) {
        match(bucket[i]) { (k, _) => if(k == key) { Some(i) } else { tail place_in(bucket, key, i + 1) } }
    } else { None }
}

// The map with `key` standing for `value`, whatever it stood for.
pub fn insert(m, key, value) {
    match(m) {
        HashMap(buckets, n) =>
            let at = bucket_of(key, buckets);
            let bucket = buckets[at];
            match(place_in(bucket, key, 0)) {
                Some(i) => HashMap(index_set(buckets, at, index_set(bucket, i, (key, value))), n),
                None => grown(HashMap(index_set(buckets, at, push(bucket, (key, value))), n + 1))
            }
    }
}

// With twice the buckets, once there are more keys than buckets.
fn grown(m) {
    match(m) {
        HashMap(buckets, n) =>
            if(n <= std::vec::len_of(buckets)) { m } else {
                fold(buckets, HashMap([[]; std::vec::len_of(buckets) * 2], 0), fn(out, bucket) {
                    fold(bucket, out, fn(acc, pair) { match(pair) { (k, v) => put_new(acc, k, v) } })
                })
            }
    }
}
// A key the map is known not to have.
fn put_new(m, key, value) {
    match(m) {
        HashMap(buckets, n) =>
            let at = bucket_of(key, buckets);
            HashMap(index_set(buckets, at, push(buckets[at], (key, value))), n + 1)
    }
}

// The map without `key`.
pub fn remove(m, key) {
    match(m) {
        HashMap(buckets, n) =>
            let at = bucket_of(key, buckets);
            let bucket = buckets[at];
            match(place_in(bucket, key, 0)) {
                // The last of the bucket takes the place, and the bucket is one shorter.
                Some(i) =>
                    let last = std::vec::len_of(bucket) - 1;
                    let moved = index_set(bucket, i, bucket[last]);
                    HashMap(index_set(buckets, at, std::vec::take(moved, last)), n - 1),
                None => m
            }
    }
}

// `f(f(init, k0, v0), k1, v1)` and so on, in no order one can rely on.
pub fn fold_map(m, init, f) {
    match(m) {
        HashMap(buckets, _) => fold(buckets, init, fn(acc, bucket) {
            fold(bucket, acc, fn(a, pair) { match(pair) { (k, v) => f(a, k, v) } })
        })
    }
}
pub fn keys(m) { fold_map(m, [], fn(out, k, v) { push(out, k) }) }
pub fn values(m) { fold_map(m, [], fn(out, k, v) { push(out, v) }) }
pub fn entries(m) { fold_map(m, [], fn(out, k, v) { push(out, (k, v)) }) }
pub fn from(pairs) { fold(pairs, new(), fn(m, pair) { match(pair) { (k, v) => insert(m, k, v) } }) }

// The same map changed where it is and looked into by reference, in the
// shape the library specification gives its maps (17).
fn slot_of<'a, K, V>(bucket: &'a [(K, V)], key: K, i: Int) -> Option<&'a V> where K: Eq {
    match(element(bucket, i)) {
        Some(pair) => if(pair.0 == key) { Some(&pair.1) } else { tail slot_of(bucket, key, i + 1) },
        None => None
    }
}

// Where in a bucket a key is, or a place that is not there.
fn place_of<K, V>(bucket: &[(K, V)], key: K, i: Int) -> Int where K: Eq {
    match(element(bucket, i)) {
        Some(pair) => if(pair.0 == key) { i } else { tail place_of(bucket, key, i + 1) },
        None => 0 - 1
    }
}

impl<K, V> HashMap<K, V> {
    // How many keys.
    pub fn count(value: &Self) -> Int { value.1 }
    // What a key stands for, where it is.
    pub fn get_ref<'a>(value: &'a Self, key: K) -> Option<&'a V> where K: Hash, K: Eq {
        let buckets = &value.0;
        match(element(buckets, int_rem(hash(key), len_at(buckets)))) {
            Some(bucket) => slot_of(bucket, key, 0),
            None => None
        }
    }
    pub fn has(value: &Self, key: K) -> Bool where K: Hash, K: Eq {
        match(HashMap::get_ref(value, key)) { Some(_) => true, None => false }
    }
    // What a key stands for, to change where it is.
    pub fn get_mut<'a>(value: &'a mut Self, key: K) -> Option<&'a mut V> where K: Hash, K: Eq {
        let buckets = &mut value.0;
        let n = len_at(&*buckets);
        match(element_mut(buckets, int_rem(hash(key), n))) {
            Some(bucket) =>
                let i = place_of(&*bucket, key, 0);
                match(element_mut(bucket, i)) {
                    Some(pair) => Some(&mut pair.1),
                    None => None
                },
            None => None
        }
    }
    // The key standing for the item from now on.
    pub fn set(value: &mut Self, key: K, item: V) where K: Hash, K: Eq {
        *value = insert(replace(value, new()), key, item);
    }
    // The key standing for nothing from now on.
    pub fn unset(value: &mut Self, key: K) where K: Hash, K: Eq {
        *value = remove(replace(value, new()), key);
    }
}
"#

/-- The texts of the library, each with the module it is. -/
def texts : List (List String × String) :=
  [(["std"], root),
   (["std", "option"], optionText),
   (["std", "result"], resultText),
   (["std", "cmp"], cmpText),
   (["std", "int"], intText),
   (["std", "char"], charText),
   (["std", "vec"], vecText),
   (["std", "text"], textText),
   (["std", "map"], mapText),
   (["std", "set"], setText),
   (["std", "iter"], iterText),
   (["std", "c"], cText),
   (["std", "fmt"], fmtText),
   (["std", "iterator"], iteratorText),
   (["std", "slice"], sliceText),
   (["std", "collections"], collectionsText),
   (["std", "host"], hostText),
   (["std", "hash"], hash),
   -- The names the library specification gives its modules (1.2): the same
   -- declarations, under `core`, `alloc` and more of `std`.
   (["std", "io"], "pub use std::host::{Console, IoError, print, println, eprintln, read_line};\n"),
   (["std", "fs"], "pub use std::host::{FileRead, FileWrite, IoError, read_text, write_text};\n"),
   (["std", "env"], "pub use std::host::{ProcessEnvironment, ProcessArgs};\n"),
   (["std", "time"], "pub use std::host::Clock;\n"),
   (["std", "random"], "pub use std::host::Entropy;\n"),
   (["std", "ffi"], "pub use std::c::*;\n"),
   (["core"], "pub mod option;\npub mod result;\npub mod cmp;\npub mod num;\npub mod char;\npub mod iter;\npub mod slice;\npub mod hash;\n"),
   (["core", "option"], "pub use std::option::*;\n"),
   (["core", "result"], "pub use std::result::*;\n"),
   (["core", "cmp"], "pub use std::cmp::*;\n"),
   (["core", "num"], "pub use std::int::*;\n"),
   (["core", "char"], "pub use std::char::*;\n"),
   (["core", "iter"], "pub use std::iterator::*;\n"),
   (["core", "slice"], "pub use std::slice::*;\n"),
   (["core", "hash"], "pub use std::hash::*;\n"),
   (["alloc"], "pub mod vec;\npub mod string;\npub mod collections;\npub mod fmt;\n"),
   (["alloc", "fmt"], "pub use std::fmt::*;\n"),
   (["alloc", "vec"], "pub use std::vec::*;\n"),
   (["alloc", "string"], "pub use std::text::*;\n"),
   (["alloc", "collections"], "pub use std::collections::*;\npub mod map;\npub mod set;\n"),
   (["alloc", "collections", "map"], "pub use std::map::*;\n"),
   (["alloc", "collections", "set"], "pub use std::set::*;\n")]

end Glorious.Std
