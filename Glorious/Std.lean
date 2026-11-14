module

/-!
# The standard library

What a program has beyond the prelude, written in the language: the module
`std` and the modules in it. A program that names `std` has it as a module of
its own, as though the texts here were files beside it.
-/

public section

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
pub mod stream;
pub mod value;
pub mod generator;
pub mod bytes;
pub mod error;
pub mod index;
pub mod budget;
pub mod parse;
pub mod graph;
pub mod source;
pub mod boxed;
pub mod task;
pub mod path;
pub mod future;
pub mod iterator;
pub mod slice;
pub mod collections;
pub mod host;
pub mod hash;
pub mod fingerprint;
pub mod diagnostic;
pub mod io;
pub mod fs;
pub mod env;
pub mod time;
pub mod random;
pub mod tuple;
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
        push_at(&mut value.items, item);
    }
    pub fn pop(value: &mut Self) -> Option<T> {
        pop_at(&mut value.items)
    }
    // The item put at a place, what was there and after it moving up; the
    // item given back if there is no such place.
    pub fn insert(value: &mut Self, index: Int, item: T) -> Result<(), T> {
        let items = &mut value.items;
        let n = len_at(&*items);
        if(index < 0) { Err(item) } else {
            if(index > n) { Err(item) } else {
                match(taken_off(replace(items, []), n - index, [])) {
                    (before, off) => unsafe { restore_at(items, put_back(push(before, item), off)) }; Ok(())
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
                        Some((before, taken)) => unsafe { restore_at(items, put_back(before, off)) }; Some(taken),
                        None => None
                    }
                }
            }
        }
    }
    // Everything of another put after what is here.
    pub fn append(value: &mut Self, source: Self) {
        let items = &mut value.items;
        match(source) { Vec { items: more } => let all = put_back(replace(items, []), turned(more, [])); unsafe { restore_at(items, all) } }
    }
    pub fn reverse(value: &mut Self) {
        let items = &mut value.items;
        let all = turned(replace(items, []), []);
        unsafe { restore_at(items, all) };
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
        push_at(&mut value.back, item);
    }
    pub fn push_front(value: &mut Self, item: T) {
        push_at(&mut value.front, item);
    }
    pub fn pop_front(value: &mut Self) -> Option<T> {
        // With nothing kept at the front, what is at the back is turned
        // round to be it.
        let front = &mut value.front;
        let back = &mut value.back;
        let ready = if(len_at(&*front) == 0) { turned(replace(back, []), []) } else { replace(front, []) };
        match(pop(ready)) {
            Some((rest, first)) => unsafe { restore_at(front, rest) }; Some(first),
            None => None
        }
    }
    pub fn pop_back(value: &mut Self) -> Option<T> {
        let front = &mut value.front;
        let back = &mut value.back;
        let ready = if(len_at(&*back) == 0) { turned(replace(front, []), []) } else { replace(back, []) };
        match(pop(ready)) {
            Some((rest, last)) => unsafe { restore_at(back, rest) }; Some(last),
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
        pop_at(&mut it.rest)
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

private def streamText : String := r#"// Streams of bytes, in the shape the library specification gives them (28): a
// trait for what can be read from and one for what can be written to. Each
// leaves to its implementation the row of effects its functions perform, so
// a stream held in memory performs nothing and one of the host's performs
// the host's effect, under the same functions.

use std::host::{IoError, Console, write_stdout, write_stderr, read_stdin};
use std::text::{utf8};

pub trait Read {
    type Effects: EffectRow;
    // Up to so many bytes. None, asked for some, is the end of the stream.
    fn read(&mut Self, Int) -> Result<[u8], IoError> / { | Self::Effects };
}

pub trait Write {
    type Effects: EffectRow;
    // How many of the bytes were taken, from the first of them.
    fn write(&mut Self, [u8]) -> Result<Int, IoError> / { | Self::Effects };
    fn flush(&mut Self) -> Result<(), IoError> / { | Self::Effects };
}

// The bytes of an array from one place up to another.
fn piece(bytes: &[u8], from: Int, upto: Int, out: [u8]) -> [u8] {
    if(from >= upto) { out } else {
        match(element(bytes, from)) {
            Some(b) => tail piece(bytes, from + 1, upto, push(out, *b)),
            None => out
        }
    }
}

// One array's bytes after another's.
fn joined(onto: [u8], more: &[u8], i: Int) -> [u8] {
    match(element(more, i)) {
        Some(b) => tail joined(push(onto, *b), more, i + 1),
        None => onto
    }
}

// Bytes held in memory: read from where the last read stopped, written at
// the end.
pub struct MemoryCursor { bytes: [u8], at: Int }

impl MemoryCursor {
    pub fn new(bytes: [u8]) -> Self { Self { bytes: bytes, at: 0 } }
    pub fn position(value: &Self) -> Int { value.at }
    pub fn into_inner(value: Self) -> [u8] { match(value) { MemoryCursor { bytes, at } => bytes } }
}

impl Read for MemoryCursor {
    type Effects = {};
    fn read(cursor, most) {
        let from = cursor.at;
        let n = len_at(&cursor.bytes);
        let upto = if(from + most > n) { n } else { from + most };
        cursor.at = upto;
        Ok(piece(&cursor.bytes, from, upto, []))
    }
}

impl Write for MemoryCursor {
    type Effects = {};
    fn write(cursor, bytes) {
        let held = &mut cursor.bytes;
        *held = joined(replace(held, []), &bytes, 0);
        Ok(len(bytes))
    }
    fn flush(cursor) { Ok(()) }
}

// The host's standard streams.
pub struct Stdout
pub struct Stderr
pub struct Stdin

impl Write for Stdout {
    type Effects = {Console};
    fn write(out, bytes) { write_stdout(bytes) }
    fn flush(out) { Ok(()) }
}

impl Write for Stderr {
    type Effects = {Console};
    fn write(out, bytes) { write_stderr(bytes) }
    fn flush(out) { Ok(()) }
}

impl Read for Stdin {
    type Effects = {Console};
    fn read(from, most) { read_stdin(most) }
}

// How far `write_all` got before it failed.
pub struct WriteAllError { pub written: Int, pub error: IoError }

fn write_from<W: Write>(writer: &mut W, bytes: [u8], done: Int)
    -> Result<(), WriteAllError> / { | <W as Write>::Effects } {
    let n = len(bytes);
    if(done >= n) { Ok(()) } else {
        match(write(writer, piece(&bytes, done, n, []))) {
            // A writer that takes nothing has failed: going round again
            // would never end.
            Ok(took) =>
                if(took <= 0) { Err(WriteAllError { written: done, error: IoError { code: 0 } }) }
                else { tail write_from(writer, bytes, done + took) },
            Err(e) => Err(WriteAllError { written: done, error: e })
        }
    }
}

// Every byte written, or how many were when it failed.
pub fn write_all<W: Write>(writer: &mut W, bytes: [u8])
    -> Result<(), WriteAllError> / { | <W as Write>::Effects } {
    write_from(writer, bytes, 0)
}

// A text written as its UTF-8 bytes.
pub fn write_str<W: Write>(writer: &mut W, text: Str)
    -> Result<(), WriteAllError> / { | <W as Write>::Effects } {
    write_from(writer, utf8(text), 0)
}

fn read_more<R: Read>(reader: &mut R, out: [u8], limit: Int)
    -> Result<[u8], IoError> / { | <R as Read>::Effects } {
    let left = limit - len(out);
    if(left <= 0) { Ok(out) } else {
        match(read(reader, if(left > 4096) { 4096 } else { left })) {
            Ok(got) =>
                if(len(got) == 0) { Ok(out) }
                else { tail read_more(reader, joined(out, &got, 0), limit) },
            Err(e) => Err(e)
        }
    }
}

// Everything a stream still has, up to so many bytes.
pub fn read_to_end<R: Read>(reader: &mut R, limit: Int)
    -> Result<[u8], IoError> / { | <R as Read>::Effects } {
    read_more(reader, [], limit)
}

// Where copying stopped: more may have been read than was written.
pub struct CopyError { pub read: Int, pub written: Int, pub error: IoError }

fn copy_more<R: Read, W: Write>(reader: &mut R, writer: &mut W, limit: Int, done: Int)
    -> Result<Int, CopyError> / { | <R as Read>::Effects, <W as Write>::Effects } {
    let left = limit - done;
    if(left <= 0) { Ok(done) } else {
        match(read(reader, if(left > 4096) { 4096 } else { left })) {
            Ok(got) =>
                let n = len(got);
                if(n == 0) { Ok(done) } else {
                    match(write_from(writer, got, 0)) {
                        Ok(_) => tail copy_more(reader, writer, limit, done + n),
                        Err(e) => Err(CopyError { read: done + n, written: done + e.written, error: e.error })
                    }
                },
            Err(e) => Err(CopyError { read: done, written: done, error: e })
        }
    }
}

// One stream into another until the first ends, up to so many bytes: how
// many went across. It performs what reading the one and writing the other
// do.
pub fn copy_stream<R: Read, W: Write>(reader: &mut R, writer: &mut W, limit: Int)
    -> Result<Int, CopyError> / { | <R as Read>::Effects, <W as Write>::Effects } {
    copy_more(reader, writer, limit, 0)
}

// What was left when a buffered writer could not finish: the writer, the
// bytes not written, and why.
pub struct FinishWriteFailure<W> { pub writer: W, pub pending: [u8], pub error: IoError }

// Bytes kept until there are enough to be worth writing. Letting one go
// writes nothing: `finish` asks for what is kept to be written, and
// `into_parts` gives it back.
pub struct BufferWriter<W> { inner: W, held: [u8], capacity: Int }

impl<W> BufferWriter<W> {
    pub fn new(writer: W, capacity: Int) -> Self {
        Self { inner: writer, held: [], capacity: if(capacity < 1) { 1 } else { capacity } }
    }
    pub fn get_ref<'a>(value: &'a Self) -> &'a W { &value.inner }
    // How many bytes are kept.
    pub fn buffered(value: &Self) -> Int { len_at(&value.held) }
    pub fn pending(value: &Self) -> [u8] { value.held }
    pub fn into_parts(value: Self) -> (W, [u8]) { match(value) { BufferWriter { inner, held, capacity: _ } => (inner, held) } }
    // What is kept written, and the writer given back; or all three of what
    // there was, where it could not be.
    pub fn finish(value: Self) -> Result<W, FinishWriteFailure<W>> / { | <W as Write>::Effects } where W: Write {
        match(value) {
            BufferWriter { inner, held, capacity: _ } =>
                let mut writer = inner;
                match(write_from(&mut writer, held, 0)) {
                    Ok(_) => match(flush(&mut writer)) {
                        Ok(_) => Ok(writer),
                        Err(e) => Err(FinishWriteFailure { writer: writer, pending: [], error: e })
                    },
                    Err(e) => Err(FinishWriteFailure { writer: writer, pending: piece(&held, e.written, len(held), []), error: e.error })
                }
        }
    }
}

impl<W> Write for BufferWriter<W> where W: Write {
    type Effects = { | <W as Write>::Effects };
    fn write(b, bytes) {
        b.held = joined(b.held, &bytes, 0);
        if(len_at(&b.held) >= b.capacity) {
            match(write_from(&mut b.inner, b.held, 0)) {
                Ok(_) => b.held = []; Ok(len(bytes)),
                // (What the writer took is no longer kept.)
                Err(e) => b.held = piece(&b.held, e.written, len_at(&b.held), []); Err(e.error)
            }
        } else { Ok(len(bytes)) }
    }
    fn flush(b) {
        match(write_from(&mut b.inner, b.held, 0)) {
            Ok(_) => b.held = []; flush(&mut b.inner),
            Err(e) => b.held = piece(&b.held, e.written, len_at(&b.held), []); Err(e.error)
        }
    }
}

// Bytes read ahead, so that a little is not asked of the reader each time.
pub struct BufferReader<R> { inner: R, held: [u8], at: Int, capacity: Int }

impl<R> BufferReader<R> {
    pub fn new(reader: R, capacity: Int) -> Self {
        Self { inner: reader, held: [], at: 0, capacity: if(capacity < 1) { 1 } else { capacity } }
    }
    pub fn get_ref<'a>(value: &'a Self) -> &'a R { &value.inner }
    // The reader, and the bytes read from it that nothing has asked for yet.
    pub fn into_parts(value: Self) -> (R, [u8]) {
        match(value) { BufferReader { inner, held, at, capacity: _ } => (inner, piece(&held, at, len(held), [])) }
    }
}

impl<R> Read for BufferReader<R> where R: Read {
    type Effects = { | <R as Read>::Effects };
    fn read(b, most) {
        if(b.at < len_at(&b.held)) {
            let from = b.at;
            let n = len_at(&b.held);
            let upto = if(from + most > n) { n } else { from + most };
            b.at = upto;
            Ok(piece(&b.held, from, upto, []))
        } else {
            // Nothing kept: more is read, as much as is kept at a time or
            // as much as is asked for, whichever is more.
            match(read(&mut b.inner, if(most > b.capacity) { most } else { b.capacity })) {
                Err(e) => Err(e),
                Ok(got) =>
                    let n = len(got);
                    let upto = if(most > n) { n } else { most };
                    b.held = got;
                    b.at = upto;
                    Ok(piece(&b.held, 0, upto, []))
            }
        }
    }
}
"#

private def valueText : String := r#"// The small things the rest is built from, as the library specification
// lists them (3).

// One of two.
pub enum Either<A, B> { Left(A), Right(B) }

// What was refused, given back with why.
pub struct Rejected<T, E> { pub value: T, pub error: E }

pub fn identity<T>(value: T) -> T { value }

// A value let go: its `drop` runs, if it has one.
pub fn discard<T>(value: T) { () }

// A type with a value to start from.
pub trait Default {
    fn default() -> Self;
}

impl Default for Int { fn default() { 0 } }
impl Default for Str { fn default() { "" } }
// (`Bool` is an `Option<()>`: its start is `false`.)
impl<A> Default for Option<A> { fn default() { None } }

// What a reference points to, taken; the type's start is left in its place.
pub fn take<T: Default>(target: &mut T) -> T { replace(target, default()) }
"#

private def errorText : String := r#"// Failures several modules share, as the library specification lists them
// (32).

// A mark used on what it was not taken from, or after that was cut back.
pub enum MarkError { WrongOwner, Stale, OutOfRange, NotTop }
// A stretch that is not within what it is a stretch of.
pub struct RangeError { pub offset: Int, pub length: Int }
// Room that could not be made.
pub enum ReserveError { CapacityOverflow }
// More things than a place can number.
pub struct IndexOverflow;
"#

private def bytesText : String := r#"// Bytes read and written a number at a time, as the library specification
// has them (23). Places and lengths are `Int`.

use std::slice::{Slice};
use std::text::{from_utf8};

pub enum DecodeErrorKind { Truncated, Overflow, NonCanonical, InvalidTag, InvalidUtf8, LimitExceeded }
pub struct DecodeError { pub offset: Int, pub kind: DecodeErrorKind }
pub use std::error::{MarkError, RangeError, ReserveError};
pub enum ByteWriteError { Range(RangeError), Reserve(ReserveError), InvalidAlignment }

// A place in some bytes, read from front to back. A read that fails leaves
// the place where it was.
pub struct ByteReader<'a> { bytes: Slice<'a, u8>, at: Int }

// Where a reader was, to go back to.
pub struct ReaderMark { at: Int, length: Int }

fn fails<T>(at: Int, kind: DecodeErrorKind) -> Result<T, DecodeError> { Err(DecodeError { offset: at, kind: kind }) }

fn byte_at<'a>(bytes: &Slice<'a, u8>, i: Int) -> Int {
    match(Slice::get(bytes, i)) { Some(b) => int(*b), None => 0 }
}

fn wide(n: Int) -> u128 { to(n) }

// The number so many bytes from a place are, the first the least.
fn le_from<'a>(bytes: &Slice<'a, u8>, at: Int, width: Int) -> u128 {
    if(width <= 0) { 0u128 } else { wide(byte_at(bytes, at)) + 256u128 * le_from(bytes, at + 1, width - 1) }
}

// And the first the greatest.
fn be_from<'a>(bytes: &Slice<'a, u8>, at: Int, width: Int, so_far: u128) -> u128 {
    if(width <= 0) { so_far } else { tail be_from(bytes, at + 1, width - 1, so_far * 256u128 + wide(byte_at(bytes, at))) }
}

impl<'a> ByteReader<'a> {
    pub fn new(bytes: Slice<'a, u8>) -> Self { Self { bytes: bytes, at: 0 } }
    pub fn position(r: &Self) -> Int { r.at }
    pub fn remaining_len(r: &Self) -> Int { Slice::len(&r.bytes) - r.at }
    pub fn remaining(r: &Self) -> Slice<'a, u8> {
        match(Slice::sub(&r.bytes, r.at, Slice::len(&r.bytes))) { Some(rest) => rest, None => r.bytes }
    }
    pub fn mark(r: &Self) -> ReaderMark { ReaderMark { at: r.at, length: Slice::len(&r.bytes) } }
    pub fn restore(r: &mut Self, mark: ReaderMark) -> Result<(), MarkError> {
        if(mark.length != Slice::len(&r.bytes)) { Err(MarkError::WrongOwner) } else {
            if(mark.at > mark.length) { Err(MarkError::OutOfRange) } else { r.at = mark.at; Ok(()) }
        }
    }
    // So many bytes on, if there are that many.
    fn step(r: &mut Self, width: Int) -> Result<Int, DecodeError> {
        let at = r.at;
        if(width < 0) { fails(at, DecodeErrorKind::Overflow) } else {
            if(at + width > Slice::len(&r.bytes)) { fails(at, DecodeErrorKind::Truncated) } else { r.at = at + width; Ok(at) }
        }
    }
    pub fn read_u8(r: &mut Self) -> Result<u8, DecodeError> {
        match(ByteReader::step(r, 1)) { Ok(at) => Ok(u8(byte_at(&r.bytes, at))), Err(e) => Err(e) }
    }
    pub fn read_u16_le(r: &mut Self) -> Result<u16, DecodeError> {
        match(ByteReader::step(r, 2)) { Ok(at) => Ok(to(le_from(&r.bytes, at, 2))), Err(e) => Err(e) }
    }
    pub fn read_u32_le(r: &mut Self) -> Result<u32, DecodeError> {
        match(ByteReader::step(r, 4)) { Ok(at) => Ok(to(le_from(&r.bytes, at, 4))), Err(e) => Err(e) }
    }
    pub fn read_u64_le(r: &mut Self) -> Result<u64, DecodeError> {
        match(ByteReader::step(r, 8)) { Ok(at) => Ok(to(le_from(&r.bytes, at, 8))), Err(e) => Err(e) }
    }
    pub fn read_u128_le(r: &mut Self) -> Result<u128, DecodeError> {
        match(ByteReader::step(r, 16)) { Ok(at) => Ok(to(le_from(&r.bytes, at, 16))), Err(e) => Err(e) }
    }
    pub fn read_u16_be(r: &mut Self) -> Result<u16, DecodeError> {
        match(ByteReader::step(r, 2)) { Ok(at) => Ok(to(be_from(&r.bytes, at, 2, 0u128))), Err(e) => Err(e) }
    }
    pub fn read_u32_be(r: &mut Self) -> Result<u32, DecodeError> {
        match(ByteReader::step(r, 4)) { Ok(at) => Ok(to(be_from(&r.bytes, at, 4, 0u128))), Err(e) => Err(e) }
    }
    pub fn read_u64_be(r: &mut Self) -> Result<u64, DecodeError> {
        match(ByteReader::step(r, 8)) { Ok(at) => Ok(to(be_from(&r.bytes, at, 8, 0u128))), Err(e) => Err(e) }
    }
    pub fn read_i64_le(r: &mut Self) -> Result<i64, DecodeError> {
        match(ByteReader::step(r, 8)) {
            Ok(at) => // (Two's complement: the upper half of what eight bytes can
                // say is the numbers below nothing.)
                let n: i128 = to(le_from(&r.bytes, at, 8));
                Ok(to(if(n >= 9223372036854775808i128) { n - 18446744073709551616i128 } else { n })),
            Err(e) => Err(e)
        }
    }
    // A number written seven bits to a byte, the least first, each byte but
    // the last with its top bit set: the one shortest way of writing it, in
    // ten bytes at most.
    pub fn read_var_u64(r: &mut Self) -> Result<u64, DecodeError> {
        let start = r.at;
        match(var_from(&r.bytes, start, 0u128, 1u128, 0)) {
            Ok((value, width)) => r.at = start + width; Ok(to(value)),
            Err(kind) => fails(start, kind)
        }
    }
    pub fn read_exact(r: &mut Self, length: Int) -> Result<Slice<'a, u8>, DecodeError> {
        match(ByteReader::step(r, length)) {
            Ok(at) => match(Slice::sub(&r.bytes, at, at + length)) { Some(found) => Ok(found), None => fails(at, DecodeErrorKind::Truncated) },
            Err(e) => Err(e)
        }
    }
    // So many bytes as the text they are in UTF-8.
    pub fn read_str(r: &mut Self, length: Int) -> Result<Str, DecodeError> {
        let start = r.at;
        match(ByteReader::step(r, length)) {
            Ok(at) => match(from_utf8(copied(&r.bytes, at, at + length, []))) {
                Some(text) => Ok(text),
                None => r.at = start; fails(start, DecodeErrorKind::InvalidUtf8)
            },
            Err(e) => Err(e)
        }
    }
    pub fn skip(r: &mut Self, length: Int) -> Result<(), DecodeError> {
        match(ByteReader::step(r, length)) { Ok(_) => Ok(()), Err(e) => Err(e) }
    }
    // A reader of the next so many bytes alone; this one goes on after them.
    pub fn subreader(r: &mut Self, length: Int) -> Result<ByteReader<'a>, DecodeError> {
        match(ByteReader::read_exact(r, length)) { Ok(part) => Ok(ByteReader { bytes: part, at: 0 }), Err(e) => Err(e) }
    }
    // Done, with nothing left unread.
    pub fn finish(r: Self) -> Result<(), DecodeError> {
        if(ByteReader::remaining_len(&r) == 0) { Ok(()) } else { fails(ByteReader::position(&r), DecodeErrorKind::LimitExceeded) }
    }
}

fn copied<'a>(bytes: &Slice<'a, u8>, at: Int, end: Int, out: [u8]) -> [u8] {
    if(at >= end) { out } else { tail copied(bytes, at + 1, end, push(out, u8(byte_at(bytes, at)))) }
}

fn var_from<'a>(bytes: &Slice<'a, u8>, at: Int, value: u128, scale: u128, width: Int) -> Result<(u128, Int), DecodeErrorKind> {
    if(at >= Slice::len(bytes)) { Err(DecodeErrorKind::Truncated) } else {
        if(width >= 10) { Err(DecodeErrorKind::Overflow) } else {
            let b = byte_at(bytes, at);
            let next = value + wide(b % 128) * scale;
            if(b >= 128) { tail var_from(bytes, at + 1, next, scale * 128u128, width + 1) } else {
                if(next >= 18446744073709551616u128) { Err(DecodeErrorKind::Overflow) } else {
                    // A last byte of nothing, after others, says the same
                    // number a byte shorter.
                    if(b == 0 and { width > 0 }) { Err(DecodeErrorKind::NonCanonical) } else { Ok((next, width + 1)) }
                }
            }
        }
    }
}

// Bytes built from front to back.
pub struct ByteBuf { bytes: [u8] }

// How long a buffer was, to cut it back to.
pub struct BufferMark { length: Int }

fn low(value: u128, modulus: u128) -> u8 { to(value % modulus) }

fn le_onto(out: [u8], value: u128, width: Int) -> [u8] {
    if(width <= 0) { out } else { tail le_onto(push(out, low(value, 256u128)), value / 256u128, width - 1) }
}

fn be_onto(out: [u8], value: u128, width: Int) -> [u8] {
    if(width <= 0) { out } else { push(be_onto(out, value / 256u128, width - 1), low(value, 256u128)) }
}

fn var_onto(out: [u8], value: u128) -> [u8] {
    if(value < 128u128) { push(out, low(value, 128u128)) }
    else { tail var_onto(push(out, u8(128 + int(low(value, 128u128)))), value / 128u128) }
}

fn zeros_onto(out: [u8], count: Int) -> [u8] {
    if(count <= 0) { out } else { tail zeros_onto(push(out, 0u8), count - 1) }
}

fn slice_onto<'a>(out: [u8], bytes: &Slice<'a, u8>, at: Int) -> [u8] {
    if(at >= Slice::len(bytes)) { out } else { tail slice_onto(push(out, u8(byte_at(bytes, at))), bytes, at + 1) }
}

// The bytes with those from a place on replaced by a number's, the least first.
fn patched(bytes: [u8], at: Int, value: u128, width: Int) -> [u8] {
    if(width <= 0) { bytes } else { tail patched(with_byte(bytes, at, low(value, 256u128)), at + 1, value / 256u128, width - 1) }
}

fn with_byte(bytes: [u8], at: Int, byte: u8) -> [u8] { let mut next = bytes; next[at] = byte; next }

// The bytes from one place up to another.
fn piece(bytes: &[u8], from: Int, upto: Int, out: [u8]) -> [u8] {
    if(from >= upto) { out } else {
        match(element(bytes, from)) {
            Some(b) => tail piece(bytes, from + 1, upto, push(out, *b)),
            None => out
        }
    }
}

fn is_power_of_two(n: Int) -> Bool { if(n <= 0) { false } else { if(n == 1) { true } else { if(n % 2 == 0) { is_power_of_two(n / 2) } else { false } } } }

impl ByteBuf {
    pub fn new() -> Self { Self { bytes: [] } }
    pub fn with_capacity(capacity: Int) -> Result<Self, ReserveError> {
        if(capacity < 0) { Err(ReserveError::CapacityOverflow) } else { Ok(Self { bytes: [] }) }
    }
    pub fn len(b: &Self) -> Int { len_at(&b.bytes) }
    pub fn as_slice<'a>(b: &'a Self) -> Slice<'a, u8> { Slice::of(&b.bytes) }
    pub fn reserve(b: &mut Self, additional: Int) -> Result<(), ReserveError> {
        if(additional < 0) { Err(ReserveError::CapacityOverflow) } else { Ok(()) }
    }
    pub fn push(b: &mut Self, byte: u8) -> Result<(), ReserveError> { b.bytes = push(b.bytes, byte); Ok(()) }
    pub fn extend<'a>(b: &mut Self, bytes: Slice<'a, u8>) -> Result<(), ReserveError> { b.bytes = slice_onto(b.bytes, &bytes, 0); Ok(()) }
    pub fn write_u16_le(b: &mut Self, input: u16) -> Result<(), ReserveError> { b.bytes = le_onto(b.bytes, to(input), 2); Ok(()) }
    pub fn write_u32_le(b: &mut Self, input: u32) -> Result<(), ReserveError> { b.bytes = le_onto(b.bytes, to(input), 4); Ok(()) }
    pub fn write_u64_le(b: &mut Self, input: u64) -> Result<(), ReserveError> { b.bytes = le_onto(b.bytes, to(input), 8); Ok(()) }
    pub fn write_u128_le(b: &mut Self, input: u128) -> Result<(), ReserveError> { b.bytes = le_onto(b.bytes, to(input), 16); Ok(()) }
    pub fn write_u16_be(b: &mut Self, input: u16) -> Result<(), ReserveError> { b.bytes = be_onto(b.bytes, to(input), 2); Ok(()) }
    pub fn write_u32_be(b: &mut Self, input: u32) -> Result<(), ReserveError> { b.bytes = be_onto(b.bytes, to(input), 4); Ok(()) }
    pub fn write_u64_be(b: &mut Self, input: u64) -> Result<(), ReserveError> { b.bytes = be_onto(b.bytes, to(input), 8); Ok(()) }
    pub fn write_var_u64(b: &mut Self, input: u64) -> Result<(), ReserveError> { b.bytes = var_onto(b.bytes, to(input)); Ok(()) }
    // A number written over bytes already there; all of them, or none.
    fn patch(b: &mut Self, offset: Int, value: u128, width: Int) -> Result<(), RangeError> {
        if(offset < 0 or { offset + width > len_at(&b.bytes) }) { Err(RangeError { offset: offset, length: width }) }
        else { b.bytes = patched(b.bytes, offset, value, width); Ok(()) }
    }
    pub fn patch_u16_le(b: &mut Self, offset: Int, input: u16) -> Result<(), RangeError> { ByteBuf::patch(b, offset, to(input), 2) }
    pub fn patch_u32_le(b: &mut Self, offset: Int, input: u32) -> Result<(), RangeError> { ByteBuf::patch(b, offset, to(input), 4) }
    pub fn patch_u64_le(b: &mut Self, offset: Int, input: u64) -> Result<(), RangeError> { ByteBuf::patch(b, offset, to(input), 8) }
    // Zeros up to the next multiple of a power of two.
    pub fn align_zeroed(b: &mut Self, alignment: Int) -> Result<(), ByteWriteError> {
        if(is_power_of_two(alignment)) {
            let over = len_at(&b.bytes) % alignment;
            b.bytes = zeros_onto(b.bytes, (alignment - over) % alignment);
            Ok(())
        } else { Err(ByteWriteError::InvalidAlignment) }
    }
    // Made so long: with zeros added, or cut short.
    pub fn resize_zeroed(b: &mut Self, length: Int) -> Result<(), ReserveError> {
        if(length < 0) { Err(ReserveError::CapacityOverflow) } else {
            let n = len_at(&b.bytes);
            b.bytes = if(length >= n) { zeros_onto(b.bytes, length - n) } else { piece(&b.bytes, 0, length, []) };
            Ok(())
        }
    }
    pub fn mark(b: &Self) -> BufferMark { BufferMark { length: len_at(&b.bytes) } }
    pub fn truncate_to(b: &mut Self, mark: BufferMark) -> Result<(), MarkError> {
        if(mark.length > len_at(&b.bytes)) { Err(MarkError::Stale) } else { b.bytes = piece(&b.bytes, 0, mark.length, []); Ok(()) }
    }
    pub fn finish(b: Self) -> [u8] { b.bytes }
}

pub enum HexErrorKind { InvalidDigit, OddLength, IncorrectLength }
pub struct HexError { pub offset: Int, pub kind: HexErrorKind }

fn hex_digit(n: Int) -> char { match(char(if(n < 10) { 48 + n } else { 87 + n })) { Some(c) => c, None => '0' } }

// (From the last byte back: a text is built from its end.)
fn hex_onto<'a>(bytes: &Slice<'a, u8>, at: Int, out: Str) -> Str {
    if(at <= 0) { out } else {
        let b = byte_at(bytes, at - 1);
        tail hex_onto(bytes, at - 1, StrChar(hex_digit(b / 16), StrChar(hex_digit(b % 16), out)))
    }
}

// Bytes as text, two digits each, the letters small.
pub fn hex_encode<'a>(bytes: Slice<'a, u8>) -> Str { hex_onto(&bytes, Slice::len(&bytes), "") }

fn hex_value(c: char) -> Option<Int> {
    let n = int(c);
    if(48 <= n and { n <= 57 }) { Some(n - 48) } else {
        if(97 <= n and { n <= 102 }) { Some(n - 87) } else {
            if(65 <= n and { n <= 70 }) { Some(n - 55) } else { None }
        }
    }
}

fn hex_from(text: Str, at: Int, out: [u8]) -> Result<[u8], HexError> {
    match(text) {
        StrEnd => Ok(out),
        StrChar(a, rest) => match(rest) {
            StrEnd => Err(HexError { offset: at, kind: HexErrorKind::OddLength }),
            StrChar(b, more) => match(hex_value(a)) {
                None => Err(HexError { offset: at, kind: HexErrorKind::InvalidDigit }),
                Some(high) => match(hex_value(b)) {
                    None => Err(HexError { offset: at + 1, kind: HexErrorKind::InvalidDigit }),
                    Some(low) => tail hex_from(more, at + 2, push(out, u8(high * 16 + low)))
                }
            }
        }
    }
}

// The bytes a text of hexadecimal digits says, or where it stops being one.
pub fn hex_decode(text: Str) -> Result<[u8], HexError> { hex_from(text, 0, []) }

// Bytes as text six bits to a character.
pub enum Base64Alphabet { Standard, UrlSafe }
pub enum Padding { Required, Optional, Forbidden }
pub struct Base64Options { pub alphabet: Base64Alphabet, pub padding: Padding }
pub enum Base64ErrorKind { InvalidDigit, InvalidPadding, NonCanonicalTail, IncorrectLength }
pub struct Base64Error { pub offset: Int, pub kind: Base64ErrorKind }

fn is_url(options: &Base64Options) -> Bool { match(options.alphabet) { Base64Alphabet::UrlSafe => true, Base64Alphabet::Standard => false } }

fn letter(n: Int) -> char { match(char(n)) { Some(c) => c, None => '?' } }

fn digit64(n: Int, url: Bool) -> char {
    if(n < 26) { letter(65 + n) } else {
        if(n < 52) { letter(71 + n) } else {
            if(n < 62) { letter(n - 4) } else {
                if(n == 62) { if(url) { '-' } else { '+' } } else { if(url) { '_' } else { '/' } }
            }
        }
    }
}

fn value64(c: char, url: Bool) -> Option<Int> {
    let n = int(c);
    if(65 <= n and { n <= 90 }) { Some(n - 65) } else {
        if(97 <= n and { n <= 122 }) { Some(n - 71) } else {
            if(48 <= n and { n <= 57 }) { Some(n + 4) } else {
                if(c == (if(url) { '-' } else { '+' })) { Some(62) } else {
                    if(c == (if(url) { '_' } else { '/' })) { Some(63) } else { None }
                }
            }
        }
    }
}

// The digits of the bytes from a place on, three bytes to four digits; the
// last one or two bytes to two or three.
fn digits64<'a>(bytes: &Slice<'a, u8>, at: Int, out: [Int]) -> [Int] {
    let left = Slice::len(bytes) - at;
    if(left <= 0) { out } else {
        let a = byte_at(bytes, at);
        if(left == 1) { push(push(out, a / 4), (a % 4) * 16) } else {
            let b = byte_at(bytes, at + 1);
            if(left == 2) { push(push(push(out, a / 4), (a % 4) * 16 + b / 16), (b % 16) * 4) } else {
                let c = byte_at(bytes, at + 2);
                tail digits64(bytes, at + 3, push(push(push(push(out, a / 4), (a % 4) * 16 + b / 16), (b % 16) * 4 + c / 64), c % 64))
            }
        }
    }
}

fn padded(n: Int, out: Str) -> Str { if(n % 4 == 0) { out } else { tail padded(n + 1, StrChar('=', out)) } }

fn text64(digits: &[Int], i: Int, url: Bool, out: Str) -> Str {
    if(i <= 0) { out } else {
        tail text64(digits, i - 1, url, StrChar(digit64(match(element(digits, i - 1)) { Some(d) => *d, None => 0 }, url), out))
    }
}

pub fn base64_encode<'a>(bytes: Slice<'a, u8>, options: Base64Options) -> Str {
    let digits = digits64(&bytes, 0, []);
    let n = len(digits);
    let end = match(options.padding) { Padding::Required => padded(n, ""), Padding::Optional => padded(n, ""), Padding::Forbidden => "" };
    text64(&digits, n, is_url(&options), end)
}

// The digits a text has before its padding, and how many `=` follow them:
// or the place of a character that is neither.
fn read64(text: Str, at: Int, url: Bool, digits: [Int], pads: Int) -> Result<([Int], Int), Base64Error> {
    match(text) {
        StrEnd => Ok((digits, pads)),
        StrChar(c, rest) =>
            if(c == '=') { tail read64(rest, at + 1, url, digits, pads + 1) } else {
                // A digit after padding is not where one can be.
                if(pads > 0) { Err(Base64Error { offset: at, kind: Base64ErrorKind::InvalidPadding }) } else {
                    match(value64(c, url)) {
                        Some(v) => tail read64(rest, at + 1, url, push(digits, v), 0),
                        None => Err(Base64Error { offset: at, kind: Base64ErrorKind::InvalidDigit })
                    }
                }
            }
    }
}

fn bytes64(digits: &[Int], at: Int, out: [u8]) -> Result<[u8], Base64Error> {
    let left = len_at(digits) - at;
    let d = fn(i: Int) -> Int { match(element(digits, at + i)) { Some(v) => *v, None => 0 } };
    if(left <= 0) { Ok(out) } else {
        if(left == 1) { Err(Base64Error { offset: at, kind: Base64ErrorKind::IncorrectLength }) } else {
            let first = u8(d(0) * 4 + d(1) / 16);
            if(left == 2) {
                // (Bits left over have to be nothing: the one way to write it.)
                if(d(1) % 16 != 0) { Err(Base64Error { offset: at + 1, kind: Base64ErrorKind::NonCanonicalTail }) } else { Ok(push(out, first)) }
            } else {
                let second = u8((d(1) % 16) * 16 + d(2) / 4);
                if(left == 3) {
                    if(d(2) % 4 != 0) { Err(Base64Error { offset: at + 2, kind: Base64ErrorKind::NonCanonicalTail }) } else { Ok(push(push(out, first), second)) }
                } else {
                    bytes64(digits, at + 4, push(push(push(out, first), second), u8((d(2) % 4) * 64 + d(3))))
                }
            }
        }
    }
}

// The bytes a text says, or where it stops being one: nothing is skipped,
// and padding is taken as the options say.
pub fn base64_decode(text: Str, options: Base64Options) -> Result<[u8], Base64Error> {
    match(read64(text, 0, is_url(&options), [], 0)) {
        Err(e) => Err(e),
        Ok((digits, pads)) =>
            let n = len(digits);
            let wanted = (4 - n % 4) % 4;
            let fits = match(options.padding) {
                Padding::Required => pads == wanted,
                Padding::Optional => pads == 0 or { pads == wanted },
                Padding::Forbidden => pads == 0
            };
            if(fits) { bytes64(&digits, 0, []) } else { Err(Base64Error { offset: n, kind: Base64ErrorKind::InvalidPadding }) }
    }
}
"#

private def indexText : String := r#"// Tables whose places cannot be mixed up with another table's, and the sets
// and queues of such places a compiler is built from, as the library
// specification has them (24). Places and lengths are `Int`.

use std::value::{Rejected};
use std::slice::{Slice};
use std::hash::{Hash, HashMap};
pub use std::error::{MarkError, IndexOverflow};

// A place among the things of one kind. `Tag` says which kind and is only a
// name: an `Id<Function>` is not an `Id<Block>`.
pub struct Id<Tag>(u32);

fn numbered<Tag>(n: Int) -> Id<Tag> { Id(to(n)) }

impl<Tag> Id<Tag> {
    pub fn from_u32(value: u32) -> Self { Id(value) }
    pub fn to_u32(id: Self) -> u32 { id.0 }
    pub fn from_usize(value: usize) -> Result<Self, IndexOverflow> { Id::at(int(value)) }
    pub fn to_usize(id: Self) -> usize { to(id.0) }
    // As a place counted in `Int`, which is what this library counts in.
    pub fn index(id: Self) -> Int { int(id.0) }
    pub fn at(index: Int) -> Result<Self, IndexOverflow> {
        if(index < 0 or { index > 4294967295 }) { Err(IndexOverflow) } else { Ok(numbered(index)) }
    }
}

// Things of one kind, each at the place it was given when it was added.
pub struct IndexVec<Tag, T> { items: [T] }

impl<Tag, T> IndexVec<Tag, T> {
    pub fn new() -> Self { Self { items: [] } }
    pub fn len(v: &Self) -> Int { len_at(&v.items) }
    pub fn push(v: &mut Self, item: T) -> Result<Id<Tag>, Rejected<T, IndexOverflow>> {
        let n = len_at(&v.items);
        if(n > 4294967295) { Err(Rejected { value: item, error: IndexOverflow }) } else {
            push_at(&mut v.items, item);
            Ok(numbered(n))
        }
    }
    pub fn get<'a>(v: &'a Self, id: Id<Tag>) -> Option<&'a T> { element(&v.items, int(id.0)) }
    pub fn get_mut<'a>(v: &'a mut Self, id: Id<Tag>) -> Option<&'a mut T> { element_mut(&mut v.items, int(id.0)) }
    pub fn as_slice<'a>(v: &'a Self) -> Slice<'a, T> { Slice::of(&v.items) }
    pub fn into_vec(v: Self) -> [T] { match(v) { IndexVec { items } => items } }
}

// The last so many of some things onto others: what is left, and what was
// taken with the last taken first.
fn taken_from<T>(items: [T], count: Int, taken: [T]) -> ([T], [T]) {
    if(count <= 0) { (items, taken) } else {
        match(pop(items)) {
            Some((rest, last)) => tail taken_from(rest, count - 1, push(taken, last)),
            None => ([], taken)
        }
    }
}

fn turned<T>(from: [T], onto: [T]) -> [T] {
    match(pop(from)) { Some((rest, last)) => tail turned(rest, push(onto, last)), None => onto }
}

// Things added and never moved, which can be cut back to how many there
// were at a mark.
pub struct Arena<Tag, T> { items: [T] }

// How many things an arena had.
pub struct ArenaMark<Tag> { length: Int }

impl<Tag, T> Arena<Tag, T> {
    pub fn new() -> Self { Self { items: [] } }
    pub fn len(a: &Self) -> Int { len_at(&a.items) }
    pub fn insert(a: &mut Self, item: T) -> Result<Id<Tag>, Rejected<T, IndexOverflow>> {
        let n = len_at(&a.items);
        if(n > 4294967295) { Err(Rejected { value: item, error: IndexOverflow }) } else {
            push_at(&mut a.items, item);
            Ok(numbered(n))
        }
    }
    pub fn get<'a>(a: &'a Self, id: Id<Tag>) -> Option<&'a T> { element(&a.items, int(id.0)) }
    pub fn get_mut<'a>(a: &'a mut Self, id: Id<Tag>) -> Option<&'a mut T> { element_mut(&mut a.items, int(id.0)) }
    pub fn mark(a: &Self) -> ArenaMark<Tag> { ArenaMark { length: len_at(&a.items) } }
    // What was added since a mark, taken back out in the order it went in.
    pub fn rollback_take(a: &mut Self, mark: ArenaMark<Tag>) -> Result<[T], MarkError> {
        if(mark.length > len_at(&a.items)) { Err(MarkError::Stale) } else {
            let count = len_at(&a.items) - mark.length;
            let items = &mut a.items;
            match(taken_from(replace(items, []), count, [])) {
                (kept, taken) => unsafe { restore_at(items, kept) }; Ok(turned(taken, []))
            }
        }
    }
    // The same, with what was added let go.
    pub fn truncate(a: &mut Self, mark: ArenaMark<Tag>) -> Result<(), MarkError> where T: Use<[0, 1]> {
        match(Arena::rollback_take(a, mark)) { Ok(_) => Ok(()), Err(e) => Err(e) }
    }
    pub fn into_vec(a: Self) -> [T] { match(a) { Arena { items } => items } }
}

// A place in an arena whose places are used again: it says which use of
// the place it was given for, and is refused once that thing is gone.
pub struct GenId<Tag> { index: u32, generation: u32 }

enum Slot<T> { Full(Int, T), Empty(Int) }

// Things that can be taken out again, their places used for others.
pub struct GenArena<Tag, T> { slots: [Slot<T>], free: [Int] }

fn slot_generation<T>(slot: &Slot<T>) -> Int {
    match(slot) { &Slot::Full(g, _) => *g, &Slot::Empty(g) => *g }
}

fn live<T>(slots: [Slot<T>], out: [T]) -> [T] {
    match(pop(slots)) {
        Some((rest, Slot::Full(_, item))) => tail live(rest, push(out, item)),
        Some((rest, Slot::Empty(_))) => tail live(rest, out),
        None => turned(out, [])
    }
}

impl<Tag, T> GenArena<Tag, T> {
    pub fn new() -> Self { Self { slots: [], free: [] } }
    pub fn insert(a: &mut Self, item: T) -> Result<GenId<Tag>, Rejected<T, IndexOverflow>> {
        match(pop(a.free)) {
            Some((rest, i)) => a.free = rest;
                match(element_mut(&mut a.slots, i)) {
                    Some(slot) =>
                        let g = slot_generation(slot);
                        match(replace(slot, Slot::Full(g, item))) {
                            Slot::Empty(_) => Ok(GenId { index: to(i), generation: to(g) }),
                            // (A place that is free holds nothing. If one
                            // did, what it held is not let go: it is what
                            // comes back.)
                            Slot::Full(_, was) => Err(Rejected { value: was, error: IndexOverflow })
                        },
                    None => Err(Rejected { value: item, error: IndexOverflow })
                },
            None => let n = len_at(&a.slots);
                if(n > 4294967295) { Err(Rejected { value: item, error: IndexOverflow }) } else {
                    push_at(&mut a.slots, Slot::Full(0, item));
                    Ok(GenId { index: to(n), generation: 0u32 })
                }
        }
    }
    pub fn contains(a: &Self, id: GenId<Tag>) -> Bool {
        match(element(&a.slots, int(id.index))) {
            Some(slot) => match(slot) { &Slot::Full(g, _) => *g == int(id.generation), &Slot::Empty(_) => false },
            None => false
        }
    }
    pub fn get<'a>(a: &'a Self, id: GenId<Tag>) -> Option<&'a T> {
        match(element(&a.slots, int(id.index))) {
            Some(slot) => match(slot) {
                &Slot::Full(g, item) => if(*g == int(id.generation)) { Some(item) } else { None },
                &Slot::Empty(_) => None
            },
            None => None
        }
    }
    pub fn get_mut<'a>(a: &'a mut Self, id: GenId<Tag>) -> Option<&'a mut T> {
        match(element_mut(&mut a.slots, int(id.index))) {
            Some(slot) => match(slot) {
                &mut Slot::Full(g, item) => if(*g == int(id.generation)) { Some(item) } else { None },
                &mut Slot::Empty(_) => None
            },
            None => None
        }
    }
    // The thing taken out; its place is for another, and this name for it
    // is refused from now on.
    pub fn remove(a: &mut Self, id: GenId<Tag>) -> Option<T> {
        if(GenArena::contains(a, id)) {
            let i = int(id.index);
            match(element_mut(&mut a.slots, i)) {
                Some(slot) => match(replace(slot, Slot::Empty(int(id.generation) + 1))) {
                    Slot::Full(_, item) => a.free = push(a.free, i); Some(item),
                    Slot::Empty(_) => None
                },
                None => None
            }
        } else { None }
    }
    // What is still in it, in the order of its places.
    pub fn into_vec(a: Self) -> [T] { match(a) { GenArena { slots, free: _ } => live(slots, []) } }
}

// What interning found: a new place, or the place of an equal thing already
// there, with the one given handed back.
pub enum InternOutcome<Tag, T> { Inserted(Id<Tag>), Existing { id: Id<Tag>, unused: T } }

// Equal things kept once, each with a place.
pub struct Interner<Tag, T> { values: [T], places: HashMap<T, Int> }

impl<Tag, T> Interner<Tag, T> where T: Eq + Hash {
    pub fn new() -> Self { Self { values: [], places: std::hash::new() } }
    pub fn len(i: &Self) -> Int { len_at(&i.values) }
    pub fn find(i: &Self, item: T) -> Option<Id<Tag>> {
        match(std::hash::get(i.places, item)) { Some(n) => Some(numbered(n)), None => None }
    }
    pub fn intern(i: &mut Self, item: T) -> Result<InternOutcome<Tag, T>, Rejected<T, IndexOverflow>> {
        match(std::hash::get(i.places, item)) {
            Some(n) => Ok(InternOutcome::Existing { id: numbered(n), unused: item }),
            None => let n = len_at(&i.values);
                if(n > 4294967295) { Err(Rejected { value: item, error: IndexOverflow }) } else {
                    i.values = push(i.values, item);
                    i.places = std::hash::insert(i.places, item, n);
                    Ok(InternOutcome::Inserted(numbered(n)))
                }
        }
    }
    // The place alone, whichever it was.
    pub fn intern_discarding(i: &mut Self, item: T) -> Result<Id<Tag>, Rejected<T, IndexOverflow>> {
        match(Interner::intern(i, item)) {
            Ok(InternOutcome::Inserted(id)) => Ok(id),
            Ok(InternOutcome::Existing { id, unused: _ }) => Ok(id),
            Err(e) => Err(e)
        }
    }
    pub fn get<'a>(i: &'a Self, id: Id<Tag>) -> Option<&'a T> { element(&i.values, int(id.0)) }
    pub fn into_values(i: Self) -> [T] { i.values }
}

// Texts kept once each.
pub struct StringInterner<Tag> { texts: Interner<Tag, Str> }

impl<Tag> StringInterner<Tag> {
    pub fn new() -> Self { Self { texts: Interner::new() } }
    pub fn len(i: &Self) -> Int { Interner::len(&i.texts) }
    pub fn intern(i: &mut Self, text: Str) -> Result<Id<Tag>, IndexOverflow> {
        match(Interner::intern_discarding(&mut i.texts, text)) { Ok(id) => Ok(id), Err(_) => Err(IndexOverflow) }
    }
    pub fn find(i: &Self, text: Str) -> Option<Id<Tag>> { Interner::find(&i.texts, text) }
    pub fn get(i: &Self, id: Id<Tag>) -> Option<Str> {
        match(Interner::get(&i.texts, id)) { Some(text) => Some(*text), None => None }
    }
}

// Whether a place of so many is in: one flag each.
pub struct BitSet<Tag> { flags: [Bool], count: Int }

fn flag_at(flags: &[Bool], i: Int) -> Bool { match(element(flags, i)) { Some(f) => *f, None => false } }

fn grown(flags: [Bool], length: Int) -> [Bool] {
    if(len(flags) >= length) { flags } else { tail grown(push(flags, false), length) }
}

fn with_flag(flags: [Bool], i: Int, flag: Bool) -> [Bool] { let mut next = grown(flags, i + 1); next[i] = flag; next }

fn places_of<Tag>(flags: &[Bool], i: Int, out: [Id<Tag>]) -> [Id<Tag>] {
    if(i >= len_at(flags)) { out } else { tail places_of(flags, i + 1, if(flag_at(flags, i)) { push(out, numbered(i)) } else { out }) }
}

// One set changed by another, a place at a time: `keep(mine, theirs)` is
// whether a place is in afterwards. How many places changed.
fn merged(mine: [Bool], theirs: &[Bool], i: Int, changed: Int, keep: fn(Bool, Bool) -> Bool) -> ([Bool], Int) {
    if(i >= len(mine) and { i >= len_at(theirs) }) { (mine, changed) } else {
        let was = flag_at(&mine, i);
        let now = keep(was, flag_at(theirs, i));
        if(was == now) { tail merged(mine, theirs, i + 1, changed, keep) }
        else { tail merged(with_flag(mine, i, now), theirs, i + 1, changed + 1, keep) }
    }
}

fn counted(flags: &[Bool], i: Int, n: Int) -> Int {
    if(i >= len_at(flags)) { n } else { tail counted(flags, i + 1, if(flag_at(flags, i)) { n + 1 } else { n }) }
}

impl<Tag> BitSet<Tag> {
    pub fn new() -> Self { Self { flags: [], count: 0 } }
    pub fn len(s: &Self) -> Int { s.count }
    pub fn contains(s: &Self, id: Id<Tag>) -> Bool { flag_at(&s.flags, int(id.0)) }
    // Put in: whether it was not in before.
    pub fn insert(s: &mut Self, id: Id<Tag>) -> Bool {
        if(flag_at(&s.flags, int(id.0))) { false } else { s.flags = with_flag(s.flags, int(id.0), true); s.count = s.count + 1; true }
    }
    // Taken out: whether it was in.
    pub fn remove(s: &mut Self, id: Id<Tag>) -> Bool {
        if(flag_at(&s.flags, int(id.0))) { s.flags = with_flag(s.flags, int(id.0), false); s.count = s.count - 1; true } else { false }
    }
    pub fn clear(s: &mut Self) { s.flags = []; s.count = 0; }
    fn merge(s: &mut Self, other: &Self, keep: fn(Bool, Bool) -> Bool) -> Bool {
        match(merged(s.flags, &other.flags, 0, 0, keep)) {
            (flags, changed) => s.count = counted(&flags, 0, 0); s.flags = flags; changed > 0
        }
    }
    // Each says whether the set changed.
    pub fn union_with(s: &mut Self, other: &Self) -> Bool { BitSet::merge(s, other, fn(mine, theirs) { mine or { theirs } }) }
    pub fn intersect_with(s: &mut Self, other: &Self) -> Bool { BitSet::merge(s, other, fn(mine, theirs) { mine and { theirs } }) }
    pub fn subtract(s: &mut Self, other: &Self) -> Bool { BitSet::merge(s, other, fn(mine, theirs) { mine and { not theirs } }) }
    pub fn is_subset(s: &Self, other: &Self) -> Bool { subset_from(&s.flags, &other.flags, 0) }
    // The places in it, least first.
    pub fn to_vec(s: &Self) -> [Id<Tag>] { places_of(&s.flags, 0, []) }
}

fn subset_from(mine: &[Bool], theirs: &[Bool], i: Int) -> Bool {
    if(i >= len_at(mine)) { true } else {
        if(flag_at(mine, i) and { not flag_at(theirs, i) }) { false } else { tail subset_from(mine, theirs, i + 1) }
    }
}

// A set of places that is gone through and emptied quickly: the places in
// it side by side, and for each place where it is among them.
pub struct SparseSet<Tag> { dense: [Int], sparse: [Int] }

fn int_at(items: &[Int], i: Int) -> Int { match(element(items, i)) { Some(n) => *n, None => 0 - 1 } }

fn grown_ints(items: [Int], length: Int) -> [Int] {
    if(len(items) >= length) { items } else { tail grown_ints(push(items, 0 - 1), length) }
}

fn with_int(items: [Int], i: Int, n: Int) -> [Int] { let mut next = grown_ints(items, i + 1); next[i] = n; next }

fn ids_of<Tag>(items: &[Int], i: Int, out: [Id<Tag>]) -> [Id<Tag>] {
    if(i >= len_at(items)) { out } else { tail ids_of(items, i + 1, push(out, numbered(int_at(items, i)))) }
}

impl<Tag> SparseSet<Tag> {
    pub fn new() -> Self { Self { dense: [], sparse: [] } }
    pub fn len(s: &Self) -> Int { len_at(&s.dense) }
    pub fn contains(s: &Self, id: Id<Tag>) -> Bool {
        let at = int_at(&s.sparse, int(id.0));
        if(at < 0) { false } else { int_at(&s.dense, at) == int(id.0) }
    }
    pub fn insert(s: &mut Self, id: Id<Tag>) -> Bool {
        if(SparseSet::contains(s, id)) { false } else {
            s.sparse = with_int(s.sparse, int(id.0), len_at(&s.dense));
            s.dense = push(s.dense, int(id.0));
            true
        }
    }
    // The last among them takes the place of the one taken out.
    pub fn remove(s: &mut Self, id: Id<Tag>) -> Bool {
        if(SparseSet::contains(s, id)) {
            let at = int_at(&s.sparse, int(id.0));
            match(pop(s.dense)) {
                Some((rest, last)) => s.dense = if(at < len(rest)) { with_int(rest, at, last) } else { rest };
                    s.sparse = with_int(with_int(s.sparse, last, at), int(id.0), 0 - 1);
                    true,
                None => false
            }
        } else { false }
    }
    pub fn clear(s: &mut Self) { s.dense = []; s.sparse = []; }
    pub fn to_vec(s: &Self) -> [Id<Tag>] { ids_of(&s.dense, 0, []) }
}

// Places waiting to be seen to, first in first out, each waiting once.
pub struct WorkQueue<Tag> { waiting: [Int], next: Int, pending: [Bool] }

impl<Tag> WorkQueue<Tag> {
    pub fn new() -> Self { Self { waiting: [], next: 0, pending: [] } }
    pub fn contains(q: &Self, id: Id<Tag>) -> Bool { flag_at(&q.pending, int(id.0)) }
    pub fn is_empty(q: &Self) -> Bool { q.next >= len_at(&q.waiting) }
    // Whether it was not already waiting.
    pub fn push(q: &mut Self, id: Id<Tag>) -> Bool {
        if(flag_at(&q.pending, int(id.0))) { false } else {
            q.pending = with_flag(q.pending, int(id.0), true);
            q.waiting = push(q.waiting, int(id.0));
            true
        }
    }
    // The one that has waited longest, no longer waiting.
    pub fn pop(q: &mut Self) -> Option<Id<Tag>> {
        if(q.next >= len_at(&q.waiting)) { None } else {
            let i = int_at(&q.waiting, q.next);
            q.pending = with_flag(q.pending, i, false);
            q.next = q.next + 1;
            // (Nothing waiting: start again from the front.)
            if(q.next >= len_at(&q.waiting)) { q.waiting = []; q.next = 0; } else { };
            Some(numbered(i))
        }
    }
    pub fn clear(q: &mut Self) { q.waiting = []; q.next = 0; q.pending = []; }
}
"#

private def budgetText : String := r#"// What a piece of work may use, counted: steps, memory, depth; and a log of
// what to undo, as the library specification has them (25.2, 25.3). Amounts
// are `Int`.

use std::value::{Rejected};
pub use std::error::{MarkError};

pub enum BudgetKind { Steps, Depth, Memory, Diagnostics, Items }
pub struct BudgetExceeded { pub kind: BudgetKind, pub requested: Int, pub remaining: Int }

// Steps that may still be taken.
pub struct StepBudget { left: Int }

impl StepBudget {
    pub fn new(limit: Int) -> Self { Self { left: if(limit < 0) { 0 } else { limit } } }
    pub fn remaining(b: &Self) -> Int { b.left }
    // So many taken, or none of them if that is more than are left.
    pub fn charge(b: &mut Self, steps: Int) -> Result<(), BudgetExceeded> {
        if(steps < 0 or { steps > b.left }) { Err(BudgetExceeded { kind: BudgetKind::Steps, requested: steps, remaining: b.left }) }
        else { b.left = b.left - steps; Ok(()) }
    }
}

// Memory that may still be asked for. What is asked for is held as a
// charge, which has to be given back to the budget it came from.
pub struct MemoryBudget { left: Int, out: Int, id: Int }
pub struct MemoryCharge { bytes: Int, of: Int }
impl Use<[1, 1]> for MemoryCharge {}

impl MemoryBudget {
    // (`id` tells this budget's charges from another's: a release checks it.)
    pub fn new(limit: Int) -> Self { Self { left: if(limit < 0) { 0 } else { limit }, out: 0, id: 0 } }
    pub fn named(limit: Int, id: Int) -> Self { Self { left: if(limit < 0) { 0 } else { limit }, out: 0, id: id } }
    pub fn remaining(b: &Self) -> Int { b.left }
    pub fn charge(b: &mut Self, bytes: Int) -> Result<MemoryCharge, BudgetExceeded> {
        if(bytes < 0 or { bytes > b.left }) { Err(BudgetExceeded { kind: BudgetKind::Memory, requested: bytes, remaining: b.left }) }
        else { b.left = b.left - bytes; b.out = b.out + bytes; Ok(MemoryCharge { bytes: bytes, of: b.id }) }
    }
    // A charge given back; one that is another budget's comes back as it was.
    pub fn release(b: &mut Self, charge: MemoryCharge) -> Result<(), Rejected<MemoryCharge, MarkError>> {
        match(charge) {
            MemoryCharge { bytes, of } =>
                if(of != b.id or { bytes > b.out }) { Err(Rejected { value: MemoryCharge { bytes: bytes, of: of }, error: MarkError::WrongOwner }) }
                else { b.left = b.left + bytes; b.out = b.out - bytes; Ok(()) }
        }
    }
}

// How deep work may still go. Going in gives a permit, which has to be
// given back on the way out, the last given first.
pub struct DepthBudget { limit: Int, depth: Int, id: Int }
pub struct DepthPermit { level: Int, of: Int }
impl Use<[1, 1]> for DepthPermit {}

impl DepthBudget {
    pub fn new(limit: Int) -> Self { Self { limit: if(limit < 0) { 0 } else { limit }, depth: 0, id: 0 } }
    pub fn named(limit: Int, id: Int) -> Self { Self { limit: if(limit < 0) { 0 } else { limit }, depth: 0, id: id } }
    pub fn depth(b: &Self) -> Int { b.depth }
    pub fn enter(b: &mut Self) -> Result<DepthPermit, BudgetExceeded> {
        if(b.depth >= b.limit) { Err(BudgetExceeded { kind: BudgetKind::Depth, requested: 1, remaining: 0 }) }
        else { b.depth = b.depth + 1; Ok(DepthPermit { level: b.depth, of: b.id }) }
    }
    pub fn leave(b: &mut Self, permit: DepthPermit) -> Result<(), Rejected<DepthPermit, MarkError>> {
        match(permit) {
            DepthPermit { level, of } =>
                if(of != b.id) { Err(Rejected { value: DepthPermit { level: level, of: of }, error: MarkError::WrongOwner }) } else {
                    if(level != b.depth) { Err(Rejected { value: DepthPermit { level: level, of: of }, error: MarkError::NotTop }) }
                    else { b.depth = b.depth - 1; Ok(()) }
                }
        }
    }
}

// Whether to go on.
pub enum ControlSignal { Proceed, CancelRequested }
pub effect RequestControl { poll() -> ControlSignal }

// Records of what was done, to undo back to a mark. It does not know what
// undoing one is: it gives the records back, the last made first.
pub struct UndoLog<T> { records: [T] }
pub struct UndoMark { length: Int }

fn last_onto<T>(items: [T], count: Int, taken: [T]) -> ([T], [T]) {
    if(count <= 0) { (items, taken) } else {
        match(pop(items)) {
            Some((rest, last)) => tail last_onto(rest, count - 1, push(taken, last)),
            None => ([], taken)
        }
    }
}

fn turned<T>(from: [T], onto: [T]) -> [T] {
    match(pop(from)) { Some((rest, last)) => tail turned(rest, push(onto, last)), None => onto }
}

impl<T> UndoLog<T> {
    pub fn new() -> Self { Self { records: [] } }
    pub fn len(log: &Self) -> Int { len_at(&log.records) }
    pub fn mark(log: &Self) -> UndoMark { UndoMark { length: len_at(&log.records) } }
    pub fn push(log: &mut Self, item: T) { push_at(&mut log.records, item); }
    // The records since a mark, the last made first, for undoing.
    pub fn rollback_take(log: &mut Self, mark: UndoMark) -> Result<[T], MarkError> {
        if(mark.length > len_at(&log.records)) { Err(MarkError::Stale) } else {
            let count = len_at(&log.records) - mark.length;
            let records = &mut log.records;
            let none = [];
            match(last_onto(replace(records, []), count, none)) {
                (kept, taken) => unsafe { restore_at(records, kept) }; Ok(taken)
            }
        }
    }
    // The same records in the order they were made: no longer needed.
    pub fn commit(log: &mut Self, mark: UndoMark) -> Result<[T], MarkError> {
        match(UndoLog::rollback_take(log, mark)) { Ok(taken) => Ok(turned(taken, [])), Err(e) => Err(e) }
    }
    pub fn clear(log: &mut Self) where T: Use<[0, 1]> { log.records = []; }
}
"#

private def parseText : String := r#"// A place in a row of things, and parsers tried from it, as the library
// specification has them (26.1). Places are `Int`.

use std::slice::{Slice};
use std::budget::{BudgetExceeded, BudgetKind};
pub use std::error::{MarkError};

// A row of things read from front to back.
pub struct Cursor<'a, T> { input: Slice<'a, T>, at: Int }
pub struct CursorMark { at: Int, length: Int }

// What a parser found: something, nothing here (and it may be tried
// elsewhere), or something wrong.
pub enum ParseStep<T, E> { Matched(T), NoMatch, Failed(E) }
pub enum ParseError<E> { User(E), NoProgress, Limit(BudgetExceeded) }

impl<'a, T> Cursor<'a, T> {
    pub fn new(input: Slice<'a, T>) -> Self { Self { input: input, at: 0 } }
    pub fn position(c: &Self) -> Int { c.at }
    pub fn is_done(c: &Self) -> Bool { c.at >= Slice::len(&c.input) }
    pub fn remaining(c: &Self) -> Slice<'a, T> {
        match(Slice::sub(&c.input, c.at, Slice::len(&c.input))) { Some(rest) => rest, None => c.input }
    }
    pub fn peek(c: &Self) -> Option<&'a T> { Slice::get(&c.input, c.at) }
    pub fn next(c: &mut Self) -> Option<&'a T> {
        match(Slice::get(&c.input, c.at)) { Some(item) => c.at = c.at + 1; Some(item), None => None }
    }
    pub fn mark(c: &Self) -> CursorMark { CursorMark { at: c.at, length: Slice::len(&c.input) } }
    pub fn restore(c: &mut Self, mark: CursorMark) -> Result<(), MarkError> {
        if(mark.length != Slice::len(&c.input)) { Err(MarkError::WrongOwner) } else {
            if(mark.at > mark.length) { Err(MarkError::OutOfRange) } else { c.at = mark.at; Ok(()) }
        }
    }
}

// A parser tried. Where it finds nothing the cursor is put back where it
// was; what else the parser did is not undone.
pub fn attempt<'a, T, U, E, e: EffectRow>(cursor: &mut Cursor<'a, T>, parse: fn(&mut Cursor<'a, T>) -> ParseStep<U, E> / e)
    -> ParseStep<U, E> / { | e } {
    let at = cursor.at;
    match(parse(cursor)) {
        ParseStep::NoMatch => cursor.at = at; ParseStep::NoMatch,
        found => found
    }
}

fn many_onto<'a, T, U, E, e: EffectRow>(cursor: &mut Cursor<'a, T>, limit: Int,
    parse: fn(&mut Cursor<'a, T>) -> ParseStep<U, E> / e, out: [U], count: Int)
    -> Result<[U], ([U], ParseError<E>)> / { | e } {
    if(Cursor::is_done(cursor)) { Ok(out) } else {
        if(count >= limit) {
            Err((out, ParseError::Limit(BudgetExceeded { kind: BudgetKind::Items, requested: count + 1, remaining: 0 })))
        } else {
            let before = cursor.at;
            match(attempt(cursor, parse)) {
                ParseStep::Matched(item) =>
                    // One that found something without moving on would
                    // find it again for ever.
                    if(cursor.at == before) { Err((push(out, item), ParseError::NoProgress)) }
                    else { many_onto(cursor, limit, parse, push(out, item), count + 1) },
                ParseStep::NoMatch => Ok(out),
                ParseStep::Failed(e) => Err((out, ParseError::User(e)))
            }
        }
    }
}

// A parser as many times as it finds something, up to so many: what it
// found each time. What was found is given back with what went wrong, too.
pub fn many<'a, T, U, E, e: EffectRow>(cursor: &mut Cursor<'a, T>, limit: Int,
    parse: fn(&mut Cursor<'a, T>) -> ParseStep<U, E> / e)
    -> Result<[U], ([U], ParseError<E>)> / { | e } {
    many_onto(cursor, limit, parse, [], 0)
}
"#

private def graphText : String := r#"// Going over a graph from what each node leads to, as the library
// specification has it (26.2). The order found is the order the nodes and
// what they lead to are given in, never a table's.

use std::hash::{Hash, HashMap};
use std::slice::{Slice};
use std::budget::{StepBudget, BudgetExceeded};

// Something with nodes, each leading to others.
pub trait Graph {
    type Node;
    fn successors(&Self, Self::Node) -> [Self::Node]
}

// Nodes that lead round to the first of them.
pub struct Cycle<N> { pub nodes: [N] }
pub enum GraphError<N> { Cycle(Cycle<N>), Limit(BudgetExceeded) }

// More onto a stack so that the first of them comes off first.
fn stacked<N>(stack: [N], more: [N], i: Int) -> [N] {
    if(i <= 0) { stack } else { tail stacked(push(stack, more[i - 1]), more, i - 1) }
}

fn reach<N: Eq + Hash, G: Graph<Node = N>>(graph: &G, stack: [N], seen: HashMap<N, ()>, out: [N], budget: &mut StepBudget)
    -> Result<[N], BudgetExceeded> {
    match(pop(stack)) {
        None => Ok(out),
        Some((rest, node)) => match(StepBudget::charge(budget, 1)) {
            Err(e) => Err(e),
            Ok(_) =>
                if(std::hash::contains_key(seen, node)) { tail reach(graph, rest, seen, out, budget) } else {
                    let next = successors(graph, node);
                    tail reach(graph, stacked(rest, next, len(next)), std::hash::insert(seen, node, ()), push(out, node), budget)
                }
        }
    }
}

// Every node that can be got to from one, itself first, each once. A step
// is charged for each node looked at.
pub fn reachable<N: Eq + Hash, G: Graph<Node = N>>(graph: &G, start: N, budget: &mut StepBudget)
    -> Result<[N], BudgetExceeded> {
    reach(graph, [start], std::hash::new(), [], budget)
}

// The nodes on the way from one of them to the end of the way.
fn way_from<N: Eq>(way: [N], node: N, i: Int, found: Bool, out: [N]) -> [N] {
    if(i >= len(way)) { out } else {
        let here = found or { way[i] == node };
        tail way_from(way, node, i + 1, here, if(here) { push(out, way[i]) } else { out })
    }
}

// Each of some nodes looked at in turn, and from it what it leads to: the
// nodes done with, each after all it leads to. (A node is being looked at,
// `1`, or done with, `2`; one met again while being looked at is on a way
// that comes back to itself.)
fn visit_each<N: Eq + Hash, G: Graph<Node = N>>(graph: &G, nodes: [N], i: Int, state: HashMap<N, Int>, done: [N], way: [N], budget: &mut StepBudget)
    -> Result<(HashMap<N, Int>, [N]), GraphError<N>> {
    if(i >= len(nodes)) { Ok((state, done)) } else {
        let node = nodes[i];
        match(StepBudget::charge(budget, 1)) {
            Err(e) => Err(GraphError::Limit(e)),
            Ok(_) => match(std::hash::get(state, node)) {
                Some(2) => visit_each(graph, nodes, i + 1, state, done, way, budget),
                Some(_) => Err(GraphError::Cycle(Cycle { nodes: way_from(way, node, 0, false, []) })),
                None => match(visit_each(graph, successors(graph, node), 0, std::hash::insert(state, node, 1), done, push(way, node), budget)) {
                    Ok((after, found)) => visit_each(graph, nodes, i + 1, std::hash::insert(after, node, 2), push(found, node), way, budget),
                    Err(e) => Err(e)
                }
            }
        }
    }
}

fn back_to_front<N>(items: [N], i: Int, out: [N]) -> [N] {
    if(i <= 0) { out } else { tail back_to_front(items, i - 1, push(out, items[i - 1])) }
}

fn copied<'a, N>(nodes: &Slice<'a, N>, i: Int, out: [N]) -> [N] {
    match(Slice::get(nodes, i)) { Some(node) => tail copied(nodes, i + 1, push(out, *node)), None => out }
}

// The nodes that can be got to from those given, each before every node it
// leads to; or nodes that lead round in a circle, where there are some.
pub fn topological_order<'a, N: Eq + Hash, G: Graph<Node = N>>(graph: &G, nodes: Slice<'a, N>, budget: &mut StepBudget)
    -> Result<[N], GraphError<N>> {
    match(visit_each(graph, copied(&nodes, 0, []), 0, std::hash::new(), [], [], budget)) {
        Ok((_, done)) => Ok(back_to_front(done, len(done), [])),
        Err(e) => Err(e)
    }
}

// What is known while the groups are looked for: when each node was first
// seen, the earliest it can get back to, the nodes not yet in a group.
struct Search<N> { seen: HashMap<N, Int>, low: HashMap<N, Int>, open: HashMap<N, Bool>, stack: [N], next: Int, groups: [[N]] }

fn number<N: Eq + Hash>(m: HashMap<N, Int>, node: N) -> Int { match(std::hash::get(m, node)) { Some(n) => n, None => 0 - 1 } }

fn lower<N: Eq + Hash>(s: Search<N>, node: N, to: Int) -> Search<N> {
    let mut next = s;
    if(to < number(next.low, node)) { next.low = std::hash::insert(next.low, node, to); } else { };
    next
}

// The nodes at the top of the stack down to one of them, as a group.
fn closed<N: Eq + Hash>(s: Search<N>, root: N, group: [N]) -> Search<N> {
    let mut next = s;
    match(pop(next.stack)) {
        None => next.groups = push(next.groups, group); next,
        Some((rest, node)) =>
            next.stack = rest;
            next.open = std::hash::insert(next.open, node, false);
            if(node == root) { next.groups = push(next.groups, push(group, node)); next }
            else { closed(next, root, push(group, node)) }
    }
}

// A node seen for the first time: numbered, and not yet in a group.
fn entered<N: Eq + Hash>(s: Search<N>, node: N) -> Search<N> {
    let mut next = s;
    let at = next.next;
    next.seen = std::hash::insert(next.seen, node, at);
    next.low = std::hash::insert(next.low, node, at);
    next.open = std::hash::insert(next.open, node, true);
    next.stack = push(next.stack, node);
    next.next = at + 1;
    next
}

fn lowered<N: Eq + Hash>(s: Search<N>, from: Option<N>, to: Int) -> Search<N> {
    match(from) { Some(node) => lower(s, node, to), None => s }
}

// Each of the nodes one leads to, in turn. One not seen before is gone into,
// and is the root of a group if nothing under it gets back above it.
fn search_each<N: Eq + Hash, G: Graph<Node = N>>(graph: &G, from: Option<N>, nodes: [N], i: Int, s: Search<N>, budget: &mut StepBudget)
    -> Result<Search<N>, BudgetExceeded> {
    if(i >= len(nodes)) { Ok(s) } else {
        let to = nodes[i];
        let first = number(s.seen, to);
        if(first < 0) {
            match(StepBudget::charge(budget, 1)) {
                Err(e) => Err(e),
                Ok(_) => match(search_each(graph, Some(to), successors(graph, to), 0, entered(s, to), budget)) {
                    Err(e) => Err(e),
                    Ok(after) =>
                        let reached = number(after.low, to);
                        let settled = if(reached == number(after.seen, to)) { closed(after, to, []) } else { after };
                        search_each(graph, from, nodes, i + 1, lowered(settled, from, reached), budget)
                }
            }
        } else {
            let still = match(std::hash::get(s.open, to)) { Some(open) => open, None => false };
            search_each(graph, from, nodes, i + 1, if(still) { lowered(s, from, first) } else { s }, budget)
        }
    }
}

// The nodes that can be got to from those given, in groups: two nodes are
// in one group when each can be got to from the other. A group comes before
// any group that leads to it.
pub fn strongly_connected_components<'a, N: Eq + Hash, G: Graph<Node = N>>(graph: &G, nodes: Slice<'a, N>, budget: &mut StepBudget)
    -> Result<[[N]], BudgetExceeded> {
    let start = Search { seen: std::hash::new(), low: std::hash::new(), open: std::hash::new(), stack: [], next: 0, groups: [] };
    match(search_each(graph, None, copied(&nodes, 0, []), 0, start, budget)) { Ok(s) => Ok(s.groups), Err(e) => Err(e) }
}
"#

private def sourceText : String := r#"// Texts by number, and places in them by line, as the library specification
// has them (25.1). Places are bytes of the text as UTF-8, counted from
// nothing, as lines and columns are; they are `Int`.

use std::value::{Rejected};
use std::text::{utf8, from_utf8};

pub struct SourceId(u32);

impl SourceId {
    // Which text of its map it is, counted from nothing.
    pub fn to_u32(value: Self) -> u32 { value.0 }
}
// A stretch of a text: from one place up to, not including, another.
pub struct SourceSpan { pub source: SourceId, pub start: Int, pub end: Int }
pub struct SourceLocation { pub source: SourceId, pub line: Int, pub column_bytes: Int }
// A place as editors count it: the column in units of UTF-16.
pub struct Utf16Location { pub line: Int, pub column_units: Int }
pub enum SourceError { UnknownSource, InvalidRange, InvalidBoundary, IndexOverflow }

struct Source { name: Str, bytes: [u8], lines: [Int] }

// Texts, each given a number when it is put in. It reads no files.
pub struct SourceMap { sources: [Source] }

fn byte_at(bytes: &[u8], i: Int) -> Int { match(element(bytes, i)) { Some(b) => int(*b), None => 0 } }

// Where each line starts: after each end of line, and at the start.
fn line_starts(bytes: &[u8], i: Int, out: [Int]) -> [Int] {
    if(i >= len_at(bytes)) { out } else {
        tail line_starts(bytes, i + 1, if(byte_at(bytes, i) == 10) { push(out, i + 1) } else { out })
    }
}

fn piece(bytes: &[u8], from: Int, upto: Int, out: [u8]) -> [u8] {
    if(from >= upto) { out } else {
        match(element(bytes, from)) {
            Some(b) => tail piece(bytes, from + 1, upto, push(out, *b)),
            None => out
        }
    }
}

// Is a place between two characters, and not inside one? A byte that goes
// on a character begun before it is `10` and six bits.
fn on_boundary(bytes: &[u8], at: Int) -> Bool {
    if(at == len_at(bytes)) { true } else { let b = byte_at(bytes, at); b < 128 or { b >= 192 } }
}

// The last line that starts at or before a place.
fn line_of(lines: &[Int], at: Int, low: Int, high: Int) -> Int {
    if(low + 1 >= high) { low } else {
        let mid = (low + high) / 2;
        match(element(lines, mid)) {
            Some(start) => if(*start <= at) { tail line_of(lines, at, mid, high) } else { tail line_of(lines, at, low, mid) },
            None => low
        }
    }
}

fn int_at(items: &[Int], i: Int) -> Int { match(element(items, i)) { Some(n) => *n, None => 0 } }

// How many units of UTF-16 the characters from one place to another are: a
// character of four bytes is two, any other one.
fn units_between(bytes: &[u8], at: Int, end: Int, units: Int) -> Int {
    if(at >= end) { units } else {
        let b = byte_at(bytes, at);
        if(b < 128) { tail units_between(bytes, at + 1, end, units + 1) } else {
            if(b < 224) { tail units_between(bytes, at + 2, end, units + 1) } else {
                if(b < 240) { tail units_between(bytes, at + 3, end, units + 1) }
                else { tail units_between(bytes, at + 4, end, units + 2) }
            }
        }
    }
}

// The place so many units of UTF-16 on from another, if that is between
// two characters and before a limit.
fn after_units(bytes: &[u8], at: Int, limit: Int, units: Int) -> Option<Int> {
    if(units == 0) { Some(at) } else {
        if(units < 0 or { at >= limit }) { None } else {
            let b = byte_at(bytes, at);
            if(b < 128) { tail after_units(bytes, at + 1, limit, units - 1) } else {
                if(b < 224) { tail after_units(bytes, at + 2, limit, units - 1) } else {
                    if(b < 240) { tail after_units(bytes, at + 3, limit, units - 1) }
                    else { tail after_units(bytes, at + 4, limit, units - 2) }
                }
            }
        }
    }
}

impl SourceMap {
    pub fn new() -> Self { Self { sources: [] } }
    pub fn len(m: &Self) -> Int { len_at(&m.sources) }
    pub fn insert(m: &mut Self, name: Str, text: Str) -> Result<SourceId, Rejected<(Str, Str), SourceError>> {
        let n = len_at(&m.sources);
        if(n > 4294967295) { Err(Rejected { value: (name, text), error: SourceError::IndexOverflow }) } else {
            let bytes = utf8(text);
            let lines = line_starts(&bytes, 0, [0]);
            push_at(&mut m.sources, Source { name: name, bytes: bytes, lines: lines });
            Ok(SourceId(to(n)))
        }
    }
    fn source<'a>(m: &'a Self, id: SourceId) -> Option<&'a Source> { element(&m.sources, int(id.0)) }
    pub fn name(m: &Self, id: SourceId) -> Option<Str> {
        match(SourceMap::source(m, id)) { Some(s) => Some(s.name), None => None }
    }
    pub fn text(m: &Self, id: SourceId) -> Option<Str> {
        match(SourceMap::source(m, id)) { Some(s) => from_utf8(s.bytes), None => None }
    }
    // The text of a stretch, which has to begin and end between characters.
    pub fn slice(m: &Self, span: SourceSpan) -> Result<Str, SourceError> {
        match(SourceMap::source(m, span.source)) {
            None => Err(SourceError::UnknownSource),
            Some(s) =>
                if(span.start < 0 or { span.end < span.start or { span.end > len_at(&s.bytes) } }) { Err(SourceError::InvalidRange) } else {
                    if(on_boundary(&s.bytes, span.start) and { on_boundary(&s.bytes, span.end) }) {
                        match(from_utf8(piece(&s.bytes, span.start, span.end, []))) { Some(text) => Ok(text), None => Err(SourceError::InvalidBoundary) }
                    } else { Err(SourceError::InvalidBoundary) }
                }
        }
    }
    // The line a place is on, and how many bytes into it.
    pub fn locate(m: &Self, id: SourceId, offset: Int) -> Result<SourceLocation, SourceError> {
        match(SourceMap::source(m, id)) {
            None => Err(SourceError::UnknownSource),
            Some(s) =>
                if(offset < 0 or { offset > len_at(&s.bytes) }) { Err(SourceError::InvalidRange) } else {
                    if(on_boundary(&s.bytes, offset)) {
                        let line = line_of(&s.lines, offset, 0, len_at(&s.lines));
                        Ok(SourceLocation { source: id, line: line, column_bytes: offset - int_at(&s.lines, line) })
                    } else { Err(SourceError::InvalidBoundary) }
                }
        }
    }
    pub fn to_utf16(m: &Self, id: SourceId, offset: Int) -> Result<Utf16Location, SourceError> {
        match(SourceMap::locate(m, id, offset)) {
            Err(e) => Err(e),
            Ok(at) => match(SourceMap::source(m, id)) {
                None => Err(SourceError::UnknownSource),
                Some(s) => Ok(Utf16Location { line: at.line, column_units: units_between(&s.bytes, offset - at.column_bytes, offset, 0) })
            }
        }
    }
    // The place a line and a column of UTF-16 are: not one inside a
    // character that is two units, nor past the line's end.
    pub fn from_utf16(m: &Self, id: SourceId, location: Utf16Location) -> Result<Int, SourceError> {
        match(SourceMap::line_range(m, id, location.line)) {
            Err(e) => Err(e),
            Ok((start, end)) => match(SourceMap::source(m, id)) {
                None => Err(SourceError::UnknownSource),
                Some(s) => match(after_units(&s.bytes, start, end, location.column_units)) {
                    Some(at) => Ok(at),
                    None => Err(if(location.column_units > units_between(&s.bytes, start, end, 0)) { SourceError::InvalidRange } else { SourceError::InvalidBoundary })
                }
            }
        }
    }
    // Where a line starts and where it ends, its end of line not counted.
    pub fn line_range(m: &Self, id: SourceId, line: Int) -> Result<(Int, Int), SourceError> {
        match(SourceMap::source(m, id)) {
            None => Err(SourceError::UnknownSource),
            Some(s) =>
                if(line < 0 or { line >= len_at(&s.lines) }) { Err(SourceError::InvalidRange) } else {
                    let start = int_at(&s.lines, line);
                    let next = if(line + 1 < len_at(&s.lines)) { int_at(&s.lines, line + 1) - 1 } else { len_at(&s.bytes) };
                    Ok((start, next))
                }
        }
    }
}
"#

private def boxedText : String := r#"// One value kept as its owner's alone, as the library specification has it
// (22.3). Every value here is kept somewhere of its own already, so a `Box`
// is the value under another name: it is for programs written to be read
// where that is not so.

use std::value::{Rejected};
use std::c::{AllocError};

pub struct Box<T> { held: T }

impl<T> Box<T> {
    pub fn new(value: T) -> Self { Self { held: value } }
    pub fn try_new(value: T) -> Result<Self, Rejected<T, AllocError>> { Ok(Self { held: value }) }
    pub fn as_ref<'a>(value: &'a Self) -> &'a T { &value.held }
    pub fn as_mut<'a>(value: &'a mut Self) -> &'a mut T { &mut value.held }
    pub fn into_inner(value: Self) -> T { match(value) { Box { held } => held } }
}
"#

private def taskText : String := r#"// Work started and waited for, as the library specification has it (30.4),
// and tasks that take turns. Nothing here runs two things at once.

use std::generator::{Yield, yield, Coroutine, Generator, GeneratorStep, resume};

// Work that was started: its result is had by waiting for it. A handle has
// to be given to `join` or `cancel_task`: there is no letting it go.
pub struct Task<T> { result: T }
impl Use<[1, 1]> for Task {}

pub enum TaskError { Cancelled, Failed, ProviderClosed }
pub enum CancelOutcome<T> { Cancelled, Completed(T) }

// Starting work that makes a `T`: whoever handles this says when it runs.
// Whoever asks is always answered, with the handle.
// (The work performs nothing, which is what lets a provider run it and be
// sure to answer.)
pub effect Spawn<T> { [1, 1] spawn(work: fn() -> T / {}) -> Task<T> }

// Waiting for work, and asking it to stop: what it made is never lost, and
// whoever asks is always answered.
pub effect TaskControl<T> {
    [1, 1] join(task: Task<T>) -> Result<T, TaskError>,
    [1, 1] cancel_task(task: Task<T>) -> CancelOutcome<T>
}

// The simplest provider: work runs where it is spawned, to its end, so
// waiting for it finds it done and asking it to stop finds it finished.
pub fn run_inline<T, R>(body: fn() -> R / {Spawn<T>, TaskControl<T>}) -> R {
    handle body() {
        spawn(work, k) => k(Task { result: work() }),
        join(task, k) => match(task) { Task { result } => k(Ok(result)) },
        cancel_task(task, k) => match(task) { Task { result } => k(CancelOutcome::Completed(result)) }
    }
}

// Giving way to the other tasks.
pub fn yield_now() / {Yield<(), ()>} { yield(()) }

fn turned<T>(from: [T], onto: [T]) -> [T] {
    match(pop(from)) { Some((rest, last)) => tail turned(rest, push(onto, last)), None => onto }
}

// A result put among those done, kept in the order of the tasks' numbers.
fn placed<T>(done: [(Int, T)], at: Int, result: T) -> [(Int, T)] {
    match(pop(done)) {
        None => [(at, result)],
        Some((rest, (i, r))) =>
            if(i > at) { push(placed(rest, at, result), (i, r)) } else { push(push(rest, (i, r)), (at, result)) }
    }
}

// (They are kept by how late each task was given, so the last of them is
// the first given.)
fn results<T>(done: [(Int, T)], out: [T]) -> [T] {
    match(pop(done)) { Some((rest, (_, r))) => tail results(rest, push(out, r)), None => out }
}

// One step of each task still going, the first given first; then again
// with those that gave way, until none is left.
fn turns<T>(waiting: [(Int, Coroutine<(), (), T>)], next: [(Int, Coroutine<(), (), T>)], done: [(Int, T)]) -> [(Int, T)] {
    match(pop(waiting)) {
        Some((rest, (i, task))) => match(resume(task, ())) {
            GeneratorStep::Yielded { value: _, rest: more } => turns(rest, push(next, (i, more)), done),
            GeneratorStep::Complete(result) => turns(rest, next, placed(done, i, result))
        },
        None => match(pop(next)) {
            None => done,
            Some((others, last)) => turns(turned(push(others, last), []), [], done)
        }
    }
}

// Each task with a number: the last given has nothing, the one before it
// one. (Taken from the end, so the first given is the last put, and is then
// the first taken off.)
fn numbered<T>(tasks: [Coroutine<(), (), T>], out: [(Int, Coroutine<(), (), T>)], late: Int) -> [(Int, Coroutine<(), (), T>)] {
    match(pop(tasks)) { Some((rest, task)) => tail numbered(rest, push(out, (late, task)), late + 1), None => out }
}

// Tasks that take turns: each runs until it gives way with `yield_now` or
// ends, then the next, round and round. What each made, in the order the
// tasks were given.
pub fn round_robin<T>(tasks: [Coroutine<(), (), T>]) -> [T] {
    results(turns(numbered(tasks, [], 0), [], []), [])
}
"#

private def pathText : String := r#"// Paths taken apart and put together as text, as the library specification
// has them (29.1), for paths written with `/`. Nothing here looks at a file
// system: a link is not followed, and a path is not shown to stay inside
// another.

use std::text::{split, join, starts_with, is_empty};

// A path, kept as it is written.
pub struct PathBuf { text: Str }

pub enum PathComponent { Root, Current, Parent, Normal(Str) }
pub enum PathError { InvalidEncoding, InvalidComponent, UnsupportedPrefix }

// The names between the `/`s, those that are nothing left out.
fn names(text: Str) -> [Str] { kept(split(text, '/'), 0, []) }
fn kept(parts: [Str], i: Int, out: [Str]) -> [Str] {
    if(i >= len(parts)) { out } else { tail kept(parts, i + 1, if(is_empty(parts[i])) { out } else { push(out, parts[i]) }) }
}

fn component(name: Str) -> PathComponent {
    if(name == ".") { PathComponent::Current } else { if(name == "..") { PathComponent::Parent } else { PathComponent::Normal(name) } }
}

fn components_of(parts: [Str], i: Int, out: [PathComponent]) -> [PathComponent] {
    if(i >= len(parts)) { out } else { tail components_of(parts, i + 1, push(out, component(parts[i]))) }
}

fn upto(parts: [Str], n: Int, i: Int, out: [Str]) -> [Str] {
    if(i >= n) { out } else { tail upto(parts, n, i + 1, push(out, parts[i])) }
}

// The place of the last `.` in a name, if it has one after its first
// character: a name that only begins with one has no extension.
fn last_dot(name: Str, i: Int, found: Int) -> Int {
    match(name) {
        StrEnd => found,
        StrChar(c, rest) => tail last_dot(rest, i + 1, if(c == '.' and { i > 0 }) { i } else { found })
    }
}

impl PathBuf {
    pub fn new() -> Self { Self { text: "" } }
    pub fn from_str(text: Str) -> Self { Self { text: text } }
    pub fn as_str(p: &Self) -> Str { p.text }
    pub fn is_absolute(p: &Self) -> Bool { starts_with(p.text, "/") }
    // What it is made of, in order: the root if it starts at it, then each
    // name, with `.` and `..` told from the others.
    pub fn components(p: &Self) -> [PathComponent] {
        components_of(names(p.text), 0, if(starts_with(p.text, "/")) { [PathComponent::Root] } else { [] })
    }
    // The last name, if the path ends in one.
    pub fn file_name(p: &Self) -> Option<Str> {
        let parts = names(p.text);
        let n = len(parts);
        if(n == 0) { None } else {
            let last = parts[n - 1];
            if(last == "." or { last == ".." }) { None } else { Some(last) }
        }
    }
    // What follows the last `.` of the last name.
    pub fn extension(p: &Self) -> Option<Str> {
        match(PathBuf::file_name(p)) {
            None => None,
            Some(name) =>
                let at = last_dot(name, 0, 0 - 1);
                if(at < 0) { None } else { Some(std::text::drop(name, at + 1)) }
        }
    }
    // The path without its last name: none for the root and for a path of
    // no names.
    pub fn parent(p: &Self) -> Option<PathBuf> {
        let parts = names(p.text);
        let n = len(parts);
        if(n == 0) { None } else {
            let before = join(upto(parts, n - 1, 0, []), "/");
            Some(PathBuf { text: if(starts_with(p.text, "/")) { "/" ++ before } else { before } })
        }
    }
    // Another path after this one; one that starts at the root takes its
    // place.
    pub fn join(p: &Self, other: &Self) -> PathBuf {
        if(starts_with(other.text, "/") or { is_empty(p.text) }) { PathBuf { text: other.text } } else {
            if(is_empty(other.text)) { PathBuf { text: p.text } } else {
                PathBuf { text: if(std::text::ends_with(p.text, "/")) { p.text ++ other.text } else { p.text ++ "/" ++ other.text } }
            }
        }
    }
    pub fn push(p: &mut Self, other: &Self) -> Result<(), PathError> {
        let joined = PathBuf::join(&*p, other);
        p.text = joined.text;
        Ok(())
    }
    // The last name taken off: whether there was one.
    pub fn pop(p: &mut Self) -> Bool {
        match(PathBuf::parent(&*p)) { Some(up) => p.text = up.text; true, None => false }
    }
}
"#

private def futureText : String := r#"// Computations that may not be done yet, as the library specification has
// them (30.3): polling one uses it up, and gives its result or the future
// that goes on. Who polls, and when, is whoever handles `await`.

pub enum FutureStep<T, F> { Ready(T), Pending(F) }

pub trait Future {
    type Output;
    fn poll(Self) -> FutureStep<Self::Output, Self>
}

// Waiting for a future's result. Whoever asks is always answered, with what
// the future made: a handler drives the future, or hands it on, and resumes
// once.
pub effect Await<F, T> { [1, 1] await(F) -> T }

// A future that is done already.
pub struct Ready<T> { value: T }
pub fn ready<T>(value: T) -> Ready<T> { Ready { value: value } }
impl<T> Future for Ready<T> {
    type Output = T;
    fn poll(r) { match(r) { Ready { value } => FutureStep::Ready(value) } }
}

// A future polled until it is done.
pub fn drive<T, F: Future<Output = T>>(future: F) -> T {
    match(poll(future)) { FutureStep::Ready(value) => value, FutureStep::Pending(rest) => drive(rest) }
}

// The simplest provider: a future awaited is driven to its end where it is
// awaited.
pub fn block_on<T, F: Future<Output = T>, R>(body: fn() -> R / {Await<F, T>}) -> R {
    handle body() { await(future, k) => k(drive(future)) }
}
"#

private def generatorText : String := r#"// Generators, in the shape the library specification gives them (30.2): a
// computation that yields is owned as a value, and resuming it uses that
// value up and gives either what it yielded with the generator that goes
// on, or what it finished with. Nothing here is known to the compiler:
// `yield` is an operation, and a generator is its resumption.

use std::iterator::{Iterator};

// A value handed out, and what the computation is resumed with. Whoever
// handles it may stop the computation there.
pub effect Yield<Y, R> { yield(Y) -> R }

// The same, for a computation that is always resumed: it can hold what has
// to be used across the operation.
pub effect YieldOnce<Y, R> { [1, 1] yield_once(Y) -> R }

pub enum GeneratorStep<Y, T, G> { Yielded { value: Y, rest: G }, Complete(T) }

pub trait Generator {
    type Yield;
    type Resume;
    type Return;
    type Effects: EffectRow;
    fn resume(Self, Self::Resume)
        -> GeneratorStep<Self::Yield, Self::Return, Self> / { | Self::Effects };
}

// A computation that yields, stopped where it last did.
pub struct Coroutine<Y, R, T>(fn(R) -> GeneratorStep<Y, T, Coroutine<Y, R, T>>)

impl<Y, R, T> Generator for Coroutine<Y, R, T> {
    type Yield = Y;
    type Resume = R;
    type Return = T;
    type Effects = {};
    fn resume(g, input) { match(g) { Coroutine(k) => k(input) } }
}

// A computation as a generator that has not started. What it is first
// resumed with starts it and is otherwise not looked at.
pub fn generator<Y, R, T>(body: fn() -> T / {Yield<Y, R>}) -> Coroutine<Y, R, T> {
    Coroutine({ (first) => handle body() {
        done => Complete(done),
        yield(value, k) => Yielded { value: value, rest: Coroutine(k) }
    } })
}

// A generator given up: the computation is left where it stopped, and its
// cleanups run. One that is merely let go is forgotten where it stopped.
pub fn close_generator<Y, R, T>(g: Coroutine<Y, R, T>) { match(g) { Coroutine(k) => cancel(k) } }

// A generator that is resumed with nothing, as something to iterate.
pub struct Generated<G, Y> { state: Option<G>, of: fn() -> Option<Y> }

impl<G, Y> Iterator for Generated<G, Y> where G: Generator<Yield = Y, Resume = ()> {
    type Item = Y;
    fn next(it) {
        match(replace(&mut it.state, None)) {
            Some(g) => match(resume(g, ())) {
                Yielded { value, rest } => it.state = Some(rest); Some(value),
                Complete(_) => None
            },
            None => None
        }
    }
}

pub fn iterate<G: Generator>(g: G) -> Generated<G, G::Yield> {
    Generated { state: Some(g), of: { None } }
}
"#

private def fingerprintText : String := r#"// Hashes that come out the same wherever they are worked out: a quick one
// of 64 bits, BLAKE3, and the fingerprints a compiler keeps of what it has
// made, as the library specification has them (20).
//
// A digest's bytes are an array here, always of thirty-two (`from_bytes`
// says if they are not); `hash64` over the `Hash` trait is not here.

use std::slice::{Slice};
use std::bytes::{hex_encode, hex_decode, HexError, HexErrorKind};
use std::text::{utf8};

fn low32(n: Int) -> Int { bit_and(n, 4294967295) }
fn rotr(x: Int, n: Int) -> Int { low32(bit_or(shr(x, n), shl(x, 32 - n))) }
fn byte(n: Int) -> u8 { to(bit_and(n, 255)) }

// The bytes of a number, the least first.
fn le_onto(out: [u8], n: Int, count: Int) -> [u8] {
    if(count == 0) { out } else { le_onto(push(out, byte(n)), shr(n, 8), count - 1) }
}
fn all_onto<'a>(out: [u8], bytes: &Slice<'a, u8>, i: Int) -> [u8] {
    match(Slice::get(bytes, i)) { Some(b) => all_onto(push(out, *b), bytes, i + 1), None => out }
}
fn array_onto(out: [u8], bytes: &[u8], i: Int) -> [u8] {
    match(element(bytes, i)) { Some(b) => array_onto(push(out, *b), bytes, i + 1), None => out }
}

// ---- A quick hash of 64 bits (FNV-1a): not a secret, not an identity. ----

// The two halves of the 64 bits so far.
pub struct Hasher { high: Int, low: Int }

impl Hasher {
    pub fn new() -> Self { Self { high: 3421674724, low: 2216829733 } }
    pub fn write_u8(value: &mut Self, input: u8) {
        let low = bit_xor(value.low, int(input));
        // Times 2^40 + 435, in 64 bits.
        let product = low * 435;
        value.high = low32(value.high * 435 + shr(product, 32) + shl(low32(shl(low, 8)), 0));
        value.low = low32(product);
    }
    pub fn write<'a>(value: &mut Self, bytes: Slice<'a, u8>) { write_from(value, &bytes, 0) }
    pub fn write_u16(value: &mut Self, input: u16) { write_le(value, int(input), 2) }
    pub fn write_u32(value: &mut Self, input: u32) { write_le(value, int(input), 4) }
    pub fn write_u64(value: &mut Self, input: u64) { write_le(value, int(input), 8) }
    pub fn finish(value: &Self) -> u64 {
        let high: u64 = to(value.high);
        let low: u64 = to(value.low);
        high * 4294967296u64 + low
    }
}
fn write_from<'a>(h: &mut Hasher, bytes: &Slice<'a, u8>, i: Int) {
    match(Slice::get(bytes, i)) { Some(b) => Hasher::write_u8(h, *b); write_from(h, bytes, i + 1), None => () }
}
fn write_le(h: &mut Hasher, n: Int, count: Int) {
    if(count == 0) { () } else { Hasher::write_u8(h, byte(n)); write_le(h, shr(n, 8), count - 1) }
}

// ---- BLAKE3, unkeyed, 256 bits. ----

fn iv() -> [Int] { [1779033703, 3144134277, 1013904242, 2773480762, 1359893119, 2600822924, 528734635, 1541459225] }

fn g(state: [Int], a: Int, b: Int, c: Int, d: Int, mx: Int, my: Int) -> [Int] {
    let mut s = state;
    s[a] = low32(s[a] + s[b] + mx);
    s[d] = rotr(bit_xor(s[d], s[a]), 16);
    s[c] = low32(s[c] + s[d]);
    s[b] = rotr(bit_xor(s[b], s[c]), 12);
    s[a] = low32(s[a] + s[b] + my);
    s[d] = rotr(bit_xor(s[d], s[a]), 8);
    s[c] = low32(s[c] + s[d]);
    s[b] = rotr(bit_xor(s[b], s[c]), 7);
    s
}

fn round(s: [Int], m: [Int]) -> [Int] {
    let s = g(s, 0, 4, 8, 12, m[0], m[1]);
    let s = g(s, 1, 5, 9, 13, m[2], m[3]);
    let s = g(s, 2, 6, 10, 14, m[4], m[5]);
    let s = g(s, 3, 7, 11, 15, m[6], m[7]);
    let s = g(s, 0, 5, 10, 15, m[8], m[9]);
    let s = g(s, 1, 6, 11, 12, m[10], m[11]);
    let s = g(s, 2, 7, 8, 13, m[12], m[13]);
    let s = g(s, 3, 4, 9, 14, m[14], m[15]);
    s
}

fn permute(m: [Int]) -> [Int] { [m[2], m[6], m[3], m[10], m[7], m[0], m[4], m[13], m[1], m[11], m[12], m[5], m[9], m[14], m[15], m[8]] }

fn rounds(s: [Int], m: [Int], left: Int) -> [Int] {
    let s = round(s, m);
    if(left == 1) { s } else { rounds(s, permute(m), left - 1) }
}

// What a block of sixteen words makes of a chaining value of eight.
fn compress(cv: [Int], block: [Int], counter: Int, length: Int, flags: Int) -> [Int] {
    let k = iv();
    let s = rounds([cv[0], cv[1], cv[2], cv[3], cv[4], cv[5], cv[6], cv[7], k[0], k[1], k[2], k[3],
        low32(counter), low32(shr(counter, 32)), length, flags], block, 7);
    [bit_xor(s[0], s[8]), bit_xor(s[1], s[9]), bit_xor(s[2], s[10]), bit_xor(s[3], s[11]), bit_xor(s[4], s[12]), bit_xor(s[5], s[13]), bit_xor(s[6], s[14]), bit_xor(s[7], s[15]),
     bit_xor(s[8], cv[0]), bit_xor(s[9], cv[1]), bit_xor(s[10], cv[2]), bit_xor(s[11], cv[3]), bit_xor(s[12], cv[4]), bit_xor(s[13], cv[5]), bit_xor(s[14], cv[6]), bit_xor(s[15], cv[7])]
}
fn first8(s: [Int]) -> [Int] { [s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7]] }

fn byte_at(bytes: &[u8], i: Int, end: Int) -> Int { if(i < end) { int((*bytes)[i]) } else { 0 } }
fn word_at(bytes: &[u8], at: Int, end: Int) -> Int {
    byte_at(bytes, at, end) + shl(byte_at(bytes, at + 1, end), 8) + shl(byte_at(bytes, at + 2, end), 16)
        + shl(byte_at(bytes, at + 3, end), 24)
}
// The sixteen words of the block at a place, with nothing past the end.
fn words_from(bytes: &[u8], at: Int, end: Int, i: Int, out: [Int]) -> [Int] {
    if(i == 16) { out } else { words_from(bytes, at, end, i + 1, push(out, word_at(bytes, at + 4 * i, end))) }
}

// What is still to be compressed of a chunk or of two halves joined: the
// last step, kept apart because the root's is done differently.
struct Out { cv: [Int], block: [Int], counter: Int, length: Int, flags: Int }

fn chaining(o: &Out) -> [Int] { first8(compress(o.cv, o.block, o.counter, o.length, o.flags)) }

// A chunk of up to 1024 bytes, block by block; `first` is 1 until one is done.
fn chunk_out(bytes: &[u8], at: Int, end: Int, counter: Int, cv: [Int], first: Int) -> Out {
    if(end - at > 64) {
        let next = first8(compress(cv, words_from(bytes, at, end, 0, []), counter, 64, first));
        chunk_out(bytes, at + 64, end, counter, next, 0)
    } else {
        Out { cv: cv, block: words_from(bytes, at, end, 0, []), counter: counter, length: end - at, flags: first + 2 }
    }
}

fn joined(left: [Int], right: [Int]) -> Out {
    Out { cv: iv(), block: [left[0], left[1], left[2], left[3], left[4], left[5], left[6], left[7],
        right[0], right[1], right[2], right[3], right[4], right[5], right[6], right[7]],
        counter: 0, length: 64, flags: 4 }
}

// The chaining values of the subtrees finished so far, the latest on top.
enum Stack { Bottom, On([Int], Stack) }

// A finished chunk joins as many finished subtrees as the count of chunks
// so far has twos in it.
fn add_chunk(stack: Stack, cv: [Int], total: Int) -> Stack {
    if(bit_and(total, 1) == 0) {
        match(stack) {
            On(left, rest) => add_chunk(rest, chaining(&joined(left, cv)), shr(total, 1)),
            Bottom => On(cv, Bottom)
        }
    } else { On(cv, stack) }
}

fn fold_up(stack: Stack, out: Out) -> Out {
    match(stack) { Bottom => out, On(left, rest) => fold_up(rest, joined(left, chaining(&out))) }
}

fn chunks(bytes: &[u8], at: Int, end: Int, counter: Int, stack: Stack) -> Out {
    if(end - at > 1024) {
        let cv = chaining(&chunk_out(bytes, at, at + 1024, counter, iv(), 1));
        chunks(bytes, at + 1024, end, counter + 1, add_chunk(stack, cv, counter + 1))
    } else { fold_up(stack, chunk_out(bytes, at, end, counter, iv(), 1)) }
}

fn words_onto(out: [u8], words: &[Int], i: Int) -> [u8] {
    match(element(words, i)) { Some(w) => words_onto(le_onto(out, *w, 4), words, i + 1), None => out }
}

fn digest_of(bytes: &[u8]) -> Digest256 {
    let last = chunks(bytes, 0, len_at(bytes), 0, Bottom);
    let root = first8(compress(last.cv, last.block, 0, last.length, bit_or(last.flags, 8)));
    Digest256 { bytes: words_onto([], &root, 0) }
}

// Thirty-two bytes.
pub struct Digest256 { bytes: [u8] }

impl Digest256 {
    // The digest these bytes are, if there are thirty-two of them.
    pub fn from_bytes(bytes: [u8]) -> Option<Self> {
        if(len(bytes) == 32) { Some(Self { bytes: bytes }) } else { None }
    }
    pub fn as_bytes<'a>(value: &'a Self) -> Slice<'a, u8> { Slice::of(&value.bytes) }
    pub fn to_hex(value: &Self) -> Str { hex_encode(Slice::of(&value.bytes)) }
    pub fn parse_hex(text: Str) -> Result<Self, HexError> {
        match(hex_decode(text)) {
            Err(e) => Err(e),
            Ok(bytes) => if(len(bytes) == 32) { Ok(Self { bytes: bytes }) }
                else { Err(HexError { offset: 0, kind: HexErrorKind::IncorrectLength }) }
        }
    }
}
impl Eq for Digest256 { fn ==(a, b) { a.bytes == b.bytes } }

pub fn blake3<'a>(bytes: Slice<'a, u8>) -> Digest256 { digest_of(&all_onto([], &bytes, 0)) }

// The same, a piece at a time: the pieces are kept and hashed at the end.
pub struct Blake3 { bytes: [u8] }

impl Blake3 {
    pub fn new() -> Self { Self { bytes: [] } }
    pub fn update<'a>(value: &mut Self, bytes: Slice<'a, u8>) {
        value.bytes = all_onto(replace(&mut value.bytes, []), &bytes, 0);
    }
    pub fn finish(value: Self) -> Digest256 { let bytes = value.bytes; digest_of(&bytes) }
}

// ---- Fingerprints: BLAKE3 of a stream written one way only. ----
//
// `GLORIOUS-FP`, a zero byte, the schema, how long the domain is, the domain;
// then each thing written, numbers the least byte first, bytes and texts
// with how many bytes they are before them.
pub struct FingerprintWriter { bytes: [u8] }

impl FingerprintWriter {
    pub fn new(domain: Str, schema: u32) -> Self {
        let name = utf8(domain);
        let start = le_onto(le_onto(push(utf8("GLORIOUS-FP"), 0u8), int(schema), 4), len(name), 8);
        Self { bytes: array_onto(start, &name, 0) }
    }
    pub fn tag(value: &mut Self, tag: u32) { value.bytes = le_onto(replace(&mut value.bytes, []), int(tag), 4); }
    pub fn u32(value: &mut Self, input: u32) { value.bytes = le_onto(replace(&mut value.bytes, []), int(input), 4); }
    pub fn u64(value: &mut Self, input: u64) { value.bytes = le_onto(replace(&mut value.bytes, []), int(input), 8); }
    pub fn bytes<'a>(value: &mut Self, bytes: Slice<'a, u8>) {
        let counted = le_onto(replace(&mut value.bytes, []), Slice::len(&bytes), 8);
        value.bytes = all_onto(counted, &bytes, 0);
    }
    pub fn text(value: &mut Self, text: Str) {
        let written = utf8(text);
        let counted = le_onto(replace(&mut value.bytes, []), len(written), 8);
        value.bytes = array_onto(counted, &written, 0);
    }
    pub fn digest(value: &mut Self, digest: &Digest256) {
        value.bytes = array_onto(replace(&mut value.bytes, []), &digest.bytes, 0);
    }
    pub fn finish(value: Self) -> Digest256 { let bytes = value.bytes; digest_of(&bytes) }
}
"#

private def diagnosticText : String := r#"// What a compiler has to say about a program, kept as what it is (how bad,
// which code, where, with what beside it) and written out at the end, as the
// library specification has it (21).
//
// Texts are `Str` and what a bag gives back is an array, as elsewhere here.

use std::source::{SourceMap, SourceSpan, SourceId};
use std::fmt::{FormatError};
use std::text::{utf8};

pub enum Severity { Note, Warning, Error }

pub struct DiagnosticCode(u32)

impl DiagnosticCode {
    pub fn from_u32(value: u32) -> Self { DiagnosticCode(value) }
    pub fn to_u32(value: Self) -> u32 { value.0 }
}

// A place something is said of: the first is what the diagnostic is about.
struct Label { span: SourceSpan, text: Str, primary: Bool }

pub struct Diagnostic { severity: Severity, code: DiagnosticCode, message: Str, labels: [Label], notes: [Str], helps: [Str] }

impl Diagnostic {
    pub fn new(severity: Severity, code: DiagnosticCode, message: Str) -> Self {
        Self { severity: severity, code: code, message: message, labels: [], notes: [], helps: [] }
    }
    pub fn primary(value: &mut Self, span: SourceSpan, label: Str) {
        value.labels = push(replace(&mut value.labels, []), Label { span: span, text: label, primary: true });
    }
    pub fn secondary(value: &mut Self, span: SourceSpan, label: Str) {
        value.labels = push(replace(&mut value.labels, []), Label { span: span, text: label, primary: false });
    }
    pub fn note(value: &mut Self, text: Str) { value.notes = push(replace(&mut value.notes, []), text); }
    pub fn help(value: &mut Self, text: Str) { value.helps = push(replace(&mut value.helps, []), text); }
    pub fn is_error(value: &Self) -> Bool { rank(&value.severity) == 0 }
    pub fn code(value: &Self) -> u32 { value.code.0 }
    pub fn message(value: &Self) -> Str { value.message }
}

// Errors first.
fn rank(s: &Severity) -> Int { match(s) { &Severity::Error => 0, &Severity::Warning => 1, &Severity::Note => 2 } }
fn word(s: &Severity) -> Str { match(s) { &Severity::Error => "error", &Severity::Warning => "warning", &Severity::Note => "note" } }

// Where a diagnostic is put among others: by the text its first primary
// place is in, then how far in, then how bad, then its code. One with no
// place comes after those that have one.
fn first_place(labels: &[Label], i: Int) -> (Int, Int) {
    match(element(labels, i)) {
        None => (4294967296, 0),
        Some(label) => if(label.primary) { (int(SourceId::to_u32(label.span.source)), label.span.start) } else { first_place(labels, i + 1) }
    }
}
fn comes_before(a: &Diagnostic, b: &Diagnostic) -> Bool {
    let pa = first_place(&a.labels, 0);
    let pb = first_place(&b.labels, 0);
    if(pa.0 != pb.0) { pa.0 < pb.0 } else {
        if(pa.1 != pb.1) { pa.1 < pb.1 } else {
            if(rank(&a.severity) != rank(&b.severity)) { rank(&a.severity) < rank(&b.severity) } else { int(a.code.0) < int(b.code.0) }
        }
    }
}

// Diagnostics up to a limit: one more is given back, not lost.
pub struct DiagnosticBag { items: [Diagnostic], limit: Int, errors: Int }

impl DiagnosticBag {
    pub fn new(limit: Int) -> Self { Self { items: [], limit: limit, errors: 0 } }
    pub fn push(value: &mut Self, diagnostic: Diagnostic) -> Result<(), Diagnostic> {
        if(len_at(&value.items) >= value.limit) { Err(diagnostic) } else {
            value.errors = value.errors + (if(Diagnostic::is_error(&diagnostic)) { 1 } else { 0 });
            push_at(&mut value.items, diagnostic);
            Ok(())
        }
    }
    pub fn len(value: &Self) -> Int { len_at(&value.items) }
    pub fn has_errors(value: &Self) -> Bool { value.errors > 0 }
    // Every diagnostic, in the order above; those the order does not tell
    // apart stay as they were pushed.
    pub fn into_vec(value: Self) -> [Diagnostic] {
        match(value) { DiagnosticBag { items, limit, errors } => in_order(items, []) }
    }
}

// Each put where it belongs among those already placed.
fn in_order(left: [Diagnostic], placed: [Diagnostic]) -> [Diagnostic] {
    match(pop_first(left)) {
        None => placed,
        Some((next, rest)) => in_order(rest, placed_with(placed, next))
    }
}
fn pop_first(items: [Diagnostic]) -> Option<(Diagnostic, [Diagnostic])> {
    let mut items = items;
    match(pop_at(&mut items)) {
        None => None,
        Some(last) =>
            // The last taken off, and what is left turned so that the first is next.
            match(pop_first(items)) {
                None => Some((last, [])),
                Some((first, rest)) => Some((first, push(rest, last)))
            }
    }
}
fn placed_with(placed: [Diagnostic], next: Diagnostic) -> [Diagnostic] {
    let mut placed = placed;
    match(pop_at(&mut placed)) {
        None => [next],
        Some(last) =>
            if(comes_before(&next, &last)) { push(placed_with(placed, next), last) }
            else { push(push(placed, last), next) }
    }
}

pub struct RenderOptions { pub maximum_notes: Int, pub maximum_bytes: Int }

// A place as `name:line:column`, both counted from one; a place that is in
// no text the map has, or not in it, is `<unknown>`.
fn place_text(span: &SourceSpan, sources: &SourceMap) -> Str {
    match(SourceMap::name(sources, span.source)) {
        None => "<unknown>",
        Some(name) => match(SourceMap::locate(sources, span.source, span.start)) {
            Err(_) => "<unknown>",
            Ok(at) => name ++ ":" ++ show(at.line + 1) ++ ":" ++ show(at.column_bytes + 1)
        }
    }
}

fn labels_text(labels: &[Label], sources: &SourceMap, i: Int, out: Str) -> Str {
    match(element(labels, i)) {
        None => out,
        Some(label) =>
            let arrow = if(label.primary) { "  --> " } else { "  ::: " };
            let said = if(label.text == "") { "" } else { ": " ++ label.text };
            labels_text(labels, sources, i + 1, out ++ arrow ++ place_text(&label.span, sources) ++ said ++ "\n")
    }
}

fn lines_text(kind: Str, lines: &[Str], i: Int, most: Int, out: Str) -> Str {
    match(element(lines, i)) {
        None => out,
        Some(text) =>
            if(i >= most) { out ++ "  (" ++ show(len_at(lines) - most) ++ " more)\n" }
            else { lines_text(kind, lines, i + 1, most, out ++ "  " ++ kind ++ ": " ++ *text ++ "\n") }
    }
}

// The diagnostic as text: its severity, code and message, each place, then
// its notes (as many as are allowed, and how many more there are) and what
// would help. Longer than is allowed, it is refused, not cut short.
pub fn render_diagnostic(value: &Diagnostic, sources: &SourceMap, options: RenderOptions) -> Result<Str, FormatError> {
    let head = word(&value.severity) ++ "[" ++ show(value.code.0) ++ "]: " ++ value.message ++ "\n";
    let places = labels_text(&value.labels, sources, 0, head);
    let noted = lines_text("note", &value.notes, 0, options.maximum_notes, places);
    let all = lines_text("help", &value.helps, 0, len_at(&value.helps), noted);
    if(len(utf8(all)) > options.maximum_bytes) { Err(FormatError::OutputLimit) } else { Ok(all) }
}
"#

private def timeText : String := r#"// Time as amounts and moments, as the library specification has them (29.3).
// The machine's clock is `Clock`, the host's effect: nanoseconds as numbers.
// What is here does nothing to the machine: a test answers `Clock` itself
// and builds moments with `Instant::at`.

pub use std::host::Clock;
use std::cmp::{Ordering};

pub enum TimeError { Overflow, BeforeOrigin, DifferentClock, Unsupported }

// So many seconds and, less than a second, so many nanoseconds.
pub struct Duration { seconds: u64, nanos: u32 }

fn wide(n: u64) -> u128 { to(n) }

impl Duration {
    pub fn zero() -> Self { Self { seconds: 0u64, nanos: 0u32 } }
    // A second or more of nanoseconds is refused: it is not carried over.
    pub fn from_parts(seconds: u64, nanos: u32) -> Result<Self, TimeError> {
        if(nanos < 1000000000u32) { Ok(Self { seconds: seconds, nanos: nanos }) } else { Err(TimeError::Overflow) }
    }
    pub fn from_nanos(nanos: Int) -> Result<Self, TimeError> {
        if(nanos < 0) { Err(TimeError::BeforeOrigin) }
        else { Ok(Self { seconds: to(nanos / 1000000000), nanos: to(nanos % 1000000000) }) }
    }
    pub fn seconds(value: Self) -> u64 { value.seconds }
    pub fn subsec_nanos(value: Self) -> u32 { value.nanos }
    pub fn checked_add(left: Self, right: Self) -> Option<Self> {
        let nanos = int(left.nanos) + int(right.nanos);
        let carry = if(nanos >= 1000000000) { 1 } else { 0 };
        let more: u128 = to(carry);
        let seconds = wide(left.seconds) + wide(right.seconds) + more;
        if(seconds > 18446744073709551615u128) { None }
        else { Some(Self { seconds: to(seconds), nanos: to(nanos - carry * 1000000000) }) }
    }
    pub fn checked_sub(left: Self, right: Self) -> Option<Self> {
        let borrow = if(int(left.nanos) < int(right.nanos)) { 1 } else { 0 };
        let nanos = int(left.nanos) + borrow * 1000000000 - int(right.nanos);
        let less: u128 = to(borrow);
        let need = wide(right.seconds) + less;
        if(wide(left.seconds) < need) { None }
        else { Some(Self { seconds: to(wide(left.seconds) - need), nanos: to(nanos) }) }
    }
    pub fn compare(left: Self, right: Self) -> Ordering {
        if(left.seconds < right.seconds) { Ordering::Less } else {
            if(right.seconds < left.seconds) { Ordering::Greater } else {
                if(left.nanos < right.nanos) { Ordering::Less } else {
                    if(right.nanos < left.nanos) { Ordering::Greater } else { Ordering::Equal }
                }
            }
        }
    }
}

// A moment on one clock: so long after that clock began. Moments on
// different clocks are not compared or taken from one another.
pub struct Instant { clock: u32, since: Duration }

impl Instant {
    // For whoever answers `Clock`: the moment so long after clock `clock` began.
    pub fn at(clock: u32, since: Duration) -> Self { Self { clock: clock, since: since } }
    pub fn checked_add(value: Self, duration: Duration) -> Result<Self, TimeError> {
        match(Duration::checked_add(value.since, duration)) {
            Some(since) => Ok(Self { clock: value.clock, since: since }),
            None => Err(TimeError::Overflow)
        }
    }
    pub fn duration_since(value: Self, earlier: Self) -> Result<Duration, TimeError> {
        if(value.clock != earlier.clock) { Err(TimeError::DifferentClock) } else {
            match(Duration::checked_sub(value.since, earlier.since)) {
                Some(between) => Ok(between),
                None => Err(TimeError::BeforeOrigin)
            }
        }
    }
    pub fn compare(left: Self, right: Self) -> Result<Ordering, TimeError> {
        if(left.clock != right.clock) { Err(TimeError::DifferentClock) }
        else { Ok(Duration::compare(left.since, right.since)) }
    }
}

// A moment by the calendar's clock, which can be set back: so long after
// its origin.
pub struct SystemTime { since: Duration }

impl SystemTime {
    pub fn from_origin(since: Duration) -> Self { Self { since: since } }
    pub fn since_origin(value: Self) -> Duration { value.since }
}

// Now, by the machine's clock that only goes forward (clock 0) and by its
// calendar clock.
pub fn monotonic_now() -> Result<Instant, TimeError> / {Clock} {
    match(Duration::from_nanos(monotonic())) { Ok(since) => Ok(Instant::at(0u32, since)), Err(e) => Err(e) }
}
pub fn system_now() -> Result<SystemTime, TimeError> / {Clock} {
    match(Duration::from_nanos(now())) { Ok(since) => Ok(SystemTime::from_origin(since)), Err(e) => Err(e) }
}
"#

private def randomText : String := r#"// Chance, as the library specification has it (29.4): bytes from the machine
// through `Entropy`, the host's effect, and a generator that gives the same
// numbers from the same seed.
//
// A source gives the bytes it was asked for as an array, or fails: there is
// no array half filled.

pub use std::host::Entropy;
use std::host::{IoError};

pub enum RandomError { Exhausted, InvalidRange, Unsupported, Host(IoError) }

pub trait RandomSource {
    type Effects: EffectRow;
    // So many bytes, all of them, or why not.
    fn fill(&mut Self, Int) -> Result<[u8], RandomError> / { | Self::Effects };
}

// The machine's own chance, where the program has been given `Entropy`.
pub struct HostEntropy;

impl RandomSource for HostEntropy {
    type Effects = {Entropy};
    fn fill(source, count) {
        match(random_bytes(count)) { Ok(bytes) => Ok(bytes), Err(e) => Err(RandomError::Host(e)) }
    }
}

// xoshiro256**, its four words taken from the seed's thirty-two bytes, the
// least byte of each first. A seed of nothing but zeros stands for the
// words 1, 2, 3, 4: the generator cannot leave a state of all zeros.
// Not for secrets.
pub struct SeededRng { a: u64, b: u64, c: u64, d: u64 }

fn wide(n: u64) -> u128 { to(n) }
fn times(x: u64, k: u64) -> u64 { to(wide(x) * wide(k) % 18446744073709551616u128) }
// (A shift that would lose bits goes wrong, as other arithmetic does: the
// bits that would be lost are taken off first.)
fn shl_wrap(x: u64, k: Int) -> u64 { shl(bit_and(x, shr(18446744073709551615u64, k)), k) }
fn rotl(x: u64, k: Int) -> u64 { bit_or(shl_wrap(x, k), shr(x, 64 - k)) }
fn word(bytes: &[u8], at: Int, i: Int, sofar: u64) -> u64 {
    if(i < 0) { sofar } else {
        let b: u64 = match(element(bytes, at + i)) { Some(b) => to(*b), None => 0u64 };
        word(bytes, at, i - 1, bit_or(shl(sofar, 8), b))
    }
}

impl SeededRng {
    // From thirty-two bytes; fewer are as if the rest were zeros.
    pub fn from_seed(seed: [u8]) -> Self {
        let a = word(&seed, 0, 7, 0u64);
        let b = word(&seed, 8, 7, 0u64);
        let c = word(&seed, 16, 7, 0u64);
        let d = word(&seed, 24, 7, 0u64);
        if(bit_or(bit_or(a, b), bit_or(c, d)) == 0u64) { Self { a: 1u64, b: 2u64, c: 3u64, d: 4u64 } }
        else { Self { a: a, b: b, c: c, d: d } }
    }
    // Which generator this is: a release that depends on its numbers says this with its seed.
    pub fn algorithm_version() -> u32 { 1u32 }
    pub fn next_u64(value: &mut Self) -> u64 {
        let out = times(rotl(times(value.b, 5u64), 7), 9u64);
        let t = shl_wrap(value.b, 17);
        let c = bit_xor(value.c, value.a);
        let d = bit_xor(value.d, value.b);
        let b = bit_xor(value.b, c);
        let a = bit_xor(value.a, d);
        value.a = a;
        value.b = b;
        value.c = bit_xor(c, t);
        value.d = rotl(d, 45);
        out
    }
}

fn le_bytes(n: u64, count: Int, out: [u8]) -> [u8] {
    if(count == 0) { out } else { le_bytes(shr(n, 8), count - 1, push(out, to(bit_and(n, 255u64)))) }
}
fn seeded_bytes(rng: &mut SeededRng, count: Int, out: [u8]) -> [u8] {
    if(count <= 0) { out } else {
        let most = if(count < 8) { count } else { 8 };
        let next = SeededRng::next_u64(rng);
        seeded_bytes(rng, count - most, le_bytes(next, most, out))
    }
}

impl RandomSource for SeededRng {
    type Effects = {};
    fn fill(source, count) { Ok(seeded_bytes(source, count, [])) }
}

// Sixty-four bits: eight bytes of the source, the least first.
pub fn random_u64<R: RandomSource>(source: &mut R) -> Result<u64, RandomError> / { | <R as RandomSource>::Effects } {
    match(fill(source, 8)) {
        Err(e) => Err(e),
        Ok(bytes) => if(len(bytes) == 8) { Ok(word(&bytes, 0, 7, 0u64)) } else { Err(RandomError::Exhausted) }
    }
}

// A number below `exclusive`, each as likely as any other: what falls in the
// part of the sixty-four bits that does not divide evenly is asked for again.
pub fn random_below<R: RandomSource>(source: &mut R, exclusive: u64) -> Result<u64, RandomError> / { | <R as RandomSource>::Effects } {
    if(exclusive == 0u64) { Err(RandomError::InvalidRange) } else {
        let spare: u64 = to(18446744073709551616u128 % wide(exclusive));
        below(source, exclusive, spare)
    }
}
fn below<R: RandomSource>(source: &mut R, exclusive: u64, spare: u64) -> Result<u64, RandomError> / { | <R as RandomSource>::Effects } {
    match(random_u64(source)) {
        Err(e) => Err(e),
        Ok(v) => if(v < spare) { below(source, exclusive, spare) } else { Ok(v % exclusive) }
    }
}
"#

private def cText : String := r#"// What C has: its memory, and texts as it writes them. Everything here is
// unsafe: an address is whatever a program says it is.

use std::slice::{Slice};
use std::value::{Rejected};

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

// How much memory, and how it has to be placed: the library specification's
// `Layout` (22.1). Sizes are whole numbers here.
pub struct Layout { size: Int, align: Int }
pub enum LayoutError { ZeroAlignment, NonPowerOfTwoAlignment, SizeOverflow }
pub enum AllocError { Exhausted, UnsupportedAlignment, LimitExceeded }

fn power_of_two(n: Int) -> Bool {
    if(n == 1) { true } else { if(n % 2 == 0) { power_of_two(n / 2) } else { false } }
}

// The next multiple of `align` at or after `n`.
fn rounded(n: Int, align: Int) -> Int { ((n + align - 1) / align) * align }

impl Layout {
    pub fn from_size_align(size: Int, align: Int) -> Result<Self, LayoutError> {
        if(align <= 0) { Err(ZeroAlignment) } else {
            if(power_of_two(align)) {
                if(size < 0) { Err(SizeOverflow) } else { Ok(Self { size: size, align: align }) }
            } else { Err(NonPowerOfTwoAlignment) }
        }
    }
    pub fn size(value: &Self) -> Int { value.size }
    pub fn align(value: &Self) -> Int { value.align }
    // This and another after it: the layout of both, and where the other
    // starts.
    pub fn extend(value: Self, other: Self) -> Result<(Self, Int), LayoutError> {
        let at = rounded(value.size, other.align);
        let align = if(value.align > other.align) { value.align } else { other.align };
        Ok((Self { size: at + other.size, align: align }, at))
    }
    // Rounded up to a multiple of its alignment.
    pub fn padded(value: Self) -> Result<Self, LayoutError> {
        Ok(Self { size: rounded(value.size, value.align), align: value.align })
    }
}

extern "C" {
    fn aligned_alloc(align: usize, size: usize) -> usize;
}

// Memory that is this value's to give back. It has to be: an `Allocation`
// cannot be let go, only given to `release` or to whatever takes it over.
pub struct Allocation { at: usize, layout: Layout }
impl Use<[1, 1]> for Allocation {}

pub fn allocate(layout: Layout) -> Result<Allocation, AllocError> {
    if(layout.align > 4096) { Err(UnsupportedAlignment) } else {
        // (C wants a size that is a multiple of the alignment, and not none.)
        let asked = rounded(if(layout.size == 0) { 1 } else { layout.size }, layout.align);
        let at = unsafe { aligned_alloc(usize(layout.align), usize(asked)) };
        if(at == 0usize) { Err(Exhausted) } else { Ok(Allocation { at: at, layout: layout }) }
    }
}

impl Allocation {
    pub fn layout(value: &Self) -> Layout { Layout { size: value.layout.size, align: value.layout.align } }
    // Where the memory is.
    pub fn as_ptr(value: &Self) -> usize { value.at }
    // The memory given back.
    pub fn release(value: Self) { match(value) { Allocation { at, layout } => unsafe { free(at) } } }
}

// C's own truth value: a byte that is nothing or one. Not `Bool`.
pub struct c_bool(u8);
pub fn c_bool_from_bool(value: Bool) -> c_bool { c_bool(if(value) { 1u8 } else { 0u8 }) }
pub fn bool_from_c_bool(value: c_bool) -> Bool { value.0 != 0u8 }

// Addresses: the one that is nowhere, and one so many bytes on from another.
pub fn null() -> usize { 0usize }
pub fn ptr_is_null(at: usize) -> Bool { at == 0usize }
pub fn ptr_add(at: usize, count: Int) -> usize { at + usize(count) }

extern "C" {
    fn memset(at: usize, byte: i32, count: usize) -> usize;
    fn memmove(to: usize, from: usize, count: usize) -> usize;
    fn memcpy(to: usize, from: usize, count: usize) -> usize;
}

// So many bytes at an address made one byte.
pub unsafe fn ptr_write_bytes(at: usize, byte: u8, count: Int) { memset(at, to(byte), usize(count)); }
// So many bytes copied from one address to another; the two stretches may
// share bytes.
pub unsafe fn ptr_copy(from: usize, to_: usize, count: Int) { memmove(to_, from, usize(count)); }
// The same where they share none.
pub unsafe fn ptr_copy_nonoverlapping(from: usize, to_: usize, count: Int) { memcpy(to_, from, usize(count)); }

// Where a zero byte was found that should not be there.
pub struct NulError { pub position: Int }
pub enum CStrError { MissingTerminator, InteriorNul(NulError) }

// The first zero among some bytes from a place on.
fn first_zero<'a>(bytes: &Slice<'a, u8>, i: Int) -> Option<Int> {
    match(Slice::get(bytes, i)) {
        Some(b) => if(*b == 0u8) { Some(i) } else { tail first_zero(bytes, i + 1) },
        None => None
    }
}

fn zero_in(bytes: &[u8], i: Int) -> Option<Int> {
    match(element(bytes, i)) {
        Some(b) => if(*b == 0u8) { Some(i) } else { tail zero_in(bytes, i + 1) },
        None => None
    }
}

fn slice_bytes<'a>(bytes: &Slice<'a, u8>, i: Int, out: [u8]) -> [u8] {
    match(Slice::get(bytes, i)) { Some(b) => tail slice_bytes(bytes, i + 1, push(out, *b)), None => out }
}

// Bytes that end in a zero and have no other: a text as C reads one, looked
// at where it is.
pub struct CStr<'a> { bytes: Slice<'a, u8> }

impl<'a> CStr<'a> {
    pub fn from_bytes_with_nul(value: Slice<'a, u8>) -> Result<Self, CStrError> {
        match(first_zero(&value, 0)) {
            None => Err(CStrError::MissingTerminator),
            Some(at) =>
                if(at + 1 == Slice::len(&value)) { Ok(Self { bytes: value }) }
                else { Err(CStrError::InteriorNul(NulError { position: at })) }
        }
    }
    // The bytes without the zero, and with it.
    pub fn bytes(value: Self) -> Slice<'a, u8> {
        let all = value.bytes;
        match(Slice::sub(&all, 0, Slice::len(&all) - 1)) { Some(found) => found, None => all }
    }
    pub fn bytes_with_nul(value: Self) -> Slice<'a, u8> { value.bytes }
    pub fn len(value: &Self) -> Int { Slice::len(&value.bytes) - 1 }
    // The text, if the bytes are UTF-8.
    pub fn to_str(value: Self) -> Option<Str> {
        let found = CStr::bytes(value);
        std::text::from_utf8(slice_bytes(&found, 0, []))
    }
}

// The bytes C has at an address, up to its zero: copied out, the zero
// with them. Unsafe: the address has to be one where that many bytes can
// be read.
pub unsafe fn bytes_at(at: usize, maximum_length: Int) -> Result<[u8], CStrError> { until_zero(at, maximum_length, []) }
unsafe fn until_zero(at: usize, left: Int, out: [u8]) -> Result<[u8], CStrError> {
    if(left <= 0) { Err(CStrError::MissingTerminator) } else {
        let b = read_byte(at);
        if(b == 0u8) { Ok(push(out, b)) } else { tail until_zero(at + 1usize, left - 1, push(out, b)) }
    }
}

// A text for C in memory of its own: its bytes and a zero after them. It
// has to be given back, with `release` or by taking its bytes out.
pub struct CString { memory: Allocation, length: Int }

impl CString {
    // From bytes with no zero among them; with one, the bytes come back.
    pub fn from_vec(bytes: [u8]) -> Result<Self, Rejected<[u8], NulError>> {
        match(zero_in(&bytes, 0)) {
            Some(at) => Err(Rejected { value: bytes, error: NulError { position: at } }),
            None =>
                let n = len(bytes);
                match(Layout::from_size_align(n + 1, 1)) {
                    Err(_) => Err(Rejected { value: bytes, error: NulError { position: n } }),
                    Ok(layout) => match(allocate(layout)) {
                        Err(_) => Err(Rejected { value: bytes, error: NulError { position: n } }),
                        Ok(memory) =>
                            unsafe { write_bytes(Allocation::as_ptr(&memory), push(bytes, 0u8)) };
                            Ok(Self { memory: memory, length: n })
                    }
                }
        }
    }
    pub fn from_str(text: Str) -> Result<Self, NulError> {
        match(CString::from_vec(std::text::utf8(text))) { Ok(found) => Ok(found), Err(rejected) => Err(rejected.error) }
    }
    // Where C can read it, for as long as this is kept.
    pub fn as_ptr(value: &Self) -> usize { Allocation::as_ptr(&value.memory) }
    pub fn len(value: &Self) -> Int { value.length }
    pub fn release(value: Self) { match(value) { CString { memory, length: _ } => Allocation::release(memory) } }
    // Its bytes, without the zero and with it; the memory is given back.
    pub fn into_bytes(value: Self) -> [u8] {
        match(value) { CString { memory, length } =>
            let bytes = unsafe { read_bytes(Allocation::as_ptr(&memory), length) };
            Allocation::release(memory);
            bytes }
    }
    pub fn into_bytes_with_nul(value: Self) -> [u8] {
        match(value) { CString { memory, length } =>
            let bytes = unsafe { read_bytes(Allocation::as_ptr(&memory), length + 1) };
            Allocation::release(memory);
            bytes }
    }
}
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

/-- `std::tuple`: tuples and functions of any length through one form. What
is written for each length is written here, for up to twelve, so that what a
program writes is written once. -/
private def tupleText : String :=
  let names := ["A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L"]
  let tuple := fun (xs : List String) => match xs with
    | [] => "()"
    | [x] => s!"({x},)"
    | xs => s!"({", ".intercalate xs})"
  let nested := fun (xs : List String) => xs.foldr (fun x rest => s!"({x}, {rest})") "()"
  let part := fun (v : String) (k : Nat) => (List.range k).foldl (fun e _ => s!"({e}.1)") v ++ ".0"
  let one := fun (n : Nat) =>
    let ps := names.take n
    let generics := if ps.isEmpty then "" else s!"<{", ".intercalate ps}>"
    let places := List.range n
    s!"impl{generics} Tuple for {tuple ps} \{
    type Nested = {nested ps};
    fn nest(t) \{ {nested (places.map fun i => s!"t.{i}")} }
    fn flat(n) \{ {tuple (places.map (part "n"))} }
}
impl<{", ".intercalate (ps ++ ["R"])}> Callable for fn({", ".intercalate ps}) -> R \{
    type Args = {nested ps};
    type Output = R;
    fn call_with(f, args) \{ (*f)({", ".intercalate (places.map (part "args"))}) }
}
"
  r#"// Tuples and functions of any length, through one form: the tuple
// `(A, B, C)` as the pairs `(A, (B, (C, ())))`. What is written for `()` and
// for a pair `(First, Rest)` is then written for every length:
//
//     trait Total { fn total(Self) -> Int }
//     impl Total for () { fn total(nothing) { 0 } }
//     impl<Rest> Total for (Int, Rest) where Rest: Total { fn total(p) { p.0 + total(p.1) } }
//     total(nest((1, 2, 3)))
//
// Up to twelve.

// A tuple, and the pairs it is.
pub trait Tuple {
    type Nested;
    fn nest(Self) -> Nested
    fn flat(Nested) -> Self
}

// A function, by what it takes, as pairs, and what it gives.
pub trait Callable {
    type Args;
    type Output;
    fn call_with(&Self, Args) -> Output
}

// A function called with a tuple of what it takes: `apply(add, (3, 4))`.
pub fn apply<F, T, L, R>(f: F, args: T) -> R where T: Tuple<Nested = L>, F: Callable<Args = L, Output = R> {
    call_with(&f, nest(args))
}

// Two lists of pairs as one, the second after the first.
pub trait Concat<Other> {
    type Joined;
    fn concat(Self, Other) -> Joined
}
impl<Other> Concat<Other> for () {
    type Joined = Other;
    fn concat(nothing, other) { other }
}
impl<First, Rest, Other, J> Concat<Other> for (First, Rest) where Rest: Concat<Other, Joined = J> {
    type Joined = (First, J);
    fn concat(pair, other) { (pair.0, concat(pair.1, other)) }
}

// How many a list of pairs has.
pub trait Count { const COUNT: Int; }
impl Count for () { const COUNT: Int = 0; }
impl<First, Rest> Count for (First, Rest) where Rest: Count { const COUNT: Int = 1 + Rest::COUNT; }

"# ++ String.join ((List.range 13).map one)

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
   (["std", "stream"], streamText),
   (["std", "value"], valueText),
   (["std", "generator"], generatorText),
   (["std", "bytes"], bytesText),
   (["std", "error"], errorText),
   (["std", "index"], indexText),
   (["std", "budget"], budgetText),
   (["std", "parse"], parseText),
   (["std", "graph"], graphText),
   (["std", "source"], sourceText),
   (["std", "boxed"], boxedText),
   (["std", "task"], taskText),
   (["std", "path"], pathText),
   (["std", "future"], futureText),
   (["alloc", "boxed"], "pub use std::boxed::*;\n"),
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
   (["std", "time"], timeText),
   (["std", "random"], randomText),
   (["std", "tuple"], tupleText),
   (["std", "ffi"], "pub use std::c::*;\n"),
   (["core"], "pub mod option;\npub mod result;\npub mod cmp;\npub mod num;\npub mod char;\npub mod iter;\npub mod slice;\npub mod hash;\npub mod value;\n"),
   (["core", "value"], "pub use std::value::*;\n"),
   (["core", "option"], "pub use std::option::*;\n"),
   (["core", "result"], "pub use std::result::*;\n"),
   (["core", "cmp"], "pub use std::cmp::*;\n"),
   (["core", "num"], "pub use std::int::*;\n"),
   (["core", "char"], "pub use std::char::*;\n"),
   (["core", "iter"], "pub use std::iterator::*;\n"),
   (["core", "slice"], "pub use std::slice::*;\n"),
   (["core", "hash"], "pub use std::hash::*;\n"),
   (["alloc"], "pub mod vec;\npub mod string;\npub mod collections;\npub mod fmt;\npub mod boxed;\npub mod fingerprint;\n"),
   (["alloc", "fmt"], "pub use std::fmt::*;\n"),
   (["alloc", "vec"], "pub use std::vec::*;\n"),
   (["alloc", "string"], "pub use std::text::*;\n"),
   (["alloc", "collections"], "pub use std::collections::*;\npub mod map;\npub mod set;\n"),
   (["alloc", "collections", "map"], "pub use std::map::*;\n"),
   (["alloc", "collections", "set"], "pub use std::set::*;\n"),
   -- (A text added to the library goes last: the places of those before it
   -- are in what is compiled of every program that names the library.)
   (["std", "fingerprint"], fingerprintText),
   (["std", "diagnostic"], diagnosticText),
   (["alloc", "fingerprint"], "pub use std::fingerprint::*;\n")]

end Glorious.Std
