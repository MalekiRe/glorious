/-!
# The prelude

Written in Glorious. None of these names is known to the compiler: conditionals,
matching, boolean operators, arithmetic operators and loops are ordinary
functions over the kernel.
-/

namespace Glorious.Prelude

def source : String := r#"
enum Result { Ok(value), Err(error) }

// Truth is success. `Option<T>` is `Result<T, ()>` and `Bool` is `Option<()>`.
let Some = Ok;
let None = Err(());
let true = Ok(());
let false = Err(());

// Matching is applying a pattern callable.
fn match(subject, arms) { tail arms(subject) }

// `if` maps success through its body and keeps failure.
fn if(condition, body) {
    match(condition) {
        Ok(_) => Ok(body()),
        Err(error) => Err(error)
    }
}

// `else` unwraps success and recovers from failure.
infixr 1 else
fn else(value, fallback) {
    match(value) {
        Ok(result) => result,
        Err(_) => tail fallback()
    }
}

// The right operands of `and` and `or` are callables, run only when needed.
infixr 3 and
fn and(left, right) {
    match(left) {
        Ok(_) => tail right(),
        Err(error) => Err(error)
    }
}

infixr 2 or
fn or(left, right) {
    match(left) {
        Ok(value) => Ok(value),
        Err(_) => tail right()
    }
}

prefix 8 not
fn not(value) {
    match(value) {
        Ok(payload) => Err(payload),
        Err(payload) => Ok(payload)
    }
}

infixl 6 +
infixl 6 -
infixl 7 *
fn +(a, b) { int_add(a, b) }
fn -(a, b) { int_sub(a, b) }
fn *(a, b) { int_mul(a, b) }

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

// The outside world.
fn print(value) { host_write(value) }

fn read() {
    match(host_read()) {
        (1, value) => Some(value),
        _ => None
    }
}

// Loops: a handler for `break` and `continue` around a body run again by a tail call.
effect LoopControl {
    break(value) -> !,
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
        if(condition()) { body() } else { break(()) }
    }
}
"#

end Glorious.Prelude
