# Explicit conversions

`as` is an ordinary generic standard-library function, not an operator,
keyword, implicit coercion, or compiler intrinsic:

```glorious
pub trait As<T> { cast(value: Self) -> T; }
pub fn as<T, S>(value: S) -> T where S: As<T> { As<T>::cast(value) }

fn sample() -> f32 { as(1) }
fn explicit() -> f32 { as<f32>(1) }
```

The target is the first type parameter. A direct function application may
supply a prefix of its generic arguments and infer omitted trailing **type**
parameters from the arguments and expected result. This rule applies to all
ordinary functions, including qualified calls, not just `as`. Omitted trailing
lifetime, effect-row, and const parameters are not part of this extension.
Explicit arguments remain constraints; inference cannot replace them.

`as(1)` receives target evidence from a return type, a typed argument position,
or a record field. With no target evidence, `let value = as(1)` is ambiguous
and rejected. Literal source types retain their usual defaults (`i64`, `f64`);
the conversion target does not retroactively change the input's type.
There is no search for multi-step conversion paths and no implicit conversion
on assignment or at ordinary calls.
An overloaded operator does not necessarily determine a unique target; use
an explicit target when a conversion inside an operator expression is ambiguous.

## Implementing conversions

```glorious
pub struct Count { value: i64 }
pub impl As<i64> for Count {
    cast(value: Count) -> i64 { value.value }
}
```

`As` is a normal, unsealed trait, governed by ordinary coherence, privacy,
ownership, and effect checking. It has no outward effects. A non-duplicable
input is moved, not secretly copied or borrowed. Implementations cannot forge
references, extend lifetimes, or access private fields through this API.
The existing orphan rule requires the trait or nominal self type to be local;
a local target argument alone does not authorize a foreign-self impl.

Its contract is an explicit conversion with a defined result for every valid
input, potentially losing information. This is a library contract, not a
compiler proof of termination, absence of traps, losslessness, or constant
cost. Do not use an invalid input as a reason to trap in `cast`; conversions
requiring validation belong in checked APIs returning `Option`/`Result`.
No safety or optimizer assumptions are granted by implementing this trait.

The blanket identity implementation `As<T> for T` transfers the value unchanged.
Do not add overlapping blanket conversions: the language has no specialization.

## Built-in numeric policy

All 196 pairs among the twelve integer types and `f32`/`f64` are supported.
`usize` and `isize` retain the VM's fixed 64-bit width.

| Conversion | Policy |
| --- | --- |
| Integer to integer | Value modulo `2^N`, interpreted with the target signedness; widening sign-extends signed inputs and zero-extends unsigned inputs. |
| Integer to float | Direct rounding to the destination precision, nearest with ties to even; overflow becomes signed infinity. |
| `f32` to `f64` | Exact widening of finite values; preserve infinities and signed zero, use canonical NaN. |
| `f64` to `f32` | Nearest with ties to even; overflow becomes signed infinity; preserve signed zero and canonicalize NaN. |
| Float to integer | Truncate toward zero; saturate at target bounds; NaN becomes zero. |

For example, `as<u8>(256)` is zero, `as<u8>(-1)` is 255, and
`as<i64>(3.9)` is 3. This is numeric conversion, not a floating bit cast.
Bit representations remain separately named operations.

Character support includes `char -> u32` (Unicode code point) and `u8 -> char`
(the corresponding code point, not UTF-8 decoding). General `u32 -> char`
still needs the checked character constructor because not every value is a
Unicode scalar. Other pairs require a deliberate trait implementation; there
are no automatic record, enum-discriminant, pointer, or truthiness casts.

This adds a lossy float-to-integer API alongside the existing checked functions;
it supersedes the older requirement that *every* public float-to-integer
conversion must be checked. The existing checked APIs keep their behavior.
Saturation and NaN policy live in source, above the existing checked VM leaves.
No conversion opcode or artifact schema is added for `as`.
