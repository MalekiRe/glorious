# Grandiose Standard Library Contract

The [September 5 unsafe/native-ABI amendment](unsafe-memory-and-native-abi.md)
supersedes this document's exclusion of raw pointers and unsafe library code.
Specialized collection/text/hash leaves below describe the compatibility
bootstrap, not the final source-owned library boundary. Safe-only guests may
use safe exports of explicitly trusted native library implementations.

Status: normative design for the generation-1 standard library and source-bundle
model. The standard library is Grandiose source built over the finite,
manifest-bound machine-type, primitive, and host-import leaves specified here.
The compiler must not recognize its control names or operator spellings.

The result-based control model is adapted from Justin Pombrio's
[“Imagining a Language without Booleans”](https://justinpombrio.net/2025/09/22/imagining-a-language-without-booleans.html).
Grandiose adopts the semantic ideas, not the post's hypothetical `T ? E` syntax.
There is no `?` type or propagation operator in generation 1.

## 1. Result, option, and truth

The foundational sum is the ordinary nominal type:

```text
Result<T, E> = Ok(T) | Err(E)
```

The standard library exposes these equations:

```text
type Option<T> = Result<T, ()>

Option::Some(value) = Result::Ok(value)
None                = Result::Err(())

type Bool = Option<()>
true      = Option::Some(())
false     = None
```

These are source-defined aliases and immutable bindings. `Bool`, `true`,
`false`, `Option`, `Option::Some`, and `None` are not compiler-known types,
literals, or keywords. `Option::Some` is the standard library's alias-qualified
constructor binding for `Result::Ok`; it does not introduce a second option
representation.

Success is truth and failure is falsehood:

```text
true  = Result::Ok(())
false = Result::Err(())
```

Comparisons and predicates exposed by the standard library return `Bool`.
Machine comparison primitives return a `u32` discriminator, and ordinary source
wrappers convert zero to `false` and one to `true`.

## 2. General operator model

The control operators work on general `Result<A, E>` values, not only `Bool` or
`Option`. This preserves useful success and error payloads.

Every right-hand computation below is lazy. It is represented by an ordinary
zero-argument callable selected through an `Fn` constraint. The parser and
compiler do not contain operator-specific laziness rules.

Evaluation is left to right:

1. evaluate the left operand exactly once;
2. inspect its `Result` variant through ordinary source-defined matching;
3. evaluate the lazy operand only in the rule that selects it;
4. propagate or construct the stated result.

### 2.1 Conditional mapping: `if`

Conceptual type:

```text
if : (Result<A, E>, lazy B) -> Result<B, E>
```

Rules:

```text
if(Ok(value), body)  = Ok(body())
if(Err(error), body) = Err(error)
```

The successful condition payload is discarded, so the general definition
requires `A: Use<[0,0]>`. The error is preserved without requiring it to be unit.
When the condition is `Bool`, `A` is unit.

An `if` without an `else` is therefore meaningful: it produces a `Result` rather
than silently producing unit on the unsuccessful path.

### 2.2 Lazy defaulting: `else`

Conceptual type:

```text
else : (Result<A, E>, lazy A) -> A
```

Rules:

```text
Ok(value)  else fallback = value
Err(error) else fallback = fallback()
```

The failure payload is discarded when the fallback is selected, so the general
definition requires `E: Use<[0,0]>`.

`else` is right associative. Consequently a chain of conditional/defaulting
operations groups from the right and supports ordinary `else if` behavior without
a compiler `ElseIf` node.

### 2.3 Success sequencing: `and`

Conceptual type:

```text
and : (Result<A, E>, lazy Result<B, E>) -> Result<B, E>
```

Rules:

```text
Ok(value)  and next = next()
Err(error) and next = Err(error)
```

The first success payload is discarded, so the general definition requires
`A: Use<[0,0]>`. The right side is evaluated only after success. This is the
result-valued counterpart of short-circuit conjunction.

### 2.4 Failure recovery: `or`

Conceptual type:

```text
or : (Result<A, E>, lazy Result<A, F>) -> Result<A, F>
```

Rules:

```text
Ok(value)  or alternative = Ok(value)
Err(error) or alternative = alternative()
```

The first failure payload is discarded, so the general definition requires
`E: Use<[0,0]>`. The right side is evaluated only after failure. Its error type
may differ from the first error type.

### 2.5 Success/failure exchange: `not`

Conceptual type:

```text
not : Result<A, E> -> Result<E, A>
```

Rules:

```text
not Ok(value)  = Err(value)
not Err(error) = Ok(error)
```

`not` exchanges the variants and preserves both payloads, so it needs no discard
bound. Applied to `Bool`, it behaves as ordinary logical negation.

## 3. Fixity and grouping

The standard library declares the fixities. The required relative order, from
tightest to loosest, is:

```text
prefix not
and
or
else
```

`and` and `or` are left associative. `else` is right associative. `or` binds
more tightly than `else`, allowing a chain of result-producing alternatives to
be defaulted once at the end. Function application and ordinary arithmetic or
comparison operators retain their separately declared tighter precedences.

The operator names are ordinary bindings. Renaming or replacing a binding changes
only source resolution; it does not select a compiler code path.

## 4. Pattern refinements

Core `is` integrates with the same result-based control model. A successful test
carries `Bindings<P_yes>` and a failed test carries `Bindings<P_no>` in an
ordinary result-like `Test` value. Standard-library control functions select the
appropriate lazy body, and expected-type elaboration supplies its hidden binding
pack.

Therefore a name introduced by a positive pattern is available only inside the
positive lazy body. The subject is evaluated once, and a negative branch cannot
observe a positive binder.

The standard library may provide convenient matching, filtering, searching, and
validation combinators that return `Result` or `Option`, allowing them to compose
with `if`, `and`, `or`, and `else`. This does not add compiler-known pattern or
loop nodes.

Pattern ownership has three explicit outcomes. Binding the whole subject or a
payload transfers it to a new owner. Deconstructing a struct or enum is an owned
use only when the definition is visible and the compiler proves the pattern set
exhaustive for the complete layout. `_`, `..`, omitted fields, and
literal-only/non-binding payload patterns request zero-use destruction of the
unbound remainder and therefore require `Use<[0,0]>` for that remainder. A
private, opaque, or non-exhaustive value may be transferred whole, but library
matching helpers must not claim to deconstruct it.

## 5. Other source-defined control

The standard library reconstructs conventional control exclusively from the
language core:

- matching uses a private label-indexed terminal case effect;
- early return invokes the named callable's implicit `@function` label;
- result propagation may use `try(value, @function)`, whose label-generic
  specialization is control-inlined to a direct `LEAVE`;
- loops use tail calls plus a fresh label-indexed loop-control effect;
- breaking with a value may produce `Option<T>`/`Result<T,E>`, so a subsequent
  `else` supplies a lazy default;
- generators and tasks own resumptions, while `yield` and `await` are ordinary
  effect-performing functions;
- failure is an ordinary terminal effect and not a compiler control node.

Names such as `if`, `else`, `and`, `or`, `not`, `match`, `loop`, `return`,
`break`, `continue`, `yield`, `await`, and `fail` remain standard-library names.

## 6. Ownership behavior

Result operators must not hide ownership loss:

| Operator path | Discarded payload | Required evidence |
|---|---|---|
| successful `if` | condition success `A` | `A: Use<[0,0]>` |
| failed `else` | error `E` | `E: Use<[0,0]>` |
| successful `and` | first success `A` | `A: Use<[0,0]>` |
| failed `or` | first error `E` | `E: Use<[0,0]>` |
| `not` | none | none beyond construction |

When a payload cannot be discarded, callers must transfer, transform, return, or
exhaustively deconstruct it. Destruction is a zero-use outcome and requires
`Use<[0,0]>`; it cannot satisfy a positive lower bound. The standard library
must not use an erased-unit shortcut, wildcard, omitted field, or helper call to
bypass `Use`.

Lazy operands participate in ordinary `Fn` and `RunsIn` checking. A complete
operator chain keeps its shared environment open until every lazy alternative
has contributed captures, quantities, effects, lifetimes, and post-state.

Custom `Drop` remains a hook, not an owned use. It is available only for a type
that proves `Use<[0,0]>`, and it runs only after a zero-use destruction path has
already been shown legal. It cannot make a wildcard, omitted payload, failed
alternative, or abandoned iterator legal. `abort` is the deliberate exception:
it terminates the worker without transfer, destruction, hooks, or cleanup.

## 7. Bootstrap library profile

The generation-1 standard library is deliberately a compiler-building library,
not a large application framework. It must be sufficient to implement the whole
self-hosted compiler without private VM conveniences. The required profile has
five layers:

1. direct, typed wrappers over frozen VM scalars, arrays, and primitives;
2. `Result`, `Option`, result-based control, and ownership traits;
3. text, byte, collection, hashing, sorting, and formatting utilities;
4. compiler-oriented arenas, typed indices, interners, bit sets, work queues,
   and binary readers/writers;
5. capability-checked process argument, file, and diagnostic effects.

Only layer 1 may invoke bytecode primitives or manifest-bound host imports.
Everything above it is ordinary Grandiose code and must also run under the
bootstrap interpreter. Public names such as `String::len` are resolved normally;
they are not bytecode instruction
spellings or compiler language items.

The consuming `array.finish_drained(Array<T>) -> ()` primitive is an internal,
manifest-bound layer-1 leaf. Its identity cannot be created by source spelling,
aliased into a public disposal function, or invoked by code above layer 1. The
leaf returns normally only after the VM confirms that every array slot is empty;
otherwise it raises a catchless primitive fault without destroying resident
elements. Layer-1 collection code may use it only to release a shell whose
elements have all been transferred. It is neither general disposal nor an
`abort` substitute, and it does not weaken the `T: Use<[0,0]>` requirement for
ordinary array destruction.

The distribution manifest freezes the opaque `Array` machine constructor at
identity `0x21`. Its trusted source bindings, together with the immutable
`char`/`Text`/`Bytes` leaves, mirror the frozen primitive identities. These names are
internal layer-1 declarations, not public APIs, and both their declarations and
their call sites require the trusted standard-library source domain:

| Identity | Trusted source binding | Primitive |
|---:|---|---|
| `0x0030` | `__g1_char_from_u32_checked` | `CharFromU32Checked` |
| `0x0031` | `__g1_char_to_u32` | `CharToU32` |
| `0x0040` | `__g1_text_byte_len` | `TextByteLen` |
| `0x0041` | `__g1_text_concat` | `TextConcat` |
| `0x0042` | `__g1_text_eq` | `TextEq` |
| `0x0043` | `__g1_text_from_utf8_checked` | `TextFromUtf8Checked` |
| `0x0044` | `__g1_text_as_bytes` | `TextAsBytes` |
| `0x0050` | `__g1_bytes_len` | `BytesLen` |
| `0x0051` | `__g1_bytes_concat` | `BytesConcat` |
| `0x0052` | `__g1_bytes_get` | `BytesGet` |
| `0x0053` | `__g1_bytes_slice` | `BytesSlice` |
| `0x0054` | `__g1_bytes_from_array_move` | `BytesFromArrayMove` |
| `0x0055` | `__g1_bytes_to_array` | `BytesToArray` |
| `0x0056` | `__g1_bytes_utf8_valid_up_to` | `BytesUtf8ValidUpTo` |
| `0x0060` | `__g1_array_new` | `ArrayNew` |
| `0x0061` | `__g1_array_len` | `ArrayLen` |
| `0x0062` | `__g1_array_get_copy` | `ArrayGetCopy` |
| `0x0063` | `__g1_array_get_move` | `ArrayGetMove` |
| `0x0064` | `__g1_array_get_borrow_shared` | `ArrayGetBorrowShared` |
| `0x0065` | `__g1_array_get_borrow_unique` | `ArrayGetBorrowUnique` |
| `0x0066` | `__g1_array_set_move` | `ArraySetMove` |
| `0x0067` | `__g1_array_empty` | `ArrayEmpty` |
| `0x0068` | `__g1_array_push_move` | `ArrayPushMove` |
| `0x0069` | `__g1_array_pop_move` | `ArrayPopMove` |
| `0x006a` | `__g1_array_capacity` | `ArrayCapacity` |
| `0x006b` | `__g1_array_reserve` | `ArrayReserve` |
| `0x006c` | `__g1_array_finish_drained` | `ArrayFinishDrained` |

Custom conformance manifests may bind arbitrary names and declaration IDs; this
table is the canonical distribution mapping only.

The bootstrap profile is normative: stage 1 must not rely on a helper that is
available only in the Rust VM or existing interpreter. Convenience APIs beyond
this profile may be added later without expanding the language or VM core.
The size target is 6,000–9,000 nonblank, noncomment Grandiose lines. It includes
the explicit all-width checked-conversion matrix, runtime/control and formatting
wrappers, deterministic collections, diagnostic/source-map support, and the
compiler-building toolkit. This is a review budget: repetitive APIs should be
generated or expressed generically where that preserves the canonical source
distribution, but conformance is not removed to meet the count.

### 7.1 Scalar and primitive surface

The standard library exposes the source scalar types `()`, `!`, `u8`, `u16`,
`u32`, `u64`, `u128`, `i8`, `i16`, `i32`, `i64`, `i128`, `usize`, `isize`,
`f32`, `f64`, and `char`. Bytecode calls the uninhabited `!` type `NEVER` in
metadata; `Never` is not a separate source binding. Bytecode `usize` and `isize`
are always 64-bit.

The finite manifest additionally supplies the immutable UTF-8 `Text`, immutable
octet `Bytes`, and growable `Array<T>` machine types. `String` is the public alias
of `Text`; `Bytes` is public directly; and `Array<T>` is kept behind the public
dense `Vec<T>` interface except inside layer 1. These identities are trusted
machine types, unlike all source-defined collection and control types.

For each numeric type it supplies the applicable arithmetic, comparison,
bitwise, shift, checked-conversion, wrapping-conversion, `min`, `max`, and
`clamp` operations. Comparisons convert the primitive zero/one result to the
standard `Bool`; user code never treats the primitive discriminator as truth.
Trapping primitive operations retain their bytecode-defined behavior. Separately
named `checked_*` source functions return `Option` and must test the exceptional
case before invoking a trapping primitive.

The generation-1 integer source spellings are ordinary generic functions:
`wrapping_add`, `wrapping_sub`, `wrapping_mul`, `bit_and`, `bit_or`, `bit_xor`,
`bit_not`, `shift_left`, and `shift_right`. Their trusted implementations select
the corresponding frozen primitive by exact distributed-standard-library
declaration identity; these names are not contextual operators or forgeable
intrinsics. Wrapping arithmetic and bitwise results retain the low `N` bits for
an `N`-bit operand. Shift counts have type `u32` and a count greater than or
equal to `N` traps. Left shift retains the low `N` bits; right shift is logical
for unsigned operands and sign-extending arithmetic shift for signed operands.

Layer 1 contains concrete, manifest-bound `f32` and `f64` leaves for arithmetic,
negation, zero/one comparisons, cross-width conversion, every integer-to-float
pair, every checked float-to-integer pair, and the exact `f32`/`u32` and
`f64`/`u64` bit pairs. These declarations are deliberately width-specific: the
trusted declaration identity and its exact parameter/result signature select a
frozen primitive, while copying the spelling into user source grants no
authority. Float-producing leaves canonicalize NaNs to the bytecode-specified
positive quiet NaN and preserve signed zero. Public traits, parsing, formatting,
and convenience APIs remain ordinary source definitions above this boundary.

Wrapping conversion to target type `T` is spelled `wrapping_convert_to_T` and
accepts every integer source type. It applies the bytecode modulo rule directly.
Checked conversion from `S` to `T` is spelled `checked_S_to_T` and returns
`Option<T>`; there is no public trapping conversion function. Its ordinary
source implementation first wrapping-converts `S -> T -> S`, requires the
round trip to equal the input, and requires the input and candidate to agree on
whether they compare below zero. Those two tests are an exact representability
proof across every width and signedness pair. Only the successful arm invokes
the private trapping `int.convert_checked` leaf. Consequently an out-of-range
public conversion cannot produce a catchless primitive fault.

Floating arithmetic and IEEE comparisons use the width-explicit public
families `f32_add` through `f32_neg` / `f64_add` through `f64_neg` and
`f32_equal` through `f32_greater_equal` / their `f64` counterparts. Integer to
float conversion is named `<integer>_to_f32` or `<integer>_to_f64`; narrowing
and widening are `f64_to_f32` and `f32_to_f64`. The original float-to-integer
conversion family is checked and returns `Option<T>` under the name
`checked_f32_to_<integer>` or `checked_f64_to_<integer>`. Its ordinary source
wrapper rejects NaN, infinity, and values outside the target's half-open
representable interval before calling the trapping frozen leaf.

The additional [trait-backed `as` function](conversions.md) supports an explicit
target (`as<f32>(1)`) or a context-inferred target (`as(1)`). It provides lossy
integer/float conversions, including saturating float-to-integer conversion,
and ordinary user-defined `As<T>` implementations. This adds a separate policy;
the checked functions above keep their existing behavior.

The canonical `f32_to_bits` and `f64_to_bits` views collapse every NaN to the
frozen quiet-NaN spelling and preserve signed zero; the inverse constructors do
the same canonicalization. Float `Eq`, `Ord`, and `Hash` all use those bits, so
NaN is reflexive, signed zeroes remain distinct, total order runs from negative
infinity through negative values, `-0`, `+0`, positive values, positive
infinity, then canonical NaN, and equal values append
the identical fixed-width hash stream. `Display` and `Debug` render a finite
value as an exact decimal scientific numeral derived from its binary rational;
rendering never consults host locale or host float formatting.

The character surface includes scalar validation (`char_is_valid_scalar`),
checked `u32` conversion (`char_from_u32`), scalar extraction (`char_to_u32`),
UTF-8 encoded length (`char_utf8_len`), and the `char_encode_utf8` /
`char_decode_utf8` codec. Invalid scalars return `CharFromU32Error`; malformed,
overlong, surrogate, truncated, and out-of-range UTF-8 returns `Utf8Error` at
the offending byte rather than invoking the trapping manifest leaf. The
compiler's lexical name classes
are ASCII in generation 1; Unicode remains fully supported in character and text
literals and values. Therefore the standard library does not carry a Unicode XID
database.

### 7.2 Fundamental traits and helpers

The required ordinary traits are intentionally few:

| Trait | Purpose |
|---|---|
| `Eq` | result-based equality returning `Bool` |
| `Ord` | total comparison returning `Ordering` |
| `Hash` | append a value to a caller-owned `Hasher` |
| `Default` | construct the conventional empty/default value |
| `Display` | append user-facing text to a `Formatter` |
| `Debug` | append diagnostic/debug text to a `Formatter` |

`Ordering` is the nominal enum `Less | Equal | Greater`. The library implements
these traits for applicable scalars, `String`, `Bytes`, `Option`, `Result`, and
tuples of arity zero through four. A compiler data type implements only the
traits it actually needs; generation 1 has no derive framework or reflection.

`Result` provides construction, variant tests, `map`, `map_err`, `and_then`,
`or_else`, and the result operators specified above. `Option` provides
`Option::Some`, `None`, `map`, `and_then`, `or_else`, `unwrap_or`, and borrowing
projections.
The lazy parameters of all fallback and chaining functions are ordinary
callables. `unwrap`, indexing, and similarly partial conveniences have explicitly
trapping names or documentation; the compiler uses result-returning forms for
untrusted input.

`Range<usize>` is the half-open pair `(start, end)`. Common helpers include
length, emptiness, containment, intersection, and checked offset arithmetic.
The library supplies index-based vector and slice iterators, but not a large
iterator-adapter hierarchy. Compiler hot loops may use indices directly.

The small ownership/memory helper surface includes `identity`, `replace`,
`swap`, `take` (when `Default` is available), and compiler-mediated zero-use
disposal. The current source surface implements receiverless `Default` for the
integer scalars, `String`, and `Bytes`; generic `take` is implemented through
receiverless `Default` evidence and `replace`, preserving initialization of the
borrowed place. A normal
`destroy<T>(value:T)` by-value function is not that operation:
the call transfers `value` and records one owned use before the body can destroy
it. A source-facing disposal helper therefore requires `T: Use<[0,0]>` and a
special compiler disposal argument mode, or is omitted. `assert`,
`assert_eq`, `unreachable`, and `abort` terminate through the VM abort operation
and are for failed internal invariants, never malformed user input. `Slot<T>`
uses a private zero-or-one-element `Vec<T>` and is accessed through
`slot_empty`, `slot_filled`, `slot_take`, `slot_replace`, and
`slot_into_option`. User code cannot destructure its storage, while each
operation either transfers the element obligation or leaves the slot visibly
initialized and empty. No `MaybeUninit`, raw pointer, intrinsic destroy, or
unsafe operation is exposed.

## 8. Text, bytes, and formatting

### 8.1 `String` and text views

`String` is the public source alias for the VM's immutable, valid UTF-8 `Text`
value. Copying a `String` copies its immutable handle, not its byte buffer. Its
minimum API is:

```text
String::empty() -> String
String::byte_len(&String) -> usize
String::is_empty(&String) -> Bool
String::concat(String, String) -> String
String::as_bytes(&String) -> Bytes
String::from_utf8(Bytes) -> Result<String, Utf8Error>
String::eq(&String, &String) -> Bool
String::bytes(&String) -> BytesIter
String::chars(&String) -> Chars
String::char_indices(&String) -> CharIndices
String::slice(&String, Range<usize>) -> Result<String, TextRangeError>
```

Text ranges use byte offsets. Slicing validates both bounds and UTF-8 scalar
boundaries. The public supporting types are the nominal definitions
`Range<T> { start: T, end: T }`, `Utf8Error { valid_up_to: usize }`, and
`TextRangeError { Reversed, OutOfBounds, NotCharBoundary }`. Range errors are
selected in that order: reversal precedes bounds, which precede boundary
validation. `String::from_utf8` uses the trusted nontrapping valid-prefix
primitive to validate the complete RFC 3629 scalar range—including overlong
encodings, surrogates, and values above
`U+10FFFF`—before invoking the private trapping conversion leaf. Invalid input
therefore returns the lead byte's `valid_up_to` offset and never catches or
translates a VM fault. `TextView` stores a duplicable `String` handle plus a validated byte
range, making lexer tokens and symbol probes cheap without adding unsized types.
It supports byte/character iteration, equality, hashing, and materialization as
a `String`.

`StringBuilder` owns a dense `Vec<u8>`. It supports reserving capacity and
appending bytes, characters, strings, views, escaped strings, integers, and
formatted values. Because raw byte appends may produce malformed UTF-8,
`finish -> Result<String, Utf8Error>` validates once; a builder cannot expose
invalid bytes as text or translate a VM fault. Repeated diagnostic construction
and pretty printing must use this builder rather than repeated immutable
concatenation.

The current integer surface provides allocation-free decimal `append_u64` and
`append_i64`, plus lowercase hexadecimal `append_hex_u64` and
`append_hex_u128`. Digits are emitted directly into the owned byte vector;
signed formatting works from negative quotients and remainders so `i64::MIN`
never requires an unrepresentable positive intermediate.

The numeric text surface includes parsing every source integer base with checked
range conversion, parsing the generation-1 floating literal grammar to the
specified IEEE value, and decimal/hex formatting needed by diagnostics. Parse
failures carry a small error kind and byte offset rather than preformatted text.

### 8.2 `Bytes` and binary construction

`Bytes` is the VM's immutable octet value. It supplies length, emptiness,
equality, hashing, checked access, checked slicing, concatenation, and conversion
to/from a moved `Vec<u8>`. A `ByteView` is the byte analogue of `TextView`.

`ByteBuf` is the mutable binary builder used by the compiler's bytecode writer.
It is backed by `Vec<u8>` and provides:

```text
len, is_empty, reserve, resize_zeroed, push, extend
write_u16_le, write_u32_le, write_u64_le, write_u128_le
patch_u16_le, patch_u32_le, patch_u64_le
align_zeroed, append_bytes, finish -> Bytes
```

All offset addition, multiplication, narrowing, reservation, and patch ranges
have checked result-returning forms. `ByteReader` performs the inverse checked
little-endian reads with a cursor and never traps on malformed input. These two
types are sufficient for canonical `.grbc` emission, bootstrap comparison, and
test decoding; the standard library does not contain a general serialization
framework.

`resize_zeroed` grows or shrinks to the exact requested length. Patch operations
return false without mutation unless their complete fixed-width range is in
bounds. `align_zeroed` accepts only nonzero powers of two, checks the length
addition before mutation, and appends the minimum zero padding. ByteReader
truncation likewise returns `None` without advancing its private cursor.

### 8.3 Formatting

`Formatter` is a thin policy wrapper around `StringBuilder`. It tracks indentation
and exposes literal, character, integer, escaped-string, newline, indent, and
dedent operations. `Display` and `Debug` append to it and do not allocate an
intermediate string. The ordinary generic `format<T>(&T)` and
`format_debug<T>(&T)` functions dispatch through those traits and validate the
finished builder once; `Formatter::display` and `Formatter::debug` provide the
corresponding nested-value operations. Generation 1 has no compiler-known
format-string macro.

The current foundation emits four spaces per indentation level lazily before
the next nonempty literal or integer. Newlines therefore never gain trailing
spaces, including consecutive blank lines. Indent growth is checked, dedenting
at level zero returns false without mutation, and finishing delegates to the
builder's single UTF-8 validation pass.

The diagnostic renderer uses `SourceMap`, line starts, spans, primary/secondary
labels, severities, and notes defined in ordinary source. `SourceDiagnostic`
builds annotations and notes and renders one deterministic finished `String`;
the caller may emit that string through the diagnostic host capability. The
compact generation-1 renderer locates an annotation by `span.start` and retains
`span.end` as metadata for a future underline renderer. Invalid starts render
the stable `<unknown>:0:0` location rather than trapping.

## 9. Collections and algorithms

### 9.1 `Vec`, slices, and queues

`Vec<T>` is the standard dense interface over the VM's growable `Array<T>`.
The VM's empty-slot state is an implementation detail used for moves; all slots
below `Vec::len` are initialized at each public call boundary. Required operations
are:

```text
new, with_capacity, len, capacity, is_empty, reserve, clear
push, pop, truncate, resize, swap, reverse
get, get_mut, first, last
insert, remove, swap_remove
as_slice, as_mut_slice, append, extend_from_slice
iter -> SliceIter<'a,T>
split_off -> Result<Vec<T>, ()>
drain(Range<usize>) -> Result<Vec<T>, ()>
```

Safe access returns `Option<&T>` or `Option<&mut T>`. Explicit `index` methods
trap and are reserved for locations already proven in range. Copying extensions
require duplicable elements; moving operations work for linear elements.
`resize(&mut Vec<T>, usize, T)` and
`extend_from_slice(&mut Vec<T>, Slice<'_,T>)` therefore require
`T: Use<[0,infinity]>`. That intrinsic interval is the generation-1
duplicability contract: `resize` may use its fill value zero or arbitrarily many
times, while `extend_from_slice` copies each borrowed source element and leaves
the source unchanged. Neither operation implies a `Clone` or `Default` trait,
and there is no fill-free/default-constructing resize overload.
The remaining index-taking operations are checked as well: `swap` returns a
`Bool`, `remove` and `swap_remove` return `Option<T>`, and `insert` returns
`Result<(),T>` so an out-of-bounds insertion transfers its input back to the
caller instead of destroying a linear value. `append(&mut Vec<T>, Vec<T>)`
consumes the source vector, moves its elements in order, and consumes the fully
drained private array shell with `array.finish_drained`.

Operations that discard initialized elements require zero-use evidence for those
elements: destroying a nonempty vector, `clear`, shrinking `truncate`/`resize`,
and any overwrite API that does not return the previous value require
`T: Use<[0,0]>`. `pop`, `remove`, and
`swap_remove` return the removed `T` and transfer its obligation instead.
`split_off` and `drain` validate their complete index/range before mutation and
move the selected elements into a returned vector, so they preserve obligations
for restricted `T`; reversed or out-of-bounds ranges leave the source unchanged.
`into_iter`/by-value iteration likewise transfers each element. Its iterator
state retains ownership of every not-yet-yielded element, so it may be destroyed
early only when `T: Use<[0,0]>`. Otherwise it must be exhausted or transferred.
Once an ownership-moving operation has emptied every machine-array slot, the
private layer-1 implementation consumes the exhausted shell with
`array.finish_drained`; this transition runs no element destruction and requires
no zero-use evidence for `T`.

The current by-value surface uses private `VecIntoIter<T>` state.
`Vec::into_iter(Vec<T>)` reverses the private dense storage once, and consuming
`VecIntoIter::next` returns `Option<(T,VecIntoIter<T>)>` so the yielded element
and continuation are transferred together in original insertion order. `None`
is returned only after `next` consumes the empty state and closes its fully
drained Array with `array.finish_drained`. `VecIntoIter<T>` has an affine
`Use<[0,1]>` implementation only when its resident `Vec<T>` is affine and
`T: Use<[0,0]>`; exact-linear iterator state therefore cannot be abandoned and
must be exhausted or transferred. The representation field is private, so user
code cannot forge a partially drained state or reach the Array shell.

`Vec::iter(&Vec<T>)` directly constructs the same checked `SliceIter<'a,T>`
state as `Slice::iter(Vec::as_slice(value))`. It adds no mutable iterator or
second representation: the iterator retains the shared backing-array loan and
threads its monotonically advancing index through
`SliceIter::next(&mut iterator) -> Option<usize>`.

`Slice<'a,T>` and `SliceMut<'a,T>` are range-checked views over a vector and
carry ordinary shared/unique lifetimes. They support length, splitting, checked
sub-slicing, iteration, and indexed access. The representation is a base array
reference plus start and length; no element buffer is copied.

The shared representation is declared in the standard-library authority domain
as `Slice<'a,T> { private base: &'a Array<T>, private start: usize, private
length: usize }`. User code cannot construct or destructure it, or project those
fields. `Vec::as_slice` is the public source constructor and establishes
`start == 0` and `length == Vec::len`. `Slice::subslice(view,start,length)`
returns `None` unless `start <= view.length` and
`length <= view.length - start`; the subtraction-first check prevents overflow.
`Slice::get` and `Slice::first` return `Option<&'a T>`, while `Slice::len` and
`Slice::is_empty` inspect only the validated window. Splitting and mutable slices
build on this invariant but are separate implementation tranches. Shared
iteration uses private `SliceIter<'a,T>` state. `Slice::iter` constructs it and
`SliceIter::next(&mut iterator)` returns `Option<usize>` while advancing its
private cursor in place; the index is relative to the original slice. The caller
retains the duplicable `Slice` and uses `Slice::get` to obtain the corresponding
reference. The iterator retains the backing loan's stored-reference provenance.

`SliceMut<'a,T>` stores the corresponding private `&'a mut Array<T>` plus the
same validated start and length. It is linear and cannot be copied. The current
surface provides non-consuming `len`/`is_empty`, while `get`, `get_mut`, `first`,
`first_mut`, `subslice`, and `subslice_mut` consume the view. Consuming access is
intentional at this stage: it transfers the unique backing loan into either the
returned element reference or the returned subview without permitting two live
mutable aliases. Shared access and `subslice` safely downgrade that unique loan;
the mutable forms preserve it.

`VecDeque<T>` is a ring buffer with amortized constant-time `push_front`,
`push_back`, `pop_front`, and `pop_back`. `Stack<T>` and `WorkList<T>` are small
source aliases/wrappers over `Vec<T>` and `VecDeque<T>` and add no VM types.
Their `pop` operations transfer elements; `clear`, truncation, or abandonment
with resident elements follows the same `T: Use<[0,0]>` rule as `Vec<T>`.

The source implementation stores a private `Vec<Slot<T>>` ring plus `head` and
logical length. Every physical slot is initialized as `Empty` or `Full(T)`;
end operations atomically replace one Slot through a unique element borrow, so
no empty machine-Array cell crosses a source call or handler. Wrapped indices
use subtraction-first arithmetic. Capacity growth is geometric: it constructs
each new `Empty` slot individually, scans the old ring from its logical head,
moves every `Full` payload into dense logical order, then pops every old Empty
Slot and closes only the fully drained old Array shell. No element is copied or
destroyed during growth, so all four end operations transfer exact-linear
elements. `clear` and affine abandonment require zero-use evidence. `WorkList<T>`
is a source alias using `push_back`/`pop_front` FIFO vocabulary and introduces no
additional nominal or VM representation.

### 9.2 Hash collections

`Hasher` is a fixed, versioned, deterministic integer state with incremental
`write_u*`, `write_bytes`, and `finish` operations. Equal values must append the
same byte sequence. Hash values are implementation details and never bytecode
artifact IDs. Changing the standard-library hash algorithm is allowed, but
stage-2/stage-3 builds use the same bundled library.

Generation 1 uses 64-bit FNV-1a. Integer writers append their complete fixed
width in little-endian order, `usize` is the VM's fixed 64-bit width, and byte
stream writes are incremental. The state field is private, so only these
versioned source operations can construct or advance a hash stream.

`HashMap<K,V>` uses open addressing with cached hashes, geometric power-of-two
growth, tombstone cleanup, and a maximum load factor of 7/8. Keys are moved into
the table and lookup borrows a key. Its required surface is:

```text
new, with_capacity, len, capacity, is_empty, clear, reserve
contains_key, get, get_mut
insert -> Option<V>
remove -> Option<V>, remove_entry -> Option<(K,V)>
raw_get(&K, cached_hash) -> Option<&V>
reserve_additional -> Bool
entry, keys, values, iter
```

`clear` and table destruction require `K: Use<[0,0]>` and
`V: Use<[0,0]>` for every resident entry. `remove -> Option<V>` transfers the
value but destroys the removed key, so it requires `K: Use<[0,0]>`;
`remove_entry -> Option<(K,V)>` transfers both and has no such requirement.
`insert -> Option<V>` also requires `K: Use<[0,0]>` because an occupied-key path
discards the incoming key; an ownership-general alternative returns that key.
Replacement and entry APIs must return the old/incoming key or value, or require
zero-use evidence for whatever they discard. Map/set `into_iter` and draining
transfer entries;
an abandoned iterator may zero-destroy its remainder only with the corresponding
zero-use evidence. `HashSet::remove` requires `T: Use<[0,0]>`, while
`HashSet::take` transfers the stored `T`; duplicate insertion likewise requires
zero-use evidence or must return the uninserted value.

The `entry` API provides occupied/vacant lookup and insert-or-get in one probe.
`HashMapEntry::or_insert(V) -> &mut V` returns the existing or newly inserted
resident directly; its private completed-probe invariant makes an empty result
unrepresentable. The map also exposes a checked raw lookup by precomputed hash;
a stale or forged hash returns `None`. `Interner<String>` uses deterministic
hash probing and allocates a standalone `String` only on an actual miss.
`HashSet<T>` is the zero-sized-value specialization with insert, contains,
remove, `union_with`, materializing `intersection`, iteration, and length
operations.

Borrowed map/set iterators retain one shared owner loan and a private cursor.
Their `next(&mut iterator)` methods advance that cursor in place and return only
the borrowed item (`(&K,&V)`, `&K`, or `&V`), so no continuation owner is hidden
inside an optional payload.

Iteration order is unspecified and must never determine emitted bytecode or
diagnostic order. The compiler sorts externally observable results. Collection
operations expose or accumulate probe counts so the compiler's global complexity
budget can turn pathological input into a structured resource diagnostic rather
than a host panic or unbounded loop.

Generation 1 does not require a tree map. Places that need ordering collect into
a vector and sort; places that need lookup use a hash table.

### 9.3 Algorithms

The library includes in-place unstable sort, stable merge sort using one reusable
scratch vector, binary search, lower/upper bound, partition, deduplication, and
lexicographic slice comparison. Sort accepts an ordinary comparison callable.
The compiler uses unstable sort for IDs and stable sort only where source-order
ties are semantically significant.

Algorithms are iterative or explicitly depth-bounded. Quicksort/introsort must
fall back to heapsort at its depth limit and insertion sort for small partitions,
so adversarial compiler input cannot cause unbounded recursion or quadratic
quicksort behavior.

## 10. Compiler-construction toolkit

These types are ordinary generic standard-library code. They exist because each
is used by several compiler phases and sharing them keeps the self-hosted compiler
small.

| Type | Contract and compiler use |
|---|---|
| `Id<Tag>` | bounds-checked `u32` typed index; zero is valid and `Tag` has no runtime payload |
| `IndexVec<I,T>` | dense vector indexed by `Id<I>`; `push` returns the new ID |
| `Arena<I,T>` | append-only `IndexVec`; supports mark/truncate scratch lifetimes |
| `Interner<T>` | `HashMap<T,Id<T>>` plus `IndexVec`; returns canonical IDs |
| `BitSet<I>` | growable machine-word bit set with insert/remove/test and set algebra |
| `SparseSet<I>` | dense/sparse integer set with constant-time clear and membership |
| `WorkQueue<I>` | deque plus membership bit set, preventing duplicate queued IDs |
| `MultiMap<K,V>` | hash map from key to a compact range/list of values |
| `SourceMap` | concatenated source segments, line starts, and byte-span lookup |
| `ByteBuf` | canonical bytecode section and artifact construction |

`Id<Tag>` conversion checks that an arena length fits `u32`; overflow is a
structured compilation resource error. `Arena::truncate(mark)` destroys values
in reverse insertion order and therefore requires `T: Use<[0,0]>`; a draining
rollback API instead transfers the truncated suffix. Interners do not intern
inference-variable-bearing terms: those stay in scratch arenas until zonked, as
required by the compiler architecture.

The library also supplies small checked counters/budgets, a monotonic timer-free
`StepBudget`, and deterministic statistics records. The VM supervisor owns wall
time and memory limits; compiler source owns logical limits such as solver steps,
MIR transforms, hash probes, recursion depth, and diagnostic count.

The following matrix is the acceptance criterion for bootstrap completeness:

| Compiler job | Standard-library facilities |
|---|---|
| source bundling and lexing | `Bytes`, `String`, `TextView`, UTF-8/ASCII helpers, `SourceMap` |
| parsing and fixity grouping | `Vec`, `Stack`, `Arena`, `HashMap` |
| symbols and declarations | `String`, `Interner`, `IndexVec`, typed `Id` |
| inference and trait solving | scratch `Arena`, `HashMap`, `HashSet`, `WorkQueue`, budgets |
| ownership and MIR dataflow | `BitSet`, `SparseSet`, `IndexVec`, `VecDeque` |
| deterministic diagnostics | sort, `Formatter`, `StringBuilder`, source line tables |
| bytecode emission | `ByteBuf`, checked arithmetic, sorting, `Bytes` |
| compiler invocation | process arguments, file read/write, diagnostic output |

No compiler phase may add a hidden dependency on a Rust collection, allocator
handle, clock, random generator, native path object, or host pointer.

## 11. Host effects and entry support

The public compiler I/O surface consists of ordinary nominal effects and
source-defined performing functions:

```text
process_args() -> Vec<String>                 / {ProcessArgs}
read_file(path: String) -> Bytes              / {FileRead}
write_file(path: String, bytes: Bytes) -> ()  / {FileWrite}
write_diagnostic(text: String) -> ()          / {Diagnostic}
```

Each public function performs its corresponding operation. The standard library
also supplies `run_compiler_host(main)`, which installs handlers for those four
protocols, calls `main`, and returns its result with an empty outward protocol
row. Each handler clause invokes one internal, manifest-bound host leaf and then
resumes exactly once. The compiler executable's closed entry calls
`run_compiler_host(compiler_main)`.

All four public operations declare resumption quantity `[1,1]`: their host
handlers either terminate with a VM host fault or resume the captured continuation
once with the returned value/unit. They never clone, cancel, or retain it.

Only the four internal leaves lower to the exact
`(capability, symbol, signature)` import tuples defined by `bytecode.md`. Their
bytecode signatures have empty outward protocol lists; a host call is nevertheless
an observable, potentially trapping MIR operation and is never treated as pure.
These implementation names live in the private standard-library module and are
not importable by ordinary source. A nominal definition containing a private
field is deconstructible only inside its declaring module's privacy domain;
public fields follow ordinary item visibility, and manifest-opaque layouts remain
non-deconstructible. Direct host-leaf use is unsupported and remains
capability-checked and observable. Security never relies on source-name privacy.
Host faults terminate as specified by the VM and cannot be caught by a
Grandiose handler.

The mapping is fixed:

| Public operation | Host capability and symbol |
|---|---|
| `ProcessArgs::get` | `process.args`, `get` |
| `FileRead::read` | `fs.read`, `read` |
| `FileWrite::write` | `fs.write`, `write` |
| `Diagnostic::write` | `diagnostic`, `write` |

There is no ambient environment, current directory query, clock, randomness,
network, subprocess, dynamic library, or arbitrary foreign-function interface.

Paths are UTF-8 `String` values passed through unchanged. Lightweight source
helpers may find a final separator, extension, or display name, but there is no
platform path abstraction in generation 1. The build driver supplies explicit
input and output paths.

## 12. Deliberate omissions

The bootstrap standard library has no runtime module/package API, reflection,
macros, derive system, garbage-collected pointer, shared mutable reference
counting, threading, async executor, networking, tree collection, regular
expression engine, locale, date/time, arbitrary-precision number, or general
serialization framework. None is needed to build the compiler.

Application libraries may later implement additional facilities in ordinary
source, but generation 1 does not automatically locate or concatenate them.

## 13. Source-bundle and module model

A generation-1 compilation unit is an application package plus explicitly
designated dependency package roots assembled as a deterministic `SourceBundle`.
Source modules and package bindings are compile-time structure; they are not
runtime objects and do not perform runtime dependency discovery.

The canonical bundle order is:

```text
std-lib.glorious
compiler-designated crate root
declared external modules in canonical module-path order
explicit dependency package roots and each declared module closure
```

The bundler inserts exactly one newline between adjacent files so tokens and line
comments cannot fuse across a boundary. `mod child;` in logical directory `D`
resolves only to `D/child/child.glorious`; an inline `mod child { ... }` advances
the same logical directory for its nested external declarations. The selected
crate root is exempt from the self-named-folder rule. Module discovery and
interface collection are deterministic and independent of filesystem traversal
order.

Typical bundles are:

```text
self-host compiler = std-lib.glorious + compiler.glorious
application        = std-lib.glorious + application.glorious
test program       = std-lib.glorious + fixture.glorious
module crate       = std-lib.glorious + root + declared module closure
```

The compiler source is included only when the compiler itself is the primary
program being built. Compiling an application does not append
`compiler.glorious` to the application.

A source segment table retains original file names and byte ranges. Structured
module identity has language semantics as the authority for private items and
`private` struct fields; segment identity still anchors manifest-bound layer-1
leaves and diagnostics. A runtime leaf is authoritative only when its
validated declaration identity belongs to the explicitly trusted first standard-
library entry; repeating that entry's display name does not reproduce its
identity. Named module items are private by default and `pub` exports them.
Imports support `crate`, `self`, `super`, explicit names, aliases, groups, globs,
and `self`; deterministic fixed-point resolution permits benign re-export cycles.
There are no initialization units or source-order dependencies.

The hermetic library API never reads the filesystem: all segments must be
supplied. Dependency roots carry an explicit manifest name; `-` normalizes to
`_` for their public package-module alias, and invalid or colliding aliases are
diagnosed. Each dependency is a separate parentless root, so `crate` remains
package-local. Positional/unmarked additional segments never become dependencies.
A missing declared module, duplicate physical module, or orphan segment
in a module-bearing crate is a structured diagnostic. The path-aware CLI may
recursively load the same declared closure before invoking that API. For
module-free programs, explicitly supplied additional segments are
crate-root fragments.

The canonical distribution bundle is paired atomically with the distribution
runtime manifest. Raw conformance bundles—even when a test explicitly grants
their first segment trusted-leaf authority—do not acquire that manifest by
position or by copying the standard-library display name. A conformance caller
must supply its exact custom manifest, and distribution-facing entry points must
not combine custom authority with the embedded distribution source implicitly.

## 14. Important generation-1 notes

- `std-lib.glorious` is the only automatically supplied source dependency.
- `mod name;` is the only source syntax requesting another file inside a package;
  dependency roots are driver-supplied manifest inputs.
- The path-aware compiler driver recursively discovers only declared modules;
  the hermetic compiler library performs no filesystem I/O.
- Undeclared files are never included by directory scanning.
- The standard library is always first and cannot be shadowed by a second global
  declaration with the same name.
- The standard-library path/version is selected by the compiler distribution,
  not by source code.
- Source programs cannot opt into alternative standard libraries in generation 1.
- Runtime file I/O through an explicitly granted effect/capability is not a source
  dependency and does not change this model.
- Bootstrap reproducibility hashes or compares the canonical crate bundle; no
  module cache, dependency cache, or lockfile participates.
- The canonical source extension is `.glorious`.

Package/dependency selection remains a build-tool concern and must not make the
generation-1 crate bundle ambiguous.
