# New standard-library scope

Status: design decisions recorded from the standard-library review. This is a
smaller generation-1 scope than the existing broad library contract. It records
what is in scope now; it does not promise the deferred application-framework
surface.

The [unsafe/native-ABI amendment](unsafe-memory-and-native-abi.md) requires source
collection, UTF-8, and hashing implementations over a small raw-memory layer.
Private algorithmic leaves below describe the bootstrap, not the final boundary.
Safe-only VM guests may call safe exports of trusted native library code.

## 1. Approved scope

The initial standard library is limited to these groups from the review:

1. **Core prelude.** `Bool`, `Option<T>`, `Result<T, E>`, `Range<T>`,
   `Ordering`, and the small ownership/value helpers: `identity`, `replace`,
   `swap`, and `take` where its normal trait bound is satisfied.
2. **Source-defined control.** The source library supplies `if`/`else`,
   `and`/`or`/`not`, `match` helpers, result-based control, looping helpers,
   and their fixity declarations. These remain ordinary source definitions,
   not compiler AST nodes.
3. **Scalar and primitive values.** The numeric scalar families, `char`, unit,
   never, checked and wrapping numeric operations, and the minimal trusted
   primitive bindings needed to implement them.
4. **Fundamental traits and formatting.** A deliberately small trait surface:
   `Eq`, `Ord`, `Hash`, `Default`, `Display`, and `Debug`, with their required
   helpers and deterministic formatting support.
6. **Collections and algorithms.** `Vec<T>`, generic borrowed slices,
   deterministic `HashMap`/`HashSet`, queues/work lists, sorting, binary
   search, and the compiler-oriented collection building blocks required by
   the self-hosted compiler.

The former broad text/bytes category is not accepted as written. Text support
is retained only in the smaller `String`/`Str` model below; it is not a reason
to add a second public immutable `Text` type or a broad text framework.

Everything else from the earlier wish list is deferred, including networking,
threading, async runtimes, regex, locale, date/time, big integers, general
serialization, reflection, macros, and application-framework facilities.

## 2. Required implementation inventory

This section is the working checklist for the approved scope. Names here are
standard-library definitions unless explicitly called an intrinsic; none of the
control names become compiler keywords.

### 2.1 Category 1 — core prelude

The prelude must provide these ordinary nominal types and aliases:

```text
Result<T, E> = Ok(T) | Err(E)
Option<T> = Result<T, ()>
Bool = Option<()>

true  = Some(())
false = None

Ordering = Less | Equal | Greater
Range<T> = { start: T, end: T }
```

`Option` does not receive a distinct runtime representation. Its initial API
is `Some`, `None`, `is_some`, `is_none`, `map`, `and_then`, `or_else`,
`unwrap_or`, `as_ref`, `as_mut`, `take`, `replace`, `get_or_insert`,
`get_or_insert_with`, and `get_or_insert_default`. `get_or_insert` requires
`T: Use<[0,1]>`, because the provided value is discarded when the option is
already occupied. The latter two construct only in the empty branch; the
default variant has the normal `T: Default` bound.
`Result` supplies `Ok`, `Err`, `is_ok`, `is_err`, `map`, `map_err`,
`and_then`, and `or_else`.

`Range<usize>` is half-open. It needs `len`, `is_empty`, `contains`,
`intersection`, and checked offset arithmetic. The ownership/value helpers are
`identity`, `replace`, `swap`, and `take` (using `Default` where appropriate).
There is no generic by-value `destroy`; disposal remains a compiler-mediated
zero-use operation and is available only when `T: Use<[0,1]>`.

The compiler-provided intrinsic vocabulary needed by this category is `Use`,
`Drop`, and `Fn`, plus the callable-environment intrinsics described in section
4. Source declarations cannot forge implementations of those intrinsic
relations.

### 2.2 Category 2 — source-defined control and fixities

The library, not the compiler, defines the bindings `if`, `else`, `and`, `or`,
and `not`. Their right operands are ordinary lazy zero-argument callables.
Evaluation is always left-to-right: evaluate the left result once, inspect it,
then invoke the right callable only on the selected path. The complete operator
chain is one `Fn`/`RunsIn` environment island, so branch captures, loans, uses,
effects, and normal post-states are checked together.

| Binding | Behavior | Discarded value and required evidence |
|---|---|---|
| `if` | `Ok(_) if body` runs `body`; `Err(e) if body` preserves `Err(e)` | Success payload: `A: Use<[0,1]>` |
| `else` | `Ok(a) else fallback` produces `a`; `Err(_) else fallback` runs `fallback` | Error payload: `E: Use<[0,1]>` |
| `and` | `Ok(_) and next` runs `next`; `Err(e) and next` preserves `Err(e)` | First success payload: `A: Use<[0,1]>` |
| `or` | `Ok(a) or alternative` preserves `Ok(a)`; `Err(_) or alternative` runs `alternative` | First error payload: `E: Use<[0,1]>` |
| `not` | Exchanges `Ok(value)` and `Err(value)` | Nothing is discarded |

In conceptual signatures:

```text
if  : (Result<A, E>, lazy B) -> Result<B, E>
else: (Result<A, E>, lazy A) -> A
and : (Result<A, E>, lazy Result<B, E>) -> Result<B, E>
or  : (Result<A, E>, lazy Result<A, F>) -> Result<A, F>
not : Result<A, E> -> Result<E, A>
```

This gives normal Boolean-style use while retaining result payloads:

```glorious
let greeting = is_member(user) if { "hello" } else { "guest" }
let value = parse(input) and { validate_config() } or { recover_config() }
let allowed = not is_blocked(user)
```

The required relative precedence, tightest first, is:

```text
prefix not
and                    // left associative
or                     // left associative
else                   // right associative
```

Thus `else if` is a normal chain rather than a compiler `ElseIf` node, and
`or` binds more tightly than `else`. Function application, arithmetic, and
comparison retain their own tighter fixities. The library must declare these
fixities with the bindings; renaming a binding never changes compiler behavior.

Also in this category, implement source-level `match` helpers and pattern-test
composition; `return` through a callable's implicit label; result propagation
through `try(value, @function)`; tail-call/label-based `loop`, `break`, and
`continue`; effect-based `yield`, `await`, and `fail`; and the ordinary result
combinators above. These are all library control, lowered through the language
core rather than represented by dedicated compiler control nodes.

The initial reusable control kernel is deliberately small:

```text
fold_until(range, accumulator, @exit, step)
  step: (A, usize) -> Result<A, A>
  Ok(next)    continues with `next`
  Err(final)  transfers `final` to `@exit`

LoopStep<S, B> = Continue(S) | Break(B)
loop_state(initial, body) -> B
  body: S -> LoopStep<S, B>
```

`fold_until` owns the label and performs the one actual transfer. This avoids
giving a callback an affine label token which would otherwise need to be moved
both into the callback and into its recursive continuation. The source-level
`break` and `continue` bindings construct `LoopStep::Break` and
`LoopStep::Continue`; `loop` aliases `loop_state`. `return(value,
@function)` is the corresponding library forwarding helper for a named
function's implicit label. None of these names are parser keywords.

### 2.3 Category 3 — scalar and primitive surface

Implement source-facing `()`, `!`, `u8`, `u16`, `u32`, `u64`, `u128`, `i8`,
`i16`, `i32`, `i64`, `i128`, `usize`, `isize`, `f32`, `f64`, and `char`.
Numeric APIs include arithmetic, comparisons, min/max/clamp, bitwise and shift
operations where applicable, wrapping conversion, and checked conversion
returning `Option<T>`. Float operations preserve the canonical NaN and signed
zero rules established by the VM. Checked float-to-integer functions coexist
with the explicit saturating policy of the [trait-backed `as` function](conversions.md).

The ordinary source-level bit API is `bit_and`, `bit_or`, `bit_xor`,
`bit_not`, `bit_shl`, and `bit_shr`. The shift helpers use a `u32` count for
every integer width; their private leaves retain the VM's integer-width and
shift-count checks.

`char` provides scalar validation, `u32` conversion, UTF-8 encoded length, and
encoding/decoding support. Primitive leaves are private, manifest-bound layer-1
bindings. Public scalar operations are ordinary wrappers, so a user spelling a
similar function name gains no privileged VM access.

### 2.4 Category 4 — fundamental traits and formatting

Keep the trait surface intentionally small:

| Trait | Required purpose |
|---|---|
| `Eq` | result-based equality returning `Bool` |
| `Ord` | total comparison returning `Ordering` |
| `Hash` | append a deterministic representation to a caller-owned hasher |
| `Default` | create the conventional empty/default value |
| `Display` | append user-facing output to a formatter |
| `Debug` | append diagnostic output to a formatter |

Provide these only where they have a real use; there is no derive framework or
reflection system. Formatting needs `Formatter`, `format`, and `format_debug`,
with `Display`/`Debug` appending to the formatter rather than allocating a
temporary string for every nested value. Formatting remains deterministic and
locale-independent.

### 2.5 Category 6 — collections and algorithms

The initial collection surface is deliberately compiler-oriented:

```text
Vec<T>
Slice<'a, T>, SliceMut<'a, T>
VecDeque<T>, Stack<T>, WorkList<T>
HashMap<K, V>, HashSet<T>
Hasher
```

`Vec<T>` needs `new`, `with_capacity`, `len`, `capacity`, `is_empty`,
`reserve`, `push`, `pop`, `get`, `get_mut`, `first`, `last`, `insert`,
`remove`, `swap_remove`, `swap`, `reverse`, `truncate`, `clear`, `append`,
`split_off`, `drain`, `as_slice`, `as_mut_slice`, and borrowed/by-value
iteration. `Slice`/`SliceMut` provide validated views, checked subslicing,
splitting, indexing access, and iteration without copying their elements.

`SliceMut::split_at` consumes one mutable view and returns two mutable views
only after checking the requested split lies inside its existing window. Its
implementation may use one private, manifest-bound array leaf that consumes a
unique array borrow plus `(start, length, split)` and materializes the two
disjoint window borrows. The leaf is not a public pointer API: ordinary code
can neither name it nor construct a `SliceMut` because the backing borrow and
window fields remain private to `std`.

Moves preserve obligations: `pop`, `remove`, `swap_remove`, `drain`,
`split_off`, `append`, and by-value iteration transfer elements out. Operations
that silently discard residents—such as `clear`, shrinking `truncate`, or
abandoning an iterator—require the relevant `T: Use<[0,1]>` evidence.
Copying operations such as `extend_from_slice` or `resize` require the
duplicability interval `T: Use<[0,infinity]>`.

`VecDeque`, `Stack`, and `WorkList` are source-level wrappers, not new VM
collection types. `HashMap` and `HashSet` use deterministic hashing, provide
checked lookup and ownership-preserving insert/remove variants, and make no
iteration-order promise. Compiler-visible output must sort externally observable
map/set results.

The current source implementation uses open addressing with cached hashes,
power-of-two growth, and tombstone cleanup. Keys and values live in a separate
dense vector, so rehashing only rewrites index metadata. Replacement preserves
the existing resident key and returns the old value. `HashMap::get_mut` lends
the resident value uniquely; `HashMap::remove_entry` returns `(K,V)` without
requiring either field to be discardable. These source algorithms do not yet
certify the physical cost of VM aggregate snapshots or backing-array mutation.

Implement in-place unstable sort, stable sort using a reusable scratch vector,
binary search, lower/upper bounds, partition, deduplication, and lexicographic
slice comparison. The initial partition spelling is:

```text
Vec::partition_by(&mut Vec<T>, F) -> usize
where F: Fn<(&T), Output = Bool>, F: Use<[0,infinity]>
```

It rearranges the vector in place, returns the first index of the false
partition, and makes no stability promise. The explicit duplicability bound
means the predicate can be invoked once per examined resident; ordinary
capture-free named functions and closures with duplicable captures satisfy it
without adding a compiler collection callback intrinsic. Do not add a broad iterator-adapter tower or a tree map in
this tranche; compiler code may use indexed loops, vectors plus sorting, and
hash maps directly.

### 2.6 Quantity decision: public affine erasure, internal flow intervals

The compiler needs to summarize how many owned uses can occur on normal control
paths. A concrete execution has one count, but a join can have several possible
counts:

```glorious
if condition {
    consume(ticket) // one owned use
} else {
    // zero owned uses
}
```

The compact internal summary is therefore an interval: this join has actual
use range `[0,1]`. It rejects an exact-linear ticket because some normal path
uses it zero times, while an affine or duplicable value is valid. This is a
compile-time place-flow fact, not a runtime counter or a user-visible tag on
each value.

The reviewed alternatives for a public library operation that may discard a
generic payload were:

| Option | Bound | Steelman |
|---|---|---|
| Exact erasure | `T: Use<[0,0]>` | States the operation's literal need: it erases the payload and never transfers it. It also leaves room for a future zero-only principal type. |
| Affine erasure | `T: Use<[0,1]>` | Defines the public class of values that may be left unused: affine and duplicable values qualify, while exact-linear values do not. It keeps the source model to three meaningful principal contracts. |

The decision is **affine erasure**. The only public principal `Use` contracts
are:

```text
Use<[0,infinity]>  duplicable: may be used any number of times
Use<[0,1]>         affine: may be unused or transferred once
Use<[1,1]>         exact-linear: must be transferred once
```

Accordingly, a public library operation that may silently discard a value uses
the bound `T: Use<[0,1]>`. This admits `Use<[0,1]>` and
`Use<[0,infinity]>` values and rejects `Use<[1,1]>` values. A
`Use<[0,0]>` result remains an internal description of one path's actual count;
it is not a source-level principal contract or a standard-library bound.

This makes structural composition uniform: a type with principal
`Use<[0,1]>` may contain affine or duplicable fields, and a type with principal
`Use<[1,1]>` may contain exact-linear, affine, or duplicable fields. Each field
must permit every use the enclosing type permits. A duplicable enclosing type
may contain only duplicable fields.

## 3. `Option<T>` is the temporary slot

There is no `Slot<T>` type.

`Option<T>` is both the domain representation of optional data and the standard
temporary storage for ownership-sensitive mutation. Its ordinary API provides
the required operations, including `take`, `replace`, insertion, and borrowed
access:

```glorious
let mut value: Option<File> = Some(file)
let file = value.take() // the storage is temporarily None
// use file
value = Some(file)      // restore the storage
```

No separate type is needed merely to say that an occupied location may be
temporarily empty. A future `Slot<T>` would need a capability beyond this API
or a repeatedly demonstrated clarity benefit before it could be justified.

## 4. Callable-environment intrinsics

`Environment` and `RunsIn` are compiler intrinsics, not user-defined standard
library traits. User code cannot implement, construct, or forge their evidence.
The compiler creates and seals that evidence while it checks a callable's
captures, loans, use quantities, effects, and post-state.

`Environment` identifies an opaque, compiler-created lexical capture scope.
`RunsIn` describes a transition for a specific callable in such a scope:

```text
F: Fn<Args, Output = R, Effects = e>
E: Environment
F: RunsIn<Access, Args, After = S>
```

Here `Access` is the actual environment access (`&E`, `&mut E`, or `E`), and
`After` is the compatible post-environment. A reading closure can run with
`&E`; a mutating closure needs `&mut E`; a closure that moves a capture may
consume `E` and produce a different post-environment.

The standard library's control combinators may quantify over these intrinsic
relations. Ordinary application code should normally receive the behavior
through closure inference, without spelling either intrinsic.

## 5. Owned strings and borrowed string slices

`String` is the public owned, growable UTF-8 string buffer. It owns its storage
and is moved by the normal ownership rules. There is no separate public `Text`
owner or alias.

`Str<'a>` is a separate opaque borrowed UTF-8 view. It is a validated window
into a `String` or static string data; it is not an alias for `Slice<'a, u8>`.
Its private representation may use a borrowed byte range, but its invariant is
that every value is valid UTF-8.

```glorious
let mut name: String = "Malek".to_string()
name.push('!')

fn show(value: Str) {
    // `Str` means `Str<'_>` here.
}

show(&name)       // borrow/view coercion from String to Str
show("Grandiose") // literal: Str<'static>
```

Borrowing a `String` as `Str` prevents conflicting mutation or reallocation
for the duration of the borrow. `Str` is immutable: exposing mutable bytes
would let safe code invalidate UTF-8. Mutation stays on `String` through
UTF-8-preserving operations such as `push`, `push_str`, `insert`, and removal
at validated character boundaries.

The core text surface is:

```text
String::as_str(&String) -> Str
String::from_utf8(Vec<u8>) -> Result<String, Utf8Error>
String::push(&mut String, char) -> ()
String::push_str(&mut String, Str) -> ()
String::insert(&mut String, usize, Str) -> Result<(), StringRangeError>

Str::len_bytes(Str) -> usize
Str::is_empty(Str) -> Bool
Str::as_bytes(Str) -> Slice<u8>
Str::chars(Str) -> Chars
Str::slice(Str, Range<usize>) -> Result<Str, StringRangeError>
Str::to_string(Str) -> String
```

String ranges use byte offsets and are half-open. Slicing checks that bounds
are ordered, in range, and at UTF-8 character boundaries; it returns a borrowed
`Str` without allocating. `StringRangeError` distinguishes reversed,
out-of-bounds, and non-character-boundary ranges.

## 6. Lifetime elision for `Str`

Lifetimes are omitted whenever the relation can be inferred. In type positions,
`Str` is shorthand for `Str<'_>`.

```glorious
fn trim(text: Str) -> Str
// equivalent to: fn trim<'a>(text: Str<'a>) -> Str<'a>

fn compare(left: Str, right: Str) -> Bool
// equivalent to: fn compare<'a, 'b>(left: Str<'a>, right: Str<'b>) -> Bool
```

Each omitted input lifetime is distinct. An omitted output lifetime is inferred
when there is one input lifetime to which it can be tied; methods similarly tie
an omitted borrowed output to their borrowed receiver. The compiler rejects an
ambiguous output rather than guessing:

```glorious
fn choose(left: Str, right: Str) -> Str // rejected

fn choose<'a>(left: Str<'a>, right: Str<'a>) -> Str<'a> // explicit relation
```

The explicit shared lifetime means the result is valid for an overlap of the
two inputs; it does not demand that callers' concrete borrows have identical
durations. Stored borrowed fields and other declarations that expose a lasting
relationship likewise name their lifetime explicitly.

## 7. Consequences for implementation

- The compiler must reserve and seal `Environment`/`RunsIn` as intrinsics.
- The standard-library source owns control flow and its fixities; the compiler
  continues to type-check and lower the resulting ordinary calls.
- The existing broad `Text` public surface should be replaced, not aliased, by
  the `String`/`Str` model before it becomes a stable library promise.
- General `Slice<'a, T>` remains the collection view. `Str<'a>` is the
  text-specific view that adds the UTF-8 invariant.

## 8. Slice representation and static compiler data

`Slice<'a, T>` is an ordinary standard-library type, not a public compiler
enum or a pair of public static/dynamic variants. Semantically it is a shared
fat pointer:

```text
Slice<'a, T>    = { data: *const T, len: usize }
SliceMut<'a, T> = { data: *mut T,   len: usize }
```

The VM may retain hidden provenance or a backing handle in addition to those
machine words when that is necessary to keep an arena allocation alive. That
is an implementation detail. The source-level representation and API are one
uniform slice abstraction: a slice may view either a live `Array<T>` allocation
or compiler-provided read-only static storage without becoming a public sum
type.

Static storage is identified in the verified artifact by a segment identity,
range, element layout, and stable type tag. The tag is a type identity rather
than an ad-hoc string, so a UTF-8 literal, a raw byte blob, and an embedded
image cannot be confused or cast by ordinary source code:

```text
Utf8Bytes       // compiler data behind "..."
u8              // compiler data behind b"..."
PngImage        // an explicitly embedded PNG asset
OpaqueAsset     // declared arbitrary static binary data
```

The compiler/VM's one hidden representation is conceptually:

```text
__StaticData<T> = { segment_id, byte_offset, length, type_tag }
```

It is not constructible or nameable by ordinary source code. The VM resolves a
verified `segment_id` to immutable compiler-owned or mapped data; bytecode
never carries an arbitrary machine pointer. The artifact constant table stores
the segment's tag, alignment, bounds, and bytes. A verifier-approved operation
must use the matching tag and remain in range, so ordinary code cannot cast a
PNG segment to UTF-8, or one opaque asset kind to another.

The lowering and public wrapping rules are deliberately concrete:

```text
"..."  -> hidden __StaticData<Utf8Bytes>
        -> standard-library Str<'static>

b"..." -> hidden __StaticData<u8>
        -> standard-library Slice<'static, u8>
```

`String` remains an ordinary opaque `Vec<u8>`/`Array<u8>` wrapper in `std`.
`String::as_str(&String)` creates the same standard-library `Str` abstraction
over a borrowed array, while `Str::as_bytes` returns a normal
`Slice<u8>` without allocating. Static and dynamic views therefore share one
public API despite having different backing storage.

The trusted standard-library implementation needs one representation bridge
plus a tiny sealed inspection interface over hidden static data:

```text
static_as_array(raw) -> &'static Array<T>
static_len(raw) -> usize
static_subslice(raw, start, len) -> raw
static_get_shared(raw, index) -> &'static T
```

`static_as_array` is not a second public slice representation. It is the
single private bridge that lets `std` build its normal `Slice { storage, start,
length }` view over read-only segment data; the VM may implement that array as
a provenance-carrying static facade rather than an allocation. The other three
leaves inspect or narrow sealed data directly. All four are private
manifest-bound leaves, not callable authority obtained by spelling their
names. The standard library owns every public `Slice` and `Str` operation.

The compiler and VM may use internal pointers after resolving a verified
segment, but neither arbitrary pointers nor a constructible `StaticData<T>`
value are exposed to source. `StaticData<T>` is at most an internal Core and
artifact-constant notion used to materialize a normal static slice. The VM
verifier checks segment tags, alignment, bounds, immutability, and the static
lifetime before such a view can exist.

`Str<'a>` remains a standard-library newtype over `Slice<'a, u8>` whose
constructors establish valid UTF-8. Thus `"hello"` lowers to read-only static
UTF-8 data and becomes `Str<'static>` without allocation, while
`String::as_str(&String)` produces the same `Str` abstraction over the owned
buffer. `Str::as_bytes` returns the underlying `Slice<u8>` without copying.

The only privileged operations are private, manifest-bound view-materializing
leaves and verifier support for static literal segments. Bounds checks,
sub-slicing policy, indexing, UTF-8 boundary validation, image decoding, and
all public `Slice`/`Str` APIs remain standard-library code.
