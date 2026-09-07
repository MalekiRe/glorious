# Glorious Standard Library Specification

**Consolidated interface draft 1.0 · 7 September 2026**

**Companion:** [Glorious Language Specification](glorious-language-specification.md).

**Language:** Glorious. **Compiler/toolchain:** Grandiose.

**Baseline:** `MalekiRe/glorious@7e4a021811b6a8e0d62b2899f10e602d037c3c14` plus the design decisions in this conversation.

This document specifies intended public types, traits, effect operations, function signatures, and observable contracts. It contains no library implementation bodies, collection algorithms, private growth strategies, or executor implementation. A declaration ending in `;` is an interface declaration here, not a claim that an unbound bodyless definition is legal in an application source file.

The draft is not a claim of current compiler support, binary compatibility, formal soundness proof, or executed conformance tests. Its control contracts rely on the complete static interface model in the companion, including checked guarded postconditions; they are not claimed to work by merely adding a single RunsIn bound to the old sources.

The companion's pre-alpha evolution policy applies: there is no legacy library, compiler, VM, ABI, or G1 compatibility requirement. Replace superseded interfaces and update their implementations and tests together instead of retaining compatibility wrappers. Runtime contract checks still reject mismatched inputs.

## Contents

1. [1. Scope, profiles, and source ownership](#1-scope-profiles-and-source-ownership)
2. [2. Interface notation and universal contracts](#2-interface-notation-and-universal-contracts)
3. [3. Foundational types and value functions](#3-foundational-types-and-value-functions)
4. [4. Operator declarations and laws](#4-operator-declarations-and-laws)
5. [5. Conditional carriers, refinements, and dispatch](#5-conditional-carriers-refinements-and-dispatch)
6. [6. Matching, labels, and result propagation](#6-matching-labels-and-result-propagation)
7. [7. Loop interfaces and imported control operations](#7-loop-interfaces-and-imported-control-operations)
8. [8. Result interfaces](#8-result-interfaces)
9. [9. Option and Bool interfaces](#9-option-and-bool-interfaces)
10. [10. Ordering, ranges, and bounded values](#10-ordering-ranges-and-bounded-values)
11. [11. Numeric scalar families](#11-numeric-scalar-families)
12. [12. Characters, ASCII, and UTF-8](#12-characters-ascii-and-utf-8)
13. [13. Borrowed text and owned String](#13-borrowed-text-and-owned-string)
14. [14. Fixed arrays and borrowed slices](#14-fixed-arrays-and-borrowed-slices)
15. [15. Vec ownership and mutation](#15-vec-ownership-and-mutation)
16. [16. Queues, stacks, and heaps](#16-queues-stacks-and-heaps)
17. [17. Hash maps, sets, and entries](#17-hash-maps-sets-and-entries)
18. [18. Iterator, owning stepper, and lending interfaces](#18-iterator-owning-stepper-and-lending-interfaces)
19. [19. Traversal, search, ordering, and sequence algorithms](#19-traversal-search-ordering-and-sequence-algorithms)
20. [20. Hashing and canonical fingerprints](#20-hashing-and-canonical-fingerprints)
21. [21. Formatting and structured diagnostics](#21-formatting-and-structured-diagnostics)
22. [22. Memory, allocation, and C-FFI support](#22-memory-allocation-and-c-ffi-support)
23. [23. Binary readers, buffers, and bounded codecs](#23-binary-readers-buffers-and-bounded-codecs)
24. [24. Compiler-construction data structures](#24-compiler-construction-data-structures)
25. [25. Source maps, locations, budgets, and transactions](#25-source-maps-locations-budgets-and-transactions)
26. [26. Bounded parser and graph helpers](#26-bounded-parser-and-graph-helpers)
27. [27. Host effects and external authority](#27-host-effects-and-external-authority)
28. [28. Stream I/O interfaces](#28-stream-io-interfaces)
29. [29. Paths, file handles, processes, clocks, and randomness](#29-paths-file-handles-processes-clocks-and-randomness)
30. [30. Generators, futures, tasks, and cancellation](#30-generators-futures-tasks-and-cancellation)
31. [31. Required trait-instance and adapter matrices](#31-required-trait-instance-and-adapter-matrices)
32. [32. Supporting errors and precise failure distinctions](#32-supporting-errors-and-precise-failure-distinctions)
33. [33. Required standard-library conformance cases](#33-required-standard-library-conformance-cases)
34. [34. Decisions, scope exclusions, and source traceability](#34-decisions-scope-exclusions-and-source-traceability)


## 1. Scope, profiles, and source ownership

### 1.1 Library organization

| Profile/module family | Required surface |
|---|---|
| `core` | Intrinsic re-exports, Result/Option/Bool, ownership-safe value helpers, control traits/operators, scalar contracts, fixed arrays, borrowed views. |
| `alloc` | Allocator boundary, Vec, String, maps/sets/queues, owned iteration and formatting. |
| `std` | Core/alloc re-exports plus typed host effects, I/O, files/process environment, clocks/entropy, task/generator protocols, and C-FFI adapters. |
| `std::compiler` | Optional compiler-construction library: typed IDs, arenas, interners, source maps, diagnostics, bounded binary data and work budgets. |
| Separately versioned extensions | Networking and concurrency implementations, extensive Unicode data, regex, arbitrary precision, general serialization, reflection/macros, and application frameworks. They are not implicit bootstrap requirements. |

Profiles are dependency closures, not runtime type tags. Core/alloc/std denote selected public modules and declaration sets in the canonical standard-library source package, not a requirement for three independently extensible packages. A member exposing String, Vec, owned formatting, or another allocation-dependent type is available only with the alloc dependency closure, even when its owner is a scalar or borrowed view. Pure core therefore does not depend on an allocating Formatter merely because the full library also specifies scalar Display implementations. A no-std build can use core and selected allocation support when it supplies their admitted runtime dependencies. A host effect module can have an interface even when the executable supplies its own handler rather than a bundled runtime implementation.

Collections, UTF-8 processing, hashing, formatting, and control are source-owned library behavior. Machine leaves supply scalar computation, memory/layout/static-data mechanisms, structural control, and explicitly bound host calls. A primitive implementing a whole map, Vec algorithm, parser, or compiler query is not a substitute for this library.

### 1.2 Canonical namespaces

The declarations in each section belong to the following modules, with explicit shared-type imports understood. Interface code is not one flat source file; identical member names of different types or operations of different effects are not free-function overloads.

| Sections | Canonical module(s) |
|---|---|
| 3, 8, 9 | `core::result`, `core::option`, `core::bool`, `core::mem`, and fundamental `core::cmp`, `core::clone`, `core::default`, `core::convert`. |
| 4 | `core::ops` for operator traits/bindings; numeric conversion stays `core::convert`. |
| 5–7 | `core::control`; `Fail`/`Report` also re-exportable through `core::effect`. |
| 10–12 | `core::cmp`, `core::range`, `core::num`, `core::char`, `core::utf8`. |
| 13–19 | `alloc::string`, `core::slice`, `core::array`, `alloc::collections`, `core::iter`, `alloc::iter`, `core::algorithm`/`alloc::algorithm` according to allocation needs. |
| 20–21 | `core::hash`, `alloc::fingerprint`, `alloc::fmt`, `std::compiler::diagnostic`. |
| 22 | `core::mem`, `core::ptr`, `alloc::allocator`, `alloc::boxed`, `std::ffi`. |
| 23–26 | `core::binary`/`alloc::binary`, `std::compiler::{storage,source,budget,parse,graph}`. |
| 27–30 | `std::host`, `std::io`, `std::path`, `std::fs`, `std::process`, `std::time`, `std::random`, `std::task`, and `core::generator`. |
| 32 | Supporting types are exported from the module of the operation defining their contract; `std::io::IoError` is shared by hosted I/O. |

Std re-exports the selected core/alloc public modules without changing their declaration identities. The prelude below is a deliberate selected export set, not all names in this table.


### 1.3 Minimal prelude

The default prelude exports Result/Ok/Err, Option/Some/None, Bool/true/false, Ordering, Range, fundamental traits, the ordinary compositional control functions, loop/loop_at/loop_state, return/break_at/try, and the directly imported LoopControl operations. Allocation profiles add Vec, String, Str, Slice/SliceMut and standard formatting traits. Broad glob imports of filesystem/network/FFI operations are not default prelude behavior.

Effect operations are imported or re-exported directly, preserving declaration identity. A function whose only purpose is to forward to the same effect operation is not part of the canonical API. Ordinary functions that transform inputs, handle effects, establish resource invariants, or implement substantive composition remain appropriate.

There is no public choose/if_else, no standalone Slot parallel to Option, no public immutable Text owner parallel to String, and no overloaded free-function families. Related arities/policies use different names.

## 2. Interface notation and universal contracts

### 2.1 Reading declarations

`impl<T> Type<T> { ... }` supplies the listed type/lifetime parameters and bounds to every enclosed member. All function type variables must be bound by their declaration or its enclosing impl. Family sections explicitly quantify concrete scalar types and spell the mechanical expansion rules. They do not introduce a magical Int or Float runtime type. An opaque interface header such as `pub struct Vec<T>;` withholds the representation; it does **not** declare a constructible zero-field unit struct. Its implementation must supply private storage and the specified ownership invariants.

Rows use the language's union form: `/ { | e1, e2 }` forwards the union of those rows; `/ {Known | e}` includes a known effect plus e. Omission means the empty outward algebraic-effect row, not freedom from allocation, faults, cleanup, or unsafe implementation work.

Every callback-taking declaration includes applicable Fn/RunsIn evidence directly or through a fully specified selected dispatch-trait implementation in this document. The accompanying **Control contract** is also normative and includes invocation cardinality, path dependence, environments, and terminal/cancellation obligations. This is not an invitation to fill in unspecified callback behavior later.

Trait member contracts apply to their implementations. A `Use<[1,1]>` bound requests permission for an exact-once use; it does not test whether the principal class is exact-linear. `Use<[0,1]>` means discardable, and `Use<[0,*]>` means structurally duplicable. Clone remains independent.

### 2.2 Generic lifetime conventions

Receiver-borrowed outputs use the explicitly named receiver lifetime. A by-value `Str<'a>` or `Slice<'a,T>` can return a subview with `'a`. A borrow of a mutable view yields a child lifetime unless the entire original view is consumed to transfer its loan. No function can return a pointer into temporary local storage merely because an elided signature appears to fit.

Repeated callback bounds use fresh reborrows:

```glorious
for<'call> &'call mut F:
    Fn<(Item,), Output = R, Effects = e>,
for<'call> &'call mut F:
    RunsIn<&'call mut Env, (Item,), After = Env>
```

Such universal borrows range over invocation regions valid inside the enclosing environment and receiver lifetimes. They do not require captured non-static state to outlive every possible lifetime. Environment inference ties these bounds to the actual scope; a returned callback cannot escape those dependencies.

### 2.3 Failure and allocation policy

A checked structural operation validates its full bounds/range before mutating. Validation failure preserves the receiver unless a weaker partial-progress contract is explicit. A failed operation that consumed an input returns that input or another value owning its remaining obligation; exact-linear residents are never silently dropped.

Fallible allocation functions use `try_` names and return structured allocation/capacity failures, preserving owned inputs as documented. Infallible allocation conveniences may terminate on allocation failure. An empty row is not a promise of allocation success. Runtime resource enforcement can still terminate an execution independently of a recoverable allocator result.

Callback algorithms distinguish validation failure from partial progress after callbacks ran. They do not roll back external effects. Sorting guarantees a valid permutation on comparator failure, not restoration of the old order. A consuming transformation returns processed output and unprocessed ownership where recovery is promised.

### 2.4 Complexity and determinism

Complexity bounds in this document are observable API obligations where explicitly stated, not prescriptions of a particular algorithm. Hash collections do not promise iteration order; deterministic artifact/diagnostic output sorts by a declared stable key. Hash-table hash values are not persistent artifact identities. Canonical fingerprint operations are separately versioned.

### 2.5 Universal receiver and cleanup rules

All by-value inputs transfer ownership to the operation. Every successful return and every recoverable failure specifies where that ownership went. Borrowed input never becomes owned without a move from a unique place, an explicitly duplicable copy, or an explicit Clone. Destruction remains subject to the language, including zero-sized residents and conditional initialization.

A callback invoked zero or one times has a skipped path. Independently materialized owning callbacks need legal skipped cleanup. Contextually correlated branch bodies can instead use the shared environment/control-contract mechanism; adding an unconditional affine bound to every alternative would incorrectly reject linear conditional programs.

## 3. Foundational types and value functions

```glorious
pub enum Result<T,E> { Ok(T), Err(E) }
pub type Option<T> = Result<T,()>;
pub type Bool = Result<(),()>;

pub const true: Bool = Result::Ok(());
pub const false: Bool = Result::Err(());
pub const None<T>: Option<T> = Result::Err(());
pub use Result::Ok as Some;

pub enum Ordering { Less, Equal, Greater }
pub struct Range<T> { pub start: T, pub end: T }
pub enum Either<A,B> { Left(A), Right(B) }
pub struct Rejected<T,E> { pub value: T, pub error: E }

pub fn identity<T>(value: T) -> T;
pub fn replace<T>(target: &mut T, replacement: T) -> T;
pub fn swap<T>(left: &mut T, right: &mut T);
pub fn take<T>(target: &mut T) -> T where T: Default;
pub fn absurd<T>(value: !) -> T;
pub fn discard<T>(value: T) where T: Use<[0,1]>;
```

`Option::Some` is also an associated constructor re-export of Result::Ok, not a second constructor type. This associated export is an interface binding, not the invalid source import spelling `as Option::Some`. All aliases normalize before coherence and type comparison. Bool constants are monomorphic; None is the language's structural generic constant scheme, not a memoized global of arbitrary ownership class.

`replace` transfers the previous resident without destroying it. `swap` neither destroys nor duplicates residents. `take` evaluates Default before creating any initialization hole. `discard` is an explicitly affine-only convenience: its ordinary by-value transfer does not let it accept exact-linear T, and it does not claim that destruction counts as a use. No universal safe forget/destroy/transmute escape is provided.

### 3.1 Fundamental ordinary traits

```glorious
pub trait Eq {
    fn eq(left: &Self, right: &Self) -> Bool;
}
pub trait Ord: Eq {
    fn cmp(left: &Self, right: &Self) -> Ordering;
}
pub trait PartialOrd: Eq {
    fn partial_cmp(left: &Self, right: &Self) -> Option<Ordering>;
}
pub trait Hash {
    fn hash(value: &Self, state: &mut Hasher);
}
pub trait Clone {
    fn clone(value: &Self) -> Self;
}
pub trait Default {
    fn default() -> Self;
}
pub trait Display {
    fn fmt(value: &Self, out: &mut Formatter);
}
pub trait Debug {
    fn fmt(value: &Self, out: &mut Formatter);
}
pub trait As<T> {
    fn cast(value: Self) -> T;
}
pub trait TryAs<T> {
    type Error;
    fn try_cast(value: Self) -> Result<T,Self::Error>;
}
pub fn as<T,S>(value: S) -> T where S: As<T>;
pub fn try_as<T,S>(value: S) -> Result<T,S::Error> where S: TryAs<T>;
```

Eq is an equivalence relation. Ord is a total order consistent with Eq. Hash must feed identical streams for equal values, though unequal values may collide. Clone produces an independently owned logical value; it grants no additional uses of the original owner. TryAs implementations must preserve required ownership on their Error path, ordinarily by using `Rejected<Self,Reason>` as Error when Self is not discardable.

There is no blanket Clone for every duplicable T if it would overlap structured implementations. Scalar, tuple, Result, String and collection implementations are explicit coherent families. There is no automatic derive framework in this version.

The exact-conversion policy has its own ordinary trait rather than an unconstrained universal cast:

```glorious
pub trait ExactAs<T> {
    type Error;
    fn exact_cast(value: Self) -> Result<T,Self::Error>;
}
pub fn exact_convert<T,S>(value: S) -> Result<T,S::Error> where S: ExactAs<T>;
```

For scalar pairs its Error is ConversionError. User implementations must preserve owned input obligations on failure just like TryAs. ExactAs accepts only value-preserving conversions; As and checked truncating float-to-integer conversion remain different policies.

### 3.2 Alias-coherent defaults and formatting

Result has one structural Eq/Ord/Hash policy inherited by Option and Bool. Enum ordering follows declared variant order, then payload order. Option<T> defaults to None without T:Default. Consequently Bool defaults to false. There is no overlapping generic Default for every Result<T,E>.

Generic Result Debug uses Ok/Err. Bool Display uses true/false and does not coexist with an overlapping blanket Display for every Result. Named `fmt_result` and `fmt_option` adapters provide alternative presentation without alias-dependent trait identity. `Clone::clone` is the canonical operation, not an additional inherent clone name on every container.

## 4. Operator declarations and laws

Independent operator traits define their own dispatch. The source binding for an operator delegates through the selected trait, not a compiler arithmetic AST category.

```glorious
pub trait Add<Rhs> { type Output; fn add(left: Self, right: Rhs) -> Self::Output; }
pub trait Sub<Rhs> { type Output; fn sub(left: Self, right: Rhs) -> Self::Output; }
pub trait Mul<Rhs> { type Output; fn mul(left: Self, right: Rhs) -> Self::Output; }
pub trait Div<Rhs> { type Output; fn div(left: Self, right: Rhs) -> Self::Output; }
pub trait Rem<Rhs> { type Output; fn rem(left: Self, right: Rhs) -> Self::Output; }
pub trait Neg { type Output; fn neg(value: Self) -> Self::Output; }
pub trait Positive { type Output; fn positive(value: Self) -> Self::Output; }

pub trait BitAnd<Rhs> { type Output; fn bit_and(left: Self, right: Rhs) -> Self::Output; }
pub trait BitOr<Rhs> { type Output; fn bit_or(left: Self, right: Rhs) -> Self::Output; }
pub trait BitXor<Rhs> { type Output; fn bit_xor(left: Self, right: Rhs) -> Self::Output; }
pub trait BitNot { type Output; fn bit_not(value: Self) -> Self::Output; }
pub trait BitShl { type Output; fn bit_shl(value: Self, count: u32) -> Self::Output; }
pub trait BitShr { type Output; fn bit_shr(value: Self, count: u32) -> Self::Output; }

pub fn bit_and<L,R>(left: L, right: R) -> L::Output where L: BitAnd<R>;
pub fn bit_or<L,R>(left: L, right: R) -> L::Output where L: BitOr<R>;
pub fn bit_xor<L,R>(left: L, right: R) -> L::Output where L: BitXor<R>;
pub fn bit_not<T>(value: T) -> T::Output where T: BitNot;
pub fn bit_shl<T>(value: T, count: u32) -> T::Output where T: BitShl;
pub fn bit_shr<T>(value: T, count: u32) -> T::Output where T: BitShr;
```

The resolved operator targets have these non-overloaded function signatures:

```glorious
pub fn add<L,R>(left: L, right: R) -> L::Output where L: Add<R>;
pub fn sub<L,R>(left: L, right: R) -> L::Output where L: Sub<R>;
pub fn mul<L,R>(left: L, right: R) -> L::Output where L: Mul<R>;
pub fn div<L,R>(left: L, right: R) -> L::Output where L: Div<R>;
pub fn rem<L,R>(left: L, right: R) -> L::Output where L: Rem<R>;
pub fn neg<T>(value: T) -> T::Output where T: Neg;
pub fn positive<T>(value: T) -> T::Output where T: Positive;
pub fn equal<T>(left: T, right: T) -> Bool where T: Eq + Use<[0,1]>;
pub fn not_equal<T>(left: T, right: T) -> Bool where T: Eq + Use<[0,1]>;
pub fn less<T>(left: T, right: T) -> Bool where T: Ord + Use<[0,1]>;
pub fn less_equal<T>(left: T, right: T) -> Bool where T: Ord + Use<[0,1]>;
pub fn greater<T>(left: T, right: T) -> Bool where T: Ord + Use<[0,1]>;
pub fn greater_equal<T>(left: T, right: T) -> Bool where T: Ord + Use<[0,1]>;

pub prefix 50 - = neg;
pub prefix 50 + = positive;
pub infixl 30 - = sub;
pub infixl 30 + = add;
pub infixl 40 * = mul;
pub infixl 40 / = div;
pub infixl 40 % = rem;
pub infix 20 == = equal;
pub infix 20 != = not_equal;
pub infix 20 < = less;
pub infix 20 <= = less_equal;
pub infix 20 > = greater;
pub infix 20 >= = greater_equal;
```

Comparison wrappers consume their operands and compare through borrowed Eq/Ord internally. Their affine bound accounts for disposal after observation. Scalars copy into these calls; nonduplicable objects are compared as `&left == &right` or with `Eq::eq(&left,&right)`. No implicit owner borrow or function-arity overload is hidden in the punctuation.

These ordinary operator traits have empty outward rows. An operation that needs host effects uses a named effectful interface instead. Comparison bindings use the declared by-value wrapper above; explicit borrowed operands select reference instances. Source operators do not gain general implicit argument borrowing. Scalar operators use duplicable values; noncopy user operators supply the exact owned/reference trait instances they support.

| Binding | Fixity | Contract |
|---|---:|---|
| prefix `+`, prefix `-` | 50 | Positive/Neg, distinct from their binary bindings. |
| `*`, `/`, `%` | left 40 | Mul/Div/Rem. |
| `+`, `-` | left 30 | Add/Sub. |
| `==`, `!=`, `<`, `<=`, `>`, `>=` | nonassociative 20 | Eq/Ord-derived comparison; return Bool. |
| `not` | prefix 6 | Swap success and failure, including contextual test branches. |
| infix `if` | left 5 | Same ordinary binding as callable if. Parenthesized `if(c)` application is primary syntax. |
| `and` | left 3 | Conditional success sequencing. |
| `or` | left 2 | Conditional failure recovery. |
| `else` | right 1 | Conditional defaulting/unwrapping. |

A word/operator's fixity does not create a new implementation. `not` is the canonical Result negation; no independent Bool-only `!` logical API is required. Bit complement is `bit_not`. Relational comparisons do not automatically chain as mathematical inequalities.

## 5. Conditional carriers, refinements, and dispatch

### 5.1 Ordinary Result algebra

For plain Result, the required value behavior is:

| Operation | Success | Failure | Discard bound |
|---|---|---|---|
| if(Result<A,X>, body) | invoke body once; wrap its B in Ok | preserve X; skip body | A affine |
| else(Result<A,X>, fallback) | return A; skip fallback | discard X; invoke fallback once | X affine |
| and(Result<A,X>, next) | discard A; invoke next once | preserve X; skip next | A affine |
| or(Result<A,X>, alternative) | preserve A; skip alternative | discard X; invoke alternative once | X affine |
| not(Result<A,X>) | move A into Err | move X into Ok | none |

Callbacks are ordinary callable values. Every operator evaluates its explicit left argument once. A right block executes only on invocation. Result failure after a callback ran is not rollback of that callback's ownership or effects.

### 5.2 One function name, ordinary trait dispatch

The following are ordinary library dispatch traits. They do not grant pattern-binding authority or compiler special cases. A selected implementation's full callback and guarded control contract is part of the public function's effective signature.

```glorious
pub trait If<'env,E0,E1,F> {
    type Output;
    type Effects: EffectRow;
    fn apply(condition: Self, body: F) -> Self::Output / { | Self::Effects };
}
pub trait Else<'env,E0,E1,F> {
    type Output;
    type Effects: EffectRow;
    fn apply(value: Self, fallback: F) -> Self::Output / { | Self::Effects };
}
pub trait And<'env,E0,E1,F> {
    type Output;
    type Effects: EffectRow;
    fn apply(value: Self, next: F) -> Self::Output / { | Self::Effects };
}
pub trait Or<'env,E0,E1,F> {
    type Output;
    type Effects: EffectRow;
    fn apply(value: Self, alternative: F) -> Self::Output / { | Self::Effects };
}
pub trait Not {
    type Output;
    fn not(value: Self) -> Self::Output;
}

pub fn if<'env,E0,E1,C,F>(condition: C, body: F) -> C::Output / { | C::Effects }
where E0: Environment<'env>, E1: Environment<'env>, C: If<'env,E0,E1,F>;
pub fn else<'env,E0,E1,C,F>(value: C, fallback: F) -> C::Output / { | C::Effects }
where E0: Environment<'env>, E1: Environment<'env>, C: Else<'env,E0,E1,F>;
pub fn and<'env,E0,E1,C,F>(value: C, next: F) -> C::Output / { | C::Effects }
where E0: Environment<'env>, E1: Environment<'env>, C: And<'env,E0,E1,F>;
pub fn or<'env,E0,E1,C,F>(value: C, alternative: F) -> C::Output / { | C::Effects }
where E0: Environment<'env>, E1: Environment<'env>, C: Or<'env,E0,E1,F>;
pub fn not<C>(value: C) -> C::Output where C: Not;
```

Associated names in each function above are resolved through its single relevant dispatch-trait bound. Fully qualified trait projections are equivalent. These are five functions, not overloaded Result and Test versions. A custom local carrier can implement the appropriate ordinary traits, but its control evidence must be derived from its actual implementation.

### 5.3 Full plain-Result implementation interfaces

The blocks below specify the **effective plain-Result instance schemas**, including associated types and bounds; no method implementations are supplied. For and/or they are the Result/Result specializations of the complete coherent carrier family in §5.6, not additional overlapping implementations to install alongside that family.

```glorious
impl<'env,E0,E1,A,X,B,F,ef: EffectRow> If<'env,E0,E1,F> for Result<A,X>
where
    E0: Environment<'env>, E1: Environment<'env>,
    A: Use<[0,1]>,
    F: Fn<(),Output=B,Effects=ef>,
    F: RunsIn<E0,(),After=E1>
{
    type Output = Result<B,X>;
    type Effects = ef;
}

impl<'env,E0,E1,A,X,F,ef: EffectRow> Else<'env,E0,E1,F> for Result<A,X>
where
    E0: Environment<'env>, E1: Environment<'env>,
    X: Use<[0,1]>,
    F: Fn<(),Output=A,Effects=ef>,
    F: RunsIn<E0,(),After=E1>
{
    type Output = A;
    type Effects = ef;
}

impl<'env,E0,E1,A,X,B,F,ef: EffectRow> And<'env,E0,E1,F> for Result<A,X>
where
    E0: Environment<'env>, E1: Environment<'env>,
    A: Use<[0,1]>,
    F: Fn<(),Output=Result<B,X>,Effects=ef>,
    F: RunsIn<E0,(),After=E1>
{
    type Output = Result<B,X>;
    type Effects = ef;
}

impl<'env,E0,E1,A,X,Y,F,ef: EffectRow> Or<'env,E0,E1,F> for Result<A,X>
where
    E0: Environment<'env>, E1: Environment<'env>,
    X: Use<[0,1]>,
    F: Fn<(),Output=Result<A,Y>,Effects=ef>,
    F: RunsIn<E0,(),After=E1>
{
    type Output = Result<A,Y>;
    type Effects = ef;
}

impl<A,X> Not for Result<A,X> { type Output = Result<X,A>; }
```

**Control contract.** On a selected callback path, the actual input environment must supply E0 and invocation produces E1. On a skipped path, the incoming environment is retained, or an already produced correlated post-state is retained. The compiler associates those states with the returned structural variant until the island seals. There is no unconditional `E0:Use<[0,1]>` on if/and/or, and no unconditional assertion that every skipped branch has the same E0 as a selected branch.

A complete `if ... else` can invoke either body from the same incoming E and join to S. An `and ... or` can invoke both callbacks sequentially, or only the alternative. For each incoming state that reaches the alternative, a separate applicable RunsIn proof is required. One generic `After=S` entry is not permission to ignore those paths.

A materialized owning F that is skipped must be discardable or explicitly returned by another interface. Contextual correlated bodies instead retain shared capture obligations until their enclosing control contract accounts for them. Guards and effects occurring before a callback's invocation are not deferred retroactively.

### 5.4 Binding-context interfaces

The language supplies sealed binding-context evidence and ordinary library code transports its values. The following intrinsic interface schemas specify the hidden callable argument tuples used by refinement consumers:

```glorious
trait BindingContext<'a>: Environment<'a> {
    type Args;
    type BorrowArgs<'b> where 'a: 'b;
}
```

For the empty context `()`, both argument tuples are `()`. For a nonempty compiler-created pattern context P, `P::Args` is `(Bindings<'a,P>,)` and `P::BorrowArgs<'b>` is `(&'b Bindings<'a,P>,)`. These tuples are part of Fn/RunsIn, even when the source block omits their spelling. Source cannot implement BindingContext or obtain lexical names by implementing If.

The library's context-bearing carrier is:

```glorious
pub struct BranchResult<'a,T,E,P,N>
where P: BindingContext<'a>, N: BindingContext<'a>;
pub type Test<'a,P,N> = BranchResult<'a,(),(),P,N>;
```

Its representation is private. Logically its alternatives are a success payload T with positive pack P, or an error payload E with negative pack N. Constructors used for `is` are compiler/authority checked. The carrier is ordinary runtime data plus resident binding payloads; its brands erase, not its residents or guards. A plain Result has the same algebra with empty contexts, but is a distinct nominal carrier and retains its original public type.

### 5.5 Full refined if/else/not contracts

```glorious
impl<'a,'env,E0,E1,T,X,P,N,B,F,ef: EffectRow>
    If<'env,E0,E1,F> for BranchResult<'a,T,X,P,N>
where
    P: BindingContext<'a>, N: BindingContext<'a>,
    E0: Environment<'env>, E1: Environment<'env>,
    T: Use<[0,1]>,
    F: Fn<P::Args,Output=B,Effects=ef>,
    F: RunsIn<E0,P::Args,After=E1>
{
    type Output = BranchResult<'a,B,X,(),N>;
    type Effects = ef;
}

impl<'a,'env,E0,E1,T,X,P,N,F,ef: EffectRow>
    Else<'env,E0,E1,F> for BranchResult<'a,T,X,P,N>
where
    P: BindingContext<'a>, N: BindingContext<'a>,
    E0: Environment<'env>, E1: Environment<'env>,
    X: Use<[0,1]>, Bindings<'a,P>: Use<[0,1]>,
    F: Fn<N::Args,Output=T,Effects=ef>,
    F: RunsIn<E0,N::Args,After=E1>
{
    type Output = T;
    type Effects = ef;
}

impl<'a,T,X,P,N> Not for BranchResult<'a,T,X,P,N>
where P: BindingContext<'a>, N: BindingContext<'a>
{
    type Output = BranchResult<'a,X,T,N,P>;
}
```

A selected refined if passes the positive pack to its body, rather than silently discarding that pack as a generic successful payload. Its error branch retains the negative pack. Refined else forwards its negative pack only to the fallback. Once a context is no longer exposed, all resident loans/guards must be lawfully closed. Returned references must point into valid original storage, not into a destroyed binding-pack object.

### 5.6 Refined and/or: context algebra and complete family expansion

For a conditional carrier C define its ordinary associated schema `Success(C)`, `Failure(C)`, `Yes(C)`, and `No(C)`. For Result these are T, E, (), (). For BranchResult they are T, E, P, N. The following is **interface-family notation**, not new source syntax or arbitrary higher-kinded type computation:

* `P + Q` is the compiler-checked context containing both sets of binders/facts with compatible loans and distinct binder keys.
* `P & Q` is the context containing only binders/facts available with compatible identity/type on both alternatives.
* Empty context is the identity for `+`; contexts can be discarded only under their resident ownership bound.

For `and(C,F)`, universally quantify the carrier types C and D; environment lifetime `'env` and brands E0/E1; all context lifetimes; and callback row ef. Let P=Yes(C), N=No(C), Q=Yes(D), and M=No(D). The complete callback constraints are:

```text
E0: Environment<'env>
E1: Environment<'env>
P,N,Q,M: BindingContext at their respective valid lifetimes
Success(C): Use<[0,1]>
Failure(C) = Failure(D)
for each valid fresh 'b:
    F: Fn<P::BorrowArgs<'b>, Output=D, Effects=ef>
    F: RunsIn<E0, P::BorrowArgs<'b>, After=E1>
```

Here F is the **actual supplied receiver type**: it may itself be an owning callable or a reference to one. There are not separate overlapping owning-F and borrowed-F implementations. The callback is invoked at most once. When supplied through a borrowed receiver, its receiver and environment access obligations must be discharged by the normal call rules; passing &mut F does not establish duplicability.

The result is `Carrier<Success(D),Failure(C),P+Q,N & (P+M)>`, with outward row ef. Carrier means Result only for the Result/Result pair, otherwise BranchResult with the stated contexts. The positive conjunction path needs checked context-merge evidence `Merge(P,Q,P+Q)`. The two failure paths need checked projection evidence `Project(N,N & (P+M))` and `Project(P+M,N & (P+M))`. Every resident excluded by a projection must satisfy `Use<[0,1]>`; every retained field keeps its original reference/ownership provenance. Merge, projection and lost-resident proofs are intrinsic static judgments, not forgeable runtime constructors.

The right callback runs only after left success. The left positive pack remains owned while the right body borrows it. Q/M describe the right test's newly introduced context, not an illicit second owner of the inherited P pack. On left failure the original error and applicable negative context are retained. On right failure its error and the permitted joined context are retained. Errors after actual callback execution preserve E1, not a rolled-back E0.

For `or(C,F)`, with the same quantification and definitions, require:

```text
E0: Environment<'env>
E1: Environment<'env>
P,N,Q,M: BindingContext at their respective valid lifetimes
Failure(C): Use<[0,1]>
Success(C) = Success(D)
for each valid fresh 'b:
    F: Fn<N::BorrowArgs<'b>, Output=D, Effects=ef>
    F: RunsIn<E0, N::BorrowArgs<'b>, After=E1>
```

The result is `Carrier<Success(C),Failure(D),P & (N+Q),N+M>`, with outward row ef. It needs `Merge(N,M,N+M)` and the corresponding success projections `Project(P,P & (N+Q))` and `Project(N+Q,P & (N+Q))`, including lawful destruction of all excluded residents. The right callback runs only after left failure. A name introduced only in one successful alternative is not available in the joined positive context.

These schemas expand over exactly four nominal pairs: Result/Result, Result/BranchResult, BranchResult/Result, and BranchResult/BranchResult. A coherent source realization uses one generic And/Or implementation for each nominal left carrier, delegating associated result/context shape to ordinary helper traits keyed by the nominal pair `(C,D)`. The four pair heads are structurally disjoint. It must **not** install four impls distinguished only by potentially overlapping callback where-clauses. Result/Result gives exactly §5.3; empty borrowed context means a zero-argument callback. Each interface includes the selected family's merge/projection and guarded ownership judgments, not only its surface return type.


**Rationale.** This interface family makes mixed expressions such as a pattern test followed by an ordinary Bool predicate compositional without inventing overloaded if functions or pretending lexical binding packs are zero-argument callbacks. It is the most substantial new interface mechanism in these drafts and requires dedicated compiler conformance work; it is not claimed to follow automatically from the old Fn-only APIs.

## 6. Matching, labels, and result propagation

```glorious
pub fn match<'env,E0,E1,T,R,F,ef: EffectRow>(subject: T, cases: F) -> R / { | ef }
where
    E0: Environment<'env> + Use<[1,1]>, E1: Environment<'env>,
    F: Fn<(T,),Output=R,Effects=ef>,
    F: RunsIn<E0,(T,),After=E1>;

pub fn return<L,T>(value: T, target: L) -> !
where L: Label<T>;
pub fn break_at<L,T>(value: T, target: L) -> !
where L: Label<T>;
pub fn try<T,E,R,L>(value: Result<T,E>, target: L) -> T
where L: Label<Result<R,E>>;

pub fn try_map_error<'env,E0,E1,T,E,D,R,L,F,ef: EffectRow>(
    value: Result<T,E>, target: L, map_error: F
) -> T / { | ef }
where
    L: Label<Result<R,D>>,
    E0: Environment<'env>, E1: Environment<'env>,
    F: Fn<(E,),Output=D,Effects=ef>, F: RunsIn<E0,(E,),After=E1>;

pub fn ensure<'env,E0,E1,R,E,L,F,ef: EffectRow>(
    condition: Bool, target: L, make_error: F
) / { | ef }
where
    L: Label<Result<R,E>>,
    E0: Environment<'env>, E1: Environment<'env>,
    F: Fn<(),Output=E,Effects=ef>, F: RunsIn<E0,(),After=E1>;

pub fn some_or_leave<'env,E0,E1,T,R,L,F,ef: EffectRow>(
    value: Option<T>, target: L, fallback: F
) -> T / { | ef }
where
    L: Label<R>, E0: Environment<'env>, E1: Environment<'env>,
    F: Fn<(),Output=R,Effects=ef>, F: RunsIn<E0,(),After=E1>;
```

**Control contract.** Match invokes cases exactly once and transfers subject; every pattern-callable clause is exhaustive under the language. Return/break_at invoke the supplied label exactly once and diverge. Try invokes the label only on Err, transferring E; it returns T on Ok. Error factories/mappers run only on their selected failure path; independent skipped captures need lawful disposal. Label dependencies cannot escape, and mandatory direct-control fusion applies transitively through these helpers. No `?` propagation operator or implicit return target is added.

### 6.1 Terminal failure, recoverable reporting, and invariants

```glorious
pub effect Fail<E> { fail(E) -> ! }
pub effect Report<D> { report(D) }
pub fn catch_fail<'env,E0,E1,T,E,F,e: EffectRow>(body: F) -> Result<T,E> / { | e }
where E0: Environment<'env>, E1: Environment<'env>,
    F: Fn<(),Output=T,Effects={Fail<E> | e}>, F: RunsIn<E0,(),After=E1>;
pub fn abort(message: Str) -> !;
pub fn unreachable(message: Str) -> !;
pub fn assert(condition: Bool);
pub fn assert_message(condition: Bool, message: Str);
pub fn assert_eq<T>(left: &T, right: &T) where T: Eq + Debug;
pub fn assert_ne<T>(left: &T, right: &T) where T: Eq + Debug;
```

Fail is a terminal operation with no resumption. Report resumes exactly once and supports reporting without aborting a phase. Neither operation has a same-named forwarding function. Catch-fail invokes body once and handles Fail<E>; normal return produces Ok and a legally handled fail produces Err. Its full control contract requires all normally returning handler paths to have compatible E1, accounting for terminal cleanup and transferred E. It is not a license to cancel a body with outstanding must-move residents.

Abort terminates the current execution without source cleanup. Unreachable and failed assertions use that defined fatal behavior, not undefined behavior or an optimizer permission to assume a predicate. The public signature does not promise successful diagnostic output. These conveniences are for internal invariants, not ordinary validation of external data. Distinct assert and assert-message names avoid arity overloading.

## 7. Loop interfaces and imported control operations

### 7.1 Generative loop identity

Every ordinary loop has a fresh static label brand L, even when the user does not name it. The effect is indexed by that brand as well as the break payload B. This prevents nested loops returning the same type from sharing an accidental effect identity.

```glorious
pub effect LoopControl<L,B> where L: Label<B> {
    break(B) -> !
    continue() -> !
    continue_at(L) -> !
}
```

These are the directly imported operations; there are no forwarding functions. `break_at` remains the ordinary label helper in §6. `continue_at(@outer)` selects the explicit L from its argument. Unqualified break/continue select the nearest explicit contextual LoopControl instance under the language's general effect-instance rule; they cannot target an outer loop merely because its B fits the value.

### 7.2 Public loop declarations

```glorious
pub fn loop<'env,Env,B,F,e: EffectRow>(body: F) -> B / { | e }
where
    Env: Environment<'env>,
    for<'call,L: Label<B>> &'call mut F:
        Fn<(L,),Output=(),Effects={LoopControl<L,B> | e}>,
    for<'call,L: Label<B>> &'call mut F:
        RunsIn<&'call mut Env,(L,),After=Env>;

pub fn loop_at<'env,Env,L,B,F,e: EffectRow>(target: L, body: F) -> B / { | e }
where
    L: Label<B>, Env: Environment<'env>,
    for<'call> &'call mut F:
        Fn<(L,),Output=(),Effects={LoopControl<L,B> | e}>,
    for<'call> &'call mut F:
        RunsIn<&'call mut Env,(L,),After=Env>;

pub enum LoopStep<S,B> { Continue(S), Break(B) }

pub fn loop_state<'env,Env,S,B,F,e: EffectRow>(initial: S, body: F) -> B / { | e }
where
    Env: Environment<'env>,
    for<'call> &'call mut F:
        Fn<(S,),Output=LoopStep<S,B>,Effects=e>,
    for<'call> &'call mut F:
        RunsIn<&'call mut Env,(S,),After=Env>;
```

The higher-ranked L in loop is supplied by its fresh internal label binder, not by a runtime type generator or a new source loop keyword. Each invocation supplies that proof-only label in the argument tuple `(L,)`. A normal trailing body can leave this duplicable argument unnamed under the general contextual-block rule; an explicit `{ target => ... }` body can name it. Putting L in Args is essential: the same `Fn<()>` implementation cannot have different associated Effects for unrelated labels. Labels erase from the runtime argument layout. A contextually supplied body is checked under that abstract instance. Standalone body values must really satisfy the higher-ranked contract. Higher-ranked borrow lifetimes are confined to valid invocation regions (§2.2).

**Control contract.** Each normal completion and each matching continue starts another iteration. A matching break transfers B and returns from that loop invocation. Loop-state owns S; Continue transfers its replacement state to the next iteration, and Break transfers B. Reusable captured environment state must satisfy the backedge invariant. Terminal exits are checked separately for lawful residual ownership and cleanup. A call whose complete structural summary proves no possible normal exit has bottom behavior; absence of a convenient B inference is not permission to guess an outer loop target.

Loop-at associates the exact L with its continue handler while active. Reusing one L for nested loop-at calls targets the nearest matching active handler, not a guessed outer activation; use distinct lexical label binders for distinct named loops. A break_at call exits the label scope, which can be broader than the loop invocation. A direct local break merely returns from loop-at.

### 7.3 Tail and cleanup requirements

The library's recursive loop backedges MUST use explicit checked `tail` invocations, or be expressed through a helper whose required tail edges carry that obligation. An implementation must close/fuse iteration handlers and temporary loans before replacing an activation. It must not accumulate handler frames or heap continuation chains proportional to iteration count. The public entry wrapper need not itself be tail-called if it retains a stable owner outside the recursion engine.

No implementation body is prescribed here. In particular, the earlier experimental `tail loop_run(...)` inside every handler arm is not endorsed without proof that no handler, capture, reference, or completion transformation remains live across the backedge.

### 7.4 Additional traversal control

```glorious
pub fn repeat_n<'env,Env,F,e: EffectRow>(count: usize, body: &mut F) / { | e }
where
    Env: Environment<'env>,
    for<'call> &'call mut F: Fn<(usize,),Output=(),Effects=e>,
    for<'call> &'call mut F: RunsIn<&'call mut Env,(usize,),After=Env>;

pub fn while_do<'env,Env,C,F,ec: EffectRow,ef: EffectRow>(
    condition: &mut C, body: &mut F
) / { | ec,ef }
where
    Env: Environment<'env>,
    for<'call> &'call mut C: Fn<(),Output=Bool,Effects=ec>,
    for<'call> &'call mut C: RunsIn<&'call mut Env,(),After=Env>,
    for<'call> &'call mut F: Fn<(),Output=(),Effects=ef>,
    for<'call> &'call mut F: RunsIn<&'call mut Env,(),After=Env>;
```

Repeat-n invokes body once per index in `[0,count)`, unless a propagated nonlocal exit interrupts it. While-do evaluates condition before each body invocation and terminates on false. It introduces no new break protocol; callers use loop/loop_at for that behavior. Both callbacks are ordinary values, not eagerly evaluated conditions disguised by a special parser rule.

## 8. Result interfaces

```glorious
impl<T,E> Result<T,E> {
    pub fn is_ok(value: &Self) -> Bool;
    pub fn is_err(value: &Self) -> Bool;
    pub fn as_refs<'a>(value: &'a Self) -> Result<&'a T,&'a E>;
    pub fn as_muts<'a>(value: &'a mut Self) -> Result<&'a mut T,&'a mut E>;
    pub fn ok(value: Self) -> Option<T> where E: Use<[0,1]>;
    pub fn err(value: Self) -> Option<E> where T: Use<[0,1]>;
    pub fn swap(value: Self) -> Result<E,T>;
    pub fn contains(value: &Self, expected: &T) -> Bool where T: Eq;
    pub fn contains_err(value: &Self, expected: &E) -> Bool where E: Eq;
    pub fn unwrap_or(value: Self, fallback: T) -> T
        where T: Use<[0,1]>, E: Use<[0,1]>;
    pub fn unwrap_or_default(value: Self) -> T where T: Default, E: Use<[0,1]>;
    pub fn expect(value: Self, message: Str) -> T where E: Debug;
    pub fn expect_err(value: Self, message: Str) -> E where T: Debug;

    pub fn map<'env,E0,E1,U,F,ef: EffectRow>(value: Self, transform: F)
        -> Result<U,E> / { | ef }
        where E0: Environment<'env>, E1: Environment<'env>,
              F: Fn<(T,),Output=U,Effects=ef>, F: RunsIn<E0,(T,),After=E1>;
    pub fn map_err<'env,E0,E1,D,F,ef: EffectRow>(value: Self, transform: F)
        -> Result<T,D> / { | ef }
        where E0: Environment<'env>, E1: Environment<'env>,
              F: Fn<(E,),Output=D,Effects=ef>, F: RunsIn<E0,(E,),After=E1>;
    pub fn and_then<'env,E0,E1,U,F,ef: EffectRow>(value: Self, transform: F)
        -> Result<U,E> / { | ef }
        where E0: Environment<'env>, E1: Environment<'env>,
              F: Fn<(T,),Output=Result<U,E>,Effects=ef>,
              F: RunsIn<E0,(T,),After=E1>;
    pub fn or_else<'env,E0,E1,D,F,ef: EffectRow>(value: Self, transform: F)
        -> Result<T,D> / { | ef }
        where E0: Environment<'env>, E1: Environment<'env>,
              F: Fn<(E,),Output=Result<T,D>,Effects=ef>,
              F: RunsIn<E0,(E,),After=E1>;
    pub fn unwrap_or_else<'env,E0,E1,F,ef: EffectRow>(value: Self, fallback: F)
        -> T / { | ef }
        where E0: Environment<'env>, E1: Environment<'env>,
              F: Fn<(E,),Output=T,Effects=ef>, F: RunsIn<E0,(E,),After=E1>;
    pub fn fold<'env,E0,E1,R,F,G,ef: EffectRow,eg: EffectRow>(
        value: Self, success: F, failure: G
    ) -> R / { | ef,eg }
        where E0: Environment<'env> + Use<[1,1]>, E1: Environment<'env>,
              F: Fn<(T,),Output=R,Effects=ef>, F: RunsIn<E0,(T,),After=E1>,
              G: Fn<(E,),Output=R,Effects=eg>, G: RunsIn<E0,(E,),After=E1>;
    pub fn map_both<'env,E0,E1,U,D,F,G,ef: EffectRow,eg: EffectRow>(
        value: Self, success: F, failure: G
    ) -> Result<U,D> / { | ef,eg }
        where E0: Environment<'env> + Use<[1,1]>, E1: Environment<'env>,
              F: Fn<(T,),Output=U,Effects=ef>, F: RunsIn<E0,(T,),After=E1>,
              G: Fn<(E,),Output=D,Effects=eg>, G: RunsIn<E0,(E,),After=E1>;
    pub fn inspect<'env,Env,F,ef: EffectRow>(value: Self, observer: &mut F)
        -> Self / { | ef }
        where Env: Environment<'env>,
              for<'a> &'a mut F: Fn<(&'a T,),Output=(),Effects=ef>,
              for<'a> &'a mut F: RunsIn<&'a mut Env,(&'a T,),After=Env>;
    pub fn inspect_err<'env,Env,F,ef: EffectRow>(value: Self, observer: &mut F)
        -> Self / { | ef }
        where Env: Environment<'env>,
              for<'a> &'a mut F: Fn<(&'a E,),Output=(),Effects=ef>,
              for<'a> &'a mut F: RunsIn<&'a mut Env,(&'a E,),After=Env>;
    pub fn is_ok_and<'env,Env,F,ef: EffectRow>(value: &Self, predicate: &mut F)
        -> Bool / { | ef }
        where Env: Environment<'env>,
              for<'a> &'a mut F: Fn<(&'a T,),Output=Bool,Effects=ef>,
              for<'a> &'a mut F: RunsIn<&'a mut Env,(&'a T,),After=Env>;
    pub fn is_err_and<'env,Env,F,ef: EffectRow>(value: &Self, predicate: &mut F)
        -> Bool / { | ef }
        where Env: Environment<'env>,
              for<'a> &'a mut F: Fn<(&'a E,),Output=Bool,Effects=ef>,
              for<'a> &'a mut F: RunsIn<&'a mut Env,(&'a E,),After=Env>;
}

impl<T,E> Result<Result<T,E>,E> {
    pub fn flatten(value: Self) -> Result<T,E>;
}
impl<T,E,D> Result<Result<T,E>,D> {
    pub fn transpose(value: Self) -> Result<Result<T,D>,E>;
}
impl<'a,T,E> Result<&'a T,E> {
    pub fn copied(value: Self) -> Result<T,E> where T: Use<[0,*]>;
    pub fn cloned(value: Self) -> Result<T,E> where T: Clone;
}
impl<'a,T,E> Result<T,&'a E> {
    pub fn copied_err(value: Self) -> Result<T,E> where E: Use<[0,*]>;
    pub fn cloned_err(value: Self) -> Result<T,E> where E: Clone;
}

pub enum ZipFailure<T,U,E,D> {
    LeftFailed { error: E, right: U },
    RightFailed { left: T, error: D },
    BothFailed { left: E, right: D },
}
pub fn zip_lossless<T,U,E,D>(left: Result<T,E>, right: Result<U,D>)
    -> Result<(T,U),ZipFailure<T,U,E,D>>;
pub fn unzip_result<A,B,E>(value: Result<(A,B),E>) -> (Result<A,E>,Result<B,E>)
    where E: Use<[0,*]>;
pub fn unzip_result_cloned<A,B,E>(value: Result<(A,B),E>) -> (Result<A,E>,Result<B,E>)
    where E: Clone;
```

**Control contract.** Map/and_then invoke their transform exactly once on Ok and zero times on Err; map_err/or_else reverse those paths. Unwrap-or-else passes the error rather than discarding it. Fold/map-both invoke exactly one correlated callback and require compatible normal post-states; their row is the union, not an equality. Inspect/predicates borrow a matching payload at most once and preserve resident ownership. Any unused owning callback and residual capture are handled under §2.5; plain Result returns cannot escape unresolved guarded environments.

Expect/expect-err terminate through abort on the wrong variant, not a catchable exception. They are inappropriate validation paths for untrusted input. Transpose uses the equations `Ok(Ok(t)) -> Ok(Ok(t))`, `Ok(Err(e)) -> Err(e)`, `Err(d) -> Ok(Err(d))`; it does not discard either failure type.

## 9. Option and Bool interfaces

Option inherits nonconflicting Result operations at its transparent instantiation. It does not introduce a second Eq/Hash/Clone implementation. Option-specific borrowed projection names differ from generic Result's plural names because `&()` is not `()`.

```glorious
impl<T> Option<T> {
    pub fn is_some(value: &Self) -> Bool;
    pub fn is_none(value: &Self) -> Bool;
    pub fn as_ref<'a>(value: &'a Self) -> Option<&'a T>;
    pub fn as_mut<'a>(value: &'a mut Self) -> Option<&'a mut T>;
    pub fn take(target: &mut Self) -> Self;
    pub fn replace(target: &mut Self, value: T) -> Self;
    pub fn insert(target: &mut Self, value: T) -> Self;
    pub fn get_or_insert<'a>(target: &'a mut Self, value: T) -> &'a mut T
        where T: Use<[0,1]>;
    pub fn insert_or_return<'a>(target: &'a mut Self, value: T) -> (&'a mut T,Option<T>);
    pub fn get_or_insert_default<'a>(target: &'a mut Self) -> &'a mut T where T: Default;
    pub fn ok_or<E>(value: Self, error: E) -> Result<T,E> where E: Use<[0,1]>;

    pub fn get_or_insert_with<'a,'env,E0,E1,F,ef: EffectRow>(target: &'a mut Self, make: F)
        -> &'a mut T / { | ef }
        where E0: Environment<'env>, E1: Environment<'env>,
              F: Fn<(),Output=T,Effects=ef>, F: RunsIn<E0,(),After=E1>;
    pub fn ok_or_else<'env,E0,E1,E,F,ef: EffectRow>(value: Self, make_error: F)
        -> Result<T,E> / { | ef }
        where E0: Environment<'env>, E1: Environment<'env>,
              F: Fn<(),Output=E,Effects=ef>, F: RunsIn<E0,(),After=E1>;
    pub fn filter<'env,Env,F,ef: EffectRow>(value: Self, predicate: &mut F)
        -> Self / { | ef }
        where T: Use<[0,1]>, Env: Environment<'env>,
              for<'a> &'a mut F: Fn<(&'a T,),Output=Bool,Effects=ef>,
              for<'a> &'a mut F: RunsIn<&'a mut Env,(&'a T,),After=Env>;
    pub fn classify<'env,Env,F,ef: EffectRow>(value: Self, predicate: &mut F)
        -> Option<Result<T,T>> / { | ef }
        where Env: Environment<'env>,
              for<'a> &'a mut F: Fn<(&'a T,),Output=Bool,Effects=ef>,
              for<'a> &'a mut F: RunsIn<&'a mut Env,(&'a T,),After=Env>;
    pub fn take_if<'env,Env,F,ef: EffectRow>(target: &mut Self, predicate: &mut F)
        -> Self / { | ef }
        where Env: Environment<'env>,
              for<'a> &'a mut F: Fn<(&'a mut T,),Output=Bool,Effects=ef>,
              for<'a> &'a mut F: RunsIn<&'a mut Env,(&'a mut T,),After=Env>;
}

pub fn zip_option<A,B>(left: Option<A>, right: Option<B>) -> Option<(A,B)>
where A: Use<[0,1]>, B: Use<[0,1]>;
pub fn zip_option_lossless<A,B>(left: Option<A>, right: Option<B>)
    -> Result<(A,B),(Option<A>,Option<B>)>;
pub fn unzip_option<A,B>(value: Option<(A,B)>) -> (Option<A>,Option<B>);

impl Bool {
    pub fn parse(text: Str) -> Option<Bool>;
    pub fn to_u8(value: Bool) -> u8;
    pub fn from_u8(value: u8) -> Option<Bool>;
    pub fn xor(left: Bool, right: Bool) -> Bool;
    pub fn equivalent(left: Bool, right: Bool) -> Bool;
}
```

Take leaves None. Replace/insert return the complete previous option without discarding T. Insert-or-return returns None for the unused-value result when inserted, Some(incoming) when already occupied. Factories run only when empty. Filter destroys a rejected T and therefore requires affine T; classify returns it in Err instead. Take-if runs at most once and leaves a rejected resident in place, including predicate mutations already made.

Bool parsing recognizes exactly `true` and `false`, without trimming or case folding. Thus parse(false-text) is `Some(false)`: success of parsing is not the truth of the parsed payload. From-u8 accepts only 0/1. There is no general numeric/string truthiness conversion.

## 10. Ordering, ranges, and bounded values

```glorious
impl Ordering {
    pub fn reverse(value: Self) -> Self;
    pub fn is_less(value: Self) -> Bool;
    pub fn is_equal(value: Self) -> Bool;
    pub fn is_greater(value: Self) -> Bool;
    pub fn then(left: Self, right: Self) -> Self;
    pub fn then_with<'env,E0,E1,F,ef: EffectRow>(left: Self, right: F) -> Self / { | ef }
        where E0: Environment<'env>, E1: Environment<'env>,
              F: Fn<(),Output=Self,Effects=ef>, F: RunsIn<E0,(),After=E1>;
}
pub fn min<T>(left: T, right: T) -> T where T: Ord + Use<[0,1]>;
pub fn max<T>(left: T, right: T) -> T where T: Ord + Use<[0,1]>;
pub fn min_ref<'a,T>(left: &'a T, right: &'a T) -> &'a T where T: Ord;
pub fn max_ref<'a,T>(left: &'a T, right: &'a T) -> &'a T where T: Ord;
pub fn clamp<T>(value: T, low: T, high: T) -> Result<T,(T,T,T)>
    where T: Ord + Use<[0,1]>;

pub enum RangeError { Reversed, OutOfBounds, Overflow }
pub enum StringRangeError { Reversed, OutOfBounds, NotCharBoundary }
pub struct BoundsError { pub index: usize, pub length: usize }
pub struct CapacityError { pub requested: usize }

impl Range<usize> {
    pub fn len(value: &Self) -> usize;
    pub fn is_empty(value: &Self) -> Bool;
    pub fn contains(value: &Self, index: usize) -> Bool;
    pub fn checked(value: Self, length: usize) -> Result<Self,RangeError>;
    pub fn intersection(left: Self, right: Self) -> Option<Self>;
    pub fn checked_offset(value: Self, delta: isize) -> Result<Self,RangeError>;
    pub fn split_at(value: Self, relative: usize) -> Result<(Self,Self),RangeError>;
}

pub struct NonZero<T>;
```

Range is half-open. Its public endpoints need not be ordered: len saturates at zero and is_empty is true when start ≥ end, while checked structural consumers diagnose Reversed before OutOfBounds. Range arithmetic checks before addition/subtraction. Intersection returns None for no nonempty overlap. Min/max are left-biased on ties; clamp rejects low > high and returns all three inputs in the error.

NonZero is supplied for each concrete integer type only, with private representation and `new(T)->Option<NonZero<T>>`, `get(&NonZero<T>)->T`, and `into_inner(NonZero<T>)->T`. The family does not grant wrapping conversions that could construct zero. Bounds are checked before creating the invariant-bearing wrapper.

## 11. Numeric scalar families

### 11.1 Family expansion and scalar traits

The integer family below expands for each of `u8,u16,u32,u64,u128,usize,i8,i16,i32,i64,i128,isize`. In the declarations, `I` denotes one such concrete type, `U` its same-width unsigned counterpart, and `N` its bit width. `F` later denotes one of f32/f64, with `Bits` u32/u64 respectively. These are enumerated interface families, not unconstrained nominal Int/Float types.

Every applicable scalar implements Eq, Ord, Hash, Clone, Default, Display, Debug, and the applicable independent operator traits. Default integer/float is positive zero. No operation silently promotes operands to a different scalar type.

### 11.2 Integer namespace interface

```glorious
impl I {
    pub fn min_value() -> I;
    pub fn max_value() -> I;
    pub fn bits() -> u32;
    pub fn checked_add(left: I, right: I) -> Option<I>;
    pub fn checked_sub(left: I, right: I) -> Option<I>;
    pub fn checked_mul(left: I, right: I) -> Option<I>;
    pub fn checked_div(left: I, right: I) -> Option<I>;
    pub fn checked_rem(left: I, right: I) -> Option<I>;
    pub fn checked_neg(value: I) -> Option<I>;
    pub fn checked_pow(value: I, exponent: u32) -> Option<I>;
    pub fn checked_shl(value: I, count: u32) -> Option<I>;
    pub fn checked_shr(value: I, count: u32) -> Option<I>;
    pub fn checked_next_power_of_two(value: I) -> Option<I>;
    pub fn checked_div_euclid(left: I, right: I) -> Option<I>;
    pub fn checked_rem_euclid(left: I, right: I) -> Option<I>;
    pub fn wrapping_add(left: I, right: I) -> I;
    pub fn wrapping_sub(left: I, right: I) -> I;
    pub fn wrapping_mul(left: I, right: I) -> I;
    pub fn wrapping_neg(value: I) -> I;
    pub fn wrapping_pow(value: I, exponent: u32) -> I;
    pub fn wrapping_shl(value: I, count: u32) -> I;
    pub fn wrapping_shr(value: I, count: u32) -> I;
    pub fn saturating_add(left: I, right: I) -> I;
    pub fn saturating_sub(left: I, right: I) -> I;
    pub fn saturating_mul(left: I, right: I) -> I;
    pub fn saturating_pow(value: I, exponent: u32) -> I;
    pub fn overflowing_add(left: I, right: I) -> (I,Bool);
    pub fn overflowing_sub(left: I, right: I) -> (I,Bool);
    pub fn overflowing_mul(left: I, right: I) -> (I,Bool);
    pub fn overflowing_neg(value: I) -> (I,Bool);
    pub fn count_ones(value: I) -> u32;
    pub fn count_zeros(value: I) -> u32;
    pub fn leading_zeros(value: I) -> u32;
    pub fn trailing_zeros(value: I) -> u32;
    pub fn leading_ones(value: I) -> u32;
    pub fn trailing_ones(value: I) -> u32;
    pub fn rotate_left(value: I, count: u32) -> I;
    pub fn rotate_right(value: I, count: u32) -> I;
    pub fn reverse_bits(value: I) -> I;
    pub fn swap_bytes(value: I) -> I;
    pub fn is_power_of_two(value: I) -> Bool;
    pub fn abs_diff(left: I, right: I) -> U;
    pub fn checked_ilog(value: I, base: I) -> Option<u32>;
    pub fn checked_ilog2(value: I) -> Option<u32>;
    pub fn checked_ilog10(value: I) -> Option<u32>;
    pub fn parse(text: Str) -> Result<I,IntParseError>;
    pub fn parse_radix(text: Str, radix: u32) -> Result<I,IntParseError>;
    pub fn format_radix(value: I, radix: u32) -> Result<String,RadixError>;
    pub fn to_le_bytes(value: I) -> [u8; N/8];
    pub fn to_be_bytes(value: I) -> [u8; N/8];
    pub fn from_le_bytes(value: [u8; N/8]) -> I;
    pub fn from_be_bytes(value: [u8; N/8]) -> I;
}
```

For signed I additionally provide `checked_abs(I)->Option<I>`, `wrapping_abs(I)->I`, `saturating_abs(I)->I`, `unsigned_abs(I)->U`, `signum(I)->I`, `is_negative(I)->Bool`, and `is_positive(I)->Bool`. Negative inputs to checked logarithms/power-of-two rounding fail where no nonnegative result exists. Unsigned `checked_neg` succeeds only for zero; wrapping_neg is modulo 2^N.

Ordinary integer operators trap on overflow or invalid division; their behavior is not debug/release dependent. Checked operations detect exceptional cases before invoking a trapping leaf. Div/rem truncate toward zero; Euclidean remainder is nonnegative and strictly below the divisor magnitude. Both divide-by-zero and signed minimum divided by −1 are invalid checked/trapping cases. Checked shifts validate count < N; they are not a checked multiplication by 2^count. Wrapping shifts/rotations reduce counts modulo N. Signed right shift sign-extends.

`overflowing_*` returns the wrapped value and whether the exact result was outside the representable range. Zero bit counts return N for leading/trailing zeros and zero for leading/trailing ones as appropriate. `checked_next_power_of_two(0)` returns one. Radix is 2–36; no trimming, separators, or prefixes are accepted by parse_radix unless explicitly handled by a distinct parser. Parse errors carry byte offsets and kinds, not preformatted strings.

### 11.3 Conversions

As<T> is supplied for every pair among the twelve integers and two float types: 196 pairs. Integer-to-integer is modulo destination width with destination signedness. Integer-to-float rounds directly to destination precision, nearest ties-to-even. f32-to-f64 preserves finite values exactly; narrowing rounds. Float-to-integer truncates toward zero, saturates at destination bounds, and maps NaN to zero.

TryAs<T> scalar instances return ConversionError. Integer-to-integer requires exact representability. Integer-to-float and finite float narrowing permit rounding but reject overflow to infinity; float widening preserves finite values. Float-to-float preserves infinities/signed zero and canonicalizes NaNs. Checked float-to-integer requires finite x in the target's half-open mathematical interval `[MIN, MAX+1)` and then truncates toward zero; for unsigned targets MIN is zero. Thus a negative fraction is rejected for an unsigned target even if truncation alone would produce zero. This retains the prior checked-input policy rather than silently treating it as As saturation.

ExactAs rejects fractional float-to-integer inputs and any finite precision loss in other scalar conversions. Infinity may convert to the same-signed floating infinity; canonical NaN may convert between float widths as canonical NaN; neither converts exactly to an integer. The separately named `exact_convert` function therefore differs from both checked representability and As lossiness.

The canonical conversion interface is as/try_as/exact_convert. Width-explicit names such as `checked_<S>_to_<T>` and `wrapping_convert_to_<T>` are superseded, not additional exports or a required compatibility module. Migrate callers and tests to the selected signatures and policies; an alias cannot change Option into Result.

No As implementation converts arbitrary u32 to char, pointers to references, or numbers to truth. Char-to-u32 and u8-to-char are total explicitly supported conversions; validating other scalar values uses checked constructors.

### 11.4 Floating namespace interface

```glorious
impl F {
    pub fn zero() -> F;
    pub fn one() -> F;
    pub fn infinity() -> F;
    pub fn neg_infinity() -> F;
    pub fn nan() -> F;
    pub fn epsilon() -> F;
    pub fn min_positive_normal() -> F;
    pub fn max_finite() -> F;
    pub fn to_bits(value: F) -> Bits;
    pub fn from_bits(value: Bits) -> F;
    pub fn classify(value: F) -> FloatClass;
    pub fn is_nan(value: F) -> Bool;
    pub fn is_infinite(value: F) -> Bool;
    pub fn is_finite(value: F) -> Bool;
    pub fn is_normal(value: F) -> Bool;
    pub fn is_subnormal(value: F) -> Bool;
    pub fn is_sign_negative(value: F) -> Bool;
    pub fn abs(value: F) -> F;
    pub fn copysign(value: F, sign: F) -> F;
    pub fn floor(value: F) -> F;
    pub fn ceil(value: F) -> F;
    pub fn trunc(value: F) -> F;
    pub fn round_ties_even(value: F) -> F;
    pub fn fract(value: F) -> F;
    pub fn next_up(value: F) -> F;
    pub fn next_down(value: F) -> F;
    pub fn ieee_eq(left: F, right: F) -> Bool;
    pub fn ieee_ne(left: F, right: F) -> Bool;
    pub fn ieee_lt(left: F, right: F) -> Bool;
    pub fn ieee_le(left: F, right: F) -> Bool;
    pub fn ieee_gt(left: F, right: F) -> Bool;
    pub fn ieee_ge(left: F, right: F) -> Bool;
    pub fn ieee_partial_cmp(left: F, right: F) -> Option<Ordering>;
    pub fn total_cmp(left: F, right: F) -> Ordering;
    pub fn min_num(left: F, right: F) -> F;
    pub fn max_num(left: F, right: F) -> F;
    pub fn mul_add(value: F, multiplier: F, addend: F) -> F;
    pub fn parse(text: Str) -> Result<F,FloatParseError>;
    pub fn format_shortest(value: F) -> String;
    pub fn format_exact(value: F) -> String;
    pub fn approximately_equal(left: F, right: F, tolerance: Tolerance<F>) -> Result<Bool,ToleranceError>;
}
pub enum FloatClass { Zero, Subnormal, Normal, Infinite, Nan }
pub struct Tolerance<F> { pub absolute: F, pub relative: F }
```

Canonical NaNs are positive quiet NaNs. Bit constructors/views canonicalize NaNs and preserve signed zero. Eq/Ord/Hash use the same canonical-bit policy: NaN is reflexive, −0 differs from +0, and the total order is negative infinity, negative finite, −0, +0, positive finite, positive infinity, canonical NaN. Scalar comparison operators use that coherent trait policy. Named IEEE comparisons treat NaN as unordered and the zeros as equal. The ordinary PartialOrd instance is consistent with Ord/Eq; `ieee_partial_cmp` deliberately uses the distinct numeric policy.

Floating arithmetic preserves defined IEEE behavior and canonicalizes NaNs. No implicit fast math. Mul-add performs one rounded fused operation where the target advertises it or an exactly equivalent implementation. Min-num/max-num choose the numeric operand when exactly one input is NaN and use −0/+0 tie policy consistently with numeric minimum/maximum. Approximate comparison rejects negative/nonfinite tolerances. It returns false for a NaN operand, true for IEEE-equal operands (including equal infinities and the two zeros), and false for the other cases involving infinity. For unequal finite operands it tests the mathematical inequality `abs(a-b) <= max(absolute, relative*max(abs(a),abs(b)))` on the exact values represented by the supplied floats, without letting an overflowing intermediate spuriously make the test true. It is not Eq and not a map key equivalence.

Display/Debug use the same locale-independent format-exact representation. NaN is `nan`; infinities are `inf`/`-inf`; zeros are `0e+0`/`-0e+0`. A nonzero finite value uses a sign only when negative, one decimal digit before the point, enough following digits to represent its exact binary rational with no redundant trailing zero, and `e` plus an explicit exponent sign and unpadded decimal exponent. The point is omitted when there is no fractional digit; for example 1.5 is `1.5e+0`.

Format-shortest uses the same normalized scientific syntax with the fewest significant decimal digits that round-trip at the original width. Ties select the decimal closest to the exact value, then the lexicographically first spelling. Parse accepts an optional sign, decimal significand and optional exponent, plus the exact special-value spellings above; it consumes the entire input and does not trim whitespace. Invalid separators or trailing bytes are errors. Parsing is directly at the destination precision with ties-to-even. Extended transcendental math is outside the mandatory scalar profile until its precision/reproducibility contract is separately versioned.

## 12. Characters, ASCII, and UTF-8

```glorious
pub enum Utf8ErrorKind { InvalidLead, InvalidContinuation, Overlong, Surrogate, OutOfRange, Truncated }
pub struct Utf8Error { pub valid_up_to: usize, pub error_length: Option<usize>, pub kind: Utf8ErrorKind }
pub struct ScalarError { pub code_point: u32 }

impl char {
    pub fn from_u32(value: u32) -> Result<char,ScalarError>;
    pub fn to_u32(value: char) -> u32;
    pub fn is_valid_scalar(value: u32) -> Bool;
    pub fn len_utf8(value: char) -> usize;
    pub fn encode_utf8(value: char, out: &mut [u8;4]) -> usize;
    pub fn decode_utf8(bytes: Slice<u8>) -> Result<(char,usize),Utf8Error>;
    pub fn is_ascii(value: char) -> Bool;
    pub fn is_ascii_alphabetic(value: char) -> Bool;
    pub fn is_ascii_alphanumeric(value: char) -> Bool;
    pub fn is_ascii_digit(value: char) -> Bool;
    pub fn is_ascii_hexdigit(value: char) -> Bool;
    pub fn is_ascii_lowercase(value: char) -> Bool;
    pub fn is_ascii_uppercase(value: char) -> Bool;
    pub fn is_ascii_whitespace(value: char) -> Bool;
    pub fn is_ascii_control(value: char) -> Bool;
    pub fn is_ascii_punctuation(value: char) -> Bool;
    pub fn to_ascii_lowercase(value: char) -> char;
    pub fn to_ascii_uppercase(value: char) -> char;
    pub fn to_digit(value: char, radix: u32) -> Option<u32>;
    pub fn from_digit(value: u32, radix: u32) -> Option<char>;
    pub fn escape_default(value: char) -> CharEscape;
    pub fn escape_unicode(value: char) -> CharEscape;
}

pub struct CharEscape;
impl CharEscape {
    pub fn next(value: &mut Self) -> Option<char>;
}

pub fn validate_utf8(bytes: Slice<u8>) -> Result<(),Utf8Error>;
pub fn utf8_valid_prefix(bytes: Slice<u8>) -> usize;
pub fn str_from_utf8<'a>(bytes: Slice<'a,u8>) -> Result<Str<'a>,Utf8Error>;
pub fn ascii_eq_ignore_case(left: Slice<u8>, right: Slice<u8>) -> Bool;
pub fn ascii_lowercase_in_place(bytes: SliceMut<u8>);
pub fn ascii_uppercase_in_place(bytes: SliceMut<u8>);
```

UTF-8 validation rejects overlong encodings, surrogate code points, and values beyond the scalar range. Error offsets refer to the lead byte of the malformed sequence; truncation has no complete invalid-sequence length. Validation never obtains failure by catching a VM trap. Encoding writes only the required prefix and returns its length. Decode-UTF8 reads one scalar and reports the number of bytes consumed; empty input is Truncated.

ASCII classification and case conversion are locale-independent. Case conversion leaves non-ASCII scalars/bytes unchanged. Digit conversion uses ASCII 0–9/a–z/A–Z and radix 2–36. No Unicode normalization, grapheme segmentation, locale, or identifier database is implied by these APIs.

## 13. Borrowed text and owned String

```glorious
pub struct Str<'a>;
pub struct String;
pub struct Chars<'a>;
pub struct CharIndices<'a>;
pub struct Lines<'a>;
pub struct Split<'a,'p>;
pub struct SplitAsciiWhitespace<'a>;

impl<'a> Str<'a> {
    pub fn len(value: Self) -> usize;
    pub fn len_bytes(value: Self) -> usize;
    pub fn is_empty(value: Self) -> Bool;
    pub fn as_bytes(value: Self) -> Slice<'a,u8>;
    pub fn chars(value: Self) -> Chars<'a>;
    pub fn char_indices(value: Self) -> CharIndices<'a>;
    pub fn lines(value: Self) -> Lines<'a>;
    pub fn is_char_boundary(value: Self, index: usize) -> Bool;
    pub fn slice(value: Self, range: Range<usize>) -> Result<Self,StringRangeError>;
    pub fn split_at(value: Self, index: usize) -> Result<(Self,Self),StringRangeError>;
    pub fn char_at(value: Self, byte_index: usize) -> Result<char,StringRangeError>;
    pub fn starts_with(value: Self, prefix: Str) -> Bool;
    pub fn ends_with(value: Self, suffix: Str) -> Bool;
    pub fn contains(value: Self, needle: Str) -> Bool;
    pub fn find(value: Self, needle: Str) -> Option<usize>;
    pub fn rfind(value: Self, needle: Str) -> Option<usize>;
    pub fn find_char(value: Self, needle: char) -> Option<usize>;
    pub fn rfind_char(value: Self, needle: char) -> Option<usize>;
    pub fn strip_prefix(value: Self, prefix: Str) -> Option<Self>;
    pub fn strip_suffix(value: Self, suffix: Str) -> Option<Self>;
    pub fn split_once(value: Self, separator: Str) -> Option<(Self,Self)>;
    pub fn rsplit_once(value: Self, separator: Str) -> Option<(Self,Self)>;
    pub fn split<'p>(value: Self, separator: Str<'p>) -> Split<'a,'p>;
    pub fn split_ascii_whitespace(value: Self) -> SplitAsciiWhitespace<'a>;
    pub fn trim_ascii(value: Self) -> Self;
    pub fn trim_ascii_start(value: Self) -> Self;
    pub fn trim_ascii_end(value: Self) -> Self;
    pub fn eq_ignore_ascii_case(value: Self, other: Str) -> Bool;
    pub fn to_string(value: Self) -> String;
    pub fn try_to_string(value: Self) -> Result<String,ReserveError>;
    pub fn repeat(value: Self, count: usize) -> Result<String,ReserveError>;
    pub fn replace(value: Self, pattern: Str, replacement: Str) -> Result<String,ReserveError>;
}

impl String {
    pub fn new() -> Self;
    pub fn with_capacity(capacity: usize) -> Self;
    pub fn try_with_capacity(capacity: usize) -> Result<Self,ReserveError>;
    pub fn len(value: &Self) -> usize;
    pub fn capacity(value: &Self) -> usize;
    pub fn is_empty(value: &Self) -> Bool;
    pub fn as_str<'a>(value: &'a Self) -> Str<'a>;
    pub fn as_bytes<'a>(value: &'a Self) -> Slice<'a,u8>;
    pub fn into_bytes(value: Self) -> Vec<u8>;
    pub fn from_utf8(bytes: Vec<u8>) -> Result<Self,Utf8Error>;
    pub fn from_utf8_recover(bytes: Vec<u8>) -> Result<Self,Rejected<Vec<u8>,Utf8Error>>;
    pub fn from_utf8_lossy(bytes: Slice<u8>) -> Self;
    pub fn reserve(value: &mut Self, additional: usize);
    pub fn try_reserve(value: &mut Self, additional: usize) -> Result<(),ReserveError>;
    pub fn shrink_to_fit(value: &mut Self);
    pub fn clear(value: &mut Self);
    pub fn push(value: &mut Self, character: char);
    pub fn try_push(value: &mut Self, character: char) -> Result<(),ReserveError>;
    pub fn push_str(value: &mut Self, text: Str);
    pub fn try_push_str(value: &mut Self, text: Str) -> Result<(),ReserveError>;
    pub fn pop(value: &mut Self) -> Option<char>;
    pub fn insert(value: &mut Self, byte_index: usize, text: Str) -> Result<(),StringEditError>;
    pub fn remove(value: &mut Self, byte_index: usize) -> Result<char,StringRangeError>;
    pub fn truncate(value: &mut Self, byte_length: usize) -> Result<(),StringRangeError>;
    pub fn split_off(value: &mut Self, byte_index: usize) -> Result<Self,StringEditError>;
    pub fn drain(value: &mut Self, range: Range<usize>) -> Result<Self,StringEditError>;
    pub fn replace_range(value: &mut Self, range: Range<usize>, text: Str) -> Result<(),StringEditError>;
    pub fn make_ascii_lowercase(value: &mut Self);
    pub fn make_ascii_uppercase(value: &mut Self);
}

impl<'a> Chars<'a> {
    pub fn next(value: &mut Self) -> Option<char>;
    pub fn next_back(value: &mut Self) -> Option<char>;
    pub fn remaining(value: &Self) -> Str<'a>;
}
impl<'a> CharIndices<'a> {
    pub fn next(value: &mut Self) -> Option<(usize,char)>;
    pub fn next_back(value: &mut Self) -> Option<(usize,char)>;
}
impl<'a> Lines<'a> { pub fn next(value: &mut Self) -> Option<Str<'a>>; }
impl<'a,'p> Split<'a,'p> { pub fn next(value: &mut Self) -> Option<Str<'a>>; }
impl<'a> SplitAsciiWhitespace<'a> { pub fn next(value: &mut Self) -> Option<Str<'a>>; }

pub fn join_strings(values: Slice<Str>, separator: Str) -> Result<String,ReserveError>;
```

String is affine owned growable UTF-8. Str is an immutable borrowed validated UTF-8 view; its lifetime is not extended by passing it by value. Mutating String cannot invalidate an outstanding Str loan. There is no safe mutable-byte view of String. All text indices/ranges are byte offsets; slicing checks reversal, bounds, then scalar boundaries in that order.

Empty substring search finds the start for find and the end for rfind. Split with an empty separator yields leading/trailing empties and individual scalar slices, never interior UTF-8 byte fragments. Lines split LF and CRLF, strip those terminators, treat a lone CR as content, and do not emit a trailing empty line merely for a final terminator. ASCII-whitespace splitting omits empty fields.

Lossy conversion replaces each maximal malformed subsequence under a fixed documented UTF-8 decoding policy with U+FFFD. From-UTF8-recover returns the original buffer on validation failure; the shorter from-UTF8 may discard it because u8 is duplicable/affine. Mutable edit validation failures leave the string unchanged; allocation failures also preserve its valid original contents.

## 14. Fixed arrays and borrowed slices

```glorious
pub struct Slice<'a,T>;
pub struct SliceMut<'a,T>;
pub struct SliceIter<'a,T>;
pub struct SliceIterMut<'a,T>;
pub struct Chunks<'a,T>;
pub struct Windows<'a,T>;

impl<'a,T> Slice<'a,T> {
    pub fn len(value: Self) -> usize;
    pub fn is_empty(value: Self) -> Bool;
    pub fn get(value: Self, index: usize) -> Option<&'a T>;
    pub fn index(value: Self, index: usize) -> &'a T;
    pub fn first(value: Self) -> Option<&'a T>;
    pub fn last(value: Self) -> Option<&'a T>;
    pub fn split_first(value: Self) -> Option<(&'a T,Self)>;
    pub fn split_last(value: Self) -> Option<(Self,&'a T)>;
    pub fn slice(value: Self, range: Range<usize>) -> Result<Self,RangeError>;
    pub fn subslice(value: Self, start: usize, length: usize) -> Result<Self,RangeError>;
    pub fn split_at(value: Self, index: usize) -> Result<(Self,Self),RangeError>;
    pub fn iter(value: Self) -> SliceIter<'a,T>;
    pub fn chunks(value: Self, size: NonZero<usize>) -> Chunks<'a,T>;
    pub fn windows(value: Self, size: NonZero<usize>) -> Windows<'a,T>;
    pub fn starts_with(value: Self, prefix: Slice<T>) -> Bool where T: Eq;
    pub fn ends_with(value: Self, suffix: Slice<T>) -> Bool where T: Eq;
    pub fn contains(value: Self, needle: &T) -> Bool where T: Eq;
    pub fn position(value: Self, needle: &T) -> Option<usize> where T: Eq;
    pub fn compare(value: Self, other: Slice<T>) -> Ordering where T: Ord;
    pub fn to_vec(value: Self) -> Vec<T> where T: Clone;
    pub fn copied_to_vec(value: Self) -> Vec<T> where T: Use<[0,*]>;
}

impl<'a,T> SliceMut<'a,T> {
    pub fn len(value: &Self) -> usize;
    pub fn is_empty(value: &Self) -> Bool;
    pub fn as_slice<'b>(value: &'b Self) -> Slice<'b,T>;
    pub fn reborrow<'b>(value: &'b mut Self) -> SliceMut<'b,T>;
    pub fn into_shared(value: Self) -> Slice<'a,T>;
    pub fn get<'b>(value: &'b Self, index: usize) -> Option<&'b T>;
    pub fn get_mut<'b>(value: &'b mut Self, index: usize) -> Option<&'b mut T>;
    pub fn index_mut<'b>(value: &'b mut Self, index: usize) -> &'b mut T;
    pub fn split_at(value: Self, index: usize) -> Result<(Self,Self),Rejected<Self,RangeError>>;
    pub fn slice(value: Self, range: Range<usize>) -> Result<Self,Rejected<Self,RangeError>>;
    pub fn split_first(value: Self) -> Result<(&'a mut T,Self),Self>;
    pub fn split_last(value: Self) -> Result<(Self,&'a mut T),Self>;
    pub fn iter(value: Self) -> SliceIterMut<'a,T>;
    pub fn swap(value: &mut Self, left: usize, right: usize) -> Result<(),BoundsError>;
    pub fn reverse(value: &mut Self);
    pub fn rotate_left(value: &mut Self, count: usize) -> Result<(),BoundsError>;
    pub fn rotate_right(value: &mut Self, count: usize) -> Result<(),BoundsError>;
    pub fn copy_from_slice(value: &mut Self, source: Slice<T>) -> Result<(),LengthError>
        where T: Use<[0,*]>;
    pub fn clone_from_slice(value: &mut Self, source: Slice<T>) -> Result<(),LengthError>
        where T: Clone + Use<[0,1]>;
    pub fn swap_with_slice(value: &mut Self, other: &mut Self) -> Result<(),LengthError>;
    pub fn fill(value: &mut Self, element: T) where T: Use<[0,*]>;
}

impl<'a,T> SliceIter<'a,T> {
    pub fn next(value: &mut Self) -> Option<&'a T>;
    pub fn next_back(value: &mut Self) -> Option<&'a T>;
    pub fn remaining(value: &Self) -> Slice<'a,T>;
    pub fn len(value: &Self) -> usize;
}
impl<'a,T> SliceIterMut<'a,T> {
    pub fn next(value: &mut Self) -> Option<&'a mut T>;
    pub fn next_back(value: &mut Self) -> Option<&'a mut T>;
    pub fn into_remaining(value: Self) -> SliceMut<'a,T>;
}
impl<'a,T> Chunks<'a,T> { pub fn next(value: &mut Self) -> Option<Slice<'a,T>>; }
impl<'a,T> Windows<'a,T> { pub fn next(value: &mut Self) -> Option<Slice<'a,T>>; }

pub fn array_as_slice<'a,T,const N: usize>(value: &'a [T;N]) -> Slice<'a,T>;
pub fn array_as_mut_slice<'a,T,const N: usize>(value: &'a mut [T;N]) -> SliceMut<'a,T>;
pub fn array_into_vec<T,const N: usize>(value: [T;N]) -> Vec<T>;
pub fn array_try_from_vec<T,const N: usize>(value: Vec<T>) -> Result<[T;N],Vec<T>>;
pub fn array_from_fn<'env,Env,T,F,const N: usize,e: EffectRow>(body: &mut F)
    -> [T;N] / { | e }
where Env: Environment<'env>,
    for<'call> &'call mut F: Fn<(usize,),Output=T,Effects=e>,
    for<'call> &'call mut F: RunsIn<&'call mut Env,(usize,),After=Env>;
```

Index/index-mut are explicitly trapping; get/get-mut are checked. Slice values carry owner loans, not element copies. Mutable splitting consumes one unique view and produces disjoint windows. Mut-iteration can yield long-lived unique element references only because each element is yielded at most once and all retained windows are disjoint. Overlapping mutable windows require a separate lending interface; no ordinary Iterator implementation is promised for them.

Array-from-fn invokes body in increasing index order, once per element. Any nonlocal callback exit must account for the already constructed residents; exact-linear partial initialization is not silently cleaned. Array conversion failure returns the complete input owner.

## 15. Vec ownership and mutation

```glorious
pub struct Vec<T>;
pub struct VecIntoIter<T>;

impl<T> Vec<T> {
    pub fn new() -> Self;
    pub fn with_capacity(capacity: usize) -> Self;
    pub fn try_with_capacity(capacity: usize) -> Result<Self,ReserveError>;
    pub fn len(value: &Self) -> usize;
    pub fn capacity(value: &Self) -> usize;
    pub fn is_empty(value: &Self) -> Bool;
    pub fn reserve(value: &mut Self, additional: usize);
    pub fn try_reserve(value: &mut Self, additional: usize) -> Result<(),ReserveError>;
    pub fn shrink_to_fit(value: &mut Self);
    pub fn as_slice<'a>(value: &'a Self) -> Slice<'a,T>;
    pub fn as_mut_slice<'a>(value: &'a mut Self) -> SliceMut<'a,T>;
    pub fn get<'a>(value: &'a Self, index: usize) -> Option<&'a T>;
    pub fn get_mut<'a>(value: &'a mut Self, index: usize) -> Option<&'a mut T>;
    pub fn index<'a>(value: &'a Self, index: usize) -> &'a T;
    pub fn index_mut<'a>(value: &'a mut Self, index: usize) -> &'a mut T;
    pub fn first<'a>(value: &'a Self) -> Option<&'a T>;
    pub fn last<'a>(value: &'a Self) -> Option<&'a T>;
    pub fn first_mut<'a>(value: &'a mut Self) -> Option<&'a mut T>;
    pub fn last_mut<'a>(value: &'a mut Self) -> Option<&'a mut T>;
    pub fn push(value: &mut Self, item: T);
    pub fn try_push(value: &mut Self, item: T) -> Result<(),Rejected<T,ReserveError>>;
    pub fn pop(value: &mut Self) -> Option<T>;
    pub fn insert(value: &mut Self, index: usize, item: T) -> Result<(),Rejected<T,BoundsError>>;
    pub fn try_insert(value: &mut Self, index: usize, item: T) -> Result<(),Rejected<T,InsertError>>;
    pub fn remove(value: &mut Self, index: usize) -> Option<T>;
    pub fn swap_remove(value: &mut Self, index: usize) -> Option<T>;
    pub fn replace(value: &mut Self, index: usize, item: T) -> Result<T,Rejected<T,BoundsError>>;
    pub fn swap(value: &mut Self, left: usize, right: usize) -> Result<(),BoundsError>;
    pub fn reverse(value: &mut Self);
    pub fn rotate_left(value: &mut Self, count: usize) -> Result<(),BoundsError>;
    pub fn rotate_right(value: &mut Self, count: usize) -> Result<(),BoundsError>;
    pub fn append(value: &mut Self, source: Self);
    pub fn try_append(value: &mut Self, source: Self) -> Result<(),Rejected<Self,ReserveError>>;
    pub fn split_off(value: &mut Self, index: usize) -> Result<Self,BoundsError>;
    pub fn drain(value: &mut Self, range: Range<usize>) -> Result<Self,RangeError>;
    pub fn clear(value: &mut Self) where T: Use<[0,1]>;
    pub fn truncate(value: &mut Self, length: usize) where T: Use<[0,1]>;
    pub fn resize(value: &mut Self, length: usize, fill: T) where T: Use<[0,*]>;
    pub fn extend_from_slice(value: &mut Self, source: Slice<T>) where T: Use<[0,*]>;
    pub fn extend_cloned(value: &mut Self, source: Slice<T>) where T: Clone;
    pub fn iter<'a>(value: &'a Self) -> SliceIter<'a,T>;
    pub fn iter_mut<'a>(value: &'a mut Self) -> SliceIterMut<'a,T>;
    pub fn into_iter(value: Self) -> VecIntoIter<T>;
    pub fn finish_empty(value: Self) -> Result<(),Self>;

    pub fn resize_with<'env,Env,F,e: EffectRow>(value: &mut Self, length: usize, make: &mut F)
        / { | e }
        where T: Use<[0,1]>, Env: Environment<'env>,
              for<'call> &'call mut F: Fn<(),Output=T,Effects=e>,
              for<'call> &'call mut F: RunsIn<&'call mut Env,(),After=Env>;
    pub fn retain<'env,Env,F,e: EffectRow>(value: &mut Self, predicate: &mut F) / { | e }
        where T: Use<[0,1]>, Env: Environment<'env>,
              for<'call> &'call mut F: Fn<(&'call T,),Output=Bool,Effects=e>,
              for<'call> &'call mut F: RunsIn<&'call mut Env,(&'call T,),After=Env>;
    pub fn partition_by<'env,Env,F,e: EffectRow>(value: &mut Self, predicate: &mut F)
        -> usize / { | e }
        where Env: Environment<'env>,
              for<'call> &'call mut F: Fn<(&'call T,),Output=Bool,Effects=e>,
              for<'call> &'call mut F: RunsIn<&'call mut Env,(&'call T,),After=Env>;
    pub fn partition<'env,Env,F,e: EffectRow>(value: Self, predicate: &mut F)
        -> (Self,Self) / { | e }
        where Env: Environment<'env>,
              for<'call> &'call mut F: Fn<(&'call T,),Output=Bool,Effects=e>,
              for<'call> &'call mut F: RunsIn<&'call mut Env,(&'call T,),After=Env>;
    pub fn extract_if<'env,Env,F,e: EffectRow>(value: &mut Self, predicate: &mut F)
        -> Self / { | e }
        where Env: Environment<'env>,
              for<'call> &'call mut F: Fn<(&'call T,),Output=Bool,Effects=e>,
              for<'call> &'call mut F: RunsIn<&'call mut Env,(&'call T,),After=Env>;
}

impl<T> VecIntoIter<T> {
    pub fn step(value: Self) -> Step<T,Self>;
    pub fn remaining_len(value: &Self) -> usize;
    pub fn into_remaining(value: Self) -> Vec<T>;
}
```

All positions below len are initialized at every safe call boundary. Moves/removals/drains/append transfer residents. Destroying a resident vector requires T affine; a nonempty Vec<Linear> and its owning iterator cannot be abandoned. Even an empty value whose static type retains a linear obligation needs a consuming finish/step operation to prove it empty rather than a generic drop loophole.

Append preserves source order and transfers the source's entire ownership. Checked drain validates the complete range and returns an owned Vec of removed elements; there is no partially abandoned borrowing drain iterator in this core API. Partition-by is in-place and returns the first index of the false partition without a stability promise. Consuming partition and extract-if preserve every resident, so no discard bound is required. Retain destroys rejects and does require affine T.

On recoverable validation/allocation failure the functions returning Rejected preserve their unused item/source. Callback failure through a nonlocal effect is governed by the language cleanup contract, not an invented rollback guarantee. Callback predicates execute at most once per inspected element unless the specific algorithm contract says otherwise. Growth policy and backing-memory implementation are private.

## 16. Queues, stacks, and heaps

```glorious
pub struct VecDeque<T>;
pub struct BinaryHeap<T>;
pub type Stack<T> = Vec<T>;
pub type WorkList<T> = VecDeque<T>;

impl<T> VecDeque<T> {
    pub fn new() -> Self;
    pub fn with_capacity(capacity: usize) -> Self;
    pub fn try_with_capacity(capacity: usize) -> Result<Self,ReserveError>;
    pub fn len(value: &Self) -> usize;
    pub fn capacity(value: &Self) -> usize;
    pub fn is_empty(value: &Self) -> Bool;
    pub fn reserve(value: &mut Self, additional: usize);
    pub fn try_reserve(value: &mut Self, additional: usize) -> Result<(),ReserveError>;
    pub fn push_front(value: &mut Self, item: T);
    pub fn push_back(value: &mut Self, item: T);
    pub fn pop_front(value: &mut Self) -> Option<T>;
    pub fn pop_back(value: &mut Self) -> Option<T>;
    pub fn front<'a>(value: &'a Self) -> Option<&'a T>;
    pub fn back<'a>(value: &'a Self) -> Option<&'a T>;
    pub fn front_mut<'a>(value: &'a mut Self) -> Option<&'a mut T>;
    pub fn back_mut<'a>(value: &'a mut Self) -> Option<&'a mut T>;
    pub fn get<'a>(value: &'a Self, index: usize) -> Option<&'a T>;
    pub fn get_mut<'a>(value: &'a mut Self, index: usize) -> Option<&'a mut T>;
    pub fn insert(value: &mut Self, index: usize, item: T) -> Result<(),Rejected<T,BoundsError>>;
    pub fn remove(value: &mut Self, index: usize) -> Option<T>;
    pub fn swap(value: &mut Self, left: usize, right: usize) -> Result<(),BoundsError>;
    pub fn rotate_left(value: &mut Self, count: usize) -> Result<(),BoundsError>;
    pub fn rotate_right(value: &mut Self, count: usize) -> Result<(),BoundsError>;
    pub fn append(value: &mut Self, other: Self);
    pub fn split_off(value: &mut Self, index: usize) -> Result<Self,BoundsError>;
    pub fn as_slices<'a>(value: &'a Self) -> (Slice<'a,T>,Slice<'a,T>);
    pub fn into_vec(value: Self) -> Vec<T>;
    pub fn from_vec(value: Vec<T>) -> Self;
    pub fn clear(value: &mut Self) where T: Use<[0,1]>;
    pub fn finish_empty(value: Self) -> Result<(),Self>;
}

impl<T> BinaryHeap<T> where T: Ord {
    pub fn new() -> Self;
    pub fn with_capacity(capacity: usize) -> Self;
    pub fn len(value: &Self) -> usize;
    pub fn is_empty(value: &Self) -> Bool;
    pub fn peek<'a>(value: &'a Self) -> Option<&'a T>;
    pub fn push(value: &mut Self, item: T);
    pub fn pop(value: &mut Self) -> Option<T>;
    pub fn replace_top(value: &mut Self, item: T) -> Option<T>;
    pub fn from_vec(value: Vec<T>) -> Self;
    pub fn into_vec(value: Self) -> Vec<T>;
    pub fn into_sorted_vec(value: Self) -> Vec<T>;
    pub fn clear(value: &mut Self) where T: Use<[0,1]>;
}
```

Deque endpoint push/pop is amortized constant time; logical iteration is front-to-back independent of split backing views. Stack and WorkList are aliases rather than parallel collection representations. BinaryHeap is max-oriented; into-sorted-vec returns ascending order. Replace-top inserts into an empty heap and otherwise transfers the old maximum. Public APIs cannot lend mutable access to a heap key without a contract that reestablishes ordering.

## 17. Hash maps, sets, and entries

```glorious
pub struct HashMap<K,V>;
pub struct HashSet<T>;
pub struct MapIter<'a,K,V>;
pub struct MapKeys<'a,K,V>;
pub struct MapValues<'a,K,V>;
pub struct MapValuesMut<'a,K,V>;
pub struct MapIntoIter<K,V>;
pub struct SetIter<'a,T>;

pub enum InsertOutcome<K,V> {
    Inserted,
    Replaced { unused_key: K, old_value: V },
}
pub enum Entry<'a,K,V> { Occupied(OccupiedEntry<'a,K,V>), Vacant(VacantEntry<'a,K,V>) }
pub enum EntryOutcome<'a,K,V> {
    Occupied { entry: OccupiedEntry<'a,K,V>, unused_key: K },
    Vacant(VacantEntry<'a,K,V>),
}
pub struct OccupiedEntry<'a,K,V>;
pub struct VacantEntry<'a,K,V>;

impl<K,V> HashMap<K,V> where K: Eq + Hash {
    pub fn new() -> Self;
    pub fn with_capacity(capacity: usize) -> Self;
    pub fn try_with_capacity(capacity: usize) -> Result<Self,ReserveError>;
    pub fn len(value: &Self) -> usize;
    pub fn capacity(value: &Self) -> usize;
    pub fn is_empty(value: &Self) -> Bool;
    pub fn reserve(value: &mut Self, additional: usize);
    pub fn try_reserve(value: &mut Self, additional: usize) -> Result<(),ReserveError>;
    pub fn contains_key(value: &Self, key: &K) -> Bool;
    pub fn get<'a>(value: &'a Self, key: &K) -> Option<&'a V>;
    pub fn get_mut<'a>(value: &'a mut Self, key: &K) -> Option<&'a mut V>;
    pub fn get_key_value<'a>(value: &'a Self, key: &K) -> Option<(&'a K,&'a V)>;
    pub fn insert(value: &mut Self, key: K, item: V) -> Option<V> where K: Use<[0,1]>;
    pub fn insert_lossless(value: &mut Self, key: K, item: V) -> InsertOutcome<K,V>;
    pub fn try_insert_lossless(value: &mut Self, key: K, item: V)
        -> Result<InsertOutcome<K,V>,Rejected<(K,V),ReserveError>>;
    pub fn insert_if_absent(value: &mut Self, key: K, item: V) -> Result<(),(K,V)>;
    pub fn remove(value: &mut Self, key: &K) -> Option<V> where K: Use<[0,1]>;
    pub fn remove_entry(value: &mut Self, key: &K) -> Option<(K,V)>;
    pub fn entry<'a>(value: &'a mut Self, key: K) -> Entry<'a,K,V> where K: Use<[0,1]>;
    pub fn entry_lossless<'a>(value: &'a mut Self, key: K) -> EntryOutcome<'a,K,V>;
    pub fn clear(value: &mut Self) where K: Use<[0,1]>, V: Use<[0,1]>;
    pub fn drain(value: &mut Self) -> Vec<(K,V)>;
    pub fn iter<'a>(value: &'a Self) -> MapIter<'a,K,V>;
    pub fn keys<'a>(value: &'a Self) -> MapKeys<'a,K,V>;
    pub fn values<'a>(value: &'a Self) -> MapValues<'a,K,V>;
    pub fn values_mut<'a>(value: &'a mut Self) -> MapValuesMut<'a,K,V>;
    pub fn into_iter(value: Self) -> MapIntoIter<K,V>;
    pub fn into_entries(value: Self) -> Vec<(K,V)>;
    pub fn finish_empty(value: Self) -> Result<(),Self>;
}

impl<'a,K,V> OccupiedEntry<'a,K,V> where K: Eq + Hash {
    pub fn key<'b>(value: &'b Self) -> &'b K;
    pub fn get<'b>(value: &'b Self) -> &'b V;
    pub fn get_mut<'b>(value: &'b mut Self) -> &'b mut V;
    pub fn into_mut(value: Self) -> &'a mut V;
    pub fn replace(value: &mut Self, replacement: V) -> V;
    pub fn remove_entry(value: Self) -> (K,V);
}
impl<'a,K,V> VacantEntry<'a,K,V> where K: Eq + Hash {
    pub fn key<'b>(value: &'b Self) -> &'b K;
    pub fn into_key(value: Self) -> K;
    pub fn insert(value: Self, item: V) -> &'a mut V;
    pub fn try_insert(value: Self, item: V)
        -> Result<&'a mut V,Rejected<(Self,V),ReserveError>>;
}
impl<'a,K,V> Entry<'a,K,V> where K: Eq + Hash {
    pub fn or_insert(value: Self, item: V) -> &'a mut V where V: Use<[0,1]>;
    pub fn or_insert_default(value: Self) -> &'a mut V where V: Default;
    pub fn or_insert_with<'env,E0,E1,F,e: EffectRow>(value: Self, make: F)
        -> &'a mut V / { | e }
        where E0: Environment<'env>, E1: Environment<'env>,
              F: Fn<(),Output=V,Effects=e>, F: RunsIn<E0,(),After=E1>;
}

impl<T> HashSet<T> where T: Eq + Hash {
    pub fn new() -> Self;
    pub fn with_capacity(capacity: usize) -> Self;
    pub fn len(value: &Self) -> usize;
    pub fn capacity(value: &Self) -> usize;
    pub fn is_empty(value: &Self) -> Bool;
    pub fn reserve(value: &mut Self, additional: usize);
    pub fn try_reserve(value: &mut Self, additional: usize) -> Result<(),ReserveError>;
    pub fn contains(value: &Self, item: &T) -> Bool;
    pub fn get<'a>(value: &'a Self, item: &T) -> Option<&'a T>;
    pub fn insert(value: &mut Self, item: T) -> Bool where T: Use<[0,1]>;
    pub fn insert_or_return(value: &mut Self, item: T) -> Option<T>;
    pub fn replace(value: &mut Self, item: T) -> Option<T>;
    pub fn remove(value: &mut Self, item: &T) -> Bool where T: Use<[0,1]>;
    pub fn take(value: &mut Self, item: &T) -> Option<T>;
    pub fn clear(value: &mut Self) where T: Use<[0,1]>;
    pub fn drain(value: &mut Self) -> Vec<T>;
    pub fn iter<'a>(value: &'a Self) -> SetIter<'a,T>;
    pub fn into_vec(value: Self) -> Vec<T>;
    pub fn is_subset(value: &Self, other: &Self) -> Bool;
    pub fn is_superset(value: &Self, other: &Self) -> Bool;
    pub fn is_disjoint(value: &Self, other: &Self) -> Bool;
    pub fn union_refs<'a>(value: &'a Self, other: &'a Self) -> Vec<&'a T>;
    pub fn intersection_refs<'a>(value: &'a Self, other: &'a Self) -> Vec<&'a T>;
    pub fn difference_refs<'a>(value: &'a Self, other: &'a Self) -> Vec<&'a T>;
    pub fn symmetric_difference_refs<'a>(value: &'a Self, other: &'a Self) -> Vec<&'a T>;
}

impl<'a,K,V> MapIter<'a,K,V> { pub fn next(value: &mut Self) -> Option<(&'a K,&'a V)>; }
impl<'a,K,V> MapKeys<'a,K,V> { pub fn next(value: &mut Self) -> Option<&'a K>; }
impl<'a,K,V> MapValues<'a,K,V> { pub fn next(value: &mut Self) -> Option<&'a V>; }
impl<'a,K,V> MapValuesMut<'a,K,V> { pub fn next(value: &mut Self) -> Option<&'a mut V>; }
impl<K,V> MapIntoIter<K,V> {
    pub fn step(value: Self) -> Step<(K,V),Self>;
    pub fn into_remaining(value: Self) -> HashMap<K,V>;
}
impl<'a,T> SetIter<'a,T> { pub fn next(value: &mut Self) -> Option<&'a T>; }
```

Insert-lossless retains the resident key when replacing an equal-key entry and returns the unused incoming key plus old V. Insert-if-absent returns the entire uninserted pair on collision. Map removal without the key needs affine K; remove-entry does not. Set insertion returns true only for a new member; insert-or-return returns the duplicate input instead of discarding it. Set replace installs the new representative and returns the old equal representative.

A vacant entry owns its candidate key and must be inserted, converted back into that key, or legally destroyed. An occupied entry does not let the caller mutate key equality/hash while resident. Entry-factory callbacks run only on vacancy. The map loan remains live, so factories cannot alias the same map through an independent capture.

Map/set hash behavior is deterministic for a fixed declared library version, but table order is unspecified. Expected lookup/insertion complexity is not a worst-case guarantee under collisions. Bounded compiler-facing variants must expose/charge logical work rather than hide an unbounded collision loop behind one “step.”

### 17.1 Borrowed heterogeneous lookup

```glorious
pub trait Equivalent<K>: Hash {
    fn equivalent(query: &Self, key: &K) -> Bool;
}
impl<K,V> HashMap<K,V> where K: Eq + Hash {
    pub fn get_equiv<'a,Q>(value: &'a Self, query: &Q) -> Option<&'a V>
        where Q: Equivalent<K>;
    pub fn get_equiv_mut<'a,Q>(value: &'a mut Self, query: &Q) -> Option<&'a mut V>
        where Q: Equivalent<K>;
    pub fn remove_equiv_entry<Q>(value: &mut Self, query: &Q) -> Option<(K,V)>
        where Q: Equivalent<K>;
}
impl<T> HashSet<T> where T: Eq + Hash {
    pub fn get_equiv<'a,Q>(value: &'a Self, query: &Q) -> Option<&'a T>
        where Q: Equivalent<T>;
    pub fn take_equiv<Q>(value: &mut Self, query: &Q) -> Option<T>
        where Q: Equivalent<T>;
}
```

Equivalent is an ordinary safe trait: equivalent queries/keys must produce compatible hash streams. Str provides Equivalent<String>, permitting lookup without constructing an owned String. Violating its law may miss an entry or produce unspecified logical lookup results, never memory unsafety. No cached-hash input is accepted as a safe proof of membership or resident provenance.

## 18. Iterator, owning stepper, and lending interfaces

### 18.1 Separate ownership shapes

```glorious
pub trait Iterator {
    type Item;
    type Effects: EffectRow;
    fn next(value: &mut Self) -> Option<Self::Item> / { | Self::Effects };
    fn size_hint(value: &Self) -> (usize,Option<usize>);
}
pub trait DoubleEndedIterator: Iterator {
    fn next_back(value: &mut Self) -> Option<Self::Item> / { | Self::Effects };
}
pub trait ExactSizeIterator: Iterator {
    fn len(value: &Self) -> usize;
}
pub trait FusedIterator: Iterator {}

pub enum Step<T,I> { Yield { item: T, rest: I }, Done }
pub trait OwnedStepper {
    type Item;
    type Effects: EffectRow;
    fn step(value: Self) -> Step<Self::Item,Self> / { | Self::Effects };
}
pub trait LendingIterator {
    type Item<'a> where Self: 'a;
    type Effects: EffectRow;
    fn next<'a>(value: &'a mut Self) -> Option<Self::Item<'a>> / { | Self::Effects };
}
```

A normal Iterator retains its owner and yields one item or absence. OwnedStepper consumes its current state and either transfers the next state with an item or finalizes an empty owner. LendingIterator ties each result to the current borrow and can express mutually exclusive mutable windows. They are not interchangeable protocols.

A None result does not by itself consume or make an owning iterator discardable. FusedIterator promises subsequent None results after the first None; ordinary Iterator does not. Size-hint lower/upper bounds must be truthful, but safe code must not use a user implementation's lie as an unsafe allocation/write proof.

### 18.2 Adapter types and full callback evidence

```glorious
pub struct Enumerate<I>;
pub struct Rev<I>;
pub struct Chain<I,J>;
pub struct Take<I>;
pub struct Skip<I>;
pub struct Peekable<I>;
pub struct Fuse<I>;
pub struct Zip<I,J>;
pub struct Map<'env,Env,I,F>;
pub struct Inspect<'env,Env,I,F>;
pub struct Filter<'env,Env,I,F>;
pub struct FilterMap<'env,Env,I,F>;
pub struct Scan<'env,Env,I,S,F>;

pub fn enumerate<I>(source: I) -> Enumerate<I> where I: Iterator;
pub fn rev<I>(source: I) -> Rev<I> where I: DoubleEndedIterator;
pub fn chain<I,J>(first: I, second: J) -> Chain<I,J>
    where I: Iterator, J: Iterator<Item=I::Item>;
pub fn take_iter<I>(source: I, count: usize) -> Take<I> where I: Iterator;
pub fn skip_iter<I>(source: I, count: usize) -> Skip<I>
    where I: Iterator, I::Item: Use<[0,1]>;
pub fn peekable<I>(source: I) -> Peekable<I> where I: Iterator;
pub fn fuse<I>(source: I) -> Fuse<I> where I: Iterator;
pub fn zip<I,J>(left: I, right: J) -> Zip<I,J> where I: Iterator, J: Iterator;

pub fn map_iter<'env,Env,I,F,U,e: EffectRow>(source: I, transform: F) -> Map<'env,Env,I,F>
where I: Iterator, Env: Environment<'env>,
    for<'call> &'call mut F: Fn<(I::Item,),Output=U,Effects=e>,
    for<'call> &'call mut F: RunsIn<&'call mut Env,(I::Item,),After=Env>;
pub fn inspect_iter<'env,Env,I,F,e: EffectRow>(source: I, observer: F) -> Inspect<'env,Env,I,F>
where I: Iterator, Env: Environment<'env>,
    for<'call> &'call mut F: Fn<(&'call I::Item,),Output=(),Effects=e>,
    for<'call> &'call mut F: RunsIn<&'call mut Env,(&'call I::Item,),After=Env>;
pub fn filter_iter<'env,Env,I,F,e: EffectRow>(source: I, predicate: F) -> Filter<'env,Env,I,F>
where I: Iterator, I::Item: Use<[0,1]>, Env: Environment<'env>,
    for<'call> &'call mut F: Fn<(&'call I::Item,),Output=Bool,Effects=e>,
    for<'call> &'call mut F: RunsIn<&'call mut Env,(&'call I::Item,),After=Env>;
pub fn filter_map_iter<'env,Env,I,F,U,e: EffectRow>(source: I, transform: F) -> FilterMap<'env,Env,I,F>
where I: Iterator, Env: Environment<'env>,
    for<'call> &'call mut F: Fn<(I::Item,),Output=Option<U>,Effects=e>,
    for<'call> &'call mut F: RunsIn<&'call mut Env,(I::Item,),After=Env>;
pub fn scan_iter<'env,Env,I,S,F,U,e: EffectRow>(source: I, state: S, step: F) -> Scan<'env,Env,I,S,F>
where I: Iterator, Env: Environment<'env>,
    for<'call> &'call mut F: Fn<(&'call mut S,I::Item),Output=Option<U>,Effects=e>,
    for<'call> &'call mut F: RunsIn<&'call mut Env,(&'call mut S,I::Item),After=Env>;
```

Adapter construction stores/transfers inputs but invokes no callback and performs no source-iteration effects. Their Iterator implementation has Effects equal to the union of underlying iterator rows and callback rows, and Item as implied by the declarations. Map transforms each yielded item once. Filter observes each candidate once and destroys rejects. Filter-map transfers each candidate into its callback, whose own ownership contract must account for it even on None. Scan retains S and stops output after its callback returns None.

### 18.3 Remainders and buffered ownership

```glorious
impl<I> Enumerate<I> { pub fn into_parts(value: Self) -> (I,usize); }
impl<I> Rev<I> { pub fn into_inner(value: Self) -> I; }
impl<I,J> Chain<I,J> { pub fn into_parts(value: Self) -> (I,J); }
impl<I> Take<I> { pub fn into_parts(value: Self) -> (I,usize); }
impl<I> Skip<I> { pub fn into_parts(value: Self) -> (I,usize); }
impl<I> Fuse<I> { pub fn into_inner(value: Self) -> I; }
impl<I> Peekable<I> where I: Iterator {
    pub fn peek<'a>(value: &'a mut Self) -> Option<&'a I::Item> / { | I::Effects };
    pub fn into_parts(value: Self) -> (I,Option<I::Item>);
}
impl<I,J> Zip<I,J> where I: Iterator, J: Iterator {
    pub fn into_parts(value: Self) -> (I,J,Option<I::Item>,Option<J::Item>);
}
impl<'env,Env,I,F> Map<'env,Env,I,F> { pub fn into_parts(value: Self) -> (I,F); }
impl<'env,Env,I,F> Inspect<'env,Env,I,F> { pub fn into_parts(value: Self) -> (I,F); }
impl<'env,Env,I,F> Filter<'env,Env,I,F> { pub fn into_parts(value: Self) -> (I,F); }
impl<'env,Env,I,F> FilterMap<'env,Env,I,F> { pub fn into_parts(value: Self) -> (I,F); }
impl<'env,Env,I,S,F> Scan<'env,Env,I,S,F> { pub fn into_parts(value: Self) -> (I,S,F); }
```

Zip may pull an item from one side before discovering the other side is exhausted; it must retain that unmatched item, not silently destroy it. Into-parts returns every buffer and remaining source. Adapter destruction requires discardability of all owned sources/callbacks/state/buffers. A borrowed callback's lifetime dependence also survives storage; no adapter factory extends it.

### 18.4 Consumers and partial progress

```glorious
pub struct FoldFailure<I,A,E> { pub rest: I, pub state: A, pub error: E }
pub struct FindOutcome<I,T> { pub found: Option<T>, pub rest: I }

pub fn fold_iter<'env,Env,I,A,F,e: EffectRow>(source: I, initial: A, step: &mut F)
    -> A / { | I::Effects,e }
where I: Iterator + Use<[0,1]>, Env: Environment<'env>,
    for<'call> &'call mut F: Fn<(A,I::Item),Output=A,Effects=e>,
    for<'call> &'call mut F: RunsIn<&'call mut Env,(A,I::Item),After=Env>;

pub fn try_fold_iter<'env,Env,I,A,E,F,e: EffectRow>(source: I, initial: A, step: &mut F)
    -> Result<A,FoldFailure<I,A,E>> / { | I::Effects,e }
where I: Iterator + Use<[0,1]>, Env: Environment<'env>,
    for<'call> &'call mut F: Fn<(A,I::Item),Output=Result<A,(A,E)>,Effects=e>,
    for<'call> &'call mut F: RunsIn<&'call mut Env,(A,I::Item),After=Env>;

pub fn fold_steps<'env,Env,I,A,F,e: EffectRow>(source: I, initial: A, step: &mut F)
    -> A / { | I::Effects,e }
where I: OwnedStepper, Env: Environment<'env>,
    for<'call> &'call mut F: Fn<(A,I::Item),Output=A,Effects=e>,
    for<'call> &'call mut F: RunsIn<&'call mut Env,(A,I::Item),After=Env>;

pub fn collect_vec<I>(source: I) -> Vec<I::Item> / { | I::Effects }
where I: OwnedStepper;
pub fn count_iter<I>(source: I) -> usize / { | I::Effects }
where I: Iterator + Use<[0,1]>, I::Item: Use<[0,1]>;
```

Fold-iter consumes every yielded item, but requires an affine iterator owner so the exhausted retained state may be closed. Fold-steps instead finalizes its source through Done and supports exact-linear sources. Try-fold returns the state and unprocessed iterator on the first callback Err; the failed item was transferred into that callback and must be accounted for by its result or authorized deconstruction, not magically reconstructed. General nonlocal effects still obey the full cleanup contract.

## 19. Traversal, search, ordering, and sequence algorithms

### 19.1 Borrowed traversals

```glorious
pub fn each<'a,'env,Env,T,F,e: EffectRow>(items: Slice<'a,T>, body: &mut F) / { | e }
where Env: Environment<'env>,
    for<'call> &'call mut F: Fn<(&'a T,),Output=(),Effects=e>,
    for<'call> &'call mut F: RunsIn<&'call mut Env,(&'a T,),After=Env>;
pub fn each_indexed<'a,'env,Env,T,F,e: EffectRow>(items: Slice<'a,T>, body: &mut F) / { | e }
where Env: Environment<'env>,
    for<'call> &'call mut F: Fn<(usize,&'a T),Output=(),Effects=e>,
    for<'call> &'call mut F: RunsIn<&'call mut Env,(usize,&'a T),After=Env>;
pub fn fold_slice<'a,'env,Env,T,A,F,e: EffectRow>(items: Slice<'a,T>, initial: A, step: &mut F)
    -> A / { | e }
where Env: Environment<'env>,
    for<'call> &'call mut F: Fn<(A,&'a T),Output=A,Effects=e>,
    for<'call> &'call mut F: RunsIn<&'call mut Env,(A,&'a T),After=Env>;
pub fn map_collect<'a,'env,Env,T,U,F,e: EffectRow>(items: Slice<'a,T>, map: &mut F)
    -> Vec<U> / { | e }
where Env: Environment<'env>,
    for<'call> &'call mut F: Fn<(&'a T,),Output=U,Effects=e>,
    for<'call> &'call mut F: RunsIn<&'call mut Env,(&'a T,),After=Env>;
pub fn find_map<'a,'env,Env,T,U,F,e: EffectRow>(items: Slice<'a,T>, map: &mut F)
    -> Option<U> / { | e }
where Env: Environment<'env>,
    for<'call> &'call mut F: Fn<(&'a T,),Output=Option<U>,Effects=e>,
    for<'call> &'call mut F: RunsIn<&'call mut Env,(&'a T,),After=Env>;
```

Each/fold/map-collect visit in increasing index order; find-map stops on the first Some. All partial output owners must be accounted for if a callback exits nonlocally. No callback is duplicated merely because it is called many times.

### 19.2 Predicate family, fully quantified

For each member in the following table, the declaration has the explicit common binders and bounds shown immediately below it. `Output` is replaced by that row's concrete type and the function name by the listed name; this is a finite declaration family, not an unresolved output type.

| Function | Output | Stopping/result rule |
|---|---|---|
| `all` | Bool | First false; empty is true. |
| `any` | Bool | First true; empty is false. |
| `count_where` | usize | Count all true results. |
| `position` | Option<usize> | First true index. |
| `rposition` | Option<usize> | Last true index, traversing from the end. |
| `find` | Option<&'a T> | First true resident borrow. |
| `find_unique` | UniqueMatch<&'a T> | Stop once a second true resident proves ambiguity. |
| `filter_refs` | Vec<&'a T> | Borrow all matching residents in order. |
| `partition_refs` | (Vec<&'a T>,Vec<&'a T>) | Preserve both partitions in source order. |

```glorious
pub fn NAME<'a,'env,Env,T,F,e: EffectRow>(items: Slice<'a,T>, predicate: &mut F)
    -> OUTPUT / { | e }
where Env: Environment<'env>,
    for<'call> &'call mut F: Fn<(&'a T,),Output=Bool,Effects=e>,
    for<'call> &'call mut F: RunsIn<&'call mut Env,(&'a T,),After=Env>;
pub enum UniqueMatch<T> { Missing, Unique(T), Ambiguous(T,T) }
```

The fallible predicate family `try_all`, `try_any`, `try_position`, and `try_find` uses the same input and environment bounds, adds E, changes callback Output to `Result<Bool,E>`, and returns `Result<OUT,E>` for OUT respectively Bool, Bool, Option<usize>, Option<&'a T>. It stops on the first Err. `Ok(false)` is not an error and must not be flattened into Err.

### 19.3 Sorting and ordered search

```glorious
pub fn sort_unstable<T>(items: &mut SliceMut<T>) where T: Ord;
pub fn sort_stable<T>(items: &mut SliceMut<T>, scratch: &mut Vec<T>) -> Result<(),ScratchError>
    where T: Ord;
pub fn binary_search<T>(items: Slice<T>, needle: &T) -> Result<usize,usize> where T: Ord;
pub fn lower_bound<T>(items: Slice<T>, needle: &T) -> usize where T: Ord;
pub fn upper_bound<T>(items: Slice<T>, needle: &T) -> usize where T: Ord;
pub fn equal_range<T>(items: Slice<T>, needle: &T) -> Range<usize> where T: Ord;
pub fn lex_compare<T>(left: Slice<T>, right: Slice<T>) -> Ordering where T: Ord;
pub fn common_prefix_len<T>(left: Slice<T>, right: Slice<T>) -> usize where T: Eq;
pub fn common_suffix_len<T>(left: Slice<T>, right: Slice<T>) -> usize where T: Eq;
pub fn find_subslice<T>(haystack: Slice<T>, needle: Slice<T>) -> Option<usize> where T: Eq;
pub fn dedup<T>(values: &mut Vec<T>) where T: Eq + Use<[0,1]>;
pub fn dedup_take<T>(values: &mut Vec<T>) -> Vec<T> where T: Eq;

pub fn sort_by<'env,Env,T,F,e: EffectRow>(items: &mut SliceMut<T>, compare: &mut F) / { | e }
where Env: Environment<'env>,
    for<'call> &'call mut F: Fn<(&'call T,&'call T),Output=Ordering,Effects=e>,
    for<'call> &'call mut F: RunsIn<&'call mut Env,(&'call T,&'call T),After=Env>;
pub fn try_sort_by<'env,Env,T,E,F,e: EffectRow>(items: &mut SliceMut<T>, compare: &mut F)
    -> Result<(),E> / { | e }
where Env: Environment<'env>,
    for<'call> &'call mut F: Fn<(&'call T,&'call T),Output=Result<Ordering,E>,Effects=e>,
    for<'call> &'call mut F: RunsIn<&'call mut Env,(&'call T,&'call T),After=Env>;
pub fn binary_search_by<'a,'env,Env,T,F,e: EffectRow>(items: Slice<'a,T>, compare: &mut F)
    -> Result<usize,usize> / { | e }
where Env: Environment<'env>,
    for<'call> &'call mut F: Fn<(&'a T,),Output=Ordering,Effects=e>,
    for<'call> &'call mut F: RunsIn<&'call mut Env,(&'a T,),After=Env>;
```

Sorts preserve every resident without a Clone/discard bound. Stable sort preserves equal-key order and requires an initially empty scratch owner; a ScratchError preserves both inputs. Comparison callbacks can be invoked repeatedly and in implementation-selected order; their ordering must be consistent for a sorted-result guarantee. Inconsistency may produce an unspecified permutation but must not cause memory unsafety.

Try-sort preserves a valid permutation on Err. Binary-search requires sorted input and returns an existing equal position on success or an insertion position on failure; no first-equal promise is implied. Lower/upper bounds provide those precise boundaries. Dedup removes adjacent equals, retaining the first representative; dedup-take returns all removed owners instead of destroying them.

## 20. Hashing and canonical fingerprints

```glorious
pub struct Hasher;
pub struct Digest256([u8;32]);
pub struct Blake3;
pub struct FingerprintWriter;

impl Hasher {
    pub fn new() -> Self;
    pub fn write(value: &mut Self, bytes: Slice<u8>);
    pub fn write_u8(value: &mut Self, input: u8);
    pub fn write_u16(value: &mut Self, input: u16);
    pub fn write_u32(value: &mut Self, input: u32);
    pub fn write_u64(value: &mut Self, input: u64);
    pub fn write_u128(value: &mut Self, input: u128);
    pub fn finish(value: &Self) -> u64;
}
pub fn hash64<T>(value: &T) -> u64 where T: Hash;
impl Digest256 {
    pub fn from_bytes(bytes: [u8;32]) -> Self;
    pub fn as_bytes<'a>(value: &'a Self) -> Slice<'a,u8>;
    pub fn to_hex(value: &Self) -> String;
    pub fn parse_hex(value: Str) -> Result<Self,HexError>;
}
impl Blake3 {
    pub fn new() -> Self;
    pub fn update(value: &mut Self, bytes: Slice<u8>);
    pub fn finish(value: Self) -> Digest256;
}
pub fn blake3(bytes: Slice<u8>) -> Digest256;
impl FingerprintWriter {
    pub fn new(domain: Str, schema: u32) -> Self;
    pub fn tag(value: &mut Self, tag: u32);
    pub fn u32(value: &mut Self, input: u32);
    pub fn u64(value: &mut Self, input: u64);
    pub fn bytes(value: &mut Self, bytes: Slice<u8>);
    pub fn text(value: &mut Self, text: Str);
    pub fn digest(value: &mut Self, digest: &Digest256);
    pub fn finish(value: Self) -> Digest256;
}
```

Hasher is deterministic for its library contract version, uses fixed-width little-endian integer streams, and is not a security token or persistent identity algorithm. Hash implementations must frame variable-length components so distinct concatenations do not become accidentally identical streams. The full byte stream, not raw object padding, defines semantic hashing.

Blake3 denotes the standard unkeyed 256-bit digest behavior; implementation details are not specified here. FingerprintWriter hashes this canonical stream: ASCII bytes `GLORIOUS-FP` followed by one zero byte, u32 little-endian schema, u64 little-endian domain-byte length, then the domain UTF-8 bytes. Subsequent tag/u32 calls append one u32 little-endian value; u64 appends one u64 little-endian value; bytes/text append their u64 little-endian byte length then bytes; digest appends exactly 32 digest bytes. Finish returns unkeyed BLAKE3 of the complete stream. The caller's versioned schema distinguishes field kinds and record tags; calling bytes and text with identical bytes intentionally has the same wire form. Address values, host paths, insertion IDs, and table order do not enter a reproducible semantic fingerprint unless its schema explicitly makes them input facts. Changing a fingerprint schema requires a new version, not a silently changed Hasher implementation.

## 21. Formatting and structured diagnostics

```glorious
pub struct Formatter;
pub struct FormatOptions {
    pub indent_width: usize,
    pub maximum_output_bytes: Option<usize>,
}
pub enum FormatError { OutputLimit, InvalidIndent, Allocation(ReserveError) }

impl Formatter {
    pub fn new() -> Self;
    pub fn with_options(options: FormatOptions) -> Self;
    pub fn write_str(value: &mut Self, text: Str);
    pub fn write_char(value: &mut Self, character: char);
    pub fn newline(value: &mut Self);
    pub fn indent(value: &mut Self) -> Result<(),FormatError>;
    pub fn dedent(value: &mut Self) -> Result<(),FormatError>;
    pub fn quoted(value: &mut Self, text: Str);
    pub fn display<T>(value: &mut Self, item: &T) where T: Display;
    pub fn debug<T>(value: &mut Self, item: &T) where T: Debug;
    pub fn finish(value: Self) -> Result<String,FormatError>;
}
pub fn format<T>(value: &T) -> String where T: Display;
pub fn format_debug<T>(value: &T) -> String where T: Debug;
pub fn try_format<T>(value: &T, options: FormatOptions) -> Result<String,FormatError> where T: Display;
pub fn fmt_result<T,E>(value: &Result<T,E>, out: &mut Formatter) where T: Debug, E: Debug;
pub fn fmt_option<T>(value: &Option<T>, out: &mut Formatter) where T: Debug;
```

Formatting appends to a caller-owned sink and does not require an intermediate String for each nested value. Text is valid UTF-8, deterministic, and locale-independent. No compiler-known format-string macro is assumed. A bounded Formatter records failure and stops appending; finish returns its error. It does not silently return truncated text as success.

Canonical indentation defaults to four spaces, applied only before a nonempty line's first content. Newline alone does not append indentation to blank lines. Dedent at zero fails without mutation. Quoted formatting escapes quotes, backslashes, control characters, and invalid source-literal content deterministically.

```glorious
pub enum Severity { Note, Warning, Error }
pub struct Diagnostic;
pub struct DiagnosticBag;
pub struct DiagnosticCode(u32);
pub struct SourceSpan { pub source: SourceId, pub range: Range<usize> }
pub struct RenderOptions { pub maximum_notes: usize, pub maximum_bytes: usize }

impl DiagnosticCode {
    pub fn from_u32(value: u32) -> Self;
    pub fn to_u32(value: Self) -> u32;
}
impl Diagnostic {
    pub fn new(severity: Severity, code: DiagnosticCode, message: String) -> Self;
    pub fn primary(value: &mut Self, span: SourceSpan, label: String);
    pub fn secondary(value: &mut Self, span: SourceSpan, label: String);
    pub fn note(value: &mut Self, text: String);
    pub fn help(value: &mut Self, text: String);
}
impl DiagnosticBag {
    pub fn new(limit: usize) -> Self;
    pub fn push(value: &mut Self, diagnostic: Diagnostic) -> Result<(),Diagnostic>;
    pub fn len(value: &Self) -> usize;
    pub fn has_errors(value: &Self) -> Bool;
    pub fn into_vec(value: Self) -> Vec<Diagnostic>;
}
pub fn render_diagnostic(value: &Diagnostic, sources: &SourceMap, options: RenderOptions)
    -> Result<String,FormatError>;
```

Diagnostics retain structured codes, severities, spans, labels, and notes rather than flattening everything to numeric status or text. Rendering invalid/missing source positions uses a stable unknown-location form, not a trap. Ordering follows an explicit source/severity/code policy. DiagnosticBag returns a rejected diagnostic when full instead of silently losing it.

## 22. Memory, allocation, and C-FFI support

### 22.1 Layout and allocation

```glorious
pub struct Layout;
pub struct Allocation;
pub struct AllocatorId(u64);
pub enum LayoutError { ZeroAlignment, NonPowerOfTwoAlignment, SizeOverflow }
pub enum AllocError { Exhausted, UnsupportedAlignment, LimitExceeded }
pub enum ReserveError { CapacityOverflow, Allocation(AllocError) }

impl Layout {
    pub fn from_size_align(size: usize, align: usize) -> Result<Self,LayoutError>;
    pub fn of<T>() -> Self;
    pub fn array<T>(count: usize) -> Result<Self,LayoutError>;
    pub fn size(value: &Self) -> usize;
    pub fn align(value: &Self) -> usize;
    pub fn extend(value: Self, other: Self) -> Result<(Self,usize),LayoutError>;
    pub fn padded(value: Self) -> Result<Self,LayoutError>;
}
pub fn size_of<T>() -> usize;
pub fn align_of<T>() -> usize;
pub fn allocate(layout: Layout) -> Result<Allocation,AllocError>;
impl Allocation {
    pub fn layout(value: &Self) -> Layout;
    pub fn allocator(value: &Self) -> AllocatorId;
    pub fn as_ptr(value: &Self) -> *mut u8;
    pub unsafe fn resize(value: &mut Self, new_layout: Layout) -> Result<(),AllocError>;
    pub unsafe fn release(value: Self);
}
```

Allocation is an exact-linear raw-storage owner, completed through release or transferred to another owning abstraction. It owns raw storage, not implicit initialized T residents. Safe allocation creates uninitialized bytes; clients use unsafe writes or a safe owning abstraction that establishes initialization. Resize/release require that resident ownership, outstanding pointers/loans, and allocator-domain constraints are satisfied. Resize failure preserves the original allocation. An arbitrary host pointer cannot be turned into Allocation by a safe constructor.

The quantity-only marker for unsafe owning representations is:

```glorious
pub struct PhantomData<T>;
```

Its widest principal class is exactly T's principal class, established by one compiler-checked generic principal restriction. It owns no T and is zero-sized. It cannot by itself justify raw memory access or a reference lifetime. Conventional uninitialized-storage wrappers that suppress destruction are not supplied as a safe escape from linear ownership; Allocation and explicit unsafe initialization contracts provide the foundational storage boundary.

### 22.2 Pointer namespace

```glorious
pub fn null<T>() -> *const T;
pub fn null_mut<T>() -> *mut T;
pub fn dangling<T>() -> *mut T;
pub fn ptr_is_null<T>(value: *const T) -> Bool;
pub fn ptr_eq<T>(left: *const T, right: *const T) -> Bool;
pub fn ptr_address<T>(value: *const T) -> usize;
pub fn ptr_from_ref<T>(value: &T) -> *const T;
pub fn ptr_from_mut<T>(value: &mut T) -> *mut T;
pub unsafe fn ptr_add<T>(value: *const T, count: usize) -> *const T;
pub unsafe fn ptr_add_mut<T>(value: *mut T, count: usize) -> *mut T;
pub unsafe fn ptr_offset<T>(value: *const T, count: isize) -> *const T;
pub fn ptr_cast<T,U>(source: *const T) -> *const U;
pub fn ptr_cast_mut<T,U>(source: *mut T) -> *mut U;
pub fn ptr_as_const<T>(source: *mut T) -> *const T;
pub unsafe fn ptr_as_ref<'a,T>(source: *const T) -> &'a T;
pub unsafe fn ptr_as_mut<'a,T>(source: *mut T) -> &'a mut T;
pub unsafe fn ptr_read<T>(source: *const T) -> T;
pub unsafe fn ptr_read_unaligned<T>(source: *const T) -> T;
pub unsafe fn ptr_write_unaligned<T>(destination: *mut T, value: T);
pub unsafe fn ptr_write_bytes(destination: *mut u8, byte: u8, count: usize);
pub unsafe fn ptr_write<T>(destination: *mut T, value: T);
pub unsafe fn ptr_replace<T>(destination: *mut T, value: T) -> T;
pub unsafe fn ptr_swap<T>(left: *mut T, right: *mut T);
pub unsafe fn ptr_copy<T>(source: *const T, destination: *mut T, count: usize)
    where T: Use<[0,*]>;
pub unsafe fn ptr_copy_nonoverlapping<T>(source: *const T, destination: *mut T, count: usize)
    where T: Use<[0,*]>;
pub unsafe fn ptr_move<T>(source: *mut T, destination: *mut T, count: usize);
pub unsafe fn ptr_move_nonoverlapping<T>(source: *mut T, destination: *mut T, count: usize);
pub unsafe fn ptr_drop_in_place<T>(value: *mut T) where T: Use<[0,1]>;
pub unsafe fn slice_from_raw<'a,T>(data: *const T, length: usize) -> Slice<'a,T>;
pub unsafe fn slice_from_raw_mut<'a,T>(data: *mut T, length: usize) -> SliceMut<'a,T>;
```

These unsafe contracts require complete range/alignment/provenance/initialization proofs, including checked byte-size arithmetic. Ptr-read transfers the initialized resident; ptr-write requires an uninitialized destination or a contract that has already disposed of its former resident. Ptr-copy duplicates only duplicable residents. Ptr-move transfers them and invalidates source ownership, with overlap semantics exactly as named. Move operations must not expose two initialized owners after the operation.

Raw cast/as-const preserves pointer provenance but establishes no U validity, alignment or ownership. Unaligned read/write relax alignment only; all other validity/initialization/ownership requirements remain. Byte fill does not establish that the resulting bytes are a valid arbitrary T. Pointer equality/address inspection does not prove lifetime, same-allocation provenance, or safe dereference. Dangling is aligned for T but does not provide an allocated resident. Raw-slice construction requires that the caller establish storage and borrow validity for the entire chosen `'a`; a generic lifetime argument is not its own proof. Safe code cannot manufacture such views from arbitrary integers.

### 22.3 Single-owner allocation

```glorious
pub struct Box<T>;
impl<T> Box<T> {
    pub fn new(value: T) -> Self;
    pub fn try_new(value: T) -> Result<Self,Rejected<T,AllocError>>;
    pub fn as_ref<'a>(value: &'a Self) -> &'a T;
    pub fn as_mut<'a>(value: &'a mut Self) -> &'a mut T;
    pub fn into_inner(value: Self) -> T;
    pub fn allocator(value: &Self) -> AllocatorId;
    pub unsafe fn into_raw(value: Self) -> *mut T;
    pub unsafe fn from_raw(value: *mut T, allocator: AllocatorId) -> Self;
}
```

Box is nonduplicable and inherits the resident's disposal requirement. Into-inner transfers T and releases only its empty storage shell. Into-raw is unsafe here because it moves the explicit ownership obligation into a programmer-maintained raw contract; it is not a safe way to forget a linear resident. From-raw requires exact allocation identity, initialized T, uniqueness, and matching release behavior.

### 22.4 C scalar and string types

The `std::ffi` module defines target-specific `c_char`, `c_schar`, `c_uchar`, `c_short`, `c_ushort`, `c_int`, `c_uint`, `c_long`, `c_ulong`, `c_longlong`, `c_ulonglong`, `c_float`, `c_double`, `c_size_t`, `c_ptrdiff_t`, and `c_void`. Their exact sizes/signedness are properties of the selected C ABI descriptor, not fixed by the spelling. `c_bool` is a distinct checked C Boolean representation, not Glorious Bool.

```glorious
pub struct CStr<'a>;
pub struct CString;
pub struct NulError { pub position: usize }
pub enum CStrError { MissingTerminator, InteriorNul(NulError) }

impl<'a> CStr<'a> {
    pub fn from_bytes_with_nul(value: Slice<'a,u8>) -> Result<Self,CStrError>;
    pub fn bytes(value: Self) -> Slice<'a,u8>;
    pub fn bytes_with_nul(value: Self) -> Slice<'a,u8>;
    pub fn as_ptr(value: Self) -> *const c_char;
    pub fn to_str(value: Self) -> Result<Str<'a>,Utf8Error>;
    pub unsafe fn from_ptr(value: *const c_char, maximum_length: usize) -> Result<Self,CStrError>;
}
impl CString {
    pub fn from_vec(value: Vec<u8>) -> Result<Self,Rejected<Vec<u8>,NulError>>;
    pub fn from_str(value: Str) -> Result<Self,NulError>;
    pub fn as_c_str<'a>(value: &'a Self) -> CStr<'a>;
    pub fn as_ptr(value: &Self) -> *const c_char;
    pub fn into_bytes(value: Self) -> Vec<u8>;
    pub fn into_bytes_with_nul(value: Self) -> Vec<u8>;
}
pub fn c_bool_from_bool(value: Bool) -> c_bool;
pub fn bool_from_c_bool(value: c_bool) -> Bool;
```

CStr includes one terminating NUL and no earlier NUL. Its bytes view excludes the terminator. Bounded pointer construction still requires the unsafe caller to prove that scanning the relevant range is valid and that the resulting borrow lives long enough. CString constructors do not confuse Unicode encoding with C string validity. No safe CString destructor frees memory allocated by an unrelated C allocator.

## 23. Binary readers, buffers, and bounded codecs

```glorious
pub struct ByteReader<'a>;
pub struct ReaderMark;
pub struct ByteBuf;
pub struct BufferMark;
pub enum DecodeErrorKind { Truncated, Overflow, NonCanonical, InvalidTag, InvalidUtf8, LimitExceeded }
pub struct DecodeError { pub offset: usize, pub kind: DecodeErrorKind }
pub enum ByteWriteError { Range(RangeError), Reserve(ReserveError), InvalidAlignment }

impl<'a> ByteReader<'a> {
    pub fn new(bytes: Slice<'a,u8>) -> Self;
    pub fn position(value: &Self) -> usize;
    pub fn remaining_len(value: &Self) -> usize;
    pub fn remaining(value: &Self) -> Slice<'a,u8>;
    pub fn mark(value: &Self) -> ReaderMark;
    pub fn restore(value: &mut Self, mark: ReaderMark) -> Result<(),MarkError>;
    pub fn read_u8(value: &mut Self) -> Result<u8,DecodeError>;
    pub fn read_u16_le(value: &mut Self) -> Result<u16,DecodeError>;
    pub fn read_u32_le(value: &mut Self) -> Result<u32,DecodeError>;
    pub fn read_u64_le(value: &mut Self) -> Result<u64,DecodeError>;
    pub fn read_u128_le(value: &mut Self) -> Result<u128,DecodeError>;
    pub fn read_u16_be(value: &mut Self) -> Result<u16,DecodeError>;
    pub fn read_u32_be(value: &mut Self) -> Result<u32,DecodeError>;
    pub fn read_u64_be(value: &mut Self) -> Result<u64,DecodeError>;
    pub fn read_i64_le(value: &mut Self) -> Result<i64,DecodeError>;
    pub fn read_var_u64(value: &mut Self) -> Result<u64,DecodeError>;
    pub fn read_exact(value: &mut Self, length: usize) -> Result<Slice<'a,u8>,DecodeError>;
    pub fn read_str(value: &mut Self, length: usize) -> Result<Str<'a>,DecodeError>;
    pub fn skip(value: &mut Self, length: usize) -> Result<(),DecodeError>;
    pub fn subreader(value: &mut Self, length: usize) -> Result<Self,DecodeError>;
    pub fn finish(value: Self) -> Result<(),DecodeError>;
}
impl ByteBuf {
    pub fn new() -> Self;
    pub fn with_capacity(capacity: usize) -> Result<Self,ReserveError>;
    pub fn len(value: &Self) -> usize;
    pub fn as_slice<'a>(value: &'a Self) -> Slice<'a,u8>;
    pub fn reserve(value: &mut Self, additional: usize) -> Result<(),ReserveError>;
    pub fn push(value: &mut Self, byte: u8) -> Result<(),ReserveError>;
    pub fn extend(value: &mut Self, bytes: Slice<u8>) -> Result<(),ReserveError>;
    pub fn write_u16_le(value: &mut Self, input: u16) -> Result<(),ReserveError>;
    pub fn write_u32_le(value: &mut Self, input: u32) -> Result<(),ReserveError>;
    pub fn write_u64_le(value: &mut Self, input: u64) -> Result<(),ReserveError>;
    pub fn write_u128_le(value: &mut Self, input: u128) -> Result<(),ReserveError>;
    pub fn write_u16_be(value: &mut Self, input: u16) -> Result<(),ReserveError>;
    pub fn write_u32_be(value: &mut Self, input: u32) -> Result<(),ReserveError>;
    pub fn write_u64_be(value: &mut Self, input: u64) -> Result<(),ReserveError>;
    pub fn write_var_u64(value: &mut Self, input: u64) -> Result<(),ReserveError>;
    pub fn patch_u16_le(value: &mut Self, offset: usize, input: u16) -> Result<(),RangeError>;
    pub fn patch_u32_le(value: &mut Self, offset: usize, input: u32) -> Result<(),RangeError>;
    pub fn patch_u64_le(value: &mut Self, offset: usize, input: u64) -> Result<(),RangeError>;
    pub fn align_zeroed(value: &mut Self, alignment: usize) -> Result<(),ByteWriteError>;
    pub fn resize_zeroed(value: &mut Self, length: usize) -> Result<(),ReserveError>;
    pub fn mark(value: &Self) -> BufferMark;
    pub fn truncate_to(value: &mut Self, mark: BufferMark) -> Result<(),MarkError>;
    pub fn finish(value: Self) -> Vec<u8>;
}
```

Reader failure does not advance its cursor. Complete reads check size arithmetic before slicing. Variable-u64 uses canonical unsigned base-128 encoding with at most ten bytes, rejecting overflow and redundant encodings. Mark values are owner-associated and cannot restore another reader/buffer or an invalidated generation. Finish-reader rejects trailing unread input.

Byte-buffer patching validates the complete fixed-width range before mutation. Alignment must be a nonzero power of two and appends the minimum zero padding. Invalid requests leave the buffer unchanged. These are binary construction contracts, not a general serialization/derive framework.

```glorious
pub fn hex_encode(bytes: Slice<u8>) -> String;
pub fn hex_decode(text: Str) -> Result<Vec<u8>,HexError>;
pub enum Base64Alphabet { Standard, UrlSafe }
pub enum Padding { Required, Optional, Forbidden }
pub struct Base64Options { pub alphabet: Base64Alphabet, pub padding: Padding }
pub fn base64_encode(bytes: Slice<u8>, options: Base64Options) -> String;
pub fn base64_decode(text: Str, options: Base64Options) -> Result<Vec<u8>,Base64Error>;
```

These small codecs are optional pure modules. Their decoder errors carry byte positions. No whitespace skipping or noncanonical-padding acceptance occurs unless the chosen options expressly permit it. These encodings provide no confidentiality or authentication.

## 24. Compiler-construction data structures

This module is ordinary reusable source support, not a compiler semantic callback surface. Nominal compiler IR types, query-provider methods, and solver transfer functions stay in the compiler package.

```glorious
pub struct Id<Tag>(u32);
pub struct IndexVec<Tag,T>;
pub struct Arena<Tag,T>;
pub struct ArenaMark<Tag>;
pub struct GenId<Tag>;
pub struct GenArena<Tag,T>;
pub struct Interner<Tag,T>;
pub struct StringInterner<Tag>;
pub struct BitSet<Tag>;
pub struct SparseSet<Tag>;
pub struct WorkQueue<Tag>;
pub enum InternOutcome<Tag,T> { Inserted(Id<Tag>), Existing { id: Id<Tag>, unused: T } }

impl<Tag> Id<Tag> {
    pub fn from_u32(value: u32) -> Self;
    pub fn to_u32(value: Self) -> u32;
    pub fn from_usize(value: usize) -> Result<Self,IndexOverflow>;
    pub fn to_usize(value: Self) -> usize;
}
impl<Tag,T> IndexVec<Tag,T> {
    pub fn new() -> Self;
    pub fn len(value: &Self) -> usize;
    pub fn push(value: &mut Self, item: T) -> Result<Id<Tag>,Rejected<T,IndexOverflow>>;
    pub fn get<'a>(value: &'a Self, id: Id<Tag>) -> Option<&'a T>;
    pub fn get_mut<'a>(value: &'a mut Self, id: Id<Tag>) -> Option<&'a mut T>;
    pub fn as_slice<'a>(value: &'a Self) -> Slice<'a,T>;
    pub fn into_vec(value: Self) -> Vec<T>;
}
impl<Tag,T> Arena<Tag,T> {
    pub fn new() -> Self;
    pub fn insert(value: &mut Self, item: T) -> Result<Id<Tag>,Rejected<T,IndexOverflow>>;
    pub fn get<'a>(value: &'a Self, id: Id<Tag>) -> Option<&'a T>;
    pub fn get_mut<'a>(value: &'a mut Self, id: Id<Tag>) -> Option<&'a mut T>;
    pub fn mark(value: &Self) -> ArenaMark<Tag>;
    pub fn truncate(value: &mut Self, mark: ArenaMark<Tag>) -> Result<(),MarkError> where T: Use<[0,1]>;
    pub fn rollback_take(value: &mut Self, mark: ArenaMark<Tag>) -> Result<Vec<T>,MarkError>;
    pub fn into_vec(value: Self) -> Vec<T>;
}
impl<Tag,T> GenArena<Tag,T> {
    pub fn new() -> Self;
    pub fn insert(value: &mut Self, item: T) -> Result<GenId<Tag>,Rejected<T,IndexOverflow>>;
    pub fn get<'a>(value: &'a Self, id: GenId<Tag>) -> Option<&'a T>;
    pub fn get_mut<'a>(value: &'a mut Self, id: GenId<Tag>) -> Option<&'a mut T>;
    pub fn remove(value: &mut Self, id: GenId<Tag>) -> Option<T>;
    pub fn contains(value: &Self, id: GenId<Tag>) -> Bool;
    pub fn into_vec(value: Self) -> Vec<T>;
}
impl<Tag,T> Interner<Tag,T> where T: Eq + Hash {
    pub fn new() -> Self;
    pub fn intern(value: &mut Self, item: T) -> Result<InternOutcome<Tag,T>,Rejected<T,IndexOverflow>>;
    pub fn intern_discarding(value: &mut Self, item: T) -> Result<Id<Tag>,Rejected<T,IndexOverflow>>
        where T: Use<[0,1]>;
    pub fn find(value: &Self, item: &T) -> Option<Id<Tag>>;
    pub fn get<'a>(value: &'a Self, id: Id<Tag>) -> Option<&'a T>;
    pub fn into_values(value: Self) -> Vec<T>;
}
impl<Tag> StringInterner<Tag> {
    pub fn new() -> Self;
    pub fn intern(value: &mut Self, text: Str) -> Result<Id<Tag>,IndexOverflow>;
    pub fn find(value: &Self, text: Str) -> Option<Id<Tag>>;
    pub fn get<'a>(value: &'a Self, id: Id<Tag>) -> Option<Str<'a>>;
}
impl<Tag> BitSet<Tag> {
    pub fn new() -> Self;
    pub fn len(value: &Self) -> usize;
    pub fn contains(value: &Self, id: Id<Tag>) -> Bool;
    pub fn insert(value: &mut Self, id: Id<Tag>) -> Bool;
    pub fn remove(value: &mut Self, id: Id<Tag>) -> Bool;
    pub fn clear(value: &mut Self);
    pub fn union_with(value: &mut Self, other: &Self) -> Bool;
    pub fn intersect_with(value: &mut Self, other: &Self) -> Bool;
    pub fn subtract(value: &mut Self, other: &Self) -> Bool;
    pub fn is_subset(value: &Self, other: &Self) -> Bool;
    pub fn to_vec(value: &Self) -> Vec<Id<Tag>>;
}
impl<Tag> SparseSet<Tag> {
    pub fn new() -> Self;
    pub fn len(value: &Self) -> usize;
    pub fn insert(value: &mut Self, id: Id<Tag>) -> Bool;
    pub fn remove(value: &mut Self, id: Id<Tag>) -> Bool;
    pub fn contains(value: &Self, id: Id<Tag>) -> Bool;
    pub fn clear(value: &mut Self);
    pub fn to_vec(value: &Self) -> Vec<Id<Tag>>;
}
impl<Tag> WorkQueue<Tag> {
    pub fn new() -> Self;
    pub fn push(value: &mut Self, id: Id<Tag>) -> Bool;
    pub fn pop(value: &mut Self) -> Option<Id<Tag>>;
    pub fn contains(value: &Self, id: Id<Tag>) -> Bool;
    pub fn is_empty(value: &Self) -> Bool;
    pub fn clear(value: &mut Self);
}
```

Id<Tag> distinguishes index domains, not arbitrary arena instances: get remains checked, and a caller needing per-instance protection uses a generative Tag or GenId owner identity. GenId validates arena identity and generation; stale/foreign handles fail instead of aliasing reused storage. Generation overflow retires a slot or returns a resource error, never silently wraps to an old valid identity.

Arena marks validate owner, position and generation. Truncate destroys suffix residents and therefore needs affine T; rollback-take transfers them. Interner duplicate insertion returns the unused input unless an explicitly discarding API is chosen. No compiler phase may use inference-variable-bearing mutable terms as stable interned keys without its own invariant proving equality/hash stability.

BitSet to-vec is sorted by numeric ID. SparseSet order is unspecified. WorkQueue is FIFO and does not enqueue an already pending ID; pop removes membership before returning it. All size/index arithmetic is checked at its public representability boundary.

## 25. Source maps, locations, budgets, and transactions

### 25.1 Source identity and coordinates

```glorious
pub struct SourceId(u32);
pub struct SourceMap;
pub struct SourceLocation { pub source: SourceId, pub line: usize, pub column_bytes: usize }
pub struct Utf16Location { pub line: usize, pub column_units: usize }
pub enum SourceError { UnknownSource, InvalidRange, InvalidBoundary, IndexOverflow, Allocation(ReserveError) }

impl SourceMap {
    pub fn new() -> Self;
    pub fn insert(value: &mut Self, name: String, text: String)
        -> Result<SourceId,Rejected<(String,String),SourceError>>;
    pub fn name<'a>(value: &'a Self, source: SourceId) -> Option<Str<'a>>;
    pub fn text<'a>(value: &'a Self, source: SourceId) -> Option<Str<'a>>;
    pub fn slice<'a>(value: &'a Self, span: SourceSpan) -> Result<Str<'a>,SourceError>;
    pub fn locate(value: &Self, source: SourceId, offset: usize) -> Result<SourceLocation,SourceError>;
    pub fn to_utf16(value: &Self, source: SourceId, offset: usize) -> Result<Utf16Location,SourceError>;
    pub fn from_utf16(value: &Self, source: SourceId, location: Utf16Location) -> Result<usize,SourceError>;
    pub fn line_range(value: &Self, source: SourceId, line: usize) -> Result<Range<usize>,SourceError>;
}
```

Lines/columns in these machine-facing structs are zero-based; renderers may display one-based positions. Byte columns and UTF-16 code-unit columns are distinct APIs. Conversion rejects a location inside a UTF-8 scalar or UTF-16 surrogate pair rather than rounding silently. Source names are presentation metadata unless a caller's explicit identity schema says otherwise. SourceMap does not read files or grant module privacy.

### 25.2 Logical budgets and resource tickets

```glorious
pub enum BudgetKind { Steps, Depth, Memory, Diagnostics, Items }
pub struct BudgetExceeded { pub kind: BudgetKind, pub requested: u64, pub remaining: u64 }
pub struct StepBudget;
pub struct MemoryBudget;
pub struct MemoryCharge;
pub struct DepthBudget;
pub struct DepthPermit;
pub enum MarkError { WrongOwner, Stale, OutOfRange, NotTop }

impl StepBudget {
    pub fn new(limit: u64) -> Self;
    pub fn remaining(value: &Self) -> u64;
    pub fn charge(value: &mut Self, steps: u64) -> Result<(),BudgetExceeded>;
}
impl MemoryBudget {
    pub fn new(limit: u64) -> Self;
    pub fn remaining(value: &Self) -> u64;
    pub fn charge(value: &mut Self, bytes: u64) -> Result<MemoryCharge,BudgetExceeded>;
    pub fn release(value: &mut Self, charge: MemoryCharge) -> Result<(),Rejected<MemoryCharge,MarkError>>;
}
impl DepthBudget {
    pub fn new(limit: u32) -> Self;
    pub fn enter(value: &mut Self) -> Result<DepthPermit,BudgetExceeded>;
    pub fn leave(value: &mut Self, permit: DepthPermit) -> Result<(),Rejected<DepthPermit,MarkError>>;
}
pub enum ControlSignal { Proceed, CancelRequested }
pub effect RequestControl { poll() -> ControlSignal }
```

Charges/permits are exact-linear bookkeeping tickets associated with their owner budget, not copyable counters. A wrong-budget release returns the ticket intact. A failed charge leaves accounting unchanged. Explicit cancellation polling returns a signal and does not secretly discard an active continuation. Source code must unwind/return its outstanding ownership correctly.

Logical allocation charges and physical process memory are different measurements. These APIs do not claim a complete allocator census. Wall-clock enforcement belongs to a host supervisor or explicit clock capability, not an ambient source timer hidden in StepBudget.

### 25.3 Undo and scoped state

```glorious
pub struct UndoLog<T>;
pub struct UndoMark;
impl<T> UndoLog<T> {
    pub fn new() -> Self;
    pub fn mark(value: &Self) -> UndoMark;
    pub fn push(value: &mut Self, item: T);
    pub fn commit(value: &mut Self, mark: UndoMark) -> Result<Vec<T>,MarkError>;
    pub fn rollback_take(value: &mut Self, mark: UndoMark) -> Result<Vec<T>,MarkError>;
    pub fn clear(value: &mut Self) where T: Use<[0,1]>;
}
```

UndoLog stores records; it does not know their semantic inverse. Rollback-take returns records in reverse insertion order for the caller's reversal policy; commit returns the records no longer needed by that transaction. Nested marks must be resolved according to their owner/generation/stack contract. A general transaction guard may perform only the language's permitted pure Drop cleanup; it cannot hide effectful I/O rollback or discard linear values.

## 26. Bounded parser and graph helpers

### 26.1 Cursor and parse outcomes

```glorious
pub struct Cursor<'a,T>;
pub struct CursorMark;
pub enum ParseStep<T,E> { Matched(T), NoMatch, Failed(E) }
pub enum ParseError<E> { User(E), NoProgress, Limit(BudgetExceeded) }

impl<'a,T> Cursor<'a,T> {
    pub fn new(input: Slice<'a,T>) -> Self;
    pub fn position(value: &Self) -> usize;
    pub fn remaining(value: &Self) -> Slice<'a,T>;
    pub fn peek(value: &Self) -> Option<&'a T>;
    pub fn next(value: &mut Self) -> Option<&'a T>;
    pub fn mark(value: &Self) -> CursorMark;
    pub fn restore(value: &mut Self, mark: CursorMark) -> Result<(),MarkError>;
}

pub fn attempt<'a,'env,Env,T,U,E,F,e: EffectRow>(cursor: &mut Cursor<'a,T>, parse: &mut F)
    -> ParseStep<U,E> / { | e }
where Env: Environment<'env>,
    for<'call> &'call mut F: Fn<(&'call mut Cursor<'a,T>,),Output=ParseStep<U,E>,Effects=e>,
    for<'call> &'call mut F: RunsIn<&'call mut Env,(&'call mut Cursor<'a,T>,),After=Env>;

pub fn many<'a,'env,Env,T,U,E,F,e: EffectRow>(
    cursor: &mut Cursor<'a,T>, limit: usize, parse: &mut F
) -> Result<Vec<U>,(Vec<U>,ParseError<E>)> / { | e }
where Env: Environment<'env>,
    for<'call> &'call mut F: Fn<(&'call mut Cursor<'a,T>,),Output=ParseStep<U,E>,Effects=e>,
    for<'call> &'call mut F: RunsIn<&'call mut Env,(&'call mut Cursor<'a,T>,),After=Env>;
```

NoMatch restores cursor position for attempt; Failed is a committed parse failure. These operations do not undo arbitrary side effects or external mutations captured by the callback. Many detects a successful iteration that made no cursor progress and returns accumulated ownership with NoProgress. Its finite limit is explicit. This is not multi-shot continuation backtracking.

### 26.2 Generic graph/worklist boundary

```glorious
pub trait Graph {
    type Node: Eq + Hash + Use<[0,*]>;
    fn successors<'a>(value: &'a Self, node: Self::Node) -> Slice<'a,Self::Node>;
}
pub struct Cycle<N> { pub nodes: Vec<N> }
pub enum GraphError<N> { Cycle(Cycle<N>), Limit(BudgetExceeded) }
pub fn reachable<G>(graph: &G, start: G::Node, budget: &mut StepBudget)
    -> Result<Vec<G::Node>,BudgetExceeded> where G: Graph;
pub fn topological_order<G>(graph: &G, nodes: Slice<G::Node>, budget: &mut StepBudget)
    -> Result<Vec<G::Node>,GraphError<G::Node>> where G: Graph;
pub fn strongly_connected_components<G>(graph: &G, nodes: Slice<G::Node>, budget: &mut StepBudget)
    -> Result<Vec<Vec<G::Node>>,BudgetExceeded> where G: Graph;
```

Traversal order derives from the supplied node/successor order, not hash iteration. Budgets count logically documented work and must be checked during input-sized traversals. A cycle is a structured outcome where appropriate. No universal compiler lattice, visitor hierarchy, or query engine is imposed on clients.

## 27. Host effects and external authority

### 27.1 Direct operation declarations

The following operation families are public contracts, not automatically granted capabilities. An operation is performed by calling its imported binding. Importing a whole effect also imports its public operations under the language's name-resolution rules; collisions require an alias or qualification. Importing a declaration neither installs a handler nor grants host authority.

```glorious
pub effect ProcessArgs {
    args() -> Result<Vec<OsString>,IoError>
}
pub effect FileRead {
    read_file<'a>(Path<'a>) -> Result<Vec<u8>,IoError>
}
pub effect FileWrite {
    write_file<'a,'b>(Path<'a>,Slice<'b,u8>) -> Result<(),IoError>
    write_file_atomic<'a,'b>(Path<'a>,Slice<'b,u8>) -> Result<(),IoError>
}
pub effect Diagnostic {
    write_diagnostic<'a>(Str<'a>) -> Result<(),IoError>
}
pub effect Console {
    read_stdin<'a>(SliceMut<'a,u8>) -> Result<usize,IoError>
    write_stdout<'a>(Slice<'a,u8>) -> Result<usize,IoError>
    write_stderr<'a>(Slice<'a,u8>) -> Result<usize,IoError>
    flush_stdout() -> Result<(),IoError>
    flush_stderr() -> Result<(),IoError>
}
pub effect ProcessEnvironment {
    env<'a>(OsStr<'a>) -> Result<Option<OsString>,IoError>
    current_dir() -> Result<PathBuf,IoError>
}
```

These are exact-once resumptive operations: omitted quantities mean `[1,1]`. A handler must return a success/error value exactly once on normally completing execution. An ordinary OS error is not grounds to abandon a live exact-once continuation. Supervised process termination or a fatal runtime violation is separate from recoverable source failure.

Read-file returns binary bytes, not unchecked text. Write-file may have externally visible partial progress when it fails. Atomic write promises all-or-nothing replacement of the destination name only where the target/provider supports that contract; otherwise it reports Unsupported. Atomic replacement is not a promise of durable persistence without a separate durability contract. Console reads/writes have the partial-progress semantics of §28. Diagnostic output is UTF-8 and is not a replacement for arbitrary binary stdout.

### 27.2 Handler installation and the closed executable boundary

A host adapter is substantive code that installs handlers and checks grants; it is not a forwarding wrapper around an operation. The compiler-oriented adapter has this interface:

```glorious
pub struct CompilerHost;
pub fn run_compiler_host<'env,E0,E1,R,F,e: EffectRow>(
    host: &mut CompilerHost, main: F
) -> R / { | e }
where
    E0: Environment<'env> + Use<[1,1]>, E1: Environment<'env>,
    F: Fn<(),Output=R,Effects={ProcessArgs,FileRead,FileWrite,Diagnostic | e}>,
    F: RunsIn<E0,(),After=E1>;
```

**Control contract.** Invoke main exactly once; handle the four listed families; forward only e and any explicitly declared adapter effects. The implementation may not borrow the same host state incompatibly in the handled body and its handlers. CompilerHost construction is an embedding/driver operation; no safe source constructor can manufacture OS authority. Empty outward effects of an executable entry are a closure requirement, not an instruction to inject arbitrary handlers automatically.

The typed-host contract requires ordinary file failures to return structured results. Update the compiler, runtime manifests, and host bindings together to implement it; retaining the old G1 `(capability,symbol,signature)` triples is not required. A source wrapper cannot turn an uncatchable HostFault into a recoverable result. The provider must implement that result contract, and admission must reject mismatched bindings.

### 27.3 Capability minimums

| Operation family | Required authority boundary |
|---|---|
| ProcessArgs | Exact argument-vector access supplied by the invoker. |
| FileRead | Read authority restricted to the provider's admitted paths/handles. |
| FileWrite | Write authority; atomic replacement additionally requires the corresponding provider facility. |
| Diagnostic | Diagnostic output sink only. |
| Console | Explicit stdin/stdout/stderr access; no implied filesystem authority. |
| ProcessEnvironment | Explicit environment/current-directory observation; no ambient permission from ProcessArgs. |
| FileSystem and ProcessControl (§29) | Independently granted file-handle/directory/process operations. |
| Clock and Entropy (§29) | Explicit nondeterministic observation/source. |

These are semantic capability requirements, not frozen numeric import IDs. An embedding can offer stricter structured capabilities. Unsafe unrestricted memory/foreign code is not contained by these in-process checks; the language explicitly does not make that sandbox claim.

## 28. Stream I/O interfaces

### 28.1 Stream traits

```glorious
pub trait Read {
    type Effects: EffectRow;
    fn read(value: &mut Self, buffer: SliceMut<u8>) -> Result<usize,IoError>
        / { | Self::Effects };
}
pub trait Write {
    type Effects: EffectRow;
    fn write(value: &mut Self, buffer: Slice<u8>) -> Result<usize,IoError>
        / { | Self::Effects };
    fn flush(value: &mut Self) -> Result<(),IoError> / { | Self::Effects };
}
pub enum SeekFrom { Start(u64), End(i64), Current(i64) }
pub trait Seek {
    type Effects: EffectRow;
    fn seek(value: &mut Self, from: SeekFrom) -> Result<u64,IoError>
        / { | Self::Effects };
}
pub trait BufferedRead: Read {
    fn fill_buf<'a>(value: &'a mut Self) -> Result<Slice<'a,u8>,IoError>
        / { | Self::Effects };
    fn consume(value: &mut Self, count: usize) -> Result<(),RangeError>;
}

pub struct ReadExactError { pub filled: usize, pub error: IoError }
pub struct WriteAllError { pub written: usize, pub error: IoError }
pub struct CopyError { pub read: u64, pub written: u64, pub error: IoError }
pub struct ReadToEndError { pub appended: usize, pub error: IoError }

pub fn read_exact<R>(reader: &mut R, buffer: SliceMut<u8>)
    -> Result<(),ReadExactError> / { | <R as Read>::Effects } where R: Read;
pub fn write_all<W>(writer: &mut W, buffer: Slice<u8>)
    -> Result<(),WriteAllError> / { | <W as Write>::Effects } where W: Write;
pub fn read_to_end<R>(reader: &mut R, out: &mut Vec<u8>, limit: usize)
    -> Result<usize,ReadToEndError> / { | <R as Read>::Effects } where R: Read;
pub fn copy_stream<R,W>(reader: &mut R, writer: &mut W, limit: u64)
    -> Result<u64,CopyError> / { | <R as Read>::Effects,<W as Write>::Effects }
    where R: Read, W: Write;
```

Read/write returns a count at most the supplied buffer length. A successful read of zero with a nonempty buffer means end of stream for that observation; a zero-sized request can complete with zero without asserting EOF. A successful write of zero with nonempty input means no progress; write-all reports WriteZero rather than looping indefinitely. An individual Err reports no committed byte count for that call; providers with partial commits must return a successful prefix or use a richer separate operation, not conceal progress in Err.

Read-exact preserves the filled prefix on error and reports its size. Write-all reports the committed prefix; retrying the entire buffer can duplicate output. Read-to-end retains appended bytes in out even on failure and never exceeds its limit. Copy-stream may have read more than it successfully wrote; its two counts are distinct. A returned byte count is not proof that a remote peer processed data or that storage is durable.

BufferedRead's borrowed buffer prevents incompatible mutation until its loan ends. Consume rejects an excessive count without changing its state. Seek failure leaves the object valid; preservation of the underlying external cursor requires a provider-specific promise and is not assumed generically.

### 28.2 Buffering and memory streams

```glorious
pub struct BufferReader<R>;
pub struct BufferWriter<W>;
pub struct MemoryCursor;
pub struct FinishWriteFailure<W> { pub writer: W, pub pending: Vec<u8>, pub error: IoError }

impl<R> BufferReader<R> {
    pub fn new(reader: R, capacity: usize) -> Result<Self,Rejected<R,AllocError>>;
    pub fn get_ref(value: &Self) -> &R;
    pub fn into_parts(value: Self) -> (R,Vec<u8>);
}
impl<W> BufferWriter<W> {
    pub fn new(writer: W, capacity: usize) -> Result<Self,Rejected<W,AllocError>>;
    pub fn get_ref(value: &Self) -> &W;
    pub fn pending(value: &Self) -> Slice<u8>;
    pub fn into_parts(value: Self) -> (W,Vec<u8>);
    pub fn finish(value: Self) -> Result<W,FinishWriteFailure<W>>
        / { | <W as Write>::Effects } where W: Write;
}
impl MemoryCursor {
    pub fn new(bytes: Vec<u8>) -> Self;
    pub fn position(value: &Self) -> u64;
    pub fn as_slice(value: &Self) -> Slice<u8>;
    pub fn into_inner(value: Self) -> Vec<u8>;
}
```

BufferReader implements Read/BufferedRead with its reader's effects. BufferWriter implements Write with its writer's effects. MemoryCursor implements Read, Write and Seek without host effects. Returning parts preserves unread or unwritten bytes; extraction must not silently discard a restricted inner stream owner. BufferWriter destruction MUST NOT perform an effectful flush. Use finish to request completion, or into-parts to recover the pending buffer. The type's principal ownership derives from its actual resident owners.

## 29. Paths, file handles, processes, clocks, and randomness

### 29.1 OS strings and paths

```glorious
pub struct OsString;
pub struct OsStr<'a>;
pub struct PathBuf;
pub struct Path<'a>;
pub enum PathComponent<'a> { Prefix(OsStr<'a>), Root, Current, Parent, Normal(OsStr<'a>) }
pub struct Components<'a>;
pub enum PathError { InvalidEncoding, InvalidComponent, UnsupportedPrefix }

impl OsString {
    pub fn new() -> Self;
    pub fn from_string(value: String) -> Self;
    pub fn as_os_str<'a>(value: &'a Self) -> OsStr<'a>;
    pub fn into_string(value: Self) -> Result<String,Self>;
}
impl<'a> OsStr<'a> {
    pub fn from_str(value: Str<'a>) -> Self;
    pub fn to_str(value: Self) -> Option<Str<'a>>;
    pub fn to_owned(value: Self) -> OsString;
}
impl PathBuf {
    pub fn new() -> Self;
    pub fn from_os_string(value: OsString) -> Self;
    pub fn as_path<'a>(value: &'a Self) -> Path<'a>;
    pub fn push(value: &mut Self, component: Path) -> Result<(),PathError>;
    pub fn pop(value: &mut Self) -> Bool;
    pub fn into_os_string(value: Self) -> OsString;
}
impl<'a> Path<'a> {
    pub fn from_os_str(value: OsStr<'a>) -> Self;
    pub fn as_os_str(value: Self) -> OsStr<'a>;
    pub fn parent(value: Self) -> Option<Self>;
    pub fn file_name(value: Self) -> Option<OsStr<'a>>;
    pub fn extension(value: Self) -> Option<OsStr<'a>>;
    pub fn is_absolute(value: Self) -> Bool;
    pub fn components(value: Self) -> Components<'a>;
    pub fn join(value: Self, other: Path) -> Result<PathBuf,PathError>;
    pub fn to_owned(value: Self) -> PathBuf;
}
impl<'a> Components<'a> { pub fn next(value: &mut Self) -> Option<PathComponent<'a>>; }
```

OsString represents valid native path/argument units for the selected target; it need not be valid UTF-8. Target-specific byte/wide-unit access belongs to an explicit platform module. Lexical path manipulation performs no I/O, follows the selected target's path syntax, and does not resolve symlinks. It cannot prove sandbox containment or replace a capability check. Canonicalization is an explicit host operation. Converting to display text lossily must be separately named and must not be used to reconstruct security-sensitive paths.

### 29.2 Files and process completion

```glorious
pub struct File;
pub struct DirectoryEntry { pub name: OsString, pub kind: FileKind }
pub enum FileKind { File, Directory, Symlink, Other }
pub struct Metadata { pub kind: FileKind, pub length: u64 }
pub enum OpenMode { Read, WriteTruncate, ReadWrite, Append, CreateNew }
pub enum CloseOutcome<R,E> { Closed, ClosedWithError(E), StillOpen { resource: R, error: E } }

pub effect FileSystem {
    open<'a>(Path<'a>,OpenMode) -> Result<File,IoError>
    metadata<'a>(Path<'a>) -> Result<Metadata,IoError>
    read_dir<'a>(Path<'a>) -> Result<Vec<DirectoryEntry>,IoError>
    canonicalize<'a>(Path<'a>) -> Result<PathBuf,IoError>
    create_dir<'a>(Path<'a>) -> Result<(),IoError>
    remove_file<'a>(Path<'a>) -> Result<(),IoError>
    remove_dir<'a>(Path<'a>) -> Result<(),IoError>
    rename<'a,'b>(Path<'a>,Path<'b>) -> Result<(),IoError>
}
pub effect FileHandle {
    read<'a,'b>(&'a mut File,SliceMut<'b,u8>) -> Result<usize,IoError>
    write<'a,'b>(&'a mut File,Slice<'b,u8>) -> Result<usize,IoError>
    seek<'a>(&'a mut File,SeekFrom) -> Result<u64,IoError>
    flush<'a>(&'a mut File) -> Result<(),IoError>
    sync<'a>(&'a mut File) -> Result<(),IoError>
    close(File) -> CloseOutcome<File,IoError>
}

pub struct Command { pub program: OsString, pub arguments: Vec<OsString> }
pub struct Child;
pub enum ExitStatus { Exited(i32), Signaled(i32) }
pub enum WaitFailure { StillRunning { child: Child, error: IoError }, ReapedWithError(IoError) }
pub effect ProcessControl {
    spawn(Command) -> Result<Child,Rejected<Command,IoError>>
    wait(Child) -> Result<ExitStatus,WaitFailure>
    terminate<'a>(&'a mut Child) -> Result<(),IoError>
}
```

File and Child are exact-linear protocol owners in this profile. They must be completed or transferred, not implicitly closed/reaped by an effectful Drop hook. A file may be usable after a failed close only in StillOpen. ClosedWithError means the resource is gone despite unsuccessful completion. Similarly WaitFailure distinguishes preserved child ownership from a reaped child. Processes can exit nondeterministically; terminate requests termination and does not replace wait/reap.

FileHandle operations are canonical direct effects, not a second list of same-named inherent forwarding methods. A File stream-trait implementation is a legitimate generic adapter: it exposes the Read/Write/Seek contract with Effects=FileHandle, without introducing free wrapper names. Directory listing order is unspecified; canonical output must sort explicitly. FileSystem rename does not promise cross-filesystem atomicity. Provider contracts specify error classification and platform support.

### 29.3 Clocks and durations

```glorious
pub struct Duration;
pub struct Instant;
pub struct SystemTime;
pub enum TimeError { Overflow, BeforeOrigin, DifferentClock, Unsupported, Host(IoError) }
impl Duration {
    pub fn zero() -> Self;
    pub fn from_parts(seconds: u64, nanos: u32) -> Result<Self,TimeError>;
    pub fn seconds(value: Self) -> u64;
    pub fn subsec_nanos(value: Self) -> u32;
    pub fn checked_add(left: Self, right: Self) -> Option<Self>;
    pub fn checked_sub(left: Self, right: Self) -> Option<Self>;
}
impl Instant {
    pub fn checked_add(value: Self, duration: Duration) -> Result<Self,TimeError>;
    pub fn duration_since(value: Self, earlier: Self) -> Result<Duration,TimeError>;
    pub fn compare(left: Self, right: Self) -> Result<Ordering,TimeError>;
}
pub effect Clock {
    monotonic_now() -> Result<Instant,TimeError>
    system_now() -> Result<SystemTime,TimeError>
    sleep(Duration) -> Result<(),TimeError>
}
```

Duration is normalized to `nanos < 1_000_000_000`; from-parts rejects an invalid subsecond component. Instant carries an opaque clock-domain identity; subtraction/comparison across distinct domains is an error. SystemTime is not monotonic. Sleep guarantees no exact wake time; it is a request to a provider and normally resumes once. Calendar/locale/time-zone databases are outside this version. Tests can supply deterministic Clock handlers without changing call sites.

### 29.4 Entropy and deterministic generators

```glorious
pub enum RandomError { Exhausted, InvalidRange, Unsupported, Host(IoError) }
pub effect Entropy {
    fill_random<'a>(SliceMut<'a,u8>) -> Result<(),RandomError>
}
pub trait RandomSource {
    type Effects: EffectRow;
    fn fill(value: &mut Self, out: SliceMut<u8>) -> Result<(),RandomError>
        / { | Self::Effects };
}
pub struct SeededRng;
impl SeededRng {
    pub fn from_seed(seed: [u8;32]) -> Self;
    pub fn algorithm_version() -> u32;
    pub fn next_u64(value: &mut Self) -> u64;
}
pub fn random_u64<R>(source: &mut R) -> Result<u64,RandomError>
    / { | R::Effects } where R: RandomSource;
pub fn random_below<R>(source: &mut R, exclusive: u64) -> Result<u64,RandomError>
    / { | R::Effects } where R: RandomSource;
```

RandomSource fill either initializes the complete supplied byte range or reports failure; callers must not interpret unspecified partial contents as a successful random value. Random-below rejects zero and has an unbiased distribution for a uniformly random source. SeededRng is deterministic for a documented algorithm version and implements RandomSource with an empty outward row; no cryptographic suitability is claimed by that trait or name. A release using it for reproducible artifacts must pin the algorithm version and seed. Entropy must be explicitly granted; no library operation silently consults a global RNG or clock.

## 30. Generators, futures, tasks, and cancellation

### 30.1 Why these contracts do not require an executor implementation

Yield and await are public effect operations. Their declarations specify suspension and ownership, but do not select an event loop, threading model, queue, task representation, or scheduling algorithm. Applications/embedders can install handlers with different scheduling policies. No special await/yield AST node, implicit async function transformation, or first-class effect-handler literal is introduced.

The interfaces below distinguish **owning a suspended state** from **borrowing that state to poll it**. Moving state through a step result is the ownership-general foundation. Borrowed polling is an optional adapter whose completed-state cleanup must be lawful. An operation named await must produce a computation's result, not return its own input unchanged.

### 30.2 Yield and owning generators

```glorious
pub effect Yield<Y,R> {
    [0,1] yield(Y) -> R
}
pub effect YieldOnce<Y,R> {
    yield_once(Y) -> R
}
pub enum GeneratorStep<Y,T,G> {
    Yielded { value: Y, rest: G },
    Complete(T),
}
pub trait Generator<R> {
    type Yield;
    type Return;
    type Effects: EffectRow;
    fn resume(value: Self, input: R)
        -> GeneratorStep<Self::Yield,Self::Return,Self> / { | Self::Effects };
}
pub fn close_generator<G>(value: G) where G: Use<[0,1]>;
```

Yield permits its continuation to be cancelled only when the language proves all captured residual state cancellation-safe. YieldOnce requires exactly one eventual resume; it can carry a must-move obligation across suspension but cannot be abandoned by merely destroying a generator object. Its different operation name is deliberate, not overloading.

Generator resume consumes one generator owner and either returns a yielded item plus successor owner or completes with the final result. Every suspended resident remains owned by rest. A completed generator cannot be resumed again because no successor owner was returned. Yield operation resume values are the caller's subsequent inputs; they are not copied from the yielded item. No Clone/duplicability of Y, R, or the generator is implied.

Close-generator performs only legal destruction; it is not a universal cancellation escape. A generator's Drop cannot issue new effects. A generator containing exact-linear state must be driven to completion or transferred to another owner. Generator producers are ordinary library/provider facilities checked against this trait; this section does not claim a compiler keyword that constructs generators automatically.

### 30.3 Owning futures and await

```glorious
pub struct WakeKey;
pub struct PollContext<'a>;
pub enum FutureStep<T,F> { Ready(T), Pending(F) }
pub trait Future {
    type Output;
    type Effects: EffectRow;
    fn poll<'a>(value: Self, context: &mut PollContext<'a>)
        -> FutureStep<Self::Output,Self> / { | Self::Effects };
}
pub effect Await<F> where F: Future {
    await(F) -> F::Output
}
```

```glorious
impl<'a> PollContext<'a> {
    pub fn wake_key(value: &Self) -> WakeKey;
}
pub effect Wake { wake(WakeKey) -> Bool }
```

WakeKey is an owning provider-issued notification token, not a borrow of PollContext. A wake request returns false when its registration has retired; it must not dereference freed state. The provider may coalesce notifications. This protocol allows a future to retain a wake key without retaining the temporary context itself.

Await is exact-once resumptive. Its payload transfers the entire future; a normal handler path must drive, transfer, or otherwise legally consume that future before resuming the awaiting continuation with its Output. It must not drop Pending state of an exact-linear future. Future Effects are effects of polling, not effects performed merely by constructing/moving its value. An await handler that polls F must itself handle or outwardly declare those effects; the public call's Await<F> identity retains F and its associated contracts.

Pending transfers the still-live future to the polling owner, which must retain it until polled again or lawfully cancelled. PollContext supplies provider-owned wake registration; a reference to the temporary PollContext may not escape in a future or retained callback. WakeKey is an opaque provider token with explicit lifetime/validity, not a native function pointer. The provider must prevent a wake operation from invoking freed task state. A wake is a request to make progress, not permission to resume an exact-once continuation twice.

This owning Future trait is a consolidation choice motivated by exact-linear states. A future borrowed `poll(&mut Self)` ecosystem can coexist through a differently named trait once its completion/close transition is specified; it is not silently substituted here.

### 30.4 Task provider interfaces

```glorious
pub struct Task<'scope,T>;
pub struct LinearTask<'scope,T>;
pub enum TaskError { Cancelled, Failed, ProviderClosed }
pub enum CancelOutcome<T> { Cancelled, Completed(T) }

pub effect Spawn {
    spawn<'scope,'env,E0,E1,T,F,e: EffectRow>(F) -> Task<'scope,T>
        where 'env: 'scope, T: 'scope,
              E0: Environment<'env>, E1: Environment<'env>,
              F: Fn<(),Output=T,Effects=e> + RunsIn<E0,(),After=E1>
                 + Use<[0,1]> + 'scope
}
pub effect SpawnLinear {
    spawn_linear<'scope,'env,E0,E1,T,F,e: EffectRow>(F) -> LinearTask<'scope,T>
        where 'env: 'scope, T: 'scope,
              E0: Environment<'env>, E1: Environment<'env>,
              F: Fn<(),Output=T,Effects=e> + RunsIn<E0,(),After=E1> + 'scope
}
pub effect TaskControl<'scope,T> {
    join(Task<'scope,T>) -> Result<T,TaskError>
    cancel_task(Task<'scope,T>) -> CancelOutcome<T>
}
pub effect LinearTaskControl<'scope,T> {
    join_linear(LinearTask<'scope,T>) -> T
}
```

Task and LinearTask handles are exact-linear owners: join/cancel transfers them to their provider. No implicit detach operation is supplied. Task permits cooperative cancellation of its worker only at boundaries whose entire continuation state is cancellation-safe. Its affine initial F is necessary for cancellation before the worker starts, but is not a proof that every later suspension is cancellation-safe. LinearTask has no generic cancel operation and must complete or remain owned until externally terminated with the whole execution.

**Control contract.** Spawn operations resume their callers exactly once with an owning handle. They transfer F to the provider; they do not execute F as argument evaluation. The provider owns the obligation to invoke F at most once for Task, and exactly once on normally completing execution for LinearTask. A Task cancelled before it runs lawfully destroys its affine F. A successfully produced T is transferred through join or Completed(T), never discarded merely because cancellation raced with completion. TaskError cannot encode loss of a produced exact-linear T. Provider-closed failures are permitted only after all transferred work/result obligations have been accounted for; otherwise the operation cannot return normally with that error.

A spawn operation generic effect row e is retained as part of the monomorphic operation contract and task registration. The provider must arrange handlers for the worker's declared row; this is not ambient capture of whatever handler happened to be on a native stack. Handler/label/reference dependencies must outlive the task; label-bearing work cannot outlive its direct-target scope. A caller cannot acquire a longer lifetime by choosing `'scope` in an explicit type argument.

The exact generic return type hides the provider's worker representation, not the worker's lifetime or effect obligations. Cross-thread execution additionally needs thread-safety contracts; no implicit Send/Sync or parallel runtime is promised by Spawn. These operations can be implemented by a single-threaded cooperative provider.

### 30.5 Structured completion

A lexical task scope MUST NOT return while child-owned borrows or exact-linear handles remain live. Scope cancellation is not implicit destructor I/O. A provider may offer a scope combinator, but its canonical interface must expose the child joining/cancellation contract and remaining effects; a universally safe `scope` with no such constraints is not specified here.

An async runtime is conforming only if it preserves deep-handler semantics, correct resumption quantities, capture ownership, target-label lifetime, and all reference validity across suspension. Scheduling fairness, timing, throughput, and networking integration are separate provider contracts. These protocol declarations alone do not claim a finished executor or guarantee progress against a noncooperative computation.

## 31. Required trait-instance and adapter matrices

### 31.1 Foundational instance families

The table is a declaration-family contract. A condition in a cell applies only to that instance. No row grants a blanket implementation for arbitrary user nominal types. `—` means no required instance, not a negative implementation.

| Type family | Eq / Ord | Hash | Clone | Default | Display / Debug |
|---|---|---|---|---|---|
| Unit, integer scalars, char | Required | Required | Required | Unit/zero/U+0000 | Required |
| f32, f64 | Required total-bit-consistent policy of §11 | Same equality policy | Required | +0 | Required deterministic forms |
| Bool | Inherited Result policy | Inherited | Inherited | false | Bool Display; inherited Result Debug |
| Result<T,E> | Corresponding traits on both payloads | Both payloads Hash | Both payloads Clone | — | Debug with both Debug; named formatter for display |
| Option<T> | Inherited Result policy | Inherited | Inherited | None, no T:Default | Inherited Debug; named fmt_option |
| Tuples of admitted arity | All fields implement corresponding trait | All fields Hash | All fields Clone | All fields Default | Debug on all fields; no generic Display |
| Fixed arrays [T;N] | T supports corresponding trait | T:Hash | T:Clone | T:Default | Debug when T:Debug |
| Shared references &T | Referent equality/order where implemented | Referent stream | Copy reference, not referent | — | Delegate borrowed value |
| Unique references &mut T | No required blanket ownership/Clone instance | — | — | — | Debug/Display by observing referent when supported |
| Str and String | Lexicographic UTF-8 bytes | Identical byte-string stream | String copies bytes; Str copies view | Empty String | Required |
| Slice<T>, Vec<T>, VecDeque<T> | Lexicographic when T supports it | Ordered sequence when T:Hash | Owned collections when T:Clone | Empty owner without T:Default | Debug when T:Debug |
| HashMap<K,V> | Eq with K:Eq+Hash and V:Eq; no Ord | — | K:Eq+Hash+Clone, V:Clone | K:Eq+Hash | Debug with K,V:Debug and lookup bounds |
| HashSet<T> | Eq with T:Eq+Hash; no Ord | — | T:Eq+Hash+Clone | T:Eq+Hash | Debug when T:Debug |
| Box<T> | Referent policy when T supports it | Referent policy | T:Clone | T:Default | Delegate borrowed referent |
| Typed IDs / generational IDs | Exact identity, including owner/generation where present | Same identity components | Required | No fabricated default ID | Debug; explicit numeric conversion |
| File, Child, tasks, linear iterators | No implicit equality/Clone by handle bits | — | — | — | Diagnostic identity only where explicitly documented |

Collection Eq/Hash/Debug methods borrow. They do not require resident discardability. Empty construction does not weaken an owner's static principal class: `Vec<Linear>` still needs lawful finalization even when currently empty. String and Str hashing are compatible for heterogeneous lookups. Raw pointers may support address comparison, but that is not referent equality or a lifetime proof.

Float total Eq intentionally differs from IEEE comparison. The generic PartialOrd implementation required for an Ord type returns Some of that total comparison; the separate named IEEE comparison APIs can report unordered NaN. Do not install mutually inconsistent trait equality and hashing just to imitate a host language's floating operators.

### 31.2 Iterator adapter instances

| Adapter | Required bound | Item | Effects | Additional completion behavior |
|---|---|---|---|---|
| Enumerate<I> | I:Iterator | (usize,I::Item) | I::Effects | Index arithmetic checked; overflow is an invariant/limit failure, not wraparound. |
| Rev<I> | I:DoubleEndedIterator | I::Item | I::Effects | Swaps front/back traversal. |
| Chain<I,J> | Both Iterator, equal Item | I::Item | Union | Exhausts first before second. |
| Take<I> | I:Iterator | I::Item | I::Effects | Stops after the requested number; retains source remainder. |
| Skip<I> | I:Iterator, Item affine | I::Item | I::Effects | Lawfully discards the skipped prefix. |
| Peekable<I> | I:Iterator | I::Item | I::Effects | At most one cached item; into-parts returns it. |
| Fuse<I> | I:Iterator | I::Item | I::Effects | Never polls source again after None. |
| Zip<I,J> | Both Iterator | (I::Item,J::Item) | Union | Retains an unmatched item and both remainders. |
| Map/Inspect/Filter/FilterMap/Scan | Exact callback bounds of §18.2 | The callback-derived type stated there | Source/callback union | Formation does not invoke callbacks. |

Marker implementations such as DoubleEnded/ExactSize/Fused are provided only when their laws follow from the source and adapter contracts. Filter is not automatically ExactSize; lending adapters do not masquerade as ordinary Iterator. Any owning adapter's principal use depends on every retained source, callback, cache and state owner, not just its yielded Item.

### 31.3 Required completion vocabulary

Every public owning container, entry, buffer, iterator, generator, future and resource must have a lawful completion path. This can be a consuming conversion, a finish-empty proof, a Step::Done transition, an operation that transfers the whole owner, or legal affine destruction. A generic `None` returned through &mut Self is not such a transition by itself.

For each concrete implementation, the exported contract must report its principal use rule, applicable Drop hook, and consuming completion operations. Unsafe internal storage must establish resident ownership; a pointer-shaped representation cannot make a container duplicable or freely discardable.

## 32. Supporting errors and precise failure distinctions

### 32.1 Numeric, length, and text failures

```glorious
pub enum ConversionError { OutOfRange, NonFinite, Fractional, PrecisionLoss }
pub enum RadixError { TooSmall, TooLarge }
pub enum IntParseErrorKind { Empty, InvalidDigit, InvalidSeparator, InvalidSign, Overflow, InvalidRadix }
pub struct IntParseError { pub offset: usize, pub kind: IntParseErrorKind }
pub enum FloatParseErrorKind { Empty, InvalidDigit, InvalidSeparator, InvalidExponent, TrailingInput, Overflow }
pub struct FloatParseError { pub offset: usize, pub kind: FloatParseErrorKind }
pub enum ToleranceError { Negative, NonFinite }
pub struct LengthError { pub expected: usize, pub actual: usize }
pub enum InsertError { OutOfBounds { index: usize, length: usize }, Reserve(ReserveError) }
pub enum StringEditError { Range(StringRangeError), Reserve(ReserveError) }
pub enum ScratchError { NonEmpty, InsufficientCapacity, Reserve(ReserveError) }
pub struct IndexOverflow;
pub enum HexErrorKind { InvalidDigit, OddLength, IncorrectLength }
pub struct HexError { pub offset: usize, pub kind: HexErrorKind }
pub enum Base64ErrorKind { InvalidDigit, InvalidPadding, NonCanonicalTail, IncorrectLength }
pub struct Base64Error { pub offset: usize, pub kind: Base64ErrorKind }
```

Numeric/text offsets count input bytes. Range checks choose Reversed before OutOfBounds before NotCharBoundary, so the same invalid request has deterministic precedence. Checked numeric helpers returning Option intentionally omit a reason; TryAs/explicit parse operations preserve a reason. Error constructors do not carry preformatted allocation-heavy messages unless the type explicitly owns one.

A Utf8Error's valid-up-to identifies the lead byte of the first invalid sequence. A truncated sequence has no complete invalid sequence length; `error_length=None` distinguishes it. UTF-8 validation rejects overlong encodings, surrogates and out-of-range scalars, and never turns malformed external bytes into a catchless character primitive fault.

### 32.2 I/O failures

```glorious
pub enum IoErrorKind {
    NotFound, PermissionDenied, AlreadyExists, NotDirectory, IsDirectory,
    InvalidInput, InvalidData, UnexpectedEof, WriteZero, Interrupted,
    WouldBlock, TimedOut, BrokenPipe, Unsupported, ResourceLimit, Other,
}
pub struct IoError {
    pub kind: IoErrorKind,
    pub native_code: Option<i64>,
}
```

IoError is a portable classification plus an optional diagnostic native code. The native code is not a stable cross-platform semantic identifier. Path text, credentials, raw addresses, or private payloads are not automatically included. Partial progress and ownership are represented by the operation-specific outcome types rather than hidden in a generic error string.

Recoverable Unsupported is different from an incompatible artifact/runtime contract. The latter is rejected at admission/linking before an unsupported operation silently executes. Neither IoError nor a user handler can catch or reinterpret a fatal violation of an unsafe contract.

### 32.3 Error trait and diagnostic conversion

```glorious
pub trait Error: Debug + Display {}
pub fn error_string<E>(value: &E) -> String where E: Error;
```

Error is an ordinary formatting/classification convention, not exception semantics, runtime type reflection, or a dyn trait hierarchy. All concrete leaf error records/enums defined in this document implement Debug and Display. Generic error outcomes implement them when their residents support them; they need not implement Error merely because their names end in Error. This avoids forcing an exact-linear recovered owner to be printable just to preserve it.

## 33. Required standard-library conformance cases

These are acceptance requirements for future implementations, not a report of tests executed for this draft. Each family must be checked under the interpreter and native backend where that profile is supported, and under changed operator/import names where name independence is relevant.

| ID | Required behavior |
|---|---|
| S01 | Bool, Option and Result aliases normalize to one representation and trait identity. |
| S02 | true equals Some(()) without a cast; it does not implicitly convert to an unrelated error instantiation. |
| S03 | None works as a structural generic constant in expressions and patterns. |
| S04 | Bool Default is false; overlapping generic Result Default is rejected. |
| S05 | Result::as_refs and Option::as_ref have different unit-error projection contracts. |
| S06 | replace/swap preserve exact-linear residents without Clone/discard bounds. |
| S07 | discard rejects exact-linear owners and continuation obligations. |
| S08 | if/else moves the same capture on mutually exclusive paths without duplicate ownership. |
| S09 | if without a covering alternative rejects an unsatisfied linear path. |
| S10 | Saving an unsealed if result cannot erase Available/environment obligations. |
| S11 | An Err produced after a callback ran retains that callback's post-state. |
| S12 | and/or sequencing accounts for paths that execute two callbacks, not just one. |
| S13 | Result operator payload discard bounds apply to the correct success/error type. |
| S14 | Distinct callback effect rows form a union; omission does not forge purity. |
| S15 | A skipped owning callback cannot lose an exact-linear capture. |
| S16 | Pattern-test binders appear only in the justified positive/negative contexts. |
| S17 | Mixed Bool/Test conjunction preserves positive binders; disjunction exports only common justified binders. |
| S18 | not exchanges both payloads and their binding contexts without erasure. |
| S19 | Renaming/importing control functions preserves all behavior and proof obligations. |
| S20 | match accepts an exhaustive pattern callable as an ordinary Fn argument. |
| S21 | A wildcard cannot discard a linear subject merely to make match exhaustive. |
| S22 | return/try/break_at lower to correctly scoped label transfer with protected payloads. |
| S23 | Ordinary loop fallthrough and continue form the same checked tail backedge. |
| S24 | Failed tail cleanup/borrow/handler proof is a compile-time error at O0 and optimized levels. |
| S25 | Nested loops returning the same B have distinct brands; no accidental outer catch. |
| S26 | An incorrectly typed inner break does not get inferred as an outer break. |
| S27 | continue_at selects the explicit target; break_at exits its label scope. |
| S28 | An open unique-reference hole is rejected on a cleanup-bearing loop exit. |
| S29 | Loop-state transfers exact-linear S through Continue and B through Break. |
| S30 | Loop execution retains bounded auxiliary control storage, not a hidden growing handler chain. |
| S31 | Integer boundaries cover every width, MIN negation, division zero/MIN÷−1, and invalid shifts. |
| S32 | Every scalar conversion pair follows the selected checked/wrapping/As policy. |
| S33 | Float NaNs canonicalize; signed zeros remain distinct for total Eq/Ord/Hash. |
| S34 | IEEE comparison and total comparison are deliberately distinguishable. |
| S35 | Decimal parsing rounds at destination precision; f32 does not silently parse through f64. |
| S36 | UTF-8 rejects malformed/overlong/surrogate/truncated input with stable byte offsets. |
| S37 | String slicing checks reversal, range and scalar boundaries before exposing a Str. |
| S38 | String-from-UTF8-recover returns the original byte owner on validation failure. |
| S39 | String/Slice borrowed views prevent invalidating mutation/reallocation. |
| S40 | SliceMut splitting returns disjoint views and preserves the input on checked failure. |
| S41 | Mutable iterator results refer to disjoint residents; overlapping windows are lending. |
| S42 | Vec insertion failure returns the input resident and leaves the receiver valid. |
| S43 | Vec clear/truncate/dedup discarding variants require affine residents. |
| S44 | Pop/remove/drain/partition transfers linear residents and preserves required order contracts. |
| S45 | Empty containers of linear element type use explicit lawful completion. |
| S46 | Zero-size residents receive the same move/Drop accounting as nonzero-size residents. |
| S47 | Rejected map insertion returns incoming key and value/old resident as specified. |
| S48 | remove-entry transfers K and V; value-only remove needs affine K. |
| S49 | A vacant entry cannot abandon an exact-linear candidate key. |
| S50 | Heterogeneous borrowed key lookup uses compatible Eq/Hash without allocating a new key. |
| S51 | Set duplicate insertion either returns the duplicate input or requires its discardability. |
| S52 | Maps/sets make no accidental iteration-order promise. |
| S53 | Iterator None does not magically consume its owning state. |
| S54 | Owning Step::Done finalizes the exhausted shell exactly once. |
| S55 | Zip returns a polled unmatched item and both source remainders. |
| S56 | Try-fold failure returns the accumulator and remaining iterator; the callback accounts for the item it consumed through its result or authorized deconstruction. |
| S57 | Filter/take/skip/scan abandonment accounts for retained sources/caches/callbacks. |
| S58 | Sorting preserves a valid permutation on comparator failure; stable ties retain order on success. |
| S59 | Stable-sort scratch preconditions are checked without silently discarding residents. |
| S60 | Hash streaming is incremental and Eq-consistent; semantic hashing never reads padding. |
| S61 | BLAKE3 fixed vectors, chunk boundaries and incremental input partitioning agree. |
| S62 | Fingerprints distinguish domain/version and framed byte sequences. |
| S63 | Formatting is locale-independent, appends through the declared formatter, and observes its explicit output bound. |
| S64 | Bounded diagnostics preserve a rejected diagnostic rather than silently dropping it. |
| S65 | Allocation failure, resize failure, zero size and alignment contracts preserve ownership. |
| S66 | Ptr-move/copy/drop reject or diagnose violated unsafe preconditions in available instrumentation; safe wrappers do not rely on byte copying to duplicate linear values. |
| S67 | CStr termination and UTF-8 validity remain separate checks. |
| S68 | Cross-engine objects retain identical backing storage and allocation-domain cleanup. |
| S69 | C callbacks cannot escape their registration lifetime or unwind/resume across an unadapted foreign frame. |
| S70 | Byte-reader truncation leaves the cursor unchanged; patching validates the whole range. |
| S71 | Varint decoding rejects overlong/noncanonical encodings and size overflow. |
| S72 | Arena rollback-take returns residents; discarding rollback needs affine T. |
| S73 | Stale generational IDs and foreign owner marks are rejected. |
| S74 | Interning duplicates return uninserted linear values unless a discardable variant is chosen. |
| S75 | Source byte/UTF-16 coordinate conversions reject invalid boundaries. |
| S76 | Memory charges and depth permits cannot be released twice or to an unrelated owner. |
| S77 | Parser attempt restores only its specified local cursor state, not arbitrary side effects. |
| S78 | Parser repetition detects successful no-progress iterations. |
| S79 | Graph/worklist traversal checks logical budgets during input-sized work. |
| S80 | Importing an effect exposes its operations without granting host authority. |
| S81 | Hosted ordinary I/O failures return typed results without cancelling exact-once continuations. |
| S82 | Typed host results are implemented at the provider boundary; wrappers do not pretend to catch fatal host faults. |
| S83 | Stream error reports retain exact committed prefixes; write-zero cannot spin forever. |
| S84 | Buffered finish failure retains both writer and unwritten bytes. |
| S85 | File close/child wait distinguish lost external resource from a safely reusable owner. |
| S86 | Path string operations do not pretend to resolve symlinks or prove filesystem containment. |
| S87 | Instants from different clock domains do not compare/subtract as ordinary timestamps. |
| S88 | Entropy/clock/process observation is explicit, and deterministic tests can replace its handler. |
| S89 | Yield cancellation is allowed only for cancellation-safe captured continuations. |
| S90 | YieldOnce's exact-once continuation cannot be discarded. |
| S91 | Future Pending transfers the only future owner; Ready consumes it. |
| S92 | Await returns Future::Output, preserves polling effects in its provider, and resumes exactly once. |
| S93 | Task cancellation racing with completion returns the produced T instead of discarding it. |
| S94 | LinearTask cannot be detached/cancelled by a generic affine cleanup helper. |
| S95 | Temporary poll contexts and wake callbacks do not outlive their valid provider state. |
| S96 | No source keyword or duplicated wrapper definition is needed for imported yield/await/fail/break/continue. |

## 34. Decisions, scope exclusions, and source traceability

### 34.1 Decisions selected in the conversation

The canonical library has no lazy parameter notation, no public choose, no free-function overloading, no forwarding functions that merely repeat effect operations, and no implicit compiler-known control names. Return/break-at are retained as readable label-invoking functions. Loop backedges require explicit tail proofs. The standard names are Glorious for the language/library and Grandiose for the compiler. Pattern matching accepts one exhaustive ordinary pattern callable. Numeric operators use independent traits, and public control contracts expose static Fn/RunsIn and path-sensitive ownership obligations.

### 34.2 Consolidation choices, not retroactively attributed decisions

| Choice | Resolution and reason |
|---|---|
| Refinement/control transport | Ordinary If/Else/And/Or dispatch plus a context-bearing carrier and sealed binding evidence; needed to compose pattern tests without overloading or forging lexical binders. |
| Branch-dependent ownership | Full guarded control contracts complement Fn/RunsIn; plain Result values cannot indefinitely hide unavailable environments. |
| Generative loops | One LoopControl<L,B> family with a distinct L per loop; a proof-only L argument indexes the callback contract, and result type alone is not a routing identity. |
| Truth constants | Closed Bool true/false; generic structural None; alias equality is not arbitrary Result error-type coercion. |
| Disposal | Public affine bounds; exact-linear completion paths on owning containers. |
| Profiles | Optional core/alloc/std dependency closures; host facilities do not become mandatory in every program. |
| Host errors | Recoverable typed ordinary OS failures; replace incompatible bindings rather than preserve a legacy HostFault interface. |
| File/process owners | Exact-linear completion through explicit operations rather than effectful Drop. |
| Future polling | An owning step protocol handles linear pending states; await directly performs its generic effect. |
| Task cancellation | Separate cancellable-work and linear-work protocols; cancellation races return completed output. |
| Formatting | Append-based formatting and deterministic scalar policy; no format macro/reflection subsystem. |
| Collection algorithms | Interfaces/complexity and ownership laws only; no fixed hashing-table layout, sort algorithm or growth strategy is prescribed. |
| Compiler toolkit | Generic reusable storage, indexing, diagnostics, budgets and codecs, not compiler AST/MIR/query-engine implementations. |

The most novel static obligations are guarded conditional contracts, refinement-context joins, and generative callback/loop interfaces. They are explicit design proposals with conformance requirements, not claims that the current Stage0 trait solver already supports them. A formal implementation must validate those obligations rather than accept an annotation as trusted proof.

### 34.3 What is deliberately not specified here

Networking transports, a concrete async executor, cross-thread memory-model APIs, arbitrary-precision arithmetic, full locale/Unicode property frameworks, regex, general serialization, reflection, macros, derive and runtime trait-object dispatch are not required by this version. This is not a prohibition on separately versioned libraries implementing appropriate source-level facilities. Their existence must not be implied by an undeclared placeholder type in the mandatory interface.

VM opcode assignments, binary-container layout, compiler queries, optimizer pass schedules, self-host bootstrapping steps, tool packaging and performance reports are engineering specifications outside these two semantic documents. The shared target ABI requirements remain normative in the companion. Those components may change together without backward compatibility; incompatible artifacts and caches are rejected or rebuilt, not silently reinterpreted.

### 34.4 Source register

Source references R01–R15 and X01–X04 are defined in the [language specification's source register](glorious-language-specification.md#23-source-register-and-reading-coverage). In particular: R02/R03 supply the baseline library and ownership contracts; R05/R06/R08 supply capture, effect and label constraints; R09/R12 supply native-memory/ABI boundaries; R10 supplies conversion policy; R07 and R13 motivate compiler-support facilities; X01 supplies the historical Result-based truth inspiration. Decisions made in this conversation and the explicit consolidation choices above take precedence over contradictory historical examples.

The old broad proposal was an idea inventory, not a second competing standard. These declarations supersede its abbreviated callback interfaces, lazy notation, redundant choose surface and obsolete effect wrappers. They have been editorially checked for cross-reference and interface consistency, but have not been compiled or validated by a formal type-system implementation.

**End of standard-library specification.**
