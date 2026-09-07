# Glorious Language Specification

**Consolidated intended-language draft 1.0 · 7 September 2026**

**Language:** Glorious. **Compiler/toolchain:** Grandiose. **Source suffix:** `.glorious`.

**Companion:** [Glorious Standard Library Specification](glorious-standard-library-specification.md).

**Repository baseline:** `MalekiRe/glorious@7e4a021811b6a8e0d62b2899f10e602d037c3c14`.

This is a proposed normative specification of the intended language, not a claim that the current compiler implements it. It consolidates the reviewed language contracts and the decisions made in the accompanying design conversation. Rules explicitly chosen during that conversation take precedence over historical repository prose. Additional resolutions made during consolidation are identified in the decision register. Examples illustrate intended source semantics; they have not been compiled against a conforming implementation.

The companion specifies library declarations and observable contracts, without algorithms or function bodies. This document specifies the mechanisms that make those declarations meaningful. Neither document is a compiler implementation plan, a migration tutorial, or a report of completed tests.

## Contents

1. [1. Authority, scope, and design principles](#1-authority-scope-and-design-principles)
2. [2. Compilation units, modules, imports, and preludes](#2-compilation-units-modules-imports-and-preludes)
3. [3. Lexical structure and literals](#3-lexical-structure-and-literals)
4. [4. Types, data, aliases, and representation](#4-types-data-aliases-and-representation)
5. [5. Functions, application, and binding](#5-functions-application-and-binding)
6. [6. Pattern callables and structural matching](#6-pattern-callables-and-structural-matching)
7. [7. Ownership and destruction](#7-ownership-and-destruction)
8. [8. Callable evidence, captures, and control composition](#8-callable-evidence-captures-and-control-composition)
9. [9. Lifetimes, borrowing, and refinements](#9-lifetimes-borrowing-and-refinements)
10. [10. Effects, handlers, and resumptions](#10-effects-handlers-and-resumptions)
11. [11. Labels and direct nonlocal control](#11-labels-and-direct-nonlocal-control)
12. [12. Explicit proper tail invocation](#12-explicit-proper-tail-invocation)
13. [13. Traits, generics, and inference](#13-traits-generics-and-inference)
14. [14. Operators, fixity, and conversion](#14-operators-fixity-and-conversion)
15. [15. Unsafe code and memory](#15-unsafe-code-and-memory)
16. [16. C foreign-function interface](#16-c-foreign-function-interface)
17. [17. Shared Glorious VM/native ABI](#17-shared-glorious-vmnative-abi)
18. [18. Failure, determinism, and resource limits](#18-failure-determinism-and-resource-limits)
19. [19. Core boundary and compilation invariants](#19-core-boundary-and-compilation-invariants)
20. [20. Compact grammar and declaration inventory](#20-compact-grammar-and-declaration-inventory)
21. [21. Required language conformance cases](#21-required-language-conformance-cases)
22. [22. Decision register and reconciliation](#22-decision-register-and-reconciliation)
23. [23. Source register and reading coverage](#23-source-register-and-reading-coverage)


## 1. Authority, scope, and design principles

### 1.1 Normative language

**MUST**, **MUST NOT**, **REQUIRED**, **SHOULD**, and **MAY** express conformance requirements. Text labeled **Rationale** explains a decision and does not add an independent rule. Code identified as a negative example MUST be rejected for the stated semantic reason. A diagnostic's exact wording is not normative.

The semantic subject of this specification is a well-formed package closure, its selected target contract, and its explicitly admitted runtime imports. Library names are not mechanisms. In particular, `if`, `else`, `and`, `or`, `not`, `match`, `loop`, `loop_at`, `break`, `continue`, `break_at`, `continue_at`, `return`, `yield`, `await`, and `fail` are ordinary resolved declarations. The compiler MUST NOT select a semantic path because one of these spellings occurs.

The structural language provides nominal data, bindings, functions and calls, pattern callables, lexical labels, effects and handlers, proper tail invocation, traits, lifetimes, ownership, unsafe contracts, and a finite target/runtime boundary. Operators become ordinary resolved calls after fixity grouping. No primitive Boolean type is required by this language; standard truth is library-defined.

### 1.2 Two authorities, not two competing definitions

This document owns lexical and typing rules, equality of types, lifetime relations, control/cleanup semantics, trait coherence, effect operation semantics, intrinsic evidence, and ABI obligations. The companion owns ordinary data definitions, traits, function/operation signatures, default policies, operator fixities, and behavioral library laws.

A library cannot relax this language's ownership or safety rules. A language implementation cannot silently replace a library declaration with an identically named intrinsic. The distribution binds genuine intrinsics by authenticated declaration identity and exact contract, not display path.

**Pre-alpha evolution policy.** Glorious, its standard library, Grandiose, and the VM are unfinished. There is no legacy source, API, ABI, host-binding, or G1 artifact compatibility obligation. They may change together; obsolete formats, interfaces, and decoder paths may be removed rather than preserved behind compatibility layers. Update the current specifications, implementations, fixtures, and bootstrap inputs together when changing a contract. Version/contract identities still distinguish incompatible inputs so they fail closed; they do not promise support for older inputs. This policy supersedes contrary preservation promises in earlier engineering documents. Current safety, ownership, verification, and full self-hosting requirements are not waived.

Compiler MIR structure, query scheduling, database revisions, optimization pass lists, build budgets, test totals, editor packaging, and bootstrap release milestones are not source-language semantics. Existing documents about those subjects remain engineering records. Their language-facing requirements are incorporated here; their internal algorithms are deliberately not promoted into this specification.

### 1.3 Governing principles

The following principles resolve otherwise ambiguous interpretation:

* Abstractions have ordinary source interfaces; compiler support is structural and name-independent.
* All closure bodies execute only on invocation. There is no `lazy` type, keyword, parameter category, or implicit arbitrary expression-to-function conversion.
* Ownership is preserved on success, failure, cancellation, nonlocal transfer, and partial initialization. A zero-sized value can still carry an ownership obligation.
* Static evidence is not runtime authority. Environment and label brands are compile-time identities; capture storage and actual jump targets are separate implementation realizations.
* Effects express observable requests and control, not permission to perform unsafe memory access. Imports control visibility; rows control permitted effects; host grants control external authority.
* The interpreter and LLVM-generated native code implement the same Glorious target ABI. Interoperation is not serialization, and C interoperability is a separate, explicit ABI boundary.
* A mandatory guarantee is checked. In particular, `tail` MUST either receive a proper-tail-call proof or a compile-time error, at every optimization level.

**Rationale.** The language should feel like ordinary systems programming with predictable movement and borrowing, while allowing control abstractions to be authored in the library. A compiler limitation must not be disguised as a design principle, and a design sketch must not be mislabeled as an implementation certificate. [R01–R10, D01–D09]

## 2. Compilation units, modules, imports, and preludes

### 2.1 Packages and source closure

A package has a driver-selected root and an explicit set of dependency packages. Source code cannot fetch a dependency, read arbitrary source files during type checking, or change its intrinsic manifest. Source acquisition and version selection belong to the build driver. The semantic compiler API accepts the complete supplied source closure and performs no ambient filesystem I/O.

The logical module layout remains the repository's self-named-directory convention. From a module in logical directory `D`, `mod child;` selects `D/child/child.glorious`. An inline `mod child { ... }` advances the same logical directory for its descendants. The chosen package root is exempt from this filename rule. A module is included only through a declaration; directory traversal does not implicitly import siblings.

Every dependency has a unique normalized package name. Hyphens in manifest names normalize to underscores in source. Normalization collisions and invalid identifiers are errors. Each package has its own parentless `crate` root.

A source bundle preserves file boundaries and original spans. Concatenation, where used, inserts a newline between files, but file order MUST NOT establish private-field authority or change resolution. Modules, not files, own privacy.

### 2.2 Declarations and visibility

Module items are private by default. `pub` exports an item. `pub(crate)` and `pub(super)` restrict visibility to the current package or parent module. Record and tuple-struct fields are private by default in this consolidated language; `pub` and restricted visibility can expose individual fields. This intentionally replaces older public-field defaults.

The declaring module and its descendants have access to its private fields and items. Sibling and parent modules require suitable visibility. Re-exporting a type does not expose its private representation. Privacy is checked at resolved declaration identities, including through aliases and generated code.

Safe ownership deconstruction requires authority over every deconstructed field. An opaque exact-linear value can be moved as a whole or handed to an authorized consuming function; calling an unrelated helper or guessing a layout does not discharge it.

### 2.3 Namespaces and imports

There are separate namespaces for types, values/callables, traits, effects, lifetimes, labels, and generic parameters where their kinds require it. Nominal type constructors occupy the corresponding value namespace as well as the type namespace. `@name` looks only in the label namespace; bare `name` never resolves to a label.

Imports support `crate`, `self`, `super`, explicit names, aliases, groups, globs, and re-exports:

```glorious
use crate::syntax::Token;
use crate::syntax::{Token, Span as SourceSpan};
use util::collections::*;
pub use crate::control::LoopControl;
```

Declarations, aliases, and imports are resolved to a deterministic fixed point. Benign re-export cycles are legal; unresolved or conflicting imports are errors. Two visible functions with the same unqualified name do not form an overload set. Local lexical bindings can shadow imports. Explicit imports take precedence over prelude/glob candidates; two distinct explicit candidates are ambiguous.

An inherent function is addressed as `Type::member`, with owner and member generic arguments separated: `Map<K,V>::get<'a>(...)`. An inherent namespace cannot contain two declarations with the same name, even if their self types, arities, or bounds differ. Trait-qualified operations remain distinct declarations rather than overloaded inherent functions.

### 2.4 Effect operation imports

An effect declaration introduces a family name and public operation bindings. `use p::Effect;` imports that family and its visible operations under their declared names. Selective imports such as `use p::Effect::{read, write as emit};` import only those operation bindings; the family can independently be named through qualification or another import. `use p::Effect as E;` renames the family, not its operations. A selective import is the escape hatch for operation-name collisions.

Calling an imported operation performs the exact same operation as a qualified call. There is no forwarding function, different effect identity, or runtime wrapper. A `pub use` preserves the original declaration identity and contracts. Importing an operation does not grant its outward effect, a host capability, or unsafe permission.

An explicit conflicting operation import is an ambiguity error. The compiler MUST NOT choose a declaration by argument type, expected return type, handler proximity, or import order. Generic instance inference happens only after a unique operation declaration has been resolved.

### 2.5 Optional standard library

Standard-library inclusion is optional in the intended language. A build selects the language's intrinsic/runtime contract and a library profile independently. A normal build injects the selected standard prelude at lowest import priority. `#![no_std]` suppresses the hosted standard library and its prelude; `#![no_implicit_prelude]` suppresses all automatic library imports. Explicit dependency and intrinsic contracts still apply.

No-std does not mean no runtime, no allocator requirement for dependencies, or arbitrary intrinsic implementations. A program must provide every dependency and runtime service its selected code actually uses. This specification does not permit an alternative library to impersonate sealed evidence by copying a name.

**Rationale.** Rust-like import ergonomics and module authority are useful independently of Rust's filesystem convention. Effect functions should feel like callable names already in scope, not second-class requests hidden behind wrappers. [R01, R04, R06, D10–D12]

## 3. Lexical structure and literals

### 3.1 Text and tokens

Source files are valid shortest-form UTF-8. Invalid encodings are lexical errors with byte spans; the compiler must not silently replace invalid input. A leading UTF-8 BOM may be ignored only at file offset zero. LF and CRLF are accepted as line endings and preserved in source maps.

Identifiers use `[A-Za-z_][A-Za-z0-9_]*` in version 1. Unicode is supported in strings and character literals, not identifier classification. `_` alone is the wildcard/discard pattern, not a readable binding. Lifetimes are `'name`, `'static`, and `'_`; label names are `@name`. Comments are `//` to the end of the line and nestable `/* ... */` blocks. Comments and whitespace separate tokens and have no semantic side effects.

Reserved structural words are `fn`, `let`, `mut`, `const`, `struct`, `enum`, `type`, `trait`, `impl`, `where`, `effect`, `handle`, `tail`, `is`, `move`, `unsafe`, `extern`, `mod`, `pub`, `use`, `as`, `infix`, `infixl`, `infixr`, and `prefix` where the grammar assigns them structural roles. `as` is contextual in an import; in expression position it remains an ordinary library function name. `for<...>` is a higher-ranked binder in constraint position; elsewhere `for` may name a library function. `self`, `super`, `crate`, and `Self` are contextual path/type forms.

`if`, `else`, `and`, `or`, `not`, `match`, `loop`, `break`, `continue`, `return`, `yield`, `await`, `fail`, `true`, `false`, `Some`, and `None` are not reserved lexical keywords. Renaming their declarations does not change the grammar.

### 3.2 Numeric literals

Integer literals support decimal, `0b`, `0o`, and `0x` bases, with underscores between digits but not an empty digit run or an invalid digit. Explicit suffixes name a scalar integer type. Magnitude checking occurs after expected-type selection, not in the lexer. Unsuffixed integer literals default to `i64` only after other ordinary constraints have been solved. Out-of-range magnitudes are errors; there is no implicit wrap of a literal.

Floating literals support decimal digits, an optional fractional part, and an optional `e`/`E` exponent with signed exponent digits. A suffix can select `f32` or `f64`; otherwise the default is `f64`. Decimal-to-binary conversion rounds directly at the selected width using round-to-nearest, ties-to-even, without an intermediate wider parse that could double-round. Finite source-literal overflow is an error; subnormal values and underflow follow the target floating contract. NaN and infinities are library constants, not identifier-like numeric tokens.

A leading `-` is an operator, not part of the literal token. An immediately negated, directly width-constrained integer literal may use the signed minimum magnitude; this is a literal-range elaboration rule, not permission for arbitrary negative unsigned literals.

### 3.3 Character, text, and byte literals

A character literal denotes one Unicode scalar value. Supported escapes are `\n`, `\r`, `\t`, `\0`, `\\`, `\'`, `\"`, ASCII `\xNN`, and scalar `\u{H...}`. Surrogates and values greater than U+10FFFF are rejected. A byte literal `b'x'` denotes one `u8`; non-ASCII content requires a numeric byte escape.

`"..."` is immutable static UTF-8 data materialized through the selected library's manifest-bound literal view, normally `Str<'static>`. `b"..."` is static octet data, normally `Slice<'static,u8>`. Runtime values use ordinary library types. Neither representation exposes a forgeable static-segment descriptor. There is no interpolation or format-string macro in version 1.

### 3.4 Tuple punctuation

`()` is both the unit type and unit value. `(x)` is grouping. `(x,)` is a one-element tuple. `(x,y)` is a two-element tuple. The same rules apply in types and patterns. Function argument lists and effect operation payload lists use parentheses, but they do not erase the distinction between one tuple argument and several arguments (§5.2).

## 4. Types, data, aliases, and representation

### 4.1 Type families

The language types include unit `()`, bottom `!`, the fixed integer families `u8/u16/u32/u64/u128` and `i8/i16/i32/i64/i128`, target-size `usize/isize`, `f32/f64`, `char`, tuples, fixed arrays `[T; N]`, shared/unique references, raw pointers, nominal records/tuple structs/enums, and compiler-created callable and continuation types.

There is no primitive source `bool`, nullable reference, arbitrary runtime type object, or universal boxed `Any`. Library sums express absence and failure. `!` has no values and a diverging expression can inhabit an expected result position without constructing a value or inventing a normal post-state.

All source value types in version 1 are sized. Borrowed dynamically sized sequences use library `Slice`/`Str` values rather than an unsized-type subsystem. A later unsized-type extension must specify layout and trait implications separately.

### 4.2 Nominal declarations

```glorious
pub struct Point { pub x: f64, pub y: f64 }
pub struct Pair<A,B>(pub A, pub B);
pub struct Ticket(u64);
pub enum Result<T,E> { Ok(T), Err(E) }
pub enum Node { Leaf(i64), Branch { left: u32, right: u32 } }
```

A tuple struct is nominally distinct from its field tuple. Constructor application creates the corresponding owner, with ordinary left-to-right evaluation and visibility checking. Numeric projections `.0`, `.1`, etc. select tuple or visible tuple-struct fields; they do not select an enum payload by unchecked numeric position.

Recursive nominal definitions are allowed when runtime layout is finite. Recursion through references or pointer-owning library types does not inline an infinite field layout. Trait/quantity derivation must not confuse an indirection with an owned-layout cycle. Directly embedding `Self` without indirection is rejected.

Enums are closed within the defining package unless declared `#[non_exhaustive]`. A non-exhaustive exported enum cannot be ownership-deconstructed outside its authority; external matching must borrow or forward an unrecognized whole value. A future variant cannot be silently destroyed by `_` when its type is exact-linear.

### 4.3 Transparent aliases and constant patterns

`type Alias<T> = Representation<T>;` introduces a synonym, not a new nominal type. Aliases share trait identity, layout, use class, and associated implementation coherence. Two alias-qualified impls that overlap are an error. The compiler does not select formatting, equality, or methods according to which alias spelling was written.

The companion's `Option<T> = Result<T,()>` and `Bool = Result<(),()>` are consequently definitionally equal to those instantiations. `true`, `Some(())`, and `Ok(())` are the same Bool value after constructor/constant alias normalization. This is not a truthiness conversion or a blanket conversion between different Result instantiations.

`true` and `false` are closed Bool constants. `None<T>` is a structurally evaluable generic constant scheme producing `Result::Err(())`; every occurrence materializes a fresh appropriately typed value, not an unrestricted global owner of arbitrary T. Constructor aliases retain constructor identity. The constant evaluator may normalize structural scalar/tuple/record/enum values but cannot run arbitrary effectful functions.

Constant patterns use structural constant values of the expected type. They do not call user `Eq`, do not perform effects, and do not invoke arbitrary initializers. A bare pattern identifier resolves to an imported constant/constructor alias if one exists; otherwise it introduces a new binder. A qualified unresolved path is always an error. An explicit `let name` pattern forces a binder when a constant would otherwise capture the spelling.

Floating-point constants are not structural equality patterns in version 1. Use ordinary comparison inside a body to choose an IEEE or total-order policy explicitly.

### 4.4 Layout and target sizes

The Glorious ABI uses `usize/isize` with the selected target's pointer width. Fixed integer types remain fixed. Compiler lowering, VM operations, native layout, artifact contracts, and tests must adopt this rule together. The current fixed-64-bit G1 implementation is not a legacy compatibility target. Inputs built for an incompatible contract are rejected or rebuilt, not silently interpreted using a different width.

Tuple/record field order, enum layout, alignment, and calling convention follow §17's Glorious ABI. Private fields have ordinary runtime storage. Static evidence erases only when it has no resident runtime payload or observable cleanup. Padding is not a source value and cannot be assumed initialized.

**Rationale.** One data vocabulary should cover tuples, tuple structs, enum payloads, function arguments, and patterns without collapsing nominal identity or tuple arity. Aliases should make ordinary equivalent values interoperate, not establish ad hoc implicit conversions. [R01, R04, R05, D13–D17]

## 5. Functions, application, and binding

### 5.1 Function declarations

Every named function is declared with `fn`. Parameters have declared types. A result annotation is required except that omission means unit. No outward effect annotation means the closed empty row. `-> ()` and `/ {}` are accepted explicit forms; canonical formatting omits them. `-> !` is never omitted.

```glorious
pub fn length(text: Str) -> usize { Str::len(text) }
fn reset(value: &mut Counter) { value.count = 0; }
fn log(text: Str) / Diagnostic { write(text); }
```

A function body evaluates to its final expression. A semicolon discards a statement result only if that result permits destruction. The lack of an explicit return annotation is not inference of an arbitrary result type.

Each function declaration and literal has a fresh anonymous nominal callable type. Noncapturing items need no capture allocation. There is no free-function overloading, arity overloading, or implicit selection between two functions of the same resolved name. Traits can supply independently named operations selected by an explicitly resolved trait contract.

Bodyless declarations ending in `;` are legal only as trait members, foreign declarations, or exact runtime-manifest bindings. An ordinary bodyless source function is an error. A placeholder body returning unit is not a valid implementation of an intrinsic.

### 5.2 Argument tuples and evaluation order

Function application evaluates the callee expression first, then each argument exactly once from left to right. Capture expressions belonging to explicitly materialized arguments are evaluated at their argument positions. Structural control bodies follow §8's contextual-capture rule; their execution is not evaluation of their bodies as arguments.

Every callable has an argument-tuple type `Args`. Surface `f(a,b)` supplies the tuple `(a,b)` to the call relation, and `f()` supplies `()`. `f((a,b))` supplies one tuple-valued argument and therefore has argument shape `((A,B),)`, not `(A,B)`.

For trait notation, a one-argument callable uses `Fn<(T,), ...>`. The old ambiguous `Fn<(T), ...>` spelling is not canonical and is rejected as a tuple argument pack when `(T)` merely groups T.

### 5.3 Local bindings, assignment, and moves

`let name = expr;` creates an immutable local binding; `let mut name = expr;` permits assignment and unique borrowing of that place. A variable's mutability does not make its type duplicable. A variable holding `&mut T` can mutate its referent without making the reference binding reassignable.

`place = expr;` is a statement, not an expression. `:=` is not part of the language. A destination must be a mutable local, a legal projection of one, or a place accessible through a unique reference. Evaluate the RHS first. If the destination is initialized, destruction of its old resident must be legal; if it is uninitialized, assignment restores it without destroying an old value.

An ordinary owned use copies a duplicable value and moves a nonduplicable value. `move place` forces transfer even for a duplicable type. `&place` and `&mut place` explicitly request borrowing; a bare owner is not automatically borrowed because of an expected parameter type. Passing an already existing reference can use an ordinary reborrow rather than move when the expected reference relation selects it. There is no general automatic dereference conversion.

General assignment through overloaded indexing is excluded from version 1; obtain a checked unique element reference and assign through it. Compound assignments are ordinary trait-backed conveniences only where their one-evaluation place contract is specified; they are not implicitly part of every arithmetic operator.

### 5.4 Anonymous functions and contextual blocks

Explicit anonymous syntax is `fn(parameters) -> R / row { body }`, with the same unit and empty-row omission rules. Compact callables are `{ => body }` for no arguments, `{ x => body }` for one argument, and `{ (x,y) => body }` for the argument tuple of a multi-argument expected callable.

A block in a call argument or operator operand is checked after unique callee/signature selection. If its expected parameter satisfies an applicable `Fn` or `RunsIn` constraint, it becomes a fresh callable of the required argument shape. Its body executes only when invoked. Otherwise it is an ordinary immediately evaluated block. A contextual block with no explicit parameter clause can leave expected inputs unnamed only when each ignored input permits destruction. This also allows a proof-only duplicable label argument to be supplied by a generic caller and left unnamed by a block. It does not silently ignore an exact-linear argument. An explicit `{ => ... }` remains a zero-argument callable. Ambiguous interpretation is a type error, not a callee-name heuristic.

This rule does not convert a computed noncallable value into a function. `while({ condition() }) { work() }` supplies a callable condition; `while(condition()) { work() }` does not. Likewise the unambiguous compositional spelling is `value or { alternative() }` and `if(c) { a } else { if(d) { b } else { c } }`. A special unbraced `else if` parser rule is not introduced.

Trailing blocks are ordinary final arguments. Both `f(args) { body }` and `f { body }` are available; the latter means a call whose only explicit argument is that block. They do not introduce new control syntax for particular functions.

### 5.5 Named function exit

Every named function activation introduces an implicit generative label `@function_name` of the function's result type. Recursive calls create different activations and different dynamic destinations. Anonymous callables have no implicit named exit.

```glorious
fn parse(input: Str) -> Result<Value,ParseError> {
    // `parse(...)` is a recursive call; `@parse(...)` exits this activation.
    @parse(Err(ParseError::Empty))
}
```

The standard `return(value,@parse)` is an ordinary function using that label. There is no implicit dynamically selected return destination and no compiler keyword named `return`.

## 6. Pattern callables and structural matching

### 6.1 One callable, several clauses

An arm block consists of one or more ordered `Pattern => Body` clauses. It elaborates to **one anonymous callable**, not a tuple of independently capturing closures and not an effect-handler value.

```glorious
match(result) {
    Result::Ok(value) => process(value),
    Result::Err(error) => recover(error),
}
```

The expected argument type supplies the scrutinee type. A single binder clause is the ordinary compact-function case. For a one-argument expected callable, a clause pattern matches that argument; for a multi-argument expected callable, its tuple pattern matches the argument tuple. Thus `Fn<((A,B),)>` and `Fn<(A,B)>` remain different callable contracts even when both use an `(x,y)` pattern inside an already known context. Missing expected arity must not silently conflate them.

Without an expected callable type, qualified constructors and explicit annotations can determine the input. Otherwise the callable remains locally inferable until its first constraining use; ambiguity at a generalization/escape boundary is an error. Pattern clauses do not make a function runtime-polymorphic.

### 6.2 Exhaustiveness and priority

Every pattern callable MUST be exhaustive over its declared argument type. Clauses are tried in source order; the first matching clause executes exactly once per invocation. Unreachable clauses are diagnosed. An uncovered input is a compile-time error, not an implicit `None`, failure effect, or abort.

`_` is a valid catch-all, but it discards the matched value or subtree. Consequently an owned exact-linear subject cannot be covered by `_` merely to satisfy exhaustiveness. Bind and transfer it, match by borrow, or exhaustively deconstruct it with authority. Exhaustiveness and legal disposal are separate checks.

Supported patterns are binders, `_`, structural constants, tuples, fixed arrays with statically checked arity, tuple structs, records, enum variants, references, and one `..` remainder. Duplicate binders are illegal. Ranges, pattern guards, OR-patterns, arbitrary user pattern traits, and view patterns are not version-1 features; use explicit callable composition instead.

### 6.3 Pattern ownership and borrows

Matching an owned subject transfers selected fields or the whole subject. Matching a shared/unique borrow yields corresponding references under ordinary pattern-borrow ergonomics; it does not copy a nonduplicable referent. Copying a payload is legal only when its type is duplicable. There is no implicit Clone.

An exhaustive, authorized ownership deconstruction consumes the shell and creates independent obligations for extracted residents. Omitted fields, `_`, and `..` are zero-use destruction requests for those exact subtrees. An aggregate with custom Drop cannot be safely ownership-deconstructed; use a defining-module consuming API whose unsafe internals establish a separate contract when necessary.

Clause bindings are lexical within that clause. They cannot be referenced from siblings. The compiler may internally represent them using binding packs, but the ordinary `match` function receives a single callable accepting T, not user-visible per-clause `Bindings` parameters.

### 6.4 Environments and effects

All clauses begin from the same incoming callable environment. Every normally returning clause must produce a compatible post-environment and result type. Diverging clauses contribute no normal result or normal post-environment; their cleanup and terminal-transfer obligations still apply.

The callable's outward row is the union of reachable clause rows. Equality of callback effect rows is not required. Clause-local loans do not become simultaneous loans merely because both clauses mention the same place. Captures belong to one callable environment and are disposed according to the actual selected path.

Pattern callables can be stored, passed, and returned subject to ordinary capture lifetime/use restrictions. Reusability depends on callable receiver evidence, not the number of clauses. They can perform effects in their bodies but cannot intercept operation syntax as pattern heads outside `handle`.

**Rationale.** Library `match` can be ordinary application. First-class effect handlers are not needed, and no `Match` intrinsic or user-implementable pattern protocol is introduced. [D18, R01, R06]

## 7. Ownership and destruction

### 7.1 Three principal classes

Ordinary source types have exactly one principal use class:

| Contract | Meaning |
|---|---|
| `Use<[0,*]>` | Duplicable; zero, one, or arbitrarily many owned uses are permitted. |
| `Use<[0,1]>` | Affine; zero or one owned use is permitted. |
| `Use<[1,1]>` | Exact-linear; the live owner must be transferred or authorizedly deconstructed. |

A bound requests a permitted interval; it is satisfied when that interval is contained in the type's principal interval. Therefore a duplicable type satisfies affine and exact-once requests, and an affine type satisfies an exact-once request. `T:Use<[1,1]>` does **not** assert that T's principal class is exact-linear.

No source nominal type may declare another principal interval. The compiler can use arbitrary intervals and finite path alternatives internally. Compiler-created resumptions have their operation's special invocation quantity (§10), which is not a fourth ordinary user-declarable ownership class.

The intrinsic `Use` has no methods. One manual principal declaration may restrict, never widen, structurally available capability. `Use` is not globally sealed against these checked restrictions. `Fn`, `RunsIn`, `Environment`, `Label`, and availability/binding evidence remain compiler-sealed.

### 7.2 What counts as an owned use

A whole move into a parameter, aggregate, result, or continuation transfers the ownership obligation to the destination. An exhaustive authorized deconstruction consumes the shell and transfers resident obligations to field owners. A structural copy creates an additional owner and is allowed only for duplicable types. A borrow does not consume the borrowed owner's use.

Destruction is zero use. Calling a destructor does not satisfy a must-move obligation. Moving a value through an identity function does not make the returned value discardable. A by-value generic helper cannot erase an exact-linear obligation by claiming that the call already counted as its required use.

Unit, scalar integers/floats/characters, raw pointers, and shared references are duplicable as values. Raw pointer copying does not copy or authorize ownership of a pointee. Unique references are affine. A resource owner may be exact-linear even if its representation is fieldless.

### 7.3 Structural derivation

A struct's available class is the intersection of its owned fields' allowed intervals. An enum's class must be safe for every possible variant. A fieldless variant contributes unrestricted capability but does not make `Option<Linear>` globally affine. Fixed arrays propagate resident constraints, including zero-length and zero-sized-resident distinctions; an explicitly empty instantiation may be proved resident-free through its concrete type.

References derive their own handle class instead of inheriting their referent's class. Private pointer-owning library representations must use compiler-checked ownership markers and unsafe invariant contracts so that residents not syntactically stored by value still determine owner behavior.

A source-defined quantity-only `PhantomData<T>` marker can forward T's principal class through one constrained quantity parameter, ranging over the three admitted classes. It has no resident T and does not independently establish pointer provenance, initialization, lifetime/variance evidence, or safe destruction. This is a checked generic principal restriction, not three overlapping selectable Use implementations.

Recursive capability derivation through pointer owners is a monotone fixed-point problem, not proof that a finite layout is infinitely large. Unresolved evidence is not unrestricted evidence. Manual impls are coherent principal restrictions, not several selectable permissions.

### 7.4 Flow and joins

Sequential owned uses add quantities; mutually exclusive branches join by interval hull; repeated use can create an unbounded upper limit. Interprocedural control summaries record actual execution alternatives rather than deducing invocation counts from a may-effect row.

An owner is usable only when definitely initialized and available. At an affine branch join, the compiler may retain a **maybe-initialized** place plus a conditional cleanup flag rather than immediately destroying a resident to force equality. Such a place cannot be read or moved until definitely restored. Scope cleanup destroys only the paths where it remains initialized. This gives Rust-like conditional moves without fabricated uses.

A positive-lower owner must have a legal disposition on every normally completing local or nonlocal path. A conditional exact-linear state may remain within a proven control island, but cannot cross a boundary that loses the relevant branch correlation. The compiler MUST NOT silently discard an exact-linear resident to merge environments.

### 7.5 Partial moves and initialization holes

Visible distinct fields may be moved independently from a type without custom Drop. Their residual shells retain initialization masks; cleanup skips moved-out slots. Using the whole partially moved owner is illegal until all required fields are restored.

`move *reference` through a live unique reference may create an initialization hole. The reference remains live but cannot be read, reborrowed, moved, ended, captured by a resumption, or passed to code that may inspect its referent until restoration. Every normal completion and every cleanup-bearing nonlocal exit that ends this loan MUST restore it or prove a complete authorized transfer of the storage obligation.

**A terminal effect or break is not an exception to this rule.** It can run cleanup and return control elsewhere. Immediate process abort has no continuation or cleanup; proven nontermination has no exit. Those are different from leaving through a label or effect handler.

### 7.6 Drop

The intrinsic destructor contract is:

```glorious
trait Drop: Use<[0,1]> {
    fn drop(value: &mut Self);
}
```

Only one checked implementation is permitted. It has no outward effects, cannot suspend, transfer to a label, capture/resume a continuation, move fields out, or return ownership of Self. It may use internally justified raw release operations with their unsafe contracts. A type with positive-lower principal ownership cannot implement Drop.

Destruction runs the custom hook once, then active owned fields in reverse declaration order, then releases enclosing storage. Locals are destroyed newest-owner first; aggregate field destruction is reverse field order. Partial initialization is honored. A hook may diverge, in which case later cleanup does not run; termination is not proved.

`Use<[0,0]>` is not a public source bound in this revision. The compiler uses the internal predicate `MayDiscard(T)`—equivalent to zero belonging to the allowed interval—to justify zero-use destruction. Public APIs and Drop use the affine bound. This resolves the earlier bound/principal distinction without introducing a fourth class.

### 7.7 Cleanup boundaries

Ordinary returns, label exits, terminal effects, cancellation, failed initialization, and tail transfers share the same disposition requirements. Protect transferred payload owners before destroying intervening locals. Destroy each remaining eligible resident exactly once in the prescribed order. An effectful `close` or `flush` must be called explicitly; Drop cannot conceal it.

Immediate abort and fatal runtime faults terminate without ordinary cleanup. They are not recoverable exceptions, and a program cannot rely on causing a fault as a legitimate source disposal operation.

**Rationale.** Three public classes retain the useful ownership distinctions. Path-sensitive initialization preserves familiar conditional movement, but no wrapper, wildcard, failure, or cleanup path turns a must-move resource into garbage. [R01–R04, D19–D22]

## 8. Callable evidence, captures, and control composition

### 8.1 Intrinsic relations

The following declarations describe compiler-intrinsic relations. Source can name them in contracts but cannot implement the sealed relations or construct their brands.

```glorious
trait Fn<Args> {
    type Output;
    type Effects: EffectRow;
}

trait Environment<'scope> {}

trait RunsIn<Access, Args>: Fn<Args> {
    type After;
}

trait Label<T>: Fn<(T,), Output = !> {}
```

`Fn` is a call relation for a receiver type, not an ordinary trait with a user-defined `call` method. A relation can exist for `F`, `&F`, or `&mut F`. There is no separate FnOnce/FnMut trait family. `RunsIn` uses those same receiver forms and describes access to an execution environment independently of the callable's physical capture layout.

In a source bound, unqualified `Fn`/`RunsIn` requires a safe-to-invoke callable. An `unsafe Fn<...>` or `unsafe RunsIn<...>` bound admits an unsafe callable with the exact signature and requires an explicit unsafe scope at invocation. This is a safety qualifier on the intrinsic relation, not a user-handleable effect or an additional callable ownership class.

`Access` is `E`, `&'a E`, or `&'a mut E`, where `E:Environment<'scope>` and `'scope:'a`. Owned access can change the environment. Shared and unique borrowed access preserve its reusable normal post-state, `After=E`. These are proof-level access forms; no pointer to an Environment object is passed at runtime.

An invocation needs applicable Fn and RunsIn evidence, lawful receiver movement/borrowing, available environment access, satisfied lifetime constraints, and permission for the outward effects. The compiler prefers shared receiver/access, then unique, then owned, only among solutions already compatible with the explicit source form and expected signature. It must not use this preference to invent a missing trait impl.

### 8.2 Ordinary closure capture

Captures are inferred at the granularity of nonoverlapping places. Observations request shared access, mutations request unique access, and consuming a nonduplicable captured place requests ownership. Ordinary ownership, privacy, and outlives rules apply. Capturing a duplicable value does not implicitly invoke Clone.

`move (places) { ... }` is an optional owned-capture assertion: listed duplicable places are copied into the new environment; listed nonduplicable places are moved. Other captures are inferred. Overlapping incompatible entries are errors. The marker changes capture formation, not what operations the body may perform on the captured value.

A materialized closure that owns exact-linear residents cannot be discarded merely because its body will not run. A borrowed invocation cannot move an owned resident out of a stored callable and leave a hole that its owner later observes. Repeatedly calling `&mut F` is not permission to duplicate F or consume its residents repeatedly.

### 8.3 Correlated contextual alternatives

A linked call/operator expression can relate several contextual bodies through one unresolved `E:Environment<'env>`. Those bodies are checked against the same incoming ownership ledger, not independently materialized as competing owners of their common captures. Each body has its own footprint and RunsIn proof. The shared ledger contains every relevant place, lifetime, and residual obligation from their union.

Only structurally proven mutual exclusion permits this sharing. Sequential calls are sequential transitions. A function named `choose` receives no special privilege, and the standard library does not need such a public function. A user-defined selector is accepted or rejected by the same proof rules as the standard `if`/`else` chain.

Once bodies escape as independently stored owning closures, normal capture semantics apply. Two separately constructed closures cannot both own the same exact-linear value merely because a later caller might select one. The compiler may fuse correlated alternatives into branches or use a shared physical capture representation, but representation choices cannot change ownership or effect order.

### 8.4 Full interfaces include guarded control contracts

A flat signature `F:RunsIn<E,Args,After=S>` is sufficient for a single uniform normal post-state. It is **not by itself a complete contract** for a function returning different values on paths with different environment states. In particular, appending that bound to `if(...)->Result<...>` does not explain how a later `else` recovers the unused environment.

Every higher-order callable therefore has a checked **control contract** in its abstract interface. The compiler derives and validates this contract from structural calls, patterns, label transfers, handlers, and ownership transitions. It contains:

| Component | Required information |
|---|---|
| Callable parameters | Selected receiver forms, argument tuples, result/effect equalities, and lifetime dependence. |
| Invocation alternatives | Which callbacks run on which paths, in what order and multiplicity; unused paths. |
| Environments | Incoming access, guarded post-environments, and compatibility at each normal join. |
| Results | Structural result-tag guards that preserve a correlation with a particular originating result. |
| Exits | Normal completion, direct labels, terminal operations, continuation capture, cancellation, and divergence. |
| Resource dispositions | Receiver/capture transfer, unused-body cleanup, partially initialized residents, and returned loans. |

In the companion, tables labeled **Control contract** are normative parts of an interface, alongside the source declaration. They are not replacement implementation bodies. A distribution must check its implementation against them; copying an annotation cannot create evidence. The same derived interface is available to user-defined control abstractions. There is no compiler-known inventory of privileged control names.

For example, the abstract contract of a two-way result mapper may state `Ok(input) => invoke F from E0 to E1; Err(input) => retain E0`. The guards refer to resolved nominal variants and the particular result's provenance, not the strings `Ok`, `Err`, `if`, or `else`. This contract may be abstracted and serialized without leaking the caller's local-place identities.

**Rationale.** This resolves a gap in the experimental signatures. Neither effect rows nor a single After parameter can encode branch-correlated callback consumption. Making the checked control contract explicit avoids pretending that hidden compiler intuition supplies the missing constraints. [R01, R03, R07, D23]

### 8.5 Open post-environments and availability

`Available<'env,E>` is a compiler intrinsic witness that a particular environment transition has not yet occurred on a path. It is unforgeable, proof-only, and scoped by E's originating lifetime. It can be transferred to another checked control composition, consumed when activating an applicable RunsIn transition, or closed when zero use of the reserved environment is legal.

Conceptual intrinsic interface:

```glorious
fn available_to_unit<'env,E>(value: Available<'env,E>)
where E: Environment<'env> + Use<[0,1]>;
```

This is not a general zero-sized-type conversion. Consuming it must dispose of any associated runtime capture storage lawfully; static erasure cannot skip observable cleanup. The witness's allowed use follows whether the environment's pending obligation permits abandonment.

Within one linked control island, the compiler retains guarded post-states until a later operation consumes or joins them. An `Err` returned after actually running a callback carries that callback's post-state; it does **not** restore the pre-callback environment. There is no transactional rollback implied by Result failure.

An unresolved guarded environment may not escape into a plain variable, aggregate, function return, opaque call boundary, or serialized interface that loses its correlation. A stored plain `Result` must be sealable at that boundary. An explicit type that carries availability and runtime ownership could support a future resumable builder, but the standard Result type does not acquire invisible persistent typestate in this revision.

```glorious
// Valid when both selected branches legally consume ticket:
if(condition) { redeem(ticket) } else { refund(ticket) };

// Rejected when the initializer cannot seal its conditional linear state:
let unfinished = if(condition) { redeem(ticket) };
// A later `else` cannot retroactively repair that boundary.
```

### 8.6 Backedges and terminal exits

A repeated body must restore every backedge invariant before normal fallthrough or continuation to the next iteration. A terminal exit can have a different post-state, but its abandoned residents and loans still need lawful disposition. `RunsIn<&mut E,...,After=E>` alone does not prove a safe consuming break path; the complete control contract must account for that path.

A contextual body that moves an outer owner only on a proven loop exit may be accepted through structural control fusion and exact place-flow evidence. The same source body is not automatically callable through `&mut` after being stored as an independently owning closure. When uniform reusable evidence is insufficient, use explicit owned-state iteration or report a source error; never assert that an initialization hole is safe merely because an effect result is `!`.

### 8.7 Effects, suspension, and execution counts

Rows are may-effect permissions. They do not imply that any operation actually occurs. A handler can multiply or abandon a captured continuation according to the operation quantity. Interprocedural summaries must distinguish finite normal-return multipliers, terminal alternatives, cancellation, unknown repetition, and divergence. Unknown evidence cannot justify an exact-once consumption claim.

## 9. Lifetimes, borrowing, and refinements

### 9.1 Regions and reference contracts

Lifetimes are lexical names for inferred regions, not runtime integers. The language supports nonlexical lifetime inference, `'_`, `'static`, outlives bounds `'a:'b` and `T:'a`, higher-ranked bounds, generic associated lifetimes, and drop checking.

Every returned reference must originate in a permitted input or retained owner and remain valid for its declared region. Equal reference types do not imply equal provenance. Branch-dependent returned references can preserve the union of possible input origins when the declared lifetime contract covers all of them. A local owner cannot be escaped by renaming its lifetime.

Shared references may coexist. A unique reference excludes conflicting reads, writes, moves, destruction, and aliases for its live region. Reborrowing creates a child loan and suspends conflicting parent use until that child ends. Distinct statically known fields can be borrowed separately; dynamic indices overlap unless a checked disjoint-view operation proves otherwise.

### 9.2 Elision and variance

Each omitted input lifetime introduces a distinct inferred lifetime. An omitted output lifetime follows a single input lifetime when unambiguous; a conventional reference receiver can supply the method's output relation. Multiple unrelated candidates require an explicit relation. `Str` is library shorthand for `Str<'_>`, not a static string.

Shared references are covariant in referent and lifetime. Unique references are covariant in lifetime and invariant in referent. Function input positions are contravariant and result positions covariant. Nominal variance is derived from representation and normalized associated projections. Unnormalized projections are treated conservatively. Compiler-created brands are invariant; two equal-looking environments are not interchangeable.

A custom Drop hook is assumed to observe all borrowed fields, which must remain live until cleanup. No `may_dangle` escape is defined. Lifetime erasure at code generation never erases the corresponding checked reference-return contract at ABI boundaries.

### 9.3 `is` tests

`subject is Pattern` is structural syntax because a runtime trait function cannot introduce a lexical binder. The subject is evaluated exactly once. In version 1, `is` is observational: duplicable projections may be copied; other projections are borrowed under the subject's lifetime. Refutable moving tests must use an exhaustive pattern callable or handler instead.

The compiler produces positive/negative binding environments using sealed `Bindings<'a,P>` values. A standard result-like test carrier records those environments. A contextual body can receive a hidden binding-pack argument when its expected callable relation requires it; only then do the pattern's names enter that body's scope. The compiler checks the full hidden argument tuple, not merely the visible parameter list.

`is` is not a user-implementable predicate protocol. A negative test establishes only facts justified by the failed structural match. It does not establish a closed-world negative fact about arbitrary user traits.

### 9.4 Test composition without overloaded control functions

The compiler supplies the sealed relation `BindingContext<'a>:Environment<'a>` with associated argument tuple `Args` and GAT `BorrowArgs<'b>` for `'a:'b`. Empty context has both tuples equal to `()`. A nonempty P has `Args=(Bindings<'a,P>,)` and `BorrowArgs<'b>=(&'b Bindings<'a,P>,)`. These are actual Fn/RunsIn arguments, even when their source spelling is omitted during contextual elaboration. Source cannot implement this relation or activate arbitrary binder names by declaring an ordinary trait implementation.

The companion's ordinary `BranchResult<'a,T,E,P,N>` carries a success or failure payload together with the corresponding context. `Test<'a,P,N>` is its unit-payload alias. Plain Result remains its original nominal type. Ordinary If/Else/And/Or dispatch traits supply one public function per name across these carriers; they do not become intrinsic truthiness operations. The full selected implementation's callable and guarded control contract is part of the generic call interface.

Contextual if passes its positive binding argument to the selected body; else passes the negative argument to its fallback. A general Result payload is not itself a binding pack. Not exchanges the positive and negative contexts with their payloads. Conjunction can retain the left positive context while its right callable borrows it; disjunction can retain the negative context on the alternative path. A joined context exports only names with the same binder identity and compatible type/loan origin on all paths represented by that context. Equal source spelling is not equal binder identity.

Context combination and projection evidence is compiler-checked against original pattern provenance. Closing a pack requires lawful cleanup of residents and guards. No surviving reference may depend on a moved or destroyed pack's physical storage. The ordinary library can transport already valid context values, but cannot forge their sealed evidence. These rules resolve the older ambiguity between a plain Result-returning test, a distinct Test enum, and callbacks whose hidden arguments were omitted from their signatures.


## 10. Effects, handlers, and resumptions

### 10.1 Effect declarations and operation payloads

An effect is a nominal family with type/lifetime/const/brand parameters and declared operations. Payloads use tuple-style positional types; no `fn` keyword or runtime field names are required inside the effect declaration:

```glorious
pub effect Console {
    read() -> String
    write(Str)
}

pub effect Stop<E> {
    fail(E) -> !
}
```

Operation payloads are ordered argument tuples. The complete callable/operation type records lifetime relations; borrowed payloads must name those relations when not inferable. Unit operation results may omit the arrow. A resumptive operation defaults to `[1,1]`. Terminal operations return declaration-site `!` and have no continuation or quantity annotation.

Effect identity is declaration identity plus normalized generic arguments. Different generative brands distinguish otherwise identical instances. A function or alias named like an operation does not perform an effect unless resolution identifies the operation declaration itself.

### 10.2 Effect rows and union

Rows denote unordered, duplicate-free sets of normalized effect instances. They use braces; a singleton may omit braces. Tuple parentheses remain products, not effect unions.

```glorious
fn a() / { FileRead, Diagnostic }
fn b<e: EffectRow>() / { FileRead | e }
fn c<e1: EffectRow,e2: EffectRow>() / { | e1, e2 }
```

After `|`, a comma-separated sequence of row terms denotes their union. A row term can be a row parameter or normalized associated effect row. For example `{|e1,e2}` is exactly `e1 ∪ e2`, not an ordered row and not an implicit constraint that the two rows are equal. This multi-tail union is a deliberate addition needed for honest full callback signatures.

Duplicate instances normalize away only after type/const/brand equality is proved. Row subtraction used by complete handlers removes exactly handled instances. A partial operation/payload handler retains that effect instance outward. Rows support equality and inclusion constraints; a caller permits a callable whose exact outward row is a subset of the caller's permitted row. Contextual permission does not falsify the callable's recorded exact row.

Unification does not arbitrarily split a known row among several unknown union operands. Infer operands from their callables/arguments first; unresolved nonunique splits are ambiguity errors. Executable interfaces cannot retain unresolved row variables.

### 10.3 Contextual instance inference

An imported generic operation may have a brand/type parameter absent from its payload, as with `continue()`. The compiler resolves its declaration first. It then uses the nearest contextual callable contract that explicitly names an instance of that same effect family as its default instance. Forwarded row tails are permissions, not competing defaults. The resulting explicit family arguments must match the payload and all rigid constraints; a type mismatch is an error rather than permission to select an outer instance.

This is a general inference rule for effect families, not recognition of `loop`, `break`, or `continue`. The default comes from an explicit signature prefix, not the order of an unordered normalized row. Two explicit instances of one family in the same context are ambiguous and require qualification/type arguments or a payload such as a label that selects the instance. Already inferred parameters and explicitly supplied parameters are never changed.

An uncontextualized helper with several permitted instances cannot guess a target. Its signature must identify an instance explicitly or quantify over one to be chosen at the call. Runtime dispatch remains nearest matching **exact** instance; it is not “nearest operation with a compatible return type.”

### 10.4 Performing and installing a handler

Calling an operation evaluates its payload arguments left to right, transfers owned payloads, and routes to the nearest active handler for the exact normalized instance and operation. `perform` is not canonical syntax and is not part of version 1.

```glorious
handle computation {
    Result::Ok(value) => value,
    Result::Err(error) => recover(error),
    Console::write(text) => emit_text(text),
    Console::read(k) => k(next_line()),
}
```

`handle` evaluates its computation under the installed delimiter. The arm block is structurally attached to `handle`; it is not an arbitrary first-class handler literal. Completion patterns match the computation's normal result. If none are supplied, an implicit identity completion arm applies. Supplied completion arms must be exhaustive.

For a resumptive operation with payload arity n, an arm with n payload patterns is a tail-resume arm: the arm result has the operation result type and resumes once. An arm with n+1 patterns binds the final continuation explicitly and returns the handler result type. An exact `[n,n]` operation with n greater than one cannot use the once-only tail-resume abbreviation. The condition is that **one lies in the permitted quantity**, not merely that the upper bound is at least one.

A terminal operation has only its payload patterns and its arm returns the handler result. It never receives a phantom continuation. Completion patterns and operation patterns are classified by resolved declaration identity and expected handled row; an unresolved ambiguity is an error.

### 10.5 Clause scope and forwarding

Handlers are deep: invoking a captured continuation reinstalls the same delimiter around the resumed computation. The operation clause itself executes outside the delimiter it is servicing, unless a nested explicit handler is installed. Its own effects therefore forward to surrounding handlers rather than accidentally reentering the same clause. This rule avoids silently recursive handling of an operation emitted by its own clause.

Payload alternatives for one operation are first-match, source-ordered pattern matrices. Only proven exhaustive coverage of every operation and payload domain removes an effect family from the outward row. Otherwise unmatched requests forward. Handler clauses share their own capture environment according to the actual dispatch/repetition structure, not an unconditional “exactly one arm over the entire handler lifetime” claim.

Completion clauses run on normal completion of the protected computation, including completion of a resumed continuation. They do not run as an invented fallback for an unhandled operation, cancellation, fatal fault, or label leave. Any completion transformation is part of a resumption's handler-result contract.

### 10.6 Resumption quantities

Version 1 admits optional one-shot `[0,1]`, exact one-shot `[1,1]`, and exact finite `[n,n]` for positive u32 n. `[0,*]`, `[1,*]`, and non-exact finite intervals are deliberately not surface contracts in this revision. The compiler's internal arithmetic may remain more general.

A one-shot resumption is invoked through ordinary application `k(value)`. An optional resumption may be legally discarded, which cancels its captured continuation. An exact positive resumption cannot be dropped on a normally completing clause path. In exact finite multi-shot use, the first n−1 invocations use independently valid snapshots and the last consumes the original continuation authority. Uses through aliases must still account to the same logical resumption obligation.

Multi-shot capture requires structurally duplicable initialized captured residents, no live unique borrow, no captured label destination, and compatible replayable handler dependencies. Clone is not automatically called to make a capture replayable. Moved-out slots are absent from snapshots; residual initialization masks and alias relationships must be preserved. Repetition of effectful observable behavior is real repeated behavior, not speculative rollback.

Cancellation destroys captured initialized residents only where each permits zero use. Capturing a continuation that could be canceled while retaining an exact-linear resident is rejected. Exact-once suspension can carry obligations that optional cancellation cannot, provided its lifetime/loan constraints are satisfied.

### 10.7 Terminal effects and faults

A terminal operation abandons the delimited continuation without producing a resumption. Its owned payload is protected and transferred; other abandoned owners must be legally cleaned before clause execution. This does not destroy the independent handler environment or the caller's borrowed closure owner indiscriminately. Cleanup follows actual ownership locations and boundaries.

A terminal source effect can be handled and control can continue outside its delimiter. It is therefore not equivalent to process abort, and it cannot leave a borrowed owner invalid. A fatal runtime fault terminates without source recovery; ordinary external failures should use the library's typed results rather than deliberately trigger such a fault.

### 10.8 First-class operations, not first-class handler blocks

An effect operation can be imported, aliased, and passed as a callable item with its exact outward row and operation identity. Calling it still performs the operation. A continuation can also be an ordinary callable value with compiler-created restrictions.

An arm block containing effect-operation clauses cannot be stored as a first-class handler policy in version 1. Multi-clause pattern callables do not change that. Ordinary functions can install handlers around supplied computations; they must expose the relevant callback, lifetime, environment, and effect contracts.

**Rationale.** Direct operations avoid repetitive wrappers. Exact rows compose by union. Restricted resumption intervals give an implementable public contract while preserving the quantitative theory internally. Handler repetition is not ordinary mutually exclusive value matching. [R01, R06, D25–D29]

## 11. Labels and direct nonlocal control

A typed scope `@name: T { body }` creates a fresh invariant brand L with intrinsic `L:Label<T>` evidence and a lexical lifetime. The block's result is T, whether supplied normally or by a direct label invocation. An omitted label type is allowed only when ordinary constraints infer it uniquely.

`@name(value)` and a generic parameter invocation `target(value)` where `L:Label<T>` both transfer directly to the designated scope, after required cleanup. The label value is duplicable, proof-only, non-addressable, and cannot escape its originating scope. It is not a C function pointer or a runtime code address.

Every specialization invoking a label must resolve one active generative destination. Label-bearing generic helpers and callables MUST be structurally control-inlined/fused into that destination's frame, or rejected. Inlining here is a correctness requirement, not an optional optimization. An unavailable body, opaque indirect boundary, unsupported recursive label cycle, or foreign call cannot be repaired by dynamic stack search.

A label may index an effect family without becoming runtime payload. A label argument can select such an instance at compile time and erase after checking. A type-correct label target does not itself imply an active handler for every effect indexed by that label.

The standard `break_at(value,@outer)` and `return(value,@function)` invoke labels. `continue_at(@outer)` performs an explicitly imported label-indexed loop operation and requires an associated active loop handler. Labels remain destinations; they are not overloaded between “exit” and “restart.”

## 12. Explicit proper tail invocation

### 12.1 Meaning

`tail callee(arguments)` is a checked transfer of the current activation's result destination to the callee. It MUST execute without retaining an additional continuation/activation for the current call. Over a repeated tail cycle, live call/control storage must not grow merely with iteration count. The requirement applies at O0 as well as optimized builds and to both interpreter and native execution.

An ordinary call may be optimized to a tail call when semantics permit, but only explicit `tail` requests mandatory diagnostics on failure. A tail site can be direct or indirect through a callable whose exact runtime contract and receiver mode permit it.

### 12.2 Required proof

The compiler must prove result/ABI compatibility, no required computation after the call, legal evaluation of callee and arguments, lawful transfer of argument/receiver owners, valid reference provenance after the current activation ends, and complete disposition of every remaining current-frame owner. Any direct label or active handler dependence that must survive must remain in a valid enclosing scope without an accumulating per-iteration retained frame.

Evaluate callee and arguments left to right into protected transfer storage. Then perform the cleanup whose scope explicitly ends at the tail transfer, end eligible loans/delimiters, and transfer execution. The language's `tail` form ends these scopes at that point; it is not a promise that replacing any ordinary returning call with `tail` preserves destructor timing.

A reference into current-frame local storage cannot be sent to a callee after that storage is reclaimed. Heap allocation or silently retaining the old frame is not an acceptable way to pretend a rejected proper tail call was accepted under the same contract. A compiler may use a proven constant-space trampoline or equivalent representation only when it preserves all specified ownership/control behavior.

### 12.3 Handlers and loops

A syntactically final recursive call inside a handler is not automatically a proper tail call. The old delimiter, clause captures, outstanding reborrows, and any computation return transformation can make the call non-tail. If the compiler cannot discharge or fuse those obligations, `tail` MUST fail.

A loop kernel should ensure that one iteration's handler and temporary loans have ended before its recursive backedge, or prove an equivalent structural fusion. Merely marking each recursive handler-arm call `tail` does not certify the implementation. The library contract requires the eventual backedge proof but does not prescribe the implementation body.

### 12.4 Diagnostics and negative cases

Reject a tail call with reachable following work; a tail call forwarding a borrow of a destroyed local; a tail call that bypasses required result transformation; a tail call retaining per-iteration cleanup or handler state; and a cross-ABI tail call with no proven compatible transfer convention. Diagnostics identify the blocking source obligation rather than reporting “optimization failed.”

**Rationale.** The user's requested `tail` is a language guarantee. LLVM's optional `tail` marker alone does not establish it; the implementation needs a verified mandatory-tail lowering or an equivalent constant-space mechanism. [R08, X02, D30]

## 13. Traits, generics, and inference

### 13.1 Generic kinds

Generic parameters have explicit kinds: ordinary type, lifetime, supported structural const, or `EffectRow`. Type parameters do not serve as row tails and lifetimes do not become types. Defaults may reference earlier binders of compatible kinds. `Self` means the fully instantiated implementation head, not a type constructor to be reapplied.

Const parameters support booleans only through structural library constants, fixed scalar integers, and closed structural enum/tuple values admitted by the compiler's terminating const normalizer. Array lengths are checked nonnegative integers representable as the target's indexing size. Ownership-quantity declarations accept only the three public class spellings. Const normalization cannot perform I/O, arbitrary recursion, or effectful runtime calls.

A direct call may provide a prefix of ordinary type arguments and infer the remaining type arguments from values and expected result. Omitted lifetime, row, or const arguments follow their own inference rules rather than automatically participating in that prefix convention. Explicit arguments are constraints, not hints.

### 13.2 Traits and coherence

Ordinary traits support associated types, associated effect rows, generic associated types, supertraits, associated equality constraints, default method bodies, receiverless functions, and higher-ranked bounds. Implementations are nominal and coherent. There is no specialization, overlapping implementation preference, ad hoc function overload resolution, or trait-object/dynamic-vtable source type in version 1.

An impl is legal only when the trait or the outer nominal self type is local to the package, subject to the intrinsic rules. A local target argument alone does not authorize a foreign-self conversion impl. Two impl heads that can unify under legal substitutions conflict; compilation does not choose the more specific one.

Negative impls can establish exclusion when orphan/coherence rules allow them. Failure to find a positive impl is not proof of a negative trait fact. Compiler-created closed refinement brands and explicitly sealed closed-world relations can supply justified negatives. General user trait cycles do not prove themselves.

Inherent functions have explicit receiver arguments. Dot-call method syntax is not introduced by these specs; `Vec::push(&mut values,item)` is the canonical call. This preserves the existing explicit-call model while adding Rust-like imports, borrowing, tuple structs, and individual operator traits. A future method-sugar revision must define receiver adjustment and ambiguity separately.

### 13.3 Higher-ranked bounds

`for<'a> Bound` introduces fresh universal regions. Higher-ranked type/const/brand/row binders are permitted where their kinds and constraints are explicit. A universally quantified label brand is evidence supplied by a generative binder, not a user-constructed runtime label.

Each higher-ranked check uses fresh rigid placeholders and a leak check. It cannot force an outer inference variable to contain a newer unbound region or brand. Nested binders preserve their scopes through associated projections and specialization.

### 13.4 Inference order and ambiguity

Type checking is bidirectional. Resolve names and fixities, select the unique callable/trait declaration, infer independently known argument constraints, then elaborate contextual bodies. This constraint-seeding order does not reorder runtime evaluation. Numeric defaults apply only after non-defaultable constraints have been considered.

Associated projections normalize under the exact lexical trait evidence, including ordered GAT arguments and their kinds. Contradictory or recursive normalization is diagnosed. Unresolved Fn/RunsIn obligations remain obligations after a type variable is assigned; solving the type alone is not proof of callability.

Effect rows use the explicit union and inclusion rules of §10. Callable result inference permits bottom on diverging branches but does not equate every branch's exact effects. A truly unconstrained generic value cannot escape as runtime polymorphism.

### 13.5 Solver termination and interfaces

Trait solving, alias expansion, const normalization, effect normalization, and lifetime reasoning must be resource-bounded and deterministic for a fixed configured limit. Exhaustion is an explicit diagnostic, never guessed success. A conforming implementation is not required to accept programs whose static proof search exceeds its declared limits.

Abstract interfaces preserve generics, exact declaration identities, visibility, safety, representation, normalized trait/effect relations, variance, callable environment/control contracts, and reference-return provenance. They exclude caller-local place IDs and unresolved inference cells. Importers must validate any proof metadata whose corruption could alter acceptance or safety.

## 14. Operators, fixity, and conversion

`infixl`, `infixr`, `infix`, and `prefix` introduce module-scoped fixity with precedence from 0 through 255. Higher numbers bind more tightly. Prefix operators nest to the right. Equal-precedence infix operators must have compatible associativity; nonassociative chains require parentheses. One spelling may have independent prefix and infix fixity, but an ordinary function declaration still has one arity and one resolved identity. Fixities can explicitly bind a position to an ordinary declaration: `prefix 50 - = numeric::neg;` and `infixl 30 - = numeric::sub;` use two differently named functions, not one overloaded function. The shorthand `infixl 3 and;` uses the same-named resolved binding. A position/token pair has one selected declaration; generic trait dispatch inside that declaration remains ordinary coherent dispatch.

The compiler collects fixities before grouping body expressions. A word with a fixity remains an ordinary identifier. Grouped operations become ordinary calls with left-to-right operands and normal contextual block checking. Imported operators bring their declared fixity; conflicting explicit fixities are errors.

A fixity declaration does not supply implicit borrowing that its target function does not declare. The standard scalar comparison operators can consume duplicable operands. For nonduplicable values, compare explicit borrows or call the trait's borrowed equality/order function; a hidden second evaluation or automatic Clone is forbidden.

`&`, `&mut`, dereference `*`, `=`, `->`, `=>`, `::`, and the label/lifetime sigils have structural grammatical roles. They are not blanket-overloadable. Bitwise operations use ordinary named library functions in this revision to avoid changing structural punctuation rules.

Numeric conversion is explicit through library `as<T>(value)` or checked APIs. There is no implicit numeric promotion, Bool truthiness conversion, multi-step conversion search, or arbitrary coercion based on equal size. Transparent aliases require no conversion. Reborrowing, lifetime shortening, bottom coercion, and manifest-defined literal materialization are the limited structural coercions.

## 15. Unsafe code and memory

### 15.1 Safety contracts

`unsafe fn` declares caller obligations. `unsafe { ... }` acknowledges obligations at a call or operation site; it does not disable ordinary typing, ownership, privacy, or lifetime checking for other expressions. An unsafe function's body still uses explicit unsafe scopes for its unsafe operations. A closure created inside an unsafe block does not inherit unsafe permission into its deferred body.

An unsafe trait declares invariants on which safe generic code may rely; an unsafe impl establishes them. Ordinary traits such as As, Eq, Hash, or Clone do not grant optimizer or safety assumptions beyond their declared safe contracts. A forged unsafe invariant remains invalid execution; the syntax does not make it true.

### 15.2 Raw pointers and storage

Raw pointers `*const T` and `*mut T` are separate from checked references. Creating/copying an address does not establish initialization, lifetime, aliasing, or ownership of T. Dereferencing or constructing a reference from a raw pointer requires alignment, valid provenance, a valid initialized T, live storage, permitted access, and an accurately bounded lifetime.

Allocation APIs pair a domain, layout, and release operation. Reallocation must preserve initialized residents and invalidate old addresses only under its contract. Checked size arithmetic prevents wraparound before allocation or pointer range derivation. One-past pointers can be formed where the allocation contract permits but cannot be dereferenced. Zero-sized residents still require correct logical initialization, transfer, and destruction.

Raw reading a resident as an owner is a move unless duplicability explicitly permits a copy; the implementation must mark the source uninitialized and must not subsequently destroy the moved value. Bytewise copying a nonduplicable T is not ownership duplication. Bulk moves must honor overlap and initialized-range contracts. Uninitialized padding may not be inspected as a defined byte value or hashed as semantic state.

### 15.3 Validity and forbidden forgery

Unsafe code must not manufacture invalid enum tags, invalid references, invalid Unicode scalars, dangling callable identities, or forged Label/Environment/Bindings/Available evidence. C-compatible integers, raw addresses, and guessed layouts do not become host grants or sealed compiler evidence.

Pointer-to-integer address inspection does not preserve permission to reconstruct a dereferenceable pointer. A provenance-preserving address API or an explicit externally allocated-storage contract is required for the reverse direction. Integers received from untrusted input cannot be treated as allocation ownership.

### 15.4 Safe-library boundary

Safe public library operations may rely on internally established unsafe invariants, but cannot export mutable access to private metadata that breaks those invariants. Returned slices and references prevent incompatible relocation/mutation for their lifetime. A raw-pointer owner must account for all initialized residents, including partially constructed values, canceled operations, and exceptional exits.

Unsafe-enabled execution can access actual process memory and is not an in-process sandbox. The source compiler, runtime checks, capability system, and unsafe implementation each have distinct obligations. Independent hostile-bytecode admission is a separate deployment guarantee, not a consequence of omitting unsafe syntax from an application's top-level file. [R09]

## 16. C foreign-function interface

### 16.1 Declarations and calling convention

C interoperability is normative for a target advertising the C-FFI capability. Foreign functions have fixed concrete, monomorphic signatures and explicit C ABI:

```glorious
unsafe extern "C" {
    fn external_hash(data: *const u8, length: c_size_t) -> u64;
}

#[export_name = "glorious_identity_u64"]
pub extern "C" fn exported_identity(value: u64) -> u64 { value }
```

The export example uses only a scalar and establishes no unchecked pointer obligation. Exported source functions using unchecked pointer access must themselves be unsafe or validate through an appropriately constrained host contract. External declaration imports are unsafe to call unless a reviewed trusted binding explicitly states a safe contract. There is no ordinary-function overload set for foreign symbols.

A foreign symbol is resolved from an explicitly configured library/import table. Capability admission is separate from linking. A matching name and machine signature do not establish safe semantics, ownership, or permission. No runtime foreign-library search is implicit in source execution.

### 16.2 C-representable types

C-facing types are the target's `c_*` scalar aliases, supported fixed scalars with an exact declared mapping, raw pointers, C function-pointer types, and records/tuple structs declared `#[repr(C)]` whose fields are themselves C-compatible. `#[repr(transparent)]` permits one nonzero-sized representation field plus permitted zero-sized markers, with explicit validity/ownership obligations unchanged.

Glorious Bool, Result, String, Vec, references, closures, effect values, labels, and resumptions are not automatically C ABI values. Export explicit representations or opaque pointers with checked owning/borrowing operations. C `_Bool` uses a distinct admitted `c_bool` representation and checked conversion; it is not the Result-based Bool layout.

Fieldless enums need an explicitly fixed integer representation before C exposure. C unions, bitfields, packed references, C variadics, and C++ ABI are not required in version 1; bindings use explicit opaque/byte representations or generated adapters until separately specified. `repr(C)` fixes layout according to the selected target C ABI, not a universal cross-platform layout.

### 16.3 Callbacks and lifetime

A C callback pointer is not a raw bytecode program counter. The runtime supplies an ABI-correct entry bridge where supported. A synchronous callback may borrow values only for the dynamic call extent. A retained callback requires an explicit registration owner that keeps its environment, code, and runtime alive and prevents use after unregistering.

Shared/unique access must survive callback re-entry without stale VM copies or overlapping unique aliases. Native code retaining a source reference past its contract is an unsafe violation. Allocation returned from C must be paired with its matching release function/domain, not arbitrarily freed by the Glorious allocator.

### 16.4 Unwinding and effects

C calls do not carry Glorious algebraic-effect rows. Glorious code invoked through C must handle its effects before returning to C, or use an explicitly specified runtime bridge protocol. A resumption cannot capture or replay an arbitrary foreign C stack. Labels cannot jump through foreign frames. Foreign exceptions, `longjmp`, and stack unwinding across this boundary are not admitted by the C ABI contract.

Translate recoverable failures into declared C status/payload representations or Glorious Result values at explicit adapters. A boundary violation is not silently translated into a successful return. `tail` across C is legal only where the exact target/cleanup/ABI contract proves it; otherwise it is rejected.

**Rationale.** Shared VM/native Glorious values and C interoperability solve different problems. Requiring explicit C representations preserves interoperability without falsely promising that Rust, C, and Glorious owners have identical layouts. [R09, X03–X04, D31]

## 17. Shared Glorious VM/native ABI

### 17.1 One target contract

For the same target and ABI generation, interpreted and LLVM-generated Glorious code MUST agree on every addressable type's size, alignment, field offsets, enum tag/payload layout, pointer width, endianness, scalar semantics, ownership/copy/drop contract, callable signature, and allocation domain. Private registers may have an internal representation, but sharing an object cannot require reconstructing it at the boundary.

The ABI is identified by an explicit descriptor containing at least generation, target triple, layout identity, callable/effect convention version, intrinsic/runtime manifest identity, and concrete type-instance identities. Equal size/alignment does not establish equal types. Linking incompatible descriptors fails before execution.

### 17.2 Concrete layout rules

For the default Glorious representation, fields retain declaration order. Each field starts at the next offset aligned to its target alignment; aggregate alignment is the maximum required alignment and aggregate size is rounded up accordingly. A zero-sized field has no bytes but retains its identity and lifetime/ownership role. Fixed arrays have a stride equal to the padded element size and N logical residents, including zero-sized residents.

The initial intended ABI uses explicit tagged enums: an unsigned tag sufficient for the declared variants, followed by suitably aligned storage for the active variant's payload. The ABI descriptor records tag width, payload offset, and all variant layouts. Niche optimizations that change an exported layout require the same declared ABI identity on both engines; they are not an unrecorded backend preference.

Scalar alignment is a target-profile fact. In particular, i128, vector extensions, and foreign types cannot inherit an arbitrary host compiler's defaults. `repr(C)` uses the selected C target layout instead of these default record rules. Reordering private fields across an externally shared concrete type also requires an ABI-compatible descriptor decision.

### 17.3 Ownership and references across engines

An owned argument transfers one logical owner. A borrowed argument retains its owner's identity and declared loan relation. Returned references follow the validated source contract. Copy/drop operations use the source-selected implementation identity for the exact concrete type, including transitively reachable resident hooks.

Native and VM access to one shared object observes the same backing allocation and current mutation. Addressable locals must have stable homes for the duration of live pointers/loans; VM frame growth cannot relocate a borrowed value without a semantics-preserving indirection already in its ABI. Boundary allocation, per-element boxing, or silent copy adapters do not satisfy the zero-marshalling contract.

### 17.4 Calls, effects, and mixed execution

A callable's ABI includes code identity, receiver mode, capture layout, parameter/result placement, and effects/control convention. A bytecode-only generic specialization can be invoked from native code through an entry bridge; it need not have been native-compiled first. A C-callable entry address is a bridge, not the bytecode code identity itself.

Glorious-to-Glorious mixed execution must preserve deep handlers, one-shot and admitted multi-shot resumptions, cleanup order, exact use obligations, and callback lifetimes. An implementation can use a shared runtime control convention or explicitly reject unsupported mixed-control paths before execution. It cannot silently turn a resumptive call into an ordinary nonresumable native call.

Tail calls must satisfy the same bounded-live-control guarantee on both engines. A language-level `tail` may lower to verified native mandatory tail transfer, a direct CFG backedge, or another proven constant-space transfer. It must not depend on optional LLVM optimization.

### 17.5 Artifacts and contract admission

Portable artifact encoding is not native object layout. It stores relocatable identities, bounds, canonical scalar encodings, and target requirements, not arbitrary serialized native addresses. A loader checks the target and ABI before materializing addressable objects or resolving imports.

Artifact formats may change incompatibly during pre-alpha. No implementation is required to retain an old decoder, old numeric assignments, or old scalar semantics. Changes must identify the new contract so an incompatible artifact cannot accidentally pass admission. Unsupported required features, malformed encodings, mismatched layouts, untrusted imports, or failed ownership/control checks fail closed.

G1 wire tables, compiler query schemas, and authoring format numbers describe implementation contracts, not permanent language syntax. Keep the actively supported producer/consumer contract documented and tested; regenerate dependent artifacts when it changes. Maintaining historical artifact or seed execution is not a requirement.

### 17.6 Conformance evidence

Shared-ABI conformance requires actual cross-engine calls demonstrating identical backing addresses, visible mutation in both directions, borrowed/owned returns, callbacks, correct destructor identity, zero-sized residents, and rejection of incompatible layouts/domains. A pointer-only substrate test or two separate runs with equal values is insufficient. A full unsafe-enabled process is not thereby a sandbox.

## 18. Failure, determinism, and resource limits

Safe source errors are diagnosed before execution. Recoverable application failures are ordinary values or declared effects. Explicit abort, primitive faults, broken host contracts, resource-enforcement termination, and runtime-internal faults are distinguishable terminal categories. Ordinary errors such as a missing file should be represented by the hosted library's Result contract, not reclassified as internal faults.

For fixed input and a fixed target contract, pure scalar operations, source evaluation order, handler selection, ownership transfer, cleanup order, and library operations whose contracts promise determinism must be deterministic. Host effects expose declared external nondeterminism; hashing/table iteration cannot silently determine diagnostic or artifact order where reproducibility is promised.

Floating arithmetic uses round-to-nearest, ties-to-even and canonical NaN rules from the selected profile, preserves signed zero, and does not enable implicit fast-math transformations. Host locale or native formatting cannot alter canonical language literals or explicitly deterministic library formatting.

An implementation can impose advertised limits on compilation proof search, source size, concrete layouts, recursion in static normalization, runtime memory, and execution supervision. Exceeding a limit is an explicit outcome. Limits cannot justify accepting ill-typed code, guessing evidence, treating malformed input as a host panic, or weakening `tail` to an ordinary call.

## 19. Core boundary and compilation invariants

The compiler may choose its internal representations, but the checked semantic core must reduce library operations to structural data construction/projection, calls and proper tail calls, labels/direct leaves, effects/handlers/resumptions, borrowing/movement/destruction, and admitted machine/host leaves.

Source `is`, pattern callable syntax, imported operator spellings, and standard control names are elaborated through those mechanisms. There is no semantic core node that grants `if`, `match`, or `loop` privileged behavior by name. A low-level CFG branch/switch is of course allowed as the implementation of a checked structural pattern decision; the prohibition is against source-name-specific semantics, not against machine branches.

Before emission, every runtime specialization has closed types/effects, normalized associated evidence, proved lifetime/use constraints, a valid control contract, well-defined cleanup, admitted safety contracts, and an exact target layout. Labels/environment brands and other proof-only values erase; resident binding payloads and capture data do not.

Correctness-required control fusion must happen even without optimization. Optional optimizations preserve observable effects, nonlocal transfer, traps, evaluation order, and cleanup. They cannot reorder a destructor or foreign call merely because the outward algebraic-effect row is empty.

## 20. Compact grammar and declaration inventory

This grammar summarizes syntax; the semantic sections govern context-sensitive ambiguities. `*` means repetition here, not the ownership upper bound.

```text
Item          := Function | Struct | Enum | Trait | Impl | Effect | Alias
               | Const | Global | Module | Import | Fixity | ExternBlock
Function      := Visibility? Safety? ABI? "fn" Name Generics?
                 "(" Parameters? ")" Result? Row? Where? (Block | ";")
Result        := "->" Type
Row           := "/" EffectPath | "/" "{" EffectList? ("|" RowTerms)? "}"
Struct        := Visibility? "struct" Name Generics?
                 ("{" Fields? "}" | "(" TupleFields? ")" ";" | ";")
Enum          := Visibility? "enum" Name Generics? "{" Variants? "}"
Effect        := Visibility? "effect" Name Generics? Where? "{" Operations* "}"
Operation     := Quantity? Name OpGenerics? "(" PayloadTypes? ")" Result? Where? Separator
Fixity        := ("infixl" | "infixr" | "infix" | "prefix") Integer Operator
                 ("=" Path)? ";"
Alias         := Visibility? "type" Name Generics? "=" Type ";"
Const         := Visibility? "const" Name Generics? ":" Type "=" ConstExpr ";"
Global        := Visibility? "let" Name ":" Type "=" Expr ";"
Statement     := "let" "mut"? Pattern (":" Type)? "=" Expr ";"
               | Place "=" Expr ";" | Expr ";" | Item
Expression    := Atom | Application | OperatorChain | Block | Callable
               | "handle" Expr ArmBlock | LabelBlock | "tail" Application
               | "unsafe" Block | "move" Place | Borrow | Expr "is" Pattern
Callable      := "fn" "(" Parameters? ")" Result? Row? Block
               | "{" "=>" Expr "}" | PatternArmBlock
LabelBlock    := "@" Name (":" Type)? Block
Application   := Expr "(" Arguments? ")" TrailingBlock?
               | CallableName TrailingBlock
Pattern       := "_" | Binder | "let" Name | ConstantPath | ScalarLiteral
               | TuplePattern | ArrayPattern | ConstructorPattern | RecordPattern
               | ReferencePattern
PatternArm    := Pattern "=>" Expr
HandlerArm    := Pattern "=>" Expr | OperationPath "(" Patterns? ")" "=>" Expr
Quantity      := "[" NonnegativeInteger "," (NonnegativeInteger | "*") "]"
```

An explicit operation quantity is legal only under §10.6, and an explicit ordinary principal quantity only under §7.1. Attribute syntax is reserved for specified forms: `repr`, `export_name`, `non_exhaustive`, `no_std`, `no_implicit_prelude`, and compiler/distribution metadata with a validated identity. Arbitrary procedural macros or attribute expansion are not part of this grammar.

Top-level runtime `let` values must be duplicable and safely memoizable without external effects or restricted-use ownership. Recursive global initialization is diagnosed; source modules do not form ordered initialization programs. Generic structural const schemes are distinct from runtime globals.

## 21. Required language conformance cases

The following are acceptance obligations, not claims about tests already executed. Each family requires positive and negative examples with source-oriented diagnostics.

| ID | Required behavior |
|---|---|
| L01 | Rename every standard control/operator binding; accepted semantics remain unchanged. |
| L02 | Reject duplicate free/inherent functions even with different arity or types. |
| L03 | Distinguish mutable bindings from immutable bindings, and binding mutability from a unique referent. |
| L04 | Distinguish `(T,)`, `T`, `(T,U)`, and `((T,U),)` in callable argument contracts. |
| L05 | Infer a contextual block as a callable only after signature selection; reject ambiguous interpretations. |
| L06 | Do not execute a closure body merely by constructing or passing it. |
| L07 | Check constructor aliases and Bool constants structurally in patterns without calling Eq. |
| L08 | Reject unqualified import ambiguity rather than overload by type. |
| L09 | Imported effect operations perform directly and retain the original effect identity. |
| L10 | Tuple structs preserve nominal identity and field visibility. |
| L11 | Every pattern callable is exhaustive; `_` still rejects an owned nondiscardable resident. |
| L12 | One pattern callable can consume a shared exact-linear capture once in every clause. |
| L13 | Clause binders do not escape to sibling clauses; bottom clauses add no normal result. |
| L14 | Bool/Option/Result aliases cannot receive overlapping trait implementations. |
| L15 | Two inline conditional alternatives can each consume one ticket; two separate owning closures cannot. |
| L16 | Sequential callbacks cannot reuse an already consumed environment. |
| L17 | A callback that ran and returned Err keeps its post-state rather than restoring its input state. |
| L18 | Plain Result storage cannot conceal an unresolved Available witness at an escape boundary. |
| L19 | Affine conditional movement retains safe conditional cleanup without a use of an uninitialized place. |
| L20 | Exact-linear resources cannot be lost through wildcard, return, cancel, or a helper call. |
| L21 | Zero-sized exact-linear values and zero-sized resident destruction receive full accounting. |
| L22 | Drop runs once in the specified order and cannot discharge a positive-lower obligation. |
| L23 | Reject field moves from custom-Drop owners in safe code. |
| L24 | A unique-reference hole must not cross a cleanup-bearing break or continuation capture. |
| L25 | NLL ends loans at the last valid use, including stored and returned reference carriers. |
| L26 | Higher-ranked placeholders cannot leak into outer inference variables. |
| L27 | Label/environment brands are invariant despite structurally equal footprints. |
| L28 | `is` evaluates once, preserves protecting loans, and scopes positive/negative binders correctly. |
| L29 | Different callback rows union; duplicate instances normalize; an ambiguous union split rejects. |
| L30 | Contextual effect defaults select the inner explicit instance, not an outer type-compatible break. |
| L31 | Exact handler instance routing and partial forwarding survive nested identical payload types. |
| L32 | Tail-resume abbreviation rejects exact-two resumption obligations. |
| L33 | Optional cancellation cannot abandon a linear capture; exact-once suspension preserves its obligation. |
| L34 | Multi-shot replay rejects unique loans/labels and preserves residual initialized fields. |
| L35 | Terminal effects run lawful abandoned-continuation cleanup before the clause. |
| L36 | Label helpers resolve to direct destinations and reject unfusable foreign/opaque boundaries. |
| L37 | Explicit tail sites reject post-call work, dead-local references, and retained dynamic delimiters. |
| L38 | Long tail cycles run with bounded live call/control storage at O0 and native optimization levels. |
| L39 | Unsafe permission is not an effect and does not leak into deferred closure bodies. |
| L40 | Raw moves, copies, allocation arithmetic, provenance, and partial initialization obey their contracts. |
| L41 | No bytes/addresses/FFI values forge intrinsic brands, callable identity, or host authority. |
| L42 | C ABI rejects non-C layouts, foreign unwinding, and unregistered retained callbacks. |
| L43 | VM/native calls share backing storage and source-selected cleanup identity with no reconstruction. |
| L44 | Compiler/VM/native operations agree on target-sized usize; incompatible artifacts are rejected or rebuilt without requiring old-format support. |
| L45 | A no-std build still checks its required intrinsic/runtime dependencies. |
| L46 | Solver/resource-limit exhaustion fails explicitly rather than manufacturing evidence. |
| L47 | Runtime faults, handled source failure, abort, and cancellation remain distinguishable. |
| L48 | Both backends preserve NaN, signed-zero, overflow, and deterministic formatting contracts. |

## 22. Decision register and reconciliation

**U** means explicitly selected in the design conversation. **C** means a consolidation choice made to close an unresolved contract. **P** means a preserved reviewed requirement. C entries are proposals for adoption, not falsely attributed user decisions.

| ID | Origin | Decision and reason |
|---|---|---|
| D01 | U | Exactly two semantic specs: intended language and standard-library interfaces; do not conflate implementation progress with either. |
| D02 | U | Language Glorious, compiler Grandiose. |
| D03 | U | No lazy modifier/type; ordinary callable invocation supplies deferred execution. |
| D04 | U | Full Fn/RunsIn/environment constraints in canonical contracts; no runtime Environment object. |
| D05 | U | Available is a core intrinsic; source cannot forge it. |
| D06 | U | Compositional Result operators; no required public choose. |
| D07 | U | No free/inherent function overloading; distinct break_at and continue_at names. |
| D08 | U | Explicit tail is checked and failure is a compile error. |
| D09 | U | Effect operations are imported directly; no mechanical forwarding-function layer. |
| D10 | U/C | Rust-like module imports/preludes; retain explicit associated-function calls rather than silently introduce dot methods. |
| D11 | U | Privacy belongs to modules, not source bundle entries. |
| D12 | C | Optional std/prelude is normative; actual dependencies remain mandatory. |
| D13 | U | Add tuple structs and tuple-pattern callables; effect payloads use positional tuple-style syntax. |
| D14 | U/C | Canonical functions use fn; unit arrows may be omitted; both let and let mut exist; assignment is =. |
| D15 | C | Fields private by default, exposed with pub, to make module-owned representation protection consistent. |
| D16 | U/C | Bool/constructor aliases work in patterns through structural constants; true/false are closed Bool constants, None is a generic structural constant scheme. |
| D17 | C/U | Target-size usize/isize in the intended ABI; compiler and VM contracts change together with no legacy G1 preservation requirement. |
| D18 | U | Multi-clause pattern callables are exhaustive ordinary callables; `_` is available but obeys ownership. |
| D19 | U | Only duplicable, affine, and exact-linear ordinary principal use classes. |
| D20 | C | Public Drop/discard bounds use affine; actual zero-use checking is an internal predicate, not a fourth class. |
| D21 | C | Conditional affine initialization is tracked without forced early destruction; linear obligations remain path-exact. |
| D22 | P | Cleanup is zero use; terminal control is not an escape from cleanup obligations. |
| D23 | C | Guarded higher-order control contracts are explicit abstract-interface metadata. A single After bound does not pretend to encode all branch states. |
| D24 | C | Ordinary control dispatch traits and a context-bearing carrier unify Result and intrinsic-binding Test consumers without function overloads; BindingContext remains sealed. |
| D25 | U/C | Effects union rather than forcing equal rows; braces are sets, parentheses products; multiple row tails denote union. |
| D26 | C | Generic effect defaults come from a unique explicit contextual family instance, never a guessed outward instance by payload compatibility. |
| D27 | C | Optional one-shot and exact finite resumptions are admitted; arbitrary resumption intervals are deferred. |
| D28 | P/C | Deep resumptions reinstall the delimiter; operation clauses execute outside their serviced delimiter. |
| D29 | U/P | Pattern callables do not require first-class effect-handler values; handler blocks remain attached to handle. |
| D30 | C | Tail closes only legally discharged scopes; no promise that the experimental recursive-handler sketch itself passes. |
| D31 | U/C | Unsafe pointers and C FFI are normative; C boundary forbids unadapted Glorious effects/unwinding. |
| D32 | U | yield/await interfaces belong in std independently of an executor implementation. |
| D33 | U | return remains an ordinary label-invoking readability helper. |
| D34 | U | Arithmetic dispatch uses independent Rust-like operator traits, not one giant Arithmetic trait. |
| D35 | U/P | VM/native Glorious ABI agreement and source-owned libraries are requirements, not copied Rust layout assumptions. |
| D36 | C | Ordinary external failures use typed hosted results; implement the host boundary directly rather than pretending a wrapper can catch a fatal HostFault. |
| D37 | C | No unbraced implicit thunk conversion is added for else-if/while; use ordinary explicit callable blocks. |
| D38 | C | Explicit fixity-to-function binding distinguishes unary and binary punctuation without arity overloading. |
| D39 | C | Generative loop callbacks include their proof-only L in Args, so distinct label-dependent effect rows do not conflict on the same Fn<()> head. |
| D40 | U | No backward-compatibility obligation during pre-alpha for source, library APIs, ABI, host bindings, compiler formats, or G1; current components and tests evolve together. |

### 22.1 Corrections to the experimental conversation

The prior sample loop kernels were explanatory sketches, not proof-correct implementations. In particular: recursive handler arms can retain dynamic state; &mut Fn evidence does not authorize arbitrary capture moves; an open unique-reference hole is not automatically safe on break; unbranded LoopControl<B> can misroute between nested loops of the same result type; and exact callback effect equalities are not a union operation. The companion's corrected contracts make these proof obligations explicit and use generative loop identity.

Likewise, the previous flat if/else signatures did not fully encode result-correlated availability. This revision does not hide that gap behind “inference”: the guarded control interface and its nonescape rule are normative. First-class pattern callables, not a fake first-class handler trait, supply library match.

### 22.2 Supersession by topic

The reviewed branded-core, frontend, ownership/capture, effect-surface, and label-unification documents are consolidated into §§2–15. Library definitions and policies from the older/newer std documents are consolidated in the companion. Unsafe/native and LLVM descriptions contribute §§15–18, with target semantics and boundary requirements separated from implementation status. The control-kernel document contributes higher-order contracts and conformance obligations, not its obsolete source paths or performance claims.

Batch-versus-incremental compiler architecture, authoring constraints, query registries, storage budgets, test totals, and release milestones remain implementation records. These two specs do not claim to rewrite or replace the GSC-2 compiler's internal database/API specification. This is an intentional scope boundary, not deletion of those engineering requirements.

## 23. Source register and reading coverage

The baseline was rechecked through the connected repository at the commit recorded above. The main language, library, control, conversion, ownership, effect, label, frontend, architecture, bytecode, unsafe/native, and tutorial materials had been read during this design conversation; the native/ABI and LLVM material was checked again for this consolidation. Compiler project/status and GSC-2 materials were consulted selectively for boundaries. This is **not** a claim of a fresh end-to-end reading of every historical Markdown performance report, compiler plan, or progress ledger. No compiler or executable conformance suite was run for these drafts.

The earlier `glorious-standard-library-proposal.md` was used as an idea inventory, not as an authoritative specification. Its lazy notation, choose/return choices, staging labels, and abbreviated callback constraints are superseded here and in the companion.

| Ref | Source | Contribution |
|---|---|---|
| R01 | [Branded-environment core](https://github.com/MalekiRe/glorious/blob/7e4a021811b6a8e0d62b2899f10e602d037c3c14/glorious-branded-environment-core-spec.md) | Intrinsic relations, ownership, brands, labels, effects, refinements. |
| R02 | [New std scope](https://github.com/MalekiRe/glorious/blob/7e4a021811b6a8e0d62b2899f10e602d037c3c14/docs/new-stdlib.md) | Three public classes, String/Str, smaller foundational library. |
| R03 | [Earlier std contract](https://github.com/MalekiRe/glorious/blob/7e4a021811b6a8e0d62b2899f10e602d037c3c14/docs/std-lib.md) | Control algebra, numeric and collection contracts, host compatibility. |
| R04 | [Frontend design](https://github.com/MalekiRe/glorious/blob/7e4a021811b6a8e0d62b2899f10e602d037c3c14/docs/frontend-design.md) | Inference, coherence, modules, lifetimes, static proof boundaries. |
| R05 | [Default moves and captures](https://github.com/MalekiRe/glorious/blob/7e4a021811b6a8e0d62b2899f10e602d037c3c14/docs/default-moves-and-closure-captures.md) | Ordinary moves/copies, explicit borrowing, contextual alternatives. |
| R06 | [Effect surface redesign](https://github.com/MalekiRe/glorious/blob/7e4a021811b6a8e0d62b2899f10e602d037c3c14/docs/effect-syntax-redesign.md) | Direct operation invocation, unified handler arms, migration removals. |
| R07 | [Control kernel](https://github.com/MalekiRe/glorious/blob/7e4a021811b6a8e0d62b2899f10e602d037c3c14/docs/control-kernel.md) | Structural control summaries, traversal, loops, transactions. |
| R08 | [Label unification](https://github.com/MalekiRe/glorious/blob/7e4a021811b6a8e0d62b2899f10e602d037c3c14/docs/optional-label-unification.md) | Generative Label, directness and control fusion. |
| R09 | [Unsafe memory and native ABI](https://github.com/MalekiRe/glorious/blob/7e4a021811b6a8e0d62b2899f10e602d037c3c14/docs/unsafe-memory-and-native-abi.md) | Source-owned libraries, genuine shared storage, trust boundaries. |
| R10 | [Conversions](https://github.com/MalekiRe/glorious/blob/7e4a021811b6a8e0d62b2899f10e602d037c3c14/docs/conversions.md) | Explicit As policy and coherence. |
| R11 | [Architecture](https://github.com/MalekiRe/glorious/blob/7e4a021811b6a8e0d62b2899f10e602d037c3c14/docs/architecture.md) and [bytecode](https://github.com/MalekiRe/glorious/blob/7e4a021811b6a8e0d62b2899f10e602d037c3c14/docs/bytecode.md) | Runtime invariants and implementation-format context; prior backward-compatibility promises are superseded by D40. |
| R12 | [LLVM backend](https://github.com/MalekiRe/glorious/blob/7e4a021811b6a8e0d62b2899f10e602d037c3c14/docs/llvm-backend.md) | Cross-backend implementation descriptions; not proof of intended conformance. |
| R13 | [GSC-2](https://github.com/MalekiRe/glorious/blob/7e4a021811b6a8e0d62b2899f10e602d037c3c14/GSC-2-glorious-incremental-self-hosted-compiler-spec.md) and [compiler README](https://github.com/MalekiRe/glorious/blob/7e4a021811b6a8e0d62b2899f10e602d037c3c14/compiler/README.md) | Compiler scope and implementation-status separation; selective consultation. |
| R14 | [Call-context lifetimes](https://github.com/MalekiRe/glorious/blob/7e4a021811b6a8e0d62b2899f10e602d037c3c14/compiler/spec/call-context-lifetimes.md) | Reference-origin and higher-ranked boundary caveats. |
| R15 | [Tutorial source chapters](https://github.com/MalekiRe/glorious/tree/7e4a021811b6a8e0d62b2899f10e602d037c3c14/tutorial/src) | Examples and historical syntax/host limitations. |
| X01 | [Justin Pombrio, Imagining a Language without Booleans](https://justinpombrio.net/2025/09/22/imagining-a-language-without-booleans.html), 22 September 2025 | Historical inspiration: Result unifies truth, optionality, and compositional control. Glorious adds its own ownership/effect contracts and does not adopt the hypothetical `T ? E` spelling. |
| X02 | [LLVM Language Reference: call](https://llvm.org/docs/LangRef.html#call-instruction) | Primary reference for the distinction between optional and mandatory backend tail support; not the definition of Glorious tail semantics. |
| X03 | [Rust Reference: type layout](https://doc.rust-lang.org/reference/type-layout.html) | Comparative primary reference for explicit target C representation versus default language layout. |
| X04 | [Rust Reference: external blocks](https://doc.rust-lang.org/reference/items/external-blocks.html) | Comparative primary reference for typed external declarations; Glorious's own FFI rules are specified above. |

**End of language specification.**
