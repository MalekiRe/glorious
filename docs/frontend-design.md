# Grandiose Frontend Design

Status: implementation design for Draft 0.1. The language specification in
[the language core](../glorious-branded-environment-core-spec.md) is authoritative. The component
and bytecode contracts in [architecture.md](architecture.md) and
[bytecode.md](bytecode.md) are normative boundaries. If this document conflicts
with either, the language specification wins first and the normative bytecode
contract wins for artifact encoding.

This is a greenfield design. It does not depend on the shape or behavior of any
previous compiler. It uses a snowflake structure: each level expands the level
before it from a compact model into decisions that can be implemented and tested.

## 1. Level 0: the compiler in one paragraph

The frontend is one deterministic, whole-program transaction. It tokenizes
structural syntax, parses declarations and flat operator streams without knowing
library control names, collects all interfaces and fixities, resolves names and
operator grouping, and elaborates syntax directly into evidence-bearing Typed
Core. Elaboration is bidirectional and constraint driven: it selects ordinary
call and trait candidates before deciding whether contextual blocks are eager or
anonymous callables; it keeps linked environment brands open until all bodies in
an expression have contributed ownership requirements; and it checks one state
containing ordinary places, environments, labels, and effects. Canonical tabled
trait solving, interval-based `Use` analysis, Rust-style region/loan analysis,
and a shared pattern decision compiler validate the result. Only after all
proofs succeed are environments sealed, static evidence erased, and canonical
Typed Core handed to MIR lowering. Errors are accumulated only at safe phase
boundaries and always name source constructs, never compiler-generated IDs.

## 2. Level 1: the seven major stages

The frontend has seven ordered stages. A stage may inspect products of earlier
stages but may mutate only its own arenas and explicitly designated inference
cells.

1. **Source ingestion.** Assemble the canonical standard-library/source bundle
   in command-line order, insert the required boundary newlines, decode UTF-8,
   lex the single stream, and retain a segment map for diagnostics and
   private-field authority plus body token ranges. Body ASTs are parsed on demand
   after fixities and interfaces are known.
2. **Interface collection.** Allocate declaration identities in source order;
   collect nominal heads, callable signatures, effect operations, trait and impl
   heads, fixities, generic binders, and intrinsic identities; reject global
   shape and coherence errors that do not require body checking.
3. **Resolution.** Resolve type, value, trait, effect, label, lifetime, and
   operator namespaces; group flat operator chains from source fixities; produce
   explicit candidate sets for overloaded calls and operators.
4. **Body elaboration.** Parse and check one demanded body bidirectionally; create
   fresh callable, label, binder-key, refinement, resumption, and provisional
   environment identities; generate type, trait, effect, lifetime, place, and
   quantity constraints; construct provisional Typed Core in left-to-right
   evaluation order.
5. **Static closure.** Solve traits and associated projections, infer variance
   and regions, run shared `PlaceFlow` NLL/loan checks, derive actual and principal
   use intervals, validate `Drop`, close effect rows, compile patterns, join
   ownership states, and seal every provisional environment.
6. **Body finalization.** Insert explicit destruction plans, resolve all evidence
   references, prove no inference variable or open brand escapes, erase
   static-only values, and validate the prohibited-node invariant.
7. **Boundary emission.** Lower the finalized body immediately to MIR, retain
   compact generic Core only while monomorphizations still need it, then reset
   body-local AST/inference/Core scratch arenas. Bytecode table indices are
   assigned later; frontend IDs never enter `.grbc`.

There is no HIR and no persistent incremental query database. Temporary CFGs,
constraint graphs, decision DAGs, and solver tables are analysis products, not
additional semantic program representations. The compiler never holds parsed
bodies for the entire program at once.

## 3. Level 2: ownership of responsibilities and data flow

### 3.1 Frontend session

One `FrontendSession` owns all arenas and interners for one invocation:

```text
FrontendSession
  source_map
  symbols, paths
  declaration_headers, body_token_ranges
  declarations, scopes, fixities
  types, consts, rows, regions
  trait_db, solver_tables
  callables, brands, place_flow
  reusable_body_scratch, generic_core
  diagnostics
  deterministic_work_queue
```

The public operation is logically:

```text
compile_frontend(source_bundle, intrinsic_manifest, limits)
    -> Ok(FrontendProduct)
     | Err(DiagnosticBundle)
```

`FrontendProduct` contains frozen declaration interfaces, lowered MIR bodies,
reachable generic Core awaiting monomorphization, and compact source provenance.
It contains no mutable inference variables. A semantic fingerprint is computed
only in reproducibility/debug mode, never on the normal self-host path.

### 3.2 Phase barriers

Each phase returns a `PhaseStatus` with either `Clean`, `Recovered`, or `Fatal`.
`Recovered` means poison/error nodes were introduced and subsequent work may
continue solely to find independent diagnostics. No bytecode or public interface
is emitted unless every stage is `Clean`.

The barriers are:

- declaration scanning must finish before interface collection; each body is
  parsed only after interface and fixity collection;
- all fixities and declaration heads must be collected before grouping any body;
- global coherence must pass before body trait selection is trusted;
- a call island must select one signature interpretation before any contextual
  body inside it is checked;
- all bodies linked to an environment must be checked before that environment is
  sealed;
- all type/row projections must normalize before NLL, `Use`, `Drop`, handler
  coverage, and final layout checks;
- all analysis must pass before evidence erasure.

### 3.3 One checking state

Expression checking implements:

```text
Gamma ; Delta ; Omega ; Lambda ; Pi
  |- expr : Type / EffectRow
  => Delta' ; Omega'
```

The implementation packages those components as:

```text
CheckContext  = Gamma + expected type/effects + lexical scopes
FlowState     = Delta + Omega + active Lambda + active Pi
CheckResult   = type + effects + normal FlowState? + CoreValue/CoreComputation
```

`normal FlowState?` is absent for `Never` computations. Branch checking takes an
undo-log checkpoint, records the first branch's sparse exit delta, rolls back,
checks the next branch, and joins the deltas. It never clones the full
place/loan/environment state or runtime values. A normal join requires compatible
ordinary places and unifiable environment post-states. The compiler does not
insert drops to make unequal branches agree.

### 3.4 Transactional inference

Candidate selection uses snapshots over inference assignments and emitted goals.
For an ordinary generic call, independently synthesizable arguments contribute
constraints before context-dependent arguments are checked. Concrete local and
structural types are considered before defaultable literals, so an earlier
empty/phantom constructor or integer literal can receive a type fixed by a later
argument. The source order is retained for evaluation and diagnostics; only the
constraint-seeding prepass is order-independent. Unfixed phantom parameters and
conflicting rigid arguments remain structured ambiguity errors.
A snapshot supports `mark`, `rollback`, and `commit`. It does not clone arenas;
it records a compact undo log for type/region/row/const variable bindings and
constraint-vector lengths. Each candidate is tested in declaration order, but
selection is semantic:

- zero viable candidates is an error with one summarized reason per candidate;
- one viable candidate commits;
- multiple equivalent candidates collapse only when they resolve to the same
  declaration and normalized substitutions;
- otherwise the expression is ambiguous, even if one candidate happened to be
  tried first.

Receiver preference (`&F`, `&mut F`, `F`) and environment-access preference
(`&E`, `&mut E`, `E`) are ordered tie-breakers only after expected source forms
and type viability are applied.

## 4. Level 3: core arenas, identities, and APIs

### 4.1 ID discipline

Every ID is a `u32` newtype in the conceptual model. The implementation may use
one generic integer representation to stay compact, but APIs must not accept an
ID from the wrong arena.

```text
SourceSegmentId, SymbolId, AstId, ScopeId, DeclId, GenericId
TypeId, TypeVarId, ConstId, ConstVarId, RegionId, RegionVarId
RowId, RowVarId, TraitId, ImplId, GoalId, EvidenceId
LocalId, PlaceId, LoanId, MovePathId
CallableId, BrandId, ControlSiteId
CoreValueId, CoreComputationId
```

IDs are append-only and optimized for direct array indexing. Their numeric values
are deliberately not deterministic output: failed speculation rolls back scratch
arenas, but committed allocation order may otherwise follow the checker worklist.
Diagnostics and serialization sort by source/semantic keys and construct their
own dense output indices. This avoids owner-local insertion, provisional-ID
remapping, and canonical allocation on the hot path. Source segments remain in
the canonical concatenation order; host path spelling never reorders them.

### 4.2 Spans and origins

A span is the inline 8-byte pair `(start_byte, end_byte)` of `u32` offsets into
the validated, concatenated source bundle. Inputs whose combined byte length
does not fit `u32` receive a resource diagnostic. The `SourceMap` maps ranges
back to their `SourceSegmentId`, original path spelling, and line starts. Segment
identity is used for the private-field authority check in section 4.3 and is
otherwise diagnostic metadata; it is not part of ordinary name lookup or
artifact identity. Tokens retain no trivia; the lexer skips it and diagnostics
recover source slices from the bundle bytes. Every generated item has an `Origin` only when
its source cannot be inherited from its owner:

```text
Source(span)
Generated { owner, reason, ordinal }
Desugared { surface_span, rule }
```

Diagnostics follow origins back to the nearest source span. Internal IDs may be
shown only in an opt-in compiler-debug dump.

### 4.3 Symbols, paths, and namespaces

All identifier text is interned as UTF-8 bytes after exact decoding; no Unicode
normalization or case folding occurs. Distinct namespaces exist for:

- values and constructors;
- nominal types and type aliases;
- traits;
- effects and operations;
- lifetimes;
- labels;
- generic type, const, and lifetime parameters;
- fixity declarations.

Nominal types and type aliases own a value subnamespace containing constructors
and directly declared inherent functions and associated bindings such as `String::len` and
`Option::Some`. A top-level qualified value declaration may add a binding only
to an already declared type or type alias. Named modules add a separate lexical
namespace. Every definition is resolved to a structured `(ModuleId, namespace,
local definition id)` identity; textual qualification and imports never become
the authoritative identity.

An inherent `impl<T> Vec<T> { pub fn push(value: &mut Self, item: T) { ... } }`
declares `Vec::push` directly. It creates neither an unqualified `vec_push`
definition nor a forwarding alias. The head must name a type or type alias
declared in the same package. Multiple blocks are allowed, including blocks in
other modules of that package, but a member name may be defined only once per
owning type; disjoint-head overloading is not provided. Type, const, and effect
impl parameters must occur in the self type; function-only parameters belong on
the function. Method parameters cannot shadow block parameters.

`Self` denotes the fully applied impl head in signatures, body annotations,
constructors, patterns, and associated paths. Block bounds apply to every
member. `Vec<T>::method<U>` supplies owner and method arguments separately;
omitted arguments use ordinary inference. Specialized heads are checked even
for receiver-less functions. Functions have ordinary per-member visibility,
safety, effects, and first-class callable behavior. Importing or renaming a type
preserves its members, and exported type interfaces include public member
contracts. Inherent blocks currently contain functions only and do not add
implicit receivers or dot-call syntax. Trait implementations remain separate.

`mod name;` declares an external child. If the declaring module's logical
directory is `D`, its source is exactly `D/name/name.glorious`. `mod name { ... }`
declares an inline child and advances the same logical directory for external
modules nested inside it. The compiler-designated crate root is exempt from the
self-named-folder rule, so `src/main.glorious` or any manifest-selected file may
be the root. Additional package roots are supplied explicitly by the driver,
never inferred from positional files. A dependency manifest name is normalized
from `-` to `_` and becomes a public package-module binding in the application
root; invalid or colliding aliases are errors. Each package root is parentless,
so `crate` names the current package rather than always naming the application.
Unmarked additional files remain ordinary module fragments and are still
subject to orphan checks. `crate`, `self`, and `super` are contextual path roots. `use`
supports explicit names, `as`, groups, globs, and `self` imports. Imports are
resolved to a deterministic fixed point; benign re-export cycles are accepted,
while unresolved and ambiguous cycles are diagnosed.

Items in a named module are private by default and `pub` exports them to the
parent/module path. Explicitly supplied source fragments without a module edge
remain crate-root fragments for module-free programs. Once a crate uses
module syntax, supplied files that are orphaned, duplicated, or mapped to the
wrong hybrid path are errors. Fixity declarations are module scoped and operator
resolution observes explicit and glob imports just like other value bindings.

Struct fields are public by default; `private field: T` records the declaring
module as its authority. Deconstruction, construction by named fields, and field
projection may name that field only inside that module's privacy domain. Code
outside the domain therefore cannot consume a must-move value by destructuring
private fields or by calling an intrinsic destructor: it must transfer the whole
value to a callable whose definition has field access and which eventually
destructures it. The source map and module-resolution table supply stable
authority identities before elaboration, and generated code receives an
unforgeable resolved authority token.

A `ResolvedName` is a declaration identity plus namespace and generic depth, not
a string. Compiler intrinsics are recognized by identities supplied in a trusted
intrinsic manifest, never by source spelling alone.

The same manifest binds the standard library's finite primitive and host-import
leaf declarations to exact bytecode primitive IDs or
`(capability,symbol,signature)` triples. Collection and checking validate their
declared signatures before any body is elaborated. No other source declaration
can create a primitive or host import by copying its name.

### 4.4 Types and static terms

Types are hash-consed after shallow resolution:

```text
Type = Error | Infer(v) | Param(generic)
     | Unit | Never | Scalar(kind)
     | Tuple(types) | Array(type)
     | Nominal(decl, substitutions)
     | SharedRef(region, type) | UniqueRef(region, type)
     | Callable(callable_id, callable_kind)
     | BindingPack(region, brand_id)
     | Available(region, brand_id)
     | Projection(trait_ref, assoc_name, assoc_args)
     | BoundVar(debruijn, index) | Placeholder(universe, index)
```

Substitutions preserve declaration binder order and contain typed `GenericArg`
values: type, lifetime, or structural const. The interner key excludes spans and
mutable inference state. Terms containing an inference variable live in the
reusable body term arena and are never hash-consed. Zonking builds the resolved
interned term once. This avoids stale hash entries and repeated re-interning after
every unification.

Structural const values are:

```text
Const = U32(n) | AmountFinite(n) | AmountInfinite
      | Quantity { lower, upper }
      | Tuple(consts) | Enum(discriminant, fields)
      | Param(generic) | Infer(v) | Error
```

Only values admitted by declared const parameter types are accepted. Const
evaluation is a terminating structural normalizer, not arbitrary program
execution.

Effect rows are canonical sorted sets of normalized protocol terms plus at most
one tail (`Empty`, generic row parameter, or inference variable). Duplicate keys
are removed after equality proof. A row with an unresolved key cannot cross the
finalization boundary.

### 4.5 Places and move paths

A place is a root local followed by projections:

```text
Place = Local(local) . Field(index)* . Deref? . Index(const_index)?
```

Dynamic array indices are conservatively the same array place for alias checks.
Move paths exist for roots and statically known aggregate fields. Moving a parent
moves all descendants; moving a child marks ancestors partially initialized.
Types with custom `Drop` never permit a child move. Enum payload paths become
available only under a dominating variant fact.

### 4.6 Callable, brand, and place-flow records

```text
CallableDef {
  id, kind: Function | Closure | HandlerClause | Resumption,
  owner, source_body, generics,
  capture_candidates, fn_relations, runs_in_relations,
  receiver_capabilities, core_body, origin
}

BrandDef {
  id, kind: Label | Execution | Refinement | Continuation | BinderKey,
  scope_region, state: Open | Sealed,
  evidence_range, runtime_realization: None | LabelTarget | ProtocolKey,
  origin
}

EnvironmentSummary {
  brand, owner_expression, place_fact_ranges,
  residual_obligations, linked_callables, requested_uses,
  principal_use, post_brands, lifetime_dependencies
}

PlaceFact { root_place, projection, access, region, use, residual, origin }
```

`CallableDef` is the only callable representation and lowering path. Handler and
resumption behavior is attached evidence, not a parallel callable hierarchy.
`PlaceFact` is the same sparse fact produced for ordinary move, loan, capture, and
cleanup analysis; execution/continuation brand summaries store ranges into it.
Every `BrandId` is nominal and invariant, so equal summaries do not imply equal
brands. A sealed record is immutable. `()` is a distinguished empty execution
brand with no facts or dependencies.

### 4.7 Trait goals and answers

```text
Goal = Implemented(trait_ref)
     | Normalize(projection, expected_type_or_row)
     | TypeOutlives(type, region)
     | RegionOutlives(a, b)
     | ConstEqual(a, b)
     | EffectEqual(a, b)
     | WellFormed(term)

Answer {
  substitution, nested_obligations, polarity,
  certainty: Proven | Ambiguous, evidence
}
```

`Use`, compiler-generated `Fn`/`RunsIn`, label/destination relations, and closed
refinement facts have dedicated fast paths but produce ordinary `EvidenceId`
records so elaboration has one proof interface.

### 4.8 Frontend subsystem APIs

The following logical operations are stable implementation boundaries:

```text
lex(file) -> TokenStream + LexDiagnostics
parse(tokens) -> AstFile + ParseDiagnostics
collect_interfaces(ast_files) -> GlobalIndex
resolve_and_group(global_index, ast) -> ResolvedAstView

check_decl(decl, session) -> CheckedDecl
check_expr(expr, expectation, flow) -> CheckResult
select_call(callee, args, expectation, flow) -> SelectedCall
elaborate_call_island(root, expectation, flow) -> CheckResult

solve(goal, environment) -> SolverResult
normalize(term, environment) -> NormalizedTerm
derive_principal_use(type) -> Quantity
analyze_actual_use(body) -> UseReport
infer_regions_and_loans(place_flow) -> BorrowReport

compile_patterns(matrix, scrutinees, mode) -> DecisionDag
seal_environment(open_environment) -> SealedEnvironment
finalize_core(checked_program) -> FrontendProduct
```

None of these APIs emits user-facing text directly. They return structured
failures with origins and proof traces; the diagnostic renderer owns wording.

## 5. Level 4: syntax, collection, and resolution algorithms

### 5.1 UTF-8 and lexing

Source must be shortest-form valid UTF-8. Invalid input produces one diagnostic
per maximal invalid byte run and no AST for that file. Byte offsets remain stable.

The lexer recognizes:

- ASCII identifiers (`[A-Za-z_][A-Za-z0-9_]*`), lifetime identifiers beginning
  with `'`, and label references beginning with `@`; source and literal text
  remain UTF-8, but generation 1 does not require Unicode identifier tables;
- integer and IEEE floating literals, character, text, and byte literals;
- structural punctuation including braces, parentheses, brackets, commas,
  colons, semicolons, dots, arrows, `=>`, `::`, `&`, and `!`;
- fixed language keywords required by the core (`let`, `struct`, `enum`,
  `trait`, `impl`, `effect`, `where`, `handle`, `perform`, `resume`, `cancel`,
  `tail`, `label`, `leave`, `is`, `type`, and fixity declaration keywords);
- operator runs composed of non-delimiter punctuation.

Names such as `if`, `match`, `loop`, `return`, `yield`, `await`, and arithmetic
spellings are lexed as ordinary identifiers or operator runs. The lexer performs
no contextual keyword conversion based on declaration names.

Numeric tokens retain their complete spelling and separator-free digit runs;
lexing never commits them to a machine scalar. Integer magnitude conversion is
deferred until elaboration supplies the expected type; the G1 integer domain
then admits magnitudes through `u128` and reports an exact token-span diagnostic
for larger spellings or narrower signed/unsigned targets. Decimal floats are
parsed directly at the selected IEEE width using round-to-nearest, ties-to-even;
an `f32` literal must not be parsed through `f64`, because that can double-round
values adjacent to a binary32 midpoint. Finite overflow is a source diagnostic,
while underflow and subnormal rounding follow IEEE rules.

Source-preserving tools use the shared `lossless` layer. Its byte spans form a
gap-free partition containing whitespace, line comments, nested block comments,
literals, identifiers, and punctuation; concatenating each span's source slice
must reproduce the input exactly. It does not decode literals or replace the
semantic lexer, so adding tooling trivia cannot change parser behavior.

`for` is also lexed as an identifier so a source library may bind that name. The
type parser recognizes the exact token sequence `for < ... >` contextually when
an HRTB binder is grammatically permitted; elsewhere it remains an ordinary
identifier. Fixities use the explicit structural declarations `infixl`,
`infixr`, and `infix` for left, right, and nonassociative binary operators, and
`prefix` for right-nesting unary operators. A declared word operator such as
`not` remains an identifier token; its fixity only classifies its use in an
operator sequence.

Nested block comments are supported; line comments end before the newline.
Literal escapes are decoded once into canonical scalar/byte payloads. Numeric
base and separator validity is checked lexically; range checking waits for the
expected scalar type. A token always advances input, including on error.

### 5.2 Declaration scan and body AST

A delimiter-aware declaration scan builds headers, generics, where clauses, type
expressions, and exact token ranges for initializers and callable bodies. After
interface/fixity collection, the reusable body parser builds patterns, explicit
callable literals, inferred closures, labels, handlers, `perform`/`resume`/
`cancel`/`tail`, core `is`, blocks, applications, projections, assignments, and
flat operator sequences for one body. It does not build semantic nodes for
library control operations.

A trailing block is represented as `ContextBlock { body, span }`, distinct from
an explicit callable but with no eager/delayed interpretation. An operator
operand records zero or more prefix tokens followed by one atom; an operator
chain records its first operand and subsequent `(infix_token, operand)` pairs.
A block used as an operand is likewise contextual until expected-type elaboration.

Patterns supported in G1 are wildcard, fresh binder, scalar literal, tuple,
named struct, named enum variant, and nested combinations. Duplicate binders in
one pattern are rejected. There are no guards, ranges, or user-overloadable
pattern protocols in G1. Multiple source clauses provide ordered alternatives;
an OR-pattern node is not needed.

Top-level immutable bindings use `let`, including the narrowly permitted
type-associated qualified form described in section 4.3. Local `let` bindings
enter the current lexical value scope after their initializer. Neither form is a
module declaration.

Assignment is a statement, not an expression:

```text
AssignmentStatement = Place `=` Expression `;`
Place               = Local (`.` Field)*
                    | `*` Expression (`.` Field)*
```

The dereferenced expression must elaborate to a live, unsuspended unique
reference. A field must be a statically selected tuple field or a visible named
struct field; enum payload assignment additionally requires a dominating active
variant fact. G1 does not admit chained assignment, assignment in an operand
position, dynamic-index assignment, or an arbitrary expression on the left of
`=`. A local `let` fixes the binding's identity but creates an addressable local
place, so no separate `mut` binding form is required. Top-level `let` values are
not assignable places.

The right-hand expression is evaluated completely, with its ordinary effects
and ownership selection, before the destination is inspected or mutated. If the
destination is initialized, assignment first performs compiler-mediated
zero-use destruction of its exact old subtree and therefore requires that
subtree's principal interval to admit zero. Duplicability alone is not
sufficient when the principal lower bound is positive. If the destination is
uninitialized after a move, assignment is reinitialization and destroys no old
value. The statement produces no value; a block whose final action is an
assignment has result `()`.

The current whole-referent move form is `move *reference`, where `reference`
is one direct, unqualified local unique-reference handle. It leaves that named
handle live but its referent uninitialized until an exact whole
`*reference = value;` restoration. Reading or moving again through the handle,
passing or aliasing it, crossing a resumptive/effect-handler capture boundary,
or completing its scope while the hole is open is rejected. An unrelated
direct nonresumptive call is permitted because it neither receives the handle
nor captures the frame. Moving through an arbitrary reference expression,
moving only a projected referent field, and restoring only a field below an
empty whole referent remain outside this frontend place slice.

The scanner/parser uses iterative delimiter stacks, recursive descent for shallow
types, and a postfix loop for expressions. While forming a flat chain it uses
only the collected prefix/infix position classification, never precedence or
associativity. Error recovery synchronizes at declaration starts,
closing delimiters, commas, and semicolons. Recovered headers do not enter
interface tables; recovered body nodes are reclaimed when that body ends.

### 5.3 Interface collection

Collection is a declaration-header walk with four products:

1. a global namespace index;
2. declaration headers with body token ranges;
3. a global fixity table;
4. trait/impl/effect coherence inputs.

Nominal type and trait names are entered before their fields/members are
resolved, allowing recursive references. Duplicate names in one namespace are
errors. Constructor names enter the value namespace. Every named or anonymous
callable receives a fresh nominal `CallableId`; a named declaration's value name
resolves to that anonymous function-item identity.

Callable signatures require `->`. Missing result means unit only; it is not
return-type inference. Missing effect annotation means a closed empty row;
explicit `/ {}` normalizes identically. `!` is never omitted.

Effect collection records declaration-site operation result types and resumption
quantities. A nonterminal operation must declare a valid `Quantity`; an operation
whose declaration-site result normalizes to `Never` is terminal and must not
declare one. Substituting an operation generic later cannot change terminality.

Fixity declarations are source declarations keyed by `(prefix|infix, token)`
with precedence `0..255`; infix entries additionally carry associativity `left`,
`right`, or `none`. Thus one spelling may have independent prefix and infix
entries. A fixity applies to all bodies after collection, independent of textual
use position. Duplicate incompatible declarations are errors; identical
duplicates collapse. Operators without a declaration for their position are
errors at grouping time.

### 5.4 Operator grouping

Flat streams are grouped with a deterministic shunting-yard algorithm. Prefix
operators nest from right to left and bind according to their declared
precedence. Higher-precedence infix operators bind first. Equal infix precedence
requires identical associativity; `none` or mixed associativity is an error with
both declarations cited. Grouped operators become ordinary call syntax whose
callee is the resolved operator binding and whose operands retain source
evaluation order.

Grouping spans a complete linked chain, including contextual blocks. The root of
that grouped chain is a call island and remains open during environment inference
until all nested operator applications connected by shared inference variables
are solved.

### 5.5 Name and label resolution

Lexical scopes are immutable parent-linked maps built in source order. Local
bindings become visible after their initializer. Callable parameters and pattern
binders are visible only in their bodies. Generic parameters shadow outer generic
parameters but cannot collide within one binder list.

Label binders use a separate lexical namespace. `@name: T { ... }` creates a
fresh nominal brand with intrinsic `Label<T>` evidence; `@name: { ... }`
infers `T`. Every direct reference uses `@name` and resolves only to the nearest
active binder. Each named callable also has an implicit label named after the
callable, with its declared result as the payload type. Bare identifiers never
resolve to labels.

Refinement source names do not enter an ordinary lexical scope during parsing or
resolution. A pattern creates fresh binder keys. A source name resolves to such a
key only while expected-type elaboration has activated the corresponding
`Bindings<P>` argument.

## 6. Level 4: type elaboration and trait solving

### 6.1 Bidirectional elaboration

`Expectation` is `None`, `Exact(TypeId)`, or `CoerceTo(TypeId)`. G1 coercions are
limited to lifetime/reference reborrowing and never include value-to-callable or
numeric truth coercions. Literal types are selected from an exact expected scalar
type or a documented default (`i64` for integers and `f64` for floats); an
out-of-range default is an error.

Checking an expression returns a value category (`Place`, `Value`, or `Never`),
normalized type, outward effect row, provisional Core, and normal flow state.
Arguments, aggregate fields, payloads, and operands are checked left to right.
Expected types flow inward only after the outer declaration/call candidate is
selected.

An ordinary generic call owns a deterministic mutable inference table for the
callee's type binders. Caller binders remain rigid. Argument and expected-result
constraints may bind either mutable side; substitutions are transitively
resolved before specialization keys are formed. Recursive bindings fail the
occurs check, kind mismatches fail before structural unification, and unresolved
or conflicting tables produce ambiguity diagnostics rather than guessed types.

### 6.2 Nominal types and generics

Nominal equality is declaration identity plus equal substitutions. Aliases are
expanded during normalization with a recursion guard and never create identity.
Generic arguments are supplied or inferred in binder order, and kind mismatches
are errors before trait solving. All declarations are checked for well-formed
generic bounds under placeholders, not inference variables.

`u32` and `Quantity` are the complete, closed set of G1 const kinds. Their
substitutions participate in nominal equality and specialization identity just
like type substitutions, but never masquerade as runtime field types. Thus
`Tag<3>` and `Tag<4>` are distinct even when `Tag` is phantom and both layouts
are otherwise identical. A named const binder is legal only in a generic
argument position whose declaration has the same const kind; using it as a
field, parameter, or result type is rejected. Generic callable consts are
inferred through nominal structure, and symbolic checked `u32` arithmetic is
folded after specialization. Const-generic aliases, trailing defaults (including
defaults that reference earlier const binders), and checked arithmetic normalize
into the same canonical identity; invalid arithmetic and kind mismatches are
diagnosed. Ground fixed-array lengths are checked against the 1024-element G1
layout limit and lowered to fixed tuple-backed storage, so array length affects
real runtime layout rather than only phantom identity. Associated-type const
parameters use the same structural values and normalize before runtime signature
lowering.

Owned nominal layout recursion is rejected after normalization. Edges through
references, callables, handlers, and resumptions break the owned-layout cycle.
Variance is inferred by a monotone fixed point over field occurrences, seeded by
the built-in reference/function rules. Compiler-created label/environment brands
and any phantom dependency on them are invariant.

### 6.3 Call islands and contextual blocks

A call island is the maximal resolved call/operator expression connected through
unresolved callable signatures, effect rows, or a common environment variable.
It is elaborated in four passes:

1. **Shape pass:** elaborate non-contextual callee/argument shapes, instantiate
   generic signatures, and retain each contextual block as a typed placeholder.
2. **Selection pass:** transactionally test call candidates and their declared
   `Fn<Args>` constraints until one normalized signature interpretation remains.
3. **Body pass:** for each contextual block, inspect its selected parameter. If
   that exact expected type is callable or a type variable with a uniquely
   applicable `Fn<Args, Output=R, Effects=e>` relation, create a fresh anonymous
   callable and check the block on invocation. Otherwise check it as an eager
   block value. No coercion or name-based heuristic is attempted.
4. **Closure pass:** solve linked `RunsIn` goals, complete the common environment
   ledger, infer post-environments, then seal at the island root unless constraints
   explicitly escape through its generic result.

If callable applicability or eager/callable interpretation remains ambiguous,
the block is rejected before its body is checked. Diagnostics show the competing
parameter obligations.

Intrinsic `Fn` obligations require a structural callable or matching lexical
evidence, including the declared input, output, and effect equalities. A concrete
non-callable argument is a type error, not a deferred MIR invariant failure.
Obligations whose subject is still unknown remain live through inference and
are discharged to a fixed point before Typed Core is sealed; solving an ordinary
type variable alone does not prove its `Fn` obligation. This checking is shared
by ordinary calls and source-defined operators, independently of their names.

### 6.4 Callable relations

For every callable body, capture analysis begins with resolved free-place uses,
then borrow and use checking determines capture mode. The compiler synthesizes
only valid receiver relations:

- observe-only state: `&F`, `&mut F`, and `F` forms may exist;
- mutated state: `&mut F` and `F` forms may exist;
- consumed state: only `F` exists.

Each form receives an intrinsic sealed `Fn<Args>` relation with `Output` and
`Effects`. `RunsIn<Access,Args>` is synthesized for each proven compatible
environment. Borrowed access has `After = E`; owned access may produce a fresh
post-environment. For a `Never` output, no normal `After` is required.

At a call, explicit source receiver forms win. Otherwise selection tries shared,
unique, then move, rejecting a less-consuming form if its body requirements do
not fit. Environment access is chosen by the same shared, unique, move order.
Both selected accesses are reflected in ordinary place/loan state.

### 6.5 Canonical tabled solver

The solver canonicalizes a goal by fully resolving known assignments, replacing
free inference variables with numbered canonical variables, preserving de
Bruijn-bound variables, and recording each placeholder's universe. The key is
`(canonical goal, ParamEnvId)`. Each lexical parameter environment is sorted,
deduplicated, and interned once on declaration entry; individual goals do not
rebuild it. G1 has one reveal mode because it has no specialization or opaque
module boundary.

Each table is `New`, `Evaluating`, or `Complete(answers)`. Evaluation uses a
deterministic work queue:

1. try intrinsic and lexical compiler-generated evidence;
2. match caller where-bounds;
3. enumerate coherent global impls by `(trait, self-head constructor)` index;
4. instantiate binders in a fresh universe/snapshot;
5. unify the head and enqueue where-goals;
6. normalize associated values and retain distinct canonical answers.

Ordinary recursive cycles yield `Ambiguous`, not success. Declared auto traits
may use coinductive success only when every edge in the cycle is an auto-trait
goal and no explicit negative impl applies. At use sites, `Proven` is required;
`Ambiguous` is accepted only while collecting constraints and must disappear by
finalization.

Associated types, associated effect rows, and GATs are projections with the
trait substitution plus associated-item generic arguments. Normalization selects
one impl, substitutes its associated definition, and recursively normalizes.
Generic callable parameter and result projections are normalized in that
callable's lexical evidence environment before specialization. A where-clause
equality is keyed by the exact trait head, associated item, and GAT arguments;
the ordered GAT argument key preserves each type-or-lifetime kind, including
rigid and higher-ranked placeholder lifetime identities;
it may rewrite projections nested under tuples, references, and nominal
applications while retaining the callable's rigid type parameters. Facts never
flow between callables. Missing keys, conflicting equalities, and recursive
projection answers are errors rather than requests for global guessing.
Two different normalized answers are ambiguity because G1 has no specialization.

This is one compact goal engine, not a Chalk-style family of databases. Goal,
answer, and work items are flat tagged records in side arrays. The common sealed
intrinsics (`Fn`, `RunsIn`, labels, environments, refinements, `Use`, and `Drop`)
take direct indexed paths before canonicalization; only ordinary user-trait and
projection goals enter tables. An answer stores a range into shared substitution
and obligation arrays rather than owning vectors. Completed tables with no
external references may be evicted between bodies except for globally reusable
ground goals.

### 6.6 HRTBs and universe solving in traits

Checking `for<T, 'a> Goal` introduces rigid type and lifetime placeholders in a universe strictly newer
than all surrounding inference variables. An answer may mention those
placeholders only beneath the binder that introduced them. The leak check rejects
an answer if a preexisting inference variable becomes equated with, or constrained
solely by, a newer placeholder. Applying a higher-ranked answer replaces bound
variables with fresh inference types or regions in the caller universe. Source
where-goal binders admit type, lifetime, const, and effect-row parameters.
Higher-ranked outlives constraints retain their own binder scope; unrelated
universal lifetimes do not acquire an outlives relation, and a shadowing binder
cannot leak facts into an outer lifetime of the same spelling.

### 6.7 Coherence, orphan, and negative reasoning

All global impl heads are checked before bodies:

- an impl is legal only when the trait or the outermost nominal self type is
  declared in this program; compiler intrinsics follow their explicit policy;
- compiler-sealed traits reject source impls;
- `Use` allows at most one positive principal impl per nominal type and no
  negative impl;
- `Drop` allows at most one exact intrinsic implementation per nominal type;
- two positive impl heads for one trait must not unify under any legal
  substitutions;
- positive and negative heads must likewise be provably disjoint;
- negative impls obey the same orphan rule and cannot contain unconstrained
  generic parameters.

Because there is no specialization, overlap is always an error rather than an
ordering decision. A negative goal is proven only by a matching explicit
negative impl, compiler-generated closed refinement fact, sealed-trait fact, or
exhaustive fact about a closed nominal enum. Failure to find a positive impl is
not negative proof.

Compiler-generated impls for unnameable callable, environment, label,
resumption, and refinement types are stored in the lexical evidence environment,
not the global coherence table.

### 6.8 Solver safeguards

Default G1 limits are configurable but deterministic: 128 nested goal frames,
1,024 distinct answers per table, 1,000,000 total table steps per declaration,
256 alias/projection normalization steps, and 65,536 canonical tables per
compilation. Crossing a limit produces a structured complexity diagnostic with
the shortest repeating goal trace; it never guesses a result. Impl declarations
whose recursive where-goals do not decrease any nominal/type constructor measure
are rejected early unless they are valid auto-trait recursion.

## 7. Level 4: ownership, lifetimes, `Use`, and `Drop`

### 7.1 Region model and NLL input

Elaboration emits Typed Core and MIR lowering exports the shared sparse
`PlaceFlow` facts. NLL, move checking, quantitative use, environments, captures,
and cleanup consume this one graph. Every multi-predecessor join carries a
canonical predecessor fact, and every indirect-call suspension carries its
exact outward row plus the source ownership snapshot. Import recomputes the CFG
joins, callable row, move paths, use intervals, residual bitmaps, live loans, and
cancellation safety before trusting those facts. The source lowerer's
`moved_paths`/`actual_uses` maps remain only source-spanned diagnostic and MIR
shape bookkeeping; successful acceptance is decided again by the PlaceFlow
fixed point. `PlaceFlow` is proof metadata indexed by MIR locations, not a fourth
semantic IR.

Regions are sets of CFG points. Constraints arise from reference creation/use,
assignment, reborrowing, type variance, callable captures, labels, handler
delimiters, environment/refinement dependencies, and `T: 'a`. Liveness seeds are
propagated through outlives edges to a least fixed point.

The current bootstrap implements the first sound vertical slice of this model.
Typed Core records canonical region identities, issuance points, reference-use
point sets, inferred end points, and parent-region outlives edges. A deterministic
backward least-fixed-point solver computes live-in/live-out sets over explicit
point successors; its oracle covers diamonds, joins, kills, and conservative
backedges. Within a source block, a named loan ends after the last use of every
alias carrying that region. Handler computations and all clauses contribute to
the statement's use set, so a region used by either branch remains live through
the handler join and may end immediately after the handler. A use after the join
keeps it live and preserves the conflict. Child reborrows likewise keep the
parent suspended until the child region ends.

The inferred boundary is an explicit Core `EndBorrow` and lowers to the existing
verified MIR/bytecode end-borrow operation. This applies equally to whole and
projected places and permits an owner, including a custom-`Drop` owner, to be
used after its loan's actual last use. Closure-containing blocks remain
conservatively lexical. Resumptive suspension is accepted only through the
existing handler/continuation capture checks, and loop/backedge liveness widens
to the least fixed point. Local-reference
escape remains rejected independently of early loan ending.

A first-class callable may carry shared-reference captures across value aliases
and grounded generic identity/forwarding calls when every retained origin stays
within its proven referent scope. This includes forming a typed callable directly
as the argument and result of a transparent generic identity; naming the closure
in an intermediate local is not semantically required. The callable value carries
the capture tuple's reference paths and origins through Typed Core; block exits
reject an origin rooted in a local owner that the callable would outlive, and a
conflicting unique borrow remains rejected until the callable is consumed. These
environments use an owned, single-shot receiver: invocation moves and
deconstructs the environment before reading its captured reference, avoiding an
unproven `&&T -> &T` copy. Unique-reference environments remain rejected until
each callable can own and release a distinct reborrow without aliasing or
double-ending the source loan.

A monomorphic ordinary function used in value position forms a capture-free
typed callable carrying the function's exact parameter, result, and outward
effect signature. Inherent functions already have that ordinary identity.
Qualified associated aliases are normalized to that ordinary
function identity before callable formation, so `let f = Namespace::member`
and an unqualified function item have identical first-class behavior. A generic
function item also forms a callable when an enclosing `Fn` context supplies its
concrete shape; it is specialized through the same closure request rather than
becoming a runtime-polymorphic value.

An otherwise unconstrained generic function item may be bound locally in a
compile-time-only deferred state. Its first direct local call must determine one
ground parameter/result/effect shape and discharge the selected generic
function's `where` evidence. Discovery then replaces the apparent direct target
with one ordinary capture-free closure specialization; later calls must use that
exact shape. Multiple consistent calls are permitted. Conflicting calls, return,
aggregate storage, or block exit before resolution are rejected. The deferred
state never appears in Typed Core, bytecode metadata, or the VM.

When a transparent generic callback wrapper has no closed discovery edge, one
explicit pure typed callable argument may select the bounded runtime fallback.
The wrapper is inlined once under the existing recursion guard, its closed
scalar/nominal/tuple signature forms a synthetic callable identity, and lexical
capture modes are recomputed before the environment is moved or borrowed. An
identical-variable `if`/`else` join is normalized to that one value. Reference
parameters/results, effect rows, inferred signatures, multiple callable
arguments, opaque wrappers, and recursive growth do not enter this fallback.

Reference-returning generic callbacks use an exact symbolic origin route when
the selected concrete closure returns one explicit parameter, one planned
reference capture, or a numeric tuple projection of either. A unique direct or
tail-wrapper specialization relation composes that route back to the caller's
runtime argument; the resulting region is therefore the original owner's
region, not a fresh or guessed borrow. Multiple compatible references do not
make the route ambiguous when the closure selects one exact source. Escape and
unique-alias checks still apply to that selected source. Opaque calls,
non-identical control alternatives, multiple indistinguishable wrapper edges,
and unsupported projections fail closed rather than choosing an origin.

### 7.2 Loans and conflicts

A loan records borrowed place, shared/unique kind, issuing point, region, and
origin. At each point:

- any number of shared loans may overlap;
- a unique loan conflicts with every other overlapping loan to an overlapping
  place;
- move, assignment, destruction, or mutable projection conflicts with a live
  overlapping loan;
- a shared reborrow can derive from shared or unique access;
- a unique reborrow requires unique access and suspends use of its parent unique
  reference for the child region.

Place overlap is field-sensitive for statically distinct tuple/struct fields and
conservative for dynamic indices, dereferences, and unions of enum variants.
There is no two-phase borrowing in G1.

A copy through a temporary reference expression is elaborated through an
internal scoped reference local, so dereference, region liveness, and cleanup
use the same rules as a source-named reference. Tuple/struct projection chains
over temporary wrapper results preserve the selected reference-field origin at
every hop. An owned enum payload field may be read only on the successful edge
of a dominating `is Variant` decision; the proof is discarded at the join, and
a reference payload retains its original owner and escape constraints. The
same proof can authorize a duplicable payload projection through `&Enum`; the
fresh MIR register created by dereferencing the enum carries the exact variant
proof into that projection. Aggregate deconstruction transfers each tracked
reference-field origin to the corresponding binding before retiring its owner.
A projected reborrow through a temporary reference expression materializes the
parent reference as the root of the MIR borrow-parent chain. The frontend
narrows its consumed whole-place loan to the selected child path, while MIR
retains and ends the parent only after every child and intermediate projection
carrier has ended.

### 7.3 Escape and variance checks

Subtyping is region containment plus declared variance. `&'a T` is covariant in
both terms; `&'a mut T` is covariant in the region and invariant in `T`; callable
arguments are contravariant and results covariant. Nominal variance is the fixed
point computed from fields and bounds.

An unused generic parameter is bivariant. Shared-reference referents preserve
their surrounding variance, while unique-reference referents are invariant.
Variance through a nominal application composes with the referenced
declaration's fixed-point evidence. Until a projection normalizes to a known
shape, every parameter mentioned beneath it is conservatively invariant.
Declaration order and binder spelling do not participate in the evidence key;
each nominal instance references its declaration's canonical evidence.

Lifetime arguments of nominal applications remain in a source side table at
their exact binder positions while runtime monomorphization erases them from
type identity. A nominal field `&'a T` or `&'a mut T` transports its loan origin
through construction, whole-value moves, calls, and authorized deconstruction;
projecting that field recovers the same origin rather than inventing a fresh
loan. Shared and unique stored references are both covariant in `'a`, while the
referent of a stored unique reference remains invariant. Private-field authority
therefore also controls who may recover or deconstruct a stored reference.

Labels, environment brands, handler evidence, binding packs, and refinements add
hidden invariant dependencies to containing callable/nominal types. A result,
stored value, or capture may cross a scope boundary only if every such dependency
outlives the destination. This is the sole dead-label/environment escape
mechanism.

### 7.4 Principal `Use` derivation

The dedicated engine computes one principal interval per normalized type:

- built-ins and references use the specification's fixed intervals;
- a callable, handler, resumption, binding pack, or environment derives from its
  hidden owned fields and compiler-declared quantity;
- a struct intersects every field interval;
- an enum intersects every payload field of every variant, with a fieldless
  variant contributing unrestricted use;
- `Available<E>` is affine if zero use of `E` is legal and exact-linear otherwise;
- recursive edges through references use the reference interval; an owned layout
  cycle is already illegal.

Intersection is `[max lowers, min uppers]`; an empty result rejects the nominal
declaration. An explicit `impl Use<Q>` replaces the structural principal only
when `Q` is contained in the derived interval. Results are memoized by canonical
type and substitution.

An open environment begins with the intersection of its ledger entries' safe
intervals and narrows with every `Use<Q>` request contributed by linked APIs.
Sealing fails if no principal interval contains every requested actual transition.

### 7.5 Actual-use analysis

Each owned binding, move path, environment authority, availability witness, and
resumption gets an interval dataflow variable. Transfer functions are:

- owned whole move or consuming call/transition: add `[1,1]` and propagate the
  residual ownership obligation to the destination;
- explicit or implicit opaque destruction: add `[0,0]` and require the complete
  destroyed subtree to satisfy `Use<[0,0]>`;
- copy: add one owned use to the source and require the principal upper bound to
  permit duplication; the source remains live and the copy becomes an
  independently checked owner;
- borrow/reborrow: add `[0,0]` and emit loan constraints;
- sequence: interval addition;
- exclusive normal branches: interval hull;
- terminal branch: no contribution to a normal join;
- unknown zero-or-more repetition: `[0,0]` if the body is unused, otherwise an
  infinite upper bound;
- invocation nested under a callable/resumption quantity: interval
  multiplication.

Finite upper overflow widens to `Infinite`. Lower-bound arithmetic uses a
one-past-`u32` sentinel; reaching it is an unsatisfied-use error because no valid
`Quantity` can contain it. A final actual interval must be contained in the
principal interval on every definition-to-exit path. A positive principal lower
bound additionally creates a must-move obligation on every normally completing
path. Counts contributed only by non-consuming copies do not discharge the
still-live source owner.

Source `move value` forces whole-owner transfer even when `value` is duplicable.
An ordinary owned use copies a duplicable value and moves a non-duplicable
value. Borrowing is always explicit through `&place` or `&mut place`.
`move (places) { ... }` optionally forces the listed outer places into a
closure environment by value, even when the closure body only borrows them.
Inference remains deliberately conservative across branches, closures,
projections, labels, handlers, effects, resumptions, active loans, and custom
`Drop`; linked source-defined selector alternatives retain their correlated
environment facts rather than becoming unrelated escaping closures. The
selected `Move` versus `Copy` mode is always explicit in Typed Core and MIR. A
transfer is rejected for an unavailable, borrowed, or partially moved source
place. Immediate abort and proven nontermination have no successor ownership
state and are exempt; ordinary terminal or nonlocal control with cleanup is
not.

This is the only quantitative checker. Callable invocation bounds, environment
transitions, resumption quantities, cancellation zero-use checks, and
`Available<E>` all emit events into these same interval variables and use the
same containment operation; none has a feature-specific affine/linear checker.

Before ownership checking, the frontend computes a canonical interprocedural
performance summary for each emitted callable. The summary retains the finite
set of caller-suffix multipliers on normally returning paths, a distinct
abandonment bit, and a widening bit for unresolved or unbounded recursion and
opaque dispatch. Sequential execution convolves multiplier sets with checked
multiplication; exclusive paths take set union; terminal paths contribute
abandonment but no normal multiplier. Direct and grounded generic calls use the
callee's concrete summary. Recursive call components are iterated to a stable
fixed point and widened only when the bounded analysis does not stabilize.

Only a non-widened, non-abandoning singleton supplies an exact ownership
multiplier. Thus two sequential exact-two performances retain exact factor four
rather than collapsing to a boolean "multi-shot" fact. A may-effect row is not
must-perform evidence: unused sibling operations and row membership neither add
nor remove a multiplier. Sorted callable summaries are part of canonical Typed
Core and therefore participate in its fingerprint.

Terminal handler dispatch contributes a branch union only when the shared
pattern-matrix exhaustiveness checker proves the matching payload rows total;
otherwise the summary retains an abandonment alternative and cannot authorize
an exact ownership multiplier. Effect-row-empty calls still consult normal-return
evidence: internal effects cannot multiply their caller's suffix, but an
unconditionally nonreturning callee must not be replaced with an identity path.

Implicit cleanup is permitted only when every still-live subtree permits zero
use. Cleanup itself adds `[0,0]`. Explicit `destroy` has the same opaque semantics
and requires `Use<[0,0]>`; it cannot discharge a positive lower bound.

Memoized global values must have the unrestricted principal `Use` interval.
Because reads are not source-bounded ownership events, a restricted-use global
is rejected during interface validation before lowering; G1 does not synthesize
singleton or bounded-read evidence for globals.

### 7.6 Move joins and cleanup

At CFG joins, each move path must have the same initialized/moved state on all
normal predecessors. Partially initialized aggregates must have the same active
children. The compiler reports unequal states rather than dropping an extra value
on one branch. Cleanup plans are derived only after this check.

Any number of disjoint tuple or visible-struct fields may be moved from an
owner without a custom `Drop` hook. Each moved child becomes independently
owned, while the parent shell retains all other initialized children. Repeating
a move of the same child, using the parent as a whole, or overlapping an active
loan remains invalid. Nested ownership is represented compositionally: moving
an aggregate child creates a new child owner, whose own disjoint fields may then
be moved. If both residual shells remain live across a continuation capture,
each carries its own canonical initialization bitmap and cleanup obligation.

For every normal and nonlocal exit, destruction order is lexical newest first;
each value runs its custom hook once, then active fields in reverse declaration
order. A terminal effect destroys the abandoned continuation before entering its
clause only if every abandoned subtree permits zero use. Return, `leave`, terminal
effects, cancellation, and other nonlocal cleanup may not discard a must-move
value. Panic/abort has no cleanup plan, and a path proven not to terminate has no
exit obligation.

### 7.7 `Drop` validation and drop checking

An intrinsic `Drop` impl must have exactly `drop(&mut self) ->`, an empty outward
row, no label transfer, effect performance, suspension, resumption capture,
field move, or ownership return. These restrictions are checked both syntactically
on provisional Core and semantically after call/effect normalization.

`Drop` has the frozen supertrait `Use<[0,0]>`. Validation therefore rejects a
`Drop` impl for every type with a positive principal lower bound. Running the
hook and later field destruction both contribute zero uses.

Safe partial moves from a custom-`Drop` type are rejected. Drop checking assumes
the hook can observe every generic field and borrowed component; there is no
`may_dangle` escape in G1. All referenced regions and static brand dependencies
must therefore remain live through the drop point. Divergence in a hook is
allowed and leaves later structural destruction unreachable.

## 8. Level 4: environments, labels, effects, and refinements

### 8.1 Open environment formation

When selected callable constraints mention the same unresolved `E`, the call
island creates one fresh open execution `BrandId` with scope equal to the smallest
region enclosing the island. Every linked body contributes indices into the
ordinary shared place-flow facts:

```text
(place, projection, Observe|Mutate|Move, required_region,
 actual_use, effects, residual_state, origin)
```

The environment summary is a sorted unique view by root place and projection;
it is not a second mutable ownership ledger. Overlap, actual use, residual state,
capture mode, and regions are read from the ordinary place-flow engine. Different
bodies do not need identical footprints; they need compatible transitions from
the same incoming nominal state. Physical capture layout is not part of identity.

Owned body access creates a post-state candidate from its residual ledger.
Borrowed access must have `After = E`. Mutually exclusive bodies may each own the
same exact-linear transition because branch use joins by hull; sequential bodies
add and fail. All normal alternatives constrained to a common `After` must have
structurally equal residual ledgers and lifetime obligations, after which one
fresh nominal post-environment is assigned. Terminal alternatives do not join.

An environment seals when leaving the maximal call island and no unbound
constraint can add a linked body. Sealing sorts its fact indices by source place,
checks requested use intervals, synthesizes lexical `RunsIn` evidence, and freezes
the brand. No separate environment fixed point runs. Escaping generic relations
retain only abstract `Fn`/`RunsIn`/`After` facts; source-local place IDs never
escape.

### 8.2 Availability witnesses

`Available<'e,E>` can be introduced only by the compiler's incremental-alternative
lowering. It has no constructible runtime payload or general zero-sized coercion.
Consuming it either activates another owned `RunsIn<E,...>` transition, passes
the same witness onward, or invokes the exact intrinsic `available_to_unit` after
proving `E: Use<[0,0]>`. All other attempts to construct, copy, project, or erase
it are rejected before Core finalization.

### 8.3 Labels

A label binder allocates one invariant nominal `BrandId` with a scope region and
sealed `Label<T>` evidence. `Label<T>` implies `Fn<(T), Output=!>`, so
`@name(value)` and invocation through a bounded generic parameter are ordinary
diverging applications at the typed surface.

Labels are proof-only: they have no runtime representation or erased form.
Specialization substitutes the exact generative brand, then mandatory control
inlining fuses every invocation into the frame containing its binder. Typed
Core records the resulting direct target and cleanup boundary, and MIR emits
the existing `LEAVE` edge. If fusion cannot prove an exact active destination,
compilation fails instead of materializing a dynamic label target. A
closure/effect/environment mentioning the brand inherits its scope dependency;
labels may not cross multishot continuation capture.

Label-indexed protocol terms include normalized brand arguments statically.
Before runtime serialization each active instantiation maps to a concrete
protocol table key and hidden handler evidence; the static brand itself is
erased.

### 8.4 Effects and rows

Protocol identity is declaration identity plus normalized type/const/brand
arguments. A call whose path resolves in the effect namespace first checks
payloads left to right, then adds the protocol
to the outward row unless an active matching handler removes it. A callable may
therefore invoke an operation without a lexical handler exactly when the
normalized protocol instance is a member of its declared outward row. Every
caller must either handle that instance or include it in its own outward row.
Payload evaluation and ownership transfer are unchanged by crossing callable
boundaries: completed payloads move into `PERFORM`, and a resumptive result is
defined only on the eventual resume edge.

The bytecode entry callable is a closed dynamic boundary: `main` must have an
empty outward row. Embedders may invoke another verified callable directly; if
no installed handler accepts its outward performance, execution terminates with
the normative `UnhandledEffect` runtime fault rather than synthesizing a source
handler or silently dropping the operation.

Source effect-row polymorphism uses an explicitly kinded callable binder,
`<e: EffectRow>`. An open row is written `{Ask, Trace | e}` (or `{| e}` for an
empty known prefix); `Fn::Effects` also accepts the equivalent bare tail
`Effects=e`. A normal type or lifetime binder cannot be used as a row tail, and
row binders are not type arguments. Rows normalize to a sorted, duplicate-free
protocol set plus at most one tail. Matching `{Known | e}` against a closed row
binds `e` to the canonical residual beyond `Known`; repeated occurrences require
the same residual. Known members are retained when the row is sealed, omitted
`Fn::Effects` remains anonymous whole-row inference, and executable outward rows
must be closed before finalization. Effect-row aliases remain closed in this
compiler slice.

Surface handlers admit completion and operation patterns in one arm block. A
payload-only operation arm tail-resumes with its body value; a final
continuation binding gives full control and calls ordinarily as `k(value)`.
Legacy `perform`, `with`, `resume`, and `cancel` spellings remain accepted
during migration and normalize to the same structural Core nodes.

Handler checking proceeds in source order:

1. normalize each protocol/operation key;
2. group all clauses for one operation into one ordered pattern matrix;
3. create anonymous clause callables and one shared incoming environment for the
   dispatch;
4. compile and check the decision DAG;
5. prove total coverage or mark the handler partial;
6. remove totally covered protocol keys from the body row and retain uncovered
   keys for a partial handler.

Handlers are deep. Clause and continuation effect rows are solved assuming the
same delimiter is reinstated by resume. The nearest matching handler is a runtime
property, but static normalized keys and hidden evidence guarantee correct
routing.

The handled body and every clause coexist while the delimiter is active, so
they cannot independently capture the same unique reference. Code returns or
ends unique state used by the body before branching on its result; clauses may
then borrow that state in the ordinary sequential scope.

### 8.5 Resumptions and cancellation

At a nonterminal `perform`, continuation capture computes all live owners, loans,
environment states, active labels, and handler dependencies between the site and
delimiter. It creates an anonymous `CallableId` of kind `Resumption` whose
principal interval is the operation's declared quantity and whose continuation
brand summarizes that captured state.

One-shot invocation moves the resumption and transitions its environment. Multi-shot
shared/unique forms are synthesized only if every capture is structurally
duplicable, no unique loan crosses capture, all handler dependencies are
duplicable, and multiplied use intervals remain legal. Ordinary `discard(k)`
consumes a cancellable resumption and applies its cleanup plan. A performance site is rejected if
cancellation exposes a captured owner's zero-use path whose principal lower bound
forbids zero.

For a terminal operation, no resumption type or normal successor exists. The
continuation cleanup plan is checked immediately and runs before clause entry.
The check requires zero-use permission for every abandoned subtree; terminal
control cannot discard a must-move capture.

### 8.6 Shared pattern compiler

Both handler clauses and `is` call:

```text
compile_patterns(pattern_matrix, scrutinee_types, match_mode)
```

The algorithm is a Maranget-style matrix specialization with source-order leaf
priority. It selects the leftmost column containing a refutable constructor,
partitions enum/scalar/tuple/struct constructors, shares repeated tests, and
emits a default edge. It never re-evaluates a scrutinee. Exhaustiveness is the
absence of a reachable failure leaf; unreachable source rows are warnings.

Handler mode may move payloads according to clause parameter ownership. `is`
mode is observational/copying only: a binder receives a copy when the projected
type is duplicable, otherwise a borrow tied to the subject's region. A refutable
ownership-moving `is` is rejected and must be expressed through exhaustive
handler matching.

An exhaustive ownership-moving matrix consumes the matched aggregate shell,
discharges that shell obligation, and creates independent move paths and
must-move obligations for every non-discarded field of the selected constructor.
It is rejected for an aggregate with custom `Drop`, including a fieldless one,
because deconstruction does not invoke the hook.
The compiler first checks nominal field visibility at the
pattern site; private fields reserve ownership deconstruction to the authorized
source-entry domain defined in section 4.3. `_`, `..`, omitted fields, and
omitted payload subpatterns are opaque
discard operations and require every discarded subtree to satisfy
`Use<[0,0]>`. They never silently satisfy a positive lower bound.

The concrete G1 ownership-pattern spelling follows these rules. `field: _`
explicitly discards one named struct field, while leaving a struct field out of
the braces discards it implicitly; `..` makes that remainder intent explicit
but does not weaken the same zero-use check. Tuple `_` discards its position,
and tuple entries not named because the pattern ends early are likewise an
implicit discarded suffix. A pattern contains at most one `..`. Tuple binders
before it count from the beginning and tuple binders after it count from the
end, so `(first, .., last)` leaves the middle as the discarded remainder.
Without `..`, excess entries are an arity error. A one-element tuple pattern
requires the trailing comma `(element,)`, matching tuple expression and type
syntax. Lowering projects every runtime field first, then destroys discarded
runtime children in reverse declaration order before consuming the empty
aggregate shell; exact-`[0,0]` children without observable drop behavior are
represented as erased `AVAILABLE` fields and produce no register or opcode.

### 8.7 `is` and binding environments

For `subject is Pattern`, elaboration evaluates `subject` once and allocates
fresh positive/negative refinement brands. Every binder receives a fresh
`BrandId` of kind `BinderKey`, even if source text is reused elsewhere. The
positive environment
records `Provides<Key,Value>` and positive/closed negative facts; the negative
environment records only facts justified by the failed structural test.

The runtime payload contains copied values, borrowed projections, temporary
owners, and guards necessary to keep those projections valid. It is represented
as `Bindings<'a,P>`. The result is ordinary
`Test<Bindings<P_yes>,Bindings<P_no>>`. Expected hidden binding parameters
activate source names only in the matching contextual callable body. A negative
body cannot resolve a positive key.

Tuple environment composition `(P,Q)` is accepted only when binder keys are
distinct, loans are compatible, facts do not conflict, and lifetimes have a
common valid scope. The empty context is `()`. `is` is completely replaced by
decision-DAG Core operations, handler dispatch, nominal construction, and
binding-pack creation before finalization.

## 9. Level 4: Typed Core construction and boundaries

### 9.1 Evidence-bearing construction

Typed Core is built in arenas while elaborating, but is not externally visible
until finalized. It contains only the specification's values and computations:

```text
Values:
  local, literal, struct/enum/tuple, callable, handler, resumption,
  binding pack, available witness (static-only)

Computations:
  pure, let, construct, project, call, tail call,
  new-label, typed-label, leave,
  perform, handle, resume, cancel, destroy, primitive, host-import call
```

A host-import call can originate only from a manifest-bound standard-library leaf
and carries its checked `HostImportId`; ordinary source cannot construct this
Core node.

Calls carry selected `FnEvidence` and `RunsInEvidence`; projections carry
normalized type and move/borrow mode; nonlocal operations carry cleanup and
runtime-target links. Evaluation order is explicit through nested lets, so later
lowering cannot reorder arguments or fields.

### 9.2 Finalization checklist

Finalization fails unless:

- every type, const, region, effect row, associated projection, and callable
  receiver is resolved;
- every goal required for execution is proven, not ambiguous;
- every environment is sealed and every owned transition has a post-state or no
  normal successor;
- every place satisfies move, borrow, use, and drop checking;
- every handler has known coverage and every resumption has legal resume/cancel
  paths;
- every label brand has a distinct runtime realization and valid scope;
- all `is` nodes are lowered and no positive binder leaks;
- no forbidden control/library/arithmetic semantic node exists;
- the bytecode entry callable has an empty outward effect row; every other
  executable outward row is closed and is preserved in its callable signature.

Static evidence is then erased from runtime operands but retained in a side table
until MIR and bytecode verification metadata have been emitted. `Available`
values erase completely; binding packs retain only their payload tuple; brands
retain only their already-resolved runtime label/protocol/handler associations.

### 9.3 Abstract interface boundary

An `AbstractInterface` contains only declaration identities, generic binders,
nominal definitions, variance, trait/effect heads, coherent impl headers, and
abstract callable relations:

```text
F: Fn<Args, Output=R, Effects=e>
F: RunsIn<Access, Args, After=S>
```

It never contains local/place IDs, concrete capture layouts, binder keys, solver
variables, loan IDs, or diagnostic spans as semantic fields. Anonymous exported
identities receive stable owner-derived opaque names.

The G1 module loader keeps this as compact tables owned by the crate session and
does not serialize or hash them.
Conformance/debug mode exercises a canonical serialization to prove that no
source-local identities escape. A future package format may persist a versioned
form without putting that cost on the self-host path.

### 9.4 Bytecode serialization boundary

The frontend never chooses `.grbc` table indices. It provides the backend with
normalized runtime types, callable signatures, closed protocol instantiations,
handler definitions, custom-drop identities, resolved host-import descriptors,
principal runtime flags, and erased Core. The backend deterministically maps
them to bytecode records.

In particular:

- source `Use` becomes only validated ownership plus the legal
  `DUPLICABLE`/`ZERO_USE_ALLOWED` flags;
- lifetimes, regions, label/environment brands, trait evidence, and refinement
  facts do not serialize as runtime types;
- callable/handler/resumption/binding-pack opaque identities and capture layouts
  do serialize;
- `Available<E>` may appear only as erased nominal metadata and never a register;
- normalized protocol keys become `PROTOCOLS` entries;
- destruction plans become MIR cleanup maps and `DROP_GLUE` entries.

## 10. Determinism, caching, and failure behavior

### 10.1 Non-incremental G1 policy

G1 recompiles the whole concatenated standard-library/source bundle on every invocation. There is
no filesystem cache, dependency graph, revision number, or query invalidation
protocol. This is an explicit compactness and bootstrap decision, not an omitted
feature.

This batch policy does not prohibit the host-side editor session. The Rust
`IncrementalCompilerSession` reparses and resolves each supplied bundle, but reuses
an unchanged body's inferred products when both its body fingerprint and the
declaration-context fingerprint match. A failed request restores the previous
per-body cache. These results are an in-memory tooling optimization only and do not
change batch semantics or artifact identity.

Within one invocation, only queries with measured reuse are memoized. Cache keys
use canonical terms and never spans, addresses, hash seeds, or insertion order.
Body-local tables are cleared with the body scratch arena; global solver and
principal-type results survive until process exit.

### 10.2 Per-run caches

The mandatory global caches are symbol/resolved-term interning, alias/projection
normalization, trait-goal tables, principal `Use` intervals, and nominal variance.
Pattern compilation and open-environment checks use body-local memo tables only
after a repeated key is observed; public-interface fingerprints are debug-only.
Cache hits may alter performance only. Determinism tests compare normal builds
with caches disabled on bounded fixtures rather than doubling every release run.

### 10.3 Stable ordering and fingerprints

Lookup maps use open addressing and may iterate in arbitrary order. Traversals are
sorted only when they affect diagnostic priority or serialized output; allocation
IDs are not observable. Debug semantic fingerprints use a fixed bytewise hash and
exclude spans, absolute paths, metadata, and host-dependent values.

Primary diagnostics are sorted by bundle start byte, severity, and diagnostic
code. Segment paths are presentation metadata only. Notes retain proof-trace
order. Stage-2/stage-3 identity is
the final determinism oracle.

### 10.4 Complexity safeguards

In addition to solver limits, the frontend enforces configurable defaults of:

- 1,000,000 body AST nodes and 512 lexical nesting depth;
- 16,384 generic parameters or where-goals per declaration;
- 65,536 inference variables per callable;
- 1,000,000 CFG points per callable and 8,000,000 across one compilation;
- 4,096 pattern rows and 65,536 decision-DAG nodes per handler;
- 65,536 ledger entries per open environment;
- 4,096 distinct normalized protocol keys per effect row.

Limits are checked before allocation growth. Body limits apply to the current
reusable arena rather than reserving their maxima up front. Exceeding one is a
deterministic resource-complexity diagnostic, not a host panic or silently
incomplete proof. After 100 primary errors, the compiler stops checking new
bodies and renders the collected bundle.

### 10.5 Poisoning and diagnostic recovery

`Error` types and poisoned AST/Core nodes unify with anything only to suppress
cascades; they never establish trait, ownership, effect, or coherence evidence.
After a primary error, checking continues at declaration or independent-body
boundaries with a fresh flow state. It does not continue through an invalid move,
loan, environment transition, or resumption state because secondary ownership
diagnostics would be misleading.

The process returns a nonzero compiler status when any error exists. It emits no
partial bytecode, replaces no requested output, and never treats a complexity
limit as an internal error.

## 11. Diagnostics

Every diagnostic is structured as:

```text
code, severity, primary origin, message template, labels[], notes[]
```

Records use flat `(start,count)` ranges. Candidate and solver traces are rendered
directly into at most eight notes while the failure stack is live; the compiler
does not retain general proof trees or implement machine-applicable suggestions
in G1.

Required diagnostic families include syntax/fixity, namespace, type/kind,
candidate ambiguity, trait/coherence, lifetime/borrow, move/use, drop,
environment/post-state, label escape/destination, effect/coverage,
resumption/cancellation, refinement, and complexity.

Generated concepts are rendered in source terms:

- an environment is “the shared execution state for these blocks,” followed by
  labeled contributing captures;
- a post-environment mismatch lists places consumed or retained by each branch;
- a brand escape names the originating label/block and destination scope;
- a trait overflow prints the shortest repeated normalized goal;
- a binder error says the name is available only after the positive pattern
  result, not that an internal binder brand is absent;
- a cancellation error points to both the performance site and captured value
  whose zero-use path is forbidden.

Candidate diagnostics show at most eight detailed failures and summarize the
remainder. Repeating canonical goals are deduplicated while rendering.

## 12. Test oracles and acceptance cases

### 12.1 Stage-local oracles

- **Lexer/parser:** golden token and AST trees with spans; fuzzing requires
  progress, bounded recovery, and no host panic.
- **Fixity/resolution:** grouped-tree goldens; renaming a library control binding
  must have exactly the same compiler behavior; undeclared/mixed/nonassociative
  operators must reject deterministically.
- **Type/trait:** canonical goal/answer goldens; solver answers are compared with
  a slow depth-bounded reference enumerator on small generated impl databases.
- **Regions/loans:** accepted/rejected CFG fixtures compared with a simple
  point-set reference solver.
- **Use:** interval results compared with exhaustive path enumeration on finite
  acyclic CFGs and bounded unrollings.
- **Patterns:** decision DAG execution compared with source-order row matching for
  every generated closed enum value.
- **Environments:** sealed ledger/post-state snapshots with source names; linked
  call islands are tested under reordered internal hash insertion.
- **Typed Core:** snapshot tests and a structural assertion that prohibited nodes
  are unrepresentable.

### 12.2 Cross-stage oracles

- Run unoptimized Typed Core/MIR behavior against the AST evaluator only for
  compiler-accepted programs in its documented bootstrap subset. The evaluator
  is not an oracle for ownership disposition,
  cleanup, borrowing, or private-field authority.
- Compare MIR execution before and after evidence erasure and cleanup lowering.
- Compile with semantic caches on/off and randomized lookup-map seeds; artifacts
  and ordered diagnostics must match.
- Stage 2 compiling the compiler and standard library must produce the same bytes as stage
  3.
- In conformance mode, serialize and deserialize `AbstractInterface`; normalized
  relations must be identical and contain no local/place/binder identities.

### 12.3 Mandatory semantic tests

Acceptance includes positive and negative cases for:

- contextual blocks selected through arbitrarily named generic parameters and
  user-defined operators, plus eager-block and ambiguity cases;
- anonymous callable receiver synthesis and least-consuming receiver/access
  choice;
- shared open environments across two-way and incremental alternatives,
  sequential exact-linear rejection, unequal post-state rejection, and terminal
  branch joining;
- HRTB placeholder leaks, GAT projection equality, variance, reborrowing, NLL,
  drop checking, and label/environment escape;
- structural and explicit principal `Use`, branch hull, sequence addition,
  repetition/multiplication, must-move propagation, exhaustive deconstruction,
  private-field rejection, zero-use wildcard/omission checks, illegal implicit
  cleanup, and explicit zero-use destroy;
- custom drop order/restrictions and partial-move rejection;
- intrinsic `Label<T>` evidence, implicit function labels, mandatory
  control-inlining directness, and label-generic effects;
- total/partial deep handlers, terminal cleanup, one-shot resume, legal
  multi-shot resume, unique-capture rejection, and illegal cancellation;
- positive/negative `is` contexts, binder lifetime, tuple context composition,
  single subject evaluation, and refutable moving-test rejection;
- closed-world negative facts versus ordinary absence of positive evidence;
- no compiler-known behavior for standard-library control or operator names.

The rejection examples and all eighteen safety invariants in the core spec
are permanent compile-fail suites with stable diagnostic codes.

## 13. Level 5: implementable vertical slices

Each slice must end in a runnable source-to-Core path, stage-local tests, and no
placeholder “accept everything” proof. Later slices may extend arenas and goal
kinds but may not reinterpret earlier accepted programs.

### Slice 1: deterministic structural frontend

Implement source maps, declaration scanning, the reusable body parser,
spans/origins, arenas, interface collection, namespace resolution, flat operator
grouping, and diagnostic serialization.
Support nominal structs/enums, scalar/tuple/reference types, named direct
callables, locals, construction, projection, and direct calls. Emit minimal Typed
Core for pure unit/scalar programs.

Gate: parser/fixity goldens are stable; control-like names are demonstrably
ordinary; two identical invocations produce identical Core fingerprints.

### Slice 2: nominal generics and the trait kernel

Add generic type/lifetime/const binders, where clauses, traits, coherent impl
collection, orphan/overlap checks, canonical tables, associated types/effect rows,
GATs, HRTBs/universes/leak checking, and restricted negative impls. Add the
intrinsic manifest and lexical compiler evidence path.

Gate: small-model solver differential tests pass; ambiguity and overflow are
structured errors; no sealed trait can be implemented in source.

### Slice 3: callables and contextual elaboration

Add anonymous callable identities, capture discovery, `Fn` synthesis, receiver
selection, call islands, contextual trailing/operator blocks, effect-row
inference, and unit-environment `RunsIn`.

Gate: arbitrarily named selectors receive delayed blocks solely through their
constraints; ambiguous block interpretation rejects before body checking.

### Slice 4: places, lifetimes, and destruction

Add place/move paths, MIR-place CFG view, region inference, NLL loans,
reborrowing, variance, outlives/escape, principal and actual `Use`, explicit and
implicit destruction, `Drop` validation, dropck, and cleanup planning.

Gate: finite-CFG reference solvers agree; all ownership/drop rejection examples
pass with source-oriented diagnostics.

### Slice 5: branded environments and labels

Add open ledger formation across call islands, access selection, `After` states,
environment sealing, availability witnesses, generative label brands, direct
`Label<T>` evidence, implicit function destinations, direct `LEAVE` lowering,
and nonlocal cleanup.

Gate: generic simultaneous/incremental selectors compile from ordinary source;
sequential activation, post-state mismatch, forged availability, and escaping
labels reject.

### Slice 6: effects, handlers, and resumptions

Add effect declarations/rows, normalized protocol keys, handler literals,
pattern matrices, deep/partial coverage, terminal performance, continuation
capture, resumption quantities, resume/cancel checking, and label-generic effects.

Gate: effect semantics and cleanup agree with bytecode executed by `grvm`; one-shot,
multi-shot, terminal, partial, and cancellation suites pass.

### Slice 7: refinements and final Core boundary

Add `is`, binder keys, positive/negative environment brands, `Bindings` payloads,
closed negative facts, tuple context composition, complete decision-DAG lowering,
evidence erasure, abstract-interface serialization, and final Core validation.

Gate: no `is` or prohibited semantic control node remains; every Draft 0.1
frontend checklist item and required rejection example passes.

### Slice 8: bootstrap hardening

Profile and compact arenas, interners, solver tables, and diagnostics; enforce all
complexity limits; add cache-off determinism runs, fuzzers, and stage-2/stage-3
bootstrap tests. Keep compiler source within the established bootstrap subset
until the previous compiler generation can build each extension.

Gate: the finalized frontend participates in reproducible self-compilation within
the architecture's 120-second and 4096-MiB process limits.
