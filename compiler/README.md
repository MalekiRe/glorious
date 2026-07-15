# Grandiose LLVM compiler

This is a standalone Grandiose project (`grandiose.toml`) whose compiler source
is itself Grandiose. It uses the `Files` and `Console` algebraic effects for all
observable I/O, so a future in-language handler can redirect or pipe the same
operations without changing the compiler pipeline.

The current bootstrap stage accepts modules of `i32` and `i64` callables with
parameters, calls, and arithmetic expressions:

```gr
main() -> i64 {
    2 + 5 * 8
}
```

It supports signed integer literals, parameter references, calls, unary
negation, parentheses, and left-associative `*`, `/`, `+`, and `-` precedence.
`String` is a canonical scalar source type. String literals decode the same
Unicode contents and `\\n`, `\\r`, `\\t`, `\\\"`, and `\\\\` escapes as the
interpreter, then lower to private UTF-8 LLVM byte globals passed through the
pointer ABI. Malformed and unfinished literals produce compiler-authored
source diagnostics. Unit-returning callable and effect declarations may omit
the result after `->`, matching the interpreter's `-> { ... }`, `-> / {...}`,
and `->;` forms.
Source scalar types and their spans are retained in the compiler's nominal AST.
Order-independent `type Name = Target;` aliases are resolved after parsing,
with diagnostics for unknown, duplicate, and cyclic names. The compiler
resolves callables and parameters, checks call arity and expression types,
performs type-directed literal range checking, and lowers matching `i32`/`i64`
LLVM signatures and instructions rather than evaluating source expressions in
the interpreter.

Nominal `struct` declarations and named construction are also supported.
Field coverage, duplicate/unknown names, and field expression types are checked
before lowering. LLVM output contains corresponding aggregate declarations and
uses `insertvalue` to construct values in declaration layout order, regardless
of the source initializer order; structs may be passed to and returned from
Grandiose callables by value. Postfix field projection is checked against the
nominal declaration and lowered with LLVM `extractvalue`; projection supports
parameters, call results, constructed values, and chained projections whose
types are intrinsically determined.

Nominal `enum` declarations support payloadless and payload-carrying variants,
qualified construction such as `Message::Move(40, 2)`, aliases, and by-value
call/return ABI. The bootstrap LLVM layout is a tag followed by
declaration-ordered typed payload slots for every variant; inactive slots are
`undef`. This preserves complete payload semantics while leaving compact union
layout as an independent backend optimization.

Callable bodies and nested expressions are typed lexical blocks. They support
both annotated `let name: Type = value;` bindings and inferred
`let name = value;` bindings. Unconstrained integer locals default to `i64`;
otherwise the initializer supplies the local's resolved type before ownership,
effect, and LLVM validation. Blocks reject duplicate names in one lexical
environment and lower locals directly to LLVM SSA values—including nominal
aggregate values.

Generic enums, structs, aliases, and callables retain their type parameters in
the compiler AST. Applied types are recursively resolved with arity checking;
generic aliases are substituted, concrete nominal layouts are monomorphized,
and generic callable invocations infer substitutions from result and argument
types before emitting specialized LLVM functions. Consequently the ordinary
prelude equations `Option<T> = Result<T, ()>` and `Bool = Option<()>` compile as
source declarations rather than compiler-known boolean types.

Module-scope immutable `let` bindings use value-restricted generalization.
Constructor values such as `let None = Result::Err(());` retain the unbound
enum parameter as a polymorphic scheme, and each value use is contextually
instantiated through the ordinary generic-call machinery. The LLVM backend
elaborates such bindings to hidden zero-argument definitions, preserving the
same ownership and monomorphization rules as other typed values without
special-casing `None`, `true`, or `false`.

Generic parameters constrained by `Fn<(), Output = R>` contextually elaborate
argument blocks into closures. LLVM lowering emits a `{ptr, ptr, ptr}` callable
value containing its function, lexical-capture environment, and drop glue, plus
a per-block thunk and an indirect call from the specialized higher-order
function. A block in any non-callable
context remains an immediately evaluated value, so this is expected-type
elaboration rather than a universal block coercion. Generic type-parameter
context is preserved through nested expression and block parsing, including
typed locals, and specialization substitutes those local annotations before
validation and LLVM lowering.

Concrete `Fn` bindings also retain whether invocation uses the ordinary value
ABI or the `%grandiose.effect_step` ABI. Creating either closure is pure; only
invoking the latter suspends. That evidence participates in specialization
mangling and follows forwarded callback values, so a higher-order function is
step-valued exactly when its selected callback specialization can suspend.
Effect obligations likewise compose with the callback's transitive invocation
interval: constructing or forwarding a delayed block does not perform its
effects, an unused `[0,0]` callback contributes none, and every possibly invoked
callback body must be admitted by the caller's effect row or handled there.
Terminal case handlers lower clause bodies to a common effect-step join when
needed. Consequently the entirely source-defined
`if(condition) { body } else { fallback }` form works with pure branches,
effectful success branches, and effectful fallback branches without a
compiler-known conditional node.

The first `RunsIn` ownership check composes callback invocation intervals with
the use interval of captured resumptions. A lazy selector that invokes a body
on only one alternative contributes `[0,1]`; a function that invokes its `Fn`
parameter twice contributes `[2,2]`. This prevents a syntactically single
`resume(k, value)` inside a callback from evading the operation's dynamic
quantity merely because the receiving higher-order function invokes that
callback repeatedly. Invocation evidence follows callback values through
higher-order forwarding calls, so `relay(body)` inherits the use interval of
the eventual receiver. A recursive forwarding cycle is conservatively assigned
`[0,infinity]` instead of being treated as unused or recursing in the compiler.
When one selector receives several callbacks together, their use intervals are
substituted into the selector body jointly: mutually exclusive handler branches
join, while sequential callback calls add. Thus two alternatives that each
capture one exact-linear resumption derive `[1,1]`, not the false independent
approximation `[0,2]`.

That correlated evidence now reaches the runtime representation as well. A
lexical handler whose mutually exclusive `Fn` alternatives capture its
resumption is lowered through the same heap-owned first-class handle used by
outward handlers. Both closures begin from one incoming environment identity,
the selector invokes exactly one, and the selected continuation establishes
the shared normal post-environment. There is no separate static-only resume
syntax once a resumption escapes into a closure.

Nominal structs and enums may declare a restricted principal owned-use interval
with `impl Use<[lower, upper]> for Type {}`. The compiler derives structural
capability by intersecting every field and possible variant payload, rejects a
manual implementation that widens that capability, and checks parameters and
annotated locals path-sensitively. Sequential uses add; mutually exclusive
handler branches join; delayed `Fn` bodies are multiplied by their transitive
invocation intervals; and several callbacks passed to one selector retain their
correlation. Thus one exact-linear value may be consumed in either of two
exclusive branches, while an unused `[1,1]` value and a duplicated `[0,1]`
value receive structured ownership diagnostics.

Explicit destruction is represented by a compiler-only `Destroy` expression
and exposed through the injected generic `destroy(value)` callable. It counts
as exactly one ordinary owned use, so it satisfies an exact-linear obligation
while repeated destruction is rejected by the same path-sensitive interval
checker. LLVM lowering destroys struct fields in reverse declaration order and
destroys only the active enum variant's payloads, also in reverse order, while
recursively invoking capture-specific closure drop glue. Closure values carry
function, environment, and drop pointers. Capturing environments are heap-owned
and their drop glue releases both captured values and storage. Values that may
be consumed on only some paths use a shared, reference-counted ownership cell:
moves claim the cell, alternative closures retain the same cell, and the final
owner performs destruction exactly once. Callable storage itself is affine
even though invoking an `Fn` does not consume it. Affine parameters and locals
receive implicit reverse-order cleanup at normal lexical scope exit. Generic struct and enum
constructors are contextually specialized from their expected nominal type,
including closures stored in generic fields and payloads; this keeps
construction, monomorphization, closure emission, and destruction on one
concrete layout.

Source-defined `impl Drop for T { drop(&mut self) -> { ... } }` hooks are
validated independently from principal `Use`: the target must be nominal and
support `[1,1]`, implementations are coherent, outward effects and suspension
are rejected, and non-unrestricted fields cannot be partially moved. Effects
handled completely inside the hook remain legal. LLVM lowering invokes the
hook exactly once through unique access before reverse structural destruction;
this applies to explicit `destroy` and implicit zero-use lexical cleanup, and
hook bodies participate in generic specialization and closure emission.
Effectful parameters, locals, and suspension-result bindings use the same
ownership cells. A generic `%grandiose.effect_step` cleanup wrapper retains
their capture environment until completion, deep resumption, or cancellation;
shared continuation environments carry a destructor callback and release
captures on their final reference. Destructible operation arguments transfer
ownership through request storage: handler bindings receive a fresh ownership
cell, non-binding patterns destroy the payload value, and destructible values
returned by resumption are owned by the continuation-result binding. Nested
variant patterns transfer bound fields into independent cells and destroy only
the unbound structural remainder in reverse order. Restricted field bindings
from a custom-`Drop` value are rejected because its hook requires the complete
value. Cleanup is no longer decided independently at each LLVM emission site.
Explicit `destroy`, nested pattern remainders, lexical locals, callable
parameters, closure captures, and effect-owner state releases first produce a
typed `OwnershipPlan`. Its guarded `OwnershipDestroyProjection` and
`OwnershipReleaseState` actions are then lowered into projection, destruction,
and drop-state instructions. This is the first ownership-MIR slice used by the
backend: ordinary return and nonlocal continuation drop now converge on the same
cleanup glue.

Shared `&T` and unique `&mut T` references are parsed and checked as distinct
source types, lower to LLVM pointers, and have principal use intervals
`[0,infinity]` and `[0,1]` respectively. Prefix borrowing requires a place and
prefix `*` dereferences a reference. Reborrowing preserves the original LLVM
pointer rather than materializing a snapshot: `&*reference` accepts either
reference kind, while `&mut *reference` requires unique input. The initial
nonlexical-loan pass ends a loan after its reference binding's final use,
permits overlapping shared loans, rejects incompatible overlaps and direct
access during a live unique loan, follows reference-valued immediate blocks,
validates nested lexical blocks, and prevents references into call- or
block-local storage from escaping. Typed `PlaceProvenance` records the root,
projection, and parent-reference edge of each place. A unique child reborrow
temporarily suspends its parent reference, while nonlexical final-use analysis
restores parent access once the child ends. Reference-returning callables also
receive a recursive provenance summary identifying which input reference is
returned; transparent forwarding calls substitute the corresponding caller
argument, preventing an identity helper from laundering a call-local borrow.
Full variance, branch-sensitive loan joins, general higher-order provenance,
and explicit lifetime relations remain follow-on work.

Generic callables may request the same evidence with
`where E: Use<[lower, upper]>`. The constraint is checked both inside the
generic body and against each concrete specialization. `Available<E>` is a
distinct compiler-intrinsic zero-sized type rather than an alias for `()`;
structural type equality keeps the two separate even though both erase to an
empty LLVM value. The intrinsic `available_to_unit` consumes only an
`Available<E>` whose concrete environment proves `Use<[0,0]>`. Exact-linear
environments and arbitrary zero-sized values are rejected with structured
diagnostics. Source cannot construct an availability witness; producing one
is restricted to the compiler intrinsics `defer_available` and
`continue_available`. The former preserves an unopened `RunsIn` transition and
returns its fresh incoming-environment witness; the latter consumes that
witness and invokes the next transition. Their closures retain the ordinary
principal-use accounting, so deferral contributes zero executions and
continuation contributes one. The `Available` type identity itself is reserved, and direct
construction, aliasing over the intrinsic name, or substitution with another
zero-sized type is rejected before LLVM lowering.

The constraint parser also accepts compiler-sealed environment relations:
`E: Environment` and `F: RunsIn<E, (), After = S>`. A RunsIn relation must
refine an existing `Fn` constraint, and both its incoming and normal-return
identities must be declared environments. At each generic call, unresolved
environment parameters receive fresh call-site-specific nominal brands; the
incoming and post-environment brands are distinct static types and participate
in specialization identity while contributing no runtime ABI value. Correlated
exact-linear callback alternatives can therefore compile under one shared
incoming brand and one shared declared post-environment rather than merely
carrying an untyped interval calculation.

Integer `==`, `!=`, `<`, `<=`, `>`, and `>=` comparisons lower through LLVM `icmp`, but their
source result is the monomorphized `Bool` alias (`Result<(), ()>`), constructed
as `Ok(())` or `Err(())`. LLVM `i1` remains only a backend branch/select value;
it is not exposed as a Grandiose source type.

Terminal case effects provide general nominal enum elimination. A direct
`handle perform Case::inspect(value) { ... }` is checked for operation arity,
variant identity, payload types, binding scope, overlap, and exhaustiveness,
then lowers to an LLVM `switch`, typed payload extraction, and a merge `phi`.
Clauses sharing an outer enum tag form an ordered payload decision chain:
integer and recursively nested variant patterns lower to guarded LLVM branches,
bindings are introduced only on the selected edge, and each tag requires a
final irrefutable payload clause. The same decision plan produces ordinary
values and `%grandiose.effect_step` results.
Using that mechanism, generic `if` and `else` are ordinary source functions;
source-declared right-associative word fixity gives callers the direct
`if(condition) { success } else { fallback }` surface form without a
compiler-known conditional expression.

Callable declarations retain normalized nominal effect-row entries, including
generic protocol applications such as `Fail<Error>`. The frontend validates
effect existence, generic arity, and duplicate row keys. It also substitutes
generic call bindings through callee rows and rejects every `perform` or
effectful call whose normalized protocol key is neither declared outward nor
removed by an exhaustive handler. Effect operation
declarations retain their resumption interval (`[lower, upper]`, with `infinity` for
an unbounded upper limit), reject quantities on terminal `!` operations, and
handler clauses retain an optional explicit `with k` resumption binding. The
Rust interpreter already executes these bindings as quantity-checked delimited
continuations: `resume(k, value)` deeply reinstalls the handler (and replays it
for multi-shot quantities), while `cancel(k)` destroys the remaining
computation only after the declared lower bound is met. The compiler assigns
each `with k` a typed `Resumption<OperationResult, HandlerResult>`, infers its
use interval, and rejects clauses outside the operation's declared quantity.
The LLVM backend now reifies lexical block suffixes as deep continuations and
executes one-shot, bounded multi-shot, and cancellation examples natively.
Effectful LLVM functions now use the first slice of the runtime CPS ABI: they
return a `%grandiose.effect_step` containing either a boxed completed value or
a suspended nominal effect request with a replayable continuation. Direct
effectful tail calls forward that step unchanged across function boundaries.
Non-tail calls compose a heap-owned, capture-bearing suffix onto the request,
and a recursive runtime dispatcher can handle and deeply resume requests
originating in another function. Operation arguments are lowered into typed,
heap-owned request payloads and unpacked into ordinary handler pattern bindings.
Generated recursive dispatcher functions return resumed values to ordinary
handler-clause blocks, including native cross-call multi-shot binding and
cancellation. Resumptions also compose directly through scalar arithmetic,
comparisons, negation, ordinary callable arguments, struct fields, enum
payloads, and projections. Generated handlers release consumed completion boxes
and typed request payload storage. Handler clauses may contain nested handled
cross-call computations; synthetic resumption binders participate in inference
but are erased from nested dispatcher signatures. Runtime resumptive clauses
perform ordered scalar-literal and recursive nominal enum-tag tests before
irrefutable fallbacks. Inactive nested variant payloads are frozen before tests,
preventing LLVM poison from entering non-selected decision paths. Complete
enum-variant sets are accepted as exhaustive without a
catch-all clause. Effectful pattern handlers use the same ordered dispatcher:
an exhaustive set removes its protocol, while a partial set retains the
protocol in the callable effect row and forwards uncovered requests. Effectful
handlers preserve outward protocols by returning
step values: unmatched requests receive wrapper resumptions that deeply
reinstall the inner handler after an outer handler resumes them. Effectful
callable blocks lower recursively into continuation functions, so pure prefixes,
discarded suspensions, multiple effectful bindings, and intervening locals are
preserved across arbitrary statement-level suspension points. Binary operands,
ordinary call arguments, and effect-operation arguments also CPS-normalize
left-to-right when they suspend, including effectful struct fields and enum
payloads. Forwarding clauses receive first-class heap-owned resumption handles
rather than backend-special resume syntax. A handle carries the deep resume
function, continuation environment, cancellation hook, remaining quantity,
active bit, and shared ownership count. Consequently a clause can resume the
same bounded continuation repeatedly, discard unused capacity, cancel
explicitly, and place ordinary effectful computations between resumptions. A
generic step finalizer carries handle ownership across newly forwarded requests
and releases or cancels the underlying continuation exactly when the clause
finishes or is dropped. Declared finite resumption quantities travel in effect
steps. Shared capture environments support multi-shot resumptions, and wrapper,
bind, finalizer, and capture frames are released after their final use or
explicit cancellation. The lexical path is the statically eliminated form of
this ABI, not a separate semantics. Resumptive handlers can transform any
step-valued computation, not only a direct call or an explicitly written block:
binary expressions and other recursively normalized forms enter continuation
MIR first and then pass through the same deep forwarding-handler transform.
Lexical block handlers retain static elimination when every clause is
irrefutable; ordered integer or nested nominal patterns instead use the shared
runtime decision tree, so an earlier refutable clause cannot be skipped in
favor of its fallback. That choice is represented by a typed
`ResumptiveHandlerControlPlan` with static-block, direct-runtime-call, and
general-runtime-step variants. Expression lowering and ahead-of-time helper
definition generation consume the same plan, preventing their control-flow
decisions from drifting apart.

It emits valid textual LLVM IR with a native `main` wrapper. Token kinds, token
spans, lexical dispatch, the fixed-grammar parser, parsed nodes, range checks,
and LLVM module construction are implemented in `src/main.gr`. The interpreter
exposes only syntax-agnostic character-class, string-slice, list, and integer
machine primitives at this bootstrap stage; it has no knowledge of Grandiose
keywords or declaration grammar.

The compiler already uses nominal structs and enums for source files, spans,
tokens, diagnostics, parsed nodes, and compilation products. Its `Bool` is the
ordinary alias `Result<(), ()>`; `if`, `else`, `and`, `or`, and `not` are
source-defined Result operators. Callable-constrained trailing blocks provide
the direct `if(condition) { ... } else { ... }` form. Pattern-bearing
`ResultCase`, `CharacterCase`, and `TokenCase` handlers perform control and
dispatch. There is no interpreter-known `if` or `match` operation.

Validated expressions now begin crossing the backend boundary as
`TypedCoreExpression` values carrying the source expression, its fully resolved
type, whether evaluation can produce an effect step, and whether it denotes a
stable borrowable place. Borrow validation and reference lowering consume the
same value-category fact, while contextual reference types preserve the
specific `GRC1860` diagnostic for untyped temporaries. Effectful block
lowering, callable specialization, callable-body lowering, and helper-definition
discovery consume that shared fact instead of independently repeating type and
suspension queries. Together with `OwnershipPlan` and
`ResumptiveHandlerControlPlan`, this forms the initial Typed Core/control-MIR
spine while the remaining expression forms are migrated incrementally.

Frontend failures are performed through the terminal `Diagnostics::abort`
effect. Its payload includes the input path, complete source, byte span, title,
message, and help. The CLI host renders it with Ariadne, while another handler
can capture or pipe the same structured diagnostic without changing the
compiler frontend.

`CompilerDiagnostic` is a Grandiose nominal value carrying severity, stable
error code, source file, primary and secondary labels, note, and help. Errors
use terminal `Diagnostics::abort`; warnings and advice use resumptive
`Diagnostics::report`, allowing compilation to continue. The Rust bootstrap
runtime only decodes this value and renders it—it does not choose compiler
messages or spans.

The next stages are:

1. extend the initial reference and nonlexical-loan implementation with
   variance, branch-sensitive loan joins, interprocedural reference provenance,
   explicit lifetime relations, and drop checking;
2. extend conditional ownership transport through the remaining uncommon
   nonlocal MIR edges;
3. finish the remaining general continuation-MIR cases currently diagnosed as
   backend coverage gaps;
4. consolidate the validated representation into explicit Typed Core and
   ownership/control MIR rather than lowering several frontend forms directly;
5. continue expanding Ariadne snapshots as the lifetime, cleanup, and backend
   layers gain diagnostics;
6. expose LLVM object emission through a handled backend effect.

Run and validate the bootstrap compiler from the repository root:

```sh
./compiler/grc compiler/examples/exit.gr /tmp/exit.ll
llvm-as /tmp/exit.ll -o /tmp/exit.bc
lli /tmp/exit.bc
test $? -eq 42
./compiler/tests/diagnostics.sh
./compiler/tests/e2e.sh
```

`compiler/grc` builds and runs the Rust bootstrap interpreter with Cargo's
optimized release profile. This keeps interpreter changes automatically fresh
while making repeated self-hosted compiler invocations substantially faster.
The bootstrap runtime stores immutable strings, lists, nominal values, lexical
environments, closures, recursive AST edges, handler clauses, and expression
collections with structural sharing. Large compiler inputs therefore retain
language-level effects and source-defined control flow without quadratic
container or syntax-tree cloning.
