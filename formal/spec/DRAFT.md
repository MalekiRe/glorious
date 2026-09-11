# First complete drafting attempt and first check

The user requested that the full formal language specification be drafted
first, followed by checking and repair. All initial modules, the aggregate
contract, regression propositions and documentation were written before
the first `lake build`. This is a specification project, not a compiler
implementation or a library-algorithm verification project.

First check, 2026-09-11:

- `lake build` stopped in `Foundation` on one unused simplification argument
  because warnings are errors.
- After removing that argument, `Foundation` checked. Its quantity,
  table, finite-execution composition and observational-refinement proofs
  contain no admissions.
- The resumed full build failed in `Terms`, beginning with reserved names
  `universe`, `unsafe`, `private`, `public` and `namespace`. Subsequent error
  messages in that file are largely consequences of failed declarations.
- No downstream module or `Checks` has passed yet. No Stage0, self-hosted,
  VM/native or library test was run for this checkpoint.

This checkpoint preserves the full first attempt and its real failed gate.
It does not claim that the proposed relations are complete, nonvacuous,
sound, deterministic, or adequate for the whole language. The remaining
repair includes the source, storage, control, primitive and target-boundary
audits listed in `COVERAGE.md`; a clean Lean build alone will not settle them.

## First verified repair checkpoint

`lake build GloriousLanguage.BasicChecks GloriousLanguage.Instantiation`
passes (12 jobs), with warnings as errors and implicit creation of undeclared
identifiers disabled. This checks Foundation, Terms, Syntax, Target,
Declarations, Static, Storage, Kernel, SourceRules and Instantiation, plus
the new focused boundary propositions. The execution/elaboration aggregate
and its full `Checks` gate remain unchecked.

The repair separates positive, grounded import derivations from fixed-point
priority selection and proves selected declaration identity unique. An
unsupported capability now has no answer: every published principal must
satisfy an equation, including types containing abstract regions or brands.
Declarations and body instantiation share one kind-checked substitution
operation, with explicit capture rejection under quantified binders.
Storage replacement can restore a hole without changing its siblings, and
fresh allocation requires an aligned, non-overlapping physical extent.
The superseded raw-byte move relation was removed; the Memory module retains
the single typed/raw bulk-movement path and shares the allocation predicate.

These changes do not prove existence of capability models for every admitted
declaration closure, adequacy of import visibility/re-exports, or complete
static/runtime type correspondence. Those and the coverage audit remain real
obligations. Identifier migrations in downstream modules are not claims that
those modules check. No compiler or library acceptance suite was run.

## Execution-rule repair checkpoint

`lake build GloriousLanguage.BasicChecks GloriousLanguage.ExecutionChecks
GloriousLanguage.Contracts GloriousLanguage.ABI` passes (24 jobs).
The execution, memory, foreign, structural typing, contract and ABI definitions
now check. Source elaboration still fails at pattern-field inference and a
byte-literal conversion; downstream origins and the full aggregate are pending.

Pattern plans now publish separate shell, binding and postorder-cleanup
sequences. Handler operation and completion clauses use fresh local activations;
serviced frames retain their environment ownership and clause context. Clause
obligations are checked after cleanup, allowing optional cancellation while
preserving borrowed handler environments. Regression proofs check nested cleanup
order, active-token rejection, lent-environment return and foreign callback
barriers. Exact positive resumption cancellation remains formally excluded.
Handler effect subtraction requires complete operation/payload coverage.
Pattern test carriers place their binding pack exactly once.

This is still an incomplete specification: runtime generative type closure,
callable/control layouts, snapshot physical extents, source-origin threading,
and source/ABI adequacy require further repair. Binding packs are no longer
incorrectly erased as zero-byte proof values; their real field encoding still
needs integration. These checked definitions and local proofs are not a
type-soundness, complete-language, compiler or library-conformance result.

## First complete Lean check

`lake build` passes all 30 jobs, including `Elaboration`, `Origins`,
`Specification` and `Checks`. Recursive module elaboration and structural
constant lists now use explicit positive companion rules. Regression proofs
use the actual principal restriction relation and check both directions;
Unicode and quantity checks unfold their specified predicates.

This establishes a checked draft, not semantic completeness. In particular,
parameter patterns currently lack their executable binding prologue, call-site
typing uses the pre-argument context, and nested source origins are not threaded
through all expression rules. Those are actual integration defects, alongside
the runtime/target audit obligations above, and remain in the repair pass.

The earlier compiler draft is retained in `formal/lean` as reference. The
new specification does not import it. Unrelated Stage0 working-tree changes
were left untouched.

## Executable source bindings and ordinary origins

`lake build GloriousLanguage.SourceChecks` passes (24 jobs). Parameter
elaboration now returns an ordered pattern plan consumed by named and anonymous
function bodies. A checked theorem shows that the plan's formal list is exactly
the incoming parameter list. Call and tail-call typing use the context after
callee and argument evaluation. Closure contexts cannot invent ambient locals;
function bodies reset unsafe permission and establish their own signatures.
Named exits must be present for named functions and absent for anonymous ones.

Ordinary expression, argument, statement, clause and operation nesting now
threads AST child positions. Member inventories relate declarations in order,
and unnamed fields use forward source indices. Focused positive/negative checks
cover plan order, impossible empty-source parameters, capture-context authority,
argument locals and a closure nested in a block's call argument.

Synthetic operator regrouping still needs origin-preserving elaboration;
contextual capture alternatives, generic/default/associated inference and
handler continuation-pattern binding remain audit obligations. This checkpoint
does not claim complete source adequacy or update the runtime/target debt above.

## Shared representation boundary

`lake build GloriousLanguage.RepresentationChecks` passes (22 jobs, through
ABI). Callable and operation resident fields now share one instantiated relation
for capability, lifetime, layout and field addressing. Explicit target identity
layouts feed callable/continuation encoding; binding packs encode real fields.
C records use the selected target's layout function with checked placement;
fixed enums have real tag bytes and transparent wrappers have wrapper offsets.
Default enum tags use supported power-of-two widths. Unit C results are void,
without admitting unit as a C parameter. Sealed traits use the manifest's actual
relation inventory rather than requiring a fictitious runtime function binding.

Logical ownership places are distinct from machine addresses: label/environment
witnesses have no direct addressability rule, and shared ABI homes are required
for addressable residents. `TypeOutlives` now follows actual nominal fields and
callable captures; an unresolved rigid/projection is not justified merely because
it has no visible type children. Checks cover capture offsets, explicit control
layouts, C layout identity and rejection of an unsupported three-byte enum tag.

Runtime lexical-to-generative type instantiation, physical snapshot relocation,
generic normalization and complete target/control-site coverage remain open.
The new target layout obligations are specifications, not implemented runtimes.

## Physical snapshots and complete abandoned-region cleanup

`lake build` passes all 32 jobs. Snapshot maps now assign checked, disjoint
physical extents and rebase provenance-carrying internal pointers with the same
map. Address-only integers and pointers into unselected storage remain unchanged.
World well-formedness checks live-region bounds, alignment and disjoint extents.
Replay excludes unique loans into copied storage, even when the unique handle is
outside the snapshot. Loan copies follow actual copied handles, avoiding phantom
copied loans for external handles; copied parent links are restricted to copied
loans. Region selection includes empty captured control scopes, not just roots.

Frame-owned regions are shared by terminal-effect, label-leave and cancellation
cleanup. Tail-frame stripping returns every intervening scope region, and the
execution path closes them after owner cleanup. Regression propositions check
pointer provenance cases, physical rebasing, nested-tail region order and
deduplicated region closure. The complete full-build checkpoint includes the
previous source and representation checks.

This still does not prove snapshot simulation, global preservation/progress,
or complete replayable-control coverage. In particular, the conservative
label-frame replay restriction and lexical-to-runtime generative type closure
remain actual adequacy work, not completed metatheorems.

## Runtime scope instantiation

`lake build` passes all 32 jobs. Lexical rigid names and concrete runtime
regions/brands now have separate term constructors. Runtime brands distinguish
labels, resumptions and proof tokens even when their numeric identities match.
One scope-instantiation operation closes allocation types, atoms, invocation
signatures, pattern bindings, handler captures and selected clause headers.
Scope entry, named exits, labels, resumptions and proof-producing control rules
bind their fresh identities through that operation. The old runtime label-only
table is removed. A theorem proves scope instantiation preserves term kind.

Borrow and label operands are terms, so ordinary generic instantiation reaches
them. Borrow execution uses the stated concrete region, not the innermost
allocation region; captured references likewise use their own region. Runtime
value typing checks reference regions against loans and separates control-token
brands. Snapshot relocation changes concrete regions and their scope mappings,
never lexical binders. Source borrowing now consumes the current lexical scope
instead of guessing an unrelated region. Focused propositions cover namespace
separation, concrete-identity stability, closed runtime regions, relocation and
rejection of unresolved lexical operands in executable atom rules.

This completes an execution-boundary repair, not the whole generative-typing
obligation. Anonymous closure elaboration still needs hidden region/brand
arguments through the existing `Instantiates` relation and a fresh body scope;
source continuation-pattern binding and proof-carrier type derivation are also
incomplete. Runtime control authority, full snapshot simulation, source
nonvacuity and global preservation/progress remain unproved. No compiler or
library code or acceptance tests were changed or run.

## Closure instances and continuation binding

`lake build` passes all 32 jobs. Closure elaboration now publishes its actual
type arguments and checks the corresponding ordinary `Instance`. Every source
closure construction stores those arguments in its callable type and atom;
runtime instantiation uses them for the signature, capture fields and body.
The empty-argument-only source path is removed. A checked theorem extracts the
same instance from every successful closure elaboration. A regression follows
a captured reference region through the capture type, signature and executable
borrow, including a numerically colliding callee-local region.

All functions now declare their lexical activation-region binder. The source
function context, named-exit type, structural typing and runtime entry consume
that binder; anonymous bodies no longer inherit an unbound caller region.
Handler continuation patterns use the ordinary executable parameter prologue,
so their source bindings are introduced by execution. Structural operation-arm
typing requires the lexical brand that clause entry actually instantiates.

The remaining source audit still includes implicit capture discovery (notably
ambient label names), correlated capture alternatives, polymorphic anonymous
heads, generic/default inference and proof-carrier types. No theorem here proves
that every legal source closure has an elaboration, or that every generated
instance satisfies semantic admission. Constructive nonvacuity, control-state
authority, snapshot simulation and global soundness remain open.
