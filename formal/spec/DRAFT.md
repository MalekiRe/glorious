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

The earlier compiler draft is retained in `formal/lean` as reference. The
new specification does not import it. Unrelated Stage0 working-tree changes
were left untouched.
