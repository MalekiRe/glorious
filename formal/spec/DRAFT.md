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

The earlier compiler draft is retained in `formal/lean` as reference. The
new specification does not import it. Unrelated Stage0 working-tree changes
were left untouched.
