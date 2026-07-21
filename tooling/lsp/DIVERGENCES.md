# Vendored frontend divergences

`src/frontend/` is a copy of `crates/grandiose/src/{span,diagnostic,lexer,ast,
parser,validate,source_bundle}.rs` + `distributed_std.gr`, taken 2026-07-19,
with `crate::` rewritten to `crate::frontend::`. The original is owned by the
compiler effort; this copy exists so the LSP can iterate without touching it.
When the compiler stabilizes, reconcile by diffing against origin — every
deliberate divergence must be listed here.

| # | Files | Divergence | Reconciliation |
|---|-------|-----------|----------------|
| 1 | all | `crate::` → `crate::frontend::` path rewrite | mechanical sed |
| 2 | mod.rs | `#[allow(dead_code)]` on module decls (LSP uses lex/parse/validate, not eval) | drop when merged back |
| 3 | parser.rs | Resilient parsing: `parse_resilient()` entry point, `Draft` accumulator extracted from `program()` (behavior-preserving refactor), `program_resilient()` + `synchronize()` for multi-error recovery at declaration boundaries | offer upstream — batch compiler could reuse it for its 100-error cap; else keep as LSP-only |

Refresh procedure (until reconciliation):
```
cd crates/grandiose/src
for f in span.rs diagnostic.rs lexer.rs ast.rs parser.rs validate.rs source_bundle.rs; do
  sed 's/crate::/crate::frontend::/g' "$f" > ../../../tooling/lsp/src/frontend/"$f"
done
cp distributed_std.gr ../../../tooling/lsp/src/frontend/
```
then re-apply any rows above that touch file bodies (currently none).
