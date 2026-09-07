# Call-context lifetime inference

The source-only reproduction below previously failed specialization with
`G7032` / `NonConcreteType`, even though neither the entry point nor its
runtime marker layout is generic:

```glorious
struct Marker<'a, 'b> {}
fn carry<T>(value: T) -> T { value }
fn inspect<'a, 'b>(value: &Marker<'a, 'b>) -> i64 { 42 }
pub fn main() -> i64 {
    let marker = carry(Marker {});
    inspect(&marker)
}
```

The later call's provisional argument unification assigned its declaration
regions to still-open constructor lifetime holes. The earlier `carry` type
application shared those holes and consequently retained `Lifetime::Generic`
arguments instead of a closed specialization. Omitting the later call or
explicitly constructing `Marker<'static, 'static> {}` avoided the failure.

## Boundaries preserved by the fix

Contextual argument inference now opens the complete parameter pack into
caller-local holes, sharing one hole for repeated regions across operands.
Those provisional types do not replace the callee's original declaration
contract. The final call still derives reference provenance from that contract
and jointly checks actual argument lifetimes. Callable-bound lookup also uses
the declaration parameter, not a freshened substitute.

When an actual caller lifetime remains an inference hole, it can open a callee
generic or applicable higher-ranked binder. The application retains the caller
hole until ordinary body inference seals it; alignment does not write the
callee's region name back into that hole. Rigid/static lifetime checks, unique
referent invariance, and concrete-instance validation are not relaxed.

A higher-ranked execution regression also exposed a separate layout-boundary
bug. A callable parameter/result was extracted as a standalone nominal layout
obligation while still referring to the removed callable binder. Layout
collection now applies the existing body-region opening operation at that
boundary only. The original callable keeps its complete higher-ranked type and
source contract. Nested binders remain bound, and genuinely detached/unapplied
regions still fail Specialized MIR validation.

## Executed regressions

Five new lifetime-suite tests cover four successful decoded/verified ordinary
executions: the delayed `carry` instance, two unconstrained operands sharing a
region, named caller regions nested in a type argument, and an actual
higher-ranked callback. The fifth test checks four rejection cases: lengthening
to static, merging rigid caller regions, changing a unique referent's lifetime,
and supplying a static-only callback where every lifetime is required.
Two unit tests check detached layout opening and nested-binder preservation
without weakening the closed-type validator. The original native nominal-field
lifetime/linking regression now passes as well; all 28 native-bridge tests pass.

The lifetime fixtures now explicitly load/import the canonical source library
for their operator cases. A fresh pre-fix run with those same corrected
fixtures has 12 passes and five failures
(`target/context-regions-clean-fixture-baseline.log`). Three of those failures
are the newly added positive regressions. The other two are reproduced with
identical diagnostics before and after this fix:

- `multi_source_reference_carriers_preserve_loans_through_moves_and_reborrows`:
  `G5006`, reborrow conflicts with a live child loan.
- `destructor_owned_loans_remain_live_until_the_owner_is_destroyed`:
  its plain-reference control reaches `G7041`, addressable storage replacement
  while a unique loan remains live in Runtime MIR.

Both remain enabled and failing. They require ownership/loan-ending work, not
accepting unclosed lifetime arguments or weakening the tested borrow contract.

The final selected authoring run (`target/context-regions-final-authoring.log`)
has 1,095 passes and 15 failures: 218 unit, 256 Core, 109 destruction, 15 lifetime,
28 native-bridge, 19 runtime-memory, four runtime-storage, 81 signature,
171 standard-library, 28 type, and 166 VM passes. The failures are the eight
previously recorded Core, two destruction, three VM, and two baseline-confirmed
lifetime cases. This is not a full workspace pass, M1 certification, or a
self-host/bootstrap completion claim.

The full source gate passes all 56 tests in 399.31 seconds
(`target/compiler-check/run-mg43ga9e/report.json`). Its 58 records retain the
existing 12 workers and resource guards and `release_ready: false`. All 32
profiled executions finish with zero raw/home live bytes and unsaturated
counters; the 26 unprofiled records keep native fields empty. The source-copy
batch preserves its previous artifact digest, 33-frame depth, 45,161-byte
combined backing peak, and logical work/allocation measurements.
The original source-only CLI reproduction now returns `42`
(`target/context-regions-minimized-fixed.log`).
