# Whole-compiler mandatory-proof attempt

The user's clarified request is a compiler proved to preserve the language's
semantics, not merely a compiler implemented in Lean. The first end-to-end
proof-bearing draft was wired into the real entry points before its first
build. It is an attempted proof and is **not yet a verified compiler**.

`Proof/Behavior`, `Static`, `Resources`, `Operational`, `Elaboration`, `Source`,
`Target`, and `Passes` define the proposed judgments and mandatory certificates.
`compileParsed` now returns a request-indexed `CompileOutput` requiring the
preparation, elaboration, transformation, analysis, and lowering proofs. The
driver's incremental parser and `compileSources` require parsing certificates.
Both use `parseOneFile`; the driver's duplicate parser invocation is removed.
No unchecked alternate compiler path or admitted theorem is supplied.

The first repair pass made the seven specification modules build, including
the trace-composition, invariant, and basic move/copy/loan lemmas. The general
phase theorems in `Proof/Passes` still fail, so the public compiler does not
build. Several proposed specifications also
remain incomplete: the source grammar does not yet cover all declarations or
expressions; target instruction rules do not yet cover all emitted operations;
cleanup records plans but does not yet schedule the source Drop bodies; and
the observer relation still needs a coherent memory-injection treatment.
Those are semantic defects in this proof attempt, not exclusions from the
requested guarantee. The draft must not be presented as complete or as proven
merely because the executable now has proof fields.

The initial end-to-end draft has been written before running a build or a test,
as requested. This is an implementation draft, not a verified checkpoint or a
claim of full language/standard-library conformance. The existing specification
and compiler architecture contract remain normative. The separate, previously
checked Quantity/Control/Cleanup/Effects kernels are not proofs of this new code.

The executable path is `Main` → `Driver` → `Compiler.compileParsed`:

1. Read the supplied package roots and only their parsed, declared module closure.
2. Decode/lex/parse source, resolve modules/imports/declarations and type terms.
3. Bind the supplied runtime manifest to exact declaration identities and ABI
   contracts; validate coherence and elaborate typed Core.
4. Specialize runtime demands and transform structurally available control code.
5. Analyze control, storage, loans, captures, cleanup, effects and resumption.
6. Lower the analyzed program to VM types/instructions and interface metadata.
7. Send those tables to the existing VM verifier and codec through the small
   `assemble_semantic_artifact` bridge. Verify both fresh and decoded artifacts
   before publishing the output. The bridge has no Stage0 dependency.

## Draft inventory

`Semantics/Model`, `Normalize`, `Traits`, `Resolve`, `Patterns`, `Core`,
`Storage`, `Layout`, `Scalar`, `Memory`, `Elaborate`, `Analyze`, `Specialize`,
`Transform`, `VM`, `Lower`, `Lexer`, `Parser`, `Manifest`, `Compiler`, `Driver`
and `Main` contain the first-pass implementation. The library and executable
are both wired into Lake. Every module is intended to be on the compiler path;
there is no separate source checker supplying unchecked success to lowering.

## Repair phase

The earlier, unchecked implementation was repaired until all 57 Lake build
targets passed. Its first generated unit program failed receiving verification
by overwriting a live register; that regression remains an acceptance failure.
The new mandatory-proof build reaches the phase theorems and fails on actual
unsolved goals; increasing tactic limits or accepting missing proofs is not a
repair. After proof and specification errors are repaired, focused source and receiving-boundary checks must expose
and repair semantic integration gaps. Known draft debts include unresolved and
associated declaration forms, generic runtime authority, capture/receiver binding,
guarded recursion, NLL evidence transport, completion handlers, continuation
obligations, physical cleanup/reference metadata and register allocation.

Fail-closed diagnostics in this draft do not count as implementing valid source
features. Replacing a missing semantic proof with success, changing the language,
or deleting a discovered failing regression is not an acceptable repair.

The driver supports a JSON request manifest, explicit dependency roots and a
VM64/no-runtime-authority default. `--emit-json` produces receiving IR only; it
does not claim that the independently verified artifact gate passed. Normal
output needs the codec bridge built with Cargo. Exact CLI/build instructions and
acceptance results will be updated after they have actually been checked.

The Rust bridge builds. Its focused tests pass for exact 128-bit integers and
IEEE bit patterns, fresh/decoded valid tables, target mismatch and malformed
register rejection. The last case initially panicked in the existing VM's
whole-artifact summary construction; the authoritative verifier now runs its
existing descriptor and instruction-shape checks before those summaries.
A focused VM regression also checks invalid receiver, register type and target
metadata. These checks are not a Lean-generated source-program acceptance gate.

The first lowering repair gives initialization flags dedicated, always-live
prologue storage, consumes their old contents on replacement, reserves ABI
parameter registers contiguously, and relocates all local branch/label targets
when inserting the prologue. `tests/RegisterLowering.lean` exercises the real
lowerer with typed Core. Its artifact passed fresh/decoded VM verification and
executed successfully. Deliberately malformed live-flag and parameter-layout
variants were rejected. This is a receiving-boundary check, not a successful
run of the still-unbuilt certified source compiler.
