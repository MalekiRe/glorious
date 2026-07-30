# Self-hosted compiler diagnostics

Status: implemented compiler-facing diagnostic contract for the self-hosted
compiler.

This document defines how failures from the existing frontend, Typed Core,
Stage-A lowering, emission, and artifact writer are normalized before they cross
the compiler API or host boundary. Phase-local error enums remain authoritative
inside their phases. The `diagnostics` module is the single adapter from those
enums to a stable cross-phase representation.

## Goals

The diagnostic layer exists to:

- preserve the detailed error value produced by each phase;
- assign stable codes without forcing every phase into one giant error enum;
- distinguish syntax, resolution, type, ownership, resource-limit, emission,
  and internal failures;
- identify whether a numeric location denotes source bytes, tokens,
  declarations, expressions, types, Core values, registers, artifact records,
  or another compiler identity space;
- carry a primary site, an optional related site, and an optional owning
  declaration;
- retain expected/found values used by type, shape, and count diagnostics;
- provide one deterministic renderer for the command-line host;
- give tests and future tooling a structured API that does not parse prose.

## Public boundary

The compiler still exposes `compiler::CompileError` as the compatibility error
surface for phase orchestration. Normal consumers should call:

```text
diagnostics::compile_source(source)
    -> Result<Bytes, CompilerDiagnostic>
```

The package entry point now invokes `diagnostics::application`, so errors emitted
by the self-hosted executable are rendered from `CompilerDiagnostic` rather than
from phase-only fallback strings.

`compile_error_diagnostic` remains public for tests, probes, and transitional
callers that already possess a `CompileError`.

## Stable codes

A diagnostic code is:

```text
phase_number * 1000 + phase_local_code
```

Phase numbers are:

| Phase | Number |
|---|---:|
| Lex | 1 |
| Declaration scan | 2 |
| Header parsing | 3 |
| Global resolution index | 4 |
| Interface collection | 5 |
| Declaration export | 6 |
| Body parsing | 7 |
| Body resolution | 8 |
| Body elaboration | 9 |
| Ownership lowering | 10 |
| Interface export | 11 |
| Emission/artifact writing | 12 |

Frontend local codes are the codes already owned by their phase error enums.
Lowering and emission receive exhaustive local codes in the normalization layer.
Every current body, resolution, elaboration, lowering, emission-name, emission,
and artifact-writer variant is matched explicitly. Adding a variant therefore
requires adding its mapping; there is no catch-all code path.

Rendered codes use the `G` prefix, for example `G2007` for declaration-ID
exhaustion during structural scanning.

## Classes

Every diagnostic has one class:

```text
Syntax
Resolution
Type
Ownership
ResourceLimit
Emission
Internal
```

Resource exhaustion is classified explicitly rather than being reported as an
ordinary syntax or type failure. Current resource-limit mappings include lexer
resource exhaustion, declaration-ID exhaustion, header type-arena exhaustion,
body expression-depth exhaustion, local-ID exhaustion, and integer-constant
encoding exhaustion.

`Internal` means the source pipeline reached a state that should have been
prevented by an earlier invariant. It is kept distinct from user source errors
so supervisors and tests can fail closed without blaming the program. Internal
body, resolution, and elaboration errors point at their actual identity spaces
rather than pretending an expression ID, interface index, or declaration ID is a
token ordinal.

## Typed location spaces

A `DiagnosticSite` contains a half-open range and a `DiagnosticSpace`:

```text
SourceByte
Token
Declaration
Interface
Type
Expression
ResolutionOccurrence
Local
CoreValue
CoreComputation
Register
RegisterPack
SwitchPack
Block
Function
StageType
Variant
Field
Artifact
```

This prevents a token ordinal, type ID, expression ID, register ID, and switch
pack ID from being interpreted as the same kind of number. Lexical failures use
source-byte spans. User-facing parser, resolution, and type failures normally use
token sites. Body failures additionally carry their owning declaration. Internal
frontend failures use declaration, interface, expression, resolution-occurrence,
local, Core-value, or Core-computation sites as appropriate. Lowering and
emission failures point into typed backend identity spaces.

A future source-map renderer may translate token and declaration sites into file,
line, and column information. That translation belongs at the rendering boundary
and does not change stable diagnostic identity.

## Related and owner sites

`primary` is always present. `related` is present when a phase supplies a second
meaningful location, such as an opening delimiter, previous declaration,
resolution occurrence, expected field, or conflicting variant. Related sites
may use a different identity space from the primary site. `owner` identifies the
body or declaration whose processing produced the failure.

The public accessors return space code `0` when an optional site is absent; all
real location spaces begin at `1`.

## Expected and found values

`expected` and `found` are compact typed arguments retained separately from the
message. They currently carry type IDs, counts, variant ordinals, field ordinals,
local limits, and other phase-defined words. A zero pair means that the
diagnostic does not supply this argument pair.

The renderer includes the pair when either value is nonzero. Tooling should use
the structured accessors rather than parsing the rendered sentence.

## Rendering

The canonical compact rendering is:

```text
[G<code>] <message> (<primary>)
    [; related <site>]
    [; owner <site>]
    [; expected <word>, found <word>]
```

For example:

```text
[G2007] self-host compiler: declaration scanning failed (token 3); related token 4
```

Rendering is deterministic and allocation is confined to the host boundary.
The semantic compiler pipeline transports `CompilerDiagnostic` values.

## Extension rules

When adding a phase error:

1. add or preserve the phase-local enum variant;
2. assign a phase-local code without renumbering existing codes;
3. map it exhaustively in the diagnostics adapters;
4. choose the narrowest correct diagnostic class;
5. identify the primary location space and any related/owner site;
6. retain expected/found values when useful to tools;
7. add a normalization test;
8. never downgrade an internal invariant failure to a user source error.

Phase implementations should not construct `CompilerDiagnostic` directly. They
return their own semantic errors, keeping phase APIs independent of presentation
and global numbering.

## Validation contract

The integration test compiles the diagnostic subsystem as part of the
self-hosted source bundle and checks:

- real lex, scan, header, body-parse, body-resolution, and body-elaboration
  failures;
- explicit resource-limit, ownership-lowering, and emission failures;
- stable phase, class, and code values;
- typed primary, related, and owner identity spaces;
- expected/found transport;
- deterministic text rendering.

The adapters intentionally use exhaustive `handle` expressions. If a phase error
enum grows, compilation must fail until its diagnostic mapping and tests are
updated.

## Future work

This change centralizes the cross-phase contract. Later architecture stages may:

- replace phase `code/token/related` projection functions with direct structured
  error fields;
- attach source-map segments and labeled spans;
- add severity, fix applicability, and typed formatting arguments;
- collect multiple recoverable diagnostics before terminal phase failure;
- emit machine-readable diagnostics through a capability host;
- keep the same stable code and location-space contract while changing prose.
