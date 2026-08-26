# Architectural review

I reviewed the current `master` implementation across the lexer, scanner, header and body parsers, resolution, elaboration, lowering, emission, artifact writer, and compiler driver.

The central issue is not any one algorithm. It is that the compiler repeatedly **encodes the same information two or three different ways**:

* semantic enums plus numeric tags;
* typed IDs plus raw `u32` conversions;
* arenas plus large accessor surfaces;
* phase errors plus separate code/primary/related projections;
* parsed resolutions plus a second elaboration resolution map;
* semantic types plus backend type copies plus artifact records;
* every phase plus its own CLI and binary snapshot serializer.

I count roughly **22,548 physical lines** in the current `self-host/src` module set—about 18.1K frontend and 4.4K backend. That is not directly comparable to your architecture document’s **nonblank, noncomment** 9–12K target, but it makes the architecture review timely, especially because the implementation still describes the Core as minimal and the backend as Stage-A. Your design explicitly calls for shared representations, table-driven logic, few abstraction layers, and exactly three semantic representations.

## 1. Introduce one `CompilerSession` and one body-local context

This would be my first foundational change.

Today, core routines repeatedly thread nearly the entire compilation state through long parameter lists. `elaborate_expression`, for example, receives the original source, headers, declarations, mutable interfaces, parsed body, resolution map, body builder, expression ID, and expected type; every recursive call repeats most of that list.

I would introduce:

* `CompilerSession`: source map, name interner, declaration table, semantic type interner, options, diagnostics, and global caches.
* `BodyContext`: current body syntax, lexical scopes, inference state, Core builder, and reusable scratch storage.
* `LoweringContext`: current Typed Core body, MIR builder, PlaceFlow state, and diagnostics.
* `EmissionContext`: canonical pools and the artifact writer.

Then operations become context methods conceptually equivalent to:

```text
body.check_expression(expr, expected)
body.resolve_name(name)
mir.lower_value(value)
artifact.emit_function(function)
```

This should remove a substantial amount of parameter threading, raw module qualification, and “plumbing” code while making lifetime and ownership boundaries much clearer.

Only the outer driver should carry `ProcessArgs`, `FileRead`, `FileWrite`, and host `Diagnostic` capabilities. Compiler phases should be pure except for compiler-internal diagnostic or abort effects.

## 2. Create one typed range-and-arena substrate

The same two-field range structure is currently reintroduced under many names:

* `TokenRange`
* `HeaderRange`
* `HeaderTokenRange`
* `ExprRange`
* `BodyTokenRange`
* `TypeElementRange`
* `InterfaceFieldRange`
* `InterfaceVariantRange`
* `VariantPayloadRange`
* `CallableParameterRange`
* `OperandRange`
* `ConstructionFieldRange`
* `MatchArmRange`
* `MatchBindingRange`
* several elaboration-only ranges

Examples appear throughout headers, bodies, and elaboration.

I would add a single generic abstraction along the lines of:

```text
IdRange<Tag>       // typed arena start plus count
IndexRange         // raw integer range only when genuinely untyped
SourceSpan         // source offsets
TokenSpan          // token IDs
```

The important addition is a range builder:

```text
mark = arena.mark()
... allocate children ...
children = arena.range_since(mark)
```

That would eliminate a large amount of manual `start = Vec::len`, append, `count = Vec::len - start`, checked conversion, and `Slice::subslice` boilerplate.

Grandiose features to lean on here are generic types, typed `Id<Tag>`, borrowed `Slice<'a, T>`, associated types or GAT-style borrowed views, and `IndexVec`.

## 3. Stop mirroring semantic enums with numeric tags

This is probably the single largest recurring source of complexity.

Examples include:

* `Token` stores `TokenKind`, `code`, and `keyword_code`.

* `DeclarationShell` stores both `DeclarationKind` and `kind_code`.

* header `TypeNode` stores a `kind_code`, then reconstructs a `HeaderTypeView`.

* body `ExprNode` stores `kind_code`, generic edge positions, and metadata.

* elaboration dispatches on body expression numbers `1` through `12`.

* `StageType` stores a `tag`, empty vectors for irrelevant variants, and is decoded into `StageTypeView`.

The elaborator itself already demonstrates the better pattern with `TypeKind`, `CoreValueKind`, and `CoreComputationKind`: direct enums with typed payloads and exhaustive handling.

I would use that model consistently:

* `DeclarationHeader` as an enum with payloads.
* `TypeSyntax` as an enum.
* `ExprKind` as an enum.
* `StageType` as an enum, assuming it survives the MIR refactor.
* `TokenKind` as the only internal token classification.

For the one-body-at-a-time AST, the memory savings of packed universal nodes are unlikely to justify thousands of lines of decoders and accessors. Start with direct enums and measure. If profiling later proves packing necessary, keep the packing private and expose exactly one typed view API generated or expressed from the same schema. Numeric tags should never escape that storage module.

This also uses one of Grandiose’s strongest features directly: exhaustive `handle` over algebraic data rather than fragile numeric conventions.

## 4. Extract all phase CLIs and snapshot encoders from production modules

The lexer, scanner, headers, bodies, resolution, and elaboration modules each contain some combination of:

* process-argument handling;
* file reads and writes;
* a phase-specific binary protocol;
* replay of every earlier compiler phase;
* a standalone `application`.

For example, the lexer spends its tail serializing tokens and implementing a CLI; headers have two standalone applications; bodies and resolution each repeat lex → scan → headers → phase → serialize.

This is useful bootstrap and differential-test infrastructure, but it should not live inside every compiler phase.

I would replace it with:

* one production `driver::compile(inputs, options)`;
* one test-only `probe::run(stage, input)` adapter;
* one generic snapshot envelope;
* phase-specific snapshot functions in test modules only.

The current root still invokes `frontend::application`, which delegates to the lexer application, while an integrated compiler application already exists in the backend. I assume this is intentional staging, but the final executable should have one driver and the stage tools should be test targets.

This extraction alone should remove a meaningful number of lines and, more importantly, enforce that compiler phases do not accidentally acquire filesystem or process capabilities.

## 5. Build delimiter pairing once and use a shared `TokenCursor`

The scanner currently finds closing delimiters through a recursive walk and then invokes that operation from other searches such as semicolon and body discovery.

Headers and bodies then independently implement cursor bounds, numeric token checks, `eat`, `expect`, and delimiter logic. The header parser, for example, has separate functions for every expected punctuation token, all expressed using magic numeric token codes.

I would make the structural pass produce:

```text
DelimiterMap: IndexVec<TokenTag, Option<TokenId>>
```

Every opening and closing delimiter is paired once in a single stack pass. Scanning and parsing can then jump over a balanced token tree in constant time.

On top of that, add a small shared cursor with operations such as:

```text
peek()
peek_kind()
eat(TokenPattern)
expect(TokenPattern, DiagnosticCode)
mark()
span_from(mark)
enter_delimited(...)
```

The body operator parser can remain Pratt- or shunting-yard-based; it does not need a large generic parser-combinator framework. The important point is that token mechanics and error construction are written once.

## 6. Unify declarations and namespaces into one `DefTable`

The current model has:

* scanner declaration shells;

* separate callable, alias, struct, enum, variant, and fixity stores;

* `NominalIndex` parallel `order_kinds` and `order_indices`;

* a function-specific resolution index;

* raw `u32` function, struct, enum, and variant identities;

* separate search and ambiguity logic for each nominal category.

I would define one declaration arena:

```text
Def {
    parent: ModuleId,
    name: NameId,
    visibility: Visibility,
    span: Span,
    kind: DefKind
}
```

`DefKind` carries a typed payload such as callable, struct, enum, variant, trait, impl, effect, or fixity. A single namespace index maps:

```text
(ModuleId, NameId, Namespace) -> small range of DefId
```

This gives one ambiguity mechanism, one visibility mechanism, one module lookup path, and one stable identity for diagnostics.

I would also merge **body-local resolution into typed elaboration**. Keep declaration indexing separate, but resolve parameters, locals, pattern binders, and global references while the body checker walks the body in source evaluation order.

Currently `ResolvedBody.names` is produced as a vector of `(ExprId, ResolvedTarget)`, and elaboration then copies it into `ResolutionMap` with a nearly identical `ElaborationTarget`.

At minimum, resolution should write directly to:

```text
IndexVec<ExprTag, Option<ResolvedTarget>>
```

A more aggressive—and probably smaller—design eliminates the persistent `ResolvedBody` entirely and lets `BodyContext` resolve as it elaborates.

For lexical scopes, use a `ScopeMap<NameId, BindingId>` with a scope journal or binding stack. The current reverse recursive scan through a flat binding vector makes each lookup linear.

## 7. Replace phase-specific error projection with one structured diagnostic model

Several modules define an error enum and then separately match every variant to obtain:

* a numeric code;
* a primary token;
* a related token.

Bodies and resolution demonstrate the resulting triplicated matches.

Meanwhile, the integrated compiler eventually discards the structured `CompileError` and prints only “compilation failed.”

I would use one representation:

```text
Diagnostic {
    code: DiagnosticCode,
    primary: Span,
    labels: SmallVec<DiagnosticLabel>,
    arguments: DiagnosticArguments
}
```

Then distinguish:

* **user diagnostics**, which can be reported;
* **resource-limit diagnostics**, which terminate a phase cleanly;
* **compiler invariant failures**, which should not masquerade as source errors.

This is an ideal, restrained use of Grandiose effects:

* a `Report(Diagnostic)` effect for recoverable diagnostics;
* a label-generic terminal `fail(diagnostic, @phase)` or typed phase-abort effect;
* `try` for ordinary result propagation;
* the actual host `Diagnostic` capability handled only by the driver.

I would not use effects for every arena allocation or state mutation. Keep hot compiler state explicit in context structs; use effects for reporting and nonlocal phase exit, where they eliminate real boilerplate.

## 8. Move copy-versus-move and final-use inference into `PlaceFlow`

This is the most important correctness-oriented architectural change.

The elaborator currently performs several syntax-directed traversals:

* determine whether an expression is straight-line;

* count occurrences of each local in a subtree;

* search for repeated locals in struct construction;

* record the last expression for each local;

* mark candidate final transfers;

* special-case root block statements and calls.

This has two major problems:

1. It is potentially expensive: repeated-local detection walks subtrees once per local.
2. Every new control construct, effect edge, callable capture, pattern, loan, or cleanup rule will require more syntax-specific exceptions.

Your architecture already identifies the correct answer: initialization, moves, loans, captures, continuation state, and cleanup should all be views over one sparse `PlaceFlow` graph. It also defines final-use transfer semantically rather than syntactically.

I would:

* elaborate references to typed places without deciding copy versus move from AST shape;
* build ordered Core or MIR uses;
* run one reverse use/liveness pass;
* select `Move` for the final legal use and `Copy` otherwise;
* feed the same facts into loans, partial moves, captures, cleanup, and must-move checking.

That prevents the future ownership implementation from becoming one subsystem per expression kind.

## 9. Enforce the “exactly three representations” rule now

The intended architecture has:

1. declaration headers plus transient body AST;
2. Typed Core;
3. ownership/control MIR.

The body AST and Core scratch are then reclaimed body by body.

The current backend adds `StageProgram`, `StageFunction`, `StageInstruction`, register packs, blocks, switch packs, type copies, constants, and then an additional artifact record layer.

Because full MIR is not yet present, I would make an explicit choice before adding it:

* either evolve `StageProgram` directly into the real ownership/control MIR;
* or delete it when MIR arrives and make instruction selection produce per-function assembler output directly.

Do not keep `Typed Core → full MIR → StageProgram → GRBC` as four persistent semantic representations.

A good final shape is:

```text
headers/transient AST
        ↓
Typed Core
        ↓
MIR + PlaceFlow
        ↓
per-function assembler scratch
        ↓
GRBC
```

Assembler scratch is a serialization mechanism, not another semantic IR.

I would also prevent `CoreComputationKind::Match` from growing into a source-level `match` implementation. It should either be a clearly named core sum eliminator or be lowered to handler/sum dispatch or MIR `Switch` before persistent Core. Typed Core must retain the language principle that source-library names such as `match`, `if`, loops, and return do not select compiler nodes.

## 10. Add a small ANF/Core builder rather than manually wrapping computations

The current elaborator distinguishes `ElaboratedForm::Value` and `ElaboratedForm::Computation`, permits `CoreValueKind::Embedded`, records `LetWrapper`s, materializes operands, and later wraps computations in reverse order. That machinery appears repeatedly in call, construction, and handle elaboration.

A small `CoreBuilder` should offer operations conceptually like:

```text
value(form) -> CoreValueId
bind(computation) -> CoreValueId
emit(statement)
finish(result)
```

`bind` automatically creates a temporary and extends the current let-prefix or Core block. Then most expression elaborators return a `CoreValueId` and do not need to know whether preceding work was pure or computational.

This is another good place to use ordinary Grandiose callables and lazy closures:

```text
with_value(elaborate(expr), { value => ... })
```

Keep this builder specific to Core. A generalized visitor/pass framework would likely add more machinery than it removes.

## 11. Introduce one generic canonical pool with freeze-and-remap

Emission currently performs recursive linear searches for constants and names. There are parallel paths for borrowed and owned string lookup, and signatures are handled similarly elsewhere.

Use one reusable abstraction:

```text
CanonicalPool<Key, Tag> {
    map: HashMap<Key, Id<Tag>>,
    values: Vec<Key>
}
```

During compilation, insertion is hash-based and IDs are noncanonical. At the serialization boundary:

1. sort keys deterministically;
2. deduplicate if necessary;
3. produce `old_id -> artifact_id`;
4. serialize in frozen order.

The same abstraction can serve:

* strings;
* constants;
* signatures;
* operand or register packs;
* type records;
* possibly cleanup layouts.

This directly implements your architectural rule that internal arena allocation need not be canonical and only serialized output is sorted.

## 12. Move type properties out of emission and schema-drive the artifact writer

Emission currently recursively recomputes zero-sized and zero-use properties while serializing types, using separate but structurally similar traversals.

Those are semantic type facts, not writer concerns.

Create a memoized side table keyed by semantic `TypeId`:

```text
TypeFacts {
    copyable,
    zero_sized,
    permits_zero_use,
    needs_drop,
    representation
}
```

Compute it once using a worklist or SCC-aware solver so recursive types are handled deliberately. `PlaceFlow`, lowering, optimization, and emission then read the same facts.

The artifact format should likewise be described once. At present:

* `SectionId` is manually converted to an ordinal;

* fixed widths are a numeric `if` chain;

* fourteen default sections are pushed individually;

* instruction words such as `20489`, `12298`, `16417`, and `4134` are embedded directly;

* optional IDs are encoded with raw `4294967295`.

I would define:

* `SectionSpec { id, encoding, fixed_width }`;
* typed `Opcode` values;
* one instruction layout description;
* a named optional-ID sentinel encoder;
* an `IndexVec<SectionTag, Section>` rather than an untyped vector;
* an exhaustive instruction encoder.

Ideally the same frozen schema drives or validates both the self-hosted writer and Rust verifier—through generated tables, a checked schema hash, or conformance tests. This does not require adding macros or reflection to Grandiose.

# Target structure

The architecture I would aim for is:

```text
driver                         // process/fs/host diagnostic capabilities
  |
  v
CompilerSession
  - SourceMap
  - NameInterner
  - DefTable
  - TypeInterner + TypeFacts
  - Diagnostics
  - Options
  |
  +--> syntax
  |      lexer -> tokens + delimiter map
  |      declaration headers
  |      transient body AST
  |
  +--> BodyContext
  |      ScopeMap
  |      expected-type elaboration
  |      trait/quantity checking
  |      CoreBuilder
  |
  +--> Typed Core
  |
  +--> MIR + PlaceFlow
  |
  +--> per-function instruction selection
  |
  +--> CanonicalPools + schema-driven GRBC writer
```

The small reusable compiler toolkit would consist of only about six real abstractions:

1. `IdRange<Tag>`
2. `TokenCursor`
3. `ScopeMap`
4. `CanonicalPool`
5. `Diagnostic`
6. `BodyScratch`/`CoreBuilder`

Everything else should be direct data and direct algorithms.

# Refactor order I would use

**First, delete nonsemantic duplication:** move all phase applications and binary snapshot writers into one probe/test layer; wire the root executable to the integrated compiler; add a normalized nonblank/noncomment line-count report.

**Second, establish the substrate:** introduce `CompilerSession`, `BodyContext`, common typed ranges, `TokenCursor`, `DelimiterMap`, and structured diagnostics. Migrate scanner and headers first because they have the least semantic risk.

**Third, simplify the body pipeline:** replace numeric `ExprNode` dispatch with a direct enum or single typed view; introduce `DefTable` and `ScopeMap`; eliminate `ResolvedBody → ResolutionMap → ElaborationTarget`; add the Core builder.

**Fourth, move ownership semantics:** replace AST-based final-transfer inference with the initial PlaceFlow/MIR analysis before adding more effects, handlers, closures, borrowing, or cleanup behavior.

**Fifth, simplify the backend:** make the Stage representation become real MIR or remove it, add canonical pools and cached type facts, and convert the writer to a schema-driven encoder.

The code already has several good foundations worth retaining: typed arena IDs, `IndexVec`, one-body-at-a-time parsing, source fixities, deterministic serialization, and the emerging borrowed semantic views. The main improvement is to apply those ideas consistently and stop crossing phase boundaries through raw tags, raw words, and phase-specific serialization APIs.
