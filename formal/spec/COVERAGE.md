# Specification audit

Initial draft only. The entries below locate the proposed formal meaning;
they are not a table of passed conformance gates.

| Language boundary | Formal modules |
| --- | --- |
| Supplied files/packages; no ambient imports | Declarations, Origins |
| UTF-8, literals, grammar and source forms | Syntax, SourceRules, Elaboration |
| Names, privacy, aliases and nominal identity | Declarations, Static, Elaboration |
| Calls, tuple arity, contextual blocks, evaluation order | Kernel, Elaboration, Machine |
| Pattern coverage, binding environments and ownership | Kernel, Typing, Control |
| Principal quantities, generic restrictions and recursion | Foundation, Static |
| Ownership, partial initialization, loans and cleanup | Storage, Machine, Contracts |
| Fn/RunsIn and guarded control interfaces | Declarations, Static, Contracts |
| Lifetimes, variance, higher-ranked constraints | Terms, Static, Typing |
| Effects, exact instances, deep handlers and quantities | Effects, Relocation |
| Direct labels and mandatory tail transfer | Machine, Control, ABI |
| Generics, traits, coherent impls and structural consts | Static, Instantiation, Elaboration |
| Fixity and ordinary operator calls | SourceRules, Elaboration |
| Unsafe memory, provenance and representation | Memory, Primitives, Typing |
| C declarations, callbacks and foreign barriers | Foreign |
| VM/native ABI, shared storage and artifact admission | ABI |
| Finite observations, divergence, rejection and limits | Foundation, Specification |

## Required repair/verification pass

The full initial draft must be written before the first build. Afterward:

1. Repair Lean elaboration failures without weakening semantic premises or
   replacing unfinished proofs with axioms/admissions.
2. Check foundational positive and negative propositions in `Checks`.
3. Audit every source form against the normative text, including generics,
   associated bindings, ownership markers, implicit operation instances,
   bodyless declarations, contextual alternatives and source-origin paths.
4. Check progress and composition at storage/control boundaries: partial
   holes, real drop-hook execution, cleanup order, nested handlers, cancellation,
   replay aliasing, lifetime restoration, binding packs and tail transfers.
5. Audit each primitive and target obligation for total defined behavior,
   closed authority, nonvacuous site coverage, and shared physical storage.
6. Distinguish checked definitions/examples from larger open metatheorems.

The target contract is for future implementations. There is no asserted
Stage0/self-hosted migration, VM/native execution test, or end-to-end compiler
proof in this standalone specification project. Library algorithms and their
verification are outside its scope, not a deferred phase of this work.
