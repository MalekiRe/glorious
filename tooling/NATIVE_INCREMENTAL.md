# Process-local native incremental iteration

Keep one release `grc --serve` process alive while editing a compiler source
bundle. Send ordinary JSON-line `compile` requests with `--emit llvm-ir`,
`--emit llvm-object`, or `--emit executable`:

```json
{"protocol":1,"id":7,"method":"compile","arguments":["-O3","--emit","executable","-o","/tmp/grc-next","/work/compiler.glorious"]}
```

Successful native requests include `native_incremental`. Its counters state
how many independently emitted LLVM function fragments were reused or emitted
for that request, plus native-object reuse/emission evidence. `cache_scope` is
always `serve-process`: ending the server discards the cache, and no response
promises a cross-process or filesystem cache.

`wild_relink` is true for every executable request. A native executable is
never served from a cache: even when earlier IR/object work is reusable, the
request performs a fresh final link through Wild. Object-only requests do not
link and report `wild_relink: false`.

The counters are work evidence, not elapsed-time benchmarks. In particular,
an unchanged request can hit the complete LLVM-module cache; that avoids a
fragment-cache pass and may therefore report zero fragment units.

## Partitioned executable request contract

The function-object native path is selected only by a persistent server
request. Its exact request shape is:

```json
{"protocol":1,"id":8,"method":"compile","arguments":["-O3","--emit","executable","--native-incremental","-o","/tmp/grc-next","/work/compiler.glorious"]}
```

`--native-incremental` is deliberately not accepted as a one-shot `grc`
command: process-local object reuse cannot survive that command's process
boundary. It requires `-O3` and `--emit executable`; no other optimization
level or emit kind may silently select a different native route.

## Durable cache for independent invocations

For ordinary one-shot recompiles, select the same function partitioning with
a private, worktree-local cache directory:

```sh
grc -O3 --emit executable \
  --native-incremental-cache .cache/native-objects \
  -o /tmp/grc-next /work/compiler.glorious
```

This route compiles a shared runtime/entry object plus one object for each
source-function LLVM fragment. A function object is reused across compiler
processes only when its complete emitted IR and exact native toolchain/runtime
ABI match. Each unit retains the runtime/global declarations it needs and only
the source-function declarations referenced by its own body, so an unrelated
sibling ABI edit does not invalidate that unit. A body-only edit therefore
recompiles that function while retaining unchanged sibling objects. Missing,
malformed, or digest-mismatched cache entries are discarded and rebuilt.

The cache directory is an input/output artifact owned by one worktree; copy a
seed into a new worktree rather than sharing a mutable directory between
worktrees. It may also retain a linked executable, but only under a
cryptographic manifest that binds the ordered object keys and bytes, bundled
host runtime, and the Clang/Wild link ABI. A missing, corrupt, or non-identical
manifest requires a fresh Wild link; this never weakens the Wild requirement.

The native-stage integration must expose this response shape on a successful
request (additional fields are permitted):

```json
{
  "native_incremental": {
    "cache_scope": "serve-process",
    "strategy": "partitioned-function-objects",
    "function_objects_reused": 2,
    "function_objects_compiled": 1,
    "shared_objects_compiled": 1,
    "wild_relink": true
  }
}
```

`function_objects_reused` and `function_objects_compiled` count source
functions, not a monolithic LLVM module. The shared runtime/entry object is
not a function cache hit and must be reported separately. `wild_relink: true`
is non-negotiable: every successful executable request links the complete
current object set with Wild, including function objects restored from the
process-local cache. A linked executable is never cached or reused.

The release contract test for this integration must issue a cold request and
then a same-ABI leaf-body edit through one `grc --serve` process. It must
assert that the second response has at least one reused function object, one
compiled function object, `strategy: "partitioned-function-objects"`, and
`wild_relink: true`; it must also assert that both requested executable paths
exist. This is evidence of safe per-function reuse plus a fresh final link,
without depending on wall-clock timing.
