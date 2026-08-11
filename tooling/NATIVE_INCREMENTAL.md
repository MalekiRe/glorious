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
