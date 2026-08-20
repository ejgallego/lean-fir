# Wasm instruction-profile consumer

Status: real-consumer compatibility checkpoint. This does not define a package
schema or change the canonical release artifact.

## Decision

The existing Node Inspector profile remains a final-function consumer only.
Node 24.19.0 also accepts V8's experimental `--perf-prof-annotate-wasm` flag,
but its embedder does not install the Wasm source-map loader required by that
path. A `perf` capture therefore resolves the optimized Wasm function and its
native PCs, but the injected ELF has no debug-line table relating those PCs to
the module source map.

The first instruction-level consumer should be V8's `d8` perf path:

```text
perf record -k 1 ... -- d8 \
  --perf-prof \
  --perf-prof-annotate-wasm \
  --perf-prof-unwinding-info ...
perf inject --jit -i perf.data -o perf.jit.data
```

This is deliberately a diagnostic-only path. The normal Node/browser
benchmark continues to execute the exact stripped release with no source map,
instrumentation, or profiler flags. FIR should not add a native Node addon or
an instrumented module merely to make the current profiler consume a map.

V8's implementation makes the embedder boundary explicit. The perf logger
reads the module's source map and emits native-PC debug entries keyed by source
filename and one-based line. Its column is fixed to one. The `d8` shell
installs the necessary `WasmLoadSourceMapCallback`; Node does not currently do
so. The relevant upstream sources are:

- <https://chromium.googlesource.com/v8/v8/+/refs/heads/main/src/diagnostics/perf-jit.cc>
- <https://chromium.googlesource.com/v8/v8/+/refs/heads/main/src/d8/d8.cc>
- <https://chromium.googlesource.com/v8/v8/+/refs/heads/main/tools/profiling/linux-perf-d8.py>

The real `d8` gate has now run. V8 15.4.29 opens W7-2's source map, but its
Wasm source-map reader rejects the standard one-field unmapped segment at the
end of the map. The exact companion therefore produces sampled Wasm native
PCs without a debug-line table. A diagnostic mapped-only projection proves
that `d8` and `perf inject` preserve the selected location key, but that
projection is not the canonical source map; the compatibility boundary is
recorded below.

## Minimum location key

The perf consumer exposes:

```text
(synthetic source filename, one-based source line)
```

It does not expose a final Wasm bytecode offset, a source-map column, or an
inline stack. W7 should allocate a unique line within each synthetic symbolic
function source. Tooling resolves that pair to one origin-table row. Repeated,
missing, or multiply resolved pairs fail closed; they are never repaired by
instruction order.

The origin row needs only the compiler facts already proposed by W7:

- stable origin identity;
- symbolic function identity;
- structured instruction path or preorder identity;
- symbolic opcode; and
- direct-call target when the instruction is a call.

## Release-bound sidecar

A first consumer sidecar must bind:

- schema and location-key versions;
- canonical stripped release byte length and SHA-256;
- mapped companion byte length and SHA-256;
- final source-map byte length and SHA-256;
- origin-table byte length and SHA-256;
- exact Binaryen version and ordered transformation arguments;
- the final function-index sidecar SHA-256;
- source filename and one-based line for each mapped origin; and
- explicit mapped, deleted, unknown, and ambiguous counts.

The companion must strip to the independently generated canonical release.
The verifier rejects hash drift, duplicate location keys, a source-map entry
without an origin, or an origin classified both mapped and deleted. A native
PC without debug-line information is `unknown`, not a nearest-neighbor match.

The synthetic filename and one-based line are sufficient as the identity
carried by a native-PC annotation. They are not, by themselves, a complete
sidecar: the authoritative sidecar must still retain final instruction
identity and explicit mapped, deleted, unknown, and ambiguous states. A
consumer-specific source-map projection must not silently turn an unmapped
interval into the nearest preceding origin.

## Node feasibility evidence

The probe consumed W7-2's ignored two-module fixture at branch
`wasm/generic-array-validation`, commit `8b67f0da`. Its release SHA-256 was
`dcd66e4279859b4770c7f602413acae72f97d94cff82c0d911fb0927831e1f53`.
The source-map-bearing module and map used for the Node capture had SHA-256:

```text
c2b52e745e891eff986350d3098303b9cca0c1e127994bc1b8b7aa6260ab32e7  pipeline-url.wasm
2ebd0c003198538057428bacad20e0cb35dce5e641305be9f05e2376e34716fb  pipeline-url.map
```

The accepted capture used Node 24.19.0, perf 6.19.10, `cycles:u` at 997 Hz,
inherited sampling, monotonic clock id 1, and a 100,000-call warmup followed by
5,000,000 measured calls. The endpoint was exactly 5,100,000. It recorded 145
samples; the optimized Wasm entry was present as `JS:entry-0-turbofan`.
After `perf inject --jit`, its generated ELF contained `.text` and `.symtab`
but no `.debug_line` section. Raw evidence is retained under the tooling
worktree's ignored `.deps/instruction-profile/run-03/` with these hashes:

```text
a39f502fa253a3cf168778252f55494935e3ed7752b697edfef7d32f873c165c  perf.data
c22529f9235ca2a93588dcacb4c15a8405eef04ebebdd1f138beb0e7a8ad1abe  perf.jit2.data
4dbd4d07e595155be33f7283f62d5dfbb43ea97f11d6657ece2a6f5cf4301a41  jit-6.dump
8d959b03fa3c68fedacfe4214892ef955c70ff64eae7d2f1fe7248e174b0f87f  jitted-6-2415.so
```

The first rejected capture omitted `perf record -k 1`; `perf inject` correctly
rejected the clock mismatch. Any future wrapper must enforce the monotonic
clock and reject an injected profile that lacks both the expected Wasm symbol
and debug-line entries.

## Real d8 gate evidence

The gate consumed W7-2's deterministic optimizer fixture from commit
`7444a33b`. The exact ignored outputs had these identities:

```text
850b6fae3fdc9761585dda42baf99b3e15aa5001e14adaa4c4cf8cd526b8427c  instruction-provenance.wasm
c9cfaf027b3da1529fd4d26e95b34eb76b7dcc1a6e5362d2a064c9d1f2355722  instruction-provenance.map
9705368cff660e5b18c827a4c6791db802081c36c76badee50ee3e5c2a38954a  instruction-provenance-report.json
```

The report binds a 58-byte canonical release at SHA-256
`0cf51807b1ccedeedbc81293acd275cd17d86b2ba2e186fc383e80a2d888a1b8`.
It classifies seven keys as mapped and five as deleted, with zero optimizer
unknowns, ambiguities, or repeated mappings. The companion remains 121 bytes,
has no imports, and exports only `fixture.entry`.

The consumer was `d8`/V8 15.4.29, installed by `jsvu` 3.0.5 from V8's official
Linux x64 release archive. The `d8` binary SHA-256 was
`ce93362b4ef8170a2b51cbe99aed57cda82613eb6dfc5f24a0f411c61a470b5b`.
The host used perf 6.19.10 on Linux 7.1.5-070105-generic x86-64, with
`kernel.perf_event_paranoid=2` and `kernel.kptr_restrict=1`.

The exact-map control kept the small fixture out of JS-to-Wasm inlining and
forced its Liftoff debug source-position path so absence of a line table could
not be blamed on the fixture's normal tiering behavior:

```text
perf record -k 1 -F 997 -o perf.data -- d8 \
  --perf-prof --perf-prof-path="$PWD/jit" \
  --perf-prof-annotate-wasm \
  --liftoff-only --wasm-debug-mask-for-testing=1 \
  --no-turbo-inline-js-wasm-calls \
  --no-wasm-in-js-inlining-body \
  --no-wasm-in-js-inlining-wrapper \
  driver.js -- instruction-provenance.wasm 100000000
perf inject --jit -i perf.data -o perf.jit.data
```

It captured 2,570 samples and resolved `JS:entry-0-liftoff`, but the injected
ELF had no `.debug_line` section and no synthetic filename. The exact map ends
in `,C`, a valid one-field unmapped segment. V8's
`WasmModuleSourceMap::DecodeMapping` consumes four fields unconditionally and
therefore rejects that segment. The raw exact-control hashes were:

```text
635f15b486b07f93d2f013ac49c7ffb7421fa95e84e3cc66c2b94aa5802cb36e  perf.data
2c75937ecd21414b9633fcbbfba358527ec3cf413cae7e657c3c985420e8586d  perf.jit.data
fa805527dea0e66d006441403e5a70e2a98e4bfeb676b207d40df4969797693f  jit-7.dump
d068404c6ae020b2f5c4a6f685c69eae0025cc7e8dd639ea5f9027618ba9bdaf  jitted-7-2528.so
```

For diagnosis only, removing that terminal unmapped segment produced a
four-field-only map at SHA-256
`44b76cfa88cbc53dc04ffbbbbd2acf735e66ec3ef0143777547a1d6d5eb2dc1d`.
With otherwise identical settings, `perf inject` emitted a native line-table
entry at PC `0x102` for the expected key
`fir-wasm-origin/1/fixture.entry:1`. This proves that the chosen filename and
one-based line survive the `d8` JIT-dump path. It is not an accepted fix:
Binaryen's source-map disassembly shows that removing the sentinel extends
`fixture.entry:7` to the function close. The authoritative exact report keeps
the five deleted keys distinct, and consumer PCs lacking an exact annotation
remain explicitly unknown.

## Next gate

W7-2 should add a V8-consumable profiling projection without changing the
canonical stripped release or losing the authoritative unmapped/deleted
classification. The repeat gate must resolve sampled final instructions to
their expected synthetic keys and reject any reassignment caused by an
unmapped interval. Only then should the instruction sidecar be versioned for
packages. Representative size and build-time costs remain separate from this
consumer-compatibility result.
