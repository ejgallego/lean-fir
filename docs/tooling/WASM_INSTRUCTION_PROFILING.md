# Wasm instruction-profile consumer

Status: consumer selection checkpoint. This does not define a package schema
or change the canonical release artifact.

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

No suitable `d8` executable is installed on the current host, so the next W7
schema step remains gated on running this same fixture through a real `d8`
capture. The consumer and its location key are nevertheless fixed narrowly
enough for W7 to avoid an incompatible offset-based design.

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

## Next gate

W7 may continue with its additive encoder-origin trace and deterministic
source-map pipeline fixture, but the package schema should wait for one `d8`
capture proving that all three surviving fixture expressions resolve to the
expected synthetic source/line keys. Representative size and build-time costs
remain separate from this feasibility result.
