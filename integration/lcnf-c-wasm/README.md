# LCNF to optimized C/Wasm lane

This directory is owned by the `wasm/lcnf-c` lane in
`.worktrees/wasm-lcnf-c`. It provides an alternative executable path:

```text
Lean source
  -> final saved impure LCNF
  -> Lean's direct LCNF C emitter
  -> optimized LLVM WebAssembly backend
  -> standards-consumable `.wasm`
```

The lane consumes Lean's existing final-impure and generated-C contracts. It
does not change FIR's symbolic Wasm surface, W6 concrete runtime, W7 resident
runtime, or shared interpreter semantics.

This is the **compiler-native C/Emscripten Wasm path**. The complementary
**FIR-native symbolic Wasm path** is packaged under
[`integration/talos/artifact`](../talos/artifact/README.md); it lowers final
impure LCNF through `Fir.Wasm` and owns the symbolic/concrete runtime proof
surface. These paths share the LCNF checkpoint, not an artifact ABI or loader.
See the [artifact-generation guide](../../docs/wasm-artifact-generation.md)
for the choice matrix and validation boundary. Host-native executables used
below are differential or performance oracles, not a third Wasm backend.

## Runtime profiles

The LCNF-to-C frontend is shared. Runtime selection is a link profile, not a
second compiler:

| Profile | Support status | Host contract | Current acceptance fixture |
| --- | --- | --- | --- |
| `freestanding` | primary, deliberately narrow | `wasm32-unknown-unknown`, no imports or libc | raw `UInt64` expression and tail loop |
| `emscripten` | primary for realistic programs | browser/Node ES module plus pinned `libleanrt`, `libInit`, and `libStd` | lists, arrays, strings, closures, `Except`, `Std.HashMap`, and real `IO.eprintln` |
| `wasi` | experimental, ABI 3 frozen | single-threaded Lean core-object runtime in a WASI Preview 1 reactor (`wasm32-wasip1`) | boxed `UInt64`, lists, object and byte arrays, strings, captured one/two-argument closures, exact reclamation, scalar C, and a real monotonic-clock import |

Normal lane acceptance runs the freestanding and Emscripten profiles through
`check-primary.sh`. WASI stays green through `check-wasi.sh` and
`check-all.sh`, but it is not on the short-term feature-expansion path. See
the [WASI support policy](WASI-PORTING.md) for the frozen boundary and the
gate for a future selective upstream runtime port.

`Smoke.lean` exports two raw `UInt64` functions. One is a scalar expression;
the other is a compiler-lowered tail loop. `HeapSmoke.lean` dynamically
allocates boxed `UInt64` values and list constructors, consumes the list, and
returns an exact checksum. `WasiCoreSmoke.lean` adds an Init-only captured
closure pipeline over ordinary object arrays and dynamically appended UTF-8
strings. `WasiScalarSmoke.lean` grows and folds a `ByteArray`, then passes its
checksum through captured two-argument closures stored in an object array.
`RuntimeSmoke.lean` widens the full-runtime coverage to mutable arrays,
success/error `Except` branches, and a `Std.HashMap`, then exposes a real
`Init` I/O probe.

The freestanding runtime is deliberately narrow. It implements only the
primitive operations referenced by `Smoke.lean`; it must not silently grow a
second object model.

The Emscripten setup builds the complete Lean runtime plus the generated
`libInit` and `libStd` archives from the exact source commit matching the
frontend. All three archives are compiled at `-O3` with LTO. The linked module
initializes `RuntimeSmoke`, reaches the real `Init` implementation of
`IO.eprintln`, and has no lane-local replacement for that symbol. Link-time
garbage collection retains only the reachable runtime/library cone.

`check-emscripten.sh` compiles the same `RuntimeSmoke.c` with the native Lean
toolchain and compares five native results byte-for-byte with the Wasm exports
and an independent JavaScript oracle. This catches frontend, runtime, and host
ABI drift separately. Setting `FIR_BROWSER` additionally serves the artifact
with cross-origin-isolation headers and runs the same Init/Std surface in a
headless browser.

`build-emscripten.sh` is the reusable form of that pipeline. It accepts an
entry Lean module, zero or more additional source modules, explicit C exports,
and an optional zero-argument `IO UInt32` start action. It discovers the
generated module initializer instead of guessing its encoded C name, links
the pinned full runtime/Init/Std cone, and exports
`fir_lcnf_c_initialize` as the mandatory host entry point. Requested exports
must be valid C identifiers present in the generated code; misspellings fail
the build before linking. Every build emits an ES module, a Wasm module, and a
deterministic manifest. The manifest contains no timestamp or absolute host
path; it records relative sources, pinned toolchains, normalized compile/link
flags, runtime requirements, the admitted ABI, byte lengths, and SHA-256
digests.

`emscripten-loader.mjs` consumes that manifest in Node or a browser. It
validates the schema and ABI, verifies both artifact lengths and digests before
loading code, supplies the verified Wasm bytes to Emscripten, initializes the
Lean runtime/module/start action exactly once, and returns only the declared
exports. Threaded browser artifacts fail early unless the page is
cross-origin isolated.

The WASI artifact is intentionally a Preview 1 core-module reactor. It links
the heap, core, and scalar fixtures against ABI 3 of a single-threaded subset
of the pinned Lean C ABI. The subset uses the official `lean.h` object layout
and calling convention, wasi-libc allocation, stack-safe reference-count
reclamation, ordinary object-array copy-on-write growth, UTF-8 string append,
byte-array copy-on-write growth, and full `apply_1`/`apply_2` calls through
arity three. Acceptance compares five fixed cases per fixture with both the
native Lean runtime and an independent JavaScript oracle. It also
requires exact list allocation counts, balanced allocation totals, zero live
objects after every call, exactly two reclaimed captured closures per core
call, one reclaimed dynamic string for the string fixture, reclaimed scalar
arrays for the byte fixture, and complete per-object-kind deallocation
dispatch.

This core profile still fails closed on partial and unadmitted closure
application, non-byte scalar arrays, structure arrays, tasks, thunks,
references, external objects, and multi-threaded reference counts. It does not
provide partial replacements for the Init or Std libraries, libuv, OpenSSL,
process, filesystem, or thread services; those remain covered by the full
Emscripten profile until genuine WASI implementations are linked. The artifact
imports `clock_time_get` (and wasi-libc reactor startup imports `random_get`),
so the check cannot pass by relabeling the freestanding artifact. WASI 0.2/0.3
component packaging belongs above this core module as an adapter/WIT layer.

## Performance profile

All profiles use:

- `-O3` for aggressive scalar and loop optimization;
- full LTO at compile and link time so the primitive shim disappears into the
  generated LCNF code;
- function/data sections plus Wasm linker garbage collection;
- stripped output and omitted frame pointers.

The freestanding and WASI core profiles also remove exceptions and unwind
tables. Emscripten follows Lean's supported runtime settings:
`-fwasm-exceptions`, `-pthread`, growing memory, and the filesystem surface
needed by full `Init`. The thread-enabled artifact therefore requires
shared-memory-capable hosts; browsers need cross-origin isolation headers.

`-ffast-math` is intentionally disabled and floating-point contraction is
disabled. FIR validates exact floating-point bit patterns, so those semantic
changes are not acceptable performance optimizations.

## Toolchain pins

- Lean `4.32.0`, commit
  `8c9756b28d64dab099da31a4c09229a9e6a2ef35`;
- Emscripten `5.0.3`, emsdk commit
  `a620cf1d71c62dfdfbb0c01fe0a371e2af2dda6c`;
- wasi-sdk `33.0`, with per-platform release SHA-256 digests in
  `toolchain-pins.sh`.

Lean 4.32.0 contains two mismatched declarations in Emscripten-only unsupported
libuv stubs. `setup-emscripten.sh` applies the lane-local, signature-preserving
patch under `patches/`; it does not modify the FIR or Lean semantic surface.

## Running the freestanding profile

A compatible Clang/`wasm-ld` pair, Node, and the pinned Lean toolchain are
required. On Debian or Ubuntu, the linker can be installed into this
worktree's ignored `.deps` directory without root:

```sh
bash integration/lcnf-c-wasm/setup-lld-debian.sh
bash integration/lcnf-c-wasm/check.sh
```

Tool locations can be overridden explicitly:

```sh
FIR_WASM_CLANG=/path/to/clang \
FIR_WASM_LD=/path/to/wasm-ld \
bash integration/lcnf-c-wasm/check.sh
```

## Running the primary profiles

The Emscripten setup installs only into this worktree's ignored
`.deps/lcnf-c-wasm` directory. After the freestanding linker setup above, run:

```sh
bash integration/lcnf-c-wasm/setup-emscripten.sh
bash integration/lcnf-c-wasm/check-primary.sh

FIR_BROWSER=google-chrome \
  bash integration/lcnf-c-wasm/check-emscripten.sh
```

To build a module for Node or a cross-origin-isolated browser:

```sh
bash integration/lcnf-c-wasm/build-emscripten.sh \
  --root integration/lcnf-c-wasm \
  --out-dir _build/my-module \
  --export fir_lcnf_c_runtime_checksum \
  --start fir_lcnf_c_runtime_probe \
  integration/lcnf-c-wasm/RuntimeSmoke.lean
```

Load the emitted artifacts through the shared manifest loader:

```js
import { loadEmscriptenModule } from
  "./integration/lcnf-c-wasm/emscripten-loader.mjs";

const loaded = await loadEmscriptenModule(
  new URL("./_build/my-module/RuntimeSmoke.manifest.json", import.meta.url),
);
const checksum =
  loaded.exports.fir_lcnf_c_runtime_checksum(1000n, 17n);
```

The loader calls `fir_lcnf_c_initialize` before returning. A nonzero result
reports module-initialization or start-action failure. The public exports use
their declared Lean C ABI; scalar `@[export]` functions are the simplest host
boundary. Use `--extra-source` for local generated modules that must be linked
with the entry module. Deploy the `.manifest.json`, `.mjs`, and `.wasm` files
together; the manifest filenames are relative to its own URL.

## Measuring native versus Emscripten

`benchmark.sh` builds `RuntimeSmoke` once through the production Emscripten
driver and once as an optimized native executable, then records two distinct
phases:

- cold startup: whole-process elapsed time, plus an internal initialization
  boundary;
- steady execution: repeated initialized calls to
  `fir_lcnf_c_runtime_checksum`, excluding process and module startup.

The workload exercises array growth and folding, `Std.HashMap`, `Except`,
captured closures, and strings. Every native and Wasm result must match the
independent JavaScript oracle. Measured runs alternate
native/Emscripten and Emscripten/native order. Process warmups are stored
separately from measured rows.

Run the default six-pass report after the Emscripten setup:

```sh
bash integration/lcnf-c-wasm/benchmark.sh
```

Each invocation creates a fresh directory under
`_build/lcnf-c-wasm/performance/` and refuses to overwrite evidence. It
preserves:

- `report/raw-runs.jsonl`: every pass, sequence, command, checksum, elapsed
  time, RSS, and observable host thread count;
- `report/warmups.jsonl`: excluded process warmups;
- `report/identity-check.json`: before/after Git, tracked-diff, executable,
  input, and artifact identities;
- `report/report.json`: distributions, paired ratios, order effects, artifact
  sizes, toolchains, host metadata, and evidence classifications.

The report parses the Wasm memory import itself and requires a shared-memory
declaration for the threaded profile. Its `threadedRuntimeEnvelope` compares
the whole native process with Node plus the thread-enabled Emscripten runtime.
It deliberately does not claim that RSS, thread-count, or startup differences
are caused solely by pthread support; isolating that cost would require a
separately built, otherwise comparable single-threaded Lean runtime.

Timing is noisy evidence. Hashes, byte lengths, exact commands, and the Wasm
memory declaration are deterministic evidence. Defaults use one process
warmup, six order-balanced passes, 4,096 logical rounds per call, 128 measured
calls, and four in-process warmup calls. Override them explicitly when needed:

```sh
FIR_LCNF_C_WASM_PERF_OUT=/tmp/fir-perf-run \
FIR_LCNF_C_WASM_PERF_PASSES=10 \
FIR_LCNF_C_WASM_PERF_WARMUPS=2 \
FIR_LCNF_C_WASM_PERF_ROUNDS=8192 \
FIR_LCNF_C_WASM_PERF_ITERATIONS=128 \
FIR_LCNF_C_WASM_PERF_IN_PROCESS_WARMUPS=4 \
  bash integration/lcnf-c-wasm/benchmark.sh
```

Pass counts must be even. A report with fewer than six passes, no process
warmups, or a median steady sample below 10 ms is marked as screening
evidence. A relative median absolute deviation or absolute AB/BA order effect
of at least 10% marks timing as inconclusive. The raw rows and deterministic
artifact evidence remain valid.

## Running the experimental WASI profile

The frozen WASI setup also installs under `.deps/lcnf-c-wasm`:

```sh
bash integration/lcnf-c-wasm/setup-wasi-sdk.sh
bash integration/lcnf-c-wasm/check-wasi.sh
```

After all setups, primary plus experimental profiles can be checked together:

```sh
bash integration/lcnf-c-wasm/check-all.sh
```

Generated C, JavaScript glue, and Wasm artifacts are written under
`_build/lcnf-c-wasm/`. `FIR_WASM_BENCH_ROUNDS` changes scalar non-gating
throughput samples; `FIR_WASM_HEAP_BENCH_ROUNDS` changes the Emscripten and
WASI heap samples; and `FIR_WASM_CORE_BENCH_ROUNDS` changes the WASI
array/string/closure sample. `FIR_WASM_SCALAR_ARRAY_BENCH_ROUNDS` changes the
WASI byte-array/two-argument-closure sample. Correctness is checked
independently with fixed exact cases.
