# WebAssembly artifact generation

FIR has two native paths from Lean's final saved impure LCNF to an executable
WebAssembly artifact. They share the compiler checkpoint, but they deliberately
do not share a lowering, runtime, or artifact-loading contract.

The thin [build-example catalog](build-examples.md) lists the accepted
consumer packages and points to the authoritative fixture registries. It does
not duplicate their inventories.

Here, **native Wasm generation** means that the repository produces a `.wasm`
artifact directly from Lean compiler output. It does not mean the host-native
executables used as differential-test oracles.

```text
                                      FIR-native symbolic path
                                    /-> Fir.Wasm lowering
Lean source -> final impure LCNF ---+   -> symbolic Wasm -> encoder/linker
                                    |   -> raw .wasm + FIR manifest
                                    |
                                    | compiler-native C path
                                    `-> Lean LCNF C emitter
                                        -> optimized C
                                        -> Emscripten/LLVM
                                        -> .wasm + ES module + manifest
```

## Choosing a path

| | FIR-native symbolic Wasm | Compiler-native C/Emscripten Wasm |
| --- | --- | --- |
| Entry package | `integration/talos/artifact` | `integration/lcnf-c-wasm` |
| Lowering | FIR's explicit `Fir.Wasm` instruction and module surface | Lean's upstream `LCNF.emitC`, then the LLVM WebAssembly backend |
| Runtime strategy | Semantic imports while operations migrate to the W6/W7 concrete resident runtime | Pinned Lean `libleanrt`, `libInit`, and `libStd` linked into an Emscripten module |
| Primary purpose | Inspectable lowering, executable semantics, concrete-runtime refinement, and resident-runtime generation | Broad executable coverage and an optimized alternative deployment path |
| Current host boundary | Raw WebAssembly plus an explicit semantic or concrete host | Verified ES-module loader for Node or a cross-origin-isolated browser |
| Proof status | The path on which FIR's symbolic and concrete Wasm proof obligations are stated | Differentially checked against native Lean and independent JavaScript oracles; not a substitute for W6/W7 refinement theorems |
| Best current fit | Backend development, proofs, deterministic fixtures, and runtime migration | Programs using realistic Lean `Init`/`Std` features and performance experiments |

Use the FIR-native path when the Wasm instruction sequence, import surface, or
runtime refinement is the object of study. Its `fir-wasm-artifact` executable
emits deterministic corpus and resident-runtime modules:

```sh
lake -d integration/talos/artifact exe fir-wasm-artifact \
  literal /tmp/literal.wasm
```

Use the compiler-native path when the goal is to run the same compiler
checkpoint through Lean's supported C/runtime ecosystem:

```sh
bash integration/lcnf-c-wasm/build-emscripten.sh \
  --root integration/lcnf-c-wasm \
  --out-dir _build/my-module \
  --export fir_lcnf_c_runtime_checksum \
  integration/lcnf-c-wasm/RuntimeSmoke.lean
```

The Emscripten build emits a deterministic manifest beside its `.mjs` and
`.wasm` files. Consumers must load that bundle through
`emscripten-loader.mjs`, which verifies artifact lengths and SHA-256 digests
before initialization.

## One logical `prettyM` API, two packages

Both paths now package a `Std.Format.prettyM` facade. The packages remain
independent at the artifact boundary:

| | FIR-native package | C/Emscripten package |
| --- | --- | --- |
| Adapter | `prettyM-browser-adapter.mjs` | `prettyM-emscripten-adapter.mjs` |
| Physical input | Raw Lean objects built in module-owned memory | One private binary request copied through Emscripten `HEAPU8` |
| Runtime | Zero-import resident runtime | Pinned full Lean runtime/Init/Std |
| Loader | Direct `WebAssembly` package metadata | Verified Emscripten manifest loader |
| Lifetime | Monotone module-owned arena | C-owned request/result buffers plus Lean runtime allocations |

At the JavaScript level both adapters accept
`lean-4.33-Std.Format.compact/v1` and return
`{ trace: { text, events }, timings, memory }`. This is the common client
surface; it does not imply a common raw Wasm ABI or interchangeable manifests.

Build the C/Emscripten package and run the exact two-engine trace comparison:

```sh
integration/lcnf-c-wasm/package-prettyM-emscripten.sh
```

The check covers Unicode, line flattening, fill groups, alignment, signed
nesting, arbitrary-precision tags and widths, nonzero starting columns, and
repeated calls. See the
[LLVM-backed C/Emscripten client guide](../integration/lcnf-c-wasm/prettyM-emscripten-package/README.md)
and the
[FIR-native package guide](../integration/talos/artifact/prettyM-package/README.md)
for client examples.

The LLVM-backed guide is copied into every generated C/Emscripten package. It
identifies the minimal deployment set, gives a standalone Node client, lists
the browser isolation headers required by the threaded build, and defines the
versioned request, result, lifetime, integrity, and resource-limit contracts.

## What the common checkpoint does and does not guarantee

Both paths consume final impure LCNF after Lean has made representation,
ownership, reference-counting, and reset/reuse operations explicit. That makes
cross-path differential testing meaningful, but it does not make the emitted
artifacts interchangeable:

- FIR lowering maps LCNF into its own symbolic WebAssembly ABI and incrementally
  links Wasm-resident runtime helpers.
- C emission maps LCNF operations to the Lean C ABI; Emscripten supplies the
  WebAssembly ABI, libc surface, threads, exceptions, and JavaScript module
  wrapper.
- Each path retains its own manifest and loader contract. A consumer must not
  feed one path's manifest to the other path's host.
- Native Lean executables remain semantic or performance references. They are
  not another WebAssembly generation path.

The C package also contains a narrow freestanding profile and a frozen WASI
Preview 1 core-runtime profile. Emscripten is the primary realistic C route.
WASI remains an explicit, green compatibility boundary rather than a
short-term effort to reproduce `Init`, `Std`, libuv, filesystem, and threading
support.

## Validation

The paths have different acceptance suites:

```sh
# FIR-native symbolic and resident-runtime artifacts
bash integration/talos/artifact/check.sh

# Compiler-native freestanding and Emscripten profiles
bash integration/lcnf-c-wasm/check-primary.sh

# Exact prettyM comparison through both package facades
bash integration/lcnf-c-wasm/package-prettyM-emscripten.sh

# Frozen optional WASI boundary
bash integration/lcnf-c-wasm/check-wasi.sh
```

Repository-wide changes still finish with `make check` and, for either Wasm
path, `make talos-check`.

For implementation details, see the
[FIR artifact package](../integration/talos/artifact/README.md), the
[LCNF-to-C package](../integration/lcnf-c-wasm/README.md), and the
[LCNF-to-C compiler guide](lcnf-to-c.md).
