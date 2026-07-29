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

## Runtime profiles

The LCNF-to-C frontend is shared. Runtime selection is a link profile, not a
second compiler:

| Profile | Host contract | Current acceptance fixture |
| --- | --- | --- |
| `freestanding` | `wasm32-unknown-unknown`, no imports or libc | raw `UInt64` expression and tail loop |
| `emscripten` | browser/Node ES module plus pinned `libleanrt`, `libInit`, and `libStd` | lists, arrays, strings, closures, `Except`, `Std.HashMap`, and real `IO.eprintln` |
| `wasi` | WASI Preview 1 reactor (`wasm32-wasip1`) | the same scalar C plus a real monotonic-clock import |

`Smoke.lean` exports two raw `UInt64` functions. One is a scalar expression;
the other is a compiler-lowered tail loop. `HeapSmoke.lean` dynamically
allocates boxed `UInt64` values and list constructors, consumes the list, and
returns an exact checksum. `RuntimeSmoke.lean` widens that coverage to a
captured-closure pipeline, mutable arrays, strings, success/error `Except`
branches, and a `Std.HashMap`, then exposes a real `Init` I/O probe.

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

The WASI artifact is intentionally a Preview 1 core-module reactor. It imports
`clock_time_get` (and the SDK reactor startup imports `random_get`), so the
check cannot pass by relabeling the freestanding artifact. WASI 0.2/0.3
component packaging belongs above this core module as an adapter/WIT layer.
Porting heap-bearing Lean runtime services to WASI is separate from that
packaging step and must preserve the same object and observation contracts.

## Performance profile

All profiles use:

- `-O3` for aggressive scalar and loop optimization;
- full LTO at compile and link time so the primitive shim disappears into the
  generated LCNF code;
- function/data sections plus Wasm linker garbage collection;
- stripped output and omitted frame pointers.

The freestanding and WASI scalar profiles also remove exceptions and unwind
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

## Running Emscripten and WASI

Both setups install only into this worktree's ignored `.deps/lcnf-c-wasm`
directory:

```sh
bash integration/lcnf-c-wasm/setup-emscripten.sh
bash integration/lcnf-c-wasm/check-emscripten.sh

FIR_BROWSER=google-chrome \
  bash integration/lcnf-c-wasm/check-emscripten.sh

bash integration/lcnf-c-wasm/setup-wasi-sdk.sh
bash integration/lcnf-c-wasm/check-wasi.sh
```

After both setups, all three profiles can be checked together:

```sh
bash integration/lcnf-c-wasm/check-all.sh
```

Generated C, JavaScript glue, and Wasm artifacts are written under
`_build/lcnf-c-wasm/`. `FIR_WASM_BENCH_ROUNDS` changes scalar non-gating
throughput samples; `FIR_WASM_HEAP_BENCH_ROUNDS` changes the Emscripten heap
sample. Correctness is checked independently with fixed exact cases.
