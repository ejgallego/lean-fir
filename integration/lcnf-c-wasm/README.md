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

## Current vertical slice

`Smoke.lean` exports two raw `UInt64` functions. One is a scalar expression;
the other is a compiler-lowered tail loop. `check.sh` asks the pinned Lean
4.32.0 frontend to emit C, compiles that C and the scalar runtime with Clang,
links a freestanding Wasm module, and executes exact differential checks in
Node.

The scalar runtime is deliberately narrow. It implements only the primitive
operations referenced by this fixture. Heap-bearing values, strings, arrays,
closures, IO, and the complete Lean runtime belong to the Emscripten runtime
tier and must not be silently added to this freestanding profile.

## Performance profile

The build uses:

- `-O3` for aggressive scalar and loop optimization;
- full LTO at compile and link time so the primitive shim disappears into the
  generated LCNF code;
- function/data sections plus Wasm linker garbage collection;
- stripped output, omitted frame pointers, and no exception or unwind tables;
- no C runtime, entrypoint, or unused Lean module initializer.

`-ffast-math` is intentionally disabled and floating-point contraction is
disabled. FIR validates exact floating-point bit patterns, so those semantic
changes are not acceptable performance optimizations.

## Running

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

Generated C and Wasm artifacts are written under
`_build/lcnf-c-wasm/`. `FIR_WASM_BENCH_ROUNDS` changes the non-gating
throughput sample; correctness is checked independently with fixed cases.

The next tier pins Emscripten and the matching Lean runtime sources so
heap-bearing final LCNF can use the same C-emission edge without weakening the
runtime contract.
