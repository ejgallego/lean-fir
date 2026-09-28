# Resident Nat multiplication differential

Run from the FIR worktree, using its accepted Lean toolchain and local scratch:

```sh
mkdir -p .deps/tmp
export TMPDIR="$PWD/.deps/tmp"
export LAKE_CACHE_DIR="$(bash scripts/fir-lake-cache-path.sh)"
export LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true
lake build Fir.Wasm.Emit.ResidentNatArithmetic
lake env lean --run Fir/Wasm/Emit/Tests/NatMultiplication.lean .deps/nat-multiplication.wasm
node Fir/Wasm/Emit/Tests/nat-multiplication.mjs .deps/nat-multiplication.wasm
```

The diagnostic module installs the production arithmetic, allocator and recycler.
It only adds diagnostic exports for the generic multiply and decrement helpers.
The existing arithmetic regression runs first. The focused test then compares
generic and public multiplication with JavaScript BigInt as an independent test
oracle (never a runtime import), validates canonical headers and borrowed inputs,
and covers immediate/promoted/big boundaries, maximal carry, unequal lengths,
squares, aliased/shared operands, and malformed input rejection.

Dirty-reuse loops preserve the recycler link but poison the rest of each dead
payload. Both full and normalized result sizes must plateau after warmup, with
frontier and memory capacity reported separately. This is not a claim that the
instance arena shrinks: released exact extents become available for reuse.
Promoted values retain the existing persistent representation; they are not
included in the reclaimable warm loop.

The implementation uses 32-bit digits within unchanged 64-bit limbs. The inner
unsigned 64-bit accumulator is bounded by `(2^32 - 1)^2 + 2*(2^32 - 1)`;
its high word is the carry. Nonzero operands need at most one fewer 64-bit limb
than the sum of their lengths. Exact-extent canonicalization therefore needs
at most one copy; single-limb output uses the existing `makeNatural` helper.
No under-construction buffer reaches a natural-number consumer. Retirement uses
the ordinary header-based decrement and recycler; input ownership is unchanged.

Full root/Talos/artifact gates and any consumer package/campaign are separate.
The emitted digest identifies this diagnostic, not a client release. The client
owns matched end-to-end performance qualification; no old RC2 timings are used
to claim a speedup on 4.34.1. Full multiplication refinement remains W6 work.

After committing the candidate, create a self-contained local diagnostic package
with the existing immutable-package utility (no canonical pointer is moved):

```sh
.deps/lcnf-c-wasm/emsdk/upstream/bin/wasm-opt .deps/nat-multiplication.wasm -O3 -o .deps/nat-multiplication-opt.wasm
cp .deps/nat-multiplication.wasm.json .deps/nat-multiplication-opt.wasm.json
node Fir/Wasm/Emit/Tests/nat-multiplication.mjs .deps/nat-multiplication-opt.wasm
node Fir/Wasm/Emit/Tests/package-nat-multiplication.mjs .deps/nat-multiplication.wasm .deps/nat-multiplication-opt.wasm .deps/packages
```

The package includes both binaries, manifest, BUILD identities, complete checksums
and a standalone Node smoke. Its diagnostic exports are not a consumer package ABI.
