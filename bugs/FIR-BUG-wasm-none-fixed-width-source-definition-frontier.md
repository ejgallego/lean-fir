---
id: FIR-BUG-wasm-none-fixed-width-source-definition-frontier
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-08-12
reproduction: integration/lean-zip/level1-smoke.mjs
regression: integration/lean-zip/level1-smoke.mjs
---

# Summary

The generic fixed-width resident layer internalizes supported external
declarations but leaves the same supported API as captured source definitions,
causing `UInt32.ofNat` to execute a generic arbitrary-precision power/modulo
path for every conversion.

## Minimal reproduction

The final LCNF for `Zip.Wasm.compressLevel1` contains:

```lean
def UInt32.ofNat (n : Nat) : UInt32 :=
  UInt32.ofBitVec (BitVec.ofNat 32 n)
```

and `BitVec.ofNat 32 n` computes `n % 2^32`. The resident fixed-width layer
already has the exact signature-checked `UInt32.ofNat` operation, but selects
it only when the declaration is an import. The captured source definition
therefore remains on the hot path.

## Exact commands

```sh
cd integration/lean-zip
lake env lean ProbeLevel1.lean

cd ../..
lake build Fir.Wasm.Emit.ResidentFixedWidth
```

## Expected semantics

Supported fixed-width APIs should use the same resident implementation whether
final LCNF presents them as externals or as ordinary source definitions. The
implementation validates the Natural and truncates its low word, matching
`BitVec.ofNat 32` followed by `UInt32.ofBitVec`.

## Actual behavior

The generic Nat implementation repeatedly materializes `2^32` and performs
long division. A 64-byte input takes about 20 seconds and advances the
monotonic frontier by about 1.33 GB. A 1,024-byte repeated input reaches
frontier `0xffff_ffd8` after about 142 seconds and traps in `fir_heap_alloc`.

## Proof or differential evidence

The trap stack is
`BitVec.ofNat → UInt32.ofNat → Nat.pow → Nat.mul → fir_heap_alloc`.
The native Lean oracle completes the same cases. Inputs below three bytes avoid
the direct-head path and therefore do not reproduce the exhaustion.

## Semantic impact

Valid Level-1 compression inputs can exhaust the wasm32 address space. The
same presentation mismatch can bypass resident implementations for any
supported fixed-width definition retained as source code.

## Classification and triage

This is a generic resident-link selection discrepancy, not a lean-zip-specific
source problem. Selection must accept exactly one checked declaration provider:
either an external import or a lowered source function with the expected ABI.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

The generic fixed-width linker now accepts exactly one provider with the
expected ABI: either an external import or a lowered source definition. Calls
to either presentation are rewritten to the same resident helper. A focused
symbolic guard covers source-defined `UInt32.ofNat`; the complete Level-1
differential covers the real captured definition and its ExplicitBoxing
wrapper. On the same 64-byte repeated input, the raw Wasm call improved from
about 19.7 seconds and 1.33 GB of frontier growth to about 10.5 seconds and
189 MB. More importantly, the former 1,024-byte wasm32 exhaustion is gone and
the complete 4 KiB/8 KiB Level-1 differential finishes successfully.
