---
id: FIR-BUG-wasm-none-generic-object-join-admission
status: fixed
classification: compiler
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-08-09
reproduction: Fir/Wasm/WellFormed.lean
regression: Fir/Wasm/Examples.lean
---

# Summary

FIR rejects a final-LCNF join argument whose generic Lean object-family ABI is
physically call-compatible with the join parameter but does not directionally
refine it.

## Minimal reproduction

Capture `VersoSlides.Pretty.formatRenderedForRuntime` after replacing its
compiler-generated `StateT` dictionary with named explicit state functions.
The resulting final LCNF passes an object-family value through a join where
the actual and expected kinds are Lean-compatible but `actual.refines
expected` is false.

## Exact commands

Run the final-LCNF closure capture and `Fir.Wasm.compileProgram` for
`VersoSlides.Pretty.formatRenderedForRuntime` under Lean 4.32. Compilation
stops at `supportedJumpArgs`; if admission alone is relaxed, lowering stops at
`compileJump` with `jump argument does not refine its join parameter ABI`.

## Expected semantics

Join transfer should use the same generic physical object-family convention
as direct calls, results, and symbolic stack validation: `object`, `tagged`,
and `tobject` are represented in the same Wasm lane and are mutually
Lean-compatible. Scalar and erased lanes remain exact.

## Actual behavior

Both `supportedJumpArgs` and `compileJump` require directional
`AbiKind.refines`, rejecting the compiler-produced object-family transfer.

## Proof or differential evidence

Changing both checks to `AbiKind.leanCompatible` admits and lowers the exact
captured closure. The resulting closed, zero-import module matches native Lean
on nine Flat rendering cases, including nested tags, UTF-8 byte offsets,
nonzero initial columns, a 64-bit tag, a 2,047-node balanced tree, and a
256-KiB Unicode result.

## Semantic impact

Valid final LCNF using generic object-family values at local joins cannot be
compiled even though the same transfer is accepted at named-call and result
boundaries. This blocks the FIR-native Verso Flat package.

## Classification and triage

This is a compiler admission/lowering inconsistency. The proposed contract
change is shared and must be reviewed by the integration and W6 owners before
landing; it does not change the directional semantic refinement relation.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Join support checking and lowering now use the same `AbiKind.leanCompatible`
relation already used by ordinary compiler-produced calls, results, and the
symbolic stack. The focused regression lowers and validates a coarse
`tobject` argument passed to a precise `object` join, while existing scalar
and erased mismatch regressions remain rejected. The former guard-specific
negative case is retained as a positive regression showing that an unrelated
sharing guard does not define the generic object-family calling convention.
