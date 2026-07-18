---
id: FIR-BUG-wasm-none-bool-argument-scalar
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-07-18
reproduction: Fir/Validation/Corpus.lean#branch-nat
regression: Fir/Wasm/Emit/SourceExamples.lean
---

# Summary

The corpus-to-Wasm invocation adapter encodes a Boolean argument as a tagged
object even when Lean 4.32 lowers the generated function parameter to scalar
`UInt8`.

## Minimal reproduction

Compile the `branch-nat` corpus fixture after admitting scalar `UInt8` case
discriminators. Its final-impure entry parameter has ABI kind `uint8`, while
the backend-neutral validation encoder supplies `Value.object (.tagged 1)`.

## Exact commands

From a clean checkout containing the scalar-case lowering:

```sh
FIR_VALIDATION_CASES='["branch-nat"]' \
FIR_VALIDATION_OUT_DIR=/tmp/fir-scalar-case-probe \
lake env lean FirValidationWasm.lean
```

## Expected semantics

The schema-directed Wasm invocation boundary should represent Boolean `true`
as scalar `UInt8` value `1` when the checked entry parameter kind is `uint8`.
This is the same representation already accepted for compiler-produced
Boolean results.

## Actual behavior

Artifact construction fails before Wasm execution with:

```text
argument Value.object (ObjectRef.tagged 1) does not match ABI kind AbiKind.uint8
```

## Proof or differential evidence

`WasmSupported` and scalar-case lowering succeed for `branch-nat`; manifest
construction is the next boundary and rejects the protocol encoder's tagged
argument against the lowered function signature.

## Semantic impact

Compiler-generated functions taking an unboxed `Bool` cannot participate in
native-to-V8 validation even though both their LCNF body and generated Wasm
are inside the admitted scalar-case fragment.

## Classification and triage

This is classified as `wasm-adapter`: the backend-neutral validation encoder
intentionally uses a tagged representation, while the Wasm adapter already
has the checked parameter ABI kind needed to select the scalar representation.
No compiler or source-semantic discrepancy is indicated.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

The Wasm source adapter now checks every validation argument schema against
the lowered parameter ABI and normalizes protocol Boolean tags zero and one
to scalar `UInt8` exactly when that ABI requires it. Other scalar widths and
invalid Boolean tags remain rejected. `Fir/Wasm/Emit/SourceExamples.lean`
permanently checks the successful `true` normalization and the invalid-tag
failure, while `branch-nat` and `branch-nat-false` exercise both values in the
native-to-V8 matrix.
