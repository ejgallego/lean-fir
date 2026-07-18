---
id: FIR-BUG-wasm-none-dependency-export-surface
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-07-18
reproduction: FirValidationWasm.lean
regression: Fir/Wasm/Emit/SourceExamples.lean
---

# Summary

Source artifact compilation exports captured dependency declarations in addition
to the selected entrypoint, violating the single-entry validation artifact
contract.

## Minimal reproduction

Compile the `boxed-uint32` validation case. Its entry
`Fir.Validation.Corpus.Source.boxedUInt32` captures the noinline dependency
`Fir.Validation.Corpus.Source.polyId`; the emitted module exports both functions.

## Exact commands

From the repository root:

```sh
python3 scripts/validate_interpreters.py \
  --case boxed-uint32 \
  --plan validation-plans/native-v8-scalars.json \
  --out-dir _build/validation-v8-w5-foundation
```

## Expected semantics

Dependencies captured to implement the selected entry remain internally
callable, while the reusable validation artifact exposes exactly the requested
entry export.

## Actual behavior

`Fir.Wasm.lowerSupported` exports every lowered declaration. The source emitter
passes that export list through unchanged, so `FirValidationWasm.lean` rejects
the module before V8 execution with `Wasm module does not export
Fir.Validation.Corpus.Source.boxedUInt32` because its exact singleton-export
invariant fails.

## Proof or differential evidence

The native-to-V8 validation build fails on the first dependency-bearing W5 case.
The retained build log is
`_build/validation-v8-w5-foundation/v8/build/stdout.jsonl`.

## Semantic impact

Every otherwise-supported validation case requiring captured helper
declarations is blocked from the independent Wasm/V8 lane, including the W5
boxing case and later direct-call/closure cases.

## Classification and triage

The captured functions and internal calls are valid; only the emitted artifact
export surface is too broad. This is classified as a Wasm adapter issue rather
than a Lean compiler or FIR semantic discrepancy.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

`Fir.Wasm.Emit.Source.compileModule` now retains captured dependencies as
internal functions while replacing the lowerer's broad export list with the
requested entry singleton before binary encoding. `SourceExamples.lean`
compiles `boxedUInt32` with `polyId`, checks that only `boxedUInt32` is exported,
and checks that `polyId` remains present internally. The `boxed-uint32`
native-to-V8 run then passes through the emitted dependency call.
