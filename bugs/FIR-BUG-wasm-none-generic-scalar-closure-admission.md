---
id: FIR-BUG-wasm-none-generic-scalar-closure-admission
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-08-02
reproduction: Fir/Validation/Corpus.lean
regression: integration/talos/FirTalos/ConcreteCompilerCorrectnessContract.lean
---

# Summary

The public source-to-Wasm compiler blocks the thirty-two-case scalar-closure
admission, rejecting representatives from both the fixed-width and Boolean
families as `unsupportedCode` after closure-application ownership was linked
through the executable W7 adapter.

## Minimal reproduction

Remove `wasm-generation-pending` from either
`captured-int16-partial-max` or `captured-bool-partial-true`, then select that
case with the native/LCNF/V8 validation plan. Both source entries compile and
execute through native Lean and final LCNF, but the Wasm provider stops while
validating the compiler-produced LCNF program.

## Exact commands

```text
lake --rehash build Fir.Validation fir-native-oracle
python3 scripts/validate_interpreters.py \
  --plan validation-plans/native-lcnf-v8-scalars.json \
  --tag entry-abi \
  --out-dir _build/validation-v8-closure-entry-abi
python3 scripts/validate_interpreters.py \
  --plan validation-plans/native-lcnf-v8-scalars.json \
  --case captured-bool-partial-true \
  --case captured-bool-partial-false \
  --out-dir _build/validation-v8-closure-bool
```

## Expected semantics

After `CLOSURE-APPLICATION-OWNERSHIP` is linked through the LCNF proof, W6
refinement, and W7 execution adapter, the thirty fixed-width generic closure
entries and two Boolean closure entries should compile to Wasm and agree with
the Lean native oracle in V8. Their final LCNF traces already exercise the
required `box`, `pap`, closure invocation, `unbox`, ownership, and return
paths.

## Actual behavior

The Wasm provider fails before emitting a module. The first fixed-width case
reports:

```text
Wasm compilation failed for captured-int16-partial-max:
  Fir.Wasm.Emit.Source.CompileError.lowering
    (Fir.Wasm.SupportedLoweringError.validation
      (Fir.Wasm.ValidationError.unsupportedCode
        `Fir.Validation.Corpus.Source.capturedInt16Partial))
```

The Boolean probe fails identically for
`Fir.Validation.Corpus.Source.capturedBoolPartial`. V8 is never started.

## Proof or differential evidence

The fixed-width build log is retained under
`_build/validation-v8-closure-entry-abi/lean-wasm-semantic/build/`; the Boolean
log is under `_build/validation-v8-closure-bool/lean-wasm-semantic/build/`.
The corresponding source cases pass the existing native/LCNF comparison with
their exact interpreter traces. No comparison matrix is published for either
failed probe because product generation stops first.

## Semantic impact

The linked ownership adapter cannot yet be exercised by the thirty-two
queued scalar-closure fixtures in a real Wasm engine. Removing their admission
fence makes the root validation gate fail during product generation, leaving
the native-to-V8 closure-application claim unvalidated.

## Classification and triage

The failure is in the W7 public compiler's supported-lowering boundary, before
the semantic host or V8 executes. The executable ownership adapter itself has
separate unit and artifact coverage. Triage should identify which generic or
boxed closure form causes `supportedDecl` to reject these otherwise executable
final-LCNF entries; validation should not replace the generic fixtures with a
weaker monomorphic matrix.

## Workaround

Keep the thirty-two cases behind `wasm-generation-pending` until the public
compiler emits them and the focused external-engine probes pass.

## Upstream tracking

none

## Resolution and regression

The W6 lowerer now derives an effective `.erased` parameter kind when a raw
`tobject` declaration parameter is used only by exact forwarding to a
statically known erased parameter. The admission is structural: it neither
matches `_boxed` names nor adds `erased ≤ tobject` to the ABI refinement
order. Partial-application descriptors, declaration locals, supported
lowering, and closure dispatch all consume the same effective parameter-kind
calculation.

`UInt8` boxing now selects `.tagged` in `boxResultKind`. The concrete boxing
refinement theorem proves this precise result from the existing 63-bit tagged
bound, and the general `BoxSupported` direct-let simulation consumes the
representation-sensitive result kind.

The contract module contains an executable synthetic final-LCNF facade
fixture. The real unfenced validation command

```text
python3 scripts/validate_interpreters.py \
  --provider-config validation-providers/lean-wasm-semantic-scalars.json \
  --adapter-config validation-adapters/v8-scalars.json \
  --pair native:lcnf --pair native:v8 --pair lcnf:v8 \
  --tag wasm-generation-pending \
  --out-dir _build/w6-scalar-closure-admission-full-2
```

passes all 32 cases and all 96 directed comparisons with zero findings. The
corpus tag remains for the integration/test-fixture owner to remove when this
W6 slice lands.
