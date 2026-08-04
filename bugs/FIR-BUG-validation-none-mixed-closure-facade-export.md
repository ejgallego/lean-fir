---
id: FIR-BUG-validation-none-mixed-closure-facade-export
status: candidate
classification: validation-harness
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-08-02
reproduction: FirValidationWasm.lean
regression: none
---

# Summary

Validation rejects a mixed floating-argument closure module because the
bit-exact transport pass correctly exports both the source entry and its
integer-lane facade, while the provider still requires an exact singleton
export array.

## Minimal reproduction

Compile either `mixed-closure-capture-once` or
`mixed-closure-capture-twice` with the semantic Wasm provider. Their source
entries take `Float32` and `Float` arguments, so
`Fir.Wasm.Emit.BitExactFloat.install` preserves the source export and adds the
canonical `_fir_bit_exact` facade.

## Exact commands

```text
python3 scripts/validate_interpreters.py \
  --provider-config validation-providers/lean-wasm-semantic-scalars.json \
  --adapter-config validation-adapters/v8-scalars.json \
  --pair native:lcnf \
  --pair native:v8 \
  --pair lcnf:v8 \
  --case mixed-closure-capture-once \
  --case mixed-closure-capture-twice \
  --out-dir _build/validation-v8-mixed-closure
```

## Expected semantics

The provider should verify the source export plus the canonical bit-exact
facade, publish the facade selected by the checked manifest, and execute the
module in V8 without exposing floating payloads to JavaScript numeric
coercion.

## Actual behavior

Source lowering and facade installation succeed. Product generation then
stops at `FirValidationWasm.lean` with:

```text
Wasm module does not export Fir.Validation.Corpus.Source.captureMixedClosure
```

The source entry is present, but `artifact.module.exports` also contains the
required bit-exact facade, so the exact equality check against
`#[validationCase.entry]` is false. V8 is never started.

## Proof or differential evidence

The provider build log is retained under
`_build/validation-v8-mixed-closure/lean-wasm-semantic/build/`. The same two
fixtures pass native/LCNF comparison with exact 36- and 62-transition traces,
including one-use and repeated shared closure application.

## Semantic impact

Validation cannot currently triangulate source entries that combine closure
ownership with floating parameters, even though the compiler emits the
bit-exact transport facade required for safe V8 invocation. This blocks the
mixed-layout ownership baseline from exercising the linked W7 adapter.

## Classification and triage

The module and facade follow the released bit-exact transport contract. The
failure is the validation provider's stale singleton-export assertion. Repair
should validate the source-plus-facade export shape and require the manifest to
select the verified facade; it must not suppress the transport wrapper or
compare floating values through JavaScript numbers.

## Workaround

Keep the mixed-closure cases behind `wasm-generation-pending` until the
provider accepts and executes the canonical facade path.

## Upstream tracking

none

## Resolution and regression

unresolved
