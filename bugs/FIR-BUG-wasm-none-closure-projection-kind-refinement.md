---
id: FIR-BUG-wasm-none-closure-projection-kind-refinement
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-08-09
reproduction: integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean
regression: integration/talos/FirTalos/ConcreteRuntimeExamples.lean
---

# Summary

Generated closure projection requests the callee parameter's expected ABI kind,
but the concrete closure descriptor records the captured argument's actual ABI
kind and rejects the legal `object`/`tagged` to `tobject` refinements.

## Minimal reproduction

Partially apply a declaration whose fixed parameter is `tobject` to an argument
compiled as `object` or `tagged`, then invoke the resulting closure through the
generated saturated closure-dispatch chain.

## Exact commands

```sh
cd integration/talos
lake build FirTalos.ConcreteCompilerCorrectnessContract
```

## Expected semantics

`AbiKind.refines` permits precise heap-object and tagged arguments at a
representation-polymorphic `tobject` parameter. The later projection should
return the unchanged wasm32 word at the expected `tobject` boundary.

## Actual behavior

`compilePartialArguments` records the actual capture kind in the closure
descriptor, while `compileFixedClosureFields` emits `closureProj` with the
target parameter kind. `ClosureApplication.project` and
`projectClosureCapture` require those kinds to be exactly equal, so a legal
refinement is reported as `closureMetadataMismatch`.

## Proof or differential evidence

The certificate-free saturated-call proof obtains the application snapshot's
descriptor kinds from the allocation refinement, but generated projection is
indexed by `SaturatedClosureCallResolution.parameterKinds`. The available
compiler fact is pointwise `AbiKind.refines`, not equality; equality is false
for the two admitted precise-object cases.

## Semantic impact

Valid compiler-generated closures can trap before entering their callee, and
the concrete-host semantics is stricter than the resident projection helper,
which loads the same physical wasm32 slot.

## Classification and triage

This is a concrete Wasm ABI adaptation error. The sound boundary is to accept
exactly `AbiKind.refines actual expected = true`; that relation preserves the
physical Wasm value type and has explicit `ValueRel` promotion proofs.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

The concrete live-object and post-application projection boundaries now accept
exactly `actualKind.refines expectedKind`, read the lane at its immutable
descriptor kind, and widen the proof relation at the generated result kind.
An executable tagged-to-`tobject` closure-application guard checks the complete
allocation, ownership-taking matcher, and projection path.
