---
id: FIR-BUG-wasm-none-generated-row-context-coherence
status: fixed
classification: compiler
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 871619fb26983c7644cbcf2f49ca18a46d27ece5
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-08-09
reproduction: integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean
regression: integration/talos/FirTalos/ConcreteCompilerCorrectnessContract.lean
---

# Summary

`ConcreteGeneratedInternalDeclaration` retained the production function,
parameter, and call-index rows, but did not retain that its declaration-local
`Context` uses the same source program and canonical cached-declaration table.

## Minimal reproduction

Attempt to prove generated declaration correctness by structural induction on
`ReuseCapacityDirectHereditaryCodeEvaluates`. At a nested direct call, the
callee derivation exposes a `LoweredInternalDeclaration` under the current
context. Selecting its matching production row requires
`context.program = program` and the corresponding cache-table equality, but
neither follows from the old generated-row structure.

## Exact commands

```text
make talos-setup
make talos-check
```

## Expected semantics

Every generated internal row selected from one successful
`lowerSupported`/`adapt` pipeline should retain the program and canonical
cache-name equalities used to construct its declaration-local context.

## Actual behavior

The equalities were proved transiently by both production selectors and then
discarded. Non-recursive clients did not need them, but recursive selection
could not establish that a nested source row belongs to the same pipeline.

## Proof or differential evidence

The direct-call case of
`codeWP_of_reuseCapacityDirectHereditaryCodeEvaluates_generated` reaches the
real nested source row and exact source evaluation but cannot apply
`exists_ofSupportedPipelineAtLowered` without the discarded context facts.

## Semantic impact

This is a proof-boundary omission, not an executable compiler discrepancy.
Both production selectors already construct the required equalities from the
real lowering context.

## Classification and triage

Strengthen `ConcreteGeneratedInternalDeclaration` with the two static context
equalities and populate them in the existing production selectors. Do not add
a call-site certificate or weaken nested production selection.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Generated internal rows now retain `context.program = program` and
`context.cachedDeclarations = cachedDeclarationNames program`. Both facts are
constructed from the existing production selector equations, and the
compiler-correctness contract checks that they are available to recursive
clients.
