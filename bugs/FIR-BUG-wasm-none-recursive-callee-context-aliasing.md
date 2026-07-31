---
id: FIR-BUG-wasm-none-recursive-callee-context-aliasing
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: e58ba9e88dcae33bb744c080251f596f124f360a
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-07-31
reproduction: integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean
regression: integration/talos/FirTalos/ConcreteCompilerCorrectnessContract.lean
---

# Summary

The recursive direct-call, saturated-closure, and lazy-initializer proof
interfaces identified every callee's compiler context with its caller's
context even though production lowering computes declaration-local kinds and
join tables independently.

## Minimal reproduction

Attempt to construct `DirectInternalCallDeclarationInduction` or
`LazyCacheInternalHereditaryDeclarationInduction` from two distinct generated
declarations. Before the repair, the callee package was required at the
caller's `Fir.Wasm.Context`. This incorrectly required the callee
`CodeAdapted`, `LocalLayoutAligned`, and `CodeWP` evidence to use the caller's
`localKinds` and `joins`.

## Exact commands

```text
make talos-setup
make talos-check
```

The contract module separately checks transport of an exact callee
`SourceCodeResult` to a coherent caller context.

## Expected semantics

Every generated declaration has its own compiler context, containing the local
ABI rows and transient join points computed for that body. Declarations in one
generated module share the source program and lazy-cache declaration table.
Recursive correctness should preserve the shared fields while retaining the
callee's actual declaration-local fields.

## Actual behavior

The hereditary interfaces used one `context` index for both the caller source
step and the callee declaration theorem. This was harmless for hand-written
same-context assumptions but blocked construction from `lowerDecl` output for
ordinary programs whose declarations have different local layouts.

## Proof or differential evidence

`Fir.Wasm.lowerDecl` constructs a fresh context from each declaration's
parameters and collected locals. Generalizing the hereditary package exposed
one genuine transport obligation in lazy misses: the source call decomposition
compares the caller's structured miss with the callee's exact source result.
Both canonical machine states depend only on `context.program`, so equal
programs transport `SourceCodeResult`; neither local kinds nor joins occur in
that proof.

## Semantic impact

No generated Wasm discrepancy is known. The old interface prevented the W6
recursive program theorem from being instantiated with production compiler
evidence and risked hiding the distinction by assuming an impossible shared
local layout.

## Classification and triage

This is a W6 proof-interface defect. It is not a compiler certificate or a
source-semantics change. The repair makes the production distinction explicit
without weakening the caller source step, target execution theorem, cache
relation, or representation refinement.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

`DeclarationContextsCoherent` records equality of the source program and
module-wide cache declaration table while deliberately omitting `localKinds`
and `joins`. Direct named calls, saturated closure dispatch, and lazy misses
now existentially return a coherent callee context and retain all hereditary
correctness at that context.
`DeclarationContextsCoherent.sourceCodeResult` proves the only semantic
transport needed by lazy publication. The compiler-correctness contract guards
that transport boundary.
