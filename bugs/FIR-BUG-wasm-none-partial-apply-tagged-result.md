---
id: FIR-BUG-wasm-none-partial-apply-tagged-result
status: confirmed
classification: compiler
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: source-closure-test
first-seen: 2026-07-20
reproduction: integration/lean-zip/ProbeLevel1.lean
regression: Fir/Wasm/Emit/ResidentClosureAllocation.lean
---

# Summary

Lean's generic final-LCNF pipeline emits `.tagged` as the result kind of
ordinary `partialApply` operations, but the resident closure allocator accepts
only `.object` and `.tobject` results.

## Minimal reproduction

Capture and lower the real `Zip.Wasm.compressLevel1` closure, then apply the
closed-application resident policy. The 391-declaration module contains 155
`.tagged` partial applications and stops at `unsupportedResult tagged`.

## Exact commands

Run the `ProbeLevel1.lean` command documented by
`integration/lean-zip/README.md` and inspect
`integration/lean-zip/_build/level1-probe.json`.

## Expected semantics

A successful partial application allocates a heap closure and returns its raw
address in Lean's shared i32 object-family call lane. Compiler annotations
`.object`, `.tagged`, and `.tobject` are physically call-compatible; captures
and semantic refinement remain directional.

## Actual behavior

`RuntimeOp.abiWellFormed` correctly recognizes all three object-family result
kinds, but `ResidentClosureAllocation.partialApplicationFunction` rejects the
`.tagged` member before emitting its otherwise identical address-retagging
path.

## Proof or differential evidence

The real Level-1 closure has 1,933 runtime operations, including 155 `.tagged`
partial applications. Compiler admission and lowering are otherwise complete.
The historical W6 proof deliberately excluded this case because
`ValueRel .tagged` encodes the more precise semantic relation; its later proof
adaptation must consume the released object-family call contract without
collapsing that relation.

## Semantic impact

Valid compiler-generated higher-order code cannot close its resident runtime,
including the production Level-1 DEFLATE path.

## Classification and triage

W7 executable helper admission plus a W6 proof follow-up. This is a real
compiler-produced object-family result, not a lean-zip-specific annotation to
rewrite and not evidence for weakening scalar compatibility.

## Workaround

None in generation. Do not rewrite `.tagged` closure results to `.object` in a
source-specific capture pass.

## Upstream tracking

none

## Resolution and regression

W7 now emits the same checked heap-closure allocation for every
`result.isObjectLike` kind. The standalone zero-import resident fixture calls
the `.tagged` export in V8, verifies the raw address, full closure header,
frontier movement, and scratch-word restoration. Contract proof adaptation is
still pending with W6, so the card remains active rather than claiming the
semantic bridge is complete.
