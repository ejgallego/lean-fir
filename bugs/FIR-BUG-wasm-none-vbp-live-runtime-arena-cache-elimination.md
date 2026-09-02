---
id: FIR-BUG-wasm-none-vbp-live-runtime-arena-cache-elimination
status: candidate
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.34.0-rc2
lean-revision: 6a10ac8c22beadecabdbb0919c2b50214762f91d
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-09-02
reproduction: integration/vbp-verso-viewer/check.sh
regression: none
---

# Summary

The retained VBP component package prepares its source through
`prepareArenaArtifact`, the mode for consumers that rewind all scratch state
after each public call. That transformation removes Lean's 1,541 lazy-cache
globals even though the component retains callbacks and cannot rewind between
renders.

## Minimal reproduction

Run the exact ten-edit FLT Chromium campaign with released-block reuse and
sample the resident heap after unmount. The campaign completes, but its
frontier reaches about 1.84 GiB and grows on every alternating update.

## Exact commands

```sh
FIR_VBP_VERSO_VIEWER_PACKAGE=/absolute/path/to/vbp-verso-viewer-current \
  node scripts/vir_preview_browser_smoke.mjs
```

## Expected semantics

Lean's nullary closed declarations use module-owned lazy-cache flag/value
globals. The first miss computes and recursively persists the singleton;
subsequent calls load the same cached value without allocating another graph.

## Actual behavior

`prepareArenaArtifact` rewrites each cache access into a direct initializer
call followed by the ordinary persistence helper. This is safe only when the
consumer rewinds the complete per-call arena. In the retained component, every
render recomputes and permanently promotes the closed graph.

A diagnostic post-unmount census found 28,791,083 heap blocks. Nearly all were
persistent, including 14,536,795 constructors, 7,102,667 strings, 4,648,155
closures, and 1,761,038 ByteArrays. Only 286 blocks / 448,056 bytes remained in
the released-block reuse index.

## Proof or differential evidence

The emitted base descriptor contains 1,541 distinct `cacheSet` operations, but
the accepted resident inventory reports zero lazy-cache initializers because
arena preparation erased their flag/value globals. The exact FLT interaction
campaign remains functionally correct, separating this ownership leak from
the callback ABI and React reconciliation behavior.

## Semantic impact

A persistent FIR-native component eventually exhausts Wasm32 memory even when
ordinary released blocks are reusable. It also loses Lean's intended singleton
identity and recomputes closed values unnecessarily.

## Classification and triage

Use the generic retained-runtime linking path: preserve compiler lazy-cache
globals and let resident cache publication persist only the first miss. Keep
`prepareArenaArtifact` for genuinely rewindable whole-call consumers.

## Workaround

Dropping the Wasm instance after each call is incompatible with retained React
callbacks and state.

## Upstream tracking

none

## Resolution and regression

unresolved
