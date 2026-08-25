---
id: FIR-BUG-wasm-none-exhaustive-pretty-closed-dispatch-ratchet
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d199458796a72b015b2e44a98ce7d628c95bf936
phase: wasm
pass: none
discovered-by: integration
first-seen: 2026-08-25
reproduction: integration/talos/artifact/check.sh
regression: integration/talos/artifact/check-resident-pretty-format.mjs
---

# Summary

The exhaustive prettyM artifact gate still requires fallback internalization
to preserve the full generic closure-dispatch and descriptor tables, although
closed styled package writing now intentionally prunes them to the finite
source `pap` target set.

## Minimal reproduction

Run the exhaustive browser artifact gate on accepted `main` `d1994587`:

## Exact commands

```text
FIR_BROWSER=google-chrome FIR_PRETTYM_EXHAUSTIVE_CHECKPOINTS=1 \
  bash integration/talos/artifact/check.sh
```

The accepted 83,996-byte styled artifact is regenerated deterministically,
but `check-resident-pretty-format.mjs` compares its 11 selected dispatch
targets with the preceding incremental String artifact's 42-target generic
table and fails.

## Expected semantics

Incremental runtime-internalization artifacts retain the generic closure
metadata.  Once the styled input boundary is closed, the written artifact must
use exactly the targets allocated by source final-LCNF `pap` nodes and the
corresponding reduced descriptor table.  The selected table must be a strict
subset of the generic table for this fixture.

## Actual behavior

The emitted closed artifact has the intended selected metadata, while the
July-era JavaScript ratchet incorrectly requires metadata equality across the
final boundary-closing step.

## Proof or differential evidence

`Fir.Wasm.Emit.SourceExamples` already checks that the source target set is
nonempty and strictly smaller, that every retained closure operation belongs
to it, that metadata equals the retained operations, and that early selected
lowering equals the generic post-pruner.  The deterministic closed Wasm bytes
remain SHA-256
`fc61301d946b1596ad08c9b20d51d2e1f68d60ca0c04b0f9d56e298c2ec6408d`.

## Semantic impact

No execution discrepancy is known.  The stale assertion blocks the exhaustive
artifact and browser acceptance gate and could tempt an integration owner to
restore the obsolete all-target package metadata.

## Classification and triage

This is a W7 artifact-acceptance regression, not a change to source semantics,
the symbolic Wasm surface, helper signatures, concrete layout, ABI, or
ownership behavior.

## Workaround

None.  Do not disable source-target pruning or weaken the compiler's existing
selected-target checks.

## Upstream tracking

W72-W7-20260825-002

## Resolution and regression

The exhaustive JavaScript gate now pins the exact 11 source-selected styled
dispatch targets and 13 descriptor shapes, and additionally requires the
selected target table to be a strict subset of the preceding generic table.
The unchanged plain closed artifact continues to require metadata equality
because it does not select the styled boundary's finite target set.
