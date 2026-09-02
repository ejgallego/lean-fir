---
id: FIR-BUG-wasm-none-bulk-adapter-rejects-recycled-allocation
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.34.0-rc2
lean-revision: 6a10ac8c22beadecabdbb0919c2b50214762f91d
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-09-02
reproduction: integration/talos/artifact/check.sh
regression: integration/talos/artifact/check-prettyM-browser-adapter.mjs
---

# Summary

The prettyM and derived Verso HTML bulk encoders require `fir_heap_alloc` to
return the current bump frontier. Once the resident allocator reuses an
exact-size canonically dead block, a valid repeated render is rejected by the
JavaScript adapter before the structured entry runs.

## Minimal reproduction

Build the prettyM package with resident released-block reuse and run its
browser-adapter smoke. A repeated coverage input obtains an exact-size block
at byte 136688 while the monotone frontier remains 303232.

## Exact commands

```bash
bash integration/talos/artifact/check.sh
```

## Expected semantics

`fir_heap_alloc(n)` returns one aligned, complete `n`-byte allocation below or
at the post-call frontier. The frontier advances by `n` on the bump path and
does not advance when an exact-size released block is reused. Removing a block
from the private reuse index reserves it for the caller just as a bump
allocation does.

## Actual behavior

The adapter requires the returned address to equal the pre-call frontier and
requires the frontier to advance by the input size. It throws even though the
allocator returned a checked exact-size dead block within module-owned memory.

## Proof or differential evidence

The standalone resident recycling smoke demonstrates both allocator paths and
the complete prettyM artifact gate reaches this rejection only after the
preceding resident allocator/release/recycling checks pass. The failing package
continues to expose a monotone frontier; only the allocation address is below
it.

## Semantic impact

Persistent package consumers cannot use generic resident reclamation: a valid
second call may fail depending on the exact allocation-size history. Derived
adapters that copied the old bump-only assumption have the same latent issue.

## Classification and triage

Keep the frontier monotone and validate the allocator's two legal outcomes:
fresh allocation at the old frontier with corresponding growth, or exact-size
reuse below the old frontier with zero growth. Report allocation address,
extent, reuse status, and frontier growth separately.

## Workaround

Disabling released-block reuse restores the stale bump-only adapter assumption
but also restores unbounded frontier growth in persistent instances.

## Upstream tracking

none

## Resolution and regression

`PrettyMAdapter.allocateBulk` now validates and reports both legal allocator
outcomes. Fresh blocks begin at the old frontier and grow it by the requested
size; reused blocks lie below the old frontier, remain within the post-call
arena, and leave the frontier unchanged. The prettyM memory report carries an
allocation inventory and the derived Verso HTML encoder consumes the same
generic method. The complete artifact gate exercises the formerly failing
repeated-render sequence and passes with released-block reuse enabled.
