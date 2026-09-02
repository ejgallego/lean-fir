---
id: FIR-BUG-wasm-none-direct-retirement-bypasses-resident-recycler
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

Resident Array growth, ByteArray replacement, and closure application consume
an exclusive source allocation by writing a canonical freed header directly.
After the resident allocator gained released-block reuse, these paths still
omit the private recycler call and leave their storage permanently unreachable.

## Minimal reproduction

Run the exact retained VBP ten-edit Chromium campaign with compiler lazy caches
preserved, then scan the module-owned heap after unmount. The functional
campaign passes, but 421,839 blocks / 26,137,728 bytes are marked freed while
only 1,282 blocks / 504,048 bytes are reachable from the reuse index.

## Exact commands

```bash
bash integration/vbp-verso-viewer/check.sh
```

On the affected revisions, run the retained VBP update campaign against the
published package and inspect the module-owned heap after unmount. The
functional package gate remains green while the dead-block census shows the
unindexed storage described below.

## Expected semantics

Every allocator-backed path that consumes an allocation without recursively
releasing its transferred payload must establish the canonical dead header and
offer the complete allocation to the same checked recycler used by ordinary
last-reference release.

## Actual behavior

The container replacement and closure-application helpers duplicate the
dead-header stores but do not call `fir_heap_recycle`. A diagnostic census
finds hundreds of thousands of freed 40--64-byte blocks outside the reuse
index. After the Array/ByteArray paths were repaired, the same VBP campaign
still left 474,985 freed blocks / 27.06 MiB, isolating closure transfer as the
dominant remaining direct-retirement path.

## Proof or differential evidence

The production VBP package remains functionally correct and drops from roughly
1.84 GiB to 28.25 MiB after restoring lazy caches. The remaining heap is mostly
dead rather than retained: 26.14 MiB is already canonically freed. This
separates the missing recycler edge from liveness and callback ownership.

## Semantic impact

Lean-visible values remain correct, but a persistent Wasm instance grows on
every update and can eventually exhaust Wasm32 memory despite the generic
released-block reuse layer.

## Classification and triage

Route allocator-backed ownership-transfer retirement through the checked
resident recycler. Preserve the existing transfer semantics: do not recurse
through payload lanes whose ownership has moved to the replacement object.

## Workaround

Dropping the complete Wasm instance reclaims memory but invalidates retained
callbacks and is not a viable live-component ownership model.

## Upstream tracking

none

## Resolution and regression

unresolved
