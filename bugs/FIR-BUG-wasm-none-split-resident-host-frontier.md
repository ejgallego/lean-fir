---
id: FIR-BUG-wasm-none-split-resident-host-frontier
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-07-26
reproduction: integration/talos/artifact/call-concrete-pretty-format.mjs
regression: integration/talos/artifact/prettyM-package/smoke.mjs
---

# Summary

A mixed resident/host artifact lets Wasm constructor allocation and JavaScript
runtime allocation advance independent heap frontiers, so later host
allocations overwrite live Wasm objects.

## Minimal reproduction

Compile the text `Std.Format.prettyM` frontier with its 23 `allocCtor`
operations internalized and the remaining 154 runtime operations imported.
Execute the normal concrete pretty-format case. A resident constructor
allocation advances `fir_heap_frontier`, but the following imported
`String.Internal.append` handler allocates from the stale
`ConcreteHost.heapCursor`.

## Exact commands

From `integration/talos/artifact` after generating the source artifacts:

```sh
node call-concrete-pretty-format.mjs \
  _build/source-pretty-format-resident-constructors.wasm
```

## Expected semantics

Every resident helper and every remaining semantic import sharing the
module-owned linear memory must allocate from one monotonically advancing
frontier. The concrete result and styling trace should remain equal to the
native oracle while runtime families are internalized incrementally.

## Actual behavior

The module client initializes `fir_heap_frontier` from
`ConcreteHost.heapCursor` only once. Resident constructor helpers then advance
the Wasm global while imported JavaScript handlers continue to read and write
the unchanged host cursor. Their allocations overlap resident objects, and the
pretty-format decoder fails in `String.Internal.append` with
`expected a concrete string object`.

## Proof or differential evidence

The same pretty-format case passes at the 177-import resident-allocator
checkpoint. The 154-import constructor checkpoint validates, contains no
`allocCtor` imports, and passes its standalone byte-layout test, but fails the
native-oracle differential call when resident and imported allocation are
interleaved.

## Semantic impact

Every incremental W7 artifact that internalizes an allocating operation while
retaining another allocating JavaScript runtime handler can corrupt its shared
heap. This blocks trustworthy differential testing on the path to the final
zero-function-import artifact; it does not indicate a defect in constructor
layout itself.

## Classification and triage

This is a `wasm-adapter` defect at the temporary mixed-runtime boundary. Both
allocators implement the frozen concrete layout correctly, but the module
client fails to maintain their shared frontier invariant.

## Workaround

The mixed-runtime adapter synchronizes its monotone frontier at every
remaining JavaScript import boundary. This bridge is removed from the
execution path naturally when the artifact reaches zero function imports.

## Upstream tracking

none

## Resolution and regression

`ConcreteHost.imports` now pulls the resident frontier before each semantic
handler and publishes the host frontier afterward. `module-client.mjs`
attaches the allocator's read/set exports after instantiation and rejects
half-present frontier surfaces. The same import-boundary synchronization also
refreshes `ConcreteHost`'s buffer and `DataView` after resident `memory.grow`,
avoiding the detached-buffer analogue of the split-frontier bug. The packaged
styled prettyM smoke test interleaves resident constructor allocation with
imported string/runtime allocation, while the standalone constructor probe
forces a resident page crossing and the browser worker exercises both paths in
Chrome.
