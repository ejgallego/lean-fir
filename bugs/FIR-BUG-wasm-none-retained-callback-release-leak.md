---
id: FIR-BUG-wasm-none-retained-callback-release-leak
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

The retained-component adapter removes its JavaScript callback lease without
decrementing the resident Lean closure whose ownership was transferred to that
lease. Replaced React graphs therefore retain every obsolete callback and its
captured Lean graph for the lifetime of the Wasm instance.

## Minimal reproduction

Run the exact FLT browser campaign through the FIR provider for thirty
alternating original/edited updates. Release each obsolete component, event,
state, and effect callback through the ordinary generic VIR React host, then
scan the resident heap immediately after unmount.

## Expected semantics

The host owns one physical Lean closure reference for each retained callback
root. Repeated invocation borrows that root. Releasing the final JavaScript
lease must perform one checked resident decrement, recursively releasing the
closure captures and offering their dead blocks to the allocator.

## Actual behavior

`callback.release()` marks the JavaScript root dead and removes it from
`callbackRoots`, but never calls a Wasm release entry. The allocator repair
proves this is no longer hidden dead storage: after thirty edits all 2,042
canonically freed blocks are indexed, while 576 callback roots remain live and
the heap contains 85,873 live constructors and 8,487 live closures. The
frontier reaches 6,311,536 bytes and continues to grow with each update.

## Proof or differential evidence

The same functional campaign passes through interpreted VIR and FIR. The FIR
adapter already borrows each retained callback before invocation, so repeat
calls are correct. The missing operation is specifically the final owned
decrement when the generic React host releases its lease.

## Semantic impact

Long-lived component providers retain obsolete Lean callback graphs even when
the host correctly releases every superseded callback. Released-block reuse
cannot reclaim live reference-counted objects, so the instance still grows
without bound.

## Classification and triage

Expose the existing checked resident decrement as an adapter-private physical
release entry. Invoke it exactly once when a callback root's final JavaScript
lease is released. Do not make callbacks persistent, insert application-name
shims, or weaken repeated invocation's borrowed boundary.

## Workaround

Dropping the complete Wasm instance releases the graphs but is incompatible
with a retained live component.

## Upstream tracking

none

## Resolution and regression

unresolved
