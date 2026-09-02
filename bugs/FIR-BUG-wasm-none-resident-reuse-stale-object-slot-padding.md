---
id: FIR-BUG-wasm-none-resident-reuse-stale-object-slot-padding
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

The first generic released-block reuse candidate exposes partial resident
Array element stores: the low wasm32 object address is replaced, but the high
four padding bytes of FIR's eight-byte semantic object slot retain data from
the block's previous allocation.

## Minimal reproduction

Build the VBP Verso viewer package with exact-size released-block reuse enabled
and run its package smoke. Decoding the first ready-document render reaches a
reused resident Array and rejects `PropValue.style.value[0]` because the slot's
high word is nonzero.

## Exact commands

```sh
cd integration/vbp-verso-viewer
FIR_REUSE_EMITTED_ARTIFACT=1 FIR_ALLOW_DIRTY_PACKAGE=1 node package.mjs
```

## Expected semantics

Every live object lane satisfies FIR's concrete layout invariant: the low four
bytes contain the wasm32 object word and the high four bytes are zero. Reusing
an allocation must not make a previously valid Array representation depend on
the old payload bytes.

## Actual behavior

Fresh linear-memory pages masked the issue because their bytes begin at zero.
Resident Array construction, copy, push, replacement, swap, and fill paths use
four-byte `i32.store` operations for elements. Once an exact-size dead block is
reused, those stores preserve stale high words and the browser adapter observes
a malformed Lean word.

## Proof or differential evidence

The existing concrete `writeObjectFields` operation explicitly writes both the
low object word and zero high padding. The generated constructor path also
zeros unwritten object-slot words. The failure therefore identifies a W7 Array
lowering gap rather than a weaker concrete contract.

## Semantic impact

The Array representation is only accidentally canonical on fresh zero-backed
memory. Any allocator that faithfully reuses released storage can turn a valid
Lean Array operation into an invalid resident graph or expose stale bits at a
host decoding boundary.

## Classification and triage

Repair the resident Array write surface so every semantic object-slot write
publishes the complete eight-byte FIR lane. Do not rely on allocator-wide
zero-fill: Lean allocation does not make stale payload bytes semantic, and the
writer owns initialization of the complete target representation.

## Workaround

Disabling released-block reuse masks the discrepancy but restores the Wasm32
address-space exhaustion reported by
`FIR-BUG-wasm-none-resident-arena-released-block-reuse`.

## Upstream tracking

none

## Resolution and regression

unresolved
