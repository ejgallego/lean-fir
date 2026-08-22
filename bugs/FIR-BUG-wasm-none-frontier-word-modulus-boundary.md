---
id: FIR-BUG-wasm-none-frontier-word-modulus-boundary
status: candidate
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: 900e363bbf5537f9133a34300b3f5f0f5da09361
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-08-22
reproduction: Fir/Wasm/Concrete/Memory.lean
regression: none
---

# Summary

The W6 raw allocator accepts a final heap cursor equal to `2^32`, while the
resident Wasm allocator must reject that transition because its `i32`
frontier global would wrap to zero.

## Minimal reproduction

`MemoryState.allocate` rejects only when
`wordModulus < requestedEnd`.  Consequently `requestedEnd = wordModulus` is
accepted, even though the successor state's `heapCursor` is not representable
by `UInt32`.  `ResidentAllocator.allocateFunction` computes the same end with
wasm32 addition, observes the wrapped result below the old cursor, and traps.

## Exact commands

```sh
rg -n "wordModulus < requestedEnd|allocationEnd.*current.*i32LtU" \
  Fir/Wasm/Concrete/Memory.lean Fir/Wasm/Emit/ResidentAllocator.lean
```

The failed proof obligation appears when proving that every successful
`MemoryState.allocate` run satisfies the resident allocator's no-wrap check:
the W6 postcondition supplies `requestedEnd ≤ wordModulus`, but the Wasm
frontier update requires `requestedEnd < wordModulus`.

## Expected semantics

Every successful concrete allocation leaves a heap cursor representable by
the resident runtime's `i32` frontier global.  An allocation ending exactly at
`2^32` must therefore fail before changing memory or the cursor.

## Actual behavior

W6 admits the exact-modulus end point and records `heapCursor = 2^32`; W7's
checked resident allocator rejects the corresponding wrapped wasm32 add.

## Proof or differential evidence

`MemoryState.allocate_spec.endWithinAddressSpace` currently concludes only
`address.value + align8 requestedBytes ≤ wordModulus`.  The execution proof
for `fir_heap_alloc` needs the strict form in order to prove that wasm32
addition returns the mathematical allocation end and that the new frontier
global equals the W6 cursor.

## Semantic impact

The mismatch affects only the terminal wasm32 address-space boundary, but it
prevents an unconditional implementation-to-W6 refinement theorem for the
resident allocator and would make the two runtimes disagree on that input.

## Classification and triage

This is a concrete-runtime contract defect.  The resident implementation's
rejection is required because zero is reserved and cannot encode a live heap
frontier.  W6 should use a strict address-space budget for successful
allocation ends.

## Workaround

Allocator execution theorems temporarily state the missing strict-end
premise explicitly; they do not weaken or alter the resident implementation.

## Upstream tracking

none

## Resolution and regression

Unresolved.  Change the W6 allocation/budget boundary from a non-strict to a
strict word-modulus end, adapt its consumers, and add a proof-level boundary
regression before marking fixed.
