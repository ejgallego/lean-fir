---
id: FIR-BUG-wasm-none-release-retains-live-kind
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-07-18
reproduction: Fir/Wasm/Concrete/Runtime.lean
regression: Fir/Wasm/Concrete/Examples.lean
---

# Summary

Concrete reference-count release marks an allocation dead but retains its old
live-object kind instead of installing the frozen W6 `.freed` header kind.

## Minimal reproduction

Allocate any ordinary boxed scalar, constructor, or heap natural at reference
count one; call `decrementReferenceOnce`; then decode the raw header with
`Header.read`. Its `live` bit is false and count is zero, but `kind` still
reports the former live payload kind.

## Exact commands

Run `lean-beam update Fir/Wasm/Concrete/Examples.lean` after adding a raw-header
guard for the count-one transition, or inspect the final branch of
`decrementReferenceOnceFuel` in `Fir/Wasm/Concrete/Runtime.lean`.

## Expected semantics

The W6.0 representation contract reserves `ObjectKind.freed` for released
allocations so dead-object diagnosis and future reuse logic cannot interpret
stale bytes using a live payload schema.

## Actual behavior

The final branch writes `{ header with refCount := 0, live := false }`, leaving
the former kind and all kind-specific auxiliary words intact.

## Proof or differential evidence

A canonical `DeadCellRel` cannot assert the dedicated freed representation:
the concrete transition only proves a dead flag on a constructor, boxed, or
natural header.

## Semantic impact

Source execution still rejects access to the dead cell, but the concrete heap
violates its frozen self-describing representation contract and leaves stale
type metadata available to later runtime slices.

## Classification and triage

This is local to the W6 concrete runtime. The semantic FIR heap already marks
the cell dead before recursive child release; only the concrete header encoding
is inconsistent with the documented target contract.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Resolved in W6.3g by introducing `Header.forRelease` as the canonical freed
encoding and using it in the count-one branch before recursive child release.
The allocation extent is preserved, while kind, persistence, liveness, count,
and every auxiliary word are normalized to the frozen released-object
contract. `releasedBoxedUInt64Max` permanently checks the raw header and the
public dead-object read failure after a count-one transition.
