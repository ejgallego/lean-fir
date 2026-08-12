---
id: FIR-BUG-wasm-none-stale-pretty-checkpoint-gate
status: fixed
classification: validation-harness
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-08-13
reproduction: integration/talos/artifact/check.sh
regression: integration/talos/artifact/check.sh
---

# Summary

The browser artifact gate can consume stale intermediate prettyM checkpoints,
and exhaustive regeneration is blocked by comparing the plain prettyM closure
with a broader shared projection catalog.

## Minimal reproduction

Run the default final-only artifact build after changing a resident helper,
then enable `FIR_BROWSER`. The browser worker exercises checkpoint files that
the current invocation did not regenerate. On a forced exhaustive run, the
plain source assertion also expects the Level-1-only packed `UInt64`
projection.

## Exact commands

```sh
FIR_BROWSER=google-chrome bash integration/talos/artifact/check.sh
FIR_PRETTYM_EXHAUSTIVE_CHECKPOINTS=1 \
  bash integration/talos/artifact/check.sh
```

## Expected semantics

An acceptance gate must either regenerate every artifact it executes or reject
an incompatible fast-mode request. The plain prettyM checkpoint must ratchet
its exact eight-operation projection closure, while the standalone reviewed
helper module may additionally cover operations required by Level-1.

## Actual behavior

The browser run reached an older big-numeric module and trapped on the newer
persistent-Natural regression. Forced regeneration stopped earlier with eight
plain prettyM read projections versus a nine-operation shared catalog; the
extra operation was `.scalarProj 1 0 .uint64` from Level-1.

## Proof or differential evidence

The current standalone big-numeric artifact accepts the persistent Natural,
while the old linked checkpoint traps on the same input. Fresh source capture
reports exactly the eight expected prettyM projection descriptors and omits
only the reviewed Level-1 `UInt64` descriptor.

Fresh specialization-provenance capture also reports 101 closure projections
across 12 physical coordinates and 105 closure matches. These replace the old
87/15/77 checkpoint inventory while retaining the same 42-entry dispatch and
19-entry descriptor tables.

The same review finds 24 constructor allocations and 131 partial applications,
replacing 23 and 87. Those additions account for the larger initial frontier,
but internalizing the expanded closure family still reaches the unchanged
65-import post-partial-application frontier.

The styled trace closure has the same 44 additional partial applications: its
constructor and immediate-Natural frontiers move from 157/153 to 201/197,
then 131 partial applications still reach the unchanged 66-import frontier.

## Semantic impact

The browser result can describe a mixture of repository revisions, defeating
the deterministic acceptance claim and obscuring whether a failure belongs to
the current generator or an ignored build product.

## Classification and triage

This is a validation-harness freshness and catalog-boundary bug. It does not
change emitted runtime semantics. Keep the fast final-only Node development
path, but make browser acceptance require exhaustive generation and retain a
separate exact plain-prettyM inventory.

## Workaround

Manually set `FIR_PRETTYM_EXHAUSTIVE_CHECKPOINTS=1` and locally repair the
stale inventory assertion. This is not acceptable for the published gate.

## Upstream tracking

none

## Resolution and regression

The linked source checkpoints now ratchet separate, exact inventories for the
plain prettyM closure while the standalone resident modules retain the broader
reviewed prettyM/Level-1 helper catalogs. The regenerated plain closure has 8
read projections, 101 closure projections over 12 physical coordinates, 105
closure matches, 24 constructor allocations, and 131 partial applications.
The styled closure records its corresponding 201/197 constructor/Natural
frontiers and the same 131 partial applications. Both paths converge on their
unchanged 65/66 import frontiers after partial-application internalization.

`check.sh` now rejects `FIR_BROWSER` unless
`FIR_PRETTYM_EXHAUSTIVE_CHECKPOINTS=1`, ensuring that browser acceptance cannot
consume intermediate modules from an earlier ignored `_build`. A fresh
exhaustive regeneration passes the persistent big-Nat checkpoint, every mixed
runtime prettyM checkpoint, and the complete Chrome Worker matrix.
