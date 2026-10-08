---
id: FIR-BUG-wasm-none-resident-release-host-descriptor-lifetime
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.34.1
lean-revision: 5045d0056413266e57c625dcd7c365b10e377c52
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-10-08
reproduction: integration/talos/artifact/repro-concrete-descriptor-lifetime.mjs
regression: integration/talos/artifact/test-concrete-lifecycle.mjs
---

# Summary

JavaScript constructor metadata survives resident release/address reuse and
conflicts with a new, correctly laid-out constructor during cache publication.

## Minimal reproduction

Allocate a two-field constructor through ConcreteHost, release it through the
existing resident helper, reuse the same 48-byte block for a one-field
SpaceResult constructor with two scalar bytes, then publish it through cacheSet.
The tracked reproducer uses production helpers and preserves the original
constructorDescriptor assertion; it invokes no prettyM formatter entry point.
It now passes through the managed lifecycle boundary and verifies persistence.

## Exact commands

After the checkpoint source fixture prepares the existing release/allocator
products, from integration/talos/artifact:

```sh
node repro-concrete-descriptor-lifetime.mjs \
  _build/source-pretty-format-resident-releases.wasm \
  _build/source-pretty-format-resident-allocator.wasm.json
```

The complete consumer case is:

```sh
node call-concrete-pretty-format.mjs \
  _build/source-pretty-format-resident-releases.wasm
```

## Expected semantics

Metadata used to traverse a live constructor belongs to that allocation's
lifetime and field layout. Native/resident release and allocation must not
leave an observer using metadata from a prior occupant of the address.

## Actual behavior

The minimal case reuses address 1024: the old descriptor has two tobject fields;
the new live header has bytes=48, tag=0, objectFields=1, usizeFields=0 and
scalarBytes=2. cacheSet -> markPersistentWord -> ownedWords ->
constructorDescriptor rejects the old descriptor's arity. The new header's
extent agrees with its field/scalar counts; no heap-layout disagreement is
established.

## Proof or differential evidence

The full all-constructors Format case at width 80 reaches address 2656.
History records host allocation of Std.Format.tag (tag=7, two object fields),
resident release (kind=255, live=false), another two-field occupant (tag=1),
release again, then a live tag=0/one-field/two-scalar-byte constructor. The host
descriptor remains [tobject,tobject] across every released/reallocated state.
Publication of Std.Format.spaceUptoLine._closed_1 triggers the arity assertion.

The minimized production-helper reproduction fails identically, independently
of formatter inputs. Detailed local history log SHA-256:
116f3ddbfad60c41826e271f4d331ed459dc4ba1e212555596190f51f804a1ab.

## Semantic impact

The exhaustive artifact gate stops at the resident-release concrete-client
stage before browser checks. Blindly ignoring arity or retaining old erased
field kinds could also misclassify ownership; no such workaround is used.

## Classification and triage

Confirmed host metadata lifetime discrepancy. An accepted-main `15dc1f460`
control with the old Talos overlay, only the two inventory fixture repairs,
and the diagnostic driver fails identically. Candidate and control release
Wasm bytes have SHA-256
7b3cd8a2f678cd4dedc891d557995b771862aa9909bf31a51f1c7ada4d1ec34b;
both unchanged concrete-host files have SHA-256
934b6beb5ae5933a246389a2e55d4f95334ae6525fbbf5b7a6fd86065877ea82.
Root delegated a host-only repair, with an explicit return to coordination if
the required distinction needs a shared lifetime contract.
ConstructorDescriptor.fieldKinds
must describe the current live allocation, not merely the address's history.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

The diagnostic checkpoint `6ddeaa00d` preserves the pre-repair raw-interface
information boundary: [erased,tobject] -> [object,tobject] resident reuse and an
illicit live erased-slot mutation produced identical heaps, frontiers and host
metadata. Both failed exact erased-field decoding. Persistent traversal already
included erased slots; no child ownership omission was established.

Root selected an explicit JavaScript managed guest-call lifecycle contract.
`module-client.mjs` now exposes a frozen instance facade for hosts with paired
hooks. Every callable export balances guest entry/exit with finally, including
helper routes. Memory/global identity and function arity are retained; raw
instances are not exposed by the supported concrete client. Non-hook hosts
retain their prior contract. Supported concrete Node/invocation/validation and
browser consumers use this boundary. Standalone raw physical engine diagnostics
are explicitly outside its provenance guarantee.

ConcreteHost discards constructor provenance across managed guest/host phase
transitions for resident modules, without inferring generations or responding
to arity mismatches. Current slots are re-derived on subsequent host observation.
Within each host phase, recorded layout/descriptor snapshots reject corruption
and exact ABI kinds remain authoritative. Field extent, bounds, liveness,
ownership, recursive persistent traversal and disposal checks remain enforced.
Nested guest/import/provider reentry and throw/unwind restore the prior phase.

The two tracked public-helper regressions pass for different- and same-layout
reuse; the latter now distinguishes otherwise identical heaps by their managed
histories and rejects the same-phase erased mutation. The focused lifecycle
regression additionally rejects descriptor/layout corruption, malformed field
extent, invalid/released pointers and dead owned children; verifies memory
growth/persistence, helper wrapping, reentrant imports, ordinary unwind and
non-hook compatibility. A prior test that simulated resident allocation by
silently deleting host metadata now creates an actual descriptor-free physical
diagnostic allocation instead.

No Wasm import/export signature, instruction or physical layout changes.
All 35 Wasm artifacts shared with the accepted-main control are byte-identical.
The complete exhaustive artifact gate passes, including browser/Worker and
concrete browser validation. The final combined repository check is recorded
in the migration report.
