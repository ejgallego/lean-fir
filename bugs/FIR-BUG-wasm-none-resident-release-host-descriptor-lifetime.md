---
id: FIR-BUG-wasm-none-resident-release-host-descriptor-lifetime
status: confirmed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.34.1
lean-revision: 5045d0056413266e57c625dcd7c365b10e377c52
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-10-08
reproduction: integration/talos/artifact/repro-concrete-descriptor-lifetime.mjs
regression: none
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

Unresolved. The host-only implementation lease preserves corruption guards.
The additional `repro-concrete-descriptor-provenance.mjs` control releases a
host [erased,tobject] constructor and reuses its block for [object,tobject]. A
second history mutates the live erased slot without releasing. Entire heaps,
frontiers, descriptor maps, allocation lists and logical address maps match.
Both reject objectJson at `does not refine erased`, so same-layout reuse cannot
be distinguished from live provenance corruption using the exposed state.
Persistent traversal includes erased slots and correctly marks the child;
this diagnostic does not establish an ownership omission.

A safe reconciliation needs a lifetime signal. Raw module-client exports and
public helper calls do not notify the host; frontier synchronization observes
only monotonic allocation extent. A JavaScript guest-call lifecycle contract
could delimit metadata validity without changing Wasm bytes, but changes the
provider boundary and must cover reentrancy. An allocator generation signal
would instead change the runtime/ABI contract. No reset-on-mismatch workaround
or guard weakening has been implemented.

Run the additional control with the same two artifact arguments as the minimal
reproducer. Its success confirms the indistinguishability and guard behavior;
it is diagnostic evidence, not a passing migration artifact gate.
