---
id: FIR-BUG-wasm-none-resident-host-observation-boundary
status: candidate
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.34.1
lean-revision: 5045d0056413266e57c625dcd7c365b10e377c52
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-09-29
reproduction: integration/talos/FirTalos/ConcreteResidentBoundaryTests.lean
regression: integration/talos/FirTalos/ConcreteResidentBoundaryTests.lean
---

# Summary

The host-backed W6 state/trace relation cannot be reused unchanged for a
host-preserving resident helper implementing a trace-producing source external.

## Minimal reproduction

Start with a related source/target state. A source `Array.mkEmpty` or
`Array.push` response appends an external event. A resident implementation that
only changes Wasm memory/globals preserves `store.host`. Consequently its host
trace has the old length while the source trace has length one greater.

## Exact commands

From an ordinary configured worktree:

```sh
make talos-setup
make talos-check
```

The trust umbrella includes `ConcreteResidentBoundaryTests` and audits its two
negative theorems. Neither theorem executes or postulates a particular helper.
They state the exact obstruction for any host-preserving execution.

## Expected semantics

Resident linking should relate the concrete model heap to actual Wasm memory
and should state which source observations correspond to deployed execution.
It must not silently erase source events or assume ghost host updates that
actual Wasm instructions do not perform.

## Actual behavior

`StateRelated` in `ConcreteRuntime.lean` reads `targetStore.host.runtime`.
`concretePrefixObservation` likewise reads its world and trace. Resident memory
writes instead update `store.mem`; `ResidentMemoryRel` deliberately relates
these two different representations. `ResidentReplacement` takes a post-state
`StateRelated` premise, so its theorem does not discharge this bridge.

## Proof or differential evidence

`not_stateRelated_after_event_of_host_preserved` rules out the required
post-state relation even with a different refinement witness.
`not_prefixObservationRel_after_event_of_host_preserved` rules out the exact
trace observation independently of heap/result representation. Both follow
from `ConcreteTraceRel.size` and the length of `Array.push`.

## Semantic impact

This blocks interpreting the current host-contract theorem plus individual
resident helper proofs as a linked-artifact theorem. It does not invalidate
the conditional W6 theorem, demonstrate wrong generated application results,
or claim that every possible observation policy is impossible.

## Classification and triage

Proof-interface/observation-boundary candidate. Root owns the shared semantic
decision: introduce and erase ghost instrumentation with a proved execution
projection, or select an explicit product-observation projection and prove the
corresponding simulation. Memory refinement is required in either case.

## Workaround

None. Keep host-backed and resident-helper claims distinct. Do not weaken the
existing trace relation or change source external semantics as a local repair.

## Upstream tracking

None; repository-owned theorem boundary.

## Resolution and regression

Unresolved. The negative regressions preserve the boundary until a separately
proved resident representation/observation bridge is integrated.
