# Optional Talos bridge

The detailed implementation, proof, and parallel-work plan is in
[`PLAN.md`](PLAN.md).

This package translates FIR's symbolic semantic-Wasm module into Talos's
`Wasm.Module`. It is intentionally separate from FIR's default build: Talos
is a fast-moving AGPL-3.0 project, while FIR's semantic core should not force
that dependency on every consumer.

The bridge is pinned to Talos commit
`a01d01c778b794dd00956748a067b6793c2c9f9b`, whose interpreter package uses
Lean 4.32.0. From the FIR repository root, set it up and validate it with:

```sh
make talos-setup
make talos-check
```

The adapter resolves FIR locals, symbolic branch labels, declaration calls,
runtime imports, function indices, and exports into Talos syntax. Host
implementations of the generated `fir.*` imports and the LCNF/Wasm simulation
proof live in this optional package rather than in FIR's core.

`FirTalos.runDifferential program entry args` runs the FIR interpreter and the
adapted Talos module together. It reports related observations, field-level
semantic mismatches, structured target failures, preparation failures, and
source fuel exhaustion while comparing only the observable reachable heap.

`FirTalos/Correctness/` now contains the W4 proof foundation: coherent handle
round trips, scalar codec lemmas, adapter signature/local/label/call
preservation, positional `HostEnv.Satisfies` packaging, and bridges from a
successful executable witness to fuel-free `TerminatesWith` and
`PartiallyMeets` observation statements.
