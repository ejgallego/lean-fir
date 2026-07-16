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
`PartiallyMeets` observation statements. The first layer-4 slice additionally
proves natural/string literal lowering equations, relates their source and
semantic-host results, and lifts both operations through Talos's abstract
host-contract `wp` rule.

Constructor allocation, object projection, and tag lookup have the same local
source/host simulation relation. The handle invariant is preserved across
successful encodings, and out-of-range constructor tags are rejected before
the `Nat`-to-`i32` case comparison can truncate them. A common Talos `wp`
theorem lifts any exact successful semantic-host step through its abstract
host contract.

Generated constructor and object-projection call stacks now use that common
rule directly. The full adapted constructor test—from discriminator
`local.get` through `getTag`, `i32.eq`, and `if`—has a source-facing `wp` rule
that selects the same arm as the source `Nat` comparison. The proof found a
missing allocation-side tag bound; constructor allocations and alternatives
are now both rejected before an out-of-range tag can be narrowed to `i32`.

The plan also defines A0, an independent artifact lane that can run alongside
W4. A0 owns new emitter and external-engine runner paths and produces the
first standards-consumable, host-backed Wasm artifact for the W3 corpus. It
must consume the frozen semantic ABI unchanged; concrete linear-memory layout
and production ABI compatibility remain W6 work.
