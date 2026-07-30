---
id: FIR-BUG-wasm-none-reuse-retained-token-ordinary
status: confirmed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 3407f806ee122cc550913ba60c12e0e4ddbbdc6f
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-07-29
reproduction: Fir/Wasm/WellFormed.lean
regression: integration/talos/FirTalos/ConcreteReuseCapacityCorrectness.lean
---

# Summary

The concrete in-place reuse protocol requires a nonzero reuse token to name an
ordinary allocation. A successful unique reset establishes that property, but
`reuseCapacitySafeCode` preserves its retained-capacity fact across every
intervening effect without tracking whether the same allocation is made
persistent. The original object name remains in scope after reset, so the
current supported domain can admit such an invalidating mutation before reuse.

## Minimal reproduction

Construct a unique ordinary constructor `object`, reset it to a nonzero token,
then use the still-bound `object` name in a persistent increment before reusing
the token:

```text
let token := reset n object
inc object 1 checked persistent
let result := reuse token replacement fields
```

The capacity transfer keeps the token's `retainedAtLeast` fact across `inc`,
and the ordinary supported-code validator accepts the individual operations.

## Exact commands

```text
lake -d integration/talos env lean \
  FirTalos/ConcreteReuseCapacityCorrectness.lean
make talos-check
```

The proof-level witness is the explicit `tokenOrdinary` premise of
`reuseStep_of_capacityEvidence`. It cannot be derived from the current
`ReuseCapacityStateRelated`: that relation tracks the retained concrete header
extent but not the source cell's persistence bit.

## Expected semantics

Every nonzero token admitted at a reuse site must still denote the ordinary
allocation produced by the unique-reset protocol. Validation may enforce
single-use/adjacency, invalidate the fact when an alias can mutate ownership
metadata, or carry a semantic ordinary-token invariant that all intervening
operations preserve.

## Actual behavior

`reuseCapacitySafeCode` threads facts unchanged through `inc`, `dec`, mutation,
delete, and other effects. In the example above, semantic reuse preserves the
now-persistent source cell metadata because it updates only `cell.object`.
Concrete reuse deliberately installs `persistent := false` in the replacement
header. The ordinary heap relation therefore cannot be re-established.

## Proof or differential evidence

`ReuseCapacityValueRel.retainedToken` proves only the physical address mapping
and retained allocation extent. The in-place branch of
`reuseStep_of_capacityEvidence` additionally needs the source cell equation
`persistent = false`; neither fitting evidence nor mapped-header transport
implies it.

## Semantic impact

The accepted compiler fragment can contain a successful source reuse whose
concrete result disagrees on ownership metadata. This blocks a sound
certificate-free whole-export reuse theorem.

## Classification and triage

This is a shared reset/reuse protocol-validation gap. The concrete runtime's
ordinary replacement header is intentional and should not be weakened.

## Workaround

The W6 operation theorem exposes `tokenOrdinary` explicitly. Compiler-level
composition must retain that premise until the authoritative supported-domain
validator establishes a stable reset-token protocol.

## Upstream tracking

none

## Resolution and regression

Confirmed. Add a source-level reset-token validity transfer to the shared
validator, then derive the ordinary source-cell fact from that transfer in the
certificate-free compiler state relation.
