---
id: FIR-BUG-wasm-none-reuse-retained-result-kind
status: confirmed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: f41a651fa5704692159653a9addfc29c200181bd
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-07-29
reproduction: Fir/Wasm/WellFormed.lean
regression: integration/talos/FirTalos/ConcreteReuseCapacityCorrectness.lean
---

# Summary

Retained reset provenance is representation-polymorphic: reset may return the
zero token for a shared or persistent source, or a nonzero token for a unique
constructor. Reusing an empty-layout constructor therefore may return either a
tagged fresh result or an in-place heap result. The current validator checks
only `(constructorKind info).refines resultKind`, which admits `.tagged` for
the empty layout even when retained evidence allows the heap branch.

## Minimal reproduction

Track a nonempty constructor as `retainedAtLeast available`, reset it, and
reuse the token with an empty-layout constructor whose declaration is compiled
at ABI kind `.tagged`.

On the reset fallback path, token zero allocates a tagged result and agrees
with `.tagged`. On the unique-reset path, the nonzero token is reused in place
and returns the existing heap address, which cannot inhabit
`ValueRel ... .tagged`.

## Exact commands

```text
make talos-check
```

The proof-level reproduction is the retained branch of the
certificate-free `reuseStep_of_capacityEvidence`: the existing operation ABI
fact supplies `constructorKind info = .tagged`, while successful in-place
reuse requires a result kind of `.object` or `.tobject`.

## Expected semantics

When reuse evidence is definitely empty, the ordinary constructor-kind
refinement is sufficient. When evidence is retained and may denote either
zero or nonzero at runtime, the result kind must accept both tagged and heap
representations; in the current ABI lattice that kind is exactly `.tobject`.

## Actual behavior

`reuseCapacityLetFacts?` validates fitting capacity but does not constrain the
declaration's result kind based on the selected provenance. The independent
`RuntimeOp.abiWellFormed` check sees only the replacement constructor layout,
so together they can admit `.tagged` for the mixed retained case.

## Proof or differential evidence

`reuseStep_none_of_capacityEvidence` constructs the tagged branch for either
provenance. `reuseStep_some_of_capacityEvidence` constructs the heap branch
and requires `.object ∨ .tobject`. For retained evidence and an empty layout,
the intersection of the two valid result-kind sets is `.tobject`.

## Semantic impact

Without the provenance-sensitive result-kind gate, the supported-domain claim
can include a successful source execution for which no ABI-indexed target
value relation exists.

## Classification and triage

This is a shared supported-domain/ABI validation gap exposed by proof
composition. It requires a coordinated contract change in
`Fir/Wasm/WellFormed.lean`; the concrete runtime need not change.

## Workaround

The W6 branch-independent operation theorem keeps an explicit compatibility
premise: definitely-empty evidence may use the constructor-selected kind,
while retained evidence requires `.tobject`. No whole-program theorem should
erase this premise until the shared validator establishes it.

## Upstream tracking

none

## Resolution and regression

Confirmed. Add a provenance-sensitive result-kind condition to the authoritative
reuse-capacity transfer/validator, land it as a shared contract change, and
rebase W6 before discharging the compatibility premise from supported source
syntax.
