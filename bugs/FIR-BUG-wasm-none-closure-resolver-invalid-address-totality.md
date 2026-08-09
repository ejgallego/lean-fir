---
id: FIR-BUG-wasm-none-closure-resolver-invalid-address-totality
status: confirmed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-08-09
reproduction: integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean
regression: integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean
---

# Summary

`SaturatedClosureCandidateResolver` quantifies over arbitrary concrete stores
and addresses while requiring every compiler candidate's matcher to return,
so the purported static metadata boundary is uninhabitable at an invalid
address.

## Minimal reproduction

Take any admitted saturated closure site whose compiler enumeration is
nonempty, an otherwise arbitrary concrete store, and an address absent from
the concrete closure tables. The resolver must construct a
`ClosureCandidateCase` for the first symbolic candidate. Its `operation` field
requires `closureMatchesStep ... = .Return ...`, but `closureMatchesStep`
traps when the supplied address cannot be decoded as a live closure.

## Exact commands

```text
rg -n "def SaturatedClosureCandidateResolver|structure ClosureCandidateCase" \
  integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean \
  integration/talos/FirTalos/ConcreteClosureDispatch.lean
rg -n "def closureMatchesStep" integration/talos/FirTalos/ConcreteRuntime.lean
```

## Expected semantics

Compiler/adapter candidate enumeration should be static and total once the
source module, adapted module, supported function, and call site are fixed.
Concrete matcher execution should be proved only at the actual runtime address
obtained from the source/target simulation invariant.

## Actual behavior

The current resolver mixes the static candidate list with a successful
concrete matcher execution at every caller-supplied `initial` store and
`address`. The definition supplies no validity, mapping, live-cell, or source
closure premise that could rule out a matcher trap.

## Proof or differential evidence

`ClosureCandidateCase.operation` requires an exact successful `Return` from
`closureMatchesStep`. Unfolding `closureMatchesStep` shows that an absent or
invalid closure address takes its error branch and calls `trap`. Therefore the
resolver's universal store/address quantifiers cannot be discharged merely
from lowering, adaptation, or host-resolution evidence.

## Semantic impact

The public recursive whole-export theorem is logically sound but its resolver
premise is stronger than the compiler can provide and may be uninhabitable for
real modules. This prevents the theorem from serving as a self-contained
compiler-correctness boundary.

## Classification and triage

This is a W6 Wasm-adapter proof-contract bug. It does not indicate an
executable compiler mismatch. The repair should separate static candidate
adaptation from runtime matcher execution, deriving the latter from the
actual closure mapping and live source-cell facts already present in the
structural saturated-call case.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

unresolved
