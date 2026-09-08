---
id: FIR-BUG-wasm-none-endpoint-native-axiom-audit
status: confirmed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-09-09
reproduction: integration/talos/FirTalos/TrustAudit.lean
regression: integration/talos/FirTalos/TrustAudit.lean
---

# Summary

The source-only trust gate reports one registered project axiom while public
W6 export theorems also depend on generated native-evaluation axioms.

## Minimal reproduction

Import `FirTalos.ConcreteResumableWasm` and inspect
`#print axioms FirTalos.Concrete.ConcreteSupportedExport.finiteTraceCorrect_of_sourceInvariant`.
At W6 checkpoint `7affa1d2` there are three standard axioms and 57 generated
axioms, including two introduced through `bv_decide`. The schema endpoint has
the same dependencies. The generic simulation theorem itself has only the
three standard axioms.

## Exact commands

```sh
make talos-check
python3 integration/talos/check-proof-trust.py
```

## Expected semantics

A public theorem's trust claim describes its transitive compiled dependencies,
including generated axioms, and the gate rejects unreviewed dependencies.

## Actual behavior

`scripts/validate_trusted_assumptions.py` scans textual declarations under
`Fir/` only. Neither generated axioms nor declarations under the Talos proof
root are covered. A successful source-hash check cannot establish an axiom-free
W6 theorem.

## Proof or differential evidence

Lean's `collectAxioms` reports 57 generated dependencies for each public
source-invariant export endpoint, 20 for the sampled UInt64 resident-installation
theorem, and 27 for the concrete literal-export example. The generic prefix,
backward composition, exact-return, fault, and replacement endpoints audited
in this slice use only `propext`, `Classical.choice`, and `Quot.sound`.

## Semantic impact

This is an incomplete trust claim and regression gate. It does not demonstrate
incorrect generated code. Existing native-evaluation dependencies must be
removed or explicitly accepted before claiming the corresponding endpoints
are kernel-only apart from standard logical axioms.

## Classification and triage

Confirmed by compiled-environment inspection. The explicit finite inventory
prevents growth of known debt; it does not discharge that debt.

## Workaround

Use the endpoint inventory when stating guarantees. Do not infer trust from
the count of textual `axiom` declarations or from an import alone.

## Upstream tracking

none

## Resolution and regression

The W6 compiled audit compares exact dependency sets and rejects missing
endpoints, unregistered axioms, and `sorryAx`. A source audit additionally
covers the Talos integration tree. Eliminating the recorded native-evaluation
dependencies remains unresolved; this card stays confirmed.
