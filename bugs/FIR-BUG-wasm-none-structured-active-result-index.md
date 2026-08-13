---
id: FIR-BUG-wasm-none-structured-active-result-index
status: confirmed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: b28b05afb9029e61230e975108ea487ecd613cf0
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-08-13
reproduction: integration/talos/FirTalos/ConcreteStructuredSimulation.lean
regression: none
---

# Summary

The strong structured simulation carries a `functionResult` ABI index without
retaining that it is the active symbolic function's actual singleton result.

## Minimal reproduction

`ConcreteSupportedExport.supportedGlobalRootAt` can construct the current
strong relation at any supplied `functionResult`. At a source `.return`, the
admission rule instead requires the returned local's ABI kind to refine that
index, so arbitrary instances cannot satisfy universal current-step coverage.

## Exact commands

```text
make talos-setup
lake build FirTalos.ConcreteResumableWasm
```

Inspect `ConcreteStructuredSupportedGlobalOutcome`,
`ConcreteStructuredCodeStepAdmission.ret`, and
`ConcreteSupportedExport.supportedGlobalRootAt`.

## Expected semantics

Every active generated-function relation should retain the exact result kind
selected by the symbolic function row. Internal call entry must switch this
index to the generated callee's result, while return/pop restores the caller's
saved result index.

## Actual behavior

The global existential hides an unconstrained `functionResult`. Resource and
supported frame stacks preserve that index structurally, but neither the
active supported function nor the global package equates it with
`sourceFunction.results[0]?`.

## Proof or differential evidence

The canonical root proof needs no fact about `sourceFunction.results` and Lean
accepts an arbitrary ABI index. The `.ret` admission constructor exposes the
missing invariant by demanding `actualResult.refines functionResult = true`.

## Semantic impact

The proposed universal admission/coverage law ranges over malformed relation
instances and is therefore stronger than compiler correctness. This blocks a
non-vacuous construction of the final ranked simulation even for executions
with sufficient address space.

## Classification and triage

This is a proof-relation indexing defect. The repair belongs in the W6 strong
relation and supported-function boundary; it should be derived from actual
lowering/adaptation rows rather than accepted as a caller certificate.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Unresolved. The root constructor is named `supportedGlobalRootAt` to expose
the temporary caller-selected index until the global relation is strengthened.
