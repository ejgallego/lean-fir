---
id: FIR-BUG-wasm-none-structured-validation-provenance
status: confirmed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: 7fd2d2d97feb82ca7d905ec8db13e30c49aeab33
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-08-13
reproduction: integration/talos/FirTalos/ConcreteResumableWasm.lean
regression: integration/talos/FirTalos/ConcreteStructuredSimulation.lean
---

# Summary

The structured simulation retained successful code adaptation for its current
LCNF node but not the source declaration and incremental validation state from
which `WasmSupported` accepted that node.

## Minimal reproduction

Attempt to construct `ConcreteStructuredCompilerCurrentStepAdmission.code`
from a `ConcreteSupportedFunction`, a current
`ConcreteStructuredCodeCoreRel`, and a successful source step. Adapter
inversion recovers generated instructions and numeric locals, but return,
join, case, and guarded sharing admission also need the source validator's
result kind, local-kind row, join points, case facts, and sharing facts.

## Exact commands

```text
make talos-setup
lake build FirTalos.ConcreteResumableWasm
```

Inspect `ConcreteSupportedFunction.validatedBody`,
`Fir.Wasm.supportedCodeWithJoins`, and
`ConcreteStructuredCompilerCurrentStepAdmission.code`.

## Expected semantics

Compiler admission should be derived from the actual declaration accepted by
`WasmSupported` and from a hereditary static validation invariant advanced in
lockstep with the existing dynamic structured relation. It should not be an
execution certificate supplied by the export theorem's caller.

## Actual behavior

Before the first repair slice, `ConcreteSupportedFunction` did not identify
its source declaration at all. The global relation also dropped the active
result equality before invoking compiler admission. Consequently the proof
could not connect a current adapted node to the exact validator judgment that
made it part of the compiler's supported domain.

## Proof or differential evidence

`CodeAdaptedWithSuffix.return_eq` supplies the compiled local kind but not the
directional result refinement required by
`ConcreteStructuredCodeStepAdmission.ret`. That refinement belongs to source
validation, not target adaptation. Similar gaps occur at joins and guarded
case/sharing paths where validation carries path-sensitive facts.

## Semantic impact

Without this provenance, a universal admission theorem would either remain
unprovable or require a new caller-supplied recursive certificate, contrary to
the intended self-verified compiler theorem.

## Classification and triage

This is a proof-relation invariant omission. It does not change source
semantics, the symbolic Wasm ABI, the concrete runtime, or generated code.

## Workaround

none

## Upstream tracking

none

## Progress

The first repair slice makes every `ConcreteSupportedFunction` retain its
exact source declaration, body identity, declaration lookup, and effective
result ABI. `ConcreteSupportedFunction.validatedBodyAt` now reconstructs the
real root `supportedCode` judgment at the active result kind, and the compiler
admission law receives the existing active-result equality. The remaining
work is to retain and advance the validator's current local/join/case/sharing
state through the structured relation, then derive each dynamic admission
constructor from that static state plus the successful source step.
