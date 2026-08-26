---
id: FIR-BUG-wasm-none-adapter-if-branch-depth
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: 86e0f74a
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-08-25
reproduction: Fir/Wasm/Emit/ResidentRelease.lean
regression: integration/talos/FirTalos/Correctness/Adapter.lean
---

# Summary

The Talos proof adapter does not count an enclosing WebAssembly `if` label
when resolving a symbolic branch to an outer block or loop.

## Minimal reproduction

Adapt a symbolic loop whose body contains an `if` and whose taken arm branches
back to the loop.  The production binary encoder emits branch depth `1`,
because depth `0` denotes the anonymous `if` label.  The Talos adapter emits
depth `0`.

The production resident Array release loop in
`Fir/Wasm/Emit/ResidentRelease.lean` is a concrete witness.

## Exact commands

```text
make talos-setup
lake build FirTalos.Correctness.Adapter
lake build FirTalos.ConcreteResidentRelease
```

Inspect `Fir.Wasm.Emit.Binary.findLabelIndex?`, the `ifElse` case of
`Fir.Wasm.Emit.Binary.encodeInstruction`, and the corresponding cases of
`FirTalos.instruction`.

## Expected semantics

The proof adapter and production binary encoder must resolve every symbolic
branch against the same structured-control stack.  Anonymous `if` labels count
toward binary branch depth even though symbolic source branches cannot name
them.

## Actual behavior

The binary encoder extends its control stack with `none` under `ifElse`, so a
branch to the immediately enclosing loop has depth `1`.  The Talos adapter
retains only named `FVarId` labels and leaves that list unchanged under
`ifElse`, producing depth `0`.  Talos therefore exits the `if` and falls
through instead of taking the loop back-edge.

## Proof or differential evidence

`wp_arrayReleaseLoopBody_continue` cannot establish the resident Array loop
invariant with the adapter-produced program: `Wasm.wp_iff_cons` consumes a
`Break 0` at the `if` boundary.  The same branch encoded by
`Fir.Wasm.Emit.Binary` is `br 1`, which propagates as `Break 0` to the enclosing
loop and restarts it.

## Semantic impact

Structured Talos executions containing branches from inside an `if` to an
outer block or loop do not model the emitted Wasm binary.  This invalidates
that adapter path as evidence for production-code refinement.

## Classification and triage

This is a shared proof-adapter contract bug.  The symbolic instruction surface
and production binary encoder are correct; the generated Wasm bytes do not
change.

## Workaround

W6 resident-helper proofs spell the exact binary-faithful target program and
use branch depth `1` for a loop back-edge nested immediately under an `if`.
They do not use the current Talos adapter as production-provenance evidence
for that branch.

## Upstream tracking

none

## Resolution and regression

The Talos adapter now uses `LabelContext = List (Option FVarId)`, matching the
production encoder's control stack: blocks and loops contribute named entries,
while `if` contributes an anonymous entry.  Branch lookup skips anonymous
entries while counting them toward depth, so the minimal loop/`if` witness
adapts and encodes its back-edge as `br 1` in both paths.

The same context is threaded through `CodeAdapted`, case-chain decomposition,
active structured states, suspended frames, and the reusable runtime-refinement
relations.  The executable regression in
`integration/talos/FirTalos/Correctness/Adapter.lean` compares the adapter with
`Fir.Wasm.Emit.encodeWithOrigins` on the exact nested shape.
