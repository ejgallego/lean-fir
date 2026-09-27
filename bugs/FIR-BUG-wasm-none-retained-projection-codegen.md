---
id: FIR-BUG-wasm-none-retained-projection-codegen
status: confirmed
classification: compiler
lean-toolchain: leanprover/lean4:v4.34.0-rc2
lean-revision: 6a10ac8c22beadecabdbb0919c2b50214762f91d
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-09-27
reproduction: integration/talos/retained-initializer/RetainedArrayCalls.lean
regression: none
---

# Summary

Lean's native compilation of pattern projections from the retained initializer
reported an unknown join point; the proof-only projections kernel-check.

## Minimal reproduction

The `capacityId`, `mkEmptySite` and `mkEmptyContinuation` definitions in
`RetainedArrayCalls.lean`, compiled as ordinary definitions rather than in its
`noncomputable section`. Each pattern-matches on `RetainedRC2.initializer.value`.
The following single projection also fails in a fresh batch process:

```lean
import RetainedDeclarations

def projectedCapacityId : Lean.FVarId :=
  match RetainedRC2.initializer.value with
  | .code (.let _ (.let capacity _)) => capacity.fvarId
  | _ => default
```

## Exact commands

First reproduce the retained project using its documented check script. Save
the minimal snippet above as the worktree-local
`.deps/retained-rc2/ProjectionProbe.lean`, then from that project run:

```sh
lake env lean ProjectionProbe.lean
```

Both Lean Beam's module check and independent batch elaboration reproduce the
failure. The batch command exits with status 1.

## Expected semantics

Projecting an identifier or a let node from a closed checked declaration should
compile, without changing its kernel value.

## Actual behavior

The frontend reported for all three definitions:
`compiler IR check failed ... Error: unknown join point 'block_0'`.
The isolated batch projection additionally reports an unreachable-code panic
in `Lean.Compiler.LCNF.Code.explicitBoxing.tryCorrectLetDeclType`.

## Proof or differential evidence

The same definitions and the actual-program call-admission/execution theorem
check when the projections are noncomputable. No differing source or target
execution observation has been demonstrated.

## Semantic impact

This affects executable compilation of proof-side projections, not the input
LCNF or emitted Wasm. It is not evidence of an unsound theorem.

## Classification and triage

Reproducible upstream compiler/elaboration issue on the captured input.
Minimization independent of the retained program remains to be done; the panic
does not by itself identify the pass which first introduced the malformed IR.

## Workaround

Keep these proof-only definitions noncomputable. The actual captured program
and production lowering are unchanged; kernel reduction still checks the
projection and call-shape equations.

## Upstream tracking

none

## Resolution and regression

unresolved
