---
id: FIR-BUG-impure-elimDeadVars-full-heap-observation
status: confirmed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: impure
pass: elimDeadVars-0
discovered-by: proof
first-seen: 2026-07-22
reproduction: Fir/LeanIR/PassCorrectness.lean#SamePhaseCorrect
regression: Fir/LeanIR/Passes/ElimDeadExamples.lean#allocatingBeforeProgram
---

# Summary

FIR's same-phase correctness contract compares raw observations even though
`elimDeadVars` deliberately removes unused allocations whose only difference
is unreachable heap garbage.

## Minimal reproduction

Consider an impure declaration whose body allocates an unused constructor and
then returns an erased value:

```lean
.let { fvarId := dead, value := .ctor info #[], ... }
  (.let { fvarId := result, value := .erased, ... }
    (.return result))
```

Lean 4.32's `LetValue.safeToElim` returns `true` for `.ctor`, so
`elimDeadVars` removes the first binding. FIR's source interpreter executes
the constructor allocation and retains its cell in `Observation.heap`; the
target interpreter does not allocate that cell.

## Exact commands

From a clean checkout using the pinned toolchain:

```sh
sed -n '45,60p' Fir/LeanIR/Interpreter.lean
sed -n '1,165p' Fir/LeanIR/PassCorrectness.lean
sed -n '55,125p' \
  /home/egallego/.elan/toolchains/leanprover--lean4---v4.32.0/src/lean/Lean/Compiler/LCNF/ElimDead.lean
lake build Fir.LeanIR.Passes.ElimDeadExamples
```

The first command shows that `observe` copies the complete runtime heap. The
second shows that `SamePhaseCorrect` asks both runs to produce the same
`Observation`, despite defining the intended garbage-insensitive
`ObservationRel` later in the file. The third shows that `.ctor` is safe to
eliminate and that an unused safe binding is removed.

## Expected semantics

Same-phase impure pass correctness should compare observations with
`Impure.ObservationRel`, which relates returned values and reachable heap cells
up to address renaming while ignoring unreachable cells. The source and target
above should therefore be equivalent.

## Actual behavior

`SamePhaseCorrect (Impure.semantics externals)` quantifies one identical raw
observation on both sides. The source observation contains the dead constructor
cell and the target observation does not, so the whole-pass statement is false
for this intended compiler rewrite.

## Proof or differential evidence

The `allocatingBeforeProgram` regression is checked against Lean 4.32's actual
pass and the FIR interpreter. The compiler removes the constructor; both runs
return erased, and an executable guard proves that their raw heaps differ. The
kernel theorem `observationRel_returned_erased_ignore_heap` proves that
`ObservationRel` relates arbitrary heaps at exactly this observable boundary.

## Semantic impact

The current same-phase theorem shape cannot state correctness for the
allocating cases of `elimDeadVars`. The same issue affects later transformations
that reorder allocation, reset/reuse, or ownership operations while preserving
only reachable behavior.

## Classification and triage

This is classified as `fir-semantics`: the compiler behavior matches
the pass's documented safe-elimination policy, and FIR already contains the
appropriate reachable-heap relation but does not connect it to same-phase
correctness. The executable and kernel regressions show no additional
interpreter issue.

## Workaround

Prove the first vertical slice only for runtime-neutral safe values, keeping
the successful-evaluation and unchanged-runtime premise explicit. Do not claim
whole-pass correctness until the shared same-phase observation contract is
fixed and landed through the integration owner.

## Upstream tracking

none

## Resolution and regression

Unresolved. Introduce a shared relational same-phase correctness boundary (or
specialize the impure one to `ObservationRel`), prove the corresponding
stuttering lifting theorem, then lift the permanent unused-constructor
regression through that contract.
