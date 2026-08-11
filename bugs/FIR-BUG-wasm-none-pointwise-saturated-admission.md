---
id: FIR-BUG-wasm-none-pointwise-saturated-admission
status: fixed
classification: compiler
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-08-11
reproduction: integration/talos/FirTalos/ConcreteStructuredSimulation.lean
regression: integration/talos/FirTalos/ConcreteStructuredSimulation.lean
---

# Summary

The pointwise `saturatedCall` admission constructor records only a nonempty
closure-call site, so it does not justify routing the current runtime state to
the exactly saturated closure-entry theorem.

## Minimal reproduction

Construct `ConcreteStructuredCodeStepAdmission.saturatedCall site`.  The
stored `SaturatedClosureCallSite` proves that the new argument array is
nonempty, but exact saturation is stated only by a separate
`SaturatedClosureCallResolution context sourceRuntime site`.  An
underapplication or overapplication can therefore inhabit the admission while
requiring a different source control protocol.

## Exact commands

```text
rg -n "saturatedCall|structure SaturatedClosureCallSite|structure SaturatedClosureCallResolution" \
  integration/talos/FirTalos/ConcreteStructuredSimulation.lean \
  integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean
```

## Expected semantics

A current-node admission that selects the exactly saturated proof rule must
retain current-runtime closure resolution, including the arity equality and
the equation that fixed plus new arguments fill the declaration parameter
row exactly.

## Actual behavior

The constructor retains only syntax, argument compilation/evaluation, and a
nonempty-argument fact.  Those facts distinguish a closure application from a
local alias but do not distinguish exact saturation from partial application
or excess arguments.

## Proof or differential evidence

The relation-wide case split reaches
`ConcreteStructuredCodeCoreRel.advance_saturatedCall_stage`, but the following
`ConcreteStructuredSaturatedCallReadyCoreRel.advance_enter` requires a
`SaturatedClosureCallResolution`.  No such resolution follows from the
admission constructor, and manufacturing one would assert a false arity fact
for under- or overapplied closures.

## Semantic impact

The executable interpreter and compiler are not known to disagree.  The proof
relation is too weakly indexed to support its claimed exactly saturated case;
using it unchanged in the main simulation would overstate the admitted
fragment or require an unsound external selection premise.

## Classification and triage

This is a W6 compiler-proof interface omission.  Strengthen only the local
current-state admission with `SaturatedClosureCallResolution` and the existing
shared-capture capacity fact.  Do not add callee evaluation, a target path, a
future continuation admission, or a termination premise.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

`ConcreteStructuredCodeStepAdmission.saturatedCall` now retains the
current-runtime `SaturatedClosureCallResolution` and shared-capture capacity
needed by the exact entry rule.  The checked `let_cases` eliminator exposes
those witnesses only in the saturated branch, and
`ConcreteStructuredCodePointwiseRel.advance` consumes that branch to select
the production-generated callee row and construct the ranked zero-target-step
successor. Under- and overapplications therefore cannot enter the exact
saturation case.
