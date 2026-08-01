---
id: FIR-BUG-impure-none-closure-application-external-runtime
status: candidate
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: dbd7d934863ada33d50b6db82ad89164793f5f03
phase: impure
pass: none
discovered-by: proof
first-seen: 2026-08-01
reproduction: Fir/LeanIR/Interpreter.lean
regression: none
---

# Summary

Closure application updates the waiting runtime, but external execution still
calls the foreign specification with the pre-application runtime and can
therefore discard or reverse the closure ownership transition.

## Minimal reproduction

Invoke an external declaration through an exclusive heap closure with
reference count one. `takeClosureApplication` marks that closure dead in the
waiting state before `invokeDecl` returns `.external`. Use an external
implementation that returns the heap and allocation frontier it receives.

`executeStep` passes the caller's original runtime to that implementation.
`resumeExternal` then installs the returned original heap into the waiting
state, making the consumed closure live again. The same mismatch affects a
shared closure: its decrement and capture retains can be replaced by the
pre-application heap.

## Exact commands

Inspect the two runtime choices and reproduce the failed proof obligation:

```text
rg -n "takeClosureApplication|externals.call request|inductive Step" Fir/LeanIR
lake build Fir.LeanIR.Passes.ElimDeadMachineRel
```

The build fails at `coreStep_invokeValue_external_runtime_eq`: that theorem
previously proved `waiting.runtime = state.runtime`, but the equality is false
after a successful non-persistent closure application.

## Expected semantics

The external implementation and `ExternalSpec` should observe the runtime in
the `.external` waiting state, after the closure ownership transition. Any
response heap should therefore extend or replace that post-application state,
not the stale caller state.

## Actual behavior

`executeStep` calls `externals.call request state.runtime`, and
`Step.external` records `externals request before.runtime response`. Both use
the runtime before `coreStep`. `resumeExternal` combines the response with
`waiting.runtime`, but replaces its heap and allocation frontier with the
response values, so a response derived from the old runtime can erase the
closure transition.

## Proof or differential evidence

The queued closure contract invalidates
`coreStep_invokeValue_external_runtime_eq` in
`Fir/LeanIR/Passes/ElimDeadMachineRel.lean`. Exclusive application changes the
closure cell to `rc = 0, live = false`; shared application changes the closure
RC and retains heap captures. Consequently the proof cannot transport an
external fact from `before.runtime` to `waiting.runtime` by equality.

The new proof-side `takeClosureApplicationBoth_related` theorem successfully
relates all ownership branches. The remaining external-step obligation is not
a missing relational lemma: it requires the shared interpreter contract to
select the post-application runtime.

## Semantic impact

External calls through non-persistent closures can resurrect exclusive
closures, undo shared reference-count updates, and discard capture retains.
The executable interpreter, relational `Step`, source-ownership proofs, and
pass-correctness simulations all observe the mismatch.

## Classification and triage

This is a shared FIR-semantics contract inconsistency. Update both
`executeStep` and `Step.external` to invoke external behavior with
`waiting.runtime`, then adjust soundness and external-compatibility proofs.
The concrete executor and relational semantics must change together.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

unresolved
