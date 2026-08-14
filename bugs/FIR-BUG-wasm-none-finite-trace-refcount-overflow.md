---
id: FIR-BUG-wasm-none-finite-trace-refcount-overflow
status: confirmed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: 7fd2d2d97feb82ca7d905ec8db13e30c49aeab33
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-08-14
reproduction: integration/talos/FirTalos/ConcreteStructuredValidation.lean
regression: integration/talos/FirTalos/ConcreteResumableWasm.lean
---

# Summary

Successful source reference-count increment does not imply that the updated
unbounded semantic count fits the concrete runtime's `UInt32` object header.
The current ordinary-increment admission predicate contains that finite-word
condition, so it cannot be derived from compiler validation and a successful
source step alone.

## Minimal reproduction

Start from a related live source cell whose reference count fits `UInt32`, then
execute an ordinary `.inc` with an amount for which `cell.rc + amount` is at
least `UInt32.size`. The source `incValue` uses `Nat` and succeeds, while the
concrete header update has no bit-exact successor satisfying the existing
heap refinement.

## Exact commands

```text
make talos-setup
lake build FirTalos.ConcreteStructuredValidation
```

Inspect
`ConcreteStructuredValidationFocus.admit_incOrdinary_of_step` and the `fits`
field of `OrdinaryIncrementEffectSupported.inc`.

## Expected semantics

Compiler admission should recover the source/compiler operation class without
claiming that every unbounded source execution fits the finite wasm32 runtime.
The eventual finite-prefix theorem must state reference-count headroom as part
of its dynamic finite-runtime safety boundary, just as allocation headroom is
already separated from compiler admission. An unconditional theorem would
instead require bounded/OOM source semantics matching the concrete runtime.

## Actual behavior

The source step supplies the exact lookup and successful `incValue` equation,
but not `cell.rc + amount < UInt32.size`. The condition is currently embedded
inside the admission constructor rather than exposed by the runtime-safety
law, so the universal compiler-admission theorem is overconstrained.

## Proof or differential evidence

`ConcreteStructuredValidationFocus.admit_decOrdinary_of_step` constructs
ordinary-decrement admission from validation, local-row agreement, and the
source step alone. The parallel increment theorem requires precisely one
additional premise: for the looked-up heap cell, the incremented count fits
`UInt32`. No target path, witness, or continuation evidence is needed.

## Semantic impact

Without an explicit headroom boundary, a theorem claiming every finite source
prefix is simulated by wasm32 is false for prefixes that overflow a concrete
reference-count header. This is independent of source termination.

## Classification and triage

Move reference-count headroom out of compiler admission and into a unified
per-step finite-runtime safety law. Keep address-space and header-count safety
visibly independent from compiler validation, then feed both to the runnable
step classifier.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Unresolved. The first validator-derived increment theorem exposes the exact
premise without weakening the concrete header relation.
