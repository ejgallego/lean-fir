---
id: FIR-BUG-wasm-none-saturated-closure-site-shape
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 791f2ac1c0ae89237e279df32cddeabd4a3c5722
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-07-30
reproduction: integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean
regression: integration/talos/FirTalos/ConcreteCompilerCorrectnessContract.lean
---

# Summary

`SaturatedClosureCallSite` currently records only a nonempty closure
application. It does not retain the semantic closure identity, the resolved
source declaration, or the equation saying that existing captures plus new
arguments exactly saturate that declaration. The production selection theorem
therefore cannot constructively prove that `compileClosureCandidatesForTarget`
emits a matching direct-call candidate.

## Minimal reproduction

Start with `SaturatedClosureCallSite` and
`SourceCallLetResult`. The site supplies the source local lookup and compiled
and evaluated new arguments, but no facts of the following form:

```text
findCell? sourceRuntime.heap location = some cell
cell.object = .closure function arity captures
context.program.findDecl? function = some target
arity = target.params.size
captures.size + argumentKinds.size = target.params.size
```

Moreover, `site.nonempty` does not distinguish exact saturation from
underapplication. The source interpreter accepts both, while
`SaturatedClosureDispatchSelectionInduction` concludes with a hereditary
direct-declaration theorem only.

## Exact commands

```text
rg -n "structure SaturatedClosureCallSite|def SaturatedClosureDispatchSelectionInduction" \
  integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean
rg -n "def compileClosureCandidatesForTarget|def compileClosureCandidateAt" \
  Fir/Wasm/Lower.lean
```

## Expected semantics

The saturated-call family should carry or derive a source/static resolution
fact identifying the live semantic closure, its declaration, and exact
saturation. From the validator's ABI facts, that resolution should prove that
the compiler enumeration contains the corresponding matcher and direct-call
body. Underapplication should remain in its distinct allocation theorem.

## Actual behavior

The source-facing constructor admits every nonempty closure application.
Candidate identity coverage and the direct-call versus partial-application
branch cannot be recovered from its fields. The abstract module-selection
premise can hide the gap by returning an arbitrary already-resolved candidate
family.

## Proof or differential evidence

`compileClosureCandidateAt` selects a direct call only when the fixed capture
count plus the new argument count reaches the target parameter count. The
current site exposes neither that equality nor the target parameter kinds.
`SourceCallLetResult` records only an arbitrary finite successful prefix and
does not itself encode the closure-flow invariant that created the source
closure.

## Semantic impact

No executable mismatch is known. The gap blocks a certificate-free proof of
production saturated dispatch and risks applying the direct-call hereditary
theorem to an underapplication source execution.

## Classification and triage

This is a W6 proof-interface omission at the source/lowering boundary. The
repair should expose a source/static closure-resolution fact and prove
compiler enumeration coverage from it. It must not add a target execution
certificate or treat nonemptiness as saturation.

## Workaround

none

## Resolution and regression

`SaturatedClosureCallSupported` now requires
`SaturatedClosureCallResolution`, which records the live source closure,
resolved declaration and ABI, exact saturation equation, argument/result
refinement, code body, and source parameter binding. The compiler-enumeration
theorems derive a candidate with that semantic identity from
`compileClosureCandidatesForTarget`; the canonical cache frame derives its
physical address and first executable match.

The production-facing
`SaturatedClosureCandidateResolutionInduction` supplies only the hereditary
implementation for such an identified compiler candidate.
`ofInternalCompilerResolved` composes those theorems into the saturated-call
implementation. Underapplication remains a separate allocation theorem.

## Upstream tracking

none
