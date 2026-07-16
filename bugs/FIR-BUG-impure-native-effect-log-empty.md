---
id: FIR-BUG-impure-native-effect-log-empty
status: closed-not-a-bug
classification: upstream-drift
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: impure
pass: none
discovered-by: differential-test
first-seen: 2026-07-16
reproduction: Fir/Validation/Corpus.lean#effect-record-nat
regression: Fir/Validation/Corpus.lean#effect-record-nat
---

# Summary

A source function with an `implemented_by` native effect recorder returns the
implemented result but the native oracle observes an empty recorder log.

## Minimal reproduction

`Source.recordOnce` calls `Source.record`, whose safe definition and native
implementation both return the input plus one.  The native implementation also
pushes one `EffectEvent` into a module-level `IO.Ref`.  Running the source on 7
returns 8, but draining that reference immediately afterward returns no events.

## Exact commands

From the native-validation worktree containing the `effect-record-nat` fixture:

```sh
python3 scripts/validate_interpreters.py \
  --case effect-record-nat --out-dir /tmp/fir-effect-validation
```

## Expected semantics

Native Lean should return 8 and report one `validation.record` event with
argument 7 and result 8.  The LCNF interpreter should project the matching
external call into the same observation.

## Actual behavior

Both backends return 8.  LCNF reports the expected event, while native Lean
reports an empty `effects` array.

## Proof or differential evidence

The validation harness reports a semantic mismatch whose only difference is
the missing native event.  The LCNF artifact retains and executes
`Fir.Validation.Corpus.NativeEffects.recordImpl`, confirming that the source
fixture reaches the intended external boundary after final-impure lowering.

## Semantic impact

Until classified, the validation corpus cannot use this recorder arrangement
as a trustworthy native oracle for controlled effects.  This does not yet
indicate that Lean program semantics or FIR's external trace is wrong; it may
be an initialization, native-code generation, or optimization issue in the
test harness construction.

## Classification and triage

Generated C showed that `recordImpl` was called correctly.  The native runner
then drained the log before evaluating its nominally pure `native` thunk: Lean
was free to reorder that evaluation because the hidden effect came from
`unsafeBaseIO`.  This is closed as not a Lean or FIR semantics bug.  The
`upstream-drift` classification records where the candidate was initially
observed rather than assigning an upstream defect.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

The native effect hook now accepts the computed `ValidationDatum`, creating an
explicit data dependency from source execution to log drain.  Generated C and
the `effect-record-nat` differential case confirm the intended order.  During
triage, a Beam-generated interface paired with a stale native object briefly
caused an ABI crash; a rehashed Lake build rebuilt the complete dependency cone
before the semantic rerun.
