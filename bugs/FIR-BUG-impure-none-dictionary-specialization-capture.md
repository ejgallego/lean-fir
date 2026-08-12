---
id: FIR-BUG-impure-none-dictionary-specialization-capture
status: candidate
classification: compiler
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: impure
pass: none
discovered-by: differential-test
first-seen: 2026-08-12
reproduction: Fir/Validation/Corpus.lean#capturedDictionaryUniqueFinalMutation
regression: none
---

# Summary

Isolated final-LCNF capture leaves compiler-generated typeclass method
specializations as opaque externals, so the interpreter faults before a valid
dictionary method call that native Lean executes successfully.

## Minimal reproduction

Construct a `CapturedByteArrayOps` typeclass dictionary whose two method
closures capture the same `ByteArray`. In the admitted S9 source, replace the
owner-bound helpers with the rejected implicit formulation below and point the
two entries directly at those helpers:

```lean
@[noinline]
def applyCapturedDictionaryMutation
    [operations : CapturedByteArrayOps] (byte : UInt8) : ByteArray :=
  operations.mutate byte

@[noinline]
def observeCapturedDictionary [operations : CapturedByteArrayOps] : Nat :=
  operations.observe ()

def capturedDictionaryUniqueFinalMutation (source : ByteArray) : ByteArray :=
  letI := makeCapturedByteArrayOps source
  applyCapturedDictionaryMutation 42

def capturedDictionaryRetainedObserver
    (source : ByteArray) : ByteArray × Nat :=
  letI := makeCapturedByteArrayOps source
  let updated := applyCapturedDictionaryMutation 42
  (updated, observeCapturedDictionary)
```

The final-LCNF entry calls
`applyCapturedDictionaryMutation._at_.capturedDictionaryUniqueFinalMutation.spec_0`,
but the captured program contains only an external stub for that generated
specialization. The retained case likewise lists the generated observer
specialization as an external.

## Exact commands

```sh
python3 scripts/validate_interpreters.py \
  --plan validation-plans/native-lcnf.json \
  --case captured-dictionary-unique-final-mutation \
  --case captured-dictionary-retained-observer \
  --out-dir _build/validation-s9-probe
```

## Expected semantics

Native Lean returns `[42, 127, 128, 255]` for the unique-final case. The
retained case returns the same updated array paired with observer result `0`,
because the retained sibling closure keeps the original capture shared across
mutation. Isolated final-LCNF capture should retain the generated
specialization bodies needed to execute the same calls.

## Actual behavior

Both LCNF runs stop at the first application with
`RuntimeFault.externalFailure`. The requested external is the generated
`applyCapturedDictionaryMutation...spec_0`, and the validation runtime reports
that it is not in the external allowlist. The unique and retained paths execute
only four and five interpreter steps respectively, before reaching any
dictionary construction, projection, closure invocation, or ByteArray
mutation.

## Proof or differential evidence

The focused matrix records two native-to-LCNF semantic mismatches. Native
returns the expected values, while LCNF captures 11/13 declarations but lists
the generated mutator specialization as an external in both cases and the
generated observer specialization as an additional external in the retained
case. Ordinary ByteArray externals are also present, showing that compilation
reached the intended method bodies but did not retain the specialization
declarations that lead to them.

## Semantic impact

Valid Lean programs that pass runtime typeclass dictionaries through implicit
arguments cannot be used as isolated native-oracle fixtures and may be
misclassified as foreign calls by any consumer of the same final-LCNF capture
path. This blocks dictionary runtime-representation and ownership validation.

## Classification and triage

Provisionally a compiler/capture-closure defect. The generated specialization
is part of the local compiled dependency closure, not a host external and not
an operation that should be added to the validation allowlist. Triage must
determine whether `LCNF.main`, `collectUsedDecls`, or generated-name cache
ownership loses the local specialization body.

## Workaround

Do not add the generated name to the external allowlist. The admitted S9
runtime dictionary fixture stores the same class value behind a named
non-class owner, which preserves dictionary construction, method projection,
and indirect invocation without requesting an implicit-call specialization.
The implicit specialization reproduction remains unresolved.

## Upstream tracking

none

## Resolution and regression

Unresolved. Retain both dictionary ownership cases as the differential
regression once final-LCNF capture includes the generated specialization
bodies.
