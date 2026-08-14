---
id: FIR-BUG-impure-none-array-mkempty-validation-external
status: candidate
classification: validation-harness
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: impure
pass: none
discovered-by: differential-test
first-seen: 2026-08-14
reproduction: Fir/Validation/Corpus.lean#repeatedByteArrayChildArraySetShared
regression: none
---

# Summary

Compiler-produced source Array literals call `Array.mkEmpty`, but neither the
LCNF validation interpreter nor the semantic Wasm host implements that runtime
external, so both candidates diverge from native Lean before the first push.

## Minimal reproduction

Compile and execute a source declaration that constructs a non-constant Array
literal:

```lean
@[noinline]
def repeatedByteArrayChildArraySetShared
    (source replacement : ByteArray) :
    Array ByteArray × Array ByteArray × ByteArray :=
  let original := #[source, source]
  let updated := original.set! 0 replacement
  let changed := source.set! 0 42
  (original, updated, changed)
```

The literal compiles to the external sequence `Array.mkEmpty`, `Array.push`,
`Array.push`; execution faults on its first operation.

## Exact commands

With the source-literal formulation above selected as the
`repeated-byte-array-child-array-set-shared` corpus entry, run:

```sh
python3 scripts/validate_interpreters.py \
  --plan validation-plans/native-lcnf-v8-scalars.json \
  --case repeated-byte-array-child-array-set-shared \
  --out-dir _build/validation-s11-probe
```

## Expected semantics

Native Lean returns the original repeated-child Array, an updated Array whose
first element is the replacement, and a copy-on-write mutation of the retained
child. `Array.mkEmpty` is a pure runtime primitive and should create the empty
generic Array from which the two pushes proceed.

## Actual behavior

Native Lean returns
`([[0,127,128,255],[0,127,128,255]],
[[255,1,2,3],[0,127,128,255]],[42,127,128,255])`.
The LCNF interpreter stops after four transitions with
`externalFailure Array.mkEmpty "external is not in the validation allowlist"`.
The V8 semantic host exits with
`externalFailure Array.mkEmpty "no external implementation installed"` and
therefore emits no result record.

## Proof or differential evidence

The captured program contains five declarations and lists the exact external
closure `Array.mkEmpty,Array.push,Array.set!,ByteArray.set!`. Its dynamic LCNF
trace is only `lit,fap,extern`, with `Array.mkEmpty` as the sole dispatched
external. The Wasm provider successfully emits the module and manifest; V8
instantiates and enters the module before the semantic host rejects the same
external.

## Semantic impact

Valid Lean source that constructs an Array literal from runtime values cannot
be compared against either validation candidate. This also prevents ownership
fixtures from exercising repeated child insertion through ordinary source
syntax, even though `Array.push` itself is modeled.

## Classification and triage

This is provisionally a validation-runtime coverage gap rather than a compiler
bug: `Array.mkEmpty` is present in final LCNF by design, and the resident Wasm
Array surface already declares a helper for it. The missing implementations are
the LCNF external dispatch and the semantic Wasm external registry. Their
ownership contract should be aligned with native Lean and the resident helper
before the external is allowlisted.

## Workaround

Materialize the initial Array through the existing validation argument schema
when a fixture is testing later Array operations. Do not translate source Array
literals away or silently substitute another external in captured LCNF.

## Upstream tracking

none

## Resolution and regression

Unresolved. Once both validation runtimes implement the external, restore a
small source-literal case that pins `Array.mkEmpty` followed by two
`Array.push` calls in native, LCNF, and V8.
