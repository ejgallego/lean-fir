---
id: FIR-BUG-impure-none-array-getinternal-validation-external
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

A proof-backed borrowed Array projection compiles to
`Array.getInternalBorrowed`, but the LCNF and semantic Wasm validation runtimes
implement only the checked `Array.get!InternalBorrowed` neighbor and reject the
valid source program.

## Minimal reproduction

Project a known in-bounds heap element from an Array without a fallback:

```lean
@[noinline]
def borrowedSecond (values : Array ByteArray) : ByteArray :=
  if h : 1 < values.size then
    values[1]'h
  else
    ⟨#[]⟩
```

## Exact commands

With that projection in the `repeated-byte-array-child-array-set-shared`
fixture, run:

```sh
python3 scripts/validate_interpreters.py \
  --plan validation-plans/native-lcnf-v8-scalars.json \
  --case repeated-byte-array-child-array-set-shared \
  --out-dir _build/validation-s11-array-alias-probe
```

## Expected semantics

For the two-element fixture, native Lean returns the second child without a
bounds diagnostic. The borrowed result remains valid while the source Array is
live, and downstream ownership code may retain it when necessary.

## Actual behavior

After successful `Array.size` and `Nat.decLt` calls, the LCNF interpreter stops
with `externalFailure Array.getInternalBorrowed "external is not in the
validation allowlist"`. The V8 semantic host enters the emitted module and
fails on the same name with `no external implementation installed`.

## Proof or differential evidence

The exact LCNF external trace is
`Array.size,Nat.decLt,Array.getInternalBorrowed`; the final form trace reaches
11 transitions before the fault. The resident Wasm Array surface already
exports and directly tests `Array.getInternalBorrowed`, whereas the two
validation external registries contain only `Array.get!InternalBorrowed`.

## Semantic impact

Native-oracle comparison cannot cover ordinary proof-backed Array reads, and
ownership fixtures that project heap children must either change their source
shape or stop before the memory-sensitive operation under test.

## Classification and triage

This is provisionally validation-runtime external coverage drift. The resident
implementation distinguishes borrowed `Array.getInternalBorrowed` from owned
`Array.getInternal`; the LCNF and semantic Wasm handlers must preserve that
ownership distinction rather than aliasing names blindly.

## Workaround

Supply an independently accessible alias in the validation input graph when a
fixture is testing a later operation. Do not rewrite the final LCNF call to the
checked `get!` variant.

## Upstream tracking

none

## Resolution and regression

Unresolved. Add owned and borrowed proof-backed read fixtures after both
validation runtimes implement their exact native contracts.
