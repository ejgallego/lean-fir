---
id: FIR-BUG-impure-none-uint64-box-tagged
status: confirmed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: impure
pass: none
discovered-by: differential-test
first-seen: 2026-08-26
reproduction: Fir/LeanIR/Runtime.lean
regression: Fir/Validation/Corpus.lean
---

# Summary

FIR represents a small final-LCNF `box UInt64` as a tagged immediate, while
Lean's `lean_box_uint64` always allocates a heap object. Compiler-generated
boxed wrappers therefore perform a valid unchecked `dec[ref]` that faults in
both FIR's interpreter and the resident Wasm runtime.

## Minimal reproduction

`boxUsesTaggedRepresentation LCNF.ImpureType.uint64 41` currently returns
true. A generic state-monad probe boxes the state `41`, unboxes it in the
compiler-generated wrapper, and then executes `dec[ref]` on the boxed value.
Native Lean returns normally; FIR's LCNF interpreter reports
`expectedHeapReference`, and the zero-import Wasm artifact traps in
`fir_dec_once`.

Lean 4.33's `lean.h` defines `lean_box_uint64` unconditionally via
`lean_alloc_ctor` and `lean_ctor_set_uint64`; it has no tagged-value branch.

## Exact commands

```sh
sed -n '2830,2875p' \
  ~/.elan/toolchains/leanprover--lean4---v4.33.0/include/lean/lean.h
sed -n '720,745p' Fir/LeanIR/Runtime.lean
sed -n '250,375p' Fir/Wasm/Emit/ResidentScalarBox.lean
```

## Expected semantics

Every boxed `UInt64` is a heap object, independent of payload. `unbox UInt64`
reads that scalar object and rejects tagged words, and an unchecked reference
decrement is valid.

## Actual behavior

The impure model and `ResidentScalarBox.boxUInt64Function` use an immediate
tag when the payload is below their physical threshold. The unchecked release
then rejects that immediate, correctly exposing the inconsistent boxing
choice.

## Proof or differential evidence

The original reachable inhabited-default probe returned `42` natively but
produced `RuntimeFault.expectedHeapReference` in `Fir.Validation.Lcnf.execute`
and a Wasm `unreachable` from `fir_dec_once`. Its captured final LCNF showed
`box` followed by the compiler-generated `dec[ref]`; the generated Wasm box
helper returned the tagged word `83` for payload `41`. Changing only the
unrelated probe state to `UInt32` made native, LCNF, and Wasm agree, isolating
the discrepancy to the `UInt64` representation choice.

## Semantic impact

Pure compiler-generated code can agree natively yet fault in both FIR's LCNF
oracle and emitted Wasm whenever a small `UInt64` crosses a generic boxed
boundary. `USize` and the wasm32/source-host treatment of `UInt32` should be
audited alongside the repair against Lean's exact target-specific boxing API.

## Classification and triage

This is a shared representation contract bug spanning the impure runtime,
W6 concrete boxing proofs, and W7 resident scalar helpers. Fix it through an
isolated integration-owned contract commit before dependent proof or
generation changes.

## Workaround

Do not use `UInt64` merely as an observable payload in unrelated generic
closure fixtures. This does not authorize changing application source types
that genuinely use `UInt64`.

## Upstream tracking

none

## Resolution and regression

The integration contract candidate makes semantic UInt64 boxes heap-only,
rejects tagged inputs at semantic `unbox UInt64`, and adds
`generic-discard-boxed-uint64-small` plus
`generic-discard-boxed-uint64-max`. Both compile the real source declaration to
the exact `box; fap; dec[ref]; return` ownership path, pin every executed form
and count, and agree between native Lean and the LCNF interpreter.

The bug remains confirmed until the W7 resident helper, external-engine
regression, and W6 concrete refinement are adapted to the same upstream
`lean_box_uint64`/`lean_unbox_uint64` representation.
