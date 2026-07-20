---
id: FIR-BUG-wasm-none-json-nat-precision
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-07-18
reproduction: Fir/Validation/Corpus.lean
regression: Fir/Validation/Protocol.lean
---

# Summary

The JSON validation protocol represents arbitrary natural numbers as JSON
numbers, so Node cannot audit or return odd natural values above its exact
integer range.

## Minimal reproduction

Run the `nat-add-tagged-to-heap` case, whose first argument is
`9223372036854775807`. The compiler manifest reconstructs that exact tagged FIR
value, while Node's parsed corpus descriptor cannot represent the same integer.

## Exact commands

```sh
python3 scripts/validate_interpreters.py \
  --case nat-add-tagged-to-heap \
  --plan validation-plans/native-v8-scalars.json \
  --out-dir _build/validation-v8-w5-externals
```

## Expected semantics

The V8 adapter should cross-check the exact manifest argument against the exact
corpus datum, call `Nat.add`, and compare the heap-natural result with native
Lean without losing integer precision.

## Actual behavior

The corpus descriptor encodes the natural payload as a JSON number. Node parses
it through IEEE-754 `Number`, while the semantic host reconstructs the exact
payload through `BigInt`; the mandatory argument audit fails with
`argument 0 cannot be represented exactly by the validation JSON protocol`.

## Proof or differential evidence

The combined W5 external probe executes the V8 backend, which exits before the
case result is emitted. `nat-add-small` passes through the same external import,
isolating the discrepancy to protocol integer precision rather than external
dispatch.

## Semantic impact

Native-to-V8 cases cannot carry or return arbitrary `Nat` payloads above
JavaScript's exact integer range, including the tagged-to-heap transition and
many heap-natural arithmetic results. Native-to-LCNF and Talos-to-V8 artifact
checks are unaffected because their comparable observations encode large
runtime payloads as decimal strings.

## Classification and triage

This was a Wasm-adapter boundary issue caused by the shared validation wire
format. It required a coordinated protocol change rather than an adapter-local
rounding exception.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Validation protocol v2 encodes every arbitrary semantic `Nat` datum payload as
a canonical decimal string and decodes it back to Lean `Nat`. Numeric and
noncanonical decimal payloads are rejected by compile-time protocol guards.
The Python harness, validation plans, native and LCNF codecs, Wasm product
manifests, and V8 runner moved atomically to version 2. The permanent default
matrix now includes `large-nat`, `nat-list-roundtrip`,
`nat-add-tagged-to-heap`, and `nat-add-heap-input`, covering values above
JavaScript's exact integer range and above `UInt64`.
