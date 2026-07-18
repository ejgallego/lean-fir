---
id: FIR-BUG-wasm-none-json-nat-precision
status: candidate
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-07-18
reproduction: Fir/Validation/Corpus.lean
regression: none
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

This is currently a Wasm-adapter boundary issue. A durable fix likely requires
changing the shared validation protocol's natural payload to a decimal string
or another exact representation, then updating every backend codec together.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

unresolved
