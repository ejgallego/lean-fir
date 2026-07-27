---
id: FIR-BUG-wasm-none-json-int-precision
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-07-27
reproduction: Fir/Validation/Corpus.lean
regression: Fir/Validation/Protocol.lean
---

# Summary

Validation protocol v2 represented arbitrary signed integers as JSON numbers,
so Node could not audit or return multi-limb `Int` values exactly.

## Minimal reproduction

Run `int-multi-limb-negative-roundtrip`, whose argument is
`-(2^128 + 17)`. The compiler manifest reconstructs the exact Lean heap integer,
while the V8 adapter cannot represent the corpus datum with a JavaScript
`Number`.

## Exact commands

```sh
python3 scripts/validate_interpreters.py \
  --case int-multi-limb-negative-roundtrip \
  --plan validation-plans/native-lcnf-v8-scalars.json \
  --out-dir _build/validation-v8-int
```

## Expected semantics

The V8 adapter should cross-check the exact manifest argument, invoke the
compiler-produced identity function, and compare the exact signed result with
native Lean and the LCNF interpreter.

## Actual behavior

Protocol v2 encoded the signed payload as a JSON number. The adapter rejected
the value before emitting a result:
`argument 0 cannot be represented exactly by the validation JSON protocol`.

## Proof or differential evidence

Native Lean and the LCNF interpreter agreed on both positive and negative
`2^128 + 17` identities. The same negative case failed only at the Node protocol
boundary before V8 invocation, isolating the discrepancy from compilation and
LCNF evaluation.

## Semantic impact

Native-to-V8 validation could not carry or return arbitrary positive or
negative `Int` payloads outside JavaScript's exact integer range. This left
multi-limb signed-integer compilation unvalidated by the real Wasm engine.

## Classification and triage

This was a Wasm-adapter boundary issue in the shared validation wire format. It
required a coordinated protocol change rather than an adapter-local rounding
exception.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Validation protocol v3 encodes every semantic `Int` datum payload as a
canonical signed decimal string and decodes it back to Lean `Int`. Numeric
payloads, leading zeroes, and negative zero are rejected by compile-time
protocol guards. The Python harness, plans, native and LCNF codecs, Wasm
provider, and V8 runner moved atomically to version 3. The permanent corpus now
includes positive and negative `2^128 + 17` identities, and the full
native/LCNF/V8 matrix compares both exactly.
