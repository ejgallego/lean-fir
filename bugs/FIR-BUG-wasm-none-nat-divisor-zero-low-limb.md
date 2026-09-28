---
id: FIR-BUG-wasm-none-nat-divisor-zero-low-limb
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.34.1
lean-revision: 5045d0056413266e57c625dcd7c365b10e377c52
phase: wasm
pass: none
discovered-by: remainder-boundary-audit
first-seen: 2026-09-28
reproduction: integration/talos/artifact/resident-nat-arithmetic-client.mjs
regression: integration/talos/artifact/resident-nat-arithmetic-client.mjs
---

# Summary

The resident Nat division and remainder wrappers classify a nonzero divisor
with a zero low 64-bit limb as zero. Found before the remainder-only optimization
on base 259408c5d82fcbefd64097daca821e0474160d66.

## Minimal reproduction

For n = 2^65 + 3 and d = 2^64, call fir_ext_Nat_div and fir_ext_Nat_mod
with valid canonical natural inputs in the zero-import arithmetic artifact.

## Exact commands

```sh
cd integration/talos/artifact
lake build fir-wasm-artifact
.lake/build/bin/fir-wasm-artifact resident-nat-arithmetic _build/resident-nat-arithmetic.wasm
node run-resident-nat-arithmetic.mjs _build/resident-nat-arithmetic.wasm
```

## Expected semantics

The quotient is 2 and remainder is 3. Only a genuinely zero divisor invokes
the Lean rules n / 0 = 0 and n % 0 = n.

## Actual behavior

An independent Node probe of the unchanged base artifact returns quotient 0
and remainder 36893488147419103235 (the original dividend).

## Proof or differential evidence

JavaScript BigInt division/remainder yields 2 and 3. Source inspection finds
both wrappers checking naturalLow(0) and naturalHigh(0) without the higher
limbs. The existing input validator already excludes heap representations
of zero; canonical zero is the immediate tagged word 1.

## Semantic impact

Valid arbitrary-precision inputs silently produce wrong results in both
operations, including powers of two at and above bit 64.

## Classification and triage

Resident implementation bug, not source capture or a required contract change.

## Workaround

None; do not narrow the admitted divisor domain.

## Upstream tracking

none

## Resolution and regression

Both wrappers now compare the validated divisor with canonical zero (tagged
word 1), without consulting only its low limb. Focused zero-import Wasm checks
pass 128 paired division/remainder cases (including rewritten remainder
callers), shared/aliased borrowed operands, canonical result extents and repeated
ordinary-result retirement. Beam reports zero diagnostics. This correctness
repair is isolated before the quotient-removal experiment; full candidate
gates and client acceptance are separate.
