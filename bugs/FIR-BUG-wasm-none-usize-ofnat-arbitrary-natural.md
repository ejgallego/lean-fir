---
id: FIR-BUG-wasm-none-usize-ofnat-arbitrary-natural
status: fixed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-08-20
reproduction: integration/talos/artifact/resident-fixed-width-client.mjs
regression: integration/talos/artifact/resident-fixed-width-client.mjs
---

# Summary

The resident `USize.ofNat` and `USize.ofNatLT` helpers trap on a valid
multi-limb Nat instead of returning its low 64 bits.

## Minimal reproduction

Allocate the canonical multi-limb Nat
`2^128 + 0xfedcba9876543210` and pass it to either resident conversion.

## Exact commands

From `integration/talos/artifact`:

```sh
lake exe fir-wasm-artifact resident-fixed-width \
  _build/resident-fixed-width.wasm
node run-resident-fixed-width.mjs _build/resident-fixed-width.wasm
```

## Expected semantics

Lean's `USize.ofNat` converts modulo `2^64`, so both helpers must return
`0xfedcba9876543210` for the reproduction value.

## Actual behavior

The helpers call the bounded `ResidentNumeric.validateNatural` accessors,
which reject the canonical arbitrary-limb representation before conversion.

## Proof or differential evidence

The real Wasm resident-fixed-width fixture traps at the `USize.ofNat` call.
The existing promoted one-limb case succeeds.

## Semantic impact

Compiled programs can trap on valid Lean Nat inputs whenever a value wider
than 64 bits reaches `USize.ofNat` or `USize.ofNatLT`.

## Classification and triage

This is a resident-runtime semantic mismatch. The generic
`ResidentBigNumeric` validation and indexed-limb accessors already implement
the required representation coverage.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

The checked fallback now uses `ResidentBigNumeric` validation and indexed
low/high limb access, while the new immediate branch decodes canonical tagged
Nats directly. The resident fixed-width fixture permanently checks immediate,
promoted one-limb, and arbitrary-limb inputs for both entry points.
