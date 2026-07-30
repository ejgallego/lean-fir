---
id: FIR-BUG-wasm-none-big-numeric-recursive-walker-stack-overflow
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-07-30
reproduction: integration/talos/artifact/resident-big-numeric-client.mjs
regression: integration/talos/artifact/resident-big-numeric-client.mjs
---

# Summary

The Wasm-resident arbitrary-precision Nat/Int helpers implement their limb
walkers with recursive Wasm calls. Valid sufficiently large inputs therefore
exhaust the engine call stack even though the module has enough linear memory
to represent and process them.

## Minimal reproduction

Construct two equal Naturals whose highest set bit is at limb 8,192, then call
the exported `Nat.decEq` helper. The descending comparison recursively calls
`fir_big_numeric_compare_at` once per limb.

## Exact commands

From `integration/talos/artifact`, emit the recursive baseline and run the
resident client with its large-limb acceptance case:

```sh
lake exe fir-wasm-artifact resident-big-numeric \
  _build/resident-big-numeric.wasm
node run-resident-big-numeric.mjs _build/resident-big-numeric.wasm
```

## Expected semantics

`Nat.decEq` returns true for the two equal inputs. Numeric helper stack usage
is independent of the number of represented limbs; input size is bounded by
linear-memory and allocation limits rather than the native Wasm call stack.

## Actual behavior

Node 24.18.0 raises:

```text
RangeError: Maximum call stack size exceeded
```

The repeating frame is the recursive `fir_big_numeric_compare_at` helper.

## Proof or differential evidence

The existing 256- and 384-bit arithmetic, comparison, and conversion corpus
passes. Raising the same operation to 8,192 limbs fails before producing a
semantic result. The input is canonical and is accepted by the resident
Natural layout validator.

## Semantic impact

The resident helper set claims canonical arbitrary-precision Nat/Int support,
but its operational domain is engine-stack-dependent. The same recursive
shape is used by copy, carry, sum-write, borrow-scan, and difference-write
walkers, so several otherwise valid arithmetic operations share the limit.

## Classification and triage

This is a W7 generator implementation defect. It does not require a change to
the W6 numeric layout or helper signatures. The landed symbolic Wasm loop
surface can express the same iteration without recursive calls.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

All six recursive limb walkers now use structured Wasm loops while preserving
their existing helper signatures. The standalone client checks equality,
carry-producing addition, borrow-producing subtraction, and Nat-to-Int copying
at 8,192 limbs. The production browser adapter also renders a tagged/nested
Format with 8,192-limb Nat/Int inputs and checks the exact styled trace in Node
and Chrome.
