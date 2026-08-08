---
id: FIR-BUG-wasm-none-illuminate-captured-specialization-object-kinds
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-08-08
reproduction: integration/illuminate-player/Emit.lean
regression: integration/illuminate-player/IlluminateFirNative/Compile.lean
---

# Summary

Capturing Lean's real private Illuminate specializations exposes five further
monomorphic heap-object values whose final-LCNF types remain `tobject`. FIR's
fail-closed Wasm admission correctly rejects the resulting named calls.

## Minimal reproduction

Clear Lean's imported specialization cache inside an isolated compiler
environment, capture the final-impure SCCs for
`Illuminate.AnimationPlayer.replayTrace`, prune the result from that entry and
`transitionPrepared`, and run `Fir.Wasm.lowerSupported`.

## Exact commands

From `integration/illuminate-player`:

```sh
lake --no-cache --rehash --keep-toolchain \
  -KilluminateRoot=/home/egallego/lean/illuminate-vir-performance \
  build IlluminateFirNative.Compile
lake --keep-toolchain \
  -KilluminateRoot=/home/egallego/lean/illuminate-vir-performance \
  env lean Emit.lean
```

## Expected semantics

The generated specializations should retain heap-only object kinds at their
monomorphic Array and product-projection sites, allowing the real final-LCNF
bodies to pass the supported Wasm boundary.

## Actual behavior

The first rejected declarations and exact call-kind mismatches are:

- `List.forIn'.loop._at_.Illuminate.AnimationPlayer.replayTrace.spec_0._redArg`:
  `transitionPrepared` expects `[object, object, tobject]` but receives
  `[object, tobject, tobject]`; the second argument is the `PlayerState`
  projection from the loop accumulator. The same accumulator's action-array
  projection subsequently reaches `Array.push` as `tobject` instead of its
  required heap `object`.
- `Array.forIn'Unsafe.loop...validatePrepared.spec_2`: `Array.size` expects an
  `object` array but receives the `tobject` result of `Array.ugetBorrowed`.
- `Array.forIn'Unsafe.loop...validatePrepared.spec_3`: its call to `spec_2`
  expects an `object` segment/parameter array but receives the corresponding
  `tobject` result of `Array.ugetBorrowed`.

The same captured closure has three reachable `Array.ugetBorrowed` sites in
the checked validation specialization family; all three elements are
heap-only arrays or structures.

## Proof or differential evidence

The capture contains the real generated specialization bodies and no
Illuminate-specific replacement implementation. Reuse-capacity validation is
green for all declarations; only `supportedDecl` rejects the three
declarations above.

## Semantic impact

Without checked monomorphic kind recovery, FIR cannot emit the real captured
specialization closure. Retaining the former handwritten resident helpers
would hide this compiler-boundary discrepancy.

## Classification and triage

This is the same erased generic-result ABI class as the existing checked
Illuminate Array refinement, newly observable because final specialization
bodies are now available. Any recovery must enumerate the exact generated
families and call-site counts and fail closed on closure drift.

## Workaround

The Illuminate source boundary performs a checked monomorphic-kind recovery
over exactly 23 sites: the existing Nat-indexed Array reads, three
`Array.ugetBorrowed` results in the generated validation family, and the two
heap-only fields projected from `replayTrace`'s generated loop accumulator.
It checks every original erased kind, caller family, target declaration, and
site count before changing any result to `object`; closure drift fails the
build.

## Upstream tracking

none

## Resolution and regression

The real 115-declaration final-LCNF closure now passes supported lowering and
retains 25 generated specializations as source functions. The complete module
has zero imports and exactly four public functions. The deterministic package
gate, packaged 11-call smoke, and all 105 local legacy/FIR differential traces
pass.
