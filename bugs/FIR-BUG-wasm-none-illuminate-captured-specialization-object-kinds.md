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

FIR should accept the coarse final-LCNF object-family annotations through the
same representation-compatible call path used by upstream Lean, while
keeping scalar and ownership-specific distinctions explicit.

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

Without the generic object-family call path, FIR cannot emit the real captured
specialization closure. Retaining the former application-specific recovery
would hide this compiler-boundary discrepancy.

## Classification and triage

This is the same erased generic-result ABI class as the original Illuminate
Array issue, newly observable because final specialization bodies are
available. The resolution belongs to the generic compiler calling convention,
not an inventory of generated family names.

## Workaround

The original source boundary performed a checked monomorphic-kind recovery
over the exact Illuminate caller inventory. That workaround has been removed.

## Upstream tracking

Current upstream Lean's direct final-LCNF C emitter assigns `object`,
`tagged`, and `tobject` the same `lean_object*` calling representation and
emits ordinary assignments at calls and returns. FIR's compatibility boundary
now follows that generic rule without reconstructing erased application
types.

## Resolution and regression

The real final-LCNF closure now passes supported lowering without any
Illuminate-specific transform. Generic Array reads retain their upstream
`tobject` results, the resident Array implementation exposes the matching
generic signature, and object-family calls use the shared Lean-compatible
boundary. The v3 and v4 complete modules retain zero imports, their six public
functions, and their exact accepted Wasm hashes.
