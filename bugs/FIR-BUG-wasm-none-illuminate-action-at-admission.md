---
id: FIR-BUG-wasm-none-illuminate-action-at-admission
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-08-06
reproduction: integration/illuminate-player/Emit.lean
regression: integration/illuminate-player/IlluminateFirNative/Compile.lean
---

# Summary

FIR rejects the fully internalized final-LCNF closure of Illuminate's pure
animation trace entry at the private `AnimationPlayer.actionAt` declaration.

## Minimal reproduction

Compile `Illuminate.Animation.Native.replayTraceNative`, whose façade only
calls Illuminate's real `initialTransition` and `transition`, through the
checked capture in `IlluminateFirNative.Compile` and
`Fir.Wasm.Emit.Source.compileModuleArtifact`.

## Exact commands

From `integration/illuminate-player`, with an Illuminate source checkout at
`/home/egallego/lean/illuminate`:

```sh
lake --keep-toolchain \
  -KilluminateRoot=/home/egallego/lean/illuminate \
  lean Emit.lean
```

## Expected semantics

The pure, monomorphic source closure should pass FIR's supported-lowering
validator, or identify a precise unsupported final-LCNF instruction that can
be implemented and tested independently.

## Actual behavior

Lean 4.32 erases the monomorphic result of ten reachable `Array.get!` and
`Array.get?` calls to `tobject`. Their actual `StepInfo`, `Segment`, and
`String` element values are heap-only objects, but later `oproj` lowering
correctly requires `object`. The first mismatch appeared in `actionAt`.

## Proof or differential evidence

The same real Illuminate `Animation.Types`, `Animation.Player`, and native
façade elaborate successfully under Lean 4.32 immediately before the FIR
capture and lowering failure.

## Semantic impact

Without exact result recovery, the complete Illuminate trace closure cannot
be emitted as Wasm, so the native third participant cannot join Illuminate's
105 differential traces.

## Classification and triage

The failure occurs after successful source elaboration and final-LCNF capture,
inside FIR's supported Wasm lowering validator. It is an erased generic-result
ABI mismatch, not an unsupported state-machine operation.

## Workaround

The Illuminate capture applies a fail-closed monomorphic ABI recovery. It
checks the exact two target declarations, all ten expected caller sites, and
the original `tobject` signatures before changing the target and call results
to `object`.

## Upstream tracking

none

## Resolution and regression

The checked recovery admits the full 84-declaration final-LCNF closure. The
lowered base module is emitted successfully; resident-runtime closure is
tracked separately from this lowering bug.
