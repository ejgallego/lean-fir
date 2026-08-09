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

The pure source closure should pass through the same object-family calling
representation as upstream Lean's final-LCNF emitter, without reconstructing
application-specific erased types.

## Actual behavior

Lean 4.32 erases the monomorphic result of reachable Nat- and USize-indexed
Array reads to `tobject`. Their actual `StepInfo`, `Segment`, nested `Array`,
and `String` element values are heap-only objects, but later calls and `oproj`
lowering correctly require `object`. The first mismatch appeared in
`actionAt`; capturing the real generated loop bodies exposed the complete
23-site recovery inventory, including two heap-only loop-accumulator
projections.

## Proof or differential evidence

The same real Illuminate `Animation.Types`, `Animation.Player`, and native
façade elaborate successfully under Lean 4.32 immediately before the FIR
capture and lowering failure.

## Semantic impact

Without object-family call compatibility, the complete Illuminate trace
closure cannot be emitted as Wasm, so the native participant cannot join the
differential traces.

## Classification and triage

The failure occurs after successful source elaboration and final-LCNF capture,
inside FIR's supported Wasm lowering validator. It is an erased generic-result
ABI mismatch, not an unsupported state-machine operation. The complete
runtime link includes the one owned `Array.get!Internal` call in `tick` in the
same fail-closed inventory.

## Workaround

The original package applied a fail-closed monomorphic ABI recovery tied to
the exact Illuminate Array targets and caller inventory. That workaround has
been removed.

## Upstream tracking

Current upstream Lean emits final LCNF directly and maps `object`, `tagged`,
and `tobject` to the same `lean_object*` call/control-flow representation in
`Lean.Compiler.LCNF.EmitC`; it does not recover caller-specific kinds.

## Resolution and regression

FIR now mirrors upstream's object-family compatibility at compiler-produced
named-call, return, and symbolic-stack boundaries while retaining directional
`AbiKind.refines` for runtime proof contracts. The unmodified Illuminate
capture passes lowering, and the application-specific recovery code has been
deleted. Both v3 and v4 resident artifacts remain byte-identical to the
previous accepted packages.
