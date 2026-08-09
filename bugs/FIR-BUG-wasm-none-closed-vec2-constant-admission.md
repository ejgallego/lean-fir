---
id: FIR-BUG-wasm-none-closed-vec2-constant-admission
status: fixed
classification: compiler
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-08-10
reproduction: integration/illuminate-hit-scene/Probe.lean
regression: integration/illuminate-hit-scene/Probe.lean
---

# Summary

FIR's former synthetic module capture made the compiler-generated closed
`Vec2` constant reachable from the real `Illuminate.HitScene.query` appear
unsupported.

## Minimal reproduction

Capture `Illuminate.HitScene.query` from clean Illuminate commit
`af088e313eaade90be100aeaf63ddac79a8c1710` through FIR's Lean 4.32 read-only
source view and lower the captured closure with
`Fir.Wasm.Emit.Source.compileModuleArtifact`.

## Exact commands

```sh
cd integration/illuminate-hit-scene
lake --keep-toolchain -KilluminateRoot=/tmp/illuminate-hit-scene-pinned \
  build IlluminateFirHitScene.Compile
lake --keep-toolchain -KilluminateRoot=/tmp/illuminate-hit-scene-pinned \
  env lean -DmaxHeartbeats=0 Probe.lean
```

## Expected semantics

The ordinary compiler-generated constant for `Illuminate.Vec2.east` should be
admitted and lowered with the same constructor representation used when a
`Vec2` is constructed dynamically. It is part of the real hit-test closure,
not an application-specific foreign operation.

## Actual behavior

The source view itself built under Lean 4.32, but the former synthetic capture
recompiled imported roots outside their original postponed declaration groups.
That changed private closed-term identities and left
`Illuminate.Vec2.east._closed_2` in a malformed apparent closure. Wasm
lowering then returned `ValidationError.unsupportedCode` for that name.

## Proof or differential evidence

The rejection occurs before resident runtime linking or external-engine
execution. `Probe.lean` records the exact captured declaration and external
inventories so the unsupported declaration can be minimized without changing
Illuminate's source.

## Semantic impact

This formerly blocked the real prepared HitScene query before its Float
operation frontier could be inventoried.

## Classification and triage

This was a compiler-capture discrepancy, not a Wasm admission gap. Lean 4.32's
ordinary `leanir` route records the source module's postponed declaration
groups and replays them in a private target-module environment. FIR did not
previously reproduce that boundary.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

`compileEntryModuleWiseInternalized` now imports each deferred target module
privately, applies the same target runtime-phase and direct-import setup as
Lean's `leanir`, initializes the required persistent extensions, and replays
the original postponed groups in a fresh `CoreM.State`. The exact private
lambda and closed-term names are therefore retained without FIR renaming.

The HitScene probe now internalizes `Illuminate.Vec2.east` and its closed
values normally. It reaches the genuine `endpointToCenter` partial-application
ABI frontier with 159 reachable declarations and no unsupported `Vec2`
declaration.
