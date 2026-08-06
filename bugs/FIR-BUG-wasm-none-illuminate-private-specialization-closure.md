---
id: FIR-BUG-wasm-none-illuminate-private-specialization-closure
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: external-engine
first-seen: 2026-08-06
reproduction: integration/illuminate-player/Emit.lean
regression: integration/illuminate-player/check-player-traces.mjs
---

# Summary

The real Illuminate whole-trace entry lowered successfully, but its final
LCNF closure retained four private compiler specializations as host imports.
That prevented publication as a self-contained runtime package.

## Minimal reproduction

Compile `Illuminate.Animation.Native.replayTraceNative`, link the reusable W7
resident runtime, and inspect `WebAssembly.Module.imports` on the resulting
module.

## Exact commands

From `integration/illuminate-player`, with an Illuminate source checkout at
`/home/egallego/lean/illuminate`:

```sh
lake --keep-toolchain \
  -KilluminateRoot=/home/egallego/lean/illuminate \
  env lean Emit.lean
node check-player-traces.mjs
```

## Expected semantics

The whole-trace module owns its memory and contains every operation reachable
from the pure Illuminate player. JavaScript only transfers a fresh structured
input graph, invokes the entry, and decodes the structured result.

## Actual behavior

The remaining import frontier was exactly:

- `Array.findIdx?.loop._at_.Illuminate.AnimationPlayer.findSegment.spec_0`;
- the private unit-stride range loop in `parameterUpdates`;
- `Option.instBEq.beq._at_.Lean.PrettyPrinter.Delaborator.delabRange.spec_0`;
- the private unit-stride range loop in `findCrossedPause`.

Attempting to bootstrap every private matcher body into a fresh compilation
unit expanded the entry closure from 84 to 200 declarations and introduced
unrelated representation-polymorphic matcher results. The extra declarations
were compiler ancestry, not source-level dependencies of the player.

## Proof or differential evidence

The linked module reports no WebAssembly imports. Its browser adapter agrees
field-for-field with Illuminate's legacy player across five focused and 100
deterministic randomized traces, including Float timestamp and Unicode paths.
The packaged smoke additionally executes every `PlayerEvent` constructor.

## Semantic impact

Leaving any of these operations imported would make the native participant
depend on undocumented JavaScript runtime handlers and violate the complete
runtime package contract.

## Classification and triage

This is a final-LCNF packaging boundary issue. The missing bodies are generated
specializations with exact monomorphic call shapes, not a missing copy of the
Illuminate state machine.

## Workaround

`Fir.Wasm.Emit.ResidentIlluminatePlayer` recognizes the exact four imported
names and signatures and links structured Wasm loops for their generated call
shapes. It fails closed if the names, signatures, range conventions, or import
inventory drift. The helpers allocate through the module-owned resident arena;
they do not call a host runtime.

## Upstream tracking

none

## Resolution and regression

The emitted module has zero function imports and zero memory imports. Native
Lean guards cover the façade, the package smoke covers all event constructors
and repeated calls, and 105 deterministic/randomized traces compare every
decoded `FrameAction` with Illuminate's legacy JavaScript oracle.
