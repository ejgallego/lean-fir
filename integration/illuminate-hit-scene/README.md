# Illuminate prepared HitScene source probe

This integration compiles the real
`Illuminate.HitScene.query : HitScene → Float → Float → HitSceneResult`
entry through FIR's Lean 4.32 final-LCNF source path. It does not copy the
algorithm, compile the JSON decoder, or modify Illuminate.

The accepted source view is a clean detached checkout at
`af088e313eaade90be100aeaf63ddac79a8c1710`. Create it outside this project,
then pass its absolute path through `illuminateRoot`; the source library is
built with `compiler.postponeCompile=true` so FIR can replay Lean's exact
module declaration groups without consuming Illuminate's `.lake` products.

```sh
git -C /home/egallego/lean/illuminate worktree add --detach \
  /tmp/illuminate-hit-scene-pinned \
  af088e313eaade90be100aeaf63ddac79a8c1710

cd integration/illuminate-hit-scene
lake --keep-toolchain --reconfigure \
  -KilluminateRoot=/tmp/illuminate-hit-scene-pinned \
  build IlluminateFirHitScene.Compile
lake --keep-toolchain \
  -KilluminateRoot=/tmp/illuminate-hit-scene-pinned \
  env lean -DmaxHeartbeats=0 Probe.lean
```

The probe writes `_build/hit-scene-probe.json` and the exact unsupported LCNF
to `_build/hit-scene-unsupported.lcnf`. At the current checkpoint it captures
159 reachable declarations, inventories 34 unresolved standard/runtime
operations including all eight expected geometry math functions, and reaches
one generic partial-application ABI blocker recorded as
`FIR-BUG-wasm-none-endpoint-partial-application-admission`.

This directory is a source-closure probe, not yet an artifact package. Package
generation, resident math, the browser adapter, fixture differential testing,
and bounded scratch ownership follow only after the shared compiler-admission
repair lands.
