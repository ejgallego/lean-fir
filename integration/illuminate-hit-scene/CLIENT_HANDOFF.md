# HitScene package tester handoff

Use the resolved immutable directory behind:

```text
/home/egallego/lean/fir/.worktrees/wasm-generation/
  integration/illuminate-hit-scene/_build/illuminate-hit-scene-current
```

Verify it before staging:

```sh
cd /home/egallego/lean/fir/.worktrees/wasm-generation/integration/illuminate-hit-scene/_build/illuminate-hit-scene-current
sha256sum -c SHA256SUMS
node smoke.mjs
```

The package contains:

```text
illuminate-hit-scene.wasm
illuminate-hit-scene.wasm.json
illuminate-hit-scene-browser-adapter.mjs
hit-scene-benchmark.json
BUILD.json
SHA256SUMS
smoke.mjs
```

The compiled entry is the real
`Illuminate.HitScene.query : HitScene → Float → Float → HitSceneResult` from
clean Illuminate commit `88dcfee895a55e804641bff485024cffec1b5419`.
The final module is self-contained, owns its memory, has zero imports, and
exports only the structured entry, its bit-exact-coordinate facade, four heap
operations, and memory.

The admitted input capability is `lean-4.33-Illuminate.HitScene/v2`. Its path
constructor includes the four prepared Float bounds emitted by Illuminate;
v1 packages and scenes are incompatible and must not be staged.

Import either adapter constructor:

```js
import {
  createIlluminateHitSceneAdapter,
  fetchIlluminateHitSceneAdapter,
} from "./illuminate-hit-scene-browser-adapter.mjs";
```

The application-facing operations are:

```text
createHitScene(encodedScene)
hitTest(scene, x, y)
hitTestDiagnostic(scene, x, y)
disposeHitScene(scene)
```

The handle is opaque. Each scene owns one instance; its encoded graph is
retained below a checkpoint, each result is copied to JavaScript, and scratch
is cleared and rewound after every query. Coordinates retain their exact
binary64 bits. `hitTestDiagnostic` additionally reports timings and frontier
movement.

Accepted local evidence is 301 fixture queries, 10,000 flat-frontier repeated
queries, independent instances, disposal/error paths, zero imports, exact
exports, and complete checksums. Read `BUILD.json` rather than copying sizes or
hashes from this note; it is the package's versioned capability and source
manifest.
