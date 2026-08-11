# FIR-native Illuminate HitScene package

This integration compiles the real Lean 4.32 entry

```lean
Illuminate.HitScene.query : HitScene → Float → Float → HitSceneResult
```

from clean Illuminate commit
`af088e313eaade90be100aeaf63ddac79a8c1710`. It publishes a complete,
zero-import Wasm module and a browser/Node adapter; it does not copy the
geometry algorithm, compile JSON inside Lean, or call JavaScript math helpers.

The canonical local pointer is:

```text
integration/illuminate-hit-scene/_build/illuminate-hit-scene-current
```

`BUILD.json` and `SHA256SUMS` inside the resolved immutable directory are the
authority for its source revisions, toolchains, closure inventory, ABI,
ownership policy, and content identity.

## Consumer API

The package exports `createIlluminateHitSceneAdapter` and
`fetchIlluminateHitSceneAdapter`. One adapter can create independent opaque
scene handles:

```js
const created = adapter.createHitScene(encodedScene);
const result = adapter.hitTest(created.scene, x, y);
const diagnostic = adapter.hitTestDiagnostic(created.scene, x, y);
adapter.disposeHitScene(created.scene);
```

`encodedScene` is Illuminate's canonical encoded HitScene JSON string. The
adapter parses and encodes it once into one module-owned Wasm instance per
scene. Coordinates cross the boundary as exact binary64 bits. No raw Wasm
address escapes.

The immutable scene graph lies below a persistent checkpoint. Query results
are copied to JavaScript; query scratch is cleared and rewound on success and
failure. Disposing a scene drops its instance and invalidates the opaque
handle. `BUILD.json` declares the shared runtime's low-memory reservation, and
the adapter starts the FIR arena above that prefix before encoding the scene.

## Build and publish

Create the clean source view once:

```sh
git -C /home/egallego/lean/illuminate worktree add --detach \
  /tmp/illuminate-hit-scene-pinned \
  af088e313eaade90be100aeaf63ddac79a8c1710
```

Install the repository-pinned Emscripten toolchain, then publish:

```sh
integration/lcnf-c-wasm/setup-emscripten.sh

cd integration/illuminate-hit-scene
ILLUMINATE_ROOT=/tmp/illuminate-hit-scene-pinned \
ILLUMINATE_HIT_SCENE_FIXTURE=/absolute/path/to/hit-scene-benchmark.json \
  node package.mjs
```

For the release gate, repeat from a clean FIR worktree and require the freshly
generated frontier and complete module to match the prior bytes:

```sh
ILLUMINATE_ROOT=/tmp/illuminate-hit-scene-pinned \
ILLUMINATE_HIT_SCENE_FIXTURE=/absolute/path/to/hit-scene-benchmark.json \
FIR_HIT_SCENE_REQUIRE_REPEAT=1 \
  node package.mjs
```

`FIR_HIT_SCENE_REUSE_FRONTIER=1` is a development convenience only. Immutable
publication must use fresh generation. `FIR_ALLOW_DIRTY_PACKAGE=1` exists for
diagnosis and must not be used for a release handoff.

The publisher writes an immutable directory named by the first 16 hex digits
of the complete package-inventory SHA-256, runs its packaged smoke test,
verifies every checksum, and atomically moves
`illuminate-hit-scene-current` only after the gate passes. Adapter or metadata
changes therefore publish a new directory even when the Wasm bytes are
unchanged.

## Accepted coverage

The package smoke checks:

- the exact zero-import module and six function exports plus module-owned memory;
- all 301 deterministic fixture queries and decoded `HitSceneResult` values;
- 10,000 additional queries with a flat post-rewind frontier;
- two independent scene instances;
- idempotent disposal, use-after-disposal rejection, and repeated create/dispose;
- malformed input rejection; and
- complete package checksums.

The closure contains 159 source declarations and 34 reviewed externals. The
resident frontier contains 439 functions and 15 C/libm Float operations before
the final merge. Exact counts, hashes, sizes, and inventories are ratcheted in
`closure-contract.json` and reproduced in package `BUILD.json`.

The standard C/libm boundary and checked export-preserving linker are shared
with other closed applications under `integration/wasm-runtime`; this package
does not carry a HitScene-specific runtime implementation.

See [CLIENT_HANDOFF.md](CLIENT_HANDOFF.md) for the concise tester handoff.
