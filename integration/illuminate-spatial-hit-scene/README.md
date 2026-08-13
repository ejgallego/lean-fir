# FIR-native Illuminate SpatialHitScene package

This integration compiles Illuminate's real spatial preparation and query:

```lean
Illuminate.SpatialHitScene.ofHitScene : HitScene → SpatialHitScene
Illuminate.SpatialHitScene.query : SpatialHitScene → Float → Float → HitSceneResult
```

The source contract is pinned to Illuminate revision
`3b912826fdb39b27e214b3fef91c2b08c000bfea` plus exact hashes for the six
relevant source files. A clean descendant checkout is accepted only when all
those hashes and both oracle-fixture hashes remain exact. FIR compiles the
source with Lean 4.33 from a read-only Lake source view and never consumes
Illuminate's `.lake` products.

The canonical local pointer is:

```text
integration/illuminate-spatial-hit-scene/_build/illuminate-spatial-hit-scene-current
```

`BUILD.json` and `SHA256SUMS` in the immutable resolved directory are the
authority for source identity, toolchains, closure inventory, ABI, ownership,
and package contents.

## Boundary and ownership

The browser adapter exposes:

```js
const created = adapter.createHitScene(encodedScene);
const result = adapter.hitTest(created.scene, x, y);
const diagnostic = adapter.hitTestDiagnostic(created.scene, x, y);
adapter.disposeHitScene(created.scene);
```

`createHitScene` parses and encodes Illuminate's canonical `HitScene` once,
then calls the compiled `SpatialHitScene.ofHitScene` inside Wasm. Guard
construction, composition balancing, region transforms, and all hit-testing
semantics remain in Lean. The source graph and Lean-produced spatial graph are
retained below an instance-local checkpoint.

The production query path makes no clock calls. It invokes the bit-exact Float
facade for a thin Lean boundary:

```lean
def queryBorrowed (scene : @& SpatialHitScene) (x y : Float) : HitSceneResult :=
  SpatialHitScene.query scene x y
```

The annotation lets Lean's own ownership pipeline borrow the persistent root;
JavaScript does not reinterpret an owned call. Results and strings are copied
before scratch is cleared and rewound. No raw Wasm address escapes. Disposal
invalidates the opaque handle and drops its instance.

Advertised capabilities are:

```text
browser API:  fir.illuminate-spatial-hit-scene.browser/v1
input layout: lean-4.33-Illuminate.SpatialHitScene/v1
ownership:    fir.illuminate-spatial-hit-scene.persistent-checkpoint/v1
```

## Build and publish

Install the repository-pinned Emscripten toolchain, then publish from a clean
FIR worktree:

```sh
integration/lcnf-c-wasm/setup-emscripten.sh

cd integration/illuminate-spatial-hit-scene
ILLUMINATE_ROOT=/home/egallego/lean/illuminate/.worktrees/vir-hit-scene \
  node package.mjs
```

The source checkout may be the exact pin or a clean descendant with identical
relevant files and fixtures. For deterministic release acceptance, run the
same command again with:

```sh
FIR_SPATIAL_HIT_SCENE_REQUIRE_REPEAT=1
```

`FIR_SPATIAL_HIT_SCENE_REUSE_FRONTIER=1` is development-only.
`FIR_ALLOW_DIRTY_PACKAGE=1` is diagnostic-only and must not be used for an
immutable handoff.

The publisher atomically advances the canonical pointer only after it has
linked the shared C/libm runtime, verified zero imports and exact exports, run
the packaged smoke, and checked every package digest.

Run the order-balanced FIR reference/spatial comparison with at least seven
measured rounds after warmup:

```sh
node benchmark.mjs
```

The raw samples and median, p95, MAD, minima, maxima, paired query delta,
creation delta, resident bytes, and Wasm sizes are written to
`_build/spatial-benchmark.json`. Production `hitTest` is measured externally;
the benchmark does not insert clocks into the untimed adapter path.

## Ratcheted coverage

The closure contains 194 source declarations and 41 reviewed externals. The
resident frontier contains 780 functions, zero runtime operations, and the
same 15 standard Float/libm declarations used by the accepted reference
package before the final zero-import merge.

The package smoke covers:

- the 83 bounds, 301 mixed, and 625 path-heavy shared-oracle queries;
- bit-exact binary64 coordinates, including signed zero and adjacent values;
- spatial preparation exactly once for each retained scene;
- 10,000 queries with a flat post-rewind frontier;
- two independent scenes and repeated create/dispose cycles;
- idempotent disposal, use-after-disposal rejection, and malformed input;
- exact zero imports, the two application functions, four arena functions,
  and module-owned memory; and
- complete package checksum verification.
