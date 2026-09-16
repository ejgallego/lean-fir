# Build examples

This page is a navigation index, not another manifest. The linked Lean and
JavaScript registries remain the sources of truth for exact inventories, and
their acceptance checks reject drift.

For the wider source/build/adapter/client relationship across FIR, VIR and
consumer repositories, see the [configuration map and analysis](package-build-client-map.md).
The index below distinguishes accepted outputs, recipe-level integrations and
branch-only work. A build directory or a generated pointer alone is not an
acceptance claim.
For evidence-first retirement decisions, see the
[consumer cleanup audit](consumer-cleanup-audit.md).

## Consumer packages

| Package | Status | Lean entry | Build and acceptance gate | Canonical pointer |
| --- | --- | --- | --- | --- |
| [FIR-native styled `prettyM`](../integration/talos/artifact/prettyM-package/README.md) | accepted W7 package | `Fir.Wasm.Emit.SourceFixture.prettyFormatTraceRaw` | `bash integration/talos/artifact/check.sh` | `integration/talos/artifact/_build/prettyM-current` |
| [Illuminate full-action player](../integration/illuminate-player/README.md) | accepted; retained as the full-action oracle | `Illuminate.AnimationPlayer.initialLive`, `transitionLive` | `ILLUMINATE_ROOT=/clean/pinned/illuminate bash integration/illuminate-player/check.sh` | `integration/illuminate-player/_build/illuminate-player-current` |
| [Illuminate selection player](../integration/illuminate-player/README.md#selection-only-v4-package) | accepted; preferred compact player | `Illuminate.AnimationPlayer.initialSelectionLive`, `transitionSelectionLive`, and the bit-exact tick facade | same Illuminate gate | `integration/illuminate-player/_build/illuminate-selection-player-current` |
| [Illuminate prepared HitScene](../integration/illuminate-hit-scene/README.md) | accepted W7 query package | `Illuminate.HitScene.query` and its bit-exact coordinate facade | `ILLUMINATE_ROOT=/clean/pinned/illuminate ILLUMINATE_HIT_SCENE_FIXTURE=/fixture.json FIR_HIT_SCENE_REQUIRE_REPEAT=1 node integration/illuminate-hit-scene/package.mjs` | `integration/illuminate-hit-scene/_build/illuminate-hit-scene-current` |
| [C/Emscripten styled `prettyM`](../integration/lcnf-c-wasm/prettyM-emscripten-package/README.md) | accepted alternative backend | `Fir.LCNFC.PrettyM.renderWire` | `bash integration/lcnf-c-wasm/package-prettyM-emscripten.sh` | `integration/lcnf-c-wasm/_build/prettyM-emscripten-current` |

An accepted package has a real source entry, immutable publication,
`BUILD.json`, complete checksums, a packaged smoke test, an explicit ABI and
ownership contract, and a deterministic acceptance gate. Generated `_build`
pointers are conveniences; their package metadata is authoritative.

## Additional package recipes

These integrations have their own source pins, policies and gates. Consult
the linked policy and the selected package's `BUILD.json` for acceptance;
do not infer it from this navigation table.

| Integration | Boundary and status | Recipe / policy |
| --- | --- | --- |
| lean-zip | Stored control, Level-1 and production raw levels 1–10; distinct ByteArray oracles | [README](../integration/lean-zip/README.md), [raw generator and assertions](../integration/lean-zip/package-raw.mjs) |
| Verso Flat formatting | Real `formatRenderedForRuntime`; Flat text/events, separate from PrettyTrace; unpublished-source builds remain provisional | [README and source gate](../integration/verso-flat/README.md), [source pin](../integration/verso-flat/verso-source.json) |
| Verso complete HTML | Real formatting entry; escaped HTML and tag events, a distinct output oracle | [README](../integration/verso-html/README.md) |
| Illuminate SpatialHitScene | Prepared spatial query, separate from linear HitScene | [README and gate](../integration/illuminate-spatial-hit-scene/README.md) |
| VBP manifest resolver | Local retained-session manifest/path boundary | [README](../integration/vbp-manifest-resolver/README.md) |
| VBP older Verso viewer | Historical mount/unmount and retained-callback regression boundary; not current-code parity or the options factory | [README](../integration/vbp-verso-viewer/README.md) |

## Branch-only packages and experiments

These are not interchangeable with a main-based package recipe:

- VBP current Document renderer and options component live on the official
  4.34 W7 child. The none-factory prototype `5fefee0c` and portable package
  `c560f6a4` have matched frozen SSR/Chromium consumer qualification, not live
  adoption or full 4.34 migration. Read the local object with
  `git show c560f6a4:integration/vbp-native-session-probe/COMPONENT_PACKAGE_20260916.md`;
  the same directory at that commit contains
  `OPTIONS_PATH_CAPTURE_20260916.md`. Neither recipe is on main or claimed
  remotely published by this index.
- Verso search remains branch-only. The client experiment uses scalar priority
  factors from FIR branch `perf/verso-search-qsort` at
  `~/lean/verso/.worktrees/fir-verso-search-qsort`. Earlier full-ranker, bulk
  and packed branches are distinct historical experiments, not interchangeable
  APIs. Resolve the consumer's package and source policy before use; none is a
  main recipe or a new main canonical pointer.

## Compiler and runtime fixture catalogs

| Purpose | Registry | Gate |
| --- | --- | --- |
| Lean compile/proof examples | the `examples` target in `Makefile` | `make examples` |
| Source-compiled semantic cases | `Fir.Validation.Corpus.cases` | `make validate` and the coverage index |
| Handwritten final-LCNF machine cases | `Fir.Validation.DirectLcnf.cases` | `make validate-direct-lcnf` |
| Native/LCNF/V8 triangle | `validation-plans/native-lcnf-v8-scalars.json` | `make validate-v8` |
| Small symbolic Wasm modules | `Fir.Wasm.Emit.Examples.initialFixtures` | `fir-wasm-artifact all` inside the artifact gate |
| Resident-runtime modules | the commands in `FirWasmArtifactMain.lean` | standalone Node checks inside the artifact gate |
| Compiler-produced concrete source probes | `CONCRETE_SOURCE_PROBES` in `concrete-corpus.mjs` | `check-concrete-source-probes.mjs` inside the artifact gate |

Cases carry their own schemas, tags, required LCNF forms and externals, and
provenance. Plans select backends and explicit admission fences. The coverage
index ratchets the aggregate, while the artifact gate emits twice, compares
bytes, and runs the registered products in real engines. Do not copy those
inventories into this page.

## Lifecycle

Add a package here only after its immutable acceptance artifact passes. Keep
an older package when it remains a distinct semantic oracle, deployment path,
or regression boundary. Remove it when no consumer or unique gate remains;
dated plans and bug cards remain historical evidence rather than active build
entries.

The old PrettyTrace/full-action/linear-HitScene and older VBP outputs have
distinct gates or consumers; do not remove them simply because a newer
representation exists. Superseded pending-publication text has been removed
from this index. No package or staging directory is designated disposable
here: resolve actual consumer staging scripts and pins first, then send any
uncertain removal proposal to the integration owner.
