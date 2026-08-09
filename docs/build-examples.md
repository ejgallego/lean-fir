# Build examples

This page is a navigation index, not another manifest. The linked Lean and
JavaScript registries remain the sources of truth for exact inventories, and
their acceptance checks reject drift.

## Consumer packages

| Package | Status | Lean entry | Build and acceptance gate | Canonical pointer |
| --- | --- | --- | --- | --- |
| [FIR-native styled `prettyM`](../integration/talos/artifact/prettyM-package/README.md) | accepted W7 package | `Fir.Wasm.Emit.SourceFixture.prettyFormatTraceRaw` | `bash integration/talos/artifact/check.sh` | `integration/talos/artifact/_build/prettyM-current` |
| [Illuminate full-action player](../integration/illuminate-player/README.md) | accepted; retained as the full-action oracle | `Illuminate.AnimationPlayer.initialLive`, `transitionLive` | `ILLUMINATE_ROOT=/clean/pinned/illuminate bash integration/illuminate-player/check.sh` | `integration/illuminate-player/_build/illuminate-player-current` |
| [Illuminate selection player](../integration/illuminate-player/README.md#selection-only-v4-package) | accepted; preferred compact player | `Illuminate.AnimationPlayer.initialSelectionLive`, `transitionSelectionLive`, and the bit-exact tick facade | same Illuminate gate | `integration/illuminate-player/_build/illuminate-selection-player-current` |
| [C/Emscripten styled `prettyM`](../integration/lcnf-c-wasm/prettyM-emscripten-package/README.md) | accepted alternative backend | `Fir.LCNFC.PrettyM.renderWire` | `bash integration/lcnf-c-wasm/package-prettyM-emscripten.sh` | `integration/lcnf-c-wasm/_build/prettyM-emscripten-current` |

An accepted package has a real source entry, immutable publication,
`BUILD.json`, complete checksums, a packaged smoke test, an explicit ABI and
ownership contract, and a deterministic acceptance gate. Generated `_build`
pointers are conveniences; their package metadata is authoritative.

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

## Queued experiments

These are not accepted catalog entries and must not be presented through a
canonical package pointer:

- Verso Flat has strong disposable native, Node, and browser evidence, but
  publication waits for the recorded generic join/box admission fixes and a
  clean, accepted Verso source revision.
- Illuminate's timing-free selection dispatch is an adapter experiment over
  the accepted v4 semantics; it remains distinct from the diagnostic API until
  its interleaved benchmark and consumer gate pass.
- Illuminate prepared hit-scene queries target the real
  `Illuminate.HitScene.query : HitScene → Float → Float → HitSceneResult`.
  The first gate is compiling the exact clean source through FIR's Lean 4.32
  source view; the requesting checkout currently uses Lean 4.33. Its clean,
  remotely published source candidate is Illuminate commit `af088e313eaa`.
  The package remains queued until the compatibility result is known. It must
  retain a scene below a checkpoint, transport bit-exact coordinates, rewind
  query scratch, and internalize Float math rather than import JavaScript
  `Math` helpers.

## Lifecycle

Add a package here only after its immutable acceptance artifact passes. Keep
an older package when it remains a distinct semantic oracle, deployment path,
or regression boundary. Remove it when no consumer or unique gate remains;
dated plans and bug cards remain historical evidence rather than active build
entries.
