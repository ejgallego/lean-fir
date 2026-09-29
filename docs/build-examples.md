# Build examples

This page is a navigation index, not another manifest. The linked Lean and
JavaScript registries remain the sources of truth for exact inventories, and
their acceptance checks reject drift.

For the wider source/build/adapter/client relationship across FIR, VIR and
consumer repositories, see the [configuration map and analysis](package-build-client-map.md).
For a recipe to appear as current main navigation, its producer must build from
the current FIR tree and toolchain, with exact external source inputs, and its
named acceptance gate must pass. Historical package acceptance does not make
an old recipe current. Frozen client pins belong to their client campaigns and
do not qualify FIR main recipes. Unverified or incompatible recipes are omitted
until their owners repair them or retire the exact obsolete inputs after
checking actual consumers. Git history preserves old versions and fixtures.

## Current main package recipes

| Package | Lean entry | Current source and toolchain | Acceptance gate |
| --- | --- | --- | --- |
| [FIR-native styled `prettyM`](../integration/talos/artifact/prettyM-package/README.md) | `Fir.Wasm.Emit.SourceFixture.prettyFormatTraceRaw` | FIR main `a460d804`; Lean 4.34.1; current FIR source, no external source snapshot | `bash integration/talos/artifact/check.sh` |

An accepted package has a real source entry, immutable publication,
`BUILD.json`, complete checksums, a packaged smoke test, an explicit ABI and
ownership contract, and a deterministic gate that passes on the current tree.
Generated `_build` pointers are conveniences; their package metadata is
authoritative.

FIR CI keeps `make check` and Talos mandatory. Separate path-triggered jobs run
the W7 artifact gate for FIR/Wasm/artifact inputs and the C/Wasm gate for FIR
and C/Wasm inputs. Consumer-specific acceptance stays with the consumer
repository: its pinned recipe is requalified after producer-pin or recipe
changes, and its scheduled moving-client canary follows that repository's
source/CI policy. FIR does not fetch a floating client checkout from core CI;
no FIR-side moving-client canary is currently configured.
Only recipes with current-tree evidence are listed above; do not create a
second package registry to track stale or pending recipes.

## Other integration sources

Other integration directories are not current recipes merely because a
README, frozen source pin, historical artifact or package pointer exists. Add
one above only after the exact current-tree recipe and its consumer gate pass.
Otherwise, its owner should repair it or remove the obsolete recipe and
fixtures after confirming no live consumer depends on them. Do not keep a
second copy of old client inputs in place of Git history.

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

Keep a main recipe only while its producer and consumer gates remain
reproducible from the current tree and toolchain. Preserve historical
acceptance in Git history, not in fixtures that no longer build against
current FIR. Retire a recipe only after checking its actual consumer and
naming the exact obsolete files; preserve distinct current semantic oracles
and deployment paths when their gates still pass.
