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
| [FIR-native styled `prettyM`](../integration/talos/artifact/prettyM-package/README.md) | `Fir.Wasm.Emit.SourceFixture.prettyFormatTraceRaw` | FIR main; Lean 4.34.1; current FIR source, no external source snapshot | `bash integration/talos/artifact/check.sh` |
| [C/Emscripten styled `prettyM`](../integration/lcnf-c-wasm/prettyM-emscripten-package/README.md) | `Fir.LCNFC.PrettyM.renderWire` | FIR main; Lean 4.34.1; exact Lean runtime and Emscripten inputs recorded by the package | `bash integration/lcnf-c-wasm/package-prettyM-emscripten.sh` (current FIR-native comparator, differential, immutable package and smoke) |

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

## Recipes being migrated

An integration directory is not a current recipe merely because a README,
source pin, old artifact or package pointer exists. Keep its recipe and migrate
it to current FIR, current Lean, and an exact owner-nominated source revision;
then add it above when its current-tree gate passes. Do not leave it in a
permanent historical or provisional category. Remove only inputs confirmed to
have no current owner-supported replacement, after checking consumers and
reviewing the exact removal with root. Git history retains prior versions.

## Building a package

Start from the current recipe table and run its acceptance command from the
FIR root. `make build` compiles the FIR library; it does not select a source
entry, assemble a consumer adapter or publish a package. The recipe gate owns
those operations and checks the resulting interface and semantic endpoint.

For either current prettyM recipe:

```sh
bash integration/talos/artifact/check.sh
# Or the independent C/Emscripten package and differential gate:
bash integration/lcnf-c-wasm/package-prettyM-emscripten.sh
```

Use the package-local BUILD.json, policy and complete SHA256SUMS inventory
to identify the immutable result. A `*-current` pointer is a convenient way
to find it; pass the resolved package to a consumer's verifier/staging command.
Record the source/adapter/ownership identities when comparing results. Do not
substitute a different ABI simply because both files end in `.wasm`.

An external-source recipe must state its source revision/hashes, module and
entry names, original Lake setup and supplied dependencies. The existing
`scripts/fir-source-prepare` command prepares private module setups; its
[input contract](package-build-client-map.md#supported-private-source-preparation)
explains exact compiler/dependency inputs. This preparation does not validate
the selected declaration or emit/link a package: the recipe's compiler and
acceptance gate must do that. Use the source project's real definitions.

Compilation, source preparation, linking, publication and application calls
have different timing boundaries. Use the [performance workflow](tooling/BENCHMARKING.md#measurement-workflow)
when evaluating them. Keep precise gates in the recipe and package metadata;
this index only provides navigation.

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
