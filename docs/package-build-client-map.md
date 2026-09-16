# Package, build, and client configuration map

Inspection snapshot: 2026-09-16, FIR `main` at `b589ac98`, with the official
4.34 generation worktree inspected separately. VIR and client worktrees were
read without modification. This document consolidates navigation and analysis;
it is not a new package manifest, consumer registry, or acceptance record.

## Summary

There are three distinct owners of information:

- **Source projects** own Lean source, Lake configuration, workload semantics,
  native oracles, and application UI.
- **FIR/VIR producers** own compiler invocation, runtime implementation,
  executable package metadata, adapters, and their ABI/lifetime checks.
- **Consumer campaigns** own exact package pins, staging, common controls,
  browser acceptance, and measurements.

Much of this division is already implemented. The fragmentation is chiefly in
navigation, inconsistent preparation paths, and multiple generations of local
client/staging code. We should connect existing contracts rather than create
another framework beside them.

## Where each kind of information lives

Paths prefixed `VIR:` are relative to the VIR repository. Client-relative paths
are identified in the inventory below; they may exist only at a pinned revision
or in a dedicated worktree, not in the client's current main checkout.

| Information | Authoritative location | Meaning |
| --- | --- | --- |
| Lean version and dependencies | Client `lean-toolchain`, `lakefile.lean`/`.toml`, `lake-manifest.json` | Source project's upstream build definition, options and dependency resolution |
| FIR source selection/provenance | Integration `*-source.json`, `source-contract.json`, or `raw-source-contract.json` | Exact source revisions and, where declared, relevant source hashes |
| Module compiler inputs | Lake-generated `ModuleSetup` and actual resolved artifacts/plugins | Derived inputs; not interchangeable with an old setup pointing into another checkout |
| FIR output inventory | Generated `.wasm.json`, package `BUILD.json`, `SHA256SUMS`, package policy | Physical Wasm interface, logical adapter contract, provenance and payload integrity |
| FIR publication/installation | [Shared package tools](../integration/package-tools/README.md) | Immutable publication and policy-backed verification/installation |
| FIR build navigation | [Build examples](build-examples.md), integration READMEs | Entry points and gates; the index is not exhaustive |
| VIR selected entries | `VIR: examples/*.virpkg.json`, `@[vir_export]`, `@[vir_startup]` | Package roots and startup selection, not a complete source-input capsule |
| VIR module/SDK generation | `VIR: lakefile.lean`, `Vir/`, `scripts/packages/`, `docs/guides/PACKAGES.md` | `+Module:vir` module products, `:virSdk`, package exports and version checks |
| VIR logical interface/runtime | `VIR: web/src/`, `.irpkg`, `.irpkg-set.json`, SDK manifests | IR package interface, ordered module products, matching interpreter/SDK and host ABI |
| Generic JS host bindings | `VIR: Vir/*.bindings.json`, `Vir/bindings.schema.json`, `web/src/vir-host-bindings.js`, `web/src/vir-react-host-bindings.js` | Binding declarations, generated Lean surface and actual native JS providers |
| Browser campaign pins/build recipes | `VIR: benchmarks/browser/artifact-builds.json` | Exact producer/workload revisions, invocation and declared staged files |
| Browser workload/controller selection | `VIR: benchmarks/browser/examples/*/example.json`, `tests.json`, controllers | Required backends, inputs, result normalization, studies and disposal |
| Local invocation/output paths | Client staging scripts, ignored local toolchain config, `_build/*-current` | Convenience locations; neither latest paths nor directory names establish source identity |
| Current cross-project disposition | [Coordination board](../coordination/BOARD.md), lane handoffs, mailbox events | Ownership, immutable candidate checkpoints and outstanding scope |

The command/configuration layer is similarly split:

| Scope | Entry points | Generated state |
| --- | --- | --- |
| FIR repository | Root `Makefile`, `scripts/`, `.github/workflows/`; `make check`, `make talos-check`, artifact `check.sh` | Worktree-local `.lake`, `.beam`, `.deps`; shared content-addressed Lake cache only |
| VIR compiler/runtime | Root `package.json`, `scripts/`, Lake facets, `.github/workflows/`; documented in `docs/HARNESS.md` | `build/`, SDK/browser output, downloaded Lean/WASI tools and IR packages |
| Browser catalog | `VIR: benchmarks/browser/package.json`, scripts and artifact-build configuration | Staged artifact sets, source views and per-run integrity locks |
| Application client | Its own Lake/npm scripts, package exporters and staging/test commands | Application bundles, native fixtures, local demo output and campaign reports |

These commands perform different jobs. Their existing wrappers should offer
concise progress and preserve full failure logs, but a single global build
command would not resolve source identity or ABI differences.

One verified correctness issue needs attention before relying on quiet command
exit status: `scripts/quiet-run.sh` reads `$?` after the completed `if` statement,
not in its failed-command branch. `bash scripts/quiet-run.sh
config-audit-negative -- false` prints `FAIL` but exits **0**. Capture the actual
command status in the failure branch and add a negative regression. This audit
records the defect; it does not change the wrapper.

`browser-benchmarks/source-package/v1` already exists in FIR's
[source-package discovery contract](../integration/package-tools/SOURCE_PACKAGE.md).
It describes an **output package** and its producer operations. In the shared
utility it is currently an in-memory, verifier-derived discovery view, not a
universally published sibling file. It must not be confused with a frozen
**input source snapshot** or expanded to own application workloads.

## Known FIR workload families and clients

This inventory includes implemented integrations and explicitly identified
branch-only work. Presence here does not upgrade an experiment to accepted.
The linked recipe/policy and its exact checkpoint remain authoritative.

| Family / variants | FIR recipe and Lean entry | Client/bootstrap information |
| --- | --- | --- |
| Styled prettyM, FIR-native | [Artifact package](../integration/talos/artifact/prettyM-package/README.md); `package-pretty-format.sh`; `Fir.Wasm.Emit.SourceFixture.prettyFormatTraceRaw` | Versioned compact Format adapter; VIR browser `examples/prettyM` and `backends/pretty-native.js` own loading, normalization and comparison |
| Styled prettyM, C/Emscripten | [Alternative package](../integration/lcnf-c-wasm/prettyM-emscripten-package/README.md); `package-prettyM-emscripten.sh`; `Fir.LCNFC.PrettyM.renderWire` | Separate generated JS/Wasm loader and full Lean runtime; same campaign workload, not the native FIR ABI |
| lean-zip stored, level1, raw | [Integration](../integration/lean-zip/README.md); `package.mjs`, `package-raw.mjs`, `export-raw-package.mjs`; `Zip.Wasm.compressStored`, `compressLevel1`, `compressRaw` | Client `bench/catalog`, `bench/web`, `bench/fir-native`, `bench/fir-c`; shared ByteArray adapter; VIR catalog owns common campaign pins |
| Illuminate full-action / selection player | [Player integration](../integration/illuminate-player/README.md); `package.mjs`, `selection-package.mjs` and exporters; `Illuminate.AnimationPlayer.*Live` | Client frontend/staging and oracle export scripts; opaque per-player adapter state; VIR `examples/illuminate` stages the compact player campaign |
| Illuminate prepared HitScene / spatial HitScene | [HitScene](../integration/illuminate-hit-scene/README.md), [spatial](../integration/illuminate-spatial-hit-scene/README.md); respective `package.mjs`; `Illuminate.HitScene.query`, spatial `ofHitScene`/`queryBorrowed` | Client `scripts/stage-fir-*` and package tests in the hit-scene worktree; persistent prepared scene, borrowed queries and copied results |
| VersoSlides Flat / HTML formatting | [Flat](../integration/verso-flat/README.md), [HTML](../integration/verso-html/README.md); `package.mjs`; `VersoSlides.Pretty.formatRenderedForRuntime` / `formatHtmlForRuntime` | Integration adapters/smokes and VersoSlides source contract; these are formatting workloads, not VBP's React renderer |
| Verso search ranking, branch-only | `integration/verso-search` on FIR branch `feat/verso-search-lane`; `Verso.Search.ExperimentalVIR.rankCandidates` | Structured ranking adapter and JS/native oracle checks; not present on FIR main at this inspection |
| VBP manifest resolver | [Resolver integration](../integration/vbp-manifest-resolver/README.md); `VersoBlueprint.Runtime.ManifestResolver.resolveBatchJson` | String-in/String-out invocation adapter; zero React/RPC closure, separate from the viewer |
| VBP older full viewer/widget | [Viewer integration](../integration/vbp-verso-viewer/README.md); `Widget.mount` / `unmount` | Older pinned source, 41 host operations and component/hook lifecycle; `.open({hostBindings})`, `.invoke(...)`, `.dispose()` |
| VBP current Document JSON renderer | Official 4.34 generation branch, `integration/vbp-native-session-probe/CURRENT_HOST.md`; compiled `Document.decode` → `Renderer.render` | `createCurrentRendererHostPrototype({module, manifest, bindings})`; `session.renderDocumentJson(encodedDocument)`; VBP `tests/vir_preview/*` assembles React/provider/SDK bootstrap |
| VBP encoded-document options factory, in progress | Same generation owner; requested `createEncodedDocumentComponent(mathComponent?)` | Frozen private setup/capture/lower/link now pass for `none`; component execution awaits generic function/callback SDK and explicit invocation roots. This is not yet the current renderer API |

Additional C/LLVM experiments exist, notably
[Illuminate's alternative player](../integration/illuminate-player-llvm/README.md).
They are backend variants, not necessarily new client projects. Counting every
fixture, package variant and benchmark directory as a distinct consumer would
overstate the number of applications.

One useful distinction: `Illuminate.Animation.FirLive` is the **source module**,
while `Illuminate.AnimationPlayer` is the **declaration namespace** used by the
actual exports. A module path and an exported function name need not match.

## What VIR contributes

VIR already has a reusable client SDK: `web/src/vir-runtime.js` exposes runtime
creation, calls, startup and disposal; ReactDOM-specific wiring is isolated in
`vir-react-host-bindings.js`. FIR instead packages application-compiled Wasm
and workload-specific adapters. They can share native provider definitions and
logical binding policy without pretending their physical runtimes are equal.

The VIR browser catalog already covers prettyM, lean-zip and Illuminate. Its
`artifact-builds.json` records frozen FIR producer revisions (`298682a7`,
`b9f6adb4`, `1b1668f1` respectively at inspection), separate VIR revisions and
workload revisions. These are campaign inputs, not promises to follow latest
FIR main. Different pinned backends may intentionally use different toolchain
versions. The current VBP 4.34 renderer is a separate integration and is not
represented by those three catalog entries.

VIR's package exporter helpers and FIR's package tools provide existing seams
for sharing provenance checks, immutable staging and discovery. Client-side
codec/lifecycle code remains workload-specific: Format traces, ByteArrays,
player state, prepared scenes and retained React callbacks have different
ownership requirements.

## Current VBP boundary

The accepted current renderer checkpoint is `4776f86e`, built against VBP
`92db6325`, VIR `36d26bc2` and Lean 4.34 rc2. It has thirteen intentional typed
VIR imports. Consumer qualification covers matched React SSR/Chromium rich and
full-FLT documents, retained callbacks/DOM, malformed recovery, provider-error
identity and disposal. It does not establish timing results or completion of
the options factory. Older `a48bbb4a` output is deliberately preserved.
The official 4.34 child also retains four known repository audit findings;
consumer qualification is not a claim that the full 4.34 repository gate is green.

The factory follow-up has a complete frozen source closure (`2c1ef0f6`, archive
`41b88ae7`) and external setup/toolchain authority (`6bbd2b32`). The first
private preparation attempt was correctly rejected: Lake rematerialized a Git
dependency and changed an authorized source file. The successor at clean
`f055e0ff` passes with official Lake `--packages` overrides and an active mutation
guard, preserving every source byte. Real `createEncodedDocumentComponent none`
captures/assembles/lowers/links; root independently verified all 404 indexed
payloads and the actual Wasm interface.

The 64,858-byte linked factory has one import, generic `Js.Function.ofLean`,
but no callback invocation export. Its captured source frontier has 31 host
rows (19 added, one removed, 12 unchanged against the accepted renderer).
Factory-only dead-code elimination does not qualify callback execution.
`ROOT-W7-20260916-017` continues through the generic typed SDK and explicit
callback roots to actual `none` component execution. Full consumer parity,
optional math and the working renderer pins remain separate.

Source/build/acceptance reports currently live in W7's ignored `.deps` and VBP's
`.worktrees/_meta`, including `VBP-FIR-CURRENT-ACCEPTANCE-20260916-001.md`.
These are local working evidence; GitHub CI is the durable validation run
record. Any distributable package must carry its own necessary metadata rather
than depend on those local paths.

## Local checkout traps

| Logical owner | Useful local view | Caveat |
| --- | --- | --- |
| VIR runtime/catalog | `~/lean/vir`; `.worktrees/lean-4.34-support` for 4.34 | Root checkout has local edits and is not the pinned campaign producer |
| Current FIR renderer | FIR `.worktrees/wasm-generation-4.34`, branch `wasm/generation-4.34` | Use official toolchain branch; do not rebuild from an unrelated historical fixture setup |
| lean-zip client | `~/lean/lean-zip/.worktrees/vir-fir-wasm-port`; catalog source view under VIR | Root's module-system branch differs from the frozen browser workload |
| Illuminate client | `~/lean/illuminate/.worktrees/vir-hit-scene`, other campaign worktrees | Root main does not contain all frontend/staging code |
| VBP client | `~/lean/verso-blueprint/.worktrees/browser-pr188` | Current dirty source is captured by the authorized frozen snapshot; capture must use private extracted sources |
| Verso search producer | `~/lean/verso/.worktrees/fir-verso-search` | Despite the parent directory, Git identifies this as a FIR worktree |

Always resolve repository/worktree identity and exact revision before treating
a local path as an input. Directory labels alone are insufficient.

## Consolidation: the smallest useful next steps

1. Fix and negatively test quiet-wrapper failure propagation. Concise output
   must preserve the original exit status, not merely print a failure label.
2. Keep [build-examples.md](build-examples.md) as FIR's package navigation index
   and the VIR catalog as the existing browser campaign manifest. Expand the
   index from reviewed package policies, without duplicating their inventories
   or claiming all recipe directories are accepted.
3. Standardize **source preparation**, not every application: exact Lean
   identity, source closure with original Lake configuration, explicit entry
   points and a path-only map to supplied dependencies. Generate setup and
   build products privately; reject unauthorized source rematerialization.
   The current W7 override gate is the concrete experiment for this boundary.
4. Reuse shared publication/verifier/export utilities. Make adapter API,
   logical types, required host providers and ownership visible in existing
   package metadata. Do not invent a second metadata file with the same facts.
5. Ship a truthful package-local bootstrap: load verified payload, instantiate
   with checked providers, expose the actual typed API, and dispose. Keep
   React controls, workload oracles and application transport in clients.
   There is no universal FIR `.component(...)` API today.
6. Retire superseded local staging/documentation only after identifying its
   remaining consumer. Keep distinct backends and semantic oracles; remove
   historical validation trees rather than create a permanent approval registry.

The resulting division is simple: **source projects define what to build;
producers define the executable and safe calls; clients define how to use it.**
