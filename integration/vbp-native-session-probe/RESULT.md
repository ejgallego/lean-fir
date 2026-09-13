# Renderer-core probe: stopped before FIR capture

Date: 2026-09-13. Request: `ROOT-W7-20260913-001`, parent
`VBP-FIR-20260913-003`. This is a negative feasibility checkpoint, not a
generation-ready package or a claim that the renderer cannot be compiled.

Root superseded NativeSession with the real
`VersoBlueprint.Experimental.VirPreview.Renderer.render` in
`ROOT-W7-20260913-002`, then landed the render-core v0 contract in
`ROOT-W7-20260913-003`. W7 observed these updates before capture, rebased to
`dc94cd4f0aa716aad5e79a7f77bafa752e9994a9`, and retargeted the fixture to that
single root. The original initial dependency run below selected NativeSession;
it never reached capture. Its first blocker is also a direct prerequisite of
the revised renderer via `Renderer -> Informal.ExternalMarkupView ->
VersoBlueprint.Html`. No second broad build was started.

## Exact inputs

- FIR compiler archive: `fdef2c1e44355367d449f26ecd87c0fd55a4319b`.
- Accepted contract base: `dc94cd4f0aa716aad5e79a7f77bafa752e9994a9`;
  only documentation/board changes relative to the compiler archive. Profile:
  `fir.wasm-host-binding/render-core/v0`.
- Lean: `leanprover/lean4:v4.34.0-rc2`, compiler commit
  `6a10ac8c22beadecabdbb0919c2b50214762f91d`, Linux x86-64 Release.
- VBP: `c4430bfe2c898c0312903ae46c45b410d253ebf4`, **dirty** only in the
  supplied production RPC file. The copied delta's SHA-256 is
  `b11a19b76283fec7137c2ea623b94b178dbae29095ec41a775c2045781d30ea6`.
- VIR: `9fafe9cfd594213ee39dc8205b08084c31101816`.
- Verso: `52c8c9557bcb5cc8c0edc0ee37e74311a3d53ee9`.
- NativeSession source SHA-256:
  `8f9f6bf2868dfca88cb30187b8e3381a26aa9fab18ec404f4d5424b8dd11cb5c`.
- Revised renderer source SHA-256:
  `f71035bbed37d779db8efdd77c4a4f471512efd2f01daa5008ff682e43230926`.
- Consumer manifest SHA-256:
  `626524417c41b30200ff0c32ee5b19796996e98d0c7a823062903640f0667eca`.

The fixture manifest preserves the consumer's remaining dependency revisions
as isolated path archives. `.deps/native-session-probe/SOURCE.json` records
all ten archive identities/hashes and the local fixture head/dirty state.
No consumer `.lake`, matched VIR report, or ordinary FIR 4.33 artifact is used
as a build input.

## First concrete blocker

The dependency build reaches Lean's **`leanir` stage**, before `Probe.capture`
or either FIR lowering/linking phase can run:

```text
Building VersoBlueprint.Html
.../VersoBlueprint/Html.ir:0:0: error: Failed to compile `VersoBlueprint.Html.escapeText`
  Unknown constant `String.Slice.posGE._redArg`
error: external command '.../v4.34.0-rc2/bin/leanir' exited with code 1
```

The source is the real three-step `String.replace` HTML escaping definition.
The fixture's generated setup has `experimental.module=true` and
`compiler.postponeCompile=true`. This does not yet distinguish a fixture
postponement/source-unit interaction from an upstream compiler issue. No
comparison build with alternate options was performed.

The initial build also reported missing generated companions in already
scheduled modules (`Lean.Name.toStringWithToken._at_.Lean.Name.toString.spec_0`
and `Option.instDecidableEq._redArg`). The build was interrupted once the
first blocker was inspected; no attempt was made to repair these errors.

FIR's `Fir.Wasm.Emit.ResidentLinker` dependency did build successfully under
the exact 4.34 toolchain, with dependency deprecation/linter warnings. This is
only an import-cone compatibility result, not successful source capture.

## Commands and evidence

From the W7 worktree, prepare the source archives with:

```sh
node integration/vbp-native-session-probe/prepare.mjs
export LAKE_CACHE_DIR="$(bash scripts/fir-lake-cache-path.sh)" LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true
export LAKE_CACHE_DIR="$(dirname "$LAKE_CACHE_DIR")/leanprover--lean4---v4.34.0-rc2"
export TMPDIR="$PWD/.deps/native-session-probe/tmp"
```

The original run used `build NativeSessionTestSource Fir.Wasm.Emit.ResidentLinker`.
That broader test-library target was removed when root revised the entry;
it is historical command evidence, not the current reproduction command.
The focused reproduction below exits 1 with the identical first diagnostic:

```sh
lake +leanprover/lean4:v4.34.0-rc2 -d integration/vbp-native-session-probe --keep-toolchain build VersoBlueprint.Html
```

Local working logs: `.deps/native-session-probe/build.log` and
`first-blocker.log`. The latter SHA-256 is
`1d3c321843e07f1d59385b550736a39bf927db4344e916f092dafca5275dcf3e`.
After the renderer-only retarget and contract rebase, the same focused command
again exits 1: `renderer-prerequisite.log`, SHA-256
`875978a0207b29fe50168b9776d67868a2836a5d6df88b6cda92f65d4503d9f6`.
These are reproducible diagnostic scratch, not a permanent approval registry.

`node --check` for both scripts, `bash -n check.sh`, and `git diff --check`
pass. The normal broad `make check`, Talos and historical artifact campaigns
were not run: root explicitly requested stopping at the first bounded
toolchain/capture/link blocker. No existing compiler/runtime/proof file changed.

## Unreached acceptance and smallest follow-up

No NativeSession final-LCNF closure, Wasm, export inventory, or import/signature
inventory was produced. `Probe.lean` and `Emit.lean` record the intended
capture/link command but are **not yet Lean-validated**, because their source
dependency build failed first. In particular, no historical 41/46-import
frontier, placeholder output, or interpreted fallback is reported as success.

Likewise no renderer closure, host-profile inventory or profile verdict is
available. The requested conditional token/dispatcher conformance work was not
started. The structural-validator scaffold fails closed pending that work;
unknown representations or retained callbacks must not be silently accepted.

A read-only Beam update/sync of the exact archived `VersoBlueprint.Html`
source passed with zero diagnostics and saveReady=true. No source was changed
or saved through Beam; its session was stopped. This separates successful
frontend elaboration from the reproducible later `leanir` failure. The drafted
capture drivers remain unvalidated because their dependency cone is blocked.

The smallest follow-up is a fixture-only investigation of the module
postponement boundary: determine whether ordinary imported VBP modules must
keep their native compilation setup while only the requested entry unit is
deferred, or whether FIR should consume its prebuilt-source capture provider
for this exact source. Preserve source-unit identity and use Lean's existing
capture APIs; do not introduce generated-name shims or change the renderer.
This is a proposed next slice, not an implemented workaround.

No semantic discrepancy was established and no workaround was added, so no
new semantic bug card was opened. Consumer sources, W6, main, historical
packages, public pointers and remote branches remain unchanged by W7.
