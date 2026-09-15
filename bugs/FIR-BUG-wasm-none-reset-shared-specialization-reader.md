---
id: FIR-BUG-wasm-none-reset-shared-specialization-reader
status: confirmed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.34.0-rc2
lean-revision: 6a10ac8c22beadecabdbb0919c2b50214762f91d
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-09-15
reproduction: integration/vbp-native-session-probe/ResetSharing.lean
regression: integration/vbp-native-session-probe/module-capture-check.sh
---

# Summary

Root-local compiler mapping reset can invalidate a shared specialization while
leaving another imported compiler body that calls it visible.

## Minimal reproduction

The pinned renderer imports Verso.Doc. Both ListItem.toJson and DescItem.toJson
have saved base bodies calling a specialization named under ListItem.toJson.
Resetting the owner hides the helper's module mapping and saved base body;
the DescItem reader and its call remain visible. The helper has no kernel body.
ResetSharing checks this metadata defect without compiling a synthetic unit.

## Exact commands

Prepare the isolated source view and cache/TMPDIR as documented in the fixture:

```sh
cd integration/vbp-native-session-probe
lake --keep-toolchain -KpostponeCompile=false env lean ResetSharing.lean
FIR_RENDERER_BOUNDARY=1 lake --keep-toolchain -KpostponeCompile=false env lean -DmaxHeartbeats=0 Boundary.lean
```

## Expected semantics

Every visible imported compiler body retains resolvable dependencies, or is
invalidated/recompiled coherently with those dependencies. Generated-name owner
provenance alone is not the complete set of readers of a specialization.

## Actual behavior

forgetGeneratedCompilerModuleMappings erases names by selected source ownership.
It does not account for retained imported base/mono bodies that share those names.
Fresh specialization generation does not repair references in such saved bodies.

## Proof or differential evidence

Read-only Beam probes identify the imported base/mono reader edges and confirm
the helper-present to helper-absent transition with the dependent reader retained.
The actual 90-root renderer rebuild includes ListItem but not DescItem. Its
compiler trace generates a new specialization with suffix spec_120 while failure
still names the imported spec_0. Boundary.lean locates failure at the mandatory
checkpoint immediately after base/saveBase (392 declarations), before the next
pass begins. It is not an exception from a wrapped pass body. The exact first
fresh declaration rejected by that check remains unreported; see REBUILD_BOUNDARY.

## Semantic impact

Capture failure before Wasm generation. No incorrect emitted execution claimed.

## Classification and triage

W7 imported compiler-context coherence. Follow actual dependency/module ownership;
do not patch specific generated names, inject precompiled closures, or seed the
renderer with manually selected source companions.

## Workaround

none

## Upstream tracking

none; comparing the owning-module pipeline remains part of the investigation.

## Resolution and regression

The legacy reset path remains open: ResetSharing is a positive diagnostic of
that defect, not a claim that mapping invalidation is repaired.

The opt-in production ModuleSource provider avoids the inconsistent context by
compiling the owning ordinary module through upstream header/command processing.
Its real Verso.Doc regression captures DescItem's final body and both calls to
the ListItem-owned shared helper together with that helper's body. The real
renderer entry also captures successfully. Repeat final-LCNF inventories/text
are identical; missing-entry and non-module setup controls reject. See
integration/vbp-native-session-probe/MODULE_RESULT.md. No generated-name seed,
reader invalidation workaround or weakened compiler checkpoint is used.
