# Executable partial-body source discovery

Date: 2026-09-15. Request: `ROOT-W7-20260915-003`. Base:
`dca28207c5fa996e68c1ba5b7fe01fd810537b5e`.

## Diagnosis

The missing `Array.mapMUnsafe` specialization is indexed in **Verso.Doc**, not
Init.Data.Array. Lean's structural specializer provenance already lets FIR
resolve its exact source caller `ListItem.toJson` and generic callee. Both source
definitions, the helper's native IR and impure signature survive the first two
capture stages unchanged. The helper is not a kernel constant and is neither
a declaration nor an external in the 1,895-declaration pre-final artifact.

The caller is absent from all existing discovery stages. The source dependency
walk reads logical bodies with `Environment.find?`. For imported partial
`Block.toJson`, that body contains an `Inhabited` default, not the executable
calls. Upstream `LCNF.toDecl` uses **`LCNF.getDeclInfo?`**, selecting its
`_unsafe_rec` body first. That body contains the missing `ListItem.toJson` edge.

Read-only actual-renderer A/B (same 42 bridged roots):

| Body selection | Discovered source names | ListItem.toJson discovered |
| --- | ---: | --- |
| Existing logical body | 695 | no |
| Upstream executable body | 944 | yes |

This is a discovery omission, not failed generated-name parsing or metadata
lost by the previous constructor reset. `Provenance.lean` invokes FIR's actual
private discovery routines via exact Lean private-name metadata and compares
body selection without adding compilation roots. It is diagnostic code, not
a new production reflection API.

## Repair

`sourceRuntimeValueClosure` now calls upstream `LCNF.getDeclInfo?` in place of
the logical-body lookup. The production delta is one expression plus its
comment. Existing compilability guards, source-unit grouping, bridge selection,
cache reset and deferred-module routing are unchanged. No manually selected
companion or generated helper is compiled by the fixture.

`PartialBody.lean` checks the actual discovery function against executable-only
dependencies of imported `Block.toJson`. It fails before repair (12 missing
dependencies, including ListItem.toJson) and passes afterward. The two earlier
probe scaffolds using a local partial definition and Lean.Json.render did not
distinguish the implementations; they are not negative regression evidence.

Bug card: `FIR-BUG-wasm-none-source-discovery-logical-partial-body`.

## Identity and reproduction

Lean 4.34.0-rc2/VBP/VIR/Verso/FIR archive identities and the dirty RPC overlay
remain pinned as in `REPAIR_RESULT.md`. Production FIR stays on Lean 4.33.
The preparer additionally overlays the one reviewed FIR Source.lean file,
SHA-256 `26667687f22cc9092b5194121ac9a8ab27b713bd196107ea2c78711a80e07486`.
No consumer source/archive or toolchain changes are included.

With the cache and persistent TMPDIR configured as in `REPAIR_RESULT.md`:

```sh
node integration/vbp-native-session-probe/prepare.mjs
cd integration/vbp-native-session-probe
lake --keep-toolchain -KpostponeCompile=false build Probe
lake --keep-toolchain -KpostponeCompile=false env lean PartialBody.lean
FIR_RENDERER_PROVENANCE=1 lake --keep-toolchain -KpostponeCompile=false env lean -DmaxHeartbeats=0 Provenance.lean
FIR_RENDERER_CAPTURE=1 lake --keep-toolchain -KpostponeCompile=false env lean -DmaxHeartbeats=0 Capture.lean
```

The pre-repair A/B JSON SHA-256 is
`e000f4cf69c190be2ee65d84abec045bbb1a91a945cb92726d5f3dcf61798da6`.
Rerunning provenance with the repair selects executable bodies in both walks.
Local logs under `.deps/native-session-probe/control/` are disposable evidence.

## Acceptance

The actual renderer retry still exits 1 with **the same generated helper
diagnostic**. Its reported rebuild roots grow from 78 to 90, now explicitly
including `_private.Verso.Doc.0.Verso.Doc.ListItem.toJson` and the generic callee.
Thus the discovery omission is repaired, but this is not sufficient to repair
capture. The remaining failure is in rebuilding the now-discovered unit; its
precise compiler/cache cause is not established. Do not claim that the previous
diagnostic has been cleared or that a new unrelated frontier was reached.

Capture log SHA-256:
`c9be278f8582130d89c324e034c97920f17d19ecf6e40d428f10ae180334cd71`.
No complete source/external/host inventory was returned. Stop for root review
of this independently regression-tested omission before further compiler edits.

Checks:

- Source Lean Beam on production 4.33 and isolated 4.34: zero blocking errors,
  saveReady; sessions stopped. No Beam save used as batch evidence.
- Provenance diagnostic Beam/direct Lean: pass, actual pre-final artifact.
- Imported-partial regression: old implementation rejects 12 executable-only
  dependencies; candidate direct 4.34 batch passes.
- Ordinary `lake build Probe`: pass, 677 jobs including reused jobs.
- `make check`: pass, 730 cases / 2,172 comparisons.
- `make talos-check`: pass after existing worktree setup, 3,205-job build and
  source/compiled trust audits; existing proof debt is unchanged.
- `bash integration/talos/artifact/check.sh`: pass, including deterministic
  source/prettyM generation and Node checks. Browser/exhaustive mode not selected.

Final focused build and hygiene are recorded in the lane handoff. No lowering,
linking, Wasm emission, host classification, package/pointer movement, runtime,
W6 proof change or performance claim is included.
