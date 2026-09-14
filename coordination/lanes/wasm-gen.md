# wasm-gen lane

Current slice: `ROOT-W7-20260915-003`, executable partial-body source discovery.
Root owns integration; W6 remains parked. Existing packages are untouched.

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: dca28207c5fa996e68c1ba5b7fe01fd810537b5e
functional-head: 9154f1c7efa0c4518bc6f0ea91c7d2ac7fa69337
contract-base: dc94cd4f0aa716aad5e79a7f77bafa752e9994a9
clean-at-update: true
slice: Reuse upstream getDeclInfo? for runtime source dependency traversal. Missing ListItem.toJson caller is now discovered, but actual capture still fails on the same generated helper while rebuilding the expanded unit.
files: Fir/Wasm/Emit/Source.lean; integration/vbp-native-session-probe/{prepare.mjs,Provenance.lean,PartialBody.lean,PROVENANCE_RESULT.md,README.md}; bugs/FIR-BUG-wasm-none-source-discovery-logical-partial-body.md; coordination/lanes/wasm-gen.md
contracts: none changed; source-unit/deferred routing and fir.wasm-host-binding/render-core/v0 unchanged
checks: Source Beam on 4.33/4.34 zero blocking diagnostics/saveReady; diagnostic Beam/batch pass; no Beam save as batch evidence. Imported partial-body regression rejects old implementation and passes candidate in direct 4.34 Lean. Ordinary Probe build 677 jobs. Actual capture exits 1 at the SAME helper diagnostic, now with correct caller among 90 rebuild roots. make check passes 730 cases/2172 comparisons. make talos-check passes after existing setup, 3205 jobs and trust audits. artifact/check.sh exit 0 including deterministic generation/Node differentials; browser/exhaustive not selected. Final SourceExamples build 66 jobs; 230 bug cards, prepare, syntax, diff and mailbox checks pass.
bug-cards: FIR-BUG-wasm-none-source-discovery-logical-partial-body
blockers: Discovery omission repaired, not full capture. Unknown Array.mapMUnsafe specialization remains despite including its exact caller/callee. Compiler-rebuild/cache cause remains unclassified.
handoff: Clean local-only partial repair and diagnostic checkpoint for root review on ROOT-W7-20260915-003. Canonical completion pins containing status commit. No main/push/package/pointer change.
next: Stop for root review. Trace the same failure inside the now-correctly discovered 90-root compiler rebuild; do not repeat name-provenance discovery or claim a new diagnostic. No named seed, manual companion or consumer/runtime change. ABI/projection/join diagnostics remain separate.
```

## Evidence

The generated helper is an extra declaration in Verso.Doc with native IR and
an impure signature, not a kernel constant. Structural provenance already
resolves the correct caller/callee before and after pre-final capture.
The caller was missing because source discovery read the logical default body
of imported partial Block.toJson. Upstream getDeclInfo? selects its executable
unsafe-rec body. Real-renderer A/B traversal: 695 -> 944 source names; caller
recovered. Production change: one expression and a comment in Source.lean.

The actual ordinary renderer retry STILL fails at:

```text
Unknown constant `_private.Init.Data.Array.Basic.0.Array.mapMUnsafe.map._at_._private.Verso.Doc.0.Verso.Doc.ListItem.toJson.spec_0`
```

Capture log SHA256:
`c9be278f8582130d89c324e034c97920f17d19ecf6e40d428f10ae180334cd71`.
No complete declaration/external/host inventory, lower/link/encoding, browser
execution or performance result is claimed. No successor compiler repair is
included. Root list grows from 78 to 90 and includes ListItem.toJson; the
remaining failure is within rebuilding this unit, not that caller's discovery.

See `integration/vbp-native-session-probe/PROVENANCE_RESULT.md` for commands,
frozen source identities and the additional checked Source.lean overlay.
Earlier metadata/capture/control reports remain historical evidence. Production
FIR stays on Lean 4.33; the consumer/source-view probe stays exactly 4.34.0-rc2.
