# wasm-gen lane

Current slice: `ROOT-W7-20260915-002`, generic constructor metadata preservation.
Root owns integration; W6 remains parked. Existing packages are untouched.

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: 6c604d41f18b42db6e19059c8f4d954686b6cbe9
functional-head: d49b65c1005270c9e91f269a9e74d9e4437ee19b
contract-base: dc94cd4f0aa716aad5e79a7f77bafa752e9994a9
clean-at-update: true
slice: Preserve imported inductive/constructor module identity during fresh source reset; exact renderer capture passes Int metadata failure and stops at a new unknown generated specialization.
files: Fir/Wasm/Emit/CompilerPrivate.lean; integration/vbp-native-session-probe/{prepare.mjs,ConstructorMetadata.lean,REPAIR_RESULT.md,README.md}; bugs/FIR-BUG-wasm-none-source-reset-inductive-metadata.md; coordination/lanes/wasm-gen.md
contracts: none changed; source-unit/deferred routing and fir.wasm-host-binding/render-core/v0 unchanged
checks: Beam CompilerPrivate on 4.33/4.34 and regression on 4.34 zero blocking diagnostics/saveReady; no Beam save as batch evidence. Negative pre-fix regression rejects; positive direct 4.33/4.34 regression passes. Ordinary build Probe 677 jobs; exact actual capture reaches documented successor. make check passes 730 cases/2172 comparisons. make talos-setup and talos-check pass, 3205 jobs and trust audits. artifact/check.sh exit 0 including deterministic generation/Node differentials; browser/exhaustive not selected. Final SourceExamples build passes 66 jobs. prepare, syntax, 229 bug cards, diff and mailbox checks pass.
bug-cards: FIR-BUG-wasm-none-source-reset-inductive-metadata
blockers: Renderer capture still does not return a complete closure; unknown Array.mapMUnsafe specialization owned by Verso.Doc.ListItem.toJson is the new first diagnostic.
handoff: Clean local-only generation fix for root review on ROOT-W7-20260915-002; canonical completion pins containing status commit. No main/push or package/pointer change.
next: Stop for root review. Separate bounded generated-specialization provenance investigation; no named seeding, broader source-unit grouping or runtime/consumer changes. Return-node ABI and projection/join diagnostics remain separate.
```

## Evidence

Real renderer tracing confirms `Int.ofNat` imported before reset and local
afterward. The generic reset had hidden upstream's defining-module metadata.
`ConstantInfo` classification now preserves types and constructors, while
ordinary function/generated-helper reset retains its previous behavior.
The regression checks three inductives, six constructors and a negative
ordinary-function control. Temporary tracing is removed; `Source.lean` has no
delta. Production change is 10 added/2 removed lines in CompilerPrivate.

The actual ordinary renderer retry now fails at:

```text
Unknown constant `_private.Init.Data.Array.Basic.0.Array.mapMUnsafe.map._at_._private.Verso.Doc.0.Verso.Doc.ListItem.toJson.spec_0`
```

Capture log SHA256:
`2d38d0fa644b6258f5b16793ed0d1ec00ff74ffc18f94d80eda9b34fdfa0ce0b`.
No complete declaration/external/host inventory, lower/link/encoding, browser
execution or performance result is claimed. No successor compiler repair is
included. The new diagnostic's cause is not yet classified.

See `integration/vbp-native-session-probe/REPAIR_RESULT.md` for exact commands,
frozen source identities and the hash-checked one-file compiler overlay.
Earlier metadata/capture/control reports remain historical evidence. Production
FIR stays on Lean 4.33; the consumer/source-view probe stays exactly 4.34.0-rc2.
