# wasm-gen lane

Bounded capture: `ROOT-W7-20260914-001`, after accepted ordinary/postponed
control `ROOT-W7-20260913-004`. Root owns integration; W6 remains parked.
CG-05A/CG-05B/source equations and existing consumer packages are untouched.

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: waiting
base: 174d5aee1f4023e8251c98cd6e5502e90949641c
functional-head: 3a656559915326d17ff85b1330f4e29012b2741b
contract-base: dc94cd4f0aa716aad5e79a7f77bafa752e9994a9
clean-at-update: true
slice: Ordinary-source renderer capture executed; stopped at Int.ofNat inductive-metadata failure in existing final dependency rebuild.
files: integration/vbp-native-session-probe/{Capture.lean,CAPTURE_RESULT.md,README.md}; coordination/lanes/wasm-gen.md
contracts: none changed; fir.wasm-host-binding/render-core/v0 unchanged
checks: Ordinary lake build Probe passes (677 jobs including replays). Beam Capture.lean update/sync zero diagnostics and saveReady, session stopped. Exact FIR_RENDERER_CAPTURE=1 ordinary-mode batch invocation exits 1 at documented dependency-rebuild diagnostic. Renderer setup and frozen renderer/RPC hashes verified. Node/bash syntax, git diff --check and scripts/mailbox check pass. No lower/link/encoding or broad make/Talos/artifact/browser gates under root's explicit first-diagnostic scope.
bug-cards: none; no semantic discrepancy established and no workaround added
blockers: internalizeFinalDependencies reports Int.ofNat was not compiled; compileDecls must run on inductive types first. No complete closure returned, so final counts/LCNF hash/host inventory/profile verdict unavailable.
handoff: Clean local-only failed-capture evidence for root review on ROOT-W7-20260914-001, not generation-ready. No main advance, push, consumer edit, package or pointer change.
next: Root review; narrow fresh-environment inductive-metadata/source-unit investigation before any compiler fix. Return-node ABI census and deeper projection/join diagnostics remain separate.
```

## Result and boundary

The same exact Lean 4.34 source still builds in ordinary mode, as established
by the previous control. The capture-only driver now executes the existing
`NativeSessionProbe.capture`. Its first failure is in the third stage,
`internalizeFinalDependencies`, after individual-entry and boxed-adapter
processing. The diagnostic names 78 requested dependency roots, then reports
missing compiled `Int.ofNat` metadata. That count is not a final closure or
host-import count. No complete capture inventory was written.

See `integration/vbp-native-session-probe/CAPTURE_RESULT.md` for exact command,
diagnostic hash, stage attribution, identities and stopping point. Earlier
`CONTROL.md` and `RESULT.md` remain historical evidence. Frozen FIR `fdef2c1e`,
VBP `c4430bfe` plus exact RPC delta, VIR `9fafe9cf`, Verso `52c8c955`, all
manifest dependencies, renderer-only target and profile scope are unchanged.
No consumer `.lake` or ordinary FIR 4.33 artifact was consumed.

No source-unit workaround, generated-name shim, production compiler/runtime
edit, lowering, resident linking, Wasm encoding, profile descriptor or browser
result. The cause within Lean's type metadata/environment preparation is not
yet established. Full allocation/ownership/tagged-result proof debt is unchanged.
