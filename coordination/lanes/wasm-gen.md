# wasm-gen lane

Current slice: `ROOT-W7-20260915-001`, read-only constructor-metadata comparison.
Root owns integration; W6 remains parked. Existing packages are untouched.

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: waiting
base: b1cbd6677806fd4122368025cdefd9d410aadd38
functional-head: 7a563a6dd227737d812298cdc7bb8a1265875735
contract-base: dc94cd4f0aa716aad5e79a7f77bafa752e9994a9
clean-at-update: true
slice: Public Int/Int.ofNat metadata queries succeed unchanged before and after existing first two capture stages; failure narrowed inside later fresh-unit rebuild.
files: integration/vbp-native-session-probe/{Probe.lean,Metadata.lean,METADATA_RESULT.md,README.md}; coordination/lanes/wasm-gen.md
contracts: none changed; fir.wasm-host-binding/render-core/v0 unchanged
checks: Beam Probe/Metadata sync zero blocking diagnostics and saveReady; session stopped. Focused ordinary lake build Probe passes. FIR_RENDERER_METADATA=1 ordinary-mode batch query exits 0; imported and pre-final metadata equal. Node/bash syntax, git diff --check and scripts/mailbox check pass. No initializer, final-rebuild/full-capture retry, lower/link/encoding or broad gates under root's bounded scope.
bug-cards: none; no semantic discrepancy established and no workaround added
blockers: Earlier capture still fails inside internalizeFinalDependencies. No public-query failure at the requested outer boundaries; exact internal loss remains untraced.
handoff: Clean local-only diagnostic checkpoint on ROOT-W7-20260915-001; root review and narrow repair scope requested. No main/push, consumer edit, package or pointer change.
next: Trace fresh-unit discovery/reset within compileEntryFinalCapturedInternalized, then ownership-aware generic repair. User prioritizes renderer compilation; no unrelated architecture work. Return-node ABI and projection/join diagnostics remain separate.
```

## Evidence

Both `Int` and `Int.ofNat` keep their `Init.Data.Int.Basic` module mapping.
Public base/mono type queries succeed at both boundaries; `nameToImpureType Int`
returns `tobj`; `getCtorLayout Int.ofNat` returns tag 0, one object field,
zero USize/scalar bytes. Constructor native IR is present. Snapshots are equal.
No metadata-initialization API was invoked.

The partial pre-final artifact contains 1,895 declarations and 125 externals,
including `Int.ofNat` and `Int.negSucc`. Of the earlier error's 78 source
roots, 36 already occur as declarations and none as exact externals; unresolved
generated descendants still exist. These are not completed-closure or host
acceptance counts. Do not skip dependency rebuilding based on this result.

See `integration/vbp-native-session-probe/METADATA_RESULT.md` for commands,
query outcomes, diagnostic hash and the proposed W7-owned investigation location.
Earlier `CAPTURE_RESULT.md`, `CONTROL.md` and `RESULT.md` remain valid history.
All frozen Lean 4.34/VBP/VIR/Verso/FIR identities and source-unit constraints
are unchanged. No W6/runtime/proof change, host classification, Wasm artifact,
browser result or performance claim.
