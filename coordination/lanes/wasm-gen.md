# wasm-gen lane

Bounded control: `ROOT-W7-20260913-004`, following the accepted negative probe
`ROOT-W7-20260913-001..003`. Root owns integration; W6 remains parked.
CG-05A/CG-05B/source equations and previous consumer packages are untouched.

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: waiting
base: 65360510826b50939a7731c2cdb397a3368bfd97
functional-head: 0cfd10174035992f25b6933a99a885f7e8d0dbaa
contract-base: dc94cd4f0aa716aad5e79a7f77bafa752e9994a9
clean-at-update: true
slice: Fixture-only A/B isolates postponed compilation failure; ordinary renderer source metadata is visible. Investigation complete, not generation-ready.
files: integration/vbp-native-session-probe/{lakefile.lean,control.mjs,Classify.lean,README.md,CONTROL.md}; coordination/lanes/wasm-gen.md
contracts: none changed; retains root's draft fir.wasm-host-binding/render-core/v0
checks: control.mjs passes: true fails with expected missing helper, false succeeds; actual option maps differ only in postponement and source SHA unchanged. Ordinary +Probe:deps and Probe pass (676/677 jobs). Beam lakefile/metadata sync zero blocking diagnostics; direct batch metadata agrees, exit 0; Beam stopped. Node/bash syntax, git diff --check and scripts/mailbox check pass. No broad make/Talos/artifact/browser gates under root's explicit bounded-control scope.
bug-cards: none; compilation investigation, no established semantic discrepancy or workaround
blockers: No ordinary source-preparation blocker. Actual capture, lower/link and profile conformance remain unexecuted, not accepted.
handoff: Clean local-only diagnostic checkpoint on ROOT-W7-20260913-004; root may review this evidence separately from artifact acceptance. No main advance, push, consumer edit, package or pointer change.
next: Root review, then separately authorize actual renderer capture through the existing ordinary-source fallback. Return-node ABI census and deeper projection/join diagnostics remain separately queued.
```

## Result and preserved boundary

With exact Lean 4.34.0-rc2, the same `VersoBlueprint.Html` source fails under
experimental postponed compilation (`String.Slice.posGE._redArg` missing in
`leanir`) but builds under ordinary compilation. The generated setup files
have identical options except `compiler.postponeCompile`. The true default is
preserved; only the control invocation overrides it.

The ordinary renderer module contains the real source root
`VersoBlueprint.Experimental.VirPreview.Renderer.render`, its impure signature
and native IR. Deferred groups are empty. These satisfy the source resolver's
metadata inputs; the existing individual-source driver has an ordinary-source
fallback. This is not proof that executing that capture will succeed.

See `integration/vbp-native-session-probe/CONTROL.md` for commands, setup/source
hashes, exact metadata, interpretation and unrun acceptance. `RESULT.md`
preserves the earlier negative checkpoint. Frozen FIR `fdef2c1e`, VBP
`c4430bfe` plus the exact RPC delta, VIR `9fafe9cf`, Verso `52c8c955`, all
manifest dependencies, renderer-only target and host-profile scope are unchanged.
No consumer `.lake` or ordinary FIR 4.33 artifacts were consumed.

`Probe.lean` compiles in ordinary mode; `Emit.lean` and actual capture/link have
not run. No closure, Wasm, host frontier, profile verdict or browser result is
claimed. Full allocation/ownership/tagged-result proof debt is unchanged.
