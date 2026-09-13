# wasm-gen lane

Current bounded probe: `ROOT-W7-20260913-001`, revised by
`ROOT-W7-20260913-002..003`. Root owns integration; W6 remains parked.
The earlier CG-05A/CG-05B/source-equation stack was accepted, with both source
equation threads closed at main `1ea81797`; no package was replaced here.

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: blocked
base: dc94cd4f0aa716aad5e79a7f77bafa752e9994a9
functional-head: a7722bf2ca4a2c1d79621d041930492ee9d340a0
contract-base: dc94cd4f0aa716aad5e79a7f77bafa752e9994a9
clean-at-update: true
slice: Isolated exact-Lean-4.34 renderer-core probe; stopped at reproducible prerequisite compilation failure before FIR capture.
files: integration/vbp-native-session-probe/; coordination/lanes/wasm-gen.md
contracts: none changed; consumes root's draft fir.wasm-host-binding/render-core/v0
checks: Source/archive identity checks pass; FIR ResidentLinker dependency builds on Lean 4.34.0-rc2; initial source dependency build fails and was interrupted after first failure; exact focused VersoBlueprint.Html build exits 1 both before and after renderer retarget. Read-only Beam update/sync of that source is green, zero diagnostics, saveReady; no save, session stopped. Node syntax checks, bash syntax check, git diff --check, mailbox check pass. Broad make check/Talos/artifact campaigns not run under root's explicit first-blocker stop rule; no generation-ready claim.
bug-cards: none; build failure, no established semantic discrepancy or workaround
blockers: Lean 4.34 leanir reports unknown String.Slice.posGE._redArg while compiling VersoBlueprint.Html.escapeText. Fixture postponement/source-unit interaction versus upstream issue remains unclassified.
handoff: One clean immutable failed-probe checkpoint for root review, not artifact acceptance. Consume exact completion on ROOT-W7-20260913-001. No main advance, push, consumer write, old package or pointer change.
next: Await root review of a fixture-only postponement/capture-boundary follow-up. Actual return-node ABI census and deeper projection/join diagnostics remain separately queued; no optimization or proof change bundled.
```

## Exact boundary and result

The sole current target is
`VersoBlueprint.Experimental.VirPreview.Renderer.render`. NativeSession
component/session roots were superseded before capture. The original initial
dependency build selected the broader source; the first failing module is also
on the renderer's dependency chain through `Informal.ExternalMarkupView`.
The focused reproduction was repeated after the retarget/contract rebase.

FIR's compiler archive remains the originally requested `fdef2c1e`; the
accepted successor `dc94cd4f` changes only contract documentation and board
state. Lean is 4.34.0-rc2, commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`.
VBP `c4430bfe` plus its exact hash-checked dirty RPC delta, VIR `9fafe9cf`,
Verso `52c8c955`, and all consumer-manifest dependency revisions are archived
into worktree-local state. No consumer or ordinary FIR 4.33 build input is used.

See `integration/vbp-native-session-probe/RESULT.md` for exact identities,
diagnostic, commands, and explicitly unrun acceptance. Local source inventory
and logs are under `.deps/native-session-probe/`; they are disposable diagnostic
working state, not a permanent approval registry.

No final-LCNF closure, Wasm, import/export inventory or binding-profile verdict
was obtained. The capture/link drivers are not yet Lean-validated because the
dependency cone fails first. Conditional token/dispatch conformance work did
not start; the structural scaffold fails closed pending actual frontier review.
Full allocation/ownership/tagged-result proof debt remains unchanged.
