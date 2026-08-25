# wasm-gen lane

The forward-looking W7 plan lives in
[`Fir/Wasm/Emit/ROADMAP.md`](../../Fir/Wasm/Emit/ROADMAP.md). Accepted milestone
history remains on `coordination/BOARD.md`; this mailbox records the current
single-writer W7 handoff.

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: 14504dc905775e8e29d3cec38f59cf058241cc0a
functional-head: f35913d47ab57f615bb9243b2f4fcb5d16821e38
contract-base: 14504dc905775e8e29d3cec38f59cf058241cc0a
clean-at-update: true
slice: Expose a reduction-visible decomposition of the exact production fir_dec_once body. The production function now consumes decrementOnceBody directly; its staged builders are public under an expose section, descriptor dispatch is structurally recursive over the descriptor list, and decrementOnceFunction_body_of_ok ties successful installation to that body without a parallel certificate.
files: Fir/Wasm/Emit/ResidentRelease.lean; coordination/lanes/wasm-gen.md
contracts: Production helper name, signature, locals, control flow, layout, ownership behavior, and emitted instructions are unchanged. The new public proof surface is decrementOnceBody plus its production-used staged builders; descriptorReleaseBody now takes List (Array AbiKind), while ownedReleaseBody preserves the production Array input by calling descriptors.toList at index zero.
checks: Lean Beam update/sync/save passed with zero diagnostics and source hash 1d1e5c758f337d10. A downstream import probe under worktree-local .deps checks every exposed builder and proves the extraction theorem. lake build +Fir.Wasm.Emit.ResidentLinker passed 54/54 jobs. git diff --check and make check passed: 726 unique cases, 2160/2160 comparisons equal, zero findings. make talos-check passed 3172 jobs. bash integration/talos/artifact/check.sh passed resident, package, Node/browser, native/LCNF/V8, and concrete gates. The focused resident-release Wasm and JSON are byte-identical before and after: 1850 bytes, Wasm SHA-256 c2edc88d12400714aa5268b37e61dd55d11d2fb6073c888d2c332565378c7d0a, JSON SHA-256 3c878a8bf9c00d557fec31ef4baade4d96bb3844324943df089b727a1b41e4db.
bug-cards: none
blockers: none. FIR-BUG-wasm-none-adapter-if-branch-depth remains separate and is not worked around by this slice.
handoff: Fast-forward f35913d47ab57f615bb9243b2f4fcb5d16821e38 and this clean lane-status commit onto main. W6 may then rebase its separate Talos-only resident-header proof stack and consume decrementOnceBody; W7 did not edit any W6-owned file.
next: Support W6 while it lifts installed-header termination to the exact production body. Independently review the W7-2 ByteArray wide-store experiment after its narrow lease completes.
```
