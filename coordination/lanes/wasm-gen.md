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
base: b54ed3c16f9a2d21c1662e792e60b33ae8d7b16e, exact accepted main
functional-head: 175324a16557ba0685c2c1e6c496140866821526
contract-base: b54ed3c16f9a2d21c1662e792e60b33ae8d7b16e; no shared semantic, helper-signature, ABI, layout, ownership, or runtime contract changed
clean-at-update: true
slice: Repairs the stale pre-rebase lean-zip raw package ratchet exposed by W72-W7-20260829-001. The accepted 383816-byte package had retained pre-rebase trusted Array bodies; exact current-main generation uses the landed native decrement-before-store bodies and is deterministically 383810 bytes. The strict contract now names that exact current output. This stack also carries the already-green rejected ByteArray placement documentation tail.
files: integration/lean-zip/raw-closure-contract.json; integration/lean-zip/README.md; this lane status
contracts: none. No executable helper, signature, ABI, layout, ownership rule, source closure, helper inventory, import/export surface, or package pointer changed. Only three exact artifact-identity fields changed: final function-index digest, function-sidecar SHA-256, and complete Wasm byte length.
performance: No new performance claim. The corrected current-main module is six bytes smaller than the stale pre-rebase artifact. All 502 sidecar records are identical except bodyBytes for fir_ext_Array_set! 401 -> 399, fir_ext_Array_set 362 -> 360, and fir_ext_Array_uset 360 -> 358; every name, index, origin, call edge, export, and other field is unchanged.
checks: W7 independently reproduced the old fail-closed gate after 50 native/Wasm/inflate comparisons, zero-import levels 1-10, and flat cache/scratch reclamation. A clean committed determinism preview generated the complete module twice byte-identically and passed package smoke: 444465-byte base cc02eaae, 885936-byte frontier e181f93f, 383810-byte complete module 06309738, 207745-byte sidecar 97c61020, ordered function digest 89974694, 502 functions, zero imports. git diff --check passed. make check passed 730 unique cases, 2172/2172 comparisons, zero findings, 212 bug cards, and 38 mailbox tests. make talos-check passed 3188 jobs with receipt 32bb2aa87e39c8da3e6b2f53913a75ab7ae74f0555b15d7788157fa026f75059. The complete artifact gate passed paired deterministic generation, resident Array/ByteArray/fixed-width and complete-runtime checks, package checks, shared validation, 44/44 concrete readiness artifacts, ownership/reclamation, and raw/concrete differentials; prettyM remains 87595 bytes with 322 functions and 25573 instruction origins.
evidence: W72-W7-20260829-001; clean preview .deps/lean-zip-ratchet/clean-determinism with package ID 175324a16557-273d0d6cd9ca-8c94e520f9a91bf61f23; canonical pointer intentionally unchanged pending root integration.
bug-cards: FIR-BUG-wasm-none-lean-zip-pre-rebase-package-ratchet, owned by W7-2
blockers: none
handoff: Land the exact clean containing W7 status checkpoint through fir/root, superseding W7-ROOT-20260828-008. After main advances, integration may explicitly authorize canonical package publication from the exact landed head; this W7 slice did not move the pointer.
next: Close W72-W7-20260829-001 after root accepts the stack, then let W7-2 profile exact current package 06309738 while W7 selects the next independent generation slice.
```
