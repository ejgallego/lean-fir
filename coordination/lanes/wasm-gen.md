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
base: 055eeb3d on clean local main, including the accepted G3.1 package verification and atomic-installation surface
functional-head: a0673300, producer-side draft of the verified source-package descriptor
contract-base: 055eeb3d. No Lean semantics, concrete layout, resident-helper signature, semantic Wasm ABI, source entry, adapter API, ownership contract, arena contract, BUILD schema, public package API, package inventory, package identity, or generated Wasm bytes changed. browser-benchmarks/source-package/v1 is currently a repository-tooling draft returned in memory after package verification, not a published package contract
clean-at-update: true
slice: Added the minimal producer-owned descriptor for packages that have already passed fir.browser-package-policy/v1 verification. The descriptor normalizes source provenance, producer/backend and Wasm identity, verifier/checksum/smoke facts, exact production/diagnostic operation inventories, public phase names, and ownership/reclamation capabilities. It fails closed on incomplete Git or SHA identities, operation or phase drift, a missing adapter checksum, and inconsistent ownership metadata. HitScene v2 and selection-player v3 declare only their existing public operations, phases, and accepted ownership model. The verifier returns the normalized descriptor in memory; immutable package payloads are intentionally unchanged pending consumer review
files: integration/package-tools/source-package.mjs; integration/package-tools/source-package.test.mjs; integration/package-tools/SOURCE_PACKAGE.md; integration/package-tools/README.md; integration/package-tools/verified-package.mjs; integration/illuminate-hit-scene/package-policy.mjs; integration/illuminate-player/selection-package-policy.mjs; integration/illuminate-player/export-selection-package.test.mjs; integration/talos/artifact/check.sh; Fir/Wasm/Emit/ROADMAP.md; coordination/lanes/wasm-gen.md
contracts: Descriptor version browser-benchmarks/source-package/v1 is a draft repository-tooling vocabulary and is not yet present in BUILD.json or SHA256SUMS. It deliberately excludes application semantics, oracles, corpora, samples, thresholds, performance claims, and codec implementation. Review snapshots are ignored outputs: HitScene 4290 bytes / dad988f4e24142a89f6b25d941ba4de081728fa49cc70e714454cd895df3c26d; selection 4523 bytes / 6aabb23f8073b682c75f6b01d68aa2994a4781b98ded91daec511b283e0f87b5. Accepted package bytes remain HitScene 64217 bytes / 0a59717fef0dafb2fac65e0cbc44c39b5116ab5bd30796be4b1853e1e25d7480 with zero imports and 7 exports, and selection 40398 bytes / 9a5364ac0e4f78559f29089e9005820c9a9246850d1d19d04ba35671e997eefd with zero imports and 8 exports
checks: TMPDIR, TMP, and TEMP stayed worktree-local. Focused package-tools and selection-export suite PASS 17/17. git diff --check PASS. make check PASS with 713 unique cases and 2121/2121 equal comparisons. make talos-setup PASS at pinned Talos 0e05edbc; make talos-check PASS all 3167 jobs. Complete W7 artifact gate PASS including the new source-descriptor and verifier tests, deterministic prettyM regeneration at 120739 bytes with exact 393-function sidecar and 35615 origins, immutable package checksum/smoke, 44 concrete artifacts, 15 source probes, and the 704-case native/LCNF/V8 triangle with 2112/2112 comparisons and zero findings
bug-cards: none; no semantic discrepancy was observed
blockers: none. Consumer reviews are open in W7-ILL-20260822-001, W7-VERSO-20260822-001, and W7-LZ-20260822-001, but they gate only a later publication decision, not this optional producer-side draft
handoff: Built on clean local main 055eeb3d. Integration may fast-forward main through functional head a0673300 and this containing status commit. No package restaging, consumer API change, or package identity update is required
next: Process the three consumer reviews, then choose whether the descriptor belongs inside BUILD or in a checksummed sibling. Publish only in a separate metadata-version and package-identity slice. G3.3 bounded codec hooks remain deferred until at least two accepted packages demonstrate the same codec boundary
```
