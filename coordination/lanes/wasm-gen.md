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
base: 90b52741 on clean local main, including W6's accepted installed Nat sum-step checkpoint
functional-head: 9efc5618, capability-driven browser-package verification and atomic installation
contract-base: 90b52741. No Lean semantics, concrete layout, resident-helper signature, semantic Wasm ABI, source entry, adapter API, ownership contract, arena contract, package metadata schema, public package API, or generated Wasm bytes changed. The shared policy is a consumer verification contract over fields already published by accepted BUILD.json files
clean-at-update: true
slice: Extracted the proven common package-consumption surface without creating a build framework. A small policy drives exact checksum and regular-file validation, BUILD schema/capability checks, artifact length/digest checks, zero-import and module-memory checks, descriptor closure, and exact exports. The fresh-output installer verifies, copies, smokes, atomically renames, verifies and smokes again, and rolls back rejection. The immutable producer gained a pre-publication validation hook. HitScene v2 and selection use package-local policies while preserving their workload smokes and public APIs; the selection export entry remains source-compatible and lost its bespoke verifier/installer implementation
files: integration/package-tools/verified-package.mjs; integration/package-tools/verified-package.test.mjs; integration/package-tools/immutable-package.mjs; integration/package-tools/immutable-package.test.mjs; integration/package-tools/README.md; integration/illuminate-hit-scene/package-policy.mjs; integration/illuminate-hit-scene/package.mjs; integration/illuminate-hit-scene/README.md; integration/illuminate-player/selection-package-policy.mjs; integration/illuminate-player/selection-package.mjs; integration/illuminate-player/export-selection-package.mjs; integration/illuminate-player/export-selection-package.test.mjs; integration/illuminate-player/README.md; integration/talos/artifact/check.sh; Fir/Wasm/Emit/ROADMAP.md; coordination/lanes/wasm-gen.md
contracts: Policy version fir.browser-package-policy/v1 is repository tooling, not a public package metadata version. Exact accepted-package replay reproduced all 7 HitScene files and all 6 selection files byte-for-byte. HitScene remains 64217 bytes, SHA-256 0a59717fef0dafb2fac65e0cbc44c39b5116ab5bd30796be4b1853e1e25d7480, zero imports, 7 exports, module memory; its accepted package-manifest SHA-256 remains 8c890b70828ec3b2e426251b2a7049ce00896d9d7cf17332bcfd33ce90ca28c5. Selection remains 40398 bytes, SHA-256 9a5364ac0e4f78559f29089e9005820c9a9246850d1d19d04ba35671e997eefd, zero imports, 8 total exports, module memory; its accepted package-manifest SHA-256 remains c937b00d838542953c36108a5a6a69254d09ecd1a2d76c0ebbbba829d6cc64a7
checks: TMPDIR, TMP, and TEMP stayed worktree-local. Node syntax checks PASS. Focused package-tools and selection-export suite PASS 15/15. Exact atomic installer replay PASS for both accepted real packages, including packaged smokes twice and 10000 flat-frontier operations per package. git diff --check PASS. make check PASS with 713 unique cases and 2121/2121 equal comparisons. make talos-setup PASS at pinned Talos 0e05edbc; make talos-check PASS all 3167 jobs. Complete W7 artifact gate PASS including new verifier tests, deterministic prettyM regeneration, exact 393-function sidecar with 35615 origins, immutable package checksum/smoke, 44 concrete artifacts, 15 source probes, and the 704-case V8 triangle
bug-cards: none; no semantic discrepancy was observed
blockers: none. The external Illuminate vir-performance worktree was dirty only in its own handoff document and was not modified or used for regeneration; exact accepted-package replay supplied the intended consumption gate without crossing repository ownership
handoff: Rebased cleanly onto local main 90b52741. Integration may fast-forward main through functional head 9efc5618 and this containing status commit. No package restaging or consumer API change is required
next: Continue G3 with the declarative immutable-publication descriptor. Keep it optional and limited to provenance, producer, verifier, operations, ownership, and phase names; do not mix codec hooks or fir_dec_once performance work into that slice
```
