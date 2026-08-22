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
base: 47635960 on clean local main, stacked directly on pushed tooling baseline 713c6e52
functional-head: fcc47335, retype Nat.add's validated one-limb and freshly allocated multi-limb results with the accepted typed object-word round trip; exact lean-zip ratchet 3cdb7ce1; W6 typed-result proof c0427a57 and tracked proof handoff 47635960
contract-base: fcc47335. No Lean semantic, concrete layout, helper signature, semantic Wasm ABI, source entry, adapter API, ownership contract, arena contract, natural-sum implementation, checked arithmetic, or local array contract changed. The existing typed i64ExtendI32U/i32WrapI64 instructions witness a known-valid object word; this slice removes only the obsolete address-zero scratch cast after validation and construction
clean-at-update: true
slice: Nat.add's immediate, checked one-limb, and checked multi-limb exits now all avoid linear-memory scratch after producing a canonical result. A source-shape guard rejects any future .tobject load from address zero in natAddFunction. The final Nat.add body shrinks from 268 to 228 bytes and 130 to 111 instructions; its three remaining scratch loads and three scratch-only stores disappear, the two genuine carry-limb stores and all 13 calls remain. Representative timing and exact-function sampling overlap, so this slice makes no speed claim
files: Fir/Wasm/Emit/ResidentBigNumeric.lean; Fir/Wasm/Emit/ROADMAP.md; integration/lean-zip/README.md; integration/lean-zip/raw-closure-contract.json; coordination/lanes/wasm-gen.md
contracts: Lean-zip remains 769 captured declarations, 139 reviewed externals, 630 retained source functions, 2782 resident helpers before optimization, and 2305 final functions comprising 390 Lean source plus 1915 resident helpers. It retains zero function and memory imports, module-owned memory, the same exports, zero runtime operations, and a flat 9237304-byte post-call frontier. Complete Wasm is 936072 bytes with SHA-256 e20df1c562cf8a3acaf80ac2d0868660aa3afa2a7e8ad6a98a371687c8b1659d; frontier Wasm is 1619339 bytes; function-index digest 86e312b051c4b160874974b0068cf687f9b09d0b0391fefe56e143f9cd57c739; the 999568-byte sidecar SHA-256 is 22b304489260ccf819de7aef50359275943a69c3ddf11777f293e3153ca660cb
checks: TMPDIR, TMP, and TEMP fixed under worktree-local .deps paths. Lean Beam sync/save PASS with zero diagnostics on source hash dff5f0ad1a9e9a81. Focused ResidentBigNumeric dependency build PASS. Standalone 12636-byte resident-big-numeric V8 fixture PASS, including tagged, promoted, checked heap, malformed-input, flat-frontier, persistent, and 8192-limb stack-safe cases. Deterministic lean-zip preview package native/Wasm differential for 5 cases by 10 levels, zero-import complete runtime, persistent-cache scratch reclamation, function sidecar, checksums, and smoke PASS repeatedly and reproduce the exact release bytes after rebasing through 713c6e52. Eight-per-side order-balanced representative rounds preserve output SHA-256 859d6d570d051bf31a309c00dbe7bfef478f2f9cf7cee79bb60e6ddbee89b751 and the flat frontier; baseline/candidate internal medians are 124.147/124.478 ms, within noise. Two artifact-bound V8 profiles place Nat.add at overlapping 3.60%/3.50% median Wasm-self share. W6 Lean Beam, forced direct Lean recompilation, and focused 3118-job dependency cone PASS. On exact combined head 47635960, git diff --check PASS; make check PASS with 713 unique cases and 2121/2121 equal comparisons; make talos-check PASS all 3167 jobs; complete W7 artifact gate PASS with deterministic prettyM publication, the instruction-provenance fixture, 44 concrete artifacts, and 15 source probes; mailbox protocol check PASS
bug-cards: none; no semantic discrepancy was observed
blockers: none for the accepted typed-result checkpoint. Operational thread W7-W6-20260821-005 remains open only for W6's stronger processed-limb-prefix proof of the installed sumCarryFrom/writeSumFrom loops
handoff: The atomic generation/ratchet/proof checkpoint is accepted locally through 47635960 on contract base fcc47335. Push main after this tracked W7 acceptance refresh; do not close W6's continuing full-loop theorem thread
next: Refresh wasm/generation on the pushed checkpoint, take fresh exact-release lean-zip and compact prettyM profiles, then begin the thin shared package verifier/descriptor extraction. fir_dec_once and static ground images remain evidence-gated parked research
```
