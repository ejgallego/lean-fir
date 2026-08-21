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
state: waiting
base: 1fbe39e9 on main, the accepted scratch-free Nat-decision stack
functional-head: 6a020114, retype only the known-valid object returned by the Nat.add immediate-input arm through i64ExtendI32U .uint64 followed by i32WrapI64 .tobject; exact lean-zip ratchet c7303630
contract-base: 1fbe39e9. No Lean semantic, concrete layout, helper signature, semantic Wasm ABI, source entry, adapter API, ownership contract, arena contract, natural-sum implementation, checked fallback, or local array changed. The existing typed i64ExtendI32U/i32WrapI64 symbolic instructions witness the known-valid object-word retype
clean-at-update: true
slice: Only Nat.add's two-immediate arm avoids linear-memory scratch after the existing naturalSum call. The typed round trip preserves every 32-bit tagged or promoted heap result and Binaryen erases the physical no-op. Checked one-limb and multi-limb paths retain their established scratch cast. The exact final Nat.add body shrinks from 296 to 268 bytes and 144 to 130 instructions; memory loads fall 5 to 3 and stores 7 to 5 while all 13 call sites remain unchanged. Seven order-balanced lean-zip rounds improve the median of round medians from 131.033 to 128.401 ms, 2.01%; four exact-function profiles reduce median Nat.add self samples from 321 to 170.5 and Wasm-self share from 6.14% to 3.52%
files: Fir/Wasm/Emit/ResidentBigNumeric.lean; integration/talos/artifact/resident-big-numeric-client.mjs; integration/lean-zip/raw-closure-contract.json; coordination/lanes/wasm-gen.md
contracts: Lean-zip remains 769 captured declarations, 139 reviewed externals, 630 retained source functions, 2782 resident helpers before optimization, and 2305 final functions comprising 390 Lean source plus 1915 resident helpers. It retains zero function and memory imports, module-owned memory, the same exports, zero runtime operations, and a flat 9237304-byte post-call frontier. Complete Wasm is 936112 bytes, frontier Wasm is 1619431 bytes, function-index digest 03977d2f49c3b487dc2e433ce862bb4ed34c41922be9e842fe7d86d9d2015266, and the 999568-byte sidecar SHA-256 is 163fd6fe3d1da4aa5a7951844fd56fd0d057d4e1a28c5b68486a5e51be5b3e04
checks: TMPDIR, TMP, and TEMP fixed under the W7 worktree. Lean Beam sync/save PASS with zero diagnostics. Focused ResidentBigNumeric build PASS. Standalone resident-big-numeric V8 fixture PASS, including tagged, promoted, checked heap, malformed-input, flat-frontier, persistent, and stack-safe cases. Deterministic lean-zip package native/Wasm differential, independent inflate, levels 1--10 adapter, zero-import complete runtime, persistent-cache scratch reclamation, checksums, and smoke PASS twice; exact Wasm SHA-256 6890e139aa1902b653051243e2ccd36c44a159367c4588b1beac1330a0ac78d0. Seven-per-side order-balanced timing PASS with identical output SHA-256 859d6d570d051bf31a309c00dbe7bfef478f2f9cf7cee79bb60e6ddbee89b751; baseline median/MAD 131.033/1.722 ms, candidate 128.401/0.956 ms. Four candidate 500-microsecond raw V8 profiles resolve through the exact sidecar and contain 4929/4912/4764/4949 Wasm samples. git diff --check PASS. The complete W7 artifact gate PASS includes 44 concrete artifacts and 15 source probes. make check PASS with 713 unique cases and 2121/2121 equal comparisons. make talos-setup PASS; make talos-check reaches 3161/3167 and fails only at the expected stale Nat.add immediate-shape theorem in FirTalos.ConcreteResidentNat
bug-cards: none; the Talos failure is the expected cross-lane proof adaptation for an intentional generation body change, not a semantic discrepancy
blockers: W6 proof adaptation requested in operational thread W7-W6-20260820-015. The request file is prepared, but the global mailbox check is temporarily blocked by an unrelated tooling/W7-2 fork after TOOL-W72-20260820-003; no W7 or W6 message was rewritten
handoff: Generation is ready at c7303630. Integration must not expose the stale-proof intermediate on main; consume a clean W6 proof stacked after c7303630, then land W7 generation first and W6 proof second atomically
next: Wait for W6 to adapt the exact immediate Nat.add object-result theorem. Phase two may audit the checked one-limb and multi-limb object returns only after this narrow slice is linked/accepted; fir_dec_once remains parked behind the ownership-semantics question
```
