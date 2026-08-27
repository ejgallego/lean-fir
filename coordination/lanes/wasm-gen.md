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
base: 4f1ebd80e8ab47a47d17c5794422cd4c53f15b6c, exact current main
functional-head: 6725cf9bba03765e289f655f89356334561eeb43
contract-base: 4f1ebd80e8ab47a47d17c5794422cd4c53f15b6c; no shared semantic, helper-signature, ABI, layout, ownership, or runtime contract changed
clean-at-update: true
slice: Accepts the measured W7-2 winner from W72-W7-20260827-004. The existing Nat decision caller rewrite is factored once and now covers Nat.decEq, Nat.decLt, and Nat.decLe for both primitive external and post-ResidentNumeric targets. Two canonical tagged words compare directly with i32.eq/i32.lt_u/i32.le_u; every mixed, promoted, or arbitrary-limb pair retains the existing checked resident fallback and UInt8 result lane. Integration-owned raw, Level-1, and stored lean-zip artifact ratchets record the resulting deterministic zero-import modules and shifted raw export indices.
files: Fir/Wasm/Emit/ResidentBigNumeric.lean; integration/lean-zip/raw-closure-contract.json; integration/lean-zip/level1-closure-contract.json; integration/lean-zip/closure-contract.json; integration/lean-zip/package-raw.mjs; this lane status
contracts: No shared contract changed. Primitive identities, call signatures, UInt8 results, arbitrary-precision helpers, malformed-input checks, semantic Wasm ABI, concrete layouts, ownership, imports, exports by name, and memory policy are unchanged. Only upstream-shaped typed caller implementation and reviewed immutable package identities change.
performance: Four order-balanced fresh-process campaigns improve: random 16-pair ratio 0.95057 (12/16 wins), random 24-pair repeat 0.96151 (22/24), structured 16-pair 0.96580 (11/16), and structured 24-pair repeat 0.95458 (23/24). The deliberate cost is +18,303 bytes (+5.0%) for the raw complete module because roughly 122 decision call sites inline the upstream-shaped tagged/tagged branch.
checks: Lean Beam update/sync/save on Fir/Wasm/Emit/ResidentBigNumeric.lean passed with zero diagnostics and source hash 9f8059325aaf1cad. W7-2's focused 17-job module cone, 95-job artifact-generator cone, unchanged resident numeric external-engine clients, 50-case raw differential, reclamation checks, balanced benchmarks, make check, all 3174 Talos jobs, and full artifact gate passed. W7 integration reran deterministic raw packaging twice: 383985-byte zero-import module b33ea862dc65272e7bd1fc5afb6aff9c7a951062aba04e2b38b65cee46c0de74, 501 final functions, function sidecar cc1039d6aae9f336f2a54b7a676086e35bdc4aac106c963b074d617973d0e013. Stored packaging passed at 12534 bytes / a8938f03d18071965bd1405085781953a77ac047319a048b5d191f05f92ca91c; Level-1 passed at 205789 bytes / c021d5db0a6861d25ddbaa443ad5da7000455a63fdebedb349a4cf3242889af6. git diff --check passed. make check passed 730 unique cases, 2172/2172 comparisons, zero findings, 211 bug cards, and 38 mailbox tests. make talos-check passed all 3174 jobs with exact receipt 367b144eb2478b3583f4274c7011fe8736836dff12d4b23c3177a8d37a6be172. The complete deterministic artifact gate passed paired generation, package checks, shared validation, 44/44 concrete readiness artifacts, and raw/concrete differentials; prettyM is 87595 bytes with 322 functions and 25573 instruction origins.
evidence: W72-W7-20260827-004 and its four raw benchmark hashes; deterministic raw package 6725cf9bba03-273d0d6cd9ca-de36a9ecbe25d4e669c5; stored package 6725cf9bba03-273d0d6cd9ca-07f43b5bfa7abbd32fd5; Level-1 package 6725cf9bba03-273d0d6cd9ca-f47ad0ea79a97d06d2e1.
bug-cards: none
blockers: none
handoff: Integrate the containing clean status checkpoint after verifying it descends from exact base 4f1ebd80. Then replay the disjoint W6 immediate Nat.mod proof checkpoint from W7-ROOT-20260827-008 onto the accepted generation head and land it second. Integration remains owned by fir/root.
next: Close the measured W7-2 lease and package-ratchet thread as landed, integrate the queued W6 Nat.mod refinement, then refresh wasm/generation to the combined accepted main and return to the consumer-driven generation queue.
```
