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
base: 97474d5beb3c19fe7916ef2fa5ce56e376590daf, exact accepted main
functional-head: 12c01b636a055e18e4a26cc37d74861cac468018
contract-base: 97474d5beb3c19fe7916ef2fa5ce56e376590daf; no shared semantic, helper-signature, ABI, layout, ownership, or runtime contract changed
clean-at-update: true
slice: Accepts the bounded W7-2 winner from W72-W7-20260828-004. Checked/public Array replacement retains exact accepted bytes. Trusted Array.uset, Array.set, and Array.set! test the resident reference count directly, return through the existing exclusive slot-replacement and checked old-value release arm, and defer capacity loading until the unchanged shared/persistent copy-on-write tail. The integration-owned raw ratchet records the resulting deterministic module identity and 12-byte-smaller frontier.
files: Fir/Wasm/Emit/ResidentArray.lean; integration/lean-zip/raw-closure-contract.json; this lane status
contracts: No shared contract changed. Input/index validation, helper identities and signatures, checked/public body, result kinds, layouts, ownership, allocation/copy/retain/release fallback, semantic Wasm ABI, imports, exports, and memory policy are unchanged. Only the trusted helper's internal scheduling and reviewed immutable package identity change.
performance: The trusted fixture shrinks 13819 to 13807 bytes; trusted uset/set/set! each lose two top-level instructions. The complete raw release remains 383985 bytes and 501 functions while the frontier shrinks 885927 to 885915 bytes. Accepted normal-load campaigns report position-adjusted ratios 0.9954 random (16/24 wins) and 0.9942 structured (15/24); the helper's sampled self share falls 1.5171% to 1.1107%, 26.8% relative. No headline end-to-end speed claim is made because a high-load structured tie-breaker was contaminated.
checks: W7-2 Lean Beam update/sync/save passed with zero diagnostics. Independent Beam replay was unavailable because the preserved W7-2 daemon registry names an unavailable cross-namespace endpoint; it was left untouched. W7's final 20-job batch ResidentArray cone passed. Deterministic raw generation matched twice; the immutable preview is 383985 bytes / 0bd3829de25a11267b3aa4bdce3aee1922520058d82f9758336ee68708aa71d0 with 501 functions, zero imports, sidecar d41b1b3b40849fffc027a1ade06d11f507b2b2b5c118eda3256c4e2b75f407cc, exact exports/indices, 50 raw comparisons, and flat cache/scratch reclamation. git diff --check passed. make check passed 730 unique cases, 2172/2172 comparisons, zero findings, 211 bug cards, and 38 mailbox tests. make talos-check passed all 3174 jobs with exact receipt 904477c0e1d41a469504463f295200af93d1751310ae476d962c22695fa85e75. The complete artifact gate passed paired generation, resident checked/trusted Array matrices, package checks, shared validation, 44/44 concrete readiness artifacts, ownership/reclamation, and raw/concrete differentials; the trusted Array fixture is 13807 bytes and prettyM remains 87595 bytes with 322 functions and 25573 instruction origins.
evidence: W72-W7-20260828-004; profile aggregate 21a3218125107eebbb675ace61290ebfcd2468ee1789b072c7ad610bc2d11ab2; deterministic preview a15bf03efed5-273d0d6cd9ca-9695dfd73f79009d14d1.
bug-cards: none
blockers: Serial integration only: W6 has active uncommitted Float32/Float descriptor/proof work on exact base 97474d5b. Do not advance main underneath it.
handoff: Freeze and consume the containing clean status checkpoint after W6 publishes its current Float32/Float contract checkpoint. Land the dependency-ordered W6 shared contract first if required, rebase this disjoint W7 checkpoint onto the accepted head, rerun proportional combined gates, then land W7. Integration remains owned by fir/root.
next: Close W72-W7-20260828-003 as generation-ready, wait for the active W6 Float32/Float checkpoint, then serialize integration and open the separate production-helper proof adaptation only after this implementation lands.
```
