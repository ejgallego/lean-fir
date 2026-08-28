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
base: cdaf6709301bba04909e52c699e0fe1a80e65b1a, exact accepted main
functional-head: e75ec777e85d870517fc3a2c511dee138d97ed7c
contract-base: cdaf6709301bba04909e52c699e0fe1a80e65b1a; no shared semantic, helper-signature, ABI, layout, ownership, or runtime contract changed
clean-at-update: true
slice: Accepts the measured W7-2 winner from W72-W7-20260828-006. UInt8.toNat, UInt8.toBitVec, and UInt16.toNat form their canonical tagged words directly. UInt32.toNat mirrors Lean 4.32/4.33's lean_usize_to_nat split: values below 2^31 box directly and the high-bit arm retains the existing fir_numeric_make_natural fallback. The integration-owned raw closure and tail-export ratchets record the reviewed deterministic release shape.
files: Fir/Wasm/Emit/ResidentFixedWidth.lean; integration/lean-zip/raw-closure-contract.json; integration/lean-zip/package-raw.mjs; this lane status
contracts: No shared contract changed. Helper identities and signatures, ABI/result kinds and refinement, layouts, ownership, source closure, pre-optimization helper inventory, imports, exported names, module-owned memory, malformed-input behavior, and promoted-Natural representation are unchanged. Only the upstream-shaped fixed-width conversion bodies and reviewed immutable package identity/export indices change.
performance: Two independent diagnostics-off campaigns each used 24 fresh-process AB/BA pairs, two warmups, and seven steady 256-KiB random level-6 samples per side. Campaign one changes median 30.7631 ms (MAD 0.4293) to 30.0417 ms (MAD 0.2755), 17/24 wins, position-adjusted ratio 0.977986. Campaign two changes 30.7199 ms (MAD 0.4370) to 29.9987 ms (MAD 0.2213), 16/24 wins, position-adjusted ratio 0.981976. Output hash 859d6d570d051bf31a309c00dbe7bfef478f2f9cf7cee79bb60e6ddbee89b751 and flat post-call frontier 9237304 are unchanged. The complete module shrinks 383985 to 383816 bytes; the frontier grows 21 bytes to 885936. The final function count grows 501 to 502 because the nontrivial fir_ext_UInt32_toNat wrapper survives optimization; fir_numeric_make_natural already existed and remains the cold high-bit fallback.
checks: W7-2 Lean Beam update/sync/save passed with zero diagnostics; exact-rebase 19-job ResidentFixedWidth cone, 95-job Talos generator cone, 17812-byte zero-import resident fixed-width artifact, and the focused UInt8/UInt16/UInt32 boundary matrix passed. W7 regenerated the exact 383816-byte module / 2c01e19067b4626f7e068795b9c1d3db88db9cc1268a19f783d44cdcd3dd96ff with 502 functions, zero imports, sidecar bbe29e5bce7d0f387bf9a42f7fc395d3ae00e2444bb49f5e5de3e97e9c8ffd6a, exact shifted tail exports, 50 raw comparisons, adapter smoke, and flat cache/scratch reclamation. git diff --check passed. make check passed 730 unique cases, 2172/2172 comparisons, zero findings, 211 bug cards, and 38 mailbox tests. make talos-check passed all 3174 jobs with exact receipt d0402a503fca224a6856738802448efae4f7406bbe736f3be2798602eb9e2ce9. The complete artifact gate passed paired deterministic generation, resident fixed-width and complete-runtime checks, package checks, shared validation, 44/44 concrete readiness artifacts, ownership/reclamation, and raw/concrete differentials; prettyM remains 87595 bytes with 322 functions and 25573 instruction origins.
evidence: W72-W7-20260828-006; BUILD.json e6f5e44cbe37a76e951ecffe4ae25e3ec2c7f4c6707265ab698cb65114ea5a20; paired campaigns cc6db3f528e9865ec8273daaf15e4547ece248e284205cd63574c3f0ef48bc34 and ab417e6f6ed722c1313b8758931f3049df0aea1983eba601980933ab35d0e5cc; W7 preview e75ec777e85d-273d0d6cd9ca-bcac0536f5e1edb24a88.
bug-cards: none
blockers: Serial integration only: W6 currently has untracked proof work in its exact-cdaf6709 worktree while reconciling the landed Float thread and queued trusted Array refinement. Do not advance main underneath it.
handoff: Freeze and consume the containing clean W7 status checkpoint only after W6 publishes or parks its current exact-cdaf6709 proof work. Rebase this disjoint W7 stack onto the resulting accepted main if it advances, rerun proportional W7/Talos/artifact gates, then land through fir/root. Integration remains owned by fir/root.
next: Close W7-W72-20260828-011 as generation-ready, queue the fixed-width implementation refinement behind W6's active trusted Array proof, then serialize the W7 landing after W6's current checkpoint.
```
