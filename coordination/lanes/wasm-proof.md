# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 680ff128 on main; tracked W7 handoff containing functional source commit db6d46a7
functional-head: 668e1288
contract-base: db6d46a7; rebased equivalent of requested W7 functional head 970e0087, changing only the immediate USize conversion implementation to return i64ExtendI32U .usize directly
clean-at-update: true
slice: Closed W7-W6-20260820-008 by rebasing the completed W6 stack onto tracked W7 handoff 680ff128. Git dropped the duplicate db6d46a7 implementation automatically and preserved W7 history before the equivalent W6 commits: 4fde5829 is the independent natural-limb proof and 668e1288 is the direct-USize proof. The latter still proves that canonical tagged Nats decode and return directly with exact store preservation, covers both USize.ofNat and erased-argument USize.ofNatLT, and retains the validator-first checked promoted/arbitrary-limb modulo-2^64 path and restoring scratch cast.
files: integration/talos/FirTalos/ConcreteResidentUSize.lean; coordination/lanes/wasm-proof.md
contracts: none changed. The proof consumes the existing typed i64ExtendI32U .usize instruction and existing helper signatures, semantic ABI, concrete layout, ownership, validation, and modulo-2^64 contracts. CheckedNaturalCalls is unchanged; its WP lemma is factored over an arbitrary continuation solely because the scratch cast now resides inside the checked ifElse arm.
checks: After rebase, Lean Beam refresh/save for FirTalos/ConcreteResidentUSize.lean passed with zero diagnostics and source hash 9a80e0a2a69d7077; `lake -d integration/talos build FirTalos.ConcreteResidentUSize` passed (3,080 jobs); `git diff --check 680ff128..HEAD` passed; `make check` passed (704 source cases across native/LCNF/V8, nine direct-machine cases, 2,121/2,121 comparisons equal, 713 unique cases, zero findings, 190 active bug cards, 25 mailbox tests); `make talos-setup` passed at Talos 0e05edbc; `make talos-check` passed (3,165 jobs).
bug-cards: none
blockers: none. The branch is exactly three W6 commits ahead of tracked W7/main base 680ff128 with no duplicate source commit.
handoff: Integration may validate and fast-forward the clean W6 stack over 680ff128: 4fde5829 (independent BigNumeric accessor boundary), 668e1288 (direct-USize proof), and the containing tracked mailbox commit resolved from wasm/talos-runtime. No W7 history or implementation, fixture, profile, shared symbolic instruction, root umbrella, or BOARD file was modified by W6.
next: After integration, claim W7-W6-20260820-003 and adapt the Nat multiplication refinement to its landed tagged-pair dispatcher; Nat subtraction follows in W7-W6-20260820-004. The longer-term validator-side canonical extent/reserved-lane/ownership/top-nonzero bridge remains the substantive CheckedNaturalCalls frontier.
```
