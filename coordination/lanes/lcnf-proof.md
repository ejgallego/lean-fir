# lcnf-proof lane

```text
lane: lcnf-proof
owner: lcnf-proof
branch: proof/simpcase
worktree: .worktrees/proof-simpcase
state: ready
base: fcd623cbb96f5846b11fb89368f417d04bb9715f on main
functional-head: b6a86e522dc2f18948e339b1898289697d5579ce; mints an allocated source-only provenance carrier at one-sided allocation, transports it through same-target-frontier operations and paired allocations, lifts it to the hereditary machine relation, and lets deleted reset/reuse readiness consume it directly
contract-base: fcd623cbb96f5846b11fb89368f417d04bb9715f; consumes the accepted target allocation ledger, hereditary machine relation, arbitrary live-prefix proof interface, and exact resident scalar-box alias contract without changing them
clean-at-update: true
slice: ELIMDEAD-SOURCE-ONLY-LIFECYCLE: added AllocatedSourceOnlyLedgerShadowRuntimeRelAt with the historical source-frontier bound required by later paired allocation; added one-sided minting, arbitrary same-target-frontier transport, reset/reuse specializations, paired-allocation transport without a current heap lookup, and the one-sided-then-paired composition; added the aligned machine-level carrier/assembler and direct deleted-operation bridges; refactored the nonempty-ledger reset/reuse regression to carry this capability across the deleted reset instead of maintaining a loose relation and separate source-only fact
files: Fir/LeanIR/Passes/ElimDeadMachineRel.lean; Fir/LeanIR/Passes/ElimDeadExamples.lean; coordination/lanes/lcnf-proof.md
contracts: none; proof-interface refinement only, with no runtime, interpreter, compiler-pass, target ledger, or shared semantic contract change
checks: PASS second rebase proof/simpcase onto exact main fcd623cb after exact resident scalar-box aliases landed; PASS final post-rebase Lean Beam refresh/save Fir/LeanIR/Passes/ElimDeadMachineRel.lean (0 errors, 143 pre-existing warnings, source hash f2c2eda766177b54); PASS final post-rebase Lean Beam refresh/save Fir/LeanIR/Passes/ElimDeadExamples.lean (0 errors, 28 pre-existing warnings, source hash e1a5d4ab214ae8f7); PASS final post-rebase lake build +Fir.LeanIR.Passes.ElimDeadMachineRel +Fir.LeanIR.Passes.ElimDeadExamples (34 jobs, forced dependency cone); PASS final post-rebase make check (21 tooling tests, 22 root jobs, 42 example jobs, 125 harness tests, 719/719 source-LCNF cases, 9/9 direct-machine cases, 719/719 Wasm-V8 cases, 728 unique cases, 2166/2166 comparisons equal, 9097 machine steps, all 210 semantic-tag and 299 semantic-domain floors, zero findings, 207 active bug cards, 26 mailbox tests, validated Lean 4.33 source hashes and exactly one registered trusted axiom); PASS git diff --check
bug-cards: none new; FIR-BUG-impure-elimDead-live-prefix-historical-target-heap remains confirmed and its negative regression remains green
blockers: none
handoff: ready; integrate functional head b6a86e52 and this containing status commit from proof/simpcase, rebased on exact main fcd623cb, with no shared-contract change
next: carry the lifecycle capability through the retained-prefix whole-program rectangular invariant and replace its DeletedLedgerLiveHeapPrefixReady special nodes with generic DeletedLedgerLetLocalReady nodes, removing the remaining focused target live-prefix producer
```
