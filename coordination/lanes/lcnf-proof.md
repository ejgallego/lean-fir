# lcnf-proof lane

```text
lane: lcnf-proof
owner: lcnf-proof
branch: proof/simpcase
worktree: .worktrees/proof-simpcase
state: ready
base: 6073bc679dbe4a8ff99f6b84b63efab854a67d9b on main
functional-head: 8d8cfcb1e4d6709131c2dd0a56baec62cfd28c0d; preserves the accepted allocation/source-only lifecycle through heap-backed deleted-constructor evaluation and lifts it across the dead result binding into the exact ledger-carrying machine relation
contract-base: 6073bc679dbe4a8ff99f6b84b63efab854a67d9b; consumes the accepted target allocation ledger, hereditary machine relation, and allocated source-only lifecycle without changing them
clean-at-update: true
slice: ELIMDEAD-DELETED-CTOR-PROVENANCE: strengthened LedgerCtorLeftGarbageResult and the failed-token reuse result with the durable allocated source-only carrier for heap results; added a deleted-constructor core-step theorem that returns the normal exact target ledger relation and the aligned machine-level carrier after binding the dead source result, so downstream reset/reuse proofs need not reconstruct allocation history from current target binders
files: Fir/LeanIR/Passes/ElimDeadMachineRel.lean; coordination/lanes/lcnf-proof.md
contracts: none; proof-interface refinement only, with no runtime, interpreter, compiler-pass, target ledger, or shared semantic contract change
checks: PASS proof/simpcase mechanically rebased onto exact main 6073bc67 after the canonical mailbox cutover; PASS post-rebase lake build +Fir.LeanIR.Passes.ElimDeadMachineRel +Fir.LeanIR.Passes.ElimDeadExamples (34 jobs, existing lint warnings only); PASS post-rebase git diff --check; prior functional checkpoint also passed Lean Beam sync/save Fir/LeanIR/Passes/ElimDeadMachineRel.lean (0 errors, 143 pre-existing warnings, source hash 72c0228df6966b62) and make check (21 tooling tests, 22 root jobs, 42 example jobs, 125 harness tests, 719/719 source-LCNF cases, 9/9 direct-machine cases, 719/719 Wasm-V8 cases, 728 unique cases, 2166/2166 comparisons equal, 9097 machine steps, all 210 semantic-tag and 299 semantic-domain floors, zero findings, 207 active bug cards, 26 mailbox tests, validated Lean 4.33 source hashes and exactly one registered trusted axiom)
bug-cards: none new; FIR-BUG-impure-elimDead-live-prefix-historical-target-heap remains confirmed and its negative regression remains green
blockers: none
handoff: ready; integrate rebased functional head 8d8cfcb1 and this containing status commit from proof/simpcase, based directly on exact main 6073bc67, with no shared-contract change and no USize or carrier-dispatch successor work mixed in
next: thread the new deleted-constructor carrier through the ledger step dispatcher/strong simulation result, then consume it in the retained-prefix whole-program invariant to replace DeletedLedgerLiveHeapPrefixReady with generic DeletedLedgerLetLocalReady nodes and remove the focused target live-prefix producer
```
