# lcnf-proof lane

```text
lane: lcnf-proof
owner: lcnf-proof
branch: proof/simpcase
worktree: .worktrees/proof-simpcase
state: ready
base: 238d6016ec28aeaa6608a9c544dc36753d7daf48 on main
functional-head: 5633b6e8; preserves the accepted allocation/source-only lifecycle through heap-backed deleted-constructor evaluation and lifts it across the dead result binding into the exact ledger-carrying machine relation
contract-base: 238d6016ec28aeaa6608a9c544dc36753d7daf48; consumes the accepted target allocation ledger, hereditary machine relation, and allocated source-only lifecycle without changing them
clean-at-update: true
slice: ELIMDEAD-DELETED-CTOR-PROVENANCE: strengthened LedgerCtorLeftGarbageResult and the failed-token reuse result with the durable allocated source-only carrier for heap results; added a deleted-constructor core-step theorem that returns the normal exact target ledger relation and the aligned machine-level carrier after binding the dead source result, so downstream reset/reuse proofs need not reconstruct allocation history from current target binders
files: Fir/LeanIR/Passes/ElimDeadMachineRel.lean; coordination/lanes/lcnf-proof.md
contracts: none; proof-interface refinement only, with no runtime, interpreter, compiler-pass, target ledger, or shared semantic contract change
checks: PASS proof/simpcase rebased/fast-forwarded onto exact main 238d6016; PASS Lean Beam sync/save Fir/LeanIR/Passes/ElimDeadMachineRel.lean (0 errors, 143 pre-existing warnings, source hash 72c0228df6966b62); PASS lake build +Fir.LeanIR.Passes.ElimDeadMachineRel +Fir.LeanIR.Passes.ElimDeadExamples (34 jobs); PASS make check (21 tooling tests, 22 root jobs, 42 example jobs, 125 harness tests, 719/719 source-LCNF cases, 9/9 direct-machine cases, 719/719 Wasm-V8 cases, 728 unique cases, 2166/2166 comparisons equal, 9097 machine steps, all 210 semantic-tag and 299 semantic-domain floors, zero findings, 207 active bug cards, 26 mailbox tests, validated Lean 4.33 source hashes and exactly one registered trusted axiom); PASS git diff --check
bug-cards: none new; FIR-BUG-impure-elimDead-live-prefix-historical-target-heap remains confirmed and its negative regression remains green
blockers: none
handoff: ready; integrate functional head 5633b6e8 and this containing status commit from proof/simpcase, based directly on exact main 238d6016, with no shared-contract change
next: thread the new deleted-constructor carrier through the ledger step dispatcher/strong simulation result, then consume it in the retained-prefix whole-program invariant to replace DeletedLedgerLiveHeapPrefixReady with generic DeletedLedgerLetLocalReady nodes and remove the focused target live-prefix producer
```
