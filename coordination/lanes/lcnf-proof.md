# lcnf-proof lane

```text
lane: lcnf-proof
owner: lcnf-proof
branch: proof/simpcase
worktree: .worktrees/proof-simpcase
state: ready
base: f20cc40a2fcf77231d7fdecfddfa5ab5dba6188e on main
functional-head: 3d8118533afc4d32dfe90099b52473bde386d9d7; transports an existing allocated source-only capability through a source-only deleted let with a monotone source frontier, and exposes the heap-backed deleted-constructor capability from the semantic Step matcher
contract-base: f20cc40a2fcf77231d7fdecfddfa5ab5dba6188e; consumes the accepted target allocation ledger, hereditary machine relation, allocated source-only lifecycle, and Step determinism without changing them
clean-at-update: true
slice: ELIMDEAD-DELETED-CARRIER-SEMANTIC-STEP: added a generic source-only deleted-let theorem that preserves an allocated source-only location across monotone source evaluation while reusing the exact target ledger, plus a semantic deleted-constructor matcher that aligns the exhibited Step with the fresh source allocation and returns the same durable heap capability alongside the ordinary ledger machine relation
files: Fir/LeanIR/Passes/ElimDeadMachineRel.lean; coordination/lanes/lcnf-proof.md
contracts: none; proof-interface refinement only, with no runtime, interpreter, compiler-pass, target ledger, or shared semantic contract change
checks: PASS Lean Beam update/sync/save Fir/LeanIR/Passes/ElimDeadMachineRel.lean (0 errors, 143 pre-existing warnings, source hash 546cc4a83df863b9); PASS lake build +Fir.LeanIR.Passes.ElimDeadMachineRel +Fir.LeanIR.Passes.ElimDeadExamples before and after the mailbox-only f20cc40a rebase (34 jobs, existing lint warnings only); PASS make check on the exact functional source content before the non-overlapping mailbox-only rebase (21 tooling tests, 22 root jobs, 42 example jobs, 125 harness tests, 719/719 source-LCNF cases, 9/9 direct-machine cases, 719/719 Wasm-V8 cases, 728 unique cases, 2166/2166 comparisons equal, 9097 machine steps, all 210 semantic-tag and 299 semantic-domain floors, zero findings, 208 active bug cards, 31 mailbox tests, validated Lean 4.33 source hashes and exactly one registered trusted axiom); PASS post-rebase git diff --check
bug-cards: none new; FIR-BUG-impure-elimDead-live-prefix-historical-target-heap remains confirmed and its negative regression remains green
blockers: none
handoff: ready; integrate rebased functional head 3d811853 and this containing status commit from proof/simpcase, based directly on exact main f20cc40a, with no shared-contract change and no heap-only USize adaptation mixed in
next: after this immutable checkpoint is accepted, address the queued heap-only USize request W7-LCNF-20260826-021 or thread this carrier through the ledger step dispatcher/strong simulation; the latter then enables the retained-prefix whole-program invariant to replace DeletedLedgerLiveHeapPrefixReady with generic DeletedLedgerLetLocalReady nodes and remove the focused target live-prefix producer
```
