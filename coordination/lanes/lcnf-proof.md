# lcnf-proof lane

```text
lane: lcnf-proof
owner: lcnf-proof
branch: proof/simpcase
worktree: .worktrees/proof-simpcase
state: ready
base: 8c939e5d59fa3767d203e5678ecfa8c90a8ec475 on main
functional-head: 730f808e3cccab4e0889533ef56836a3201e6e14; introduces a ledger-aligned source-only carrier for ElimDead deleted operations, routes the arbitrary live-prefix adapter through it, removes the retained-prefix fixture's duplicate target phase automaton, and proves that historical target allocations make a direct global live-prefix derivation impossible
contract-base: 8c939e5d59fa3767d203e5678ecfa8c90a8ec475; consumes the accepted target allocation ledger, hereditary machine relation, and arbitrary live-prefix proof interface
clean-at-update: true
slice: ELIMDEAD-ALIGNED-SOURCE-ONLY-PROVENANCE: added SourceOnlyLedgerBinderReadyReachableMachineRelatedAt and historical-heap-safe deleted-operation bridges; retained live-prefix evidence is now one producer of that carrier rather than the generic proof boundary; the retained-prefix whole-program contract stores canonical target reachability and reconstructs focused phase facts only at special nodes; added a two-cell negative kernel regression showing an unreachable historical target allocation has no direct live binder
files: Fir/LeanIR/Passes/ElimDeadMachineRel.lean; Fir/LeanIR/Passes/ElimDeadExamples.lean; bugs/FIR-BUG-impure-elimDead-live-prefix-historical-target-heap.md; coordination/lanes/lcnf-proof.md
contracts: none; proof-interface refinement only, with no runtime, interpreter, compiler-pass, or shared semantic contract change
checks: PASS exact rebase/base audit against main 8c939e5d; PASS Lean Beam refresh/save Fir/LeanIR/Passes/ElimDeadMachineRel.lean (0 errors, 143 pre-existing warnings, source hash 064e46c619b66c59); PASS Lean Beam refresh/save Fir/LeanIR/Passes/ElimDeadExamples.lean (0 errors, 28 pre-existing warnings, source hash a44a417592a35cb8); PASS lake build +Fir.LeanIR.Passes.ElimDeadMachineRel +Fir.LeanIR.Passes.ElimDeadExamples (34 jobs, forced dependency cone); PASS make check on exact base 8c939e5d (21 tooling tests, 22 root jobs, 42 example jobs, 125 harness tests, 719/719 source-LCNF cases, 9/9 direct-machine cases, 719/719 Wasm-V8 cases, 728 unique cases, 2166/2166 comparisons equal, 9097 machine steps, all 210 semantic-tag and 299 semantic-domain floors, zero findings, 205 active bug cards, 26 mailbox tests, validated Lean 4.33 source hashes and exactly one registered trusted axiom); PASS git diff --check
bug-cards: FIR-BUG-impure-elimDead-live-prefix-historical-target-heap (confirmed proof-coverage gap; negative regression landed)
blockers: none
handoff: ready; integrate functional head 730f808e and this containing status commit from proof/simpcase, rebased on exact main 8c939e5d, with no shared-contract change
next: create the source-only carrier at the original allocLeftGarbage step and transport it through same-target-frontier and paired-allocation results, allowing reset/reuse clients to consume provenance directly without the focused live-prefix producer
```
