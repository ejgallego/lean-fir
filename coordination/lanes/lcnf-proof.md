# lcnf-proof lane

```text
lane: lcnf-proof
owner: lcnf-proof
branch: proof/simpcase
worktree: .worktrees/proof-simpcase
state: ready
base: 44c764f0ee0af5915fe9a5f0873ed51a562057b2 on main
functional-head: 69947186303ba5697bb798ef449a3160afef9459
contract-base: 44c764f0ee0af5915fe9a5f0873ed51a562057b2; accepted Lean 4.34.1 source/target runtime and allocation-ledger contract, unchanged by this proof replay
clean-at-update: true
slice: ELIMDEAD-DELETED-RESET-SOURCE-ONLY: a semantic deleted-let step preserves an existing allocated source-only location when the target stutters and the source frontier is monotone; the full deleted-reset dispatcher now obtains the required post-runtime relation and frontier fact from reset readiness, including the runtime-neutral branch
files: Fir/LeanIR/Passes/ElimDeadMachineRel.lean; coordination/lanes/lcnf-proof.md
contracts: none; proof-owned theorem additions only, with no runtime, interpreter, pass, W6/W7, or shared semantic change
checks: PASS Lean Beam update/sync/save Fir/LeanIR/Passes/ElimDeadMachineRel.lean on 44c764f0e (0 errors, 235 existing warnings, source hash 9a84bf042593e729); PASS lake build +Fir.LeanIR.Passes.ElimDeadMachineRel +Fir.LeanIR.Passes.ElimDeadExamples; PASS make check; PASS git diff --check; git range-diff confirms the proof commit is patch-identical to original 9602e8863
bug-cards: none new; the historical-target-heap live-prefix limitation remains recorded and its negative regression stays green
blockers: none
handoff: ready for root integration at the clean containing proof/simpcase checkpoint; the refreshed proof commit is 699471863 and the branch descends directly from exact main 44c764f0e; original checkpoint 54ba62f5c remains reachable from untouched proof/deleted-reuse
next: root lands this refreshed reset checkpoint; the separately pinned deleted-reuse successor then needs rebasing before integration, followed by dispatcher/strong-simulation work
```
