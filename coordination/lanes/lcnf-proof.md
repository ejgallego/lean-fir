# lcnf-proof lane

```text
lane: lcnf-proof
owner: lcnf-proof
branch: proof/simpcase
worktree: .worktrees/proof-simpcase
state: waiting
base: ae995ba8
functional-head: ae995ba8
contract-base: d392e194 requested
clean-at-update: true
slice: Preserve Alpha equivalence and pass correctness across takeClosureApplication
files: Fir/LeanIR/Passes/ and proof-owned examples or bug cards as required
contracts: consume CLOSURE-APPLICATION-OWNERSHIP without changing runtime semantics
checks: not-run for this milestone
bug-cards: none currently
blockers: integration must publish the stable contract-base commit on the milestone branch
handoff: none
next: Rebase from the published contract base, adapt AlphaEqvCode and dependent pass proofs, and report Beam plus dependency-cone checks
```
