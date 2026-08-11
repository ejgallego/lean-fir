# test-fixtures lane

```text
lane: test-fixtures
owner: test-fixtures
branch: validation/closure-ownership-fixtures
worktree: .worktrees/validation-closure-ownership-fixtures
state: active
base: d271499113d754d1fa4409a33a3504c2541b1ae0 on main
functional-head: none; S2 fixture code is not yet committed
contract-base: d271499113d754d1fa4409a33a3504c2541b1ae0 on main; consumes the landed semantic-fidelity baseline and changes no shared contract
clean-at-update: true
slice: S2 closure-use multiplicity: extend the mixed captured closure from one/two uses to zero/three uses, distinguish shared intermediate applications from the unique final application, and pin exact ownership-sensitive final-LCNF evidence
files: Fir/Validation/Corpus.lean; validation-plans/coverage-index.json; validation-plans/native-oracle-attestations.json; docs/validation.md
contracts: none; fixture, trace, native-oracle, and coverage-policy changes only
checks: not-run
bug-cards: none
blockers: none; retain the zero-use source case only if a real closure allocation survives final LCNF, otherwise cover that state in the direct-machine tier
handoff: none; S2 is active
next: elaborate the zero-use and three-use source cases, inspect final LCNF, then admit only the surviving high-signal cases with exact traces and atomic coverage ratchets
```
