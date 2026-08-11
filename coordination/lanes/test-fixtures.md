# test-fixtures lane

```text
lane: test-fixtures
owner: test-fixtures
branch: validation/closure-ownership-fixtures
worktree: .worktrees/validation-closure-ownership-fixtures
state: released
base: 348977fea0f44694200e2a2c141ce80a7c377baf on main
functional-head: b5080fe342a9b462ca7f3e385a5bd600d9dc4abe
contract-base: 348977fea0f44694200e2a2c141ce80a7c377baf on main; consumes the landed S2 closure-multiplicity matrix and W6 unified-control-relation checkpoint, and changes no shared contract
clean-at-update: true
slice: S3a repeated-capture ByteArray topology: capture the same heap object in two closure slots, retain an independent outside alias, and compare a returned-alias path with a consuming/mutating path
files: Fir/Validation/Corpus.lean; validation-plans/coverage-index.json; validation-plans/native-oracle-attestations.json; validation-plans/semantic-fidelity-roadmap.md; docs/validation.md
contracts: none; fixture, trace, native-oracle, and coverage-policy changes only
checks: PASS after rebase on base 348977fe and exact coordination candidate 822cc248: Lean Beam update/sync/save Fir/Validation/Corpus.lean with zero diagnostics and save-ready; lake --rehash build fir-native-oracle Fir.Validation; focused native/LCNF exact-obligation validation 2/2 equal; focused native/LCNF/real-V8 triangle 6/6 equal; git diff --check main...HEAD; complete make check with both Lean build cones, 122 harness tests, 650 unique cases, 641/641 native-LCNF cases, 9/9 direct-machine cases, 641/641 native-LCNF-V8 cases, native-oracle policy accepting both required edges with 1282 witnesses, 1932/1932 aggregate comparisons equal, 6050 machine steps, 96/96 tag floors, 201/201 semantic domains, findings 0
bug-cards: none
blockers: none; S3a reuses the linked ByteArray argument/result and set! external contracts and does not depend on the deferred effect-wrapper work; an initial direct-call probe was strengthened with a noinline closure consumer before any coverage claim or commit
handoff: accepted under milestone VALIDATION-CAPTURE-TOPOLOGY-S3A; main lands functional head b5080fe342a9b462ca7f3e385a5bd600d9dc4abe and its containing coordination completion commit directly from base 348977fe; no W6, W7, LCNF-proof, or shared-contract file changes
next: after S3a integration, add an ignore/read repeated-capture pair and one constructor or String representative before moving to S4 tail ownership
```
