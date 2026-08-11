# test-fixtures lane

```text
lane: test-fixtures
owner: test-fixtures
branch: validation/closure-ownership-fixtures
worktree: .worktrees/validation-closure-ownership-fixtures
state: released
base: 2d96f7a19d16d0fa915cf8a0823abfa249a690ce on main
functional-head: 0fec2b0f1759224c811e024489604edfcd9c04cd
contract-base: 2d96f7a19d16d0fa915cf8a0823abfa249a690ce on main; consumes the landed semantic-fidelity baseline and W6 canonical structured-entry proof checkpoint, and changes no shared contract
clean-at-update: true
slice: S2 closure-use multiplicity: extend the mixed captured closure from one/two uses to zero/three uses, distinguish shared intermediate applications from the unique final application, and pin exact ownership-sensitive final-LCNF evidence
files: Fir/Validation/Corpus.lean; validation-plans/coverage-index.json; validation-plans/native-oracle-attestations.json; validation-plans/semantic-fidelity-roadmap.md; docs/validation.md
contracts: none; fixture, trace, native-oracle, and coverage-policy changes only
checks: PASS on base 2d96f7a1 and exact integration lease candidate 9b16ee55: Lean Beam 0.2.0-beta update/sync/save Fir/Validation/Corpus.lean zero diagnostics and save-ready; lake --rehash build fir-native-oracle Fir.Validation rebuilt the exact importer cone after the final tag edit; focused native/LCNF exact-obligation validation 2/2 equal and focused native/LCNF/real-V8 triangle 6/6 equal; git diff --check; complete make check with 122 harness tests, 648 unique cases, 639/639 native-LCNF cases, 9/9 direct-machine cases, 639/639 native-LCNF-V8 cases, native-oracle policy accepted both required edges with 1278 witnesses, 1926/1926 aggregate comparisons equal, 6001 machine steps, 88/88 tag floors, 193/193 semantic domains, findings 0
bug-cards: none
blockers: none; the zero-use source case retains four boxes and a real pap in final LCNF, so no direct-machine fallback is needed
handoff: accepted under milestone VALIDATION-CLOSURE-MULTIPLICITY-S2; main lands functional head 0fec2b0f1759224c811e024489604edfcd9c04cd and its containing coordination completion commit directly from base 2d96f7a1; no W6, W7, LCNF-proof, or shared-contract file changes
next: execute S3 capture alias topology with repeated captures, an independent outside alias, and action-sensitive ignore/read/return/consume pairs
```
