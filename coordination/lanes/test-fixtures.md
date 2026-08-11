# test-fixtures lane

```text
lane: test-fixtures
owner: test-fixtures
branch: validation/closure-ownership-fixtures
worktree: .worktrees/validation-closure-ownership-fixtures
state: ready
base: d1bb3b55dce9bb6c5efc2793af4abedaa51934ef on main
functional-head: 101ecd8de371d9dbe36d5e8ea5df9c90ca7a80ea
contract-base: d1bb3b55dce9bb6c5efc2793af4abedaa51934ef on main; consumes the landed S4 transfer/reuse baseline, W6 external-evidence checkpoint, accepted mapped-owner proof slice, and existing direct recursive-release/native-IR attestations; changes no shared contract
clean-at-update: true
slice: S5a recursive release/reuse complete: compiler-generated unique owner release recursively decrements a retained leaf to the reuse path, paired with an outside child alias that stops recursion and forces the later leaf update to allocate while preserving the original leaf
files: Fir/Validation/Corpus.lean; docs/validation.md; validation-plans/coverage-index.json; validation-plans/native-oracle-attestations.json; validation-plans/semantic-fidelity-roadmap.md; coordination/lanes/test-fixtures.md
contracts: none; fixture, trace, native-oracle, and coverage-policy changes only
checks: Lean Beam update/sync/save Fir/Validation/Corpus.lean PASS with zero diagnostics; lake --rehash build fir-native-oracle Fir.Validation PASS; focused native-lcnf two-case matrix PASS 2/2 equal; focused native-lcnf-v8 two-case matrix PASS all six edges with all four provider products opened; clean rebase on accepted proof head d1bb3b55; git diff --check PASS; complete post-rebase make check PASS including lake dependency cones, 122 harness tests, 649/649 native-lcnf, nine direct-machine cases, 649/649 native-v8 and lcnf-v8, 1,298 native comparison witnesses, coverage-index generation/verification at 658 unique cases, 1,307 tier cases, 1,956 equal comparisons, 6,563 interpreter steps, 116 tag floors, 221 semantic domains, zero findings/obligation/telemetry failures, bug-card validation, trusted-assumption validation, and no-placeholders
bug-cards: none
blockers: none; the mapped-owner proof lease is released and the existing direct native-IR recorder remains unchanged as the native recursive-release fact anchor
handoff: base d1bb3b55dce9bb6c5efc2793af4abedaa51934ef; functional head 101ecd8de371d9dbe36d5e8ea5df9c90ca7a80ea; ready for integration by fast-forward after resolving this mailbox's containing commit from validation/closure-ownership-fixtures
next: integrate S5a promptly; then keep S5 active with the next compact repeated-child-alias/release-order pair rather than expanding scalar coverage
```
