# test-fixtures lane

```text
lane: test-fixtures
owner: test-fixtures
branch: validation/closure-ownership-fixtures
worktree: .worktrees/validation-closure-ownership-fixtures
state: active
base: d6599de83a000ebdc6e32804190e41cf79c25f36 on main
functional-head: ef8823fdc6cc268468447210a4c460146a4db865
contract-base: d6599de83a000ebdc6e32804190e41cf79c25f36 on main; consumes the landed S4 transfer/reuse baseline, W6 external-evidence checkpoint, and existing direct recursive-release/native-IR attestations; changes no shared contract
clean-at-update: true
slice: S5a recursive release/reuse complete: compiler-generated unique owner release recursively decrements a retained leaf to the reuse path, paired with an outside child alias that stops recursion and forces the later leaf update to allocate while preserving the original leaf
files: Fir/Validation/Corpus.lean; docs/validation.md; validation-plans/coverage-index.json; validation-plans/native-oracle-attestations.json; validation-plans/semantic-fidelity-roadmap.md; coordination/lanes/test-fixtures.md
contracts: none; fixture, trace, native-oracle, and coverage-policy changes only
checks: pre-rebase Lean Beam update/sync/save Fir/Validation/Corpus.lean PASS with zero diagnostics; lake --rehash build fir-native-oracle Fir.Validation PASS; focused native-lcnf two-case matrix PASS 2/2 equal; focused native-lcnf-v8 two-case matrix PASS all six edges with all four provider products opened; git diff --check PASS; pre-rebase make check PASS including lake dependency cones, 122 harness tests, 649/649 native-lcnf, nine direct-machine cases, 649/649 native-v8 and lcnf-v8, 1,298 native comparison witnesses, coverage-index generation/verification at 658 unique cases, 1,307 tier cases, 1,956 equal comparisons, 6,563 interpreter steps, 116 tag floors, 221 semantic domains, zero findings/obligation/telemetry failures, bug-card validation, trusted-assumption validation, and no-placeholders; rebased cleanly on d6599de8 with post-rebase gate pending
bug-cards: none
blockers: integration lease ELIMDEAD-GENERIC-MAPPED-OWNER-READINESS is active under lcnf-proof; do not compete for main; the existing direct native-IR recorder remains unchanged and anchors the native recursive-release facts
handoff: none while the proof integration lease is active; fixture candidate is queued cleanly behind it
next: after the proof lease lands/releases, rebase on the new main, rerun the complete post-rebase gate, publish a refreshed ready mailbox, and integrate S5a promptly
```
