# test-fixtures lane

```text
lane: test-fixtures
owner: test-fixtures
branch: validation/closure-ownership-fixtures
worktree: .worktrees/validation-closure-ownership-fixtures
state: ready
base: 473d5ec3f7ff590b4ac09a5befcf77920b952e7b on main
functional-head: f997949f01552a37fafc2a5d7c550e8f48cc0a4e
contract-base: 473d5ec3f7ff590b4ac09a5befcf77920b952e7b on main; consumes landed S3a repeated-capture topology and HitScene v2 artifact acceptance, and changes no shared contract
clean-at-update: true
slice: S3b repeated-capture ignore/read topology: four native-oracle fixtures compare dropping versus borrowing the same repeated ByteArray capture, then dropping versus projecting an allocated constructor containing a large Nat and nested String; every case retains an independent outside alias
files: Fir/Validation/Corpus.lean; docs/validation.md; validation-plans/coverage-index.json; validation-plans/native-oracle-attestations.json; validation-plans/semantic-fidelity-roadmap.md; coordination/lanes/test-fixtures.md
contracts: none; fixture, trace, native-oracle, and coverage-policy changes only
checks: Lean Beam update/sync/save for Fir/Validation/Corpus.lean (save-ready, zero diagnostics); lake --rehash build fir-native-oracle Fir.Validation (pass); focused four-case native/LCNF exact validation (8/8 results, 4/4 comparisons equal, zero findings); focused four-case native/LCNF/V8 validation (12/12 results, all three 4/4 edges equal, eight products opened with strace, zero findings); pre-rebase make check (pass); rebased onto main at 473d5ec3; post-rebase git diff --check (pass); post-rebase make check (pass: 645/645 source/native-LCNF, 9/9 direct machine, 645/645 native-LCNF-V8 with 1,290 products opened and 1,316 strace paths, 1,290 native-oracle witnesses, 654 unique cases, 1,944/1,944 aggregate comparisons, 6,184 interpreter steps, 98/98 tag floors, 209/209 domains, zero findings)
bug-cards: none
blockers: none; all four cases reuse linked constructor, String, ByteArray, and scalar result surfaces and do not overlap W6, W7, or LCNF-proof ownership
handoff: ready for integration from validation/closure-ownership-fixtures; integrate f997949f plus this containing mailbox commit by fast-forward after resolving the branch head
next: integration owner takes the S3b lease, fast-forwards main, closes the lease, then the fixture lane starts S4/B1 tail-call ownership from the landed alias vocabulary
```
