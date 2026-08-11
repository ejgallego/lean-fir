# test-fixtures lane

```text
lane: test-fixtures
owner: test-fixtures
branch: validation/closure-ownership-fixtures
worktree: .worktrees/validation-closure-ownership-fixtures
state: active
base: e206463119e98dc48a2a60e11f6ac9173beec686 on main
functional-head: none yet; S5 planning seed only
contract-base: e206463119e98dc48a2a60e11f6ac9173beec686 on main; consumes the landed S4 transfer/reuse baseline and existing direct recursive-release/native-IR attestations; changes no shared contract
clean-at-update: true
slice: S5a recursive release/reuse: compare replacing a nested owner whose retained leaf becomes exclusive after recursive child release with the same replacement while an outside child alias stops recursion and forces the later leaf update to allocate
files: validation-plans/semantic-fidelity-roadmap.md; coordination/lanes/test-fixtures.md; planned Fir/Validation/Corpus.lean, validation coverage/oracle ratchets, and docs/validation.md
contracts: none; fixture, trace, native-oracle, and coverage-policy changes only
checks: not-run; planning seed only
bug-cards: none
blockers: none; source constructors, erased fields, nested results, and ownership forms are already linked; the direct native-IR recorder remains unchanged
handoff: none; active fixture-only slice
next: compile the paired owner replacement and leaf update, then admit exact obligations only if native Lean, LCNF, and real V8 agree
```
