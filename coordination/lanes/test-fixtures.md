# test-fixtures lane

```text
lane: test-fixtures
owner: test-fixtures
branch: validation/closure-ownership-fixtures
worktree: .worktrees/validation-closure-ownership-fixtures
state: active
base: d6a77d9d53d9f651ce712f8b4f84d8a532a17093 on main
functional-head: none yet; planning seed only
contract-base: d6a77d9d53d9f651ce712f8b4f84d8a532a17093 on main; consumes landed S3 capture topology and W7 tail-call generation support, and changes no shared contract
clean-at-update: true
slice: S4/B1 tail-call ownership bridge: compare three tail-recursive updates of a uniquely transferred nested ByteArray owner with the same worker called while an independent alias to the original owner survives
files: validation-plans/semantic-fidelity-roadmap.md; coordination/lanes/test-fixtures.md; planned Fir/Validation/Corpus.lean, validation coverage/oracle ratchets, and docs/validation.md
contracts: none; fixture, trace, native-oracle, and coverage-policy changes only
checks: not-run; planning seed only
bug-cards: none
blockers: none; the semantic pair reuses linked constructor, String, ByteArray, recursion, and result surfaces; W7's separate large-depth transform claim remains outside this fixture slice
handoff: none; active fixture-only slice
next: compile the paired nested-owner worker, inspect unique/shared exact final-LCNF paths, and admit only if native Lean, LCNF, and real V8 agree
```
