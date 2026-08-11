# test-fixtures lane

```text
lane: test-fixtures
owner: test-fixtures
branch: validation/closure-ownership-fixtures
worktree: .worktrees/validation-closure-ownership-fixtures
state: active
base: be7eb51482235c2793f931a48d6dd3d65ff66f8a on main
functional-head: none yet; planning seed only
contract-base: be7eb51482235c2793f931a48d6dd3d65ff66f8a on main; consumes landed S3a repeated-capture topology and changes no shared contract
clean-at-update: true
slice: S3b repeated-capture ignore/read topology: compare dropping versus borrowing a repeated ByteArray capture, then repeat the same outside-alias shape for an internally constructed object and compare dropping versus projecting it
files: validation-plans/semantic-fidelity-roadmap.md; coordination/lanes/test-fixtures.md; planned Fir/Validation/Corpus.lean, validation coverage/oracle ratchets, and docs/validation.md
contracts: none; fixture, trace, native-oracle, and coverage-policy changes only
checks: not-run; planning seed only
bug-cards: none
blockers: none; both pairs reuse linked constructor, ByteArray, and scalar result surfaces and do not overlap W6, W7, or LCNF-proof ownership
handoff: none; active fixture-only slice
next: compile the two paired probes, inspect exact final-LCNF traces, then admit their native/LCNF/V8 obligations and coverage domains
```
