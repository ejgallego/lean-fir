# test-fixtures lane

```text
lane: test-fixtures
owner: test-fixtures
branch: validation/closure-ownership-fixtures
worktree: .worktrees/validation-closure-ownership-fixtures
state: active
base: c9b80cd777a936e6d67f6ddc0766da3e81038364 on main
functional-head: none yet; planning seed only
contract-base: c9b80cd777a936e6d67f6ddc0766da3e81038364 on main; consumes the landed S2 closure-multiplicity matrix and changes no shared contract
clean-at-update: true
slice: S3a repeated-capture ByteArray topology: capture the same heap object in two closure slots, retain an independent outside alias, and compare a returned-alias path with a consuming/mutating path
files: validation-plans/semantic-fidelity-roadmap.md; coordination/lanes/test-fixtures.md; planned Fir/Validation/Corpus.lean, validation coverage/oracle ratchets, and docs/validation.md
contracts: none; fixture, trace, native-oracle, and coverage-policy changes only
checks: not-run; planning seed only
bug-cards: none
blockers: none; S3a reuses the linked ByteArray argument/result and set! external contracts and does not depend on the deferred effect-wrapper work
handoff: none; active fixture-only slice
next: compile the compact return-versus-consume pair, inspect exact final-LCNF traces, then admit its native/LCNF/V8 obligations and coverage domains
```
