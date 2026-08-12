# test-fixtures lane

```text
lane: test-fixtures
owner: test-fixtures
branch: validation/closure-ownership-fixtures
worktree: .worktrees/validation-closure-ownership-fixtures
state: active
base: ad3bea7365c3ae9fde1899c8e2d655a18530bea7 on main
functional-head: pending
contract-base: ad3bea7365c3ae9fde1899c8e2d655a18530bea7 on main; consumes only accepted aggregate, erased-field, closure-application, and ByteArray runtime surfaces; does not consume or duplicate the active argument-alias, effectful-native-oracle, IO-error, exception, or source-stream contracts
clean-at-update: true
slice: S8/E1 aggregate erasure: project a nested ByteArray through a proof-bearing aggregate into a closure, then compare releasing the aggregate before final application with retaining it across application
files: coordination/lanes/test-fixtures.md initially; planned fixture-only edits to Fir/Validation/Corpus.lean, validation plans, and validation documentation
contracts: none expected; fixture-only; active argument-alias, effectful-native-oracle, IO/error, exception, and source-stream contracts remain fenced
checks: pending
bug-cards: none
blockers: none
handoff: not ready; active design/probe phase
next: admit only a pair whose final-LCNF and executed traces prove erased-field layout, aggregate construction, nested case/projection, release distinction, closure application, and ByteArray mutation all executed
```
