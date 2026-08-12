# test-fixtures lane

```text
lane: test-fixtures
owner: test-fixtures
branch: validation/closure-ownership-fixtures
worktree: .worktrees/validation-closure-ownership-fixtures
state: active
base: 8051df3c7430df5688035973635e66b058bff502 on main
functional-head: none yet
contract-base: 8051df3c7430df5688035973635e66b058bff502 on main; consumes only the linked closure-application and ByteArray runtime surfaces; does not consume or duplicate the active argument-alias, effectful-native-oracle, IO-error, exception, or source-stream contracts
clean-at-update: true
slice: S7 escaping closure ownership: return a ByteArray-capturing closure from a noinline maker, then distinguish unique final mutation from retained-outside-alias copy-on-write after the return boundary
files: validation-plans/semantic-fidelity-roadmap.md; coordination/lanes/test-fixtures.md; planned Fir/Validation/Corpus.lean, validation coverage plans, and docs/validation.md
contracts: none; fixture-only; active argument-alias and IO/error contracts remain fenced
checks: pending candidate compilation and dominance filter
bug-cards: none
blockers: none for this candidate; reject it if compiler normalization removes the returned-closure boundary or its path signature is dominated by an existing case
handoff: none; active fixture design
next: compile the smallest unique/shared returned-closure pair, inspect exact final-LCNF and executed signatures, then admit it only if the boundary remains observable
```
