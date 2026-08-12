# test-fixtures lane

```text
lane: test-fixtures
owner: test-fixtures
branch: validation/closure-ownership-fixtures
worktree: .worktrees/validation-closure-ownership-fixtures
state: released
base: d286e41a4d4712311628cdc197588f999455613f on main
functional-head: d695bd66a171264d5091337e76a5bf7386c622b7
contract-base: d286e41a4d4712311628cdc197588f999455613f on main; consumes only the linked closure-application and ByteArray runtime surfaces; does not consume or duplicate the active argument-alias, effectful-native-oracle, IO-error, exception, or source-stream contracts
clean-at-update: true
slice: S7 escaping closure ownership: return a ByteArray-capturing closure from a noinline maker, then distinguish unique final mutation from retained-outside-alias copy-on-write after the return boundary
files: Fir/Validation/Corpus.lean; validation-plans/semantic-fidelity-roadmap.md; validation-plans/coverage-index.json; validation-plans/native-oracle-attestations.json; docs/validation.md; coordination/lanes/test-fixtures.md
contracts: none; fixture-only; active argument-alias and IO/error contracts remain fenced
checks: PASS post-rebase Lean Beam refresh/save Fir/Validation/Corpus.lean at version 1 with zero diagnostics and source hash 415ae70e6d916bfe; PASS lake build fir-native-oracle Fir.Validation; PASS focused pinned native/LCNF replay 2/2; PASS focused native/LCNF/V8 triangle 6/6 with 4/4 unique products opened under strace; PASS git diff --check; PASS complete post-rebase make check including 122 harness tests, 657/657 source native/LCNF cases, 9/9 direct machines, 657/657 native/LCNF/V8 triangles, 1,314 native-oracle witnesses, 1,980/1,980 indexed comparisons, 6,978 interpreter steps, 138/138 tag floors, and 245/245 semantic domains; findings 0; PASS 145 bug cards and exactly one registered trusted axiom
bug-cards: none
blockers: none; the first bare-function candidate was rejected because eta-normalization removed the return boundary, while the admitted single-field wrapper retains a distinct exact path
handoff: accepted on main through ready head 1cfcb9b8; functional head d695bd66, base and contract base d286e41a, lane test-fixtures; this released mailbox is carried by the integration acceptance record
next: retain S7 as the returned-closure ownership baseline; select the smallest undominated E1 aggregate/erasure pair or another fixture-only memory interaction without consuming active shared contracts
```
