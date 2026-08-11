# test-fixtures lane

```text
lane: test-fixtures
owner: test-fixtures
branch: validation/closure-ownership-fixtures
worktree: .worktrees/validation-closure-ownership-fixtures
state: released
base: 43a5c14e23b227f8ff54d874d9f6b24ec3d65119 on main
functional-head: 072e90d73288ccde574cf93766643af4ab0ea121
contract-base: 43a5c14e23b227f8ff54d874d9f6b24ec3d65119 on main; consumes the landed S5a/S5b release fixtures, existing one-step grow/delete signatures, and accepted proof-only W6 pointwise resource stack; changes no shared contract
clean-at-update: true
slice: S5c coverage-guided grow/delete release: compare consuming a unique two-field seed/leaf owner while growing to three scalar fields against retaining the original owner so release stops before its leaf; a surviving leaf alias and later update expose reuse versus allocation
files: Fir/Validation/Corpus.lean; validation-plans/semantic-fidelity-roadmap.md; validation-plans/coverage-index.json; validation-plans/native-oracle-attestations.json; docs/validation.md; coordination/lanes/test-fixtures.md
contracts: none; fixture, exact-trace, coverage-search documentation, native-oracle floor, and coverage-policy changes only
checks: PASS lean-beam update/sync/save Fir/Validation/Corpus.lean at version 7 with zero diagnostics and source hash 89f3b2b8603ee5ba; PASS lake --rehash build fir-native-oracle Fir.Validation; PASS focused native-lcnf probe and exact pinned replay 2/2; PASS focused native-lcnf-v8 triangle 6/6 with 4/4 unique products opened under strace; PASS git diff --check; PASS complete make check before and after rebasing on 43a5c14e, including 122 harness tests, 653/653 source native-lcnf cases, 9/9 direct machines, 653/653 native-lcnf-v8 triangles, 1,306 native-oracle witnesses, 1,968/1,968 indexed comparisons, 6,829 interpreter steps, 124/124 tag floors, and 233/233 semantic domains; findings 0; PASS 129 bug cards and exactly one registered trusted axiom
bug-cards: none
blockers: none; the candidate uses the landed source compiler, existing constructor/reset/reuse protocol, final LCNF telemetry, and current V8 provider
handoff: accepted on main through 0deba7156e67d42632b4cdcfff56ce02ab7ea128; base and contract base 43a5c14e23b227f8ff54d874d9f6b24ec3d65119, functional head 072e90d73288ccde574cf93766643af4ab0ea121, lane test-fixtures
next: after the integration checkpoint is pushed, select the smallest undominated memory-lifetime interaction outside the covered replacement/release matrix; keep native Lean as the admission oracle
```
