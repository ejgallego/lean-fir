# test-fixtures lane

```text
lane: test-fixtures
owner: test-fixtures
branch: validation/closure-ownership-fixtures
worktree: .worktrees/validation-closure-ownership-fixtures
state: ready
base: 5dfa5778abce04e0108052c79fc3be44e38d7019 on main
functional-head: 865006bf93afeb96de273b1ee09ff2b396b67bf6
contract-base: 5dfa5778abce04e0108052c79fc3be44e38d7019 on main; consumes the landed S5a recursive-release pair and existing direct repeated-alias/native-IR attestation; changes no shared contract
clean-at-update: true
slice: S5b coverage-guided repeated-child release: compare consuming a unique owner with the same leaf in two slots against retaining that owner so release stops before both slots; an outside leaf alias and subsequent update expose reuse versus allocation
files: Fir/Validation/Corpus.lean; validation-plans/semantic-fidelity-roadmap.md; validation-plans/coverage-index.json; validation-plans/native-oracle-attestations.json; docs/validation.md; coordination/lanes/test-fixtures.md
contracts: none; fixture, trace, coverage-search documentation, native-oracle floor, and coverage-policy changes only
checks: PASS lean-beam update/sync/save Fir/Validation/Corpus.lean with zero diagnostics; PASS lake --rehash build fir-native-oracle Fir.Validation; PASS focused native-lcnf probe and pinned replay 2/2; PASS focused native-lcnf-v8 triangle 6/6 with both bundles opened under strace; PASS git diff --check; PASS make check, including 122 harness tests, 651/651 source native-lcnf cases, 9/9 direct machines, 651/651 native-lcnf-v8 triangles, 1,302 native-oracle witnesses, 1,962/1,962 indexed comparisons, 6,689 interpreter steps, 122/122 tag floors, and 227/227 semantic domains; findings 0
bug-cards: none
blockers: none; source-level repeated fields and outside aliases need no compiler, proof, W6, or W7 change
handoff: ready for integration owner; base 5dfa5778abce04e0108052c79fc3be44e38d7019, functional head 865006bf93afeb96de273b1ee09ff2b396b67bf6, lane test-fixtures, contract base 5dfa5778abce04e0108052c79fc3be44e38d7019, clean before this mailbox update
next: integrate S5b promptly, then use the documented coverage-guided narrowing model to select the smallest undominated retained-capacity or grow/delete ownership pair
```
