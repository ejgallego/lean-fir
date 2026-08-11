# test-fixtures lane

```text
lane: test-fixtures
owner: test-fixtures
branch: validation/closure-ownership-fixtures
worktree: .worktrees/validation-closure-ownership-fixtures
state: active
base: 5dfa5778abce04e0108052c79fc3be44e38d7019 on main
functional-head: none yet; S5b planning seed only
contract-base: 5dfa5778abce04e0108052c79fc3be44e38d7019 on main; consumes the landed S5a recursive-release pair and existing direct repeated-alias/native-IR attestation; changes no shared contract
clean-at-update: true
slice: S5b coverage-guided repeated-child release: compare consuming a unique owner with the same leaf in two slots against retaining that owner so release stops before both slots; an outside leaf alias and subsequent update expose reuse versus allocation
files: validation-plans/semantic-fidelity-roadmap.md; coordination/lanes/test-fixtures.md; planned Fir/Validation/Corpus.lean, validation coverage/oracle ratchets, and docs/validation.md
contracts: none; fixture, trace, coverage-search documentation, native-oracle floor, and coverage-policy changes only
checks: not-run; planning seed only
bug-cards: none
blockers: none; source-level repeated fields and outside aliases need no compiler, proof, W6, or W7 change
handoff: none; active fixture-only slice
next: implement the compact repeated-child pair, probe native versus final LCNF, and retain only distinct path signatures before exact admission
```
