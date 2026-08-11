# test-fixtures lane

```text
lane: test-fixtures
owner: test-fixtures
branch: validation/closure-ownership-fixtures
worktree: .worktrees/validation-closure-ownership-fixtures
state: active
base: 5d4a9b3dc1f0c539c7f2088d9f92ac85bf47c632 on main
functional-head: none yet; S5c planning seed only
contract-base: 5d4a9b3dc1f0c539c7f2088d9f92ac85bf47c632 on main; consumes the landed S5a/S5b release fixtures and existing one-step grow/delete signatures; changes no shared contract
clean-at-update: true
slice: S5c coverage-guided grow/delete release: compare consuming a unique one-field leaf owner while growing to two scalar fields against retaining the original owner so release stops before its leaf; a surviving leaf alias and later update expose reuse versus allocation
files: validation-plans/semantic-fidelity-roadmap.md; coordination/lanes/test-fixtures.md; planned Fir/Validation/Corpus.lean, validation coverage/oracle ratchets, and docs/validation.md
contracts: none; fixture, exact-trace, coverage-search documentation, native-oracle floor, and coverage-policy changes only
checks: not-run; planning seed only
bug-cards: none
blockers: none; the candidate uses the landed source compiler, existing constructor/reset/reuse protocol, final LCNF telemetry, and current V8 provider
handoff: none; active fixture-only slice
next: probe the compact grow/delete release pair against native Lean and discard it if its signatures are dominated by the one-step grow/delete or same-size release cases
```
