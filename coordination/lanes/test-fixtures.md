# test-fixtures lane

```text
lane: test-fixtures
owner: test-fixtures
branch: validation/closure-ownership-fixtures
worktree: .worktrees/validation-closure-ownership-fixtures
state: active
base: d113b5501b92cd532f6cab7ddef5ddea906c7e13 on main
functional-head: 49a39129c3dd49ccf7a0fc6aefbf83fa43f61c3a, accepted S17 predecessor; S18 has not yet published a tracked functional commit
contract-base: d113b5501b92cd532f6cab7ddef5ddea906c7e13 on main; consumes the accepted cache/persistence semantics, repeated cached String child vocabulary, S17 self-tail ownership baseline, non-tail LCNF recursion, recursive release, copy-on-write append, and real-V8 surface; changes no shared protocol, interpreter, runtime, proof, generation, concrete-layout, or artifact contract
clean-at-update: true
slice: S18 non-tail ownership fidelity: retain every repeated-child loop owner across its recursive call, reconcile the returned String with the older owner during unwind, and compare the resulting allocation/release trace with S17's self-tail transfer while preserving the same outside alias, append, and cache reread
files: Fir/Validation/Corpus.lean; validation-plans/coverage-index.json; validation-plans/semantic-fidelity-roadmap.md; coordination/lanes/test-fixtures.md
contracts: none. S18 is fixture, observation, exact telemetry, and coverage-policy work only; it does not change non-tail lowering, recursive release, interpreter, semantic-Wasm, W6/W7, proof, generator, concrete layout, or artifact contracts
checks: accepted S17 baseline is green on main d113b550. Detached S18 dominance candidate passes strict native/LCNF and native/LCNF/V8 probes with zero findings and both Wasm products opened under strace; clean candidate make check passes 715 source cases, 2145 three-way results, 1430 products opened under strace, 8617 source-machine steps, all 200 tag and 295 conjunctive-domain floors, and zero findings; candidate make talos-check passes 3178 jobs. Tracked promotion gates not yet run
bug-cards: none
blockers: none
handoff: none while S18 is active
next: promote the detached S18 candidate onto the tracked branch, refresh it through Lean Beam, run the focused S17/S18 differential cone, and then run the full validation and Talos gates
```
