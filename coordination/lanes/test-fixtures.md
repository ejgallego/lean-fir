# test-fixtures lane

```text
lane: test-fixtures
owner: test-fixtures
branch: validation/closure-ownership-fixtures
worktree: .worktrees/validation-closure-ownership-fixtures
state: ready
base: d113b5501b92cd532f6cab7ddef5ddea906c7e13 on main
functional-head: 322fa030867484c4c9e06bd02b74e72f8df560ad, S18 retained-owner non-tail unwind fixture, exact telemetry, coverage policy, and roadmap
contract-base: d113b5501b92cd532f6cab7ddef5ddea906c7e13 on main; consumes the accepted cache/persistence semantics, repeated cached String child vocabulary, S17 self-tail ownership baseline, non-tail LCNF recursion, recursive release, copy-on-write append, and real-V8 surface; changes no shared protocol, interpreter, runtime, proof, generation, concrete-layout, or artifact contract
clean-at-update: true
slice: S18 non-tail ownership fidelity: retain every repeated-child loop owner across its recursive call, reconcile the returned String with the older owner during unwind, and compare the resulting allocation/release trace with S17's self-tail transfer while preserving the same outside alias, append, and cache reread
files: Fir/Validation/Corpus.lean; validation-plans/coverage-index.json; validation-plans/semantic-fidelity-roadmap.md; coordination/lanes/test-fixtures.md
contracts: none. S18 is fixture, observation, exact telemetry, and coverage-policy work only; it does not change non-tail lowering, recursive release, interpreter, semantic-Wasm, W6/W7, proof, generator, concrete layout, or artifact contracts
checks: accepted S17 baseline is green on main d113b550. Tracked Lean Beam update, sync, and save on Fir/Validation/Corpus.lean pass with zero diagnostics, save-ready, and source hash 54e9d3437b8ef183. Focused S17/S18 native/LCNF/V8 validation passes all 6/6 comparisons with zero findings and opens all 4/4 Wasm products under strace. Fresh make check passes tooling 21 tests, core build 22 jobs, examples 42 jobs, scalar surface 163/163, harness 125 tests, source native/LCNF 715/715 equal, direct machines 9/9 equal, V8 three-way 2145/2145 results equal with 1430/1430 products opened under strace, 1430 native witnesses accepted and verified, coverage 724 unique cases with 2154/2154 policy comparisons equal and 8777 aggregate machine steps (8617 source plus 160 direct), all 200 tag and 295 domain floors satisfied, zero findings. make talos-setup passes at Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254 and make talos-check passes 3172 jobs; git diff --check passes
bug-cards: none
blockers: none
handoff: integration may land the two-commit S18 test-fixtures stack from base d113b550 through the containing ready mailbox commit; the boundary is fixture-only and independently useful
next: after S18 integration, prototype the remaining B3 recursion-shape point as a mutual-recursion counterpart with the same cached repeated-child observation, retaining it only if its exact ownership telemetry is distinct
```
