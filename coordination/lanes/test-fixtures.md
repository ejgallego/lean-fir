# test-fixtures lane

```text
lane: test-fixtures
owner: test-fixtures
branch: validation/closure-ownership-fixtures
worktree: .worktrees/validation-closure-ownership-fixtures
state: ready
base: 9f53aca11e400f1cb9b6a6f5c54cac913e3aa8ce on main
functional-head: 0a91e283256f3ab186d135216cac4ab79f7452ff, S17 cached ownership through self-tail state fixture, exact telemetry, coverage policy, and roadmap
contract-base: 9f53aca11e400f1cb9b6a6f5c54cac913e3aa8ce on main; consumes the accepted cache/persistence semantics, repeated cached String child vocabulary, self-tail LCNF lowering, recursive release, copy-on-write append, and real-V8 surface; changes no shared protocol, interpreter, runtime, proof, generation, concrete-layout, or artifact contract
clean-at-update: true
slice: S17 tail-position ownership fidelity: compare zero and repeated self-tail transfers of a cached repeated-child String survivor while sibling aliases and loop-carried aggregate owners are released; retain an independent outside alias, append through the returned survivor, and reread the cache
files: Fir/Validation/Corpus.lean; validation-plans/coverage-index.json; validation-plans/semantic-fidelity-roadmap.md; coordination/lanes/test-fixtures.md
contracts: none. S17 is fixture, observation, exact telemetry, and coverage-policy work only; it does not change self-tail lowering, recursive release, interpreter, semantic-Wasm, W6/W7, proof, generator, concrete layout, or artifact contracts
checks: branch rebased cleanly on current main; W7 operational mailbox confirms E3e landed. Detached dominance probe and tracked Lean Beam update/sync/save on Fir/Validation/Corpus.lean pass with zero diagnostics and save-ready source hash 9173269b88c3b0c2. Detached and tracked focused native/LCNF/V8 runs pass all 6/6 comparisons with zero findings and 4/4 products opened under strace. Zero-tail executes exactly 92 interpreter steps with oset=0 and Nat.sub=0; three-tail executes exactly 183 steps with oset=6, sset=4, oproj=12, sproj=4, dec=6, and isShared=4. Clean lean-beam shutdown then make clean and make check pass: tooling 21 tests, core build 22 jobs, examples 42 jobs, scalar surface 163/163, harness 125 tests, source native/LCNF 714/714 equal, direct machines 9/9 equal, V8 three-way 2142/2142 results equal with 1428/1428 products opened under strace, 1428 native witnesses accepted and verified, coverage 723 unique cases with 2151/2151 policy comparisons equal and 8565 machine steps, all 192 tag and 289 domain floors satisfied, zero findings; make talos-setup passes at Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254; make talos-check passes 3172 jobs; git diff --check and mailbox protocol validation pass
bug-cards: none
blockers: none
handoff: integration may land the two-commit S17 test-fixtures stack through the containing ready mailbox commit; the boundary is fixture-only and independently useful
next: after integration, schedule S18 non-tail ownership fidelity: retain each repeated-child loop owner across its recursive call and compare unwind-time release against S17's tail transfer, preserving the same outside alias and cache reread
```
