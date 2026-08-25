# test-fixtures lane

```text
lane: test-fixtures
owner: test-fixtures
branch: validation/closure-ownership-fixtures
worktree: .worktrees/validation-closure-ownership-fixtures
state: ready
base: cf3f7cb88506d9a282a444e5757b0e48acc296ee on main
functional-head: 2b357bf9795e018534d47596e5ab66518d9a4e13
contract-base: cf3f7cb88506d9a282a444e5757b0e48acc296ee on main; S19 and its direct-self-tail, retained-non-tail, and mutual-tail recursion-shape family are accepted. S20 consumes the linked native/LCNF/V8 validation surface and changes no shared protocol, interpreter, runtime, proof, generation, concrete-layout, or artifact contract
clean-at-update: true
slice: S20/B3-A2 carries a runner-supplied ByteArray and repeated aliases through three alternating noinline mutual tail calls, retains an independent outside alias, and makes ownership errors observable with post-call copy-on-write mutation; exact 118-step and 100-form traces are required
files: Fir/Validation/Corpus.lean; validation-plans/coverage-index.json; validation-plans/semantic-fidelity-roadmap.md; coordination/lanes/test-fixtures.md
contracts: none. This fixture-only slice changes no interpreter, semantic-Wasm, proof, generator, concrete layout, runtime, ABI, artifact, result-schema, effect, or termination contract
checks: tracked Lean Beam update, sync, and save pass with zero diagnostics and save-ready source hash 09f0835253553c66; focused native/LCNF/V8 passes all 3 edges and opens both Wasm products under strace; git diff --check passes; make check passes both Lean build cones, 125 harness tests, 717 source cases, 2151 three-way results, 1434 products opened under strace, 726 unique cases, 2160 equal policy comparisons, 9077 aggregate machine steps (8917 source plus 160 direct), all 210 tag and 299 domain floors, 195 active bug-card validations, and 25 mailbox tests, with zero findings; make talos-setup pins Talos 0e05edbc; make talos-check passes 3172 jobs
bug-cards: none
blockers: none
handoff: integration may fast-forward the clean validation/closure-ownership-fixtures branch to admit S20 and its executable coverage ratchets; no contract queue or board edit is requested from this lane
next: after S20 lands, rebase on accepted main and select the smallest undominated memory-lifetime interaction, preferring an ownership-sensitive source-level application shape unless the shared source-error contract has become available
```
