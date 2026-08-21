# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 818a1be1, the rebased W7 proof-visible impure-hygiene contract on accepted main 66aa9281
functional-head: 1d44bfe5
contract-base: 818a1be1. W6 consumes the strengthened supportedDecl conjunction and globally fresh abiCaseProgram binders without changing the shared hygiene invariant, executable admission check, ABI, layout, runtime, or generated behavior for valid compiler LCNF
clean-at-update: true
slice: Adapted all W6 Talos consumers to proof-visible impure hygiene. ConcreteSupportedFunction.validatedBody now projects supported code through the leading hygiene conjunct; the explicit Bool case simulation uses globally fresh false/true binders r/u and their exact generated locals 1/2 throughout body-shape, local-row, lowering, and execution facts; declarationParameterIdsUnique_of_lowerSupported projects parameter uniqueness through the same strengthened conjunction. Forced full Talos recompilation exposed the third projection consumer after W7 had reported two; it is repaired without weakening any invariant.
files: integration/talos/FirTalos/ConcreteSupportedExportCorrectness.lean; integration/talos/FirTalos/Correctness/FunctionCaseExample.lean; integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; coordination/lanes/wasm-proof.md
contracts: W7 contract 818a1be1 is consumed unchanged. W6 changes proof consumers only. No semantic ABI, concrete layout, runtime/helper signature, ownership behavior, emitter, source semantics, or artifact contract changed.
checks: `make talos-setup` refreshed Talos 0e05edbc. Lean Beam sync/save passed for all three edited modules; ConcreteSupportedExportCorrectness and FunctionCaseExample have zero diagnostics, and ConcreteReuseCapacityCacheCorrectness has zero errors with its 20 pre-existing linter warnings. Direct `lake env lean` recompilation passed for all three modules. Focused Lake builds passed: the first two modules in a 3,117-job cone and ConcreteReuseCapacityCacheCorrectness in a 3,118-job cone. `git diff --check` passed. Final `make check` passed with 713 unique cases, 2,121/2,121 equal comparisons, zero findings, 191 active bug cards, and 25 mailbox tests. Final `make talos-check` passed all 3,167 jobs.
bug-cards: none
blockers: none
handoff: Integration should fast-forward main from 66aa9281 through W7 contract 818a1be1, W6 proof 1d44bfe5, and the containing W6 status commit atomically. Do not expose the contract-only prefix on main because Talos proof consumers are stale there.
next: After atomic acceptance, close W7-W6-20260821-003 and parent hygiene thread W6-W7-20260820-021, then require W7 and validation consumers to rebase on accepted main.
```
