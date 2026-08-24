# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 94108ba0, W7 selected-closure lowering stack and proof-visible production helpers, based on main a3eca661
functional-head: 75b33caf
contract-base: 94108ba0; consumes W7's selected declaration array and exact lowerDeclWithClosureCandidates/lowerWithClosureTargetFilter production bodies without changing them
clean-at-update: true
slice: Closure-dispatch refinement now follows the compiler-selected declaration array. The generic path remains all program declarations. Restricted lowering carries two explicit admission facts: every selected declaration comes from the source program, and the declaration reached by the current closed-ingress closure is present in the selected table. Candidate matching, direct selected dispatch, the exact saturated closure call theorem, and the lazy-cache structured proof now use that same table. The whole-module compiler lemmas unfold W7's newly proof-visible production helpers, so function, import, initializer, and declaration-local equations are recovered from the executable lowering rather than duplicated proof code.
files: integration/talos/FirTalos/ConcreteClosureDispatch.lean; integration/talos/FirTalos/ConcreteReuseCapacityCallCorrectness.lean; integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; bugs/FIR-BUG-wasm-none-selected-lowering-proof-surface.md; coordination/lanes/wasm-proof.md
contracts: No source semantics, semantic ABI, concrete runtime operation, resident helper signature, symbolic Wasm surface, emitter, ownership behavior, or layout changed. W6 strengthens only its proof admission records with the static selected-table subset fact and dynamic closed-ingress target-membership fact. W7 commit 94108ba0 makes the existing production lowering helpers proof-visible without changing executable behavior.
checks: `git diff --check` passed. Bug-card validation passed with 195 active cards. Lean Beam refresh/save passed with zero errors for ConcreteClosureDispatch.lean (source hash 366bda8e0bf1f58a), ConcreteReuseCapacityCallCorrectness.lean (source hash 38b8a98b156ea008), and ConcreteReuseCapacityCacheCorrectness.lean (source hash 7d4721a71ff1d37e). Forced `lake build +FirTalos.ConcreteClosureDispatch +FirTalos.ConcreteReuseCapacityCallCorrectness +FirTalos.ConcreteReuseCapacityCacheCorrectness` passed all 3,118 jobs and rebuilt the cache module. `make check` passed with 724 unique cases, 2,154/2,154 comparisons equal, zero findings, 8,777 machine steps, 195 active bug cards, and 25 mailbox tests. `make talos-setup` selected Talos 0e05edbc and `make talos-check` passed all 3,172 jobs.
bug-cards: FIR-BUG-wasm-none-selected-lowering-proof-surface (fixed by W7 proof visibility plus forced direct W6 elaboration regression)
blockers: none
handoff: Integration may land the dependency-ordered pair 94108ba0 then W6 functional head 75b33caf. This unblocks W7's selected-closure artifact and test-fixture work while preserving the generic all-declaration proof path.
next: After landing, rebase wasm/talos-runtime onto main and process the highest-priority remaining W6 proof mailbox request; do not carry the selected-lowering stack as a long-lived divergence.
```
