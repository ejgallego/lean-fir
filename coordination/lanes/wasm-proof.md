# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 4d9668a1 on main
functional-head: 716cc1f1
contract-base: 4d9668a1; accepted supported generated call-stack and current Lean 4.33/Talos contracts
clean-at-update: true
slice: Closed the branch-complete strong one-source-step boundary. Direct values and returns now expose exact frame preservation; ConcreteStructuredCodePointwiseRel.advance_supportedGlobal transports aligned static/resource support. ConcreteStructuredRunnableOutcome combines the four current control alternatives with only their local runnable premise, and ConcreteStructuredRunnableGlobalOutcome hides active-function indices, forgets to ConcreteStructuredSupportedGlobalOutcome, preserves observations, and advances one ordinary source step to the same supported global relation after a finite target path. Zero target steps are accepted only with strict compiler-control-rank descent; no future admission, termination proof, or execution certificate is stored.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof relation and roadmap only
checks: Lean Beam update/sync/save at version 16 passed with saveReady true and zero errors; direct lake build FirTalos.ConcreteStructuredSimulation passed all 3119 jobs; git diff --check passed; make check passed (122 unit/harness tests plus native/V8 validation); make talos-setup pinned Talos 0e05edbc and make talos-check passed all 3143 jobs; post-commit git rebase main was a no-op and the worktree was clean before this mailbox update
bug-cards: none
blockers: none
handoff: ready for integration; base 4d9668a1, functional head 716cc1f1, branch wasm/talos-runtime; no shared contracts changed
next: Widen ConcreteStructuredRunnableOutcome over the already proved external, lazy/cache, case, and effect transition laws, then prove the source-local admission classifier needed to instantiate the public ranked finite-prefix simulation without certificates.
```
