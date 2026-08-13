# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 3e63192d on main; includes the accepted nested input-alias validation contract and all prior W6 pointwise slices
functional-head: 47abc3f6
contract-base: 3e63192d; consumes the accepted structured-Wasm/compiler, source-semantics, concrete-runtime, generated-call, resident-runtime, and validation contracts without changing a shared semantic or executable ABI contract
clean-at-update: true
slice: W6.7e generated lazy-cache pointwise closure for hits and non-heap misses. Current-node admission records only the populated/empty semantic lookup and production cache environment. Staging takes one source step with target stutter. A hit takes one source lookup and four target flag/conditional/value-load steps to the existing bind protocol. A miss takes one source and three target steps into the compiler-selected generated initializer while pushing exact lazy caller constructors in the resource and supported stacks. On a related non-heap yield, one source publication step matches seven target steps for call return, concrete cacheSet, value/flag global publication, conditional exit, and value reload, then rejoins the existing final bind protocol. Every boundary reconstructs the complete entry-relative cache, ownership, budget, closure-table, ABI, and supported-caller invariants. No theorem accepts an initializer evaluation, termination premise, future admission, target code/path certificate, or caller-selected branch.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean, integration/talos/FirTalos/ConcreteResumableWasm.lean, integration/talos/PLAN.md, integration/talos/W6-THEOREM-ROADMAP.md, coordination/lanes/wasm-proof.md
contracts: none; proof-side lazy hit/non-heap miss admission, exact staged control and finite prefixes, lazy hereditary caller frames, strong dispatcher/coverage inversion, and roadmap clarification only
checks: rebased cleanly from 520cc7ef onto main 3e63192d; Lean Beam update/sync/save PASS after rebase with zero errors and save-ready module, source hash dc74789b10667059; direct lake build FirTalos.ConcreteResumableWasm PASS after rebase (3120 jobs); git diff --check PASS before and after rebase; make check PASS on 3e63192d (125 harness tests, 666/666 native-LCNF, 9/9 direct-machine, 666-case native/LCNF/V8 triangle, 675 unique cases, 2007/2007 comparisons, 7252 machine steps, zero findings, 165 active bug cards, Lean 4.33 trusted-assumption gate); make talos-setup PASS at Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254; make talos-check PASS on 3e63192d (3143 jobs, including modified proof and ConcreteResumableWasm import cone)
bug-cards: none
blockers: none
handoff: integration may fast-forward wasm/talos-runtime from main 3e63192d through functional head 47abc3f6 and this mailbox commit; no shared contract changed
next: prove the production current-step coverage law and canonical root construction needed by ConcreteFiniteTraceCorrect; widen heap-valued lazy miss publication separately through facts-aware invalidation, and retain target-only loop unwinding as a later widening
```
