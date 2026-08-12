# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: a03b034f on main
functional-head: bf92264b (supported generated call-stack closure plus Lean 4.33 suffix-contract alignment)
contract-base: a03b034f; accepted Lean 4.33/Talos 0e05edbc bridge and global call-entry contracts; no shared semantic contract change
clean-at-update: true
slice: Retain each suspended generated caller's supported-function identity, canonical cache table, exact result ABI, and generated continuation-with-suffix proof in a hereditary static stack aligned constructor-by-constructor with the existing dynamic resource stack. Direct and saturated entries push both stacks; exact direct and matcher-label pop paths restore the caller as ConcreteStructuredSupportedGlobalOutcome after one ordinary source step. The nil/root return case is ruled out for a nonterminal source successor. No whole-callee evaluation, termination premise, or execution certificate is used.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/PLAN.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proof relation and roadmap only
checks: Rebased directly on main a03b034f. make talos-setup pinned Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254. Lean Beam update/sync/save reported saveReady true with zero errors. Direct lake build FirTalos.ConcreteStructuredSimulation passed 3119/3119 jobs. git diff --check passed. make check passed 122 harness tests, 653/653 native-LCNF, 9/9 direct-machine, 653/653 native-LCNF-V8, 662 unique cases, 1968/1968 comparisons, 6829 machine steps, zero findings, 133 bug cards, and the Lean 4.33 trusted-assumption gate. make talos-check passed 3143 jobs.
bug-cards: none
blockers: none
handoff: integrate wasm/talos-runtime through functional head bf92264b and this clean ready mailbox. This is a W6 proof-only slice; it changes no shared semantics, layout, symbolic-Wasm surface, or resident-helper signature.
next: Prove the relation-wide pointwise advance theorem that carries ConcreteStructuredSupportedGlobalOutcome through direct values, staged named/saturated calls, generated entries, and generated returns; then widen its dispatcher across the already proved external, lazy, case, effect, and ranked silent-step families.
```
