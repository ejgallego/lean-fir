# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 2b5851e6, current main including the accepted Talos anonymous-control-depth repair
functional-head: bfc01d77
contract-base: 8cb20ce7, accepted production decrement installation, constructor/closure adapters, resident release ABI, and anonymous-if adapter-depth repair; rebased through current main 2b5851e6 with the decrement contract unchanged
clean-at-update: true
slice: Normalized leaf, persistent, and above-one fuel-indexed installed decrement successes to the common DecrementOnceSuccess relation; extracted exact fixed resident results from relational TerminatesWith posts using Talos fuel monotonicity; proved exact installed checked no-ops for erased zero and immediate tagged words; factored persistent live dispatch; and proved the heap-resident promoted-tagged Natural path through the installed public helper. The uniform tagged theorem covers both physical representations and states the promoted-map canonical-header premise explicitly.
files: integration/talos/FirTalos/ConcreteResidentRelease.lean; coordination/lanes/wasm-proof.md
contracts: No source semantics, runtime operation, resident helper signature, semantic ABI, concrete layout, symbolic Wasm surface, emitter, executable behavior, or shared adapter contract changed. All additions are proof-only consequences. The promoted theorem exposes, but does not yet add to the global simulation relation, the raw-header invariant required for witness-only promoted allocations.
checks: On current main 2b5851e6, a fresh Lean Beam daemon reported zero diagnostics and save-ready status for ConcreteResidentRelease.lean; targeted `lake build +FirTalos.ConcreteResidentRelease` passed all 3,080 jobs; `git diff --check` passed; `make check` passed with 726 unique cases, 2,160/2,160 comparisons equal, zero findings, 9,077 machine steps, 203 active bug cards, and 26 mailbox tests; `make talos-setup` refreshed Talos at 0e05edbcfbb105b33e90c60b4f50e2cf193d9254; `make talos-check` passed all 3,172 jobs.
bug-cards: none; FIR-BUG-wasm-none-adapter-if-branch-depth was repaired on main at 8cb20ce7
blockers: The recursive ownership theorem still needs canonical raw headers for witness-only promoted tags carried by the global simulation relation; this checkpoint makes that missing invariant explicit and proves all downstream promoted control flow under it. Exact production Array adapter provenance is no longer blocked.
handoff: GREEN LIGHT. Integration may fast-forward current main 2b5851e6 through functional head bfc01d77 and this containing mailbox commit. The stack is proof-only, exact-result preserving, rebased, and fully green.
next: Land this refreshed checkpoint. Then rebase W6 onto the accepted UInt64 box/unbox contract stack and implement its isolated kind-aware concrete runtime/proof adaptation. After that atomic handoff, add the promoted-map canonical-header invariant, consume the now-repaired exact installed Array arm, and instantiate ResidentOwnershipStep from the fuel induction.
```
