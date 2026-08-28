# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 92f60ba255f7b2cd7ac525fe5d97b5fedd5d6131
functional-head: 176cdbc779aaa2cab5f87e4551ce6d0d469549dc
contract-base: 92f60ba255f7b2cd7ac525fe5d97b5fedd5d6131
clean-at-update: true
slice: Define the smallest reusable source-only value/environment typing predicates needed by the semantic invariant, then derive the return and descriptor-bearing mutation admission families from them without compiler or target evidence.
files: integration/talos/FirTalos/ConcreteStructuredValidation.lean; integration/talos/FirTalos/ConcreteResumableWasm.lean; integration/talos/PLAN.md; coordination/lanes/wasm-proof.md
contracts: none expected; proof-side semantic typing predicates and extraction lemmas only
checks: not-run
bug-cards: none
blockers: none
handoff: none
next: Audit existing return/descriptor predicates and factor their shared value/environment premises before proving source-admission constructors.
```
