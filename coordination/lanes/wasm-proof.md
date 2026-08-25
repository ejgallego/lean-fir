# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: adfddcbd, current main including the accepted typed getTag fast-path checkpoint
functional-head: 189ba687
contract-base: 62c4ca81, accepted production decrement installation, constructor/closure adapters, and resident release ABI; rebased through current main adfddcbd with that contract unchanged
clean-at-update: true
slice: Normalized leaf, persistent, and above-one fuel-indexed installed decrement successes to the common DecrementOnceSuccess relation; extracted exact fixed resident results from relational TerminatesWith posts using Talos fuel monotonicity; proved exact installed checked no-ops for erased zero and immediate tagged words; factored persistent live dispatch; and proved the heap-resident promoted-tagged Natural path through the installed public helper. The uniform tagged theorem covers both physical representations and states the promoted-map canonical-header premise explicitly.
files: integration/talos/FirTalos/ConcreteResidentRelease.lean; coordination/lanes/wasm-proof.md
contracts: No source semantics, runtime operation, resident helper signature, semantic ABI, concrete layout, symbolic Wasm surface, emitter, executable behavior, or shared adapter contract changed. All additions are proof-only consequences. The promoted theorem exposes, but does not yet add to the global simulation relation, the raw-header invariant required for witness-only promoted allocations.
checks: On current main adfddcbd, Lean Beam refresh/save passed ConcreteResidentRelease.lean with zero diagnostics; targeted `lake build +FirTalos.ConcreteResidentRelease` passed all 3,080 jobs; after rebase, `git diff --check` passed; `make check` passed with 726 unique cases, 2,160/2,160 comparisons equal, zero findings, 9,077 machine steps, 203 active bug cards, and 26 mailbox tests; `make talos-check` passed all 3,172 jobs.
bug-cards: FIR-BUG-wasm-none-adapter-if-branch-depth (existing shared-adapter blocker; unchanged)
blockers: Exact production adapter provenance for the resident Array loop still awaits FIR-BUG-wasm-none-adapter-if-branch-depth. The recursive ownership theorem additionally needs canonical raw headers for witness-only promoted tags carried by the global simulation relation; this checkpoint makes that missing invariant explicit and proves all downstream promoted control flow under it.
handoff: GREEN LIGHT. Integration may fast-forward current main adfddcbd through functional head 189ba687 and this containing mailbox commit. The stack is proof-only, exact-result preserving, rebased, and fully green.
next: Rebase after landing. Add the promoted-map canonical-header invariant as an isolated W6 proof-contract slice, prove it for allocation and preservation transitions, then instantiate ResidentOwnershipStep from the fuel induction. Reconsume the Array arm after the independent adapter-depth repair lands.
```
