# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: ce78663b, current main including the accepted single-pass lean-zip publication
functional-head: 6318ec66
contract-base: 913c2552, accepted W7 reduction-visible production decrement-body surface; rebased through current main ce78663b with unchanged resident release ABI, layout, helper bodies, and proof-visible staged builders
clean-at-update: true
slice: Rebased the cumulative production decrement proof stack onto current main and generalized the installed-body boundary. DecrementOnceInstallation.wp_body_of_decrementOnceProgram recovers the actual descriptor-dependent production branch and discards only the standard terminal suffix. A shared return bridge lifts branch-independent body proofs to the public installed call, while the exceptional bridge states exact eventual public-run traps because Talos TerminatesWith is success-only. The installed helper now refines persistent no-op and zero-count underflow in addition to ordinary rc > 1; the latter was refactored through the shared bridge. Underflow preserves the exact final store and trap message for every sufficiently large fuel.
files: integration/talos/FirTalos/Correctness/Adapter.lean; integration/talos/FirTalos/ConcreteResidentRelease.lean; coordination/lanes/wasm-proof.md
contracts: No source semantics, runtime operation, resident helper signature, semantic ABI, concrete layout, symbolic Wasm surface, emitter, or executable behavior changed. All new surfaces are proof-only consequences of successful production generation, adaptation, and installation; no body certificate or trusted premise was added.
checks: On current main ce78663b, Lean Beam refresh/save passed ConcreteResidentRelease.lean with zero diagnostics; targeted `lake build +FirTalos.ConcreteResidentRelease` passed all 3,079 jobs; `git diff --check` passed; `make check` passed with 726 unique cases, 2,160/2,160 comparisons equal, zero findings, 9,077 machine steps, 201 active bug cards, and 26 mailbox tests; `make talos-check` passed all 3,172 jobs.
bug-cards: none
blockers: none
handoff: GREEN LIGHT. Integration may fast-forward current main ce78663b through functional head 6318ec66 and this containing mailbox commit. This supersedes the pre-rebase 04fa8770 checkpoint while preserving its complete proof content, and additionally includes installed persistent and underflow refinements plus the reusable success/trap lifting boundary.
next: After landing, rebase wasm/talos-runtime onto the new main. Derive the production last-reference adapter as release-header call plus the exact generated object-kind dispatcher, then reuse the existing constructor, closure-descriptor, Array, and leaf semantic theorems at the installed call boundary before joining the exhaustive production helper simulation.
```
