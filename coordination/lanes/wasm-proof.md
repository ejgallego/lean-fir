# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: b52710d2, current main including the accepted wide-ByteArray push stack
functional-head: ddfc40f3
contract-base: 913c2552, accepted W7 reduction-visible production decrement-body surface; rebased through current main b52710d2 with unchanged resident release ABI, layout, helper bodies, and proof-visible staged builders
clean-at-update: true
slice: Connect the production resident decrement helper to its existing concrete-runtime refinement without a body certificate. Generation success now yields the complete positional parameter/local map. Exact adapter theorems cover checked no-op, full-header probe, shared-count store, persistent release, and each staged outer dispatcher. Computation-level composition proves that the descriptor-dependent last-reference fragment is the sole remaining fallible adapter subcomputation. DecrementOnceInstallation.body extracts its actual adapted target from successful whole-function adaptation and identifies the installed body as decrementOnceProgram persistentReleaseProgram lastTarget plus only the standard terminal suffix. The first installed-call theorem proves the ordinary rc > 1 case across concrete memory, FIR decValueOnce semantics, live-heap/canonical-header/resident-memory refinement, the real installed function index, exact empty result, and unchanged caller operand tail. The cumulative stack also records the production signature, installation and entry frame, and the installed release-header theorem.
files: integration/talos/FirTalos/Correctness/Adapter.lean; integration/talos/FirTalos/ConcreteResidentRelease.lean; coordination/lanes/wasm-proof.md
contracts: No source semantics, runtime operation, resident helper signature, semantic ABI, concrete layout, symbolic Wasm surface, emitter, or executable behavior changed. Proof-only Talos adapter composition lemmas were moved to the lower Adapter module and extended for successful append and structured instruction composition; downstream theorem API is preserved.
checks: After rebasing the six-commit W6 stack onto current main b52710d2, Lean Beam refresh passed ConcreteResidentRelease.lean with zero diagnostics; `git diff --check` passed; targeted `lake build +FirTalos.ConcreteResidentRelease` passed all 3,079 jobs before the source-preserving rebase; post-rebase `make check` passed with 726 unique cases, 2,160/2,160 comparisons equal, zero findings, 9,077 machine steps, 200 active bug cards, and 26 mailbox tests; post-rebase `make talos-check` passed all 3,172 jobs.
bug-cards: none
blockers: none
handoff: Integration may fast-forward the clean cumulative W6 stack from current main b52710d2 through functional head ddfc40f3 and this containing mailbox commit. This is the production-installed ordinary shared-decrement proof checkpoint requested by W7; it uses the accepted W7 staged body surface and introduces no certificate premise.
next: After landing, rebase wasm/talos-runtime onto the new main. Generalize the installed-call lifting pattern over terminal branch postconditions, then expose installed persistent, underflow, and exact last-reference constructor/closure/Array refinements using the same extracted production lastTarget. Continue toward a single production helper simulation theorem by joining those exhaustive admission and live-object cases.
```
