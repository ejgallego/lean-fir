# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 9397a80d, current main including the accepted production closure-descriptor adapter checkpoint
functional-head: 5bb7e88a
contract-base: 913c2552, accepted W7 reduction-visible production decrement-body surface; rebased through current main 9397a80d with unchanged resident release ABI, layout, helper bodies, and proof-visible staged builders
clean-at-update: true
slice: Exposed the production closure-descriptor release adapter and completed the installed public-call lift for count-one constructors and closures. The adapter proof factors direct and guarded recursive child-list adaptation, proves that the emitter's descriptor filter computes exactly closureOwnedCaptureIndices, and recursively adapts the checked ordinal/capture-count dispatch to closureDescriptorReleaseProgram. DecrementOnceInstallation.body_constructorClosure identifies the installed body with exact constructor and closure targets, leaving only the opaque/Array target existential. The new DecrementOnceSuccess relation packages the concrete operation plus heap, resident-memory, canonical-header, and payload-frame preservation. Generic body-to-call lifting and branch admission theorems now establish this common postcondition for the actual installed fir_dec_once public call while preserving the caller operand tail.
files: integration/talos/FirTalos/ConcreteResidentRelease.lean; coordination/lanes/wasm-proof.md
contracts: No source semantics, runtime operation, resident helper signature, semantic ABI, concrete layout, symbolic Wasm surface, emitter, executable behavior, or shared adapter contract changed. The new surfaces are proof-only consequences of successful generation, adaptation, and installation; no certificate or trusted premise was added.
checks: On current main 9397a80d, Lean Beam refresh/save passed ConcreteResidentRelease.lean with zero diagnostics; targeted `lake build +FirTalos.ConcreteResidentRelease` passed all 3,079 jobs; `git diff --check` passed; `make check` passed with 726 unique cases, 2,160/2,160 comparisons equal, zero findings, 9,077 machine steps, 202 active bug cards, and 26 mailbox tests; `make talos-check` passed all 3,172 jobs.
bug-cards: FIR-BUG-wasm-none-adapter-if-branch-depth (existing confirmed shared-adapter bug; unchanged)
blockers: Exact adapter provenance for the resident Array loop remains blocked by FIR-BUG-wasm-none-adapter-if-branch-depth because the production encoder emits br 1 under if while the Talos adapter emits br 0. This checkpoint does not weaken or work around that contract. Constructor and closure-descriptor installed-body provenance are unblocked.
handoff: GREEN LIGHT. Integration may fast-forward current main 9397a80d through functional head 5bb7e88a and this containing mailbox commit. This slice proves installed public fir_dec_once refinement for count-one constructors and closures on top of the accepted closure adapter.
next: After landing, rebase wasm/talos-runtime onto the new main. Use DecrementOnceSuccess as the common induction conclusion and connect the installed constructor/closure admissions to the fuel-recursive all-object theorem. Coordinate the existing shared if-label depth repair before claiming adapter provenance for the Array arm.
```
