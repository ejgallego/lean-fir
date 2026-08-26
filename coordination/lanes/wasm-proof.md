# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 3536a3dff0b3ce3c9dfa65d516284fbe445bc523, current main after deleted-allocation semantic-carrier acceptance
functional-head: c9d1e4bcfe1cd47faefea0abc8b1329588951ae5
contract-base: 3536a3dff0b3ce3c9dfa65d516284fbe445bc523
clean-at-update: true
slice: Retains residual validation across lazy-cache hit/miss staging and pure external calls, then factors the return boundary into physical carrier and source-semantic provenance. SemanticValueAtAbi states the exact source value shapes for all ABI kinds; PhysicalValueRel.ofSemanticValueAtAbi proves safe bit-preserving reclassification, including tobject-to-object/tagged only with the corresponding heap/tagged fact. The new core return theorem canonicalizes a yielded value at the active function result ABI. The closed validated return theorem derives the compiled local from production residual validation and needs only the independent source-semantic result fact, eliminating the per-step admission certificate for that boundary without weakening leanCompatible/refines. Dynamic wasm32 address-space safety remains separate.
files: integration/talos/FirTalos/ConcreteRuntime.lean; integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/FirTalos/ConcreteStructuredValidation.lean; coordination/lanes/wasm-proof.md
contracts: No shared source semantics, executable runtime behavior, compiler ABI, concrete memory layout, resident helper signature, emitter, symbolic Wasm instruction, or W7 artifact changed. SemanticValueAtAbi and its physical transport theorem are W6 proof-side interfaces; the closed validation relation is strengthened only through new theorems and the previous admission-based return theorem remains available.
checks: Lean Beam update/sync/save reported zero errors for ConcreteRuntime, ConcreteStructuredSimulation, and ConcreteStructuredValidation; targeted lake build FirTalos.ConcreteStructuredValidation passed 3,127 jobs before rebase; branch rebased cleanly onto main 3536a3df; git diff --check and git diff main...HEAD --check passed; post-rebase make check passed with 719/719 source cases across native, LCNF, and V8, 9/9 direct-machine cases, 728 unique cases, 2,166/2,166 comparisons equal, zero findings, 208 active bug cards, and 31 mailbox tests; post-rebase make talos-check passed all 3,174 jobs.
bug-cards: FIR-BUG-wasm-none-return-admission-refinement-direction (existing; semantic transport boundary solved, global source-result invariant remains)
blockers: none
handoff: GREEN LIGHT. Resolve the containing status commit from wasm/talos-runtime and fast-forward the pending W6 stack through functional head c9d1e4bc, based directly at 3536a3df. The branch is rebased on current main and all required gates pass.
next: Thread the source-semantic result invariant through active and suspended validated states, prove it is preserved by binding/call/cache/external transitions, and use the new admission-free return theorem in the module-wide validated dispatcher. Continue to keep dynamic address-space safety as a separate execution premise.
```
