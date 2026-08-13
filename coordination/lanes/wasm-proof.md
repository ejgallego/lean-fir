# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 3a67ccc0 on main; includes the accepted W7 spatial HitScene package and all prior W6 pointwise slices
functional-head: 88613614
contract-base: 3a67ccc0; consumes the accepted structured-Wasm/compiler, source-semantics, concrete runtime, generated-call, and resident-runtime contracts without changing a shared semantic or executable ABI contract
clean-at-update: true
slice: W6.7e singleton object-case pointwise closure. ConcreteStructuredCodeStepAdmission now admits the existing source/compiler-only SingleObjectConstructorCaseSupported boundary. The exact five-step production getTag/tag-comparison/conditional prefix enters the selected arm and records its target-only case label in ConcreteStructuredFrameRel, ConcreteStructuredSuspendedResourceStack, ConcreteStructuredSupportedFrameStack, and their agreement relation. The resource and supported stacks carry no source frame or future execution evidence for this administrative layer. The yielded-control return rule now inducts through any number of case-label layers, executes their exact returnLabel paths, and only then consumes the underlying direct/saturated caller frame. Both local and strong supported-global dispatchers preserve the relation through singleton selection; nested calls inside the selected arm therefore compose with return-pop. The roadmap records the stable singleton boundary while leaving arbitrary object/scalar tables and lazy/cache control as explicit subsequent widenings.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean, integration/talos/PLAN.md, integration/talos/W6-THEOREM-ROADMAP.md, coordination/lanes/wasm-proof.md
contracts: none; proof-side current-node admission, target-only case-frame relation, exact prefix/unwind laws, dispatcher coverage, and roadmap clarification only
checks: branch rebased cleanly from bad7b4ba onto main 3a67ccc0 after the functional proof checkpoint; Lean Beam update/sync/save PASS at version 11 with zero errors and save-ready module, source hash 28b35f0f4f07b0f7; direct lake build FirTalos.ConcreteResumableWasm PASS before rebase and PASS again on 3a67ccc0 (3120 jobs); git diff --check PASS before and after rebase; make talos-setup PASS at Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254; make check PASS before and after rebase (122 harness tests, 661/661 native-LCNF, 9/9 direct-machine, 661-case native/LCNF/V8 triangle, 670 unique cases, 1992/1992 comparisons, 7176 machine steps, zero findings, 162 active bug cards after rebase, Lean 4.33 trusted-assumption gate); make talos-check PASS before and after rebase (3143 jobs, including modified proof and ConcreteResumableWasm import cone)
bug-cards: none
blockers: none
handoff: integration may fast-forward wasm/talos-runtime from main 3a67ccc0 through functional head 88613614 and this mailbox commit; no shared contract changed
next: generalize the pointwise case admission/dispatcher from the singleton hit to arbitrary normalized object-constructor and scalar-UInt8 tables using the new case-label stack layer, then add lazy/cache control and close remaining production current-step coverage/root construction
```
