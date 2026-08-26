# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 6073bc679dbe4a8ff99f6b84b63efab854a67d9b, current main after direct-call proof acceptance and mailbox hardening
functional-head: d20022482657b42895c2fae30c47c4858c903d0d
contract-base: 6073bc679dbe4a8ff99f6b84b63efab854a67d9b
clean-at-update: true
slice: Extended the closed validation-carrying structured relation across the two remaining staged call protocols. Lazy-cache staging now retains branch-exact hit/miss admission, continuation validation, validated caller frames, resource agreement, and validation/resource spine agreement; cache hits close through the validated bind boundary and misses enter the generated initializer with a validated lazy frame. Pure external staging now retains exact destination validation through argument evaluation and the one host call, then closes through the same validated bind boundary. A general named-external signature theorem factors the common Nat, Int, and scalar compiler-local result proof. Static ABI admission remains independent from the explicit dynamic stepCost address-space budget required by allocating Nat/Int results.
files: integration/talos/FirTalos/ConcreteStructuredValidation.lean; coordination/lanes/wasm-proof.md
contracts: No shared semantic definition, runtime behavior, ABI, concrete layout, resident helper, emitter, symbolic Wasm instruction, or W7-owned artifact changed. This is a proof-only strengthening of the W6 closed relation and its exact administrative transitions; the existing admission-free supported relation remains available through validation-forgetting projections.
checks: Lean Beam sync/save for FirTalos/ConcreteStructuredValidation reported zero errors and two pre-existing warnings before the coordination-only rebase; targeted lake build FirTalos.ConcreteStructuredValidation passed 3,127 jobs; git diff --check and git diff main...HEAD --check passed after rebase; post-rebase make check passed with 719/719 source cases across native, LCNF, and V8, 9/9 direct-machine cases, 2,166/2,166 indexed comparisons equal, zero findings, 208 active bug cards, and 31 mailbox tests; Talos remains fixed at 0e05edbcfbb105b33e90c60b4f50e2cf193d9254; post-rebase make talos-check passed all 3,174 jobs.
bug-cards: none
blockers: none
handoff: GREEN LIGHT. Resolve the containing status commit from wasm/talos-runtime and integrate the two proof commits ccfe764a and d2002248 based at 6073bc67. The branch is rebased on current main, all gates pass, and only the W6-owned validation proof plus this single-writer mailbox changed.
next: Assemble the validated module-wide dispatcher and derive its compiler-admission boundary from residual validation, keeping dynamic address-space safety as a separate runtime premise. This closes the local one-step theorem needed by the universal finite-trace proof.
```
