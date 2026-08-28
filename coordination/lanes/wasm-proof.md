# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 3b81c5255b638ef93e2160b6086150a6cb6a485b
functional-head: e6d3c2a5924cdf44c3bf9ea52682a231e7ab4c98
contract-base: 9dc9abd34aac196803f386fc53a5830a17b2efea
clean-at-update: true
slice: Complete authoritative mailbox thread W7-W6-20260828-004 for production UInt8.toNat, UInt8.toBitVec, UInt16.toNat, and UInt32.toNat. Commit 794c9de3 proves the declaration-independent target programs, exact canonical immediate words, complete UInt8/UInt16 range facts, precise .tagged/.tobject ValueRel results, and the UInt32 low/high WPs. Commit 2ac347e8 lifts the bounded core to a generic fuel-free installed-function TerminatesWith theorem with unchanged store and caller tail, and propagates the UInt32 high arm through the existing promoted-Natural constructor refinement. Commit e6d3c2a5 consumes W7's accepted closed source-body equations, attaches all four production aliases, and exposes exact production low/high TerminatesWith theorems. The UInt32 high theorem deliberately retains the resolved fir_numeric_make_natural(value, 0) run, changed result store, and extended refinement witness as explicit premises.
files: integration/talos/FirTalos.lean; integration/talos/FirTalos/ConcreteResidentFixedWidth.lean; coordination/lanes/wasm-proof.md
contracts: No shared contract changed. These are proof-only refinements of the production W7 functions and proof-visible body equations accepted on main. Helper names, signatures, instructions, ABI, concrete layouts, ownership rules, source semantics, linker inventory, and artifacts are unchanged.
checks: Lean Beam update/sync/save passed with zero diagnostics for the final source, source hash 311a745ea80b0850. Focused lake build FirTalos.ConcreteResidentFixedWidth passed all 3,126 jobs. git diff --check passed. make check passed with 730 unique validation cases, 2,172/2,172 comparisons equal, zero findings, 212 active bug cards, and 38 mailbox tests. make talos-setup completed at Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254. Post-rebase make talos-check passed all 3,182 jobs with exact receipt 36c2023e78c92756a9479bfea40c5ef721f5b0906cd7127eb3fccc2ad259f924.
bug-cards: none
blockers: none
handoff: GREEN LIGHT. Fast-forward main from 3b81c5255b638ef93e2160b6086150a6cb6a485b through 794c9de3, 2ac347e8, and e6d3c2a5 plus this containing status commit. This closes W7-W6-20260828-004 and supplies W7 the requested production fixed-width Natural refinement checkpoint.
next: After integration acceptance, rebase and select the highest-priority remaining authoritative W6 request. Do not overlap this frozen ready handoff.
```
