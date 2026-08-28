# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 97474d5beb3c19fe7916ef2fa5ce56e376590daf
functional-head: 48e340b7b651143d484b634466df9a7dc8999806
contract-base: 97474d5beb3c19fe7916ef2fa5ce56e376590daf
clean-at-update: true
slice: First dependency-ordered checkpoint for authoritative mailbox thread W7-W6-20260826-022. The isolated shared contract commit admits Float32 marker 6 and Float marker 7 as exact heap-only concrete scalar boxes. The proof stack establishes canonical 40-byte allocation, owned nonpersistent headers, four exact Float32 payload bytes plus zero high padding, eight exact Float payload bytes, heap-object result-kind refinement, physical lane decoding, resolver admission, and compiler scalar extraction for exact raw bits. It also factors pure wasm32-word assembly/projection lemmas into the concrete memory boundary, eliminating a Lean 4.33 bv_decide enum-auxiliary diamond exposed by forced source recompilation.
files: Fir/Wasm/Concrete/Layout.lean; Fir/Wasm/Concrete/Runtime.lean; Fir/Wasm/Concrete/Memory.lean; Fir/Wasm/Concrete/BoxingCorrectness.lean; Fir/Wasm/Concrete/Refinement.lean; integration/talos/FirTalos/ConcreteRuntime.lean; integration/talos/FirTalos/ConcreteResolver.lean; integration/talos/FirTalos/ConcreteCompilerCorrectness.lean; integration/talos/FirTalos/ConcreteResidentBigNumeric.lean; coordination/lanes/wasm-proof.md
contracts: Shared concrete BoxedScalarKind and BoxedScalar descriptor extension only: Float32 uses marker 6, payloadBytes 4, Float uses marker 7, payloadBytes 8, and both disallow tagged representation. Existing integer/USize codes, representations, ownership, allocator behavior, source semantics, lowering, symbolic Wasm, W7 helper names/signatures/bodies, and artifacts are unchanged. Consumers gain exact Float32/Float resolver and refinement cases; no contract is weakened.
checks: Lean Beam update/refresh/save passed with zero diagnostics for every edited Lean module. Forced source-only root dependency cone passed. Forced source-only full Talos build passed all 3,174 jobs. Four direct import-order probes passed in both directions after factoring the memory lemmas. git diff --check passed. make check passed with 730 unique validation cases, 2,172/2,172 comparisons equal, zero findings, 211 active bug cards, and 38 mailbox tests. make talos-setup completed at Talos 0e05edbc. make talos-check passed all 3,174 jobs with exact receipt 068f288e0cf8cadb5010c1c7c2a5eb2c9d11fbbbe778f78fc2e32cf3452ece62.
bug-cards: none
blockers: none
handoff: GREEN LIGHT. Land the exact dependency-ordered commits ca25935e (isolated shared descriptor contract), f492bfeb (reusable 64-bit memory proof boundary and Lean 4.33 diamond repair), and 48e340b7 (Float consumer/refinement adaptation) on main before rebasing W7 checkpoint 917c0a46. The worktree is clean at the containing status commit and publication remains local-only.
next: After this checkpoint lands, W7 rebases its disjoint trusted-Array checkpoint. W6 then rebases on the resulting accepted main and completes W7-W6-20260826-022 by proving the actual installed fir_float32_box/unbox and fir_float_box/unbox bodies, including malformed-layout guards, exact trace/store, and caller-tail preservation.
```
