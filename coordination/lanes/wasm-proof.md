# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 5eb82447f2dcc806e9cf5ff393b209affe4a944d, the UInt64 semantic contract stack through the LCNF ElimDead runtime-relation repair
functional-head: 5854171ca4f384ebb4865ebd0322de712916f2b7
contract-base: 9046caf3e1b3024c75a2fcf4f54aa3a79025d701, heap-only semantic UInt64 boxing, tagged UInt64 unbox rejection, and aligned JavaScript semantic host
clean-at-update: true
slice: Made the W6 concrete scalar-box boundary kind-aware: UInt8, UInt16, UInt32, and USize retain their payload-bounded tagged representation, while every UInt64 box allocates an ordinary heap cell and physical tagged words fail UInt64 decoding. Proved the generic heap/tag classifier, allocation/read/failure refinements, and Talos runtime/compiler consequences; added small-UInt64 allocation and tagged-rejection executable guards.
files: Fir/Wasm/Concrete/Runtime.lean; Fir/Wasm/Concrete/BoxingCorrectness.lean; Fir/Wasm/Concrete/Examples.lean; integration/talos/FirTalos/ConcreteRuntime.lean; integration/talos/FirTalos/ConcreteReuseCapacityCorrectness.lean; integration/talos/FirTalos/ConcreteCompilerCorrectness.lean; integration/talos/FirTalos/ConcreteCompilerCorrectnessContract.lean; coordination/lanes/wasm-proof.md
contracts: The W6 concrete scalar boxing/decoding refinement boundary is now kind-aware and agrees with semantic contract 9046caf3. Ordinary heap decoding is unchanged. No concrete layout constant, resident-helper signature, symbolic Wasm instruction, semantic ABI signature, source interpreter operation, or emitter changed.
checks: Lean Beam update/sync reported zero errors and save-ready status for Fir/Wasm/Concrete/Runtime.lean, Fir/Wasm/Concrete/BoxingCorrectness.lean, Fir/Wasm/Concrete/Examples.lean, integration/talos/FirTalos/ConcreteRuntime.lean, integration/talos/FirTalos/ConcreteReuseCapacityCorrectness.lean, integration/talos/FirTalos/ConcreteCompilerCorrectness.lean, and integration/talos/FirTalos/ConcreteCompilerCorrectnessContract.lean; targeted `lake build +Fir.LeanIR.Passes.ElimDeadRuntimeRel` passed 15 jobs; targeted `lake build +FirTalos.ConcreteCompilerCorrectness` passed 3,115 jobs; `git diff --check` passed; `make check` passed with 719/719 native-LCNF-V8 cases, 9/9 direct-machine cases, 2,166/2,166 indexed comparisons equal, zero findings, 203 active bug cards, and 26 mailbox tests; `make talos-setup` fixed Talos at 0e05edbcfbb105b33e90c60b4f50e2cf193d9254; `make talos-check` passed all 3,172 jobs.
bug-cards: FIR-BUG-impure-none-uint64-box-tagged; the semantic, LCNF-proof, and W6 concrete/proof portions are repaired, while W7 still owns the resident-helper and executable-artifact portion
blockers: none for W6 integration; W7 must consume this contract in the resident scalar-box helper and its acceptance artifacts
handoff: GREEN LIGHT. Integration may atomically land the semantic stack through 5eb82447 and W6 commits through 0a8e7c64 plus this containing mailbox commit. The branch is rebased, fully green, and changes no W7-owned implementation file.
next: W7 rebases onto the accepted stack, changes the resident UInt64 boxing helper to allocate for every payload, and reruns standalone, linked, Node/Chrome, native-oracle, and import-closure acceptance. W6 then proves any new resident-helper implementation-to-concrete-host theorem requested at that stable helper boundary.
```
