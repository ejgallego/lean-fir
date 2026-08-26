# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 8c939e5d59fa3767d203e5678ecfa8c90a8ec475, current main after acceptance of arbitrary ElimDead live prefixes
functional-head: 45989debfc57aed664ff0b736557b639cd80cd81
contract-base: af7d10a807c7d401c9dac1b5d261688277d66d98, production ResidentScalarBox UInt64 helpers; concrete allocation/read refinements through c09cbb8779c8737902014e5e422c72b4164c141d
clean-at-update: true
slice: Proved the production resident UInt64 box/unbox helper bridge end to end. Every 64-bit payload follows the ordinary 40-byte heap allocation path, writes the canonical boxed header and bit-exact i64 payload, and establishes the allocator, object, raw-header, alignment, and payload-read refinements. Canonically admitted boxes unbox to the exact bits with unchanged store; tagged immediates, below-heap or misaligned words, wrong-kind objects, and canonical promoted-tag allocations trap. The public theorems target the exact resolver-installed helper bodies, signatures, indices, installation order, and adapter terminal suffix.
files: integration/talos/FirTalos/ConcreteResidentMemory.lean; integration/talos/FirTalos/ConcreteResidentAllocator.lean; integration/talos/FirTalos/ConcreteResidentScalarBox.lean; coordination/lanes/wasm-proof.md
contracts: No shared semantic definition, ABI, layout constant, helper signature, emitter, symbolic Wasm instruction, resident implementation, or artifact changed. The slice reuses the landed generic concrete UInt64 memory/allocation boundary and proves the exact W7 production bodies against it.
checks: Lean Beam post-rebase sync reported zero errors and zero warnings for integration/talos/FirTalos/ConcreteResidentScalarBox.lean; targeted lake build FirTalos.ConcreteResidentScalarBox passed 3,125 jobs; git diff --check passed; make check passed with 719/719 source cases, 9/9 direct-machine cases, 2,166/2,166 indexed comparisons equal, zero findings, 204 active bug cards, and 26 mailbox tests; make talos-setup fixed Talos at 0e05edbcfbb105b33e90c60b4f50e2cf193d9254; make talos-check passed all 3,172 jobs.
bug-cards: none
blockers: none; W7 may integrate the proof stack immediately
handoff: GREEN LIGHT. Resolve the containing status commit from wasm/talos-runtime and integrate the stack based at 8c939e5d through functional head 45989deb. The branch is clean, rebased on current main, and changes only W6-owned proof consumers plus this single-writer mailbox.
next: At integration, W7 should add FirTalos.ConcreteResidentScalarBox to the integration-owner-controlled FirTalos umbrella so the new bridge joins the default Talos dependency cone. After landing, W6 rebases on main and continues the next installed resident-helper/finite-trace proof slice.
```
