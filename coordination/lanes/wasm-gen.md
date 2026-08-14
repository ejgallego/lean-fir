# wasm-gen lane

The forward-looking W7 plan lives in
[`Fir/Wasm/Emit/ROADMAP.md`](../../Fir/Wasm/Emit/ROADMAP.md). Accepted milestone
history remains on `coordination/BOARD.md`; client-specific contracts remain
inside their integration directories. This mailbox records only the active
queue and current handoff boundary.

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: 5ad696a9 on main
functional-head: 9213e239, ratchet and publish the isolated lean-zip raw closure
contract-base: 5ad696a9 on main. Consumes the accepted setTag UInt32-bound production-validator contract and its W6 constructor-tag admission theorem. Changes no shared semantic operation, concrete layout, symbolic-Wasm instruction, ownership rule, resident-helper signature, or W6 theorem surface. Hardens only the lean-zip integration's exact closure and immutable-package contract after accepted compiler-cache isolation
clean-at-update: true
slice: Review the lean-zip raw closure after G2 compiler-cache isolation instead of weakening its stale 702-declaration ratchet. Pin the exact ordered external, source-function, resident-helper, and complete-function inventories by SHA-256; update the reviewed counts and sizes; document the closure transition; close the stale-ratchet bug card; and atomically publish a clean, immutable, zero-import raw-compression package against lean-zip 30737b4e and zipCommon 4425bab1. The package compiles Zip.Wasm.compressRaw directly, retains the persistent compiler-cache floor, rewinds scratch state after each call, and supports compression levels 1 through 10
files: integration/lean-zip/raw-closure-contract.json; integration/lean-zip/package-raw.mjs; integration/lean-zip/README.md; Fir/Wasm/Emit/ROADMAP.md; bugs/FIR-BUG-wasm-none-lean-zip-raw-cache-isolation-ratchet.md
contracts: none. The integration now ratchets 662 captured declarations, 128 reviewed externals, 534 retained source functions, 2,598 resident helpers, and 3,132 complete functions. Ordered inventory hashes are externals 171395362573b56dc128258c940a0a42b56bab3ffacfaec06be8c19cef6e3512, source c5e7e16dd321e9e861e026579e298a021ffd52ba53c1d24863ef8961c25ee820, resident ef10483be01760671ac79d79487a647cb68d377171bc14c700679e743fe1673e, and complete 265e50a6ddd7afe0b06a0f337ad77c14b00c3b69b0b7084337ea79a842811359
checks: The clean package generator passed deterministic repeated capture/lower/link, five native-Lean/Wasm dispatcher cases at all ten compression levels, zero-import complete-runtime adapter checks, persistent-cache plus scratch-checkpoint reclamation, package smoke, SHA256SUMS verification, and a second package smoke from the canonical directory. After rebasing on the isolated setTag production contract at 49b56a0d, git diff --check passed; make check passed 125 harness tests, 701 native/LCNF cases, 9 direct-machine cases, 701 native/LCNF/V8 cases, 710 unique cases, and 2,112/2,112 comparisons; bug-card, trusted-assumption, and 25 mailbox tests passed. make talos-check passed 3,148 jobs. bash integration/talos/artifact/check.sh passed all resident standalone checks, deterministic prettyM generation, Node clients, the 701-case V8 triangle, 640 executable concrete cases with the existing 61 ByteArray exclusions, and deterministic concrete artifacts. Main then accepted only the corresponding W6 constructor-tag admission theorem, explicitly changing no generation surface; W7 rebased cleanly on that accepted 5ad696a9 checkpoint. Clean package publication at branch head bac1a428 reproduced byte-identical base, frontier, and complete Wasm hashes, and final canonical checksum/smoke verification passed
bug-cards: FIR-BUG-wasm-none-lean-zip-raw-cache-isolation-ratchet (fixed); FIR-BUG-wasm-none-array-panic-observation remains open and is being audited by test-fixtures through W7-FIX-20260814-001
blockers: none
handoff: Integration may fast-forward functional commit 9213e239 followed by the containing status commit after resolving the actual wasm/generation branch head. The branch is rebased directly on main 5ad696a9. Immutable package: integration/lean-zip/_build/lean-zip-raw-packages/bac1a4282f87-30737b4e2ebf-bdafe20f52c1c053266a. Canonical pointer: integration/lean-zip/_build/lean-zip-raw-current. Complete Wasm: 902,411 bytes, SHA-256 d3992d5b5e5a4bd11edb93f48e0b95fbc2148a1c0b7c87b395d208e4a61e44cc, zero function imports, zero memory imports, module-owned memory. Exports: Zip.Wasm.compressRaw, fir_heap_frontier, fir_heap_set_frontier, fir_heap_rewind, fir_heap_alloc, and memory. Base Wasm: 1,050,780 bytes, SHA-256 1e6a69b445c22f2fd8a273fb66331645f2dca5a7b98ad1c92a8c9b060df687fb. Frontier Wasm: 1,570,637 bytes, SHA-256 705e4c0a044d22c5877c0faaf8d9b2738011e2dbab2803d9abbb00a349d31b08
next: Integrate this closure/package ratchet. Then consume the fixture lane's focused Array observation result and design the recoverable panic-observation mechanism without replacing Lean's observable panic/default path with a Wasm trap. The next independent generation-infrastructure item is thin checksum/installer extraction shared by immutable packages; do not broaden it into a coordination framework
```
