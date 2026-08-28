# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: cdaf6709301bba04909e52c699e0fe1a80e65b1a
functional-head: 846ba8f0d914f39aab2a692dcefc828a5cbee428
contract-base: cdaf6709301bba04909e52c699e0fe1a80e65b1a
clean-at-update: true
slice: Complete authoritative mailbox thread W7-W6-20260826-022 for the actual installed fir_float32_box, fir_float32_unbox, fir_float_box, and fir_float_unbox bodies. Commit 4ad364ee proves exact installed unboxing, including caller-tail preservation, exact raw-bit recovery, Float32 padding checks, pointer/alignment/tag guards, and eventual traps for malformed inputs. Commit 846ba8f0 proves exact installed boxing from allocateBoxedScalar admission through fresh-zero initialization, canonical six-word header construction, Float32 zero-extended payload storage, Float 64-bit payload storage, returned object identity, exact final store, exact trace, and arbitrary caller-tail preservation. The reusable proof boundary factors common allocation, zero-store, header-write, retyping, page-preservation, and physical-memory refinement facts rather than certifying reconstructed helper examples.
files: integration/talos/FirTalos/ConcreteResidentFloat.lean; coordination/lanes/wasm-proof.md
contracts: No shared contract changed. These are proof-only refinements of the production W7 helper bodies already accepted on main. Helper names, signatures, instructions, concrete layout, ownership, allocator semantics, source semantics, and artifacts are unchanged.
checks: Lean Beam update/sync/save passed with zero diagnostics for the final source. Forced lake build FirTalos.ConcreteResidentFloat FirTalos passed all 3,177 jobs. git diff --check passed. make check passed with 730 unique validation cases, 2,172/2,172 comparisons equal, zero findings, 211 active bug cards, and 38 mailbox tests. make talos-setup completed at Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254. make talos-check passed all 3,177 jobs with exact receipt a319034b03a07f556b79923f0f55aeb01162670a60428622a7489b8e63433c87.
bug-cards: none
blockers: none
handoff: GREEN LIGHT. Fast-forward main from cdaf6709301bba04909e52c699e0fe1a80e65b1a through 4ad364ee and 846ba8f0 plus this containing status commit. This closes W7-W6-20260826-022 and gives W7 the requested installed-helper proof checkpoint.
next: Rebase on accepted main, reassess the canonical W6 mailbox, and take the highest-priority remaining resident-runtime refinement request. The likely candidates are the trusted Array fast-path refinement and fixed-width natural boxing; priority is determined from the current authoritative mailbox rather than this snapshot.
```
