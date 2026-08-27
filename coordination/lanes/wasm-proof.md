# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 1aba4be61551b8d5bcc28f5ace3f29b71c3b91ac
functional-head: 7aaa5c420cd124c75e68e4c90e445fbf27d95d2f
contract-base: 1aba4be61551b8d5bcc28f5ace3f29b71c3b91ac
clean-at-update: true
slice: Completes the exact scalar-alias proof bridge requested in W7-W6-20260826-021. One result-kind-parametric UInt16 adapter theorem proves that generic fir_box_uint16 and production fir_box_uint16_tagged compile to the same physical i32 program; uint16ImmediateWord_physical identifies that program's arithmetic result with the canonical concrete tagged word. One generic exact-alias installation boundary factors signature, installed-body, resolver, and terminal reasoning. Production fir_box_uint64_object compiles to the same heap-only allocator program as generic fir_box_uint64, and the unconditional installed-call theorem reuses the generic allocator and heap refinement to return the exact address, establish UInt64BoxAdmission, preserve ResidentAllocatorRel, and preserve caller operand slack. No compiler certificate or duplicated heap proof is introduced.
files: integration/talos/FirTalos/ConcreteResidentScalarBox.lean; coordination/lanes/wasm-proof.md
contracts: Additive W6 proof interface over accepted W7 closed alias-body equations at main 1aba4be6. The production UInt16 tagged and UInt64 object aliases are now connected to their generic physical programs and installed concrete-runtime refinements. No source semantics, LCNF lowering, emitter instruction, helper signature, semantic ABI, concrete layout, allocator, ownership rule, symbolic Wasm surface, artifact, or compiler behavior changed.
checks: After final rebase onto main 1aba4be6, Lean Beam update/sync/save passed with zero diagnostics for FirTalos/ConcreteResidentScalarBox.lean. lake -d integration/talos build FirTalos.ConcreteResidentScalarBox passed all 3,125 jobs. git diff --check passed. make check passed with 721/721 source cases, 9/9 direct-machine cases, 730 unique cases, 2,172/2,172 comparisons equal, zero findings, 211 active bug cards, and 38 mailbox tests. make talos-setup completed at Talos 0e05edbc. make talos-check passed all 3,174 jobs with receipt 9d66f0097a1a3db967f21944d7a1211aa237ae9290ef39cf622c6dd92460e7cc.
bug-cards: none
blockers: none
handoff: GREEN LIGHT. Consume the exact clean integration checkpoint published by the completion event in authoritative mailbox thread ROOT-W6-20260827-002. It is based directly on main 1aba4be6, has functional head 7aaa5c42, changes only the W6-owned Talos proof module plus this mailbox, and passes every required W6 gate.
next: Integrate this exact scalar-alias proof checkpoint promptly; after landing, reassess the open wasm-proof mailbox and select the next independent proof slice.
```
