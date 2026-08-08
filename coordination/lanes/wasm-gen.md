# wasm-gen lane

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: aecae9a404cab3e90cdbd6cfb02d23732bfe785d on main
functional-head: 2dc72b812f890213f4f4739b42635963425ebf45
contract-base: aecae9a4 on main; no shared contract changed
clean-at-update: true
slice: Capture Lean's final impure LCNF specialization closure without entering IR; compile the real Illuminate.AnimationPlayer.replayTrace and its 25 generated specializations; remove the handwritten Illuminate transition linker; internalize the newly exposed generic Array/USize/Nat.shiftRight runtime edges; and publish a deterministic, module-owned, zero-import package with exactly the structured entry and three frontier/allocator exports
files: Fir/Wasm/Emit/CompilerPrivate.lean; Fir/Wasm/Emit/Source.lean; Fir/Wasm/Emit/ResidentArray.lean; Fir/Wasm/Emit/ResidentUSize.lean; Fir/Wasm/Emit/ResidentNatShift.lean; integration/illuminate-player/IlluminateFirNative/Compile.lean; integration/illuminate-player/README.md; integration/illuminate-player/package.mjs; bugs/FIR-BUG-wasm-none-illuminate-action-at-admission.md; bugs/FIR-BUG-wasm-none-illuminate-private-specialization-closure.md; bugs/FIR-BUG-wasm-none-illuminate-captured-specialization-object-kinds.md; this mailbox
contracts: none; new generation-ready resident helper signatures are Array.ugetBorrowed [erased,object,usize,erased] -> object, USize.decLt [usize,usize] -> uint8, USize.add [usize,usize] -> usize, and Nat.shiftRight [tobject,tobject] -> tobject; W6 refinement proofs are a separate follow-up and are not claimed here
source: Illuminate 006dc1d1db18c5dc73d637c926cf132e88df05b5, dirty solely because src/Illuminate/Animation/Player.lean is untracked; Types.lean sha256 97a030fdd3ef718912479343cadf0131616a8a9b458901e963dc3709cf5633a3; Player.lean sha256 3ed87ac8d6a21c0afb2b00efcde6f5390c47be336c09214c24ead847bdb4f306; exact source compiles under FIR's Lean 4.32 read-only source view
artifact: integration/illuminate-player/_build/illuminate-player-packages/2dc72b812f89-006dc1d1db18-c41154362d40223074bb; canonical pointer integration/illuminate-player/_build/illuminate-player-current; complete Wasm 53888 bytes sha256 24a41cef9f6f9cdeace44b544e0cc2c635750ad94fb788aa3e60bf8876afc785; base Wasm 21977 bytes sha256 34b24b1a49c321c47f964d5e9992a4dcefc5a020d1264fb1f305dff3fba8f096; 0 function imports; 0 memory imports; module-owned memory; exactly 4 public functions and 253 internal functions; 115 final-LCNF declarations; 73 retained source functions; 25 captured generated specializations; 184 resident helpers; no fir_illuminate_* handwritten resident functions; unresolved runtime operations none
checks: PASS Lean Beam update/sync/save with zero diagnostics during Lean iteration; PASS focused Lean 4.32 Illuminate source-view build; PASS post-rebase deterministic Illuminate package gate with two identical publications, stable package ID and Wasm digest, complete SHA256SUMS, 11-call packaged smoke, and 105/105 local legacy/FIR traces; PASS git diff --check; PASS post-rebase make check (642 unique cases, 1844/1844 comparisons equal, 106 active bug cards, trusted-assumption gate); PASS make talos-setup; PASS post-rebase make talos-check (3125 jobs); PASS post-rebase bash integration/talos/artifact/check.sh including deterministic source/prettyM emission, zero-import resident checks, packaged browser adapter, stack-safety stress, semantic-engine matrix, and concrete readiness cone
bug-cards: FIR-BUG-wasm-none-illuminate-action-at-admission (fixed); FIR-BUG-wasm-none-illuminate-private-specialization-closure (fixed); FIR-BUG-wasm-none-illuminate-captured-specialization-object-kinds (fixed)
blockers: none
handoff: ready for the integration owner to fast-forward functional head 2dc72b812f890213f4f4739b42635963425ebf45 and this containing mailbox commit onto main
next: persistent-player W7 slice will compile Illuminate.AnimationPlayer.initialLive and transitionLive, retain one encoded animation per module instance below a checkpoint, and rewind per-dispatch scratch memory; W6 may independently prove the four new resident helper contracts
```
