# wasm-gen lane

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: a5d8422ff1190ef8d05015da9ee6c9522dd347b1 on main
functional-head: 66125259f08b67c9813041899c7434777dbbca2c
contract-base: a5d8422f on main; consumes the linked Illuminate Talos instruction adaptation
clean-at-update: true
slice: Separate linker-visible helpers from the production browser ABI: add checked pruneToExports reachability pruning, restrict Illuminate to replayTraceNative plus frontier/set-frontier/allocate, embed exact retained source/resident inventories in BUILD.json, and reduce the same 84-declaration zero-import module from 50,237 to 40,922 bytes while reducing function exports from 196 to 4
files: Fir/Wasm/Emit/ResidentDeadCode.lean; integration/illuminate-player/IlluminateFirNative/Compile.lean; integration/illuminate-player/Emit.lean; integration/illuminate-player/package.mjs; integration/illuminate-player/package-smoke.mjs; integration/illuminate-player/smoke.mjs; integration/illuminate-player/README.md; this mailbox
contracts: none; standalone resident-helper fixtures retain their historical exported test surfaces, while production consumers may only hide existing exports and cannot promote an internal declaration
checks: PASS Lean Beam update/sync with zero diagnostics for ResidentDeadCode, Illuminate Compile, and Emit; PASS focused lake build Fir.Wasm.Emit.ResidentDeadCode; PASS immutable Lean 4.32 Illuminate source snapshot build for Compile and Examples; PASS zero-import 40,922-byte V8 smoke with exactly 4 function exports plus module memory; PASS 105/105 legacy-JS/FIR-native traces; PASS deterministic double package publication, package smoke, and SHA256SUMS; PASS JavaScript syntax checks; PASS git diff --check; PASS make check (642 unique cases, 1,844/1,844 comparisons equal, 104 bug cards, trusted-assumption gate); PASS make talos-setup and make talos-check after W6 landed; PASS complete bash integration/talos/artifact/check.sh including deterministic double source/styled generation, production browser adapter stack-safety stress, 601/601 native/LCNF/V8 cases with 1,803/1,803 comparisons, and 44/44 concrete readiness artifacts
bug-cards: none
blockers: none; the live Illuminate checkout has independently moved to PlayerAnimation/prepare and requires a later compilation-boundary adaptation before canonical repackaging, while this slice was measured against the immutable accepted 84-declaration source snapshot
handoff: ready for the integration owner to fast-forward the rebased W7 stack through functional head 66125259 and this containing mailbox commit onto main
next: after integration, rebase wasm/generation on main and adapt the package boundary to Illuminate.AnimationPlayer.replayTrace over PlayerAnimation, omitting synchronization SVG and encoding PatchTarget directly
```
