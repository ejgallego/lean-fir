# wasm-gen lane

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: waiting
base: a5d8422ff1190ef8d05015da9ee6c9522dd347b1 on main
functional-head: 66125259f08b67c9813041899c7434777dbbca2c
contract-base: a5d8422f on main; consumes the linked Illuminate Talos instruction adaptation
clean-at-update: true
slice: Separate linker-visible helpers from the production browser ABI: add checked pruneToExports reachability pruning, restrict Illuminate to replayTraceNative plus frontier/set-frontier/allocate, embed exact retained source/resident inventories in BUILD.json, and reduce the same 84-declaration zero-import module from 50,237 to 40,922 bytes while reducing function exports from 196 to 4
files: Fir/Wasm/Emit/ResidentDeadCode.lean; integration/illuminate-player/IlluminateFirNative/Compile.lean; integration/illuminate-player/Emit.lean; integration/illuminate-player/package.mjs; integration/illuminate-player/package-smoke.mjs; integration/illuminate-player/smoke.mjs; integration/illuminate-player/README.md; this mailbox
contracts: none; standalone resident-helper fixtures retain their historical exported test surfaces, while production consumers may only hide existing exports and cannot promote an internal declaration
checks: PASS Lean Beam update/sync with zero diagnostics for ResidentDeadCode, Illuminate Compile, and Emit; PASS focused lake build Fir.Wasm.Emit.ResidentDeadCode; PASS immutable Lean 4.32 Illuminate source snapshot build for Compile and Examples; PASS zero-import 40,922-byte V8 smoke with exactly 4 function exports plus module memory; PASS 105/105 legacy-JS/FIR-native traces; PASS deterministic double package publication, package smoke, and SHA256SUMS; PASS JavaScript syntax checks; PASS git diff --check; PASS make check (642 unique cases, 1,844/1,844 comparisons equal, 104 bug cards, trusted-assumption gate); PASS make talos-setup and make talos-check after W6 landed; INTERRUPTED bash integration/talos/artifact/check.sh during the known long prettyM source-capture phase after all resident standalone and source dependency-cone stages reported green, with no failure diagnostic
bug-cards: none
blockers: complete the required artifact/check.sh determinism cone during a lower-contention window before integration; the live Illuminate checkout has independently moved to PlayerAnimation/prepare and requires a later compilation-boundary adaptation before canonical repackaging, while this slice was measured against the immutable accepted 84-declaration source snapshot
handoff: none until artifact/check.sh completes; functional commits 30fdbbef and 66125259 are rebased on current main and otherwise green
next: rerun bash integration/talos/artifact/check.sh to completion, change this mailbox to ready, then separately adapt the package boundary to Illuminate's finalized PlayerAnimation preparation API
```
