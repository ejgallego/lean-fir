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
state: active
base: 515bf4017867001cbdee41c07b0f95a534d218e1 on main
functional-head: 1d79658dbcc14bdc1fbd5e210086c82843bc9cd0, already accepted on main; this checkpoint changes roadmap/coordination only
contract-base: 515bf4017867001cbdee41c07b0f95a534d218e1 on main. No shared semantic, concrete-runtime, symbolic-Wasm, ownership, helper-signature, or package contract changes
clean-at-update: true
slice: Refresh the W7 roadmap after generic Array acceptance and the successful lean-zip raw levels 1--10 package. Treat realistic exact-source compilation feasibility as established; focus the next phase on generic compiler quality, compactness, production adapter overhead, and a thin reusable package surface. Retire completed Flat, HTML, HitScene, SpatialHitScene, Array, and raw-runtime frontier requests from the active queue. Park static simple-ground images on their named experiment branch, with explicit future alignment to Lean upstream SimpleGroundExpr
files: Fir/Wasm/Emit/ROADMAP.md; coordination/lanes/wasm-gen.md
contracts: none
checks: documentation-only checkpoint; git diff --check and make check pass on the exact branch head
bug-cards: none
blockers: none
handoff: none; this is the active W7 queue, not an integration request
next: G1 integrate the already-green closure allocator consolidation from branch wasm/closure-allocation-consolidation through 052866ca, notify W6 of the future emitted-helper signature surface, then regenerate and publish stored/Level-1/raw lean-zip packages from accepted main. G2 split Illuminate production dispatchTick from diagnostic dispatchTickTimed. G3 extract only the verifier/atomic-installer and descriptor/codec behavior proven across at least two accepted packages. G4 continue generic runtime expansion only when a real exact-source closure reaches a new operation. Static simple-ground images remain parked at wasm/simple-ground-image-experiment/23589d5a until reprioritized by profiling
```
