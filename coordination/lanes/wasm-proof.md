# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 56d1c09c on main
functional-head: none yet
contract-base: 56d1c09c on main; ranked finite-trace, instruction-boundary adequacy, and emitted frame-collapse laws are linked/accepted; no shared semantic or runtime contract is queued
clean-at-update: true
slice: Define the explicit emitted-subset frame-stack state and small-step relation; expose primitive progress, call/block/loop/conditional entry, normal frame exits, loop restart, returns through nested structured frames, and outward branch propagation; relate its store observation to the concrete ranked trace machine
files: coordination/lanes/wasm-proof.md; anticipated proof-owned state/transition modules under integration/talos/FirTalos/Correctness/ and concrete packaging under integration/talos/FirTalos/
contracts: none anticipated; adds proof-local target semantics without changing shared source semantics, symbolic Wasm instructions, Talos, concrete runtime layout/operations, resident helpers, or artifacts
checks: pending; Lean edits will use Lean Beam, followed by focused/umbrella builds, git diff --check, make check, make talos-setup, and make talos-check
bug-cards: none
blockers: none
handoff: none; active slice
next: Implement the frame/state grammar first, prove store exposure and the administrative progress rules, then add the terminal-collapse theorem in a separate checked layer
```
