# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: b4b33102 on main
functional-head: none yet
contract-base: b4b33102 on main; ranked finite-trace simulation boundary is linked/accepted; no shared semantic or runtime contract is queued
clean-at-update: true
slice: Define a structured resumable Wasm configuration for the emitted subset and prove finite terminating adequacy to Talos Wasm.run, preserving the state needed by the ranked finite-prefix simulation rather than treating OutOfFuel as resumable
files: coordination/lanes/wasm-proof.md; anticipated proof-owned modules under integration/talos/FirTalos/Correctness/ and integration/talos/FirTalos/
contracts: none anticipated; this slice should relate proof-local structured execution to the existing Talos evaluator without changing source semantics, symbolic Wasm instructions, concrete runtime layout, resident helpers, or artifacts
checks: pending; Lean edits will use Lean Beam, followed by the focused dependency cone, git diff --check, make check, make talos-setup, and make talos-check
bug-cards: none
blockers: none
handoff: none; active slice
next: Inspect the Talos evaluator state/result surface, choose the smallest faithful emitted-subset configuration, and prove its terminating-run bridge before compiler instantiation
```
