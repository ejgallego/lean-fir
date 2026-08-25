# wasm-gen lane

The forward-looking W7 plan lives in
[`Fir/Wasm/Emit/ROADMAP.md`](../../Fir/Wasm/Emit/ROADMAP.md). Accepted milestone
history remains on `coordination/BOARD.md`; this mailbox records the current
single-writer W7 handoff.

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: 913c25523698853cca66491e71f82e0bc7fc5545
functional-head: 3e0eef6119b34ae9e1008bafeeaf01b807b6888f
contract-base: 913c25523698853cca66491e71f82e0bc7fc5545
clean-at-update: true
slice: Align the exclusive-reuse ByteArray.pushUInt64LE path with Lean's native wide push. After prepareAppend establishes uniqueness and capacity, eight-byte-slack inputs use one unaligned i64.store; tight-capacity inputs retain the byte loop so no write crosses the logical allocation. Zero-count, shared, growth, and later-overwrite behavior is unchanged. Executable commit 158914b8fabbacb665113b3fc0f9ebd0b21ad893; exact Level-1 package ratchet 3e0eef6119b34ae9e1008bafeeaf01b807b6888f.
files: Fir/Wasm/Emit/ResidentByteArray.lean; integration/lean-zip/README.md; integration/lean-zip/raw-closure-contract.json; integration/lean-zip/level1-closure-contract.json; coordination/lanes/wasm-gen.md
contracts: No helper signature, public checked behavior, ABI/layout, symbolic instruction surface, ownership contract, import frontier, or flat-rewind contract changed. The optimization is confined to the existing exclusive reuse branch and requires at least eight bytes of physical slack. W6-owned files are untouched.
checks: Lean Beam update/sync/save passed on the exact W7 source with zero diagnostics, source hash 409a97ee8c33a529. lake build +Fir.Wasm.Emit.ResidentLinker passed 54/54 jobs. Focused cases cover counts zero through eight, tight/slack capacity, shared input, growth, and later logical pushes overwriting slack. git diff --check and make check passed: 726 unique cases, 2160/2160 comparisons equal, zero findings. make talos-check passed 3172 jobs. bash integration/talos/artifact/check.sh passed the resident modules, deterministic prettyM/package/browser stack-safety checks, 726-case native/LCNF/V8 evidence cone, and concrete-host suite. The clean canonical stored package is 12418 bytes, SHA-256 3343c2d1c2656c19ceac6c19a6c7cca0162f96e6d28929999f70dba465e6a8f0, zero imports. The clean Level-1 package is 193694 bytes, SHA-256 d10bb3960160639a44cb4555529dfe86c38de39cfaf82fa9585b5b68113cc123, zero imports, and passed Node/native, reclamation, and Chrome. The clean raw levels 1-10 package is 367201 bytes, SHA-256 58abc76b8269b6aec529cc317b0cf71adf3f350ac1fadf328955b6131e5528b3, sidecar SHA-256 d03a2c9f5ad7cc8a6a2629a2d671b3424f54119809cc0c28072955489babd7e9, 501 final functions, zero imports, 630 source functions, and 830 resident helpers; its 5 cases times 10 levels, persistent-cache, scratch-reclamation, sidecar, and smoke gates passed. Diagnostics-off 32-pair AB/BA timing measured baseline 38.267ms median (MAD 1.365) versus candidate 38.007ms (MAD 1.883), paired median -0.143ms (-0.37%), 19/32 wins; both halves and both orders remained negative. Exact-artifact sampled self share for fir_ext_ByteArray_pushUInt64LE fell from 3.04% to 2.51%. This is accepted as a small targeted win, not a broad speedup; raw Wasm grew 25 bytes and Level-1 grew 33 bytes.
bug-cards: none
blockers: none. Cached replay diagnostics retain historical /tmp/fir-lean-zip paths, but every active source view, scratch directory, and publication path for these checks is worktree-local under .deps or _build.
handoff: Fast-forward 3e0eef6119b34ae9e1008bafeeaf01b807b6888f and this clean lane-status commit onto main. Canonical packages are lean-zip-stored-current -> 3e0eef6119b3-273d0d6cd9ca-b1e5964729f386597069, lean-zip-level1-current -> 3e0eef6119b3-273d0d6cd9ca-aab683ae39e24ea2f45a, and lean-zip-raw-current -> 3e0eef6119b3-273d0d6cd9ca-816ba6680b87ab2ba0d5. W6's active committed and dirty delta is confined to integration/talos/FirTalos proof files, so it does not overlap this checkpoint.
next: After integration, rebase the acknowledged W72-W7-20260825-007 successor onto accepted main and measure the upstream-shaped trusted Array.set! scalar index dispatch. Separately queue W6 refinement of the stable wide-push reuse/slack invariant without blocking generation acceptance.
```
