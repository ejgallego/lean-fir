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
base: 34f75084a04374239dea877ff4a22413dd4fae8d
functional-head: 32ac281efc9ef6baa3bbf97f9368b489045e0f94
contract-base: 34f75084a04374239dea877ff4a22413dd4fae8d
clean-at-update: true
slice: Align the trusted final-LCNF `Array.set!` index boundary with upstream `lean_array_set`. Checked/public callers retain full arbitrary-width Natural validation. Trusted callers test the immediate tag, decode scalar indices directly, and treat every heap Natural as out of bounds, which is exact for a wasm32-resident Array. The common out-of-bounds path still consumes the replacement and returns the original Array; unique reuse and shared copy-on-write are unchanged. This was accepted for upstream fidelity and smaller code shape despite elapsed effect below benchmark resolution.
files: Fir/Wasm/Emit/ResidentArray.lean; integration/talos/artifact/resident-array-client.mjs; integration/lean-zip/README.md; integration/lean-zip/raw-closure-contract.json; coordination/lanes/wasm-gen.md
contracts: No public checked behavior, helper signature, semantic ABI, layout, ownership/reclamation rule, symbolic Wasm instruction surface, import/export frontier, or source semantics changed. The trusted body consumes the same final-LCNF representation premise already used by other proof-indexed Array paths. W6-owned files are untouched; the W6 installed decrement proof stack landed first at main 34f75084.
checks: Lean Beam update/sync/save and post-rebase refresh/save passed ResidentArray.lean with zero diagnostics, source hash 5a1d2ad8bad4c0e7. The focused 20-job ResidentArray cone passed. The zero-import resident trusted module directly passed scalar in-bounds, scalar out-of-bounds, heap-Nat, unique reuse, shared copy-on-write, and replacement-release cases. git diff --check passed. make check passed: 726 unique cases, 2160/2160 comparisons equal, zero findings, 9077 steps, 201 active bug cards, and 26 mailbox tests. make talos-setup selected Talos 0e05edbc and make talos-check passed 3172 jobs. bash integration/talos/artifact/check.sh passed the full resident-helper including the new Array path, deterministic prettyM/package/browser stack-safety, 717-case native/LCNF/V8 evidence, and concrete-host cones. The explicit lean-zip determinism gate reproduced the frontier, complete Wasm, descriptor, libm runtime, and sidecar byte-for-byte. The clean canonical package passed 5 cases times 10 levels against native Lean and independent inflate, zero-import adapter, persistent-cache scratch reclamation, sidecar, checksums, and smoke.
bug-cards: none. This is an upstream implementation-alignment slice, not a semantic discrepancy or workaround.
blockers: none. Cached Lake replay warnings retain historical /tmp/fir-lean-zip paths, but every active source view, temporary directory, preview, export, and publication path used here is worktree-local under .deps or _build.
handoff: Fast-forward this clean lane-status commit, whose functional head is 32ac281efc9ef6baa3bbf97f9368b489045e0f94, onto main. The immutable canonical package is integration/lean-zip/_build/lean-zip-raw-packages/32ac281efc9e-273d0d6cd9ca-f904e7a2c47ac02feefb and lean-zip-raw-current points to it. Final Wasm is 366796 bytes, SHA-256 7bd29a5a617d238ff8f3edbc037368ea4c5bb7fa2f4694955b5e3da3ed7fa048; sidecar is 207591 bytes, SHA-256 d418e63c5220eab99f5327d4d5589d6613abd0c16e5c6d9d4e2ef985ce9c1b98; 501 final functions, zero function and memory imports, 630 source functions, and 830 resident helpers. The helper shrinks from 407 to 377 bytes and the complete module by 30 bytes. Prior diagnostics-off timing was neutral (+0.17ms paired median, 14/32 wins), so no runtime-speed claim is made.
next: After integration, acknowledge W7-2 thread W72-W7-20260825-011 and require its fixed-width i64 experiment to rebase onto this accepted main before any ResidentFixedWidth edit. Separately retain the generic same-process capture reproducibility minimization as non-blocking generator debt.
```
