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
base: b52710d268a1126c505ccfb41f8ed6e0be92e2b4
functional-head: de2ee5bbf13ab5f217c24e2e064c1dcd3d2f489d
contract-base: b52710d268a1126c505ccfb41f8ed6e0be92e2b4
clean-at-update: true
slice: Make ordinary lean-zip raw publication single-pass. One final-LCNF capture/lower now produces an immutable source-only ModuleArtifact; the reviewed resident frontier is linked from that exact value, and external libm closure then produces the complete module. The separate opt-in determinism command retains the diagnostic probe and byte-for-byte double-generation gate. Monotonic phase timings are reported outside BUILD.json. The change removes redundant ordinary capture, probe, and regeneration work without introducing a generalized build cache.
files: integration/lean-zip/LeanZipFir/Compile.lean; integration/lean-zip/EmitRaw.lean; integration/lean-zip/package-raw.mjs; integration/lean-zip/check-raw-determinism.mjs; integration/lean-zip/check.sh; integration/lean-zip/README.md; integration/lean-zip/raw-closure-contract.json; bugs/FIR-BUG-wasm-none-repeated-final-capture-code-shape.md; coordination/lanes/wasm-gen.md
contracts: No source semantics, ABI/layout, ownership/reclamation policy, runtime helper signature or implementation, symbolic Wasm instruction surface, import frontier, or public export changed. The reusable API only exposes compilation of an already captured artifact and pure linking of an immutable ModuleArtifact. W6-owned files are untouched.
checks: git diff --check passed. JS syntax and six exporter unit tests passed. lake --keep-toolchain build LeanZipFir.Compile passed 104 jobs. The Lean Beam wrapper was attempted for both changed Lean files but rejects the nested integration/lean-zip project because it inherits the parent toolchain and has no local lean-toolchain; direct focused Lake builds and complete gates passed. make bug-cards passed with 201 active cards. make check passed: 726 unique cases, 2160/2160 comparisons equal, zero findings, 9077 steps, and 26 mailbox tests. make talos-check passed 3172 jobs. bash integration/talos/artifact/check.sh passed the full resident-helper, deterministic prettyM/package/browser stack-safety, 726-case native/LCNF/V8 evidence, and concrete-host cones. integration/lean-zip/check.sh passed stored/Level-1 double generation, Node/native differentials, ownership, and Chrome. The explicit node check-raw-determinism.mjs gate passed byte-for-byte equality for the frontier, complete Wasm, descriptor, libm runtime, and sidecar. The clean-producer fresh-output catalog export passed 5 cases times 10 levels, independent inflate, zero-import adapter, persistent-cache scratch reclamation, complete checksums, and repeated package smoke. Ordinary baseline was 165226.498ms; candidate preview was 45974.094ms (72.2% lower, 3.59x throughput), and the clean fresh-output run was 43407.209ms. Explicit diagnostic/determinism mode remains 142824.191ms. These are build-path timings, not generated-code runtime claims.
bug-cards: FIR-BUG-wasm-none-repeated-final-capture-code-shape. The former same-process second capture selected a different optimized body shape despite identical 501 names/indices/callees/origins and identical semantics/ABI/import inventory; generic capture reproducibility remains a follow-up. The package avoids the issue architecturally and fresh-process determinism is green.
blockers: none. Cached Lake replay warnings retain historical /tmp/fir-lean-zip paths, but every active source view, temporary directory, preview, export, and publication path used here is worktree-local under .deps or _build.
handoff: Fast-forward this clean lane-status commit, whose functional head is de2ee5bbf13ab5f217c24e2e064c1dcd3d2f489d, onto main. The immutable canonical package is integration/lean-zip/_build/lean-zip-raw-packages/de2ee5bbf13a-273d0d6cd9ca-6e69245675f168587ab4 and lean-zip-raw-current points to it. Final Wasm is 366826 bytes, SHA-256 d08fc73e1da024a8c03d1034a6becf4568c31aa4a95505cf4fc43b5169fa0c18; sidecar is 207604 bytes, SHA-256 1e05a4c01b1d9b305e2e48930c3ba0e86696b4a004b79e6aec9a1fb42c9608be; 501 final functions, zero function and memory imports, 630 source functions, and 830 resident helpers. The complete Wasm is 375 bytes smaller than the historical redundant-second-capture shape.
next: Minimize the generic same-process capture reproducibility defect separately. After integration, consume the independently acknowledged W7-2 Array.set! candidate only from its exact clean handoff; it does not overlap this build-path slice.
```
