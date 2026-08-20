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
base: 54165c6a on main
functional-head: 1b1668f1, publish provider-free Illuminate full-action and selection players
contract-base: 54165c6a. No Lean semantic, Wasm ABI, resident-helper, symbolic-module, or proof contract changed. The package-local ownership capability advances from persistent-checkpoint/v2 to /v3 and replaces fir.standard-math/v1 reservation metadata with fir.closed-resident-runtime/v1: provider none, source-compiled Float.ofNat and Float.ofScientific, zero external declarations, exact 1024-byte module heap base
clean-at-update: true
slice: The real Illuminate full-action and selection source closures now consume FIR's generic final-LCNF source compilation of upstream Float.ofNat and Float.ofScientific. Both resident modules are already import-free before packaging. Packaging no longer compiles or links the bounded C math provider; a generic closed-module optimizer performs fail-closed Binaryen cleanup without adding a provider or temporary directory. Both adapters require the exact module-owned 1024-byte heap base instead of reserving and skipping the first 65536 bytes. Public methods, structured Lean entries, exports, bit-exact timestamp lane, copied outputs, persistent checkpoint, and disposal behavior remain unchanged
files: integration/illuminate-player/README.md; integration/illuminate-player/check-player-traces.mjs; integration/illuminate-player/illuminate-player-browser-adapter.mjs; integration/illuminate-player/illuminate-selection-player-browser-adapter.mjs; integration/illuminate-player/package-smoke.mjs; integration/illuminate-player/package.mjs; integration/illuminate-player/selection-package-smoke.mjs; integration/illuminate-player/selection-package.mjs; integration/illuminate-player/selection-smoke.mjs; integration/illuminate-player/smoke.mjs; integration/wasm-runtime/README.md; integration/wasm-runtime/optimize-closed-module.mjs; coordination/lanes/wasm-gen.md
contracts: Full-action BUILD schema v2 and selection BUILD schema v3 carry complete-runtime/v2 plus fir.closed-resident-runtime/v1. Full-action retains exactly six function exports; selection retains exactly seven; both export module memory and have zero function and memory imports. Full-action source inventory is 212 declarations, 168 retained source functions, and 302 resident helpers. Selection inventory is 224 declarations, 177 retained source functions, and 320 resident helpers. Both retain one allocator global, zero lazy-cache initializers, and zero runtime operations. The upstream arbitrary-precision Float model raises the full-action 10000-tick bounded scratch delta from 704 to 4232 bytes; every dispatch still clears and rewinds to the exact checkpoint. Selection's production scalar tick remains allocation-free on the host and its Wasm scratch delta remains 552 bytes
artifacts: clean functional producer 1b1668f1 against clean Illuminate 6f16cdc3d432. Full-action immutable package integration/illuminate-player/_build/illuminate-player-packages/1b1668f141c1-6f16cdc3d432-649acf33a55a7a9ad692 is 37287 bytes at SHA-256 25e3f3ec476b7bb9cc650d89b3664c1a55880b44fde54576078278f5e2e87643. Selection immutable package integration/illuminate-player/_build/illuminate-selection-player-packages/1b1668f141c1-6f16cdc3d432-c77c697acc666adda3b5 is 40398 bytes at SHA-256 9a5364ac0e4f78559f29089e9005820c9a9246850d1d19d04ba35671e997eefd. Canonical pointers are illuminate-player-current and illuminate-selection-player-current
checks: All commands used TMPDIR under the worktree's ignored .deps and no /tmp dependency. The complete Illuminate check passed: six exporter tests, focused Lean cones, deterministic double publication, source and packaged checksums/smokes, 10000-call flat-frontier tests, all six events, bit-exact scalar ticks, and 107 legacy/full-action/selection traces equal. git diff --check PASS. make check PASS 704 source cases, nine direct machines, complete 704-case V8 triangle, 713 unique cases, 2121/2121 comparisons equal, zero findings, 188 active bug cards, and 25 mailbox tests. make talos-setup PASS at Talos 0e05edbc; make talos-check PASS 3162 jobs. bash integration/talos/artifact/check.sh PASS, including deterministic source-Float, libm, resident, prettyM, V8, and concrete readiness gates
bug-cards: none
blockers: none
handoff: Integration resolves the containing clean branch head after this tracked status commit and may fast-forward main. Functional head 1b1668f1 is based directly on 54165c6a. No W6-owned file changed and no external package publication is authorized
follow-up: Audit and migrate HitScene and SpatialHitScene from the legacy standard-math provider, preserving their genuine libm frontier where needed. Once the consumer scan is empty, retire fir.standard-math/v1 while retaining standard-libm/v2 for opaque platform libm operations
```
