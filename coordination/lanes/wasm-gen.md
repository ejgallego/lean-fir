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
state: ready
base: 300f8ab8 on main
functional-head: 4b84f35b, export the accepted Illuminate selection package through the generic caller-owned catalog boundary and refresh its linked resident-Array ratchets
contract-base: 300f8ab8 on main. Consumes the accepted proof-indexed resident Array implementation and existing Illuminate selection adapter API v5 / hot-event v2. Changes no source semantics, production validation, concrete layout/runtime contract, symbolic-Wasm instruction, ownership rule, resident-helper signature, adapter ABI, input layout, or W6 theorem surface
clean-at-update: true
slice: Add an executable generic package command for the existing Illuminate selection player. The canonical command accepts one fresh caller-owned output and exactly two named clean checkouts, producer and illuminate; it rejects all dependency packages, unknown or duplicate roles, wrong or dirty revisions, and existing or symbolic output. It runs the existing complete selection integration gate, verifies an exact six-regular-file inventory and ordered SHA256SUMS, runs package-local smoke before and after the atomic directory move, and leaves no output on failure. The positional-output plus ILLUMINATE_ROOT direct-use alias remains. The accepted proof-indexed resident Array implementation changes only linked helper bodies, so the unchanged v3 and selection source/helper inventories now pin exact complete-module byte hashes as well as updated sizes
files: integration/illuminate-player/export-selection-package.mjs; integration/illuminate-player/export-selection-package.test.mjs; integration/illuminate-player/check.sh; integration/illuminate-player/package.mjs; integration/illuminate-player/selection-package.mjs; integration/illuminate-player/README.md; coordination/lanes/wasm-gen.md
contracts: none. Selection remains adapter API fir.illuminate-player.browser/v5, hot-event fir.illuminate-player.hot-event/v2, module-owned memory, zero function and memory imports, the existing seven public function exports plus memory, one instance per player, retained selection and state below the checkpoint, and exact scratch rewind. Source inventories remain 99 declarations / 72 source functions / 190 resident helpers for v3 and 111 / 81 / 209 for selection
checks: Focused exporter tests PASS 6/6, covering the executable command, generic and alias parsing, dirty/wrong checkouts, unknown roles, rejected package inputs, fresh/existing/symbolic output, exact regular-file inventory, checksum mismatch, and real package-local smoke success/failure. The exact generic invocation against clean FIR functional head 4b84f35b and Illuminate 6f16cdc3 passed the complete integration check: deterministic two-pass v3 and selection publication, all six events, 10,000 flat-frontier ticks, 107 legacy/v3/selection traces, complete checksums, package-local smokes, and caller-owned revalidation. git diff --check PASS; make check PASS with 125 harness tests, 710 unique cases, 2,112/2,112 equal comparisons, zero findings, 182 active bug cards, and 25 mailbox tests; make talos-check PASS 3,148 jobs; bash integration/talos/artifact/check.sh PASS all standalone resident helpers, deterministic prettyM artifacts/clients, 701 native/LCNF/V8 triangles, 44/44 concrete readiness artifacts, and complete executable concrete cone
bug-cards: none for this slice. FIR-BUG-wasm-none-array-panic-observation remains independently parked; no value-only workaround was added
blockers: none
handoff: Integration may fast-forward functional commit 4b84f35b followed by the containing tracked status commit after resolving the actual wasm/generation branch head. The branch is based directly on main 300f8ab8. Canonical producer command: integration/illuminate-player/export-selection-package.mjs --output OUTPUT --checkout producer=EXACT_CLEAN_FIR_CHECKOUT --checkout illuminate=EXACT_CLEAN_ILLUMINATE_CHECKOUT. Immutable selection package: integration/illuminate-player/_build/illuminate-selection-player-packages/4b84f35bc327-6f16cdc3d432-d8aff69ccdf23c05db5d. Caller-owned acceptance copy: /tmp/fir-selection-export-4b84f35b. Complete selection Wasm: 35,370 bytes, SHA-256 22f295c5f249d1bd6e04e80bee10406f8e7d31a5bc7dcbec29131a7bb78896cd, zero imports, module-owned memory. Complete v3 Wasm: 32,334 bytes, SHA-256 8fc7e56bd597163153e35e24a0288a22f8f3bde6f40906ea332661d91845fed5
next: Integrate this independent exporter/package-ratchet slice while W7-2 continues its separate Verso semantic/publisher history split. Then notify VIR and Illuminate of the exact accepted FIR command/head and let the client activate illuminate/default. Tooling-side function evidence remains a separate handoff
```
