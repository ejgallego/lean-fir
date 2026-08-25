# lean-zip-perf lane

This is the narrowly scoped successor to the W7-2 optimization role. It owns
one lean-zip performance experiment at a time; `wasm-gen` remains the stable
generation and integration owner.

```text
lane: lean-zip-perf
owner: lean-zip-perf
branch: perf/lean-zip-loop-s5
worktree: .worktrees/lean-zip-perf
state: ready
base: 70cebb6fb38e044ef10f6e02295abc50e84a7536, accepted main including source-compiled inhabited defaults
functional-head: 3f7f324ac1a53b2dfd82e7dfa2030f39e20fadca
contract-base: 70cebb6fb38e044ef10f6e02295abc50e84a7536; no shared semantic, ABI, layout, ownership, helper-signature, proof, or source-entry contract change
clean-at-update: true
slice: Aligned typed final-LCNF constructor discrimination with upstream lean_obj_tag. Immediate constructors decode their tagged word and ordinary heap constructors read aux0 in the caller; all other heap families retain the unchanged checked fir_getTag helper as a cold fallback. The persistent planner registers the typed runtime-target rewrite, reserves its locals, and filters it by the source module's runtime-operation inventory
files: Fir/Wasm/Emit/ResidentRuntime.lean; Fir/Wasm/Emit/ResidentLinker.lean; integration/lean-zip/README.md; integration/lean-zip/level1-closure-contract.json; integration/lean-zip/raw-closure-contract.json; coordination/lanes/lean-zip-perf.md
contracts: No shared contract changed. The getTag runtime operation, helper signature, checked fallback, 32-byte concrete header layout, ABI, ownership, imports, exports, and observable semantics are unchanged. This is a private typed caller implementation plus reviewed package ratchets
performance: Exact one-call/two-call trace subtraction on a steady 256-byte call reduces dynamic fir_getTag calls from 37810 to zero; the baseline split was 37076 tag-one and 734 tag-zero results. Four fresh profiles contain no fir_getTag samples and no replacement resident hotspot. Two independent diagnostics-off 32-pair order-balanced fresh-process campaigns give a combined -0.350ms paired median, median ratio 0.990802 (about -0.92%), 43/64 wins, and improvement in both order buckets. The raw complete module grows 359760 to 366313 bytes and its frontier 818241 to 830433 bytes; the Level-1 complete module grows 193150 to 198424 bytes. Inventories and public surfaces remain unchanged
checks: Lean Beam update/sync/save passed with zero diagnostics for both Lean modules. The 54-job ResidentLinker dependency cone passed. The immutable raw preview passed deterministic double generation, native/Wasm dispatcher levels 1-10, zero-import complete runtime, persistent-cache and scratch-rewind checks, sidecar checks, checksum verification, and smoke. make check passed: 726 unique cases, 2160/2160 comparisons equal across native/LCNF/V8, zero findings, 9077 machine steps, 202 active bug cards, and 26 mailbox tests. make talos-setup and make talos-check passed, including 3172 jobs. The complete Talos artifact gate passed with prettyM stress, 717 V8 cases, 654 concrete cases, and the exact 63-case ByteArray blocker inventory. The lean-zip gate passed stored 10-case and Level-1 5-case native/Wasm differentials, zero imports, reclamation, checksums, and smoke. git diff --check passed
bug-cards: none
blockers: none
handoff: Rebasing onto current main preserves the functional result at 3f7f324a; it is ready for wasm-gen review and integration. The pre-rebase preview package .deps/perf/s5-gettag-accepted-package has package ID 6eec8088435d-273d0d6cd9ca-9e2a43f81f5c10de8121, complete Wasm SHA-256 55137db09f2247de98097ad243d32bd921ceec851ed4b1e43b8a1737c43ebf7d, size 366313 bytes, zero imports, 500 final functions, 630 source functions, and 830 resident helpers. Publication remains local-only
next: wasm-gen reviews and integrates the green candidate. W6 reviews the typed immediate/ordinary-constructor branches against LiveHeapRel.readTag_tobject_refines while retaining the checked fallback theorem. The separately requested successor lease makes inline/cold fast-path classification exhaustive and records compact upstream-aligned object representation as parked research
```
