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
base: f2dc8d0b on main
functional-head: b167bddc, package exact final optimized function evidence with the immutable zero-import lean-zip raw artifact
contract-base: f2dc8d0b on main. Consumes the accepted optional runtime-link function-evidence API and final function-index protocol. Changes no ordinary linked Wasm bytes, source semantics, lowering, semantic ABI, concrete layout/runtime contract, ownership rule, resident-helper signature, or W6 theorem surface
clean-at-update: true
slice: `package-raw.mjs` now produces `lean-zip-raw.wasm.functions.json` through the generic evidence-preserving linker, verifies every final index, pins the exact export indices and origin counts, compares Wasm and sidecar bytes across two complete generations, and includes the sidecar in BUILD v3, SHA256SUMS, the immutable fingerprint, and package smoke. The adapter and Wasm runtime do not consume the sidecar. The release remains 902,411 bytes at SHA-256 d3992d5b5e5a4bd11edb93f48e0b95fbc2148a1c0b7c87b395d208e4a61e44cc with zero imports. The 943,785-byte sidecar has SHA-256 0948c7497690ffaf61a6bc7f4a441846099e8c7d03c3a8d6cd00e98a694536ab and indexes all 2,171 final functions: 354 Lean-source, 1,811 resident-helper, and six optimizer-or-linked-runtime functions
files: integration/lean-zip/package-raw.mjs; integration/lean-zip/raw-package-smoke.mjs; integration/lean-zip/raw-closure-contract.json; integration/lean-zip/README.md; coordination/lanes/wasm-gen.md
contracts: none. The client-specific immutable package schema advances from fir.lean-zip.raw.build/v2 to v3 to bind diagnostic function evidence. The adapter API, input/output layout, ownership and reclamation policy, zero-import/six-export module, and release Wasm identity are unchanged
checks: git diff --check PASS. Node syntax checks PASS. Clean package publication and a second complete invocation PASS byte-for-byte immutable-directory comparison at integration/lean-zip/_build/lean-zip-raw-packages/b167bddcf866-30737b4e2ebf-56f5c5393c735eaaf0e9 with canonical pointer integration/lean-zip/_build/lean-zip-raw-current. Both invocations PASS two internal complete generations, generic function-sidecar verification, 5 inputs x all 10 levels native/Wasm byte equality, independent inflate, zero imports, cache-aware ownership/rewind, and package smoke. Complete make check PASS with 125 harness tests, 702/702 source native/LCNF cases, 9/9 direct machines, 702/702 native/LCNF/V8 triangles, 711 unique cases, 2,115/2,115 equal comparisons, 7,602 interpreter steps, zero findings, 185 active bug cards, and 25 mailbox tests. make talos-check PASS 3,148 jobs. bash integration/talos/artifact/check.sh PASS standalone resident helpers, deterministic prettyM artifacts/clients, complete 702-case V8/concrete validation, 44/44 concrete readiness artifacts, and the executable concrete cone
bug-cards: none
blockers: none
handoff: Integration may fast-forward functional commit b167bddc followed by the containing tracked status commit after resolving the actual wasm/generation branch head. The branch is based directly on accepted main f2dc8d0b, changes only W7-owned lean-zip package files plus this mailbox, and requires no cross-lane adaptation
next: Integrate the lean-zip function-evidence package slice. Then accept the isolated bounded function-view tooling stack and root build wiring before choosing between the fresh-output lean-zip catalog producer and the profiled resident-linker scaling lane. W7-2 continues its independent Verso work
```
