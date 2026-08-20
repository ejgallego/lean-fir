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
base: 27de2d1f on main
functional-head: 5e30208f, stabilize lean-zip stored and Level-1 packages on persistent source views
contract-base: 27de2d1f. No shared semantic, ABI, layout, ownership, helper, or proof contract changed; this is an exact artifact-ratchet and source-view durability slice
clean-at-update: true
slice: Stored and Level-1 lean-zip package gates now ratchet the current deterministic bytes after all accepted direct-scalar and resident-runtime changes. Their declaration/function inventories remain unchanged, every semantic and ownership gate passes, and both final modules remain zero-import with module-owned memory. All lean-zip package defaults and documented setup now use persistent ignored FIR-local .deps/source-views checkouts; no package depends on a periodically cleaned /tmp source view. The forward W7 roadmap records the accepted proof-indexed Array, immediate-Nat, scalar, source-Float, and production-dispatch milestones and the current raw closure inventory
files: Fir/Wasm/Emit/ROADMAP.md; integration/lean-zip/README.md; integration/lean-zip/check.sh; integration/lean-zip/closure-contract.json; integration/lean-zip/level1-closure-contract.json; integration/lean-zip/package.mjs; integration/lean-zip/package-raw.mjs; coordination/lanes/wasm-gen.md
contracts: No shared contract changed. Stored remains 21 captured declarations, 14 reviewed externals, seven retained source functions, and 67 resident helpers. Level-1 remains 404 captured declarations, 108 reviewed externals, 296 retained source functions, and 1068 resident helpers. Both retain zero runtime operations, the same public APIs, cache/checkpoint behavior, and zero imports
artifacts: clean functional producer 5e30208f. Stored immutable package integration/lean-zip/_build/lean-zip-stored-packages/5e30208f289b-273d0d6cd9ca-21e8f6f2de070968eecf is 12779 bytes at SHA-256 9b9630dba3d5d04913b2e95647e8613596672bd1d3c4a7373a5c33ec32773e25. Level-1 immutable package integration/lean-zip/_build/lean-zip-level1-packages/5e30208f289b-273d0d6cd9ca-f4e2385c2a54c51b6de0 is 331043 bytes at SHA-256 fcccdfaf024d78c35e37152a338a2ae75cf035d28390d274dd8a4497abb6d6b3. Canonical pointers end in lean-zip-stored-current and lean-zip-level1-current
checks: Persistent clean source views at lean-zip 273d0d6cd9ca and zip-common 4425bab1f952. Repeated stored and Level-1 generation byte-identical. Stored native/Wasm differential PASS 10 cases; Level-1 native/Wasm differential PASS five cases; independent zero-import ByteArray adapters, lazy persistent-cache floor, scratch reclamation, and package smokes PASS. Raw exporter tests 6/6 PASS. git diff --check PASS. make check PASS 704 source cases, nine direct machines, complete 704-case V8 triangle, 713 unique cases, 2121/2121 comparisons equal, zero findings, 188 active bug cards, and 25 mailbox tests. make talos-setup PASS at Talos 0e05edbc; make talos-check PASS 3162 jobs. bash integration/talos/artifact/check.sh PASS, including deterministic libm/source-Float/resident/prettyM artifacts, 642/704 concrete products with the existing 62 initial-ByteArray blockers, 44/44 readiness artifacts, and all executable concrete cases
bug-cards: none
blockers: none
handoff: Integration resolves the containing clean branch head after this tracked status commit and may fast-forward main. Functional head 5e30208f is based directly on 27de2d1f. No W6-owned file changed and no feature branch or external package publication is authorized
follow-up: Migrate Illuminate selection and player packages from fir.standard-math/v1 to source-compiled Float. The selection frontier currently contains only Float.ofScientific and Float.ofNat, so its expected complete target is provider-free and zero-import
```
