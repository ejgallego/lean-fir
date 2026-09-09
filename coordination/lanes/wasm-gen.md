# wasm-gen lane

Generation roadmap: `Fir/Wasm/Emit/ROADMAP.md`. Accepted history remains on
`coordination/BOARD.md`; this is the separate CG-05A generation handoff.

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: 4f8d111c2f436f7ac63f253bf0c575dd1f2799fb
functional-head: 32524c14c2ffa5668d0219b765c540bf795de60e
contract-base: 4f8d111c2f436f7ac63f253bf0c575dd1f2799fb
clean-at-update: true
slice: CG-05A scratch-free closure allocation result transport, using the constructor allocator's typed unsigned extend/wrap bridge. Remove two scratch-only locals and all scratch memory traffic; retain exact allocation/zero/header/capture prefix and typed signatures. Add full mixed-capture poisoned reallocation checks.
files: Fir/Wasm/Emit/{ResidentClosureAllocation.lean,ROADMAP.md}; integration/talos/artifact/{resident-closure-allocation-client.mjs,README.md}; this status
contracts: none changed. Same heap layout, initializer footprint, capture ownership, target/arity/descriptor IDs, helper sharing keys and result ABI. No W6 source, root gate, manifest or symbolic surface edits.
checks: git diff --check and patch-identical git range-diff pass. Before rebase, Lean Beam update/sync/save accepted the emitter and guards with zero diagnostics, followed by lake clean Fir, a clean 51-job build and forced direct Lean. No Lean source changed in the rebase. Post-rebase make check passes 730 cases / 2172 equal comparisons, 243-file source trust audit and 38 mailbox tests. make talos-check passes 3204 jobs, 3165-job audit cone and forced 44-endpoint audit. Talos setup was already completed in this worktree for accepted CG-01; toolchain/manifests are unchanged. FIR_CHECK_JOBS=2 bash integration/talos/artifact/check.sh passes, including paired deterministic emissions, Node differentials and immutable package checksums. Forced direct Lean and final focused 66-job build pass. Raw closure Wasm and prettyM LCNF/Wasm are byte-identical to pre-rebase CG-05A; the retained pinned-Binaryen-optimized closure module passes the poisoned-memory test again. Exact containing-head receipt is supplied in the immutable mailbox handoff. No new browser or workload timing campaign is claimed.
bug-cards: none; no semantic discrepancy
blockers: none for the narrow result-transport delta. W6 accepted existing unsignedI32RoundTrip coverage in W6-W7-20260909-002; requester closure W7-W6-20260909-009. Full allocation/initialization/capture ownership and installed-helper replacement refinement remain debt. The unchanged tagged physical result path is not a ValueRel tagged theorem; FIR-BUG-wasm-none-partial-apply-tagged-result remains open.
handoff: Root independently accepted the four separate W6 slices at 4f8d111c and requested this isolated CG-05A rebase. Consume the new exact clean mailbox checkpoint, not the superseded pre-rebase e7c955af. The two CG-05A patches are unchanged; CG-05B is not included. Standing fir/root alone owns integration. No main advance, push or external client-pointer update by W7.
next: CG-05B selective initialization, separately from this result-transport change. Keep the initialization byte contract and poisoned-memory tests; do not edit W6's pending proof work.
```

## Code-shape evidence

The return suffix shrinks from 14 instructions to 4, with locals 3 -> 1.
Across the old standalone helper shapes, raw bodies shrink by 46 bytes each;
the pinned closed-module Binaryen profile yields 24 bytes saved per surviving
body and removes two loads/two stores that survived optimization previously.
The enlarged standalone test module includes a new mixed-capture facade/helper,
so its total size is not used as an old/new performance comparison.

The external-engine regression covers all three object-family result lanes,
object/erased captures, seven scalar kinds, Float32/Float signed zero,
subnormals, infinities and quiet/signaling NaN payloads via integer lanes.
It verifies the whole initialized extent, zero slot padding, target/arity/
descriptor/refcount fields, a retained prefix, reserved words and a suffix
canary across checkpoint rewind and poisoned reallocation.

## Immutable local package

`integration/talos/artifact/_build/prettyM-current-releases/b9780a80cda4-49ab2b7bde34de3c`
is the worktree-local `prettyM-current` target. BUILD.json records clean
rebased source `b9780a80` (functional `32524c14`). The original immutable
`87d766a1bf88-e9a15005f95644f0` package is retained as pre-rebase evidence.
Wasm: 86,690 bytes, SHA-256
`e65000ff59279ec7eec37a4f43d8e398a35c56f8c85dc42c26e23c33533f75b4`.

Versus CG-01's package, exactly 25 closure helper body sizes decrease by 46
bytes each: 1,150 bytes saved (about 1.3%). The 322 functions, all 269 function
export names/indices, zero imports, module-owned memory and ownership metadata
are unchanged. Captured LCNF is byte-identical. This is a package-size and
instruction-shape result, not a workload speedup measurement.

Original logs and raw/optimized standalone comparisons: `.deps/cg05a/`.
Post-rebase gate logs: `.deps/cg05a-rebase/`. The first
attempt at module-scoped `lake clean` was rejected (clean accepts packages);
the successful `lake clean Fir` and subsequent batch/direct checks are the
reported clean validation. Earlier malformed test-facade probes were fixed
before Beam save and are not counted as passing checks.
