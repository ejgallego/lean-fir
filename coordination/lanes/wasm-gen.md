# wasm-gen lane

Generation roadmap: `Fir/Wasm/Emit/ROADMAP.md`. Accepted history remains on
`coordination/BOARD.md`; this is the separate CG-05A generation handoff.

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: c4eefca5942cd8f6abb584fb8820b1a262c21449
functional-head: 87d766a1bf881bda1c430af7a93950e2b662d672
contract-base: c4eefca5942cd8f6abb584fb8820b1a262c21449
clean-at-update: true
slice: CG-05A scratch-free closure allocation result transport, using the constructor allocator's typed unsigned extend/wrap bridge. Remove two scratch-only locals and all scratch memory traffic; retain exact allocation/zero/header/capture prefix and typed signatures. Add full mixed-capture poisoned reallocation checks.
files: Fir/Wasm/Emit/{ResidentClosureAllocation.lean,ROADMAP.md}; integration/talos/artifact/{resident-closure-allocation-client.mjs,README.md}; this status
contracts: none changed. Same heap layout, initializer footprint, capture ownership, target/arity/descriptor IDs, helper sharing keys and result ABI. No W6 source, root gate, manifest or symbolic surface edits.
checks: git diff --check passes. Lean Beam update/sync/save accepts the emitter and guards with zero diagnostics. After stopping Beam and lake clean Fir, the focused 51-job dependency build and forced direct Lean pass. make check on functional head passes 730 cases / 2172 equal comparisons, 240-file source trust audit and 38 mailbox tests. make talos-check passes 3201 jobs, 3162-job audit cone and forced 24-endpoint audit; exact functional receipt 72d9514a5530e01a34fb4a988df7f63d08ee9a642f1d1eba3e60f62d6c617ba9 verifies. Talos setup was already completed in this worktree for accepted CG-01; toolchain/manifests are unchanged. FIR_CHECK_JOBS=2 bash integration/talos/artifact/check.sh passes, including paired deterministic emissions, Node differentials and immutable package checksums. Standalone raw and pinned-Binaryen-optimized closure modules both pass poisoned-memory tests. No browser or workload timing campaign is claimed.
bug-cards: none; no semantic discrepancy
blockers: no generation blocker; W6 delta review is requested separately before helper acceptance. Full closure-allocation refinement remains recorded proof debt, not claimed here.
handoff: Consume this clean generation checkpoint only; do not fold in pending W6 extraction, precision or terminal-simulation checkpoints. Root alone schedules acceptance. No main advance, push or external client-pointer update by W7.
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

`integration/talos/artifact/_build/prettyM-current-releases/87d766a1bf88-e9a15005f95644f0`
is the worktree-local `prettyM-current` target. BUILD.json records clean
functional source `87d766a1`. Wasm: 86,690 bytes, SHA-256
`e65000ff59279ec7eec37a4f43d8e398a35c56f8c85dc42c26e23c33533f75b4`.

Versus CG-01's package, exactly 25 closure helper body sizes decrease by 46
bytes each: 1,150 bytes saved (about 1.3%). The 322 functions, all 269 function
export names/indices, zero imports, module-owned memory and ownership metadata
are unchanged. Captured LCNF is byte-identical. This is a package-size and
instruction-shape result, not a workload speedup measurement.

Logs and raw/optimized standalone comparisons: `.deps/cg05a/`. The first
attempt at module-scoped `lake clean` was rejected (clean accepts packages);
the successful `lake clean Fir` and subsequent batch/direct checks are the
reported clean validation. Earlier malformed test-facade probes were fixed
before Beam save and are not counted as passing checks.
