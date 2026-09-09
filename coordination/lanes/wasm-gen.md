# wasm-gen lane

Generation roadmap: `Fir/Wasm/Emit/ROADMAP.md`. CG-05A is accepted on main;
this is the separate CG-05B selective-initialization handoff to standing
integration owner `fir/root`.

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: 14a2b07f3f0ef849de150b714c77a84dd923805f
functional-head: 6402d306d77425e5cc3e6e91d0a120826a82c823
contract-base: 14a2b07f3f0ef849de150b714c77a84dd923805f
clean-at-update: true
slice: CG-05B initializes only unwritten closure capture words. Existing stores fill the complete header and full-width slots; physical i32/f32 slot upper words remain explicitly zeroed. Expand the fixture to compare whole initialized allocations through poisoned checkpoint reuse and actual resident last-reference release/reuse.
files: Fir/Wasm/Emit/{ResidentClosureAllocation.lean,ROADMAP.md}; integration/talos/artifact/{FirWasmArtifactMain.lean,resident-closure-allocation-client.mjs,run-resident-closure-allocation.mjs,check.sh,README.md}; this status
contracts: none changed. Same allocator call, eight header stores, capture stores, extent, layout, target/arity/descriptor IDs, helper keys/signatures and scratch-free result suffix. Only redundant zero stores are removed. No W6, root gate, manifest, toolchain or symbolic surface changes. Release linkage is fixture-only.
checks: git diff --check; Lean Beam emitter update/sync/save and artifact-main sync, zero blocking diagnostics; stopped Beam, lake clean Fir, then clean artifact dependency build (95 jobs); forced direct Lean; make check (730 cases, 2172 equal comparisons, 38 mailbox tests); make talos-check (3204 jobs, 3165-job audit cone, 46 forced trust endpoints); FIR_CHECK_JOBS=2 bash integration/talos/artifact/check.sh (paired deterministic emissions, raw and pinned-optimized closure reuse, Node differentials, prettyM adapter stress, checksums); final focused lake -d integration/talos/artifact build fir-wasm-artifact fir-prettyM-artifact (124 jobs). Talos setup already completed in this worktree; toolchain/manifests unchanged. Exact containing-head Talos receipt is supplied in the authoritative completion. No fresh browser or balanced runtime timing campaign.
bug-cards: none new; no semantic workaround. Known FIR-BUG-wasm-none-partial-apply-tagged-result remains unchanged.
blockers: separate narrow W6 initialization-footprint review requested before root acceptance. CG-05A's result-suffix compatibility is not initialization approval. Full allocation/capture ownership and installed-helper refinement remain explicit debt; physical tagged-result fixture checks do not prove ValueRel tagged.
handoff: generation-ready only. Consume the exact clean containing integrationCheckpoint from the authoritative completion on ROOT-W7-20260909-107, then serialize the W6 footprint review. No main advance, remote push or external client-pointer publication by W7.
next: W6 narrow footprint review and root integration. Return-node ABI census W6-W7-20260830-001 and deeper projection-owner/all-jump provenance W6-W7-20260831-006 remain queued; neither is replaced by earlier named-call census work. Prioritize a requested diagnostic before more optimization if needed by W6 admission work.
```

## Exact reuse and code-shape evidence

The accepted full-zero baseline was retained after expanding the fixture, but
before changing production initialization. Baseline/candidate inventories are
identical. Both raw and pinned-optimized variants match all 81 full allocation
snapshots: 28 poisoned checkpoint allocations and 53 retirement/reuse results.
Checks include all result lanes, mixed kinds, exact floating payload bits,
retained prefix, canaries, canonical dead headers, real nonempty payload links,
header-only bump fallback and flat recycled frontier. A negative control that
omits one required upper-word store is rejected by the poison test.

| Standalone variant | Before bytes | After bytes |
| --- | ---: | ---: |
| Raw (29 functions each) | 6286 | 5128 |
| Pinned optimized (21 functions each) | 3353 | 2980 |

Raw candidate SHA-256:
`940922161c0d2226ea541cac80a60563b292aa41bd8878e3258aac5cc3e5ea1c`.
Optimized candidate SHA-256:
`d02d93d5b446eecb8e58d50e3cec57cebd4c9aff08feaa92ee20986aa6340f07`.
Same helper-body/store-count comparison is recorded in the roadmap. Binaryen
merges physical aliases in both versions; do not sum aliases as unique bodies.

## Immutable local prettyM package

Worktree-local `integration/talos/artifact/_build/prettyM-current` selects:

`integration/talos/artifact/_build/prettyM-current-releases/6402d306d774-96f827377ebc7972`

BUILD.json records exact clean functional source `6402d306d77425e5cc3e6e91d0a120826a82c823`.
Wasm: **83,737 bytes**, SHA-256
`f8593cbb727e212b1846886145b35cd85b1503aea92149c53c115f4b01997f43`.
Versus accepted CG-05A's 86,690 bytes: 2,953 bytes smaller (about 3.4%).
Exactly 25 closure body sizes decrease (2,948 body bytes plus 5 length-encoding
bytes). The 322 functions, 269 function export names/indices, captured LCNF,
zero imports, module memory and complete capability/ownership metadata match.
This is size/shape evidence, not a runtime speedup measurement.

## Evidence and limits

Logs, baseline/candidate binaries, exact toolkit shape inventories and commands
are retained under `.deps/cg05b/`, including `READOUT.md`, `shapes.json`,
`make-check.log`, `artifact-check.log` and `talos-check.log`.
The nested artifact main's Beam save was rejected because it is not a root
workspace module; its successful sync plus clean batch build are the evidence,
not a claimed Beam save. Fixture-authoring mistakes were corrected against the
accepted runtime before changing initialization. No new proof theorem is claimed.
