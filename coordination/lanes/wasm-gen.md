# wasm-gen lane

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: 2a870967aca985a772187d9aa478480548718070 on main
functional-head: 9e6d5fdfc058cb0d5725311d26d062f2b7937040
contract-base: 2a870967aca985a772187d9aa478480548718070 on main; packed ByteArray and fixed-width helpers are generation-ready only, with W6 refinement deliberately pending
clean-at-update: true
slice: Add dependency-thin generic packed ByteArray and UInt16 resident families; add an operation-derived closed-application policy for exact narrow closures; compile the real Zip.Wasm.compressStored : ByteArray -> ByteArray from lean-zip 30737b4e2ebfd0fc889f0b2e265aae0635d668a1 and zipCommon 4425bab1f9522307d77e8d485bc536149ba31c36; and publish a deterministic zero-import Node/browser package with native-Lean differential checks and per-call scratch rewind
files: Fir/Wasm/Emit/{ResidentByteArray,ResidentFixedWidth,ResidentLinker,ResidentScalarBox}.lean; integration/talos/artifact/{FirWasmArtifactMain,browser-pretty-format-worker,check,resident-byte-array-client,resident-fixed-width-client,run-resident-byte-array,run-resident-fixed-width}.*; integration/lean-zip/
contracts: fir.wasm.byte-array/v1 uses a checked 32-byte resident header followed by packed bytes and module-owned capacity. Generation-ready externs are ByteArray.size, ByteArray.mk, ByteArray.emptyWithCapacity, ByteArray.copySlice, UInt16.shiftRight, UInt16.ofNat, UInt16.toUInt8, UInt16.land, and UInt16.xor. Public package API fir.lean-zip.stored.browser/v1 accepts copied ArrayBuffer views and returns copied Uint8Array output; ownership fir.lean-zip.module-owned-scratch/v1 saves and rewinds the resident frontier in finally, and exposes no raw address
checks: Lean Beam update passed after every Lean edit; focused root and integration Lake builds passed; git diff --check passed; make check passed 122 harness tests, 653/653 native-LCNF, 9/9 direct-machine, 653/653 native-LCNF-V8, 662 unique cases, 1968/1968 comparisons, 6829 machine steps, and zero findings; make talos-setup pinned Talos a01d01c778b794dd00956748a067b6793c2c9f9b and make talos-check passed 3133/3133 jobs; bash integration/talos/artifact/check.sh passed the complete deterministic resident/runtime/package cone and 653-case V8 triangle; integration/lean-zip/check.sh passed deterministic double emission, SHA256SUMS, Node smoke, native/Wasm equality on 10 cases through 1 MiB, inflateRaw round trips, two instances, malformed input, flat scratch frontier, injected clock, and headless Chrome. The optional FIR_BROWSER umbrella worker additionally exposes the pre-existing mixed resident-constructor/host-objectSet bookkeeping limitation recorded by FIR-BUG-wasm-none-resident-import-location-registry; the lean-zip browser package itself passes and has no host operations
bug-cards: no new card; existing FIR-BUG-wasm-none-resident-import-location-registry remains the unrelated optional mixed-runtime browser limitation
blockers: none for Stored correctness or publication. W6 refinement proofs are pending. Full Zip.Wasm.compressRaw/Level1 requires the additional ByteArray and algorithm operations selected by its exact source closure; do not model ByteArray as Array UInt8 or add host fallbacks
artifacts: immutable package integration/lean-zip/_build/lean-zip-stored-packages/9fdd4e301122-30737b4e2ebf-bfbc63c1bf381973e206; canonical pointer integration/lean-zip/_build/lean-zip-stored-current; complete Wasm 11315 bytes SHA-256 7cdccc5d5822ec76dd9099fac9aecfd035f025d5560b296d396e252dadc5d40e; base Wasm 1884 bytes; zero function and memory imports; exact function exports Zip.Wasm.compressStored, fir_heap_frontier, fir_heap_set_frontier, fir_heap_rewind, and fir_heap_alloc plus module-owned memory
measurements: exact capture has 21 declarations, 14 externals, zero unsupported declarations, 7 retained source functions, 65 resident helpers, 72 complete functions, zero residual runtime operations, and zero imports. A non-headline local 1 MiB diagnostic completed in about 14.6 ms total with about 12.4 ms in the Wasm entry and returned to the scratch checkpoint
handoff: integrate functional head 9e6d5fdf after resolving this mailbox commit from wasm/generation. The immediately following 9fdd4e30 commit only records the already-requested spatial HitScene task. The packed ByteArray signatures are generation-ready; W6 owns their later refinement proofs. No PR is requested
next: probe Zip.Wasm.compressRaw/Level1 with exact capture and extend the generic packed ByteArray surface only for live operations, sharing or aligning the mechanism with VIR where practical; separately keep the spatial HitScene request queued
```

## Verso Flat end-to-end probe (2026-08-09)

The disposable Flat experiment now includes a standalone browser adapter and
a package-shaped validation artifact at `/tmp/fir-verso-flat-package`. This is
evidence only, not a publishable package: `BUILD.json` honestly records the
clean local Verso probe commit `e9ae2ed6` and the still-dirty disposable FIR
compiler/runtime patch. The eventual immutable package must replace both with
integrated, remotely resolvable commits.

The exact Wasm is 164,441 bytes with SHA-256
`cb4092061337d29f44c3444560b0bcbfaa2ea275ef256cae7a9cf7de7612ba35`,
zero imports, 656 functions, five function exports plus module-owned memory,
and zero residual runtime operations. The adapter is deterministically
specialized from the accepted PrettyFormat control adapter: normalization,
bulk raw encoding, timings, and ownership stay identical; only the browser API
version and `Rendered` result decoder differ. The current generated adapter is
33,318 bytes.

Passed gates:

- 19 existing Verso native tests and 9 explicit-state/native-oracle tests;
- 9 native/Wasm Flat differential cases, including exact UTF-8 event offsets;
- 1 MiB UTF-8 output with memory growth from 1 to 33 pages;
- the 2,047-node balanced and 256-break grouped stack-safety shapes;
- 32 repeated calls on one adapter with monotonic frontier synchronization;
- package SHA-256 verification and Node smoke;
- Verso's exact `validate-native-flat-package.py` contract validator; and
- Chrome fetch/compile/instantiate/render smoke over HTTP.

Integration order remains: accept the scalar-tick stack; land the two isolated
generic join/box admission fixes through the shared-contract queue; obtain the
clean Verso source refactor; then commit and validate the W7 resident scalar
helpers, batched linker, Flat package generator, immutable publication, and
full FIR gates. W6 proof adaptation for the new helpers proceeds in parallel
after their signatures are generation-ready.

## Illuminate request — timing-free production dispatch (2026-08-09)

Illuminate requests a v5 selection-player package that separates the
production scalar-tick path from adapter diagnostics. The full handoff
is published on `ejgallego/illuminate` branch `feat/vir-performance` at
commit `56b9f99b5cfecdeb340bdf120f6dd1a7ef227f20`:

```text
/home/egallego/lean/illuminate/.worktrees/vir-performance/
  FIR_UNTIMED_DISPATCH_HANDOFF.md
```

Preferred API: timing-free `dispatchTick(player, timestamp)` plus
diagnostic `dispatchTickTimed(player, timestamp)` in the same package,
both using the same compiled scalar-tick semantics. The fast path must
omit clock calls and timing/memory object construction while retaining
ownership checks, exact rewind, poisoning, bit-exact timestamps, zero
tick scratch, zero imports, and module-owned memory. Keep generic
dispatch as the oracle and do not combine this experiment with the
resident-state ABI request.

Illuminate's 24-observation same-runtime RAF matrix cannot resolve the
host observer cost: every on/off range crosses 1x and every time-delta
range crosses zero. The handoff therefore requires an interleaved,
fixed-event timed/untimed benchmark with warmup, action-digest checks,
median, and p95. Illuminate will map detailed mode off/on to the new
fast/timed methods and run the consumer acceptance suite. Keep work on
a named `ejgallego/lean-fir` branch and do not open a PR.

## Illuminate HitScene v2 package (2026-08-11)

The exact-source v2 package is complete at functional head `53c8b917`. Its
immutable directory is
`integration/illuminate-hit-scene/_build/illuminate-hit-scene-7daab5f2bb96f121`;
the canonical pointer resolves to that directory. The 46,089-byte complete
Wasm has SHA-256
`06708aac339cd7f6f7fcbe7c973dc29125e263925635d0311a0571d4428e97b7`,
zero imports, six function exports plus module-owned memory, and deterministic
fresh frontier/complete-link evidence. Layout
`lean-4.32-Illuminate.HitScene/v2` transfers the real source's prepared path
bounds; the adapter retains one scene below a checkpoint, transports binary64
coordinates bit-exactly, supports production and diagnostic queries, copies
results, and rewinds scratch. Smoke covers 301 fixture queries and 10,000
flat-frontier queries.

## Illuminate request — spatial HitScene package (2026-08-11)

Illuminate requests the missing spatial-FIR cell in its 2 by 2 HitScene
comparison. The complete, source-pinned handoff is published on
`ejgallego/illuminate` branch `feat/vir-hit-scene` at commit
`c8d321721262b5987226ae9626abf5ca3e1dfe9b`:

```text
/home/egallego/lean/illuminate/.worktrees/vir-hit-scene/
  FIR_SPATIAL_HIT_SCENE_HANDOFF.md
```

Compile the real `Illuminate.SpatialHitScene.ofHitScene` and
`Illuminate.SpatialHitScene.query` declarations from the exact Illuminate
source revision and hashes in that handoff. Spatial preparation must execute
inside compiled Lean once when the retained scene is created; do not reproduce
the algorithm in the browser adapter. Keep the accepted reference HitScene v2
package immutable and publish this as a separately versioned, zero-import,
module-owned package with untimed production and timed diagnostic query paths.

Consumer acceptance is the shared 1,009-query oracle, bit-exact binary64
coordinates, concurrent-scene isolation, idempotent disposal, and a flat
10,000-query memory frontier. Return paired measurements sufficient to compare
reference/spatial under both VIR and FIR. Keep the work on a named
`ejgallego/lean-fir` branch and do not open a PR.
