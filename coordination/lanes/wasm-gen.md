# wasm-gen lane

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: f47ee55318550b37f690566a69987f99473f9f9e on main
functional-head: 6fb0b6e2 (resident setter prerequisite 01a77e71)
contract-base: f47ee55318550b37f690566a69987f99473f9f9e on main
clean-at-update: true
slice: Add generation-ready packed Float32/Float resident setters and a measured Illuminate constructor-specific dispatchTick(player, timestamp) path that constructs PlayerEvent.tick inside Wasm while retaining generic dispatch as the semantic oracle; consolidate accepted build examples into a thin navigation index backed by existing registries; record the pinned HitScene generation request
files: Fir/Wasm/Emit/ResidentMutation.lean; bugs/FIR-BUG-wasm-none-resident-float-scalar-setter.md; integration/talos/artifact/resident-setter-client.mjs; integration/illuminate-player/IlluminateFirNative/SelectionCompile.lean; integration/illuminate-player/SelectionEmit.lean; integration/illuminate-player/illuminate-selection-player-browser-adapter.mjs; integration/illuminate-player/selection-package.mjs; integration/illuminate-player/selection-package-smoke.mjs; integration/illuminate-player/selection-smoke.mjs; integration/illuminate-player/check-player-traces.mjs; integration/illuminate-player/check-selection-dashboard.mjs; integration/illuminate-player/selection-hot-event-benchmark.mjs; integration/illuminate-player/README.md; docs/build-examples.md; docs/wasm-artifact-generation.md; integration/talos/artifact/README.md; this mailbox
contracts: no shared signature or layout change; isolated commit 01a77e71 implements the existing RuntimeOp.scalarSet Float32/Float lanes by bit-preserving reinterpretation into the existing checked i32/i64 stores and marks them generation-ready; W6 implementation-to-concrete-host proof coverage remains a separate follow-up
checks: PASS original Lean Beam sync/save with zero diagnostics for ResidentMutation.lean and SelectionCompile.lean; PASS clean rebase on main f47ee553 including the pinned Illuminate-source gate; PASS git diff main...HEAD --check; PASS refreshed make check (642 unique cases, 633 native/LCNF, 9 direct-machine, 601-case native/LCNF/V8 triangle, 1844/1844 comparisons equal, 116 bug cards); PASS refreshed make talos-check (3131 jobs); PASS refreshed complete bash integration/talos/artifact/check.sh including 963-byte Float setter external-engine artifact sha256 222990f5abb0782513dbd06994740fc02923ea84972426f5cd33a314c756f767, deterministic PrettyFormat packages, 15/15 compiler-source probes, 601-case V8 matrix, and 44/44 concrete readiness artifacts; PASS env ILLUMINATE_ROOT=/tmp/illuminate-fir-pinned bash integration/illuminate-player/check.sh against clean detached Illuminate 6f16cdc3 with two deterministic publications, package checksum/smoke, 10000 scalar ticks with exact flat frontier, and all 107 generic/scalar-tick trace matches; PASS disposable Flat native/Wasm differential probe on 9 focused cases
bug-cards: fixed FIR-BUG-wasm-none-resident-float-scalar-setter; confirmed FIR-BUG-wasm-none-generic-object-join-admission and FIR-BUG-wasm-none-precise-box-result-admission in standalone record commit 324b91c4, with no workaround on this branch
blockers: none for the catalog handoff or the HitScene Lean-4.32 source-view compatibility probe; no owner or lane answer is pending. Integration should land 01a77e71 before dependent Illuminate commit 6fb0b6e2 and notify W6 that packed Float32/Float scalar setters are generation-ready but not newly contract-proved. Flat publication still depends on the recorded generic join/box admission fixes and a clean accepted Verso source revision
artifacts: immutable refreshed Illuminate selection package /home/egallego/lean/fir/.worktrees/wasm-generation/integration/illuminate-player/_build/illuminate-selection-player-packages/3bd93212ad87-6f16cdc3d432-3485104ee4c2a65606f7; complete Wasm 56156 bytes sha256 8b13c8124ba7235e2a00cec154f42d406e6f568f071f51ec831bbb95486ae3f5; base Wasm 20761 bytes sha256 b2b90d44c6a053eb5f59ef6330e44b9e0e2c0a0f160e832f48b003725a663314; zero imports, module-owned memory, seven public functions; 127 final-LCNF declarations, 82 retained source functions, 167 resident helpers; compiled source files are byte-identical at pinned Illuminate 6f16cdc3, consumer handoff 5a5f2b7d, and current vir-performance head despite different repository revisions
measurements: eight balanced rounds x 240 samples on two dashboard workloads preserve action digests and reduce host Wasm scratch from 40 bytes/one allocation to zero; final encode medians 4.32 -> 0.43 microseconds and 2.43 -> 0.19 microseconds; whole-callback medians 28.72 -> 34.90 microseconds and 17.45 -> 15.34 microseconds, so the supported conclusion is removal of generic event-boundary allocation/encoding, not a universal callback speedup; raw report integration/illuminate-player/_build/illuminate-selection-hot-event-benchmark.json
handoff: integration may land isolated generation helper commit 01a77e71 followed by Illuminate consumer commit 6fb0b6e2, the standalone Flat bug-card record 324b91c4, documentation/catalog commit a637e0a2, and the containing ready mailbox commit from wasm/generation; verify the clean worktree, synthesize the accepted result into coordination/BOARD.md, and publish the accepted scalar-tick head on a named ejgallego/lean-fir branch without opening a pull request as requested by Illuminate's FIR_STATE_SYNC_HANDOFF.md. For Flat, queue one isolated shared compiler-contract commit implementing the two confirmed cards, notify W6 of the join/box admission surface, and land it before dependent W7 helper/package work
next: build the separate Verso FIR Wasm Flat artifact requested by /home/egallego/lean/verso-slides/.worktrees/vir-pretty-prototype/handoffs/fir-wasm-flat-runtime/AGENT_TASK.md without replacing PrettyTrace. Disposable end-to-end evidence is now complete: the clean source-side shape uses an explicit reducible RenderedM monad and MonadPrettyFormat dictionary plus a local Nat-indexed tail-recursive chunk join, preserves the public formatRenderedForRuntime semantics in 19 existing and 9 focused native tests, captures exactly 113 declarations with 24 reviewed Array/Nat/Int/String/fallback externals, and closes to a module-owned-memory Wasm artifact with zero imports, zero residual runtime operations, 656 functions, five public functions plus memory, 164441 bytes, and sha256 cb4092061337d29f44c3444560b0bcbfaa2ea275ef256cae7a9cf7de7612ba35. The exact module matches native Lean on all 9 focused cases: empty, nested/multiple tags, UTF-8 byte offsets, indentation, wide/narrow nonzero-column grouping, a 64-bit tag, a 2047-node balanced append tree, and a 256-KiB Unicode output. Required W7-owned implementation is generic UInt8 box / UInt8 and UInt32 unbox helpers, tagged closure projection, and batched internalization for read projections, closure projections, closure matches, and partial applications; batching avoids hundreds of repeated whole-module rewrites. Before committing it, integration must land the two shared admission cards and the Verso owner must adopt the semantically equivalent source refactor. After Flat, implement Illuminate's timing-free dispatch request from FIR_UNTIMED_DISPATCH_HANDOFF.md as a distinct adapter experiment, then evaluate FIR_STATE_SYNC_HANDOFF.md without combining their measurements
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

## Illuminate request — prepared hit-scene queries (2026-08-09)

Illuminate requests a separate FIR-native package for the real
`Illuminate.HitScene.query : HitScene → Float → Float → HitSceneResult` entry.
The source handoff is
`/home/egallego/lean/illuminate/.worktrees/vir-performance/FIR_HIT_SCENE_HANDOFF.md`.
This is queued work, not an accepted package or a replacement for either
player artifact.

The first action is a clean source-view compatibility probe: the requesting
Illuminate checkout currently uses Lean 4.33.0-rc2, while FIR generation is
pinned to Lean 4.32.0. Do not change either toolchain or copy the hit-test
algorithm to bypass that gate. If compatible, capture the real query closure,
inventory its Float operations early (`Float.abs`, square root, and
trigonometric paths are expected), and internalize them in Wasm rather than
adding per-operation JavaScript `Math` imports. The clean worktree and remote
`ejgallego/feat/vir-performance` branch both resolve to immutable candidate
`af088e313eaade90be100aeaf63ddac79a8c1710`; all six task-relevant source
hashes match the handoff. No Illuminate-owner answer is currently needed.

The intended package retains one encoded immutable `HitScene` below a
persistent checkpoint, transports two bit-exact binary64 coordinates per
query, decodes the allocation-conscious `HitSceneResult`, clears and rewinds
bounded scratch, and exposes opaque create/query/dispose handles with isolated
instances. Acceptance includes the existing 295-point Illuminate differential
scene, every relevant constructor, 10,000-query flat-frontier evidence, two
instances, disposal/error paths, exact source/helper/import/export inventories,
and immutable package publication. The Illuminate worktree remains read-only
to this lane.
