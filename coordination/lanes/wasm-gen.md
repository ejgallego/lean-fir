# wasm-gen lane

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: active
base: 7aab434b08777be79af53c63836f774e6bfe24e2 on main
functional-head: 1d79658dbcc14bdc1fbd5e210086c82843bc9cd0
contract-base: 7aab434b08777be79af53c63836f774e6bfe24e2 on main. Characterization changes no contract. A future preinitialized-image design must preserve lazy-observable cache semantics, stable object layout, module-owned memory, cache-aware rewind, and the zero-import package boundary; signature or concrete-layout changes enter the shared contract queue before implementation
clean-at-update: true
slice: Characterize the next independent W7 runtime slice after accepting constant-time resident Array indexing. The official lane does not own wasm-gen-2's closure-helper consolidation or the generic Array semantic/proof stack. The accepted raw package still constructs and publishes 6,622,744 bytes of closed compiler tables/graphs on its first level-6 call, while warm calls have zero persistent growth and no single comparably dominant resident helper. The proposed milestone is generation-time materialization of eligible immutable closed constants into a module-owned persistent image, preserving lazy-observable behavior and the existing cache-aware rewind floor
files: this mailbox only; characterization artifacts are diagnostics under `/tmp` and are not committed
contracts: none in this characterization. The next design must distinguish pure materializable closed graphs from panic/effectful or unsupported initializers and must not eagerly execute arbitrary Lean initializer code
checks: accepted raw package identity reverified at 1,753,310 bytes and SHA-256 `0686e69684c187b1b14415f0f3b88fe4ce28514c97f8aac003fbd7359f15b838`; zero imports and the exact six exports remain recorded by the immutable package. Exact structured 1 KiB level-6 browser evidence from the accepted Array-O(1) artifact is cold 318.63 ms and warm samples 8.47/11.53/15.05/10.63/12.05 ms (median 11.53 ms), with exact native bytes, independent inflate, 6,622,744-byte first-call persistent growth, 1,000,464-byte scratch growth, and zero warm persistent growth. A diagnostic profile of the exact post-Array linked module before final O3 shows cold cost distributed across closed initializers plus generic numeric/object work; a 20-call warm profile has no single generic resident helper above 5.8% self time. Profiles are target-selection evidence only, not headline timing
bug-cards: none; no semantic discrepancy was observed
blockers: none
artifacts: raw immutable package `integration/lean-zip/_build/lean-zip-raw-packages/1d79658dbcc1-30737b4e2ebf-9cce2a4d2849ac7ce273`; canonical pointer `integration/lean-zip/_build/lean-zip-raw-current`; BUILD SHA-256 `40aee377f49edf1d0dc13c8a783273a20088ae57c7913957e7ef20c26b56a40d`. Complete raw Wasm is 1,753,310 bytes, SHA-256 `0686e69684c187b1b14415f0f3b88fe4ce28514c97f8aac003fbd7359f15b838`; base remains 1,888,508 bytes, SHA-256 `d03549469c5a4287eba2a06c313b9b860405024c2b90a0ab4ad241467578f42e`; frontier is 3,265,131 bytes, SHA-256 `ff6c40bad0bc2d6e860b5b1670d0f321f7b127a803b6d4f4e4d978fc18a3bbe1`. Level-1 immutable package `integration/lean-zip/_build/lean-zip-level1-packages/1d79658dbcc1-30737b4e2ebf-ad1b0007642fde252367`; canonical pointer `integration/lean-zip/_build/lean-zip-level1-current`; BUILD SHA-256 `869df15d42850c9551075f22034c6422b351d809debe01991d63bebd453a2db5`. Complete Level-1 Wasm is 508,531 bytes, SHA-256 `cec08523e4abf4b9555db565952903b5b693c3a1af7ef698117a2ebefc4230de`; base remains 218,625 bytes. Stored immutable package `integration/lean-zip/_build/lean-zip-stored-packages/1d79658dbcc1-30737b4e2ebf-015308f8a04b5d1b9a64`; complete Wasm is 12,852 bytes, SHA-256 `d757bcdd0c28bca0604315003bfeeb28d92fb6ec5966c19e946443e732a64596`; BUILD SHA-256 `0fe18ca80f2a733407e1de75ceb2036ab650c542fba706b1d21be87c7c1bab51`. All complete modules have zero imports and module-owned memory
measurements: exact A/B from the isolated characterization on the same generic patch and 1 KiB structured level-6 workload: baseline cold execute 917.5 ms, warm 30.0/28.6/27.6 ms; candidate cold 195.6 ms, warm 11.7/8.9/7.3 ms. Persistent and scratch growth are byte-identical. Artifact deltas: raw frontier -193 bytes, raw complete -217 bytes, Level-1 complete -177 bytes, stored complete -16 bytes; declaration/function/helper inventories unchanged
handoff: none; the previous constant-time Array slice is already accepted on main through `7aab434b`
next: design a fail-closed static closed-graph materializer for a small focused cache fixture; require module-owned data/global initialization, zero imports, exact native value equality, idempotent lazy publication, no run-time heap growth for materialized constants, and unchanged scratch rewind. Only after that focused gate should the raw package opt in and be republished. wasm-gen-2 independently owns closure-helper consolidation; the generic Array contract remains with its W6 and LCNF-proof consumers
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
