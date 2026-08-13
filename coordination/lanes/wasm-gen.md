# wasm-gen lane

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: waiting
base: a6f4510e1d7658e738710b7dfe805d483810a6c0 on main
functional-head: cf4dc78a4aac7de2b847968ddf67585fd1d225de
contract-base: a6f4510e1d7658e738710b7dfe805d483810a6c0 on main. The exported allocator signatures are unchanged; object-valued compiler cache publication now advances a private persistent floor and generated `fir_heap_rewind` clamps to that floor. `Float.log2` is added to the checked standard-math contract. W6 refinement of the cache-floor behavior is pending and does not block generation-ready status
clean-at-update: true
slice: Compile and package the real read-only `Zip.Wasm.compressRaw : ByteArray -> UInt8 -> ByteArray` entry for production raw-DEFLATE levels 1 through 10. The generic resident frontier closes fixed-width, arbitrary-Nat, scalar-box, Array/ByteArray, and direct Float comparison operations; the checked standard runtime closes exactly `Float.ofNat`, `Float.ofScientific`, and `Float.log2`. Binary-only meta-DCE scales the external-runtime link. Compiler constants remain lazy: a cold object-cache miss recursively publishes persistence and advances a rewind floor, while warm calls rewind flat. The browser adapter transfers packed ByteArrays, validates levels, reserves standard-runtime memory, copies outputs, exposes timings/memory diagnostics, and never exposes raw addresses
files: W7-owned `Fir/Wasm/Emit/ResidentAllocator.lean`, `ResidentCache.lean`, resident scalar/Nat/fixed-width/Float families and linker; `integration/wasm-runtime`; `integration/lean-zip`; W7 bug cards; `integration/talos/artifact/resident-cache-client.mjs`; this mailbox
contracts: generation-ready cache-aware rewind behavior as described in contract-base, with unchanged public ABI; reviewed standard-math frontier extended by exact `Float.log2`; no LCNF semantic/interpreter contract changed. Binaryen linking now enables multivalue and removes private runtime exports with binary `wasm-metadce`, preserving the exact frontier export inventory
checks: Lean Beam refresh/save passed `ResidentAllocator`, `ResidentCache`, and `ResidentLinker` with zero diagnostics after rebasing. Focused lean-zip build passed 157 jobs. Exact probe passed with 702 captured declarations, 128 reviewed externals, 0 unsupported declarations, exactly 3 reviewed imports, and 0 runtime operations. Focused resident-cache artifact passed in real Wasm (2,520 bytes): cold cache publication clamps rewind above prior scratch, preserves the exact cached root, and repeated warm calls remain flat. Clean immutable package generation on final base `a6f4510e` emitted frontier and complete modules twice and compared byte-identical bytes/descriptors/runtime; native/Wasm equality and independent raw inflate passed 5 input families at all 10 levels, including warm repeats and ownership checks. On base `8bcafc05`, `git diff --check` passed; `make check` passed 125 harness tests, 676/676 native-LCNF, 9/9 direct-machine, the complete 676-case native/LCNF/V8 triangle, 685 unique cases, 2,037/2,037 comparisons, zero findings, 173 valid bug cards, and trusted assumptions; `make talos-check` passed 3,143 jobs; and `bash integration/talos/artifact/check.sh` passed the complete resident/source/prettyM/concrete and V8 gates. On final base `a6f4510e`, `make check` again passed all 2,037 semantic comparisons but failed only because newly landed W6 card `FIR-BUG-wasm-none-structured-validation-provenance` lacks the mandatory `## Resolution and regression` heading. `make talos-setup` had already passed at Talos `0e05edbc`
bug-cards: FIR-BUG-wasm-none-raw-deflate-generic-resident-frontier fixed; FIR-BUG-wasm-none-external-runtime-link-multivalue fixed; FIR-BUG-wasm-none-external-runtime-link-wat-size fixed; FIR-BUG-wasm-none-persistent-cache-eager-panic remains candidate because the raw path is repaired generically but the older explicit eager Level-1 initializer API still needs migration/removal
blockers: current `main` fails `scripts/validate_bug_cards.py` because W6-owned `FIR-BUG-wasm-none-structured-validation-provenance` lacks `## Resolution and regression`; message `W7-ROOT-20260813-023` requests the W6/integration repair
artifacts: immutable package `integration/lean-zip/_build/lean-zip-raw-packages/cf4dc78a4aac-30737b4e2ebf-57467d1d684be1f40716`; canonical pointer `integration/lean-zip/_build/lean-zip-raw-current`. Complete Wasm is 1,753,527 bytes, SHA-256 `431007aefe59858f913845a8f540800c5e4c503dabebd6a21d27dcf0e21d289c`; base is 1,888,508 bytes, SHA-256 `d03549469c5a4287eba2a06c313b9b860405024c2b90a0ab4ad241467578f42e`; frontier is 3,265,324 bytes, SHA-256 `c8c57995f49ed0dcec035f43e92f2e17791c5b7ad0994bb03278d4c2b8631938`. Complete module has zero imports, module-owned memory, one application entry, four arena controls, and memory. BUILD schema `fir.lean-zip.raw.build/v2`; adapter `fir.lean-zip.raw.browser/v2`; ownership `fir.lean-zip.raw.lazy-cache-floor/v2`; BUILD SHA-256 `af562b57c0526eea9f0baa8254c2963c2e1b2ec11082e2f775c0fb3e43357633`
measurements: clean FIR artifact source `cf4dc78a4aac7de2b847968ddf67585fd1d225de`; clean lean-zip `30737b4e2ebfd0fc889f0b2e265aae0635d668a1`; clean zipCommon `4425bab1f9522307d77e8d485bc536149ba31c36`; Lean 4.33.0 commit `d8b18978`; Emscripten 5.0.3. Closure contains 574 retained source functions and 5,265 currently classified resident/lowering helpers. The large helper count includes per-call-site closure allocation code-size/build-time debt and is a follow-up, not duplicate linker installation
handoff: waiting for the W6/integration bug-card schema repair on `main`; after rebasing that standalone fix and rerunning the affected gates, fast-forward `wasm/generation` through functional head `cf4dc78a`, documentation head `acf3b40a`, and the containing ready mailbox commit. Land the cache-floor contract commit before the dependent lean-zip adaptation. No PR requested
next: W6/integration repairs and validates its newly landed card; W7 rebases, changes this mailbox to ready, and integration lands the cache-floor/raw package stack. Then W7 can migrate the remaining Level-1 eager initializer consumer to the lazy floor protocol and separately reduce per-call-site closure allocator code-size/build-time overhead
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
