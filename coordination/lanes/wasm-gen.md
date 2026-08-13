# wasm-gen lane

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: 0ebc8b428a7194709030c97f9fa9aeba037d75b1 on main
functional-head: 2cb6dfeec6128789963fc33705b95d45b4d7b508
contract-base: 0ebc8b428a7194709030c97f9fa9aeba037d75b1 on main. The exported allocator signatures remain unchanged. Object-valued compiler cache publication advances a private persistent floor and generated `fir_heap_rewind` clamps to that floor. Production packages retain compiler constants at their original lazy use sites; the former eager closure walk is retained only behind explicitly unsafe diagnostic APIs. `Float.log2` is part of the checked standard-math contract. W6 refinement of the cache-floor behavior is pending and does not block generation-ready status; W7-W6-20260813-001 records the proof request
clean-at-update: true
slice: Compile and package the real read-only `Zip.Wasm.compressRaw : ByteArray -> UInt8 -> ByteArray` entry for production raw-DEFLATE levels 1 through 10, then migrate the older `Zip.Wasm.compressLevel1 : ByteArray -> ByteArray` package from an eager compiler-cache initializer to the same generic lazy cache-floor protocol. The generic resident frontier closes fixed-width, arbitrary-Nat, scalar-box, Array/ByteArray, and direct Float comparison operations; the checked standard runtime closes exactly `Float.ofNat`, `Float.ofScientific`, and `Float.log2`. Binary-only meta-DCE scales the external-runtime link. A cold object-cache miss recursively publishes persistence and advances the rewind floor; an immediate warm repeat rewinds exactly flat. Both browser adapters transfer packed ByteArrays, reserve runtime memory, copy outputs, expose timings/memory diagnostics, and never expose raw addresses
files: W7-owned `Fir/Wasm/Emit/ResidentAllocator.lean`, `ResidentCache.lean`, resident scalar/Nat/fixed-width/Float families and linker; `integration/wasm-runtime`; `integration/lean-zip`; W7 bug cards; `integration/talos/artifact/resident-cache-client.mjs`; this mailbox
contracts: generation-ready cache-aware rewind behavior as described in contract-base, with unchanged public Wasm ABI; reviewed standard-math frontier extended by exact `Float.log2`; no LCNF semantic/interpreter contract changed. Binaryen linking enables multivalue and removes private runtime exports with binary `wasm-metadce`, preserving the exact frontier export inventory. The diagnostic eager-initializer Lean API and manifest key are explicitly renamed unsafe; production packages use ordinary lazy linking
checks: after conflict-free rebase onto main `0ebc8b42`, Lean Beam refresh/save passed `ResidentCache` and `ResidentLinker` with zero diagnostics. Focused lean-zip build passed 157 jobs. Raw probe passed with 702 captured declarations, 128 reviewed externals, 0 unsupported declarations, exactly 3 reviewed math imports at the frontier, and 0 runtime operations. Level-1 probe passed with 432 declarations, 108 externals, 0 unsupported declarations, 0 imports, and 0 runtime operations. Focused resident-cache artifact passed in real Wasm (2,520 bytes). Node and Chrome package smokes passed: cold cache publication monotonically advances the floor; immediate warm repeats return equal bytes and rewind exactly flat. Clean immutable raw and Level-1 package generation emitted each artifact twice and compared byte-identical bytes/descriptors/runtime. Raw native/Wasm equality plus independent inflate passed 5 inputs at all 10 levels; Level-1 native/Wasm equality passed 5 inputs. `git diff --check` passed. `make check` passed 125 harness tests, 676/676 native-LCNF, 9/9 direct-machine, the complete 676-case native/LCNF/V8 triangle, 685 unique cases, 2,037/2,037 comparisons, zero findings, 175 valid bug cards, and trusted assumptions. `make talos-check` passed 3,144 jobs. `bash integration/talos/artifact/check.sh` passed the complete resident/source/prettyM/concrete, deterministic artifact, and V8 gates. `make talos-setup` had already passed at Talos `0e05edbc`
bug-cards: FIR-BUG-wasm-none-raw-deflate-generic-resident-frontier fixed; FIR-BUG-wasm-none-external-runtime-link-multivalue fixed; FIR-BUG-wasm-none-external-runtime-link-wat-size fixed; FIR-BUG-wasm-none-persistent-cache-eager-panic fixed by the raw and Level-1 production migrations
blockers: none
artifacts: raw immutable package `integration/lean-zip/_build/lean-zip-raw-packages/850225165263-30737b4e2ebf-3bb480fc737d06e89d4e`; canonical pointer `integration/lean-zip/_build/lean-zip-raw-current`; BUILD SHA-256 `a08badcf219a31851d02a9425cb2113beaf6c60d6a32bf6afc337e6469c6f13c`. Complete raw Wasm is 1,753,527 bytes, SHA-256 `431007aefe59858f913845a8f540800c5e4c503dabebd6a21d27dcf0e21d289c`; base is 1,888,508 bytes, SHA-256 `d03549469c5a4287eba2a06c313b9b860405024c2b90a0ab4ad241467578f42e`; frontier is 3,265,324 bytes, SHA-256 `c8c57995f49ed0dcec035f43e92f2e17791c5b7ad0994bb03278d4c2b8631938`. Level-1 immutable package `integration/lean-zip/_build/lean-zip-level1-packages/2cb6dfeec612-30737b4e2ebf-b72556c9e7bcd8388bc5`; canonical pointer `integration/lean-zip/_build/lean-zip-level1-current`; BUILD SHA-256 `a2166f3781651086d407d9739ff378464d3c79ebe3acfa3b2573642318c1c728`. Complete Level-1 Wasm is 508,708 bytes, SHA-256 `e920239ddc907914844711eaa2f17a2bf378c0cb6962a63238174983b53a763f`; base is 218,625 bytes, SHA-256 `65c95b04877da5430310cf50dab879a1e602e6cbd57bcd46a83e0597c9c02b05`. Both complete modules have zero imports, module-owned memory, one application entry, four arena controls, and memory. Raw uses BUILD/adapter/ownership v2; Level-1 uses BUILD `fir.lean-zip.level1.build/v3`, adapter `fir.lean-zip.level1.browser/v3`, and ownership `fir.lean-zip.level1.lazy-cache-floor/v3`
measurements: clean raw FIR source `850225165263172608fa485cac87540244bd1558`; clean Level-1 FIR source `2cb6dfeec6128789963fc33705b95d45b4d7b508`; clean lean-zip `30737b4e2ebfd0fc889f0b2e265aae0635d668a1`; clean zipCommon `4425bab1f9522307d77e8d485bc536149ba31c36`; Lean 4.33.0 commit `d8b18978`; Emscripten 5.0.3. Raw retains 574 source functions and 5,265 classified resident/lowering helpers. Level-1 retains 324 source functions and 1,552 helpers; removing eager initialization reduced its base by 3,076 bytes and its complete artifact by 2,259 bytes
handoff: integration may fast-forward the rebased `wasm/generation` stack through functional head `2cb6dfee` and the containing ready mailbox commit. Land the cache-floor runtime commits before the dependent raw and Level-1 package adaptations. The raw functional prefix is `85022516`; the Level-1 migration completes at `2cb6dfee`. No PR requested
next: after integration, reduce per-call-site closure allocator helper/code-size/build-time overhead on the compilation-performance branch; keep generic Array/ByteArray proof refinement with W6 while W7 consumes stable signatures
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
