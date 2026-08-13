# wasm-gen lane

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: f65205c82b46a0df1973742f1d34a21e79ccbdfd on main
functional-head: afc8b88548a9ae3ab1b9a9f053b3674ba4d58a74
contract-base: f65205c82b46a0df1973742f1d34a21e79ccbdfd on main; no shared semantic, concrete-runtime, symbolic-Wasm, or resident-helper signature changed
clean-at-update: true
slice: Publish the separately versioned Illuminate SpatialHitScene package on the accepted resident-container runtime. FIR compiles the real `Illuminate.SpatialHitScene.ofHitScene` and `Illuminate.SpatialHitScene.query` closure through a read-only Lean 4.33 source view. Spatial preparation runs once inside Wasm. Persistent queries use a thin borrowed façade generated with Lean's ownership convention, retain the source and Lean-built spatial graphs below a checkpoint, copy results, and rewind scratch. Production and diagnostic paths share bit-exact binary64 transport; no spatial algorithm is duplicated in JavaScript or FIR
files: W7-owned `integration/illuminate-spatial-hit-scene`; `bugs/FIR-BUG-wasm-none-spatial-hit-scene-retained-query-root.md`; this mailbox
contracts: none. The slice consumes the accepted semantic Wasm ABI, container runtime, resident helpers, allocator exports, and shared C/libm linker without changing a signature or W6 proof surface. The package-local borrowed façade is an ownership-correct call boundary, not a shared ABI
checks: Lean Beam refresh/save passed the compiler module with zero diagnostics after the container-runtime rebase. Focused 73-job Lake build passed. Deterministic repeat generation compared byte-identical frontier and complete Wasm. Node and Chrome each passed all 1,009 shared-oracle queries, bit-exact coordinates, 10,000 flat-frontier queries, independent scenes, repeated create/dispose, disposal and malformed-input failures, exact imports/exports, and checksums. The refreshed order-balanced benchmark passed 3 warmups and 9 measured rounds, checking all 1,009 results in every backend/round. `git diff --check` passed. `make check` passed 122 harness tests, 661/661 native-LCNF, 9/9 direct-machine, the complete 661-case native/LCNF/V8 triangle, 670 unique cases, 1,992/1,992 comparisons, zero findings, 162 valid bug cards, and trusted assumptions. `make talos-setup && make talos-check` passed all 3,143 jobs. `FIR_PRETTYM_EXHAUSTIVE_CHECKPOINTS=1 FIR_BROWSER=google-chrome bash integration/talos/artifact/check.sh` passed with exit 0, including deterministic prettyM publication, the complete resident catalog, repeated V8 triangle, Chrome Worker checks, 43 concrete artifacts, and 15 source probes
bug-cards: FIR-BUG-wasm-none-spatial-hit-scene-retained-query-root fixed. The initial owned query export trapped after preparing a retained graph; the thin `@& SpatialHitScene` façade makes the persistent host call obey Lean's generated ownership convention
blockers: none
artifacts: immutable package `integration/illuminate-spatial-hit-scene/_build/illuminate-spatial-hit-scene-06a9c64aaa7f61c7`; canonical pointer `integration/illuminate-spatial-hit-scene/_build/illuminate-spatial-hit-scene-current`; package SHA-256 `06a9c64aaa7f61c7539967d42219f912be82c5590a826cab7b94d6094a71141e`. Complete Wasm is 96,006 bytes, SHA-256 `366d84059bd0d0ffba6f77e1d68414dd93b512568359835b7b2620274c7afe74`; base Wasm is 61,489 bytes, SHA-256 `622912cf33c24208768f67f66d54ef5fac5eeb7cf72c2cfa9c75951ca5a0d595`; frontier is 170,354 bytes, SHA-256 `368c4c5f4379073e70b9a0ab250a396cf283164c371141f84b3b3bec3936b716`. It has zero imports, module-owned memory, two application entries, four arena controls, and memory. API `fir.illuminate-spatial-hit-scene.browser/v1`; layout `lean-4.33-Illuminate.SpatialHitScene/v1`; ownership `fir.illuminate-spatial-hit-scene.persistent-checkpoint/v1`
measurements: clean Illuminate commit `c8d321721262b5987226ae9626abf5ca3e1dfe9b`, descendant of requested pin `3b912826fdb39b27e214b3fef91c2b08c000bfea`, with all six source hashes and both fixture hashes exact. Closure: 194 declarations, 41 reviewed externals, 780 frontier functions, zero runtime operations; all 15 reviewed Float/libm frontier imports are closed in the final module. Refreshed median: reference 14.991 microseconds/query, spatial 15.932 microseconds/query, paired spatial delta 1.293ms over 1,009 queries. Median spatial creation 2.224ms, including 0.295ms projection, 1.109ms encoding, and 0.273ms Lean preparation. Persistent bytes 93,328; post-query frontier flat. Raw samples remain in ignored `_build/spatial-benchmark.json`
handoff: fast-forward `wasm/generation` from base `f65205c8` through functional head `afc8b885` and the containing ready mailbox commit. No PR requested
next: integration owner lands this green stack, then W7 starts the generic persistent lazy-cache initializer with lean-zip's focused `distanceCodeCacheProbe`
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
