# wasm-gen lane

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: 8051df3c7430df5688035973635e66b058bff502 on main
functional-head: 45ee2ff9a919bff15713381d60a17c4d82c5a700
contract-base: f996628c736546c85a87795fc6d95c694baf0a48 on main (Lean 4.33 and accepted generic object-family call ABI); the branch is rebased over validation acceptance 8051df3c. New tagged partial-application, scalar projection/boxing, promoted-literal, and fixed-width helpers are generation-ready only, with W6 refinement deliberately pending
clean-at-update: true
slice: Capture the real Zip.Wasm.compressLevel1 final-LCNF closure through the generic single-unit source path, drive its resident runtime-operation frontier from 55 to zero, and internalize the first 30 ordinary fixed-width declaration imports. The generic fixed-width family now covers 35 exact UInt8/UInt16/UInt32/UInt64 operations and preserves the Lean 4.33 result-lane distinction: UInt8.toNat and UInt16.toNat return tagged, whereas UInt32.toNat returns tobject. The real Level1 closure now links 1696 resident functions with 47 remaining declaration imports and zero runtime operations, down from 1666 functions and 77 imports
files: Fir/Wasm/Emit/{ResidentClosureAllocation.lean,ResidentFallback.lean,ResidentFixedWidth.lean,ResidentLiteral.lean,ResidentRuntime.lean,ResidentScalarBox.lean}; integration/lean-zip/{LeanZipFir/Compile.lean,ProbeLevel1.lean}; integration/talos/artifact/{FirWasmSourceExample.lean,concrete-validation-case.mjs,resident-closure-allocation-client.mjs,resident-closure-projections-client.mjs,resident-fixed-width-client.mjs,resident-literal-client.mjs,resident-read-projections-client.mjs,resident-scalar-box-client.mjs}; bugs/FIR-BUG-wasm-none-{lean-zip-level1-final-capture-u8,lean-zip-fixed-width-import-frontier,partial-apply-tagged-result,available-fallback-requires-pair,scalar-closure-projection-widths,integer-box-kind-coverage,packed-scalar-projection-kinds,promoted-natural-literal}.md
contracts: no shared contract changed after contract-base. W7 reuses the accepted symbolic Wasm instruction, eight-byte scratch, resident natural, allocator, and physical object-family ABI surfaces. The added executable helpers and exact signatures are generation-ready; W6 owns their implementation-to-concrete-runtime refinement. The two-line concrete-validation ratchet only admits the new main fixtures to the existing explicit ByteArray-layout blocker set (47 total); it does not alter execution semantics or weaken fail-closed checks
checks: Lean Beam refresh/save for Fir/Wasm/Emit/ResidentFixedWidth.lean passed with zero errors. Focused zero-import external-engine fixed-width fixture passed all 35 exports and exact scratch restoration; emitted module 7793 bytes. Real Lean 4.33 Level1 probe captured 391 declarations and 110 externals with zero unsupported declarations and zero runtime operations; latest measured generation linked 1696 functions and retained 47 declaration imports (capture 26532ms, lower 229662ms, link 384636ms). git diff --check passed. Post-rebase make check passed 122 harness tests, 655/655 native-LCNF, 9/9 direct-machine, the 655-case native-LCNF-V8 triangle, 664 unique cases, 1974/1974 comparisons, 6922 machine steps, zero findings, 145 active bug cards, and the trusted-assumption gate. make talos-setup retained Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254; make talos-check passed 3143/3143 jobs. bash integration/talos/artifact/check.sh passed after ratcheting the two new main fixtures: all resident helpers, deterministic double generation, complete checksum/package/browser/stack-safety cone, 608/655 concrete cases executed with exactly 47 ByteArray-layout blockers, and the repeated 655-case V8 triangle
bug-cards: FIR-BUG-wasm-none-lean-zip-fixed-width-import-frontier confirmed (30-import checkpoint; 25 fixed-width/USize imports remain); FIR-BUG-wasm-none-partial-apply-tagged-result confirmed (generation passes; W6 semantic proof bridge pending); all previously reported capture/fallback/scalar/literal cards in this slice fixed
blockers: none for generation or integration. The Level1 artifact is not yet import-free: 47 explicit Lean declaration imports remain, consisting of 13 USize, 8 ByteArray, 7 UInt64, 6 Array, 4 Nat, 3 UInt32, 2 UInt16, 2 List, 1 System.Platform, and 1 String declaration. There are no hidden/runtime-operation imports. W6 proof adaptation remains a parallel follow-up
artifacts: deterministic prettyM gate prepared integration/talos/artifact/_build/prettyM-current-releases/45ee2ff9a919-b218bd58b9ec674b with canonical pointer integration/talos/artifact/_build/prettyM-current; source prettyM Wasm remains 138755 bytes and trace Wasm 142833 bytes, reproduced byte-for-byte. Level1 remains an inventory probe, not a published package
measurements: Level1 runtime frontier moved 55 -> 5 -> 2 -> 0 across generic helper slices. Its explicit declaration frontier then moved 77 -> 47 by adding 30 exact fixed-width helpers. No execution benchmark was run because the module is not yet import-free. Generic compile-path profiling was handed to isolated branch perf/compilation-perf through local mailbox W7-ROOT-20260812-022
handoff: integrate the eight commits in order from base 8051df3c: a5dac8d8 (real Level1 closure probe), 604887c9 (generic single-unit capture), 9f0efdf5 (object-family/fallback resident linking), 2bd4bab6 (generic scalar/literal resident operations), 4cb6bdc3 (zero-runtime inventory reporting), acf9e831 (prior status checkpoint), 4bc7edf3 (generic fixed-width frontier), and 45ee2ff9 (validation-ratchet adaptation), resolving this mailbox commit from wasm/generation. No W6-owned file or shared contract changed; no PR is requested
next: close the remaining 25 fixed-width/USize declarations without widening the symbolic instruction surface where avoidable, then address the 22 container/Nat/List/String/platform declarations. Ratchet the real Level1 probe after each generic family until the declaration frontier reaches zero, then emit and differential-test the actual lean-zip package
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
