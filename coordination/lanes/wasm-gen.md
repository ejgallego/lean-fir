# wasm-gen lane

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: 0c1e5b9111d68f72a0f6c5ca4dcebb07a4e90fdb on main
functional-head: 9bd136d77b334495c88683eb2c296a893bc25ffa
contract-base: 0c1e5b9111d68f72a0f6c5ca4dcebb07a4e90fdb on main; no shared contract changed. The helpers are W7 generation-ready surfaces and W6 refinement remains independent
clean-at-update: true
slice: Finish the generic fixed-width and USize frontier, distinguish base String helpers from complete-link additions, internalize generic Array mutation and List conversion operations, and provide the exact wasm32/Lean64 System.Platform.getNumBits helper. The real Lean 4.33 Zip.Wasm.compressLevel1 closure remains 391 declarations and 110 externals with zero unsupported declarations and zero runtime operations; its explicit import frontier moves 47 -> 22 -> 18 -> 17 -> 15 while the linked module reaches 1,730 functions
files: Fir/Wasm/Emit/{ResidentArray.lean,ResidentFixedWidth.lean,ResidentLinker.lean,ResidentPlatform.lean,ResidentString.lean,ResidentUSize.lean}; integration/talos/artifact/{FirWasmArtifactMain.lean,check.sh,concrete-validation-case.mjs,resident-array-client.mjs,resident-fixed-width-client.mjs,resident-platform-client.mjs,resident-string-client.mjs,run-resident-platform.mjs,run-resident-string.mjs}; bugs/FIR-BUG-wasm-none-lean-zip-{fixed-width-import-frontier,container-import-frontier}.md
contracts: none. W7 consumes the accepted symbolic Wasm, concrete object layout, reference-counting, resident String, arbitrary-precision Nat, allocator, and module-memory surfaces. No W6-owned file changed. Array.mk and Array.toList implement the actual generic List/Array ownership boundary, including unique/shared/persistent inputs, without a host fallback
checks: Lean Beam update/sync/save passed ResidentArray with zero diagnostics. Focused dependency-cone lake builds passed. Standalone zero-import Node fixtures passed 61 fixed-width/USize helpers, String USize.repr, four Array mutation helpers, Array.mk/Array.toList, and System.Platform.getNumBits; resident Array Wasm is 14,558 bytes. After rebasing on the indexed validator c792df8c, the real Level1 probe passed with 391 declarations, 110 externals, zero unsupported declarations, zero runtime operations, 1,730 linked functions, and exactly 15 imports (capture 54,040ms; lower 13,876ms; link 108,402ms). git diff --check passed; make check passed 122 harness tests, 661/661 native-LCNF, 9/9 direct-machine, the 661-case native/LCNF/V8 triangle, 670 unique cases, 1,992/1,992 comparisons, 7,176 machine steps, zero findings, 147 active bug cards, and the trusted-assumption gate; make talos-check rebuilt and passed 3,143/3,143 jobs; bash integration/talos/artifact/check.sh passed all resident-helper, deterministic double-generation, package/checksum/browser/stack-safety, repeated V8-triangle, 44/44 concrete-artifact, and 15/15 source-probe checks with 608/661 concrete cases executed and exactly 53 ByteArray-layout blockers. The final cache-only rebase on 0c1e5b91 passed the ResidentArray dependency cone and regenerated the exact 14,558-byte zero-import module under a writable user toolchain cache; its Node ownership fixture passed
bug-cards: FIR-BUG-wasm-none-lean-zip-fixed-width-import-frontier fixed; FIR-BUG-wasm-none-lean-zip-container-import-frontier confirmed and ratcheted to the exact remaining 15-import production frontier. No new semantic discrepancy was found
blockers: none for integration. Level1 publication remains blocked on eight ByteArray operations, four Nat operations, two compiler-generated List specializations, and String.ofList. ByteArray work is isolated on wasm/gen-bytearray-level1; W7 must not duplicate it
artifacts: deterministic prettyM gate prepared integration/talos/artifact/_build/prettyM-current-releases/404ae51aa824-496a12820a9f9aa3 with canonical pointer integration/talos/artifact/_build/prettyM-current; prettyM and PrettyTrace remain byte-for-byte reproducible at 138,755 and 142,833 bytes. Level1 remains an inventory probe until its 15 imports reach zero
measurements: final-base real Level1 capture 54.040s, lower 13.876s, resident link 108.402s, approximately 176.3s total. The accepted indexed symbolic-validation change reduces link time another 9.6% from 119.920s and 49.7% from the earlier 214.664s. In the deterministic gate, prettyM frontend generation fell from roughly 12-14s to 4.6s and PrettyTrace from roughly 6-7s to 2.3s while preserving exact bytes
handoff: fast-forward the six functional commits from 0c1e5b91 through functional head 9bd136d7 in order: e547986b fixed-width/USize closure, c7f9287f String helper inventory distinction, 696dac3e Array mutation, 145429c9 target platform width, 64ff6161 Array/List conversions, and 9bd136d7 dictionary ByteArray blocker ratchet; resolve this containing status commit from wasm/generation. No PR is requested
next: coordinate with wasm-gen-2 on the eight ByteArray imports; independently implement the principled generic Nat frontier, then String.ofList and capture-based resolution of the two generated List specializations. Ratchet the real Level1 probe after each family until the artifact is zero-import and publishable
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
