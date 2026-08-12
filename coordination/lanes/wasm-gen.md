# wasm-gen lane

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: f996628c736546c85a87795fc6d95c694baf0a48 on main
functional-head: c61a9d1b32f95fee3233cd468c2ed1371d32faa8
contract-base: f996628c736546c85a87795fc6d95c694baf0a48 on main (Lean 4.33 and accepted generic object-family call ABI); new tagged partial-application, scalar projection/boxing, and promoted-literal helpers are generation-ready only, with W6 refinement deliberately pending
clean-at-update: true
slice: Capture the real Zip.Wasm.compressLevel1 final-LCNF closure through the generic single-unit source path and drive its resident runtime frontier from 55 unresolved operations to zero. Generic fixes include object-family/tagged partial-application results, capability-sensitive fallback subsets, UInt16/UInt64/USize closure projections, complete packed scalar projection loads, UInt16/UInt32 integer boxing, and promoted tagged natural literals. The probe now reports linked function/import/runtime inventories and distinguishes linking errors from a successful empty frontier
files: Fir/Wasm/Emit/{ResidentClosureAllocation.lean,ResidentFallback.lean,ResidentLiteral.lean,ResidentRuntime.lean,ResidentScalarBox.lean}; integration/lean-zip/{LeanZipFir/Compile.lean,ProbeLevel1.lean}; integration/talos/artifact/{FirWasmSourceExample.lean,resident-closure-allocation-client.mjs,resident-closure-projections-client.mjs,resident-literal-client.mjs,resident-read-projections-client.mjs,resident-scalar-box-client.mjs}; bugs/FIR-BUG-wasm-none-{lean-zip-level1-final-capture-u8,partial-apply-tagged-result,available-fallback-requires-pair,scalar-closure-projection-widths,integer-box-kind-coverage,packed-scalar-projection-kinds,promoted-natural-literal}.md
contracts: no shared contract changed after base. W7 implements the accepted physical object-family calling convention for tagged closure-result annotations; capture and ValueRel remain directional. Resident scalar helpers reuse the existing eight-byte slot, promoted-natural header, allocator, and semantic tagged limit. These executable semantics and helper signatures are generation-ready; W6 owns the implementation-to-concrete-runtime theorems, including the active tagged partial-application semantic bridge
checks: Lean Beam update/sync returned zero diagnostics for every edited Lean helper. Focused zero-import V8/concrete-host guards pass: closure allocation 2070 bytes; closure projections 2181 bytes; scalar boxing 1912 bytes with exhaustive 65536-value UInt16 roundtrip and UInt32 immediate/promoted boundary; packed read projections 1101 bytes with bit-exact UInt64; literals 1802 bytes with exact promoted 4294967296 header/payload/frontier. The real Level1 probe captured 391 declarations, 110 externals, zero unsupported declarations, lowered successfully, linked 1666 resident functions, retained 77 explicit declaration imports and zero runtime operations (last run capture 23210ms, lower 109482ms, link 282497ms). git diff --check passed; make check passed 122 harness tests, 653/653 native-LCNF, 9/9 direct-machine, the 653-case native-LCNF-V8 triangle, 662 unique cases, 1968/1968 comparisons, 6829 machine steps, zero findings, 144 active bug cards, and the trusted-assumption gate; make talos-setup retained Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254 and make talos-check passed 3143/3143 jobs; bash integration/talos/artifact/check.sh passed all resident helpers, deterministic double generation, complete checksum/package/browser/stack-safety cone, and the repeated 653-case V8 triangle
bug-cards: FIR-BUG-wasm-none-lean-zip-level1-final-capture-u8 fixed; FIR-BUG-wasm-none-available-fallback-requires-pair fixed; FIR-BUG-wasm-none-scalar-closure-projection-widths fixed; FIR-BUG-wasm-none-integer-box-kind-coverage fixed; FIR-BUG-wasm-none-packed-scalar-projection-kinds fixed; FIR-BUG-wasm-none-promoted-natural-literal fixed; FIR-BUG-wasm-none-partial-apply-tagged-result confirmed (generation passes; W6 semantic proof bridge pending)
blockers: none for generation or integration. The Level1 artifact is not yet import-free because 77 explicit Lean declaration helpers remain; there are no hidden/runtime-operation imports. W6 proof adaptation for the new executable helper cases remains parallel follow-up
artifacts: deterministic prettyM gate prepared integration/talos/artifact/_build/prettyM-current-releases/0dae694fcfb9-878dfea1976a58a5 with canonical pointer integration/talos/artifact/_build/prettyM-current; source prettyM Wasm remains 138755 bytes and trace Wasm 142833 bytes, reproduced byte-for-byte. Level1 is currently an inventory probe, not a published package
measurements: Level1 closure runtime frontier moved 55 -> 5 -> 2 -> 0 across generic helper slices while its explicit declaration frontier remained 77. No headline execution benchmark was run because the module is not yet import-free
handoff: integrate the five commits in order: 8eb06afa (real Level1 closure probe), 0dae694f (generic single-unit capture), 337f8586 (object-family/fallback resident linking), a91917d9 (generic scalar/literal resident operations), c61a9d1b (zero-runtime inventory reporting), resolving this mailbox commit from wasm/generation. All are based directly on main f996628c; no W6-owned file changed and no PR is requested
next: audit the 77 explicit imports by generic capability family. Prioritize the existing fixed-width/USize/Nat surface, then Array/ByteArray helpers including Array.swap and the UInt32/UInt64 LE accessors. Ratchet the Level1 probe after each family until the declaration frontier reaches zero, then emit and differential-test the actual package
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
