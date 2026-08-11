# wasm-gen lane

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: e37175ba2db2139e9d85261287fee979eaa1beb5 on main
functional-head: 114a484010b92479e60a19ebacedd2152fff507c
contract-base: e37175ba2db2139e9d85261287fee979eaa1beb5 on main (Lean 4.33); Array and String ownership helpers are generation-ready only, with W6 refinement deliberately pending
clean-at-update: true
slice: Preserve Lean's uniqueness optimization across the generic resident Array core and String append/push paths, and make the Array-to-ByteArray bridge consume the newly live Array representation correctly. Fresh Arrays are live refcount-one objects; emptyWithCapacity preserves requested capacity; push, uset, and pop reuse exclusive storage and copy shared or persistent storage; growth is geometric; owned reads retain children; replicate and recursive Array release preserve child ownership. Strings retain their frozen header ABI while deriving capacity from allocation extent, reusing exclusive capacity for append/pushn, growing geometrically, and copying shared or persistent inputs. ByteArray.mk now accepts live or persistent Arrays and recursively consumes one owned Array reference after packing
files: Fir/Wasm/Emit/{ResidentArray.lean,ResidentByteArray.lean,ResidentContainerLayout.lean,ResidentReferenceCount.lean,ResidentRelease.lean,ResidentString.lean}; integration/talos/artifact/{resident-array-client.mjs,resident-byte-array-client.mjs,resident-string-client.mjs}; bugs/{FIR-BUG-wasm-none-array-unique-update.md,FIR-BUG-wasm-none-string-unique-update.md,FIR-BUG-wasm-none-byte-array-mk-owned-array.md}
contracts: The existing generic Array and String object layouts remain stable. Module-created Arrays and Strings now carry ordinary live refcount-one ownership. Capacity-fitting exclusive mutations preserve address and frontier; shared and persistent values use copy-on-write; generic release recognizes the shared ARRY layout marker and recursively releases the live Array prefix. String capacity is allocation extent minus the frozen header rather than new header metadata. ByteArray.mk accepts the live Array representation and consumes its owned input after packing. These executable helper semantics are generation-ready; W6 owns the corresponding refinement theorems
checks: Lean Beam update/sync returned zero diagnostics for ResidentString.lean and ResidentByteArray.lean. Beam repeatedly disconnected while processing the unusually large ResidentArray.lean, so its focused lake build, direct Lean check, real-engine fixture, and final dependency cones were used as the definitive checks. The pre-repair Array and String fixtures failed on persistent allocation/no-reuse, and the pre-repair ByteArray.mk fixture trapped on a valid live Array; all pass after repair. Focused artifacts passed: resident Arrays 10122 bytes, resident ByteArrays 8160 bytes, resident Strings 12027 bytes. After a conflict-free rebase onto current main e37175ba, git diff --check passed; make check passed 122 harness tests, 653/653 native-LCNF, 9/9 direct-machine, 653/653 native-LCNF-V8, 662 unique cases, 1968/1968 comparisons, 6829 machine steps, zero findings, 136 bug cards, and the Lean 4.33 trusted-assumption gate; make talos-setup retained Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254 and make talos-check passed 3143/3143 jobs; bash integration/talos/artifact/check.sh passed the complete deterministic resident/runtime/package cone, checksum and package checks, production prettyM stack-safety checks, and the 653-case V8 triangle
bug-cards: FIR-BUG-wasm-none-array-unique-update fixed; FIR-BUG-wasm-none-string-unique-update fixed; FIR-BUG-wasm-none-byte-array-mk-owned-array fixed
blockers: none for generation or integration. W6 refinement of the Array/String ownership and recursive-release helper contracts is pending. Array.swap, the expanded mutable ByteArray push/set/uset surface required by compressRaw/Level1, and the FloatArray family remain explicit fail-closed follow-up slices
artifacts: the post-rebase deterministic gate prepared tested prettyM package integration/talos/artifact/_build/prettyM-current-releases/1732591981df-37cbbfa392708468 with canonical pointer integration/talos/artifact/_build/prettyM-current; source prettyM Wasm is 122384 bytes and trace Wasm is 126462 bytes, reproduced byte-for-byte on the second emission
measurements: Array and ByteArray fixtures observe stationary frontier for capacity-fitting exclusive mutations and exact reference-count transitions for shared inputs. The String fixture observes zero-address-change/zero-frontier-growth for zero push, exclusive capacity reuse after geometric growth, shared refcount decrement, persistent copy-on-write, and borrowed-right preservation. No headline performance benchmark was run
handoff: integrate 6592e2cb77ef63aeca52c061ca0ea77c8c958aa8 first (generic Array ownership and recursive release), then 114a484010b92479e60a19ebacedd2152fff507c (String ownership and ByteArray.mk live-Array bridge), resolving this mailbox commit from wasm/generation. Both commits were rebased directly on main e37175ba after the proof-only staged-external lease landed. W6 owns refinement proofs; no PR is requested
next: hand the stable Array/String helper semantics to W6; then implement the exact ByteArray push/set/uset surface needed by Zip.Wasm.compressRaw/Level1, followed by Array.swap. Treat FloatArray as a separate packed-layout and ownership slice rather than broadening the current contract implicitly
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
