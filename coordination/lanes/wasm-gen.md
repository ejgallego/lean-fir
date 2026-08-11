# wasm-gen lane

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: 41cd4b2912a0ba9903e9612aba560da3197ad93a on main
functional-head: 5033d79776b72bae3e8d11e7852c0b3db5f0a9d7
contract-base: 41cd4b2912a0ba9903e9612aba560da3197ad93a on main; packed ByteArray layout/ownership v2 is generation-ready only, with W6 refinement deliberately pending
clean-at-update: true
slice: Repair packed resident ByteArray ownership so the compiled runtime preserves Lean's uniqueness optimization. Fresh ByteArrays now have live nonpersistent refcount-one ownership; ByteArray.copySlice mutates an exclusive capacity-fitting destination in place, copies and consumes one reference for shared/growing destinations, and never mutates persistent boundary input. Add a real-engine regression that failed against the v1 always-persistent helper, bump the package layout/ownership contract to v2, and republish the real Zip.Wasm.compressStored package from a clean rebased head
files: Fir/Wasm/Emit/ResidentByteArray.lean; bugs/FIR-BUG-wasm-none-byte-array-unique-update.md; integration/talos/artifact/resident-byte-array-client.mjs; integration/lean-zip/{README.md,closure-contract.json,lean-zip-stored-browser-adapter.mjs,package-smoke.mjs,package.mjs}
contracts: fir.wasm.byte-array/v2 retains the checked 32-byte packed layout but gives module allocations ordinary Lean reference counts. The unique copySlice path preserves address and frontier exactly when capacity suffices, flags are live nonpersistent, and refcount is one. Shared and growing paths allocate with Lean's exact/geometric rule and consume one ordinary destination reference; persistent values are copied without decrement. The browser adapter API remains fir.lean-zip.stored.browser/v1; ownership is fir.lean-zip.stored.scratch-transfer/v2, with borrowed persistent encoded input, copied output, and no raw address exposure
checks: Rebased conflict-free onto main 41cd4b29. Lean Beam update returned zero diagnostics; focused resident ByteArray real-engine fixture passed; git diff --check passed; make check passed 122 harness tests, 653/653 native-LCNF, 9/9 direct-machine, 653/653 native-LCNF-V8, 662 unique cases, 1968/1968 comparisons, 6829 machine steps, zero findings, 133 bug cards, and the trusted-assumption gate; make talos-setup pinned Talos a01d01c778b794dd00956748a067b6793c2c9f9b and make talos-check passed 3133/3133 jobs; bash integration/talos/artifact/check.sh passed the complete deterministic resident/runtime/package cone and 653-case V8 triangle; integration/lean-zip/check.sh passed deterministic double emission, SHA256SUMS, Node smoke, native/Wasm equality on 10 cases through 1 MiB, inflateRaw round trips, two instances, malformed input, flat scratch frontier, injected clock, and headless Chrome
bug-cards: FIR-BUG-wasm-none-byte-array-unique-update fixed. Before the repair, the fixture failed with `emptyWithCapacity unique flags: expected 2, got 3`; it now also checks stationary-frontier reuse, growth release, shared copy-on-write/refcount decrement, and persistent copy-on-write
blockers: none for generation, Stored correctness, or publication. W6 refinement of the v2 ownership/helper contract is pending. This slice does not claim that the older resident Array family already preserves all analogous uniqueness paths
artifacts: immutable package integration/lean-zip/_build/lean-zip-stored-packages/5033d79776b7-30737b4e2ebf-5b649bec770fb41979d9; canonical pointer integration/lean-zip/_build/lean-zip-stored-current; complete Wasm 11667 bytes SHA-256 a639faedf81e1812d5fe9bb535aaced79b7230699c541b049eb0e4b08424870b; base Wasm 1884 bytes SHA-256 148e43a85c855f788e327118d9b57df9d5cdb2488e4b673cc6f3c671902a3017; zero function and memory imports; exact function exports Zip.Wasm.compressStored, fir_heap_frontier, fir_heap_set_frontier, fir_heap_rewind, and fir_heap_alloc plus module-owned memory
measurements: exact capture has 21 declarations, 14 externals, zero unsupported declarations, 7 retained source functions, 66 resident helpers, 73 complete functions, zero residual runtime operations, and zero imports. The uniqueness fixture observes zero frontier growth for a capacity-fitting exclusive copySlice
handoff: integrate functional head 5033d797 after resolving this mailbox commit from wasm/generation. The branch is based directly on main 41cd4b29 and includes the prior packed ByteArray/Stored package commits plus this v2 repair. The helper implementation and real-engine checks are generation-ready; W6 owns refinement proofs. No PR is requested
next: give W6 the v2 ownership contract for proof adaptation; then audit other mutable resident families for the same always-persistent shortcut before expanding the exact ByteArray surface required by Zip.Wasm.compressRaw/Level1
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
