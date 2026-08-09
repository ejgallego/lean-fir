# wasm-gen lane

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: 691e00b93ccd78a300a5ad03f3039e87793a9d5e on main
functional-head: fb2c922a1b94a01c146fbc6072e5aa01c2ea0d96
contract-base: 691e00b93ccd78a300a5ad03f3039e87793a9d5e on main
clean-at-update: true
slice: Replay Lean 4.32 postponed final-LCNF module groups through the upstream-aligned private target-module environment and capture the real Illuminate.HitScene.query closure without copying Illuminate code; add the pinned HitScene source probe and classify the remaining admission frontier
files: Fir/Wasm/Emit/CompilerPrivate.lean; Fir/Wasm/Emit/Source.lean; integration/illuminate-hit-scene/; bugs/FIR-BUG-wasm-none-closed-vec2-constant-admission.md; bugs/FIR-BUG-wasm-none-endpoint-partial-application-admission.md; this mailbox
contracts: no shared semantic, signature, layout, or runtime change in this slice; compileEntryModuleWiseInternalized is a W7 source-generation API that follows leanir's postponed-group replay. The remaining endpoint partial-application repair is explicitly not worked around here because either precise boxed-result propagation or broader object-family closure compatibility crosses the integration-owned lowering contract and may affect W6 closure-projection proofs
checks: PASS Lean Beam sync/save with zero diagnostics for Fir/Wasm/Emit/CompilerPrivate.lean and Fir/Wasm/Emit/Source.lean, plus zero Probe.lean errors; PASS lake build Fir.Wasm.Emit.Source; PASS lake --keep-toolchain -KilluminateRoot=/tmp/illuminate-hit-scene-pinned build IlluminateFirHitScene.Compile; PASS lake --keep-toolchain -KilluminateRoot=/tmp/illuminate-hit-scene-pinned env lean -DmaxHeartbeats=0 Probe.lean (159 reachable declarations, 34 externals, two unsupported declarations at the single endpoint partial-application frontier); PASS git diff --check; PASS make check (642 unique cases, 1844/1844 comparisons equal, 119 active bug cards); PASS make talos-check (3131 jobs)
bug-cards: fixed FIR-BUG-wasm-none-closed-vec2-constant-admission; candidate FIR-BUG-wasm-none-endpoint-partial-application-admission; no workaround
blockers: HitScene artifact generation is waiting at one shared compiler-admission frontier: Illuminate.endpointToCenter._closed_1 partially applies an object-parameter function to a compiler-generated boxed Float whose declaration result is typed as tobject. FIR requires actual.refines expected at partial application even though ordinary calls and joins accept the common Lean object-family representation. No answer is currently needed from Illuminate or Verso
artifacts: no HitScene Wasm package yet; probe inventory contains 159 reachable final-LCNF declarations and 34 externals, including Float.abs, Float.sqrt, Float.sin, Float.cos, Float.acos, Float.atan2, Float.cbrt, and Float.floor; exact diagnostic files are generated under integration/illuminate-hit-scene/_build and intentionally ignored
measurements: source capture and lowering probe completes in approximately 7.3 seconds on the current worktree; no execution-performance claim is made before resident math and external-engine acceptance exist
handoff: integration may fast-forward the green wasm/generation stack through functional head fb2c922a and its containing mailbox commit, then synthesize the checkpoint into coordination/BOARD.md. For the dependent HitScene milestone, integration should open a shared-contract queue record for FIR-BUG-wasm-none-endpoint-partial-application-admission, prefer precise boxed-result propagation if it preserves existing refinement premises, and notify W6 before any alternative that broadens closure capture/projection compatibility
next: after the shared admission repair lands and W7 rebases, confirm the 159-declaration closure has zero unsupported source declarations; then implement the eight resident Float/math operations without JavaScript Math imports, publish the module-owned-memory HitScene package, and run the 301-query plus 10000-query bounded-frontier acceptance suite
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
