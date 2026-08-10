# wasm-gen lane

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: active
base: d7907814 on main
functional-head: c447a413
contract-base: d7907814 on main
clean-at-update: true
slice: The HitScene source-admission stack, exact W6 lazy-cache proof adaptation, and resident-artifact ratchet are accepted on main. Start the principled successor by freezing object/tagged/tobject transfer and heap-operation behavior before the shared compiler representation is split into source annotation, physical carrier, and semantic provenance
files: coordination/lanes/wasm-gen.md; generation-side examples will be added only after the integration-owned contract plan at docs/wasm-object-carrier-provenance-plan.md
contracts: consumes the accepted effectiveDeclarationResultKind? contract at c93bf226 and the object-carrier/provenance milestone at d7907814; no new shared contract, runtime signature, concrete layout, or helper change in this mailbox update
checks: PASS integrated git diff --check; PASS make check (642 unique cases, 1844/1844 comparisons equal, 119 active bug cards); PASS make talos-check (3131 jobs); PASS complete deterministic resident-artifact gate; PASS exact HitScene source probe (159 declarations, 34 externals, zero unsupported); PASS follow-up documentation make check with the same 642/1844 coverage
bug-cards: fixed FIR-BUG-wasm-none-closed-vec2-constant-admission; fixed FIR-BUG-wasm-none-endpoint-partial-application-admission; fixed FIR-BUG-wasm-none-lazy-cache-result-refinement
blockers: none; W6 can continue independent proof work until integration publishes a standalone descriptor/signature contract, and no answer is currently needed from Illuminate or Verso
artifacts: no executable HitScene Wasm package yet; the accepted compiler probe inventories 159 reachable declarations and 34 externals, including Float.abs, Float.sqrt, Float.sin, Float.cos, Float.acos, Float.atan2, Float.cbrt, and Float.floor
measurements: source capture is approximately 6.5 seconds and symbolic lowering approximately 62 seconds on the accepted probe; no execution-performance claim is made before resident math and external-engine acceptance exist
handoff: none; the previous compiler/proof/artifact stack is accepted on main through 4d91fb0d, and the object-carrier/provenance plan is accepted at d7907814
next: add the nine object-family transfer combinations and negative heap-operation fixtures without changing output; then introduce carrier/provenance descriptors alongside AbiKind on the integration branch. After that contract stabilizes, notify W6 and continue the zero-import HitScene resident-math package
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
