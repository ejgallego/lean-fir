# wasm-gen lane

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: be7eb51482235c2793f931a48d6dd3d65ff66f8a on main
functional-head: 53c8b9174d84b9694c52aa966bc4fdf04dad2d96
contract-base: be7eb51482235c2793f931a48d6dd3d65ff66f8a on main; consumes the accepted concrete closure-projection refinement and changes no shared contract
clean-at-update: true
slice: Publish Illuminate HitScene v2 from exact Illuminate revision 88dcfee895a55e804641bff485024cffec1b5419. Compile the real Illuminate.HitScene.query entry, transfer the v2 prepared path bounds and bit-exact coordinates, expose production and diagnostic query paths, retain one scene below a per-instance checkpoint, and publish a deterministic zero-import module. Also consume the already accepted W6 closure-projection refinement in the W7 concrete host and refresh the exact ByteArray blocker inventory for the landed closure-multiplicity and capture-topology fixtures
files: integration/illuminate-hit-scene/{CLIENT_HANDOFF.md,README.md,closure-contract.json,illuminate-hit-scene-browser-adapter.mjs,illuminate-source.json,package-smoke.mjs,package.mjs}; bugs/FIR-BUG-wasm-none-hitscene-v2-path-scalar-layout.md; integration/talos/artifact/{concrete-host.mjs,concrete-validation-case.mjs,test-concrete-closure-dispatch.mjs}
contracts: no shared Lean semantics, symbolic Wasm surface, concrete layout/runtime, or resident-helper signature changed. Package input layout advances to lean-4.32-Illuminate.HitScene/v2; browser API remains fir.illuminate-hit-scene.browser/v1 and ownership remains fir.illuminate-hit-scene.persistent-checkpoint/v1. The publisher now forces Lake reconfiguration at both external-source build and final-LCNF capture. The concrete host mirrors the existing directional AbiKind.refines rule and reads captures at their immutable descriptor kind
checks: Lean Beam 0.2.0-beta refresh/sync source-view probe passed with zero diagnostics and the temporary probe was removed; focused Lake external-source build passed with --reconfigure; FIR_HIT_SCENE_REQUIRE_REPEAT=1 publication passed fresh frontier and complete-link determinism; package SHA256SUMS and Node smoke passed 301 fixture queries, 10000 flat-frontier queries, independent instances, disposal/error paths, production/diagnostic parity, and bit-exact coordinates; node integration/talos/artifact/test-concrete-closure-dispatch.mjs passed exact object/tagged-to-tobject widening and reverse-direction rejection; git diff --check passed; final make check passed with 122 harness tests, 650 unique cases, 641/641 native-LCNF, 9/9 direct-machine, 641/641 native-LCNF-V8, 1932/1932 aggregate comparisons, zero findings, and 129 active bug cards; make talos-check passed all 3133 jobs on Talos a01d01c; bash integration/talos/artifact/check.sh passed, including 600/641 concrete product executions and the exact 41-case ByteArray blocker inventory
bug-cards: FIR-BUG-wasm-none-hitscene-v2-path-scalar-layout fixed; consumed fixed FIR-BUG-wasm-none-closure-projection-kind-refinement; refreshed the exact inventory governed by fixed FIR-BUG-wasm-none-concrete-blocker-inventory-validation-growth
blockers: none for W7 publication. Illuminate consumer acceptance remains downstream and intentionally runs in its own worktree
artifacts: immutable package integration/illuminate-hit-scene/_build/illuminate-hit-scene-7daab5f2bb96f121; canonical pointer integration/illuminate-hit-scene/_build/illuminate-hit-scene-current; package SHA-256 7daab5f2bb96f121b5117c5829d91e27941e1a727c937f3704d2d5dd4b721964; complete Wasm 46089 bytes SHA-256 06708aac339cd7f6f7fcbe7c973dc29125e263925635d0311a0571d4428e97b7; base Wasm 30965 bytes SHA-256 366245b7876d1d719632fcdd0b31e0330c743876fa9f6264e966f568bcec5027; frontier 73323 bytes SHA-256 fa3dd1aa15bbd66cdec287bb449861935c87d2ab61a9c82fedf09c2adadcff33; zero function/memory imports; exact exports Illuminate.HitScene.query, Illuminate.HitScene.query._fir_bit_exact, fir_heap_frontier, fir_heap_set_frontier, fir_heap_rewind, fir_heap_alloc, and module-owned memory
measurements: 162 captured source declarations, 34 reviewed externals, 444 frontier functions, 15 standard Float/libm operations before complete linking, zero runtime operations after linking; encoded fixture scene 4464 bytes below checkpoint 70000; 10000 post-checkpoint queries retain a flat frontier
handoff: integrate the rebased W7 stack through functional head 53c8b9174d84b9694c52aa966bc4fdf04dad2d96 and publish the immutable package to Illuminate. No PR is requested
next: Illuminate runs ILLUMINATE_FIR_HIT_SCENE_DIR=/home/egallego/lean/fir/.worktrees/wasm-generation/integration/illuminate-hit-scene/_build/illuminate-hit-scene-7daab5f2bb96f121 npm run accept:fir-hit-scene; then W7 repins the resolved Verso HTML source at 2ee1c804 and resumes zero-import publication; ROOT-FIR-20260811-001..003 follow as secondary generator/verifier/toolkit work
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
