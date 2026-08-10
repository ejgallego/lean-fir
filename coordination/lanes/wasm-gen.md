# wasm-gen lane

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: 31b9290c on main
functional-head: 5a4fc4e0
contract-base: 31b9290c on main
clean-at-update: true
slice: Published the real Illuminate.HitScene.query as a clean immutable zero-import package. Added bit-exact Float32/Float closure capture/projection, the resident closure-application ownership protocol, and rewind-safe fresh lazy-singleton publication through the existing recursive cache persistence helper. Kept physical layout/discriminator fixtures stateless while production-linked helpers enable matcher-to-projection ownership
files: Fir/Wasm/Emit/ResidentCache.lean; Fir/Wasm/Emit/ResidentClosureAllocation.lean; Fir/Wasm/Emit/ResidentRuntime.lean; integration/illuminate-hit-scene/**; integration/talos/artifact/resident-closure-projections-client.mjs; docs/build-examples.md; four fixed W7 bug cards; coordination/lanes/wasm-gen.md; coordination/BOARD.md
contracts: consumes the existing semantic/concrete closure-application and persistent-cache contracts; executable helper implementation changed without changing RuntimeOp signatures, concrete object layout, public semantic ABI, or the W6-owned proof surface. Production matcher success now consumes the closure application and projection transfers captures; standalone layout artifacts deliberately omit that stateful protocol
checks: PASS Lean Beam update/sync/save for ResidentCache and ResidentRuntime with zero diagnostics; PASS focused root and HitScene dependency cones; PASS git diff --check; PASS make check (642 unique cases, 1844/1844 comparisons equal, 123 active bug cards); PASS make talos-setup at a01d01c and make talos-check (3131 jobs); PASS complete deterministic resident-artifact gate (44/44 artifacts, 15/15 sources, 601-case V8 triangle); PASS clean HitScene frontier repeat, complete-runtime repeat, SHA256SUMS, 301 oracle queries, 10000 flat-frontier queries, two instances, disposal/error paths
bug-cards: fixed FIR-BUG-wasm-none-resident-float-closure-capture; fixed FIR-BUG-wasm-none-resident-closure-application-transfer; fixed FIR-BUG-wasm-none-hitscene-lazy-cache-rewind; fixed FIR-BUG-wasm-none-rewindable-lazy-initializer-persistence
blockers: none for generation or publication; W6 still owns the separate implementation-to-concrete-runtime refinement theorem for the resident closure-application helper and may audit the fresh-persistent lazy initializer transform against its existing cache proof cone
artifacts: integration/illuminate-hit-scene/_build/illuminate-hit-scene-current -> illuminate-hit-scene-960979c729bc1199; 45595 bytes; SHA-256 960979c729bc119988abba24046c4bccd294f3346300d6d20ce53175b5f062d6; zero imports; six function exports plus module-owned memory; BUILD.json records clean FIR package source da69d378 and clean Illuminate af088e313eaa
measurements: 159 captured declarations, 34 reviewed source externals, 439 frontier functions, 15 unresolved Float/C-libm imports before the final resident merge, persistent checkpoint 69872, encoded scene allocation 4336 bytes, and flat post-query frontier across 10000 repeated calls
handoff: integrate 48605780, da69d378, a8db316e, and 5a4fc4e0 in order, then resolve this mailbox commit from wasm/generation. The immutable package source identity remains da69d378 because the later commits change only card schema and standalone artifact separation
next: after this package lands, rebase integration/object-provenance on the new main before resuming the interface adaptation fixtures and carrier/provenance descriptors
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

## Illuminate prepared HitScene package (2026-08-10)

The request is complete at functional head `5a4fc4e0`. The immutable package
pointer is `integration/illuminate-hit-scene/_build/illuminate-hit-scene-current`;
its complete Wasm is 45,595 bytes with SHA-256
`960979c729bc119988abba24046c4bccd294f3346300d6d20ce53175b5f062d6`,
zero imports, six intended function exports plus module-owned memory, and a
clean exact-source manifest. The adapter retains one scene per instance below
a checkpoint, transports coordinates bit-exactly, copies results, and rewinds
query scratch. Its acceptance smoke covers 301 oracle queries and 10,000
flat-frontier repeats. W6 refinement of the new executable ownership helper is
an independent proof follow-up and does not block this generation artifact.
