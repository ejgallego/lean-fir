# wasm-gen lane

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: 81c03c983f19722c2189336be70d3e58e6f75485 on main
functional-head: f289322a240613ba66133747381ccdec1d016589
contract-base: 81c03c983f19722c2189336be70d3e58e6f75485 on main
clean-at-update: true
slice: Generic closed-application/Flat prerequisite. The shared policy now declaration-selects complete String and fallback families and optional direct self-tail-call elimination; Flat uses the same capture, arena preparation, policy, and postconditions as Illuminate instead of a 14-step package policy. The tail transform now preserves fresh-call local semantics through control-flow-aware definite-assignment analysis and zeroes only locals observable before assignment. Flat package publication forces Lake reconfiguration so source provenance cannot name one checkout while compiling stale oleans from another
files: Fir/Wasm/Emit/ResidentFallback.lean; Fir/Wasm/Emit/ResidentLinker.lean; Fir/Wasm/Emit/ResidentString.lean; Fir/Wasm/Emit/TailCall.lean; integration/verso-flat/{VersoFirFlat/Compile.lean,closure-contract.json,package.mjs}; integration/illuminate-player/{package.mjs,selection-package.mjs}; integration/illuminate-hit-scene/closure-contract.json; three bug cards
contracts: no shared Lean semantics, concrete layout, semantic ABI, external-runtime ABI, or resident-helper signature changed. The W7-only closedApplicationPolicy now accepts available String/fallback families and applies validated optional self-tail-call elimination. Player, selection, HitScene, and Flat public import/export/ownership contracts remain unchanged
checks: Lean Beam update/sync/save for TailCall passed with zero diagnostics and structural guards for fresh local reset; focused lake build Fir.Wasm.Emit.TailCall Fir.Wasm.Emit.ResidentLinker passed; git diff --check passed; final post-rebase make check passed (642 unique cases, 1844/1844 comparisons, zero findings, 127 active bug cards); make talos-setup retained Talos a01d01c and final make talos-check passed (3133 jobs); bash integration/talos/artifact/check.sh passed after the first proof-only rebase; clean deterministic integration/illuminate-player/check.sh passed (107 legacy/FIR-v3/FIR-v4 traces and both 10000-tick flat-frontier smokes); clean repeat-required HitScene publication passed (301 oracle queries and 10000 flat-frontier queries); clean provisional integration/verso-flat/check.sh passed deterministic double publication, checksums, 9 native/Wasm cases, 1 MiB UTF-8, cold stack shapes, 32 repeated calls, malformed/timing checks, and the Verso validator. The final rebase added only W6-owned proof/roadmap files; make check and all 3133 Talos jobs were rerun on the exact functional head
bug-cards: FIR-BUG-wasm-none-self-tail-local-reinitialization (fixed); FIR-BUG-wasm-none-flat-source-view-stale-reconfiguration (fixed); FIR-BUG-impure-none-generated-external-source-ancestor (candidate upstream/toolchain closure limitation)
blockers: accepted Flat publication waits for the Verso owner to publish the semantic-neutral Pretty.lean source refactor currently proven only at clean local commit e9ae2ed6; the FIR prerequisite slice itself is green and ready
artifacts: player 29018-byte Wasm SHA-256 3c7667bf3d5b5907650bf52dd87bd8e53e99efdfedad2378b04c5e07219d60cc; selection 31787-byte Wasm SHA-256 155443b3f3251f28e39414ba2da4be2ade8d8c29be10be3cad3dc1a4f8bcc62d; HitScene 45621-byte Wasm SHA-256 2bfe26020afe22c0f965bf85dcfd1c9f7aea4deb55ce44815fb937eb696698aa; provisional Flat 154635-byte Wasm SHA-256 60a70d63a38d230f37c04e1a88bad264a69cd9b23215b1ba859bd6dd125f0b0e; all zero imports
measurements: generic Flat closure is 90 captured declarations, 64 source functions, 504 resident helpers, 568 complete functions, zero lazy initializers, and three resident globals, down from 113/82/574/656 with 23 lazy initializers. Safe precise local reset preserves the exact provisional Flat bytes; player shrinks 128 bytes and selection shrinks 142 bytes after generic self-tail lowering; HitScene grows 26 optimized bytes while retaining its exact semantics
handoff: integration may fast-forward the two-commit W7-GENERIC-FLAT-PREREQUISITE stack through functional head f289322a after resolving the containing mailbox commit from wasm/generation
next: after this prerequisite lands, repin Flat to the remotely published Verso source and perform accepted immutable publication; then resume the parked object-carrier/provenance interface adaptation. HTML remains after accepted Flat publication
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
