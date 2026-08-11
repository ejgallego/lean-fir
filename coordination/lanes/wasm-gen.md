# wasm-gen lane

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: aa3940b6 on main
functional-head: 1ab73d0e4212a1b6c2d202d272ac2ca7ede4c6df
contract-base: aa3940b6 on main
clean-at-update: true
slice: Generic closed-application build closure. Removed the exact Illuminate elapsedFrame declaration-name rewrites and source-body Float.ofNat substitution; introduced declaration/signature-driven retained external selection, checked residual-import policies, generic pure-lazy arena preparation, and one shared standard-math runtime/linker consumed by the full player, selection player, and HitScene packages. Kept the real final-LCNF source closures and application algorithms unchanged
files: Fir/Wasm/Emit/ExternalRuntime.lean; Fir/Wasm/Emit/Resident{Array,Float,Linker,NatMod,NatShift}.lean; integration/wasm-runtime/; integration/illuminate-player/; integration/illuminate-hit-scene/; bugs/FIR-BUG-wasm-none-external-runtime-arena-overlap.md
contracts: no shared semantic ABI, concrete layout, or resident-helper signature changed. New package-local runtime capability fir.standard-math/v1 reserves the first 65536 memory bytes and supports canonical immediate/one-limb u64 Nat plus Float.ofScientific exponents through 20; adapters validate this metadata and advance the FIR frontier before encoding
checks: git diff --check passed; make check passed (642 unique cases, 1844/1844 comparisons, zero findings, 124 active bug cards); make talos-setup passed at Talos a01d01c; make talos-check passed (3131 jobs); bash integration/talos/artifact/check.sh passed before commit and again from clean functional head; bash integration/illuminate-player/check.sh passed from clean functional head (107 legacy/FIR-v3/FIR-selection-v4 traces, package checksums, 10000-tick flat-frontier smokes); clean deterministic HitScene publication passed (301 oracle queries and 10000 flat-frontier queries)
bug-cards: FIR-BUG-wasm-none-external-runtime-arena-overlap (fixed; the linked C runtime reserved low memory overlapping FIR's old frontier 1024, so adapters now validate the shared runtime reservation and advance to 65536 before encoding)
blockers: none
artifacts: prettyM-current -> prettyM-current-releases/1ab73d0e4212-87f4b2452ccc706e (125540-byte Wasm, SHA-256 c9f62c69bd20fb9ccff6e444fd54f9e5f4d20281e566c93ab004fc539fb13919, zero imports); illuminate-player-current -> 1ab73d0e4212-6f16cdc3d432-e52eb0fa3f7fd5d558a6 (29146 bytes, SHA-256 8b9d1c9d5adfea0e734cdc0aa74f6816cdb064e76ed73f45833682b9000687e7, zero imports); illuminate-selection-player-current -> 1ab73d0e4212-6f16cdc3d432-01590a8f6d62e0c7142b (31929 bytes, SHA-256 3223e06a91874d735aa9b47a9a9c9c6f99e6023cdf6bd5d21360f73dae85a26a, zero imports); illuminate-hit-scene-current -> illuminate-hit-scene-0fc210079c434684 (package SHA-256 0fc210079c4346847bdcf06e67a9b09f51e036cc5de75f4ce8697e49abf8e6a3; 45595-byte Wasm SHA-256 960979c729bc119988abba24046c4bccd294f3346300d6d20ce53175b5f062d6; zero imports)
measurements: player exact source closure 99 declarations/72 source functions/188 resident helpers/19097-byte base/29146-byte complete; selection 111/81/207/21046/31929; both retain exactly Float.ofScientific and Float.ofNat before the checked standard-math link; player checkpoint 66384 and peak 67088, selection checkpoint 66304 and peak 67024, HitScene checkpoint 69872, all flat after 10000 dispatches/queries
handoff: integration may fast-forward the W7-GENERIC-BUILD-CLOSURE stack through functional head 1ab73d0e after resolving this containing mailbox commit from wasm/generation
next: close the Flat provenance/publication backlog by regenerating it through the accepted generic closure, then resume the parked object-carrier/provenance interface adaptation; HTML remains after Flat and has no publishable package yet
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
