# wasm-gen lane

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: 71890121f98eec5eeae171fbb1c4501b115537f7 on main
functional-head: 95ccd21c99867b33812e879e371ac7a10c85e74c
contract-base: 8bcd73260d7cf18d2915e2aaee0a333ed6072c8c on main
clean-at-update: true
slice: Accepted Verso Flat publication plus the first principled complete-HTML closure probe. Flat is pinned to published Verso commit 3dbc9ef4 and its immutable package passed deterministic, Node, Chrome, and Verso consumer gates. HTML captures the real formatHtmlForRuntime through module-wise postponed final LCNF; it emits a stable base module and fails closed at the exact precompiled-core boundary instead of adding host fallbacks or copying semantics into FIR
files: integration/verso-flat/verso-source.json; integration/verso-html/{lakefile.lean,lake-manifest.json,lean-toolchain,VersoFirHtml.lean,VersoFirHtml/Compile.lean,Emit.lean,README.md,verso-source.json}; bugs/FIR-BUG-impure-none-generated-external-source-ancestor.md
contracts: no shared Lean semantics, symbolic Wasm surface, concrete layout/runtime, resident-helper signature, or existing package API changed. Flat keeps fir-prettyM-package-metadata-v2 and fir.prettyM.flat.browser/v1. The prospective HTML compiler descriptor establishes the physical entry ABI as [tobject,object,tobject,tobject,tobject] -> object; Array TaggedAnnotation is physically object
checks: Lean Beam update/sync/save for VersoFirHtml.Compile and VersoFirHtml passed with zero diagnostics; Emit reached the recorded expected fail-closed linker diagnostic; focused module-wise Verso source build passed; exact HTML base identity repeated after rebase (32407 bytes, SHA-256 6befd7de55f0c6044104a43b9b8ffa9b4ca25009f3871b66155bc1a7dcb41917, 52 external-name inventory SHA-256 1d1546f915150586a44c631b8e32baa966fc5abf8a1fb905dc20bc7f8a06d1bb); git diff --check passed; final post-rebase make check passed (642 unique cases, 1844/1844 comparisons, zero findings, 127 active bug cards); make talos-setup retained Talos a01d01c and final post-rebase make talos-check passed (3133 jobs); bash integration/talos/artifact/check.sh passed; VERSO_ROOT=/tmp/verso-flat-published FIR_BROWSER=google-chrome bash integration/verso-flat/check.sh passed deterministic double publication, checksums, 9 native/Wasm cases, 1 MiB UTF-8, cold stack shapes, 32 repeats, timing/malformed checks, Verso validator, and Chrome smoke
bug-cards: FIR-BUG-impure-none-generated-external-source-ancestor (candidate; exact HTML reproduction updated)
blockers: HTML publication requires the Verso owner to make the HTML source closure self-contained in its postponed module: explicit specialized HtmlM/dictionary and chunk join plus a source-local specialized escaping loop instead of precompiled generic StateT/String.join/String.replace declarations
artifacts: accepted Flat package integration/verso-flat/_build/verso-flat-packages/a4dce92bc6e1-3dbc9ef4fa5a-7d16ade417a24f50058e; 154635-byte Wasm SHA-256 60a70d63a38d230f37c04e1a88bad264a69cd9b23215b1ba859bd6dd125f0b0e; zero imports; exact package FIR source commit remotely reachable at origin/publish-verso-flat-a4dce92b. HTML has no package claim; diagnostic base only is 32407 bytes with 498 FIR operations and 52 Lean externals
measurements: accepted Flat closure remains 90 captured declarations, 64 source functions, 504 resident helpers, 568 complete functions, zero lazy initializers, and three resident globals. Module-wise Verso source replay takes 2.6 seconds on the warm FIR worktree; the abandoned single-unit HTML capture did not finish after 15 minutes
handoff: integrate the three rebased W7 commits through functional head 95ccd21c; Flat is complete, accepted, and remotely reproducible; preserve the HTML diagnostic as a fail-closed source-contract handoff
next: wait for the Verso HTML source refactor, then publish the zero-import HTML package/adapter and run its Node/Chrome/Verso-validator gates; otherwise resume the parked object-carrier/provenance interface adaptation
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
