# wasm-gen lane

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: 260ce30af106df208d9f224a5985e66404b5441e on main
functional-head: 8c7dfdd79f89dba697789f40d89c5510d9a06c13
contract-base: 260ce30af106df208d9f224a5985e66404b5441e on main; generation-ready shared resident frontier adds Array.pop, UInt32.decEq, String.append, String.push, String.Pos.next, and String.decodeChar without changing symbolic Wasm, concrete layout, or Lean semantics
clean-at-update: true
slice: Close the published Verso complete-HTML boundary. Fix generic partial resident-String selection; add the six generic Array/scalar/String operations exercised by the captured closure; compile the real VersoSlides.Pretty.formatHtmlForRuntime entry from exact Verso revision 2ee1c804; encode compact Std.Format plus TaggedAnnotation values; decode copied escaped HTML; publish a deterministic zero-import Node/browser package; and repair the W7 concrete validation observer so constructor slots track their post-mutation physical kind
files: Fir/Wasm/Emit/{ResidentArray,ResidentLinker,ResidentScalarBox,ResidentString}.lean; integration/talos/artifact/{check-concrete-validation-products,concrete-host,resident-array-client,resident-scalar-box-client,resident-string-client,test-concrete-initial-runtime}.mjs; bugs/FIR-BUG-wasm-none-{concrete-validation-tagged-ctor-field,resident-string-partial-frontier}.md; integration/verso-html/{README.md,Oracle.lean,VersoFirHtml/Compile.lean,browser-check.sh,browser-smoke.html,build-adapter.mjs,check-html.mjs,check.sh,closure-contract.json,package-smoke.mjs,package.mjs,verso-source.json}
contracts: generation-ready resident signatures add Array.pop : erased x object -> object, UInt32.decEq : uint32 x uint32 -> uint8, String.append : object x object -> object, String.push : object x uint32 -> object, String.Pos.next : object x tobject x erased -> tagged, and String.decodeChar : object x tobject x erased -> uint32. ResidentString.internalizeAvailable now selects only present supported imports while historical strict internalize/externalDeclarations remain stable. Public package API is fir.prettyM.html.browser/v1; input layout lean-4.32-Std.Format.compact/v1 plus Array TaggedAnnotation; ownership fir.prettyM.module-owned-transfer/v1; output EscapedHtmlString under verso-token-html/v1
checks: Lean Beam update/sync passed with zero diagnostics for every Lean edit; focused Fir.Wasm.Emit.ResidentLinker and VersoFirHtml.Compile builds passed; native Verso oracle and Wasm agree 8/8; standalone Array, scalar, and String real-engine clients passed; git diff --check passed before the ready update; post-rebase make check passed 122 harness tests, 653/653 native-LCNF, 9/9 direct-machine, 653/653 native-LCNF-V8, 662 unique cases, 1968/1968 comparisons, 6829 machine steps, and zero findings; make talos-setup pinned a01d01c and post-rebase make talos-check passed all 3133 jobs; post-rebase bash integration/talos/artifact/check.sh passed the complete resident/runtime/package cone, the 653-case V8 triangle, 608/653 concrete validation products with 45 ByteArray-blocked cases, and deterministic 44/44 concrete artifacts; complete Verso HTML check published twice to the same identity and passed SHA256SUMS, Node smoke, 8 native/Wasm differential cases, bounded memory growth, 32 repeated calls, malformed annotation rejection, the Verso package validator, and headless Chrome
bug-cards: FIR-BUG-wasm-none-resident-string-partial-frontier fixed; FIR-BUG-wasm-none-concrete-validation-tagged-ctor-field fixed; none unresolved in this slice
blockers: none for correctness/publication. Source-owner performance follow-up: the current immutable character-at-a-time HTML escape loop has quadratic allocation volume in the monotonic arena, so the package uses a bounded growth smoke and does not claim the deferred >=1 MiB throughput gate
artifacts: immutable package integration/verso-html/_build/verso-html-packages/8c7dfdd79f89-2ee1c804106b-f991e46bebfce2bb4e45; canonical pointer integration/verso-html/_build/verso-html-current; complete Wasm 187855 bytes SHA-256 ce63b4fd71abddda8aa5795a57ab7849666f8029b501a015ee3e3c714a3eec1c; base Wasm 66762 bytes SHA-256 7c19975691662a59c4269ad60b286ff6dd7d9f005b54b70646e71fd3c33ef0e5; zero function/memory imports; exact exports VersoSlides.Pretty.formatHtmlForRuntime, fir_heap_frontier, fir_heap_set_frontier, fir_heap_rewind, fir_heap_alloc, and module-owned memory
measurements: single-unit compileEntryFinalCapturedInternalized captures 128 declarations, reviews 31 externals, retains 93 source functions, links 631 resident helpers into 724 complete functions, retains zero lazy initializers and runtime operations, and defines 3 resident globals. Adapter uses two bulk resident allocations per render and copies the output String before return
handoff: integrate the standalone runtime-helper commit 57ae699e followed by the HTML publication and concrete-observer repair stack through functional head 8c7dfdd7. The resident signatures are generation-ready; their later W6 refinement is intentionally distinct. Publish the immutable path to the Verso owner. No PR is requested
next: Verso consumes the package and replaces its source escape loop with a builder/chunk implementation before the deferred >=1 MiB throughput gate. W7 then takes ROOT-FIR-20260811-001..003 as secondary generic producer/verifier/toolkit work
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
