# wasm-gen lane

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: 36b605d6a96d93eab83c9d0022665d0def5e5b2b on main
functional-head: bc2dcc6677594d4a751389de46c874a08314b073
contract-base: 36b605d6a96d93eab83c9d0022665d0def5e5b2b on main; no shared semantic, concrete-runtime, symbolic-Wasm, or resident-helper contract changed
clean-at-update: true
slice: Align synthetic final-LCNF capture with Lean's generic specialization path. Decode the upstream `._at_.<caller>.spec_N` provenance, rebuild each caller with its generic callee, invalidate only generated compiler state owned by the recompilation roots, and terminate the stock LCNF pass manager before its unused IR phase. The real Lean 4.33 Level1 closure now captures every private specialization locally instead of leaking two stale imported names
files: Fir/Wasm/Emit/{CompilerPrivate.lean,Source.lean,SourceExamples.lean}; integration/lean-zip/ProbeLevel1.lean; bugs/FIR-BUG-wasm-none-final-capture-specialization-caller-provenance.md
contracts: none. FIR still consumes untouched final impure LCNF produced by Lean's configured generic passes. The change is confined to W7 source-capture orchestration and compiler-cache isolation; W6 proof surfaces are unchanged
checks: Lean Beam refresh/save passed CompilerPrivate, Source, and SourceExamples with zero diagnostics. `lake build Fir.Wasm.Emit.SourceExamples` passed. The real Level1 probe passed with 425 declarations, 111 reviewed externals, zero external specialization names, zero unsupported declarations, zero runtime operations, and exactly three remaining ordinary imports (`UInt8.ofNat._boxed`, `UInt32.ofNat._boxed`, `UInt8.toNat._boxed`); warm phases were capture 45,101ms, lower 3,054ms, link 3,725ms. `git diff --check` passed. `make check` passed 122 harness tests, 661/661 native-LCNF, 9/9 direct-machine, the complete 661-case native/LCNF/V8 triangle, 670 unique cases, 1,992/1,992 comparisons, zero findings, 151 valid bug cards, and the trusted-assumption gate. `make talos-setup` and `make talos-check` passed all 3,149 jobs. `bash integration/talos/artifact/check.sh` passed resident helpers, deterministic double generation, both prettyM packages, checksums, stack safety, the repeated 661-case triangle, 44/44 concrete artifacts, and 15/15 source probes
bug-cards: FIR-BUG-wasm-none-final-capture-specialization-caller-provenance fixed. The permanent Level1 regression rejects any generated specialization left external
blockers: none for this integration. Zero-import Level1 publication is now blocked only by three generic compiler-generated boxed fixed-width wrappers: UInt8.ofNat._boxed, UInt32.ofNat._boxed, and UInt8.toNat._boxed
artifacts: deterministic gate prepared integration/talos/artifact/_build/prettyM-current-releases/bc2dcc667759-883eb5cc95e2dc05; Level1 remains an inventory probe until the final three imports close
measurements: on the accepted fused/indexed linker base, warm Level1 phases are capture 45.101s, lowering 3.054s, and linking 3.725s. The same closure linked in 92.155s before the current performance stack. A controlled rejected caller-only capture took 179.717s, captured only 384 declarations, and retained one runtime operation; caller-plus-callee provenance captured the complete 425-declaration closure
handoff: fast-forward the single functional commit bc2dcc66 from base 36b605d6; resolve the containing ready status commit from wasm/generation. No PR is requested
next: derive the three `_boxed` fixed-width wrappers through the generic resident linker from their already resident unboxed operations; add a zero-import Level1 ratchet and publish the package only after engine checks pass
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
