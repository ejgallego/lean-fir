# FIR lane coordination board

This is the portable coordination snapshot for parallel FIR work. The
integration owner is the only writer so the board cannot become a cross-branch
merge conflict. Lane owners send updates; the integration owner applies them
atomically. A harness-backed board may mirror this schema and become the live
view, while this file remains the repository handoff snapshot.

The board contains no executable policy. Separate Git worktrees provide the
actual isolation; this file only makes ownership, dependencies, and handoffs
visible. Add automation only after a repeated coordination failure gives it a
specific behavior to prevent.

Statuses are `active`, `ready`, `blocked`, `released`, or `parked`.

## Active integration lease

- No cross-lane integration lease is currently active.

## Latest completed integration lease

- Milestone: `W6-RANKED-FINITE-TRACE-SIMULATION-BOUNDARY`.
- Integration owner: `wasm-proof`; the user retained the W6 owner as
  integration owner for the certificate-free compiler proof.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`.
- Published stack: active-slice record `f463519c`, W6 functional head
  `115fd2a1`, and ready mailbox `a7a33083`, based directly on `main` at
  `ef8a16eb`.
- Lease boundary: satisfied. The proof library now provides heterogeneous
  observation-aware weak simulation, exact finite-path composition, and a
  natural-number rank that rules out infinite target silence while matching
  a source step. Its W6 specialization transports every finite deterministic
  LCNF `ExecSteps` prefix to a finite resumable concrete-machine prefix with
  exactly related world and semantic trace, without a source-termination
  premise. The compiler theorem's target witness remains compiler-produced;
  no translation or execution certificate is accepted from the caller. The
  boundary deliberately does not claim that Talos `OutOfFuel` is resumable:
  adequacy between a structured Wasm configuration and `Wasm.run` is the next
  proof slice. No shared semantics, symbolic Wasm ABI, resident helper,
  concrete layout, or executable artifact changed.
- Validation: Lean Beam zero-error saves for both new proof modules; final
  3,127-job Talos dependency cone; `git diff --check`; complete `make check`
  on the immediately preceding documentation-only base with 642 unique cases,
  1,844/1,844 equal comparisons, zero findings, and all 113 bug cards
  validated; Talos setup at `a01d01c`; and all 3,127 final
  `make talos-check` jobs.

## Previous completed integration lease

- Milestone: `W6-DERIVED-CLOSURE-RESOLVER-PACKAGING`.
- Integration owner: `wasm-proof`; the user retained the W6 owner as
  integration owner for the certificate-free compiler proof.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`.
- Published stack: active-slice record `d00a26ce`, W6 functional head
  `bea8c53a`, and ready mailbox `9c9ae995`, based directly on `main` at
  `480c15e7`.
- Lease boundary: satisfied. Successful adaptation of each actual generated
  closure-dispatch chain is inverted into the compiler's exact flat-map
  candidate enumeration, including numeric adaptation and the precise
  `closureMatches` import/host contract. Consequently the recursive
  declaration proof and public whole-export theorem derive their resolver
  evidence internally and accept no caller-supplied resolver package,
  translation certificate, target execution, or termination oracle. No
  shared semantics, symbolic Wasm ABI, resident helper, concrete layout, or
  executable artifact changed.
- Validation: Lean Beam zero-error saves for both changed proof modules;
  focused 3,104-job dependency cone; `git diff --check`; complete `make check`
  with 642 unique cases, 1,844/1,844 equal comparisons, zero findings, and all
  113 bug cards validated; Talos setup at `a01d01c`; and all 3,125
  `make talos-check` jobs.

## Previous completed integration lease

- Milestone: `W6-STATIC-CLOSURE-CANDIDATE-RESOLUTION`.
- Integration owner: `wasm-proof`; the user retained the W6 owner as
  integration owner for the certificate-free compiler proof.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`.
- Published stack: bug-card report `1d55e858`, W6 functional head
  `9f6c5a05`, resolution `f4bf542e`, and ready mailbox `fcc1525d`, based
  directly on `main` at `9dab5f3c`.
- Lease boundary: satisfied. Closure-candidate resolution is now static
  compiler/adapter/host metadata only. The proof derives matcher miss and hit
  execution at the actual mapped live closure address from the concrete
  runtime relation, immutable tables, shared capacity, and the source
  ownership transition. This removes the uninhabitable premise that every
  candidate matcher must return successfully for every arbitrary store and
  address, and repairs both the one-layer theorem and recursive whole-export
  theorem. No shared semantics, symbolic Wasm ABI, resident helper, concrete
  layout, executable artifact, or W7 contract changed.
- Validation: Lean Beam zero-error sync/save; focused 3,104-job post-rebase
  dependency cone; `git diff --check`; complete `make check` with 642 unique
  cases, 1,844/1,844 equal comparisons, and all 113 bug cards validated; and
  all 3,125 post-rebase `make talos-check` jobs.

## Previous completed integration lease

- Milestone: `W6-RECURSIVE-WHOLE-EXPORT-CORRECTNESS`.
- Integration owner: `wasm-proof`; the user retained the W6 owner as
  integration owner for the certificate-free compiler proof.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`.
- Published stack: W6 functional head `d8d5e607` and ready mailbox
  `de79fe52`, based directly on `main` at `de1c7ca7`.
- Lease boundary: satisfied. The structural production proof now consumes an
  explicit local operation/resolver interface, so it starts directly at a
  supported export and recursively selects the corresponding interface from
  each actual generated row. The public theorem matches every admitted finite
  source execution, with arbitrarily nested named and exactly saturated
  closure calls, by a terminating generated Wasm export with the same runtime
  and semantic value. Its compiler-side resolver inputs are executable
  metadata, not target executions or behavior certificates. No shared
  semantics, symbolic Wasm ABI, resident helper, concrete layout, executable
  artifact, or W7 contract changed.
- Validation: Lean Beam zero-error sync/save; focused 3,104-job dependency
  cone; `git diff --check`; complete `make check` with 642 unique cases and
  1,844/1,844 equal comparisons; and all 3,125 `make talos-check` jobs.

## Previous completed integration lease

- Milestone: `W6-RECURSIVE-GENERATED-CLOSURE-INDUCTION`.
- Integration owner: `wasm-proof`; the user retained the W6 owner as
  integration owner for the certificate-free compiler proof.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`.
- Published stack: W6 functional head `feea71dc` and ready mailbox
  `40456ea0`, rebased directly on `main` at `db1295ab`.
- Lease boundary: satisfied. W6 now proves the generated target execution by
  structural induction over every finite recursive production derivation,
  including nested named calls and exactly saturated closure calls. Recursive
  exact-budget and arbitrary-slack runs share the same proof; closure
  resolution consumes executable generated-row metadata, not a behavioral
  certificate. The corrected unstable proof boundary requires the concrete
  closure ABI at declaration entry, where capture projection consumes it, and
  proves it again at exit. No shared semantics, symbolic Wasm ABI, resident
  helper, concrete layout, executable artifact, or W7 contract changed.
- Validation: Lean Beam zero-error sync/save; focused 3,104-job post-rebase
  dependency cone; `git diff --check`; complete `make check` with 642 unique
  cases and 1,844/1,844 equal comparisons; Talos setup at `a01d01c`; and all
  3,125 post-rebase `make talos-check` jobs.

## Previous completed integration lease

- Milestone: `W7-UPSTREAM-GENERIC-OBJECT-FAMILY-ABI`.
- Integration owner: `wasm-gen`; the user assigned the W7 owner the dynamic
  integration lease for this compiler/generation consolidation.
- Integration branch/worktree: `wasm/generation` in
  `.worktrees/wasm-generation`.
- Published stack: isolated shared contract `bd7a5e55`, W7 consumer
  `a13fa2ad`, Illuminate source-inventory ratchet `e5a8612b`, and ready
  mailbox `dfe6da0b`, based directly on `main` at `cdb8c4f3`.
- Lease boundary: satisfied. Compiler call, result, and symbolic-stack
  admission now follow Lean's generic physical object-family convention:
  `object`, `tagged`, and `tobject` are mutually call-compatible, while scalar
  and erased lanes remain exact. The directional semantic/proof refinement
  relation is unchanged. W7 no longer repairs final-LCNF kinds by application
  name, the `prettyM` facade has a concrete state without `unsafeCast`, and
  generic resident Array and weak-Inhabited results preserve their captured
  `tobject` kind. W6 consumes these stable signatures after rebasing its next
  checkpoint; no concrete layout or runtime representation changed.
- Artifact identity: PrettyFormat styled
  `c928d30adb3d39f7409e7091b4e1f13289aac35c02b34d761062c8a8f3e74b60`
  (117,389 bytes) and plain
  `84939d58da4e75f48f1791947edc5ce462842b0bc24b984ffb4d1842751d0be2`
  (113,311 bytes). Illuminate v3 is
  `a4de0ec22d50c5070dbfa90969dc95c41be6f747955f60c8f9620baeafefbfa5`
  (50,211 bytes), and v4 is
  `1c3064d4ee5b9ea0f96055b03e50e8477d29ce6f2313c23c9dcfc83d314eecd8`
  (55,527 bytes); both retain zero imports and their reviewed six-function
  live-player export surface.
- Validation: Lean Beam zero-error checkpoint; `git diff --check`; complete
  `make check` with 642 unique cases and 1,844/1,844 equal comparisons; all
  3,125 `make talos-check` jobs; the complete deterministic PrettyFormat
  artifact gate; and the Illuminate v3/v4 gate against clean Illuminate
  `b233ce7` and corrected `Player.lean` source hash `e1f98f9d`, with two
  deterministic publications, all 106 checked-in traces including duplicate
  frame-zero initialization, and flat frontiers in both 10,000-dispatch tests.

## Previous completed integration lease

- Milestone: `W6-RECURSIVE-PRODUCTION-CLOSURE-PROOF-BOUNDARY`.
- Integration owner: `wasm-proof`; the user retained the W6 owner as
  integration owner for the certificate-free compiler-proof boundary.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`.
- Published stack: W6 functional head `cd8cd485` and ready mailbox
  `f6a09d46`, based directly on `main` at `a8f8ec0d`.
- Lease boundary: satisfied. W6 now states the exact target induction for
  every actual generated declaration row and every finite recursive
  production source derivation, plus its derived closure-ABI strengthening.
  Recursive closure dispatch consumes module-wide executable candidate
  enumeration for generated rows; that metadata contains no source
  evaluation, target execution, store relation, or correctness certificate.
  No shared source semantics, symbolic Wasm ABI, resident-helper signature,
  concrete layout, or executable artifact changed.
- Validation: Lean Beam zero-error sync/save; focused 3,103-job dependency
  cone; `git diff --check`; complete `make check` with 642 unique cases and
  1,844/1,844 equal comparisons; Talos setup at `a01d01c`; and all 3,125
  `make talos-check` jobs.

## Previous completed integration lease

- Milestone: `W6-DERIVED-CLOSURE-ABI-INDUCTION`.
- Integration owner: `wasm-proof`; the user retained the W6 owner as
  integration owner for the certificate-free compiler-proof boundary.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`.
- Published stack: W6 functional head `9feaaa00` and ready mailbox
  `e802efaf`, rebased directly on `main` at `8ec10ffe`.
- Lease boundary: satisfied. Pure external results, effects, direct calls, and
  lazy-cache steps now carry cumulative closure-allocation persistence. The
  ordinary hereditary generated-declaration theorem therefore implies its
  closure-ABI strengthening. The saturated-closure runtime theorem consumes
  only that ordinary induction, and its production one-lazy specialization is
  derived from lowering, adaptation, operation laws, and executable resolver
  metadata rather than a separate ABI theorem or target certificate. No
  shared source semantics, symbolic Wasm ABI, resident-helper signature, or
  concrete layout changed.
- Validation: Lean Beam zero-error checkpoints and saves for every changed
  proof/contract module; focused 3,105-job downstream dependency cone;
  `git diff --check`; complete post-rebase `make check` with 642 unique cases
  and 1,844/1,844 equal comparisons; Talos setup at `a01d01c`; and all 3,125
  post-rebase `make talos-check` jobs.

## Previous completed integration lease

- Milestone: `W7-REUSABLE-RESIDENT-LINKER`.
- Integration owner: `wasm-gen`; the user assigned the W7 owner the dynamic
  integration lease for this generation-only consolidation.
- Integration branch/worktree: `wasm/generation` in
  `.worktrees/wasm-generation`.
- Published stack: reusable resident linker `e46fbe3b` and ready mailbox
  `2ae6a1e9`, based directly on `main` at `4af25685`.
- Lease boundary: satisfied. PrettyFormat and Illuminate v3/v4 now use one
  ordered, policy-driven symbolic linker with explicit strict-versus-available
  helper admission, module-owned-memory and import-closure postconditions,
  exact public-export checks, final validation, and one final Wasm encoding.
  Application-specific source capture and ownership preparation remain outside
  the generic linker. No shared semantic, helper-signature, concrete-runtime,
  or ABI contract changed.
- Artifact identity: PrettyFormat styled `bcf8da4eaa0edc6f` (104,909 bytes),
  PrettyFormat plain `3625bdcde88379f8` (100,831 bytes), Illuminate v3
  `b36cfaf21175a40b` (50,203 bytes), and Illuminate v4
  `0371d430f2b04dab` (55,518 bytes), all byte-identical to their pre-refactor
  artifacts. Both Illuminate artifacts retain zero imports and their reviewed
  six-function live-player export surface.
- Validation: Lean Beam zero-diagnostic checkpoints; `git diff --check`;
  focused `lake build Fir.Wasm.Emit.ResidentPrettyFormat`; complete
  `make check` with 642 unique cases and 1,844/1,844 equal comparisons; Talos
  setup at `a01d01c`; all 3,125 `make talos-check` jobs; the complete
  PrettyFormat artifact gate; and the Illuminate v3/v4 gate with two
  deterministic publications, all 106 four-way traces, and flat frontiers in
  both 10,000-tick tests.

## Previous completed integration lease

- Milestone: `W6-CLOSURE-ALLOCATION-PERSISTENCE`.
- Integration owner: `wasm-proof`; the user retained the W6 owner as
  integration owner for the certificate-free compiler-proof boundary.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`.
- Published stack: proof transport foundation `7943fdfa` and ready mailbox
  `5f6ba8e5`, based directly on `main` at `18af585a`.
- Lease boundary: satisfied. Every currently proved non-closure concrete
  runtime transition now proves that it cannot invent a closure descriptor.
  The cache/call proof can therefore transport program-indexed closure ABI
  alignment across constructors, reuse, scalar boxing, promoted tags, and
  their compiled runtime steps instead of assuming alignment again after each
  step. Actual closure allocation remains governed by the compiler-derived
  ABI compatibility law.
- Validation: Lean Beam zero-error checkpoints and saves for all changed proof
  consumers; focused 3,103- and 3,098-job dependency cones;
  `git diff --check`; complete `make check` with 642 unique cases and
  1,844/1,844 equal comparisons; Talos setup at `a01d01c`; and all 3,125
  `make talos-check` jobs.

## Previous completed integration lease

- Milestone: `W6-SATURATED-CLOSURE-HEREDITARY-RUNTIME-LAW`.
- Integration owner: `wasm-proof`; the user retained the W6 owner as
  integration owner for the certificate-free compiler-proof boundary.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`.
- Published stack: closure ABI alignment `8194acef`, generated argument
  assembly `3340ae73`, ownership-aware call composition `527e13ea`, runtime
  law `bca03085`, and the ready lane mailbox based directly on `5307f77d`.
- Lease boundary: satisfied. The production theorem now composes semantic
  closure consumption, executable matcher selection, exact compiler body
  inversion, post-matcher capture projection, generated callee entry, and
  hereditary declaration correctness without a per-call target certificate.
- Validation: Lean Beam zero-error checkpoints and save; focused root and
  Talos dependency cones; `git diff --check`; complete `make check` with 642
  unique cases and 1,844/1,844 equal comparisons; all 3,125
  `make talos-check` jobs.

## Previous completed integration lease

- Milestone: `W6-CLOSURE-MATCHER-OWNERSHIP-AND-PROJECTION`.
- Integration owner: `wasm-proof`; the user retained the W6 owner as
  integration owner for the certificate-free compiler-proof boundary.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`.
- Published stack: ownership-threaded matcher/frame proof `9ef99067`, refined
  projection contract and regression `625d4883`, and ready mailbox `22d15cf3`,
  based directly on `main` at `92e94f2d`.
- Lease boundary: satisfied. A selected nonzero generated matcher now exposes
  its real post-consumption store and re-establishes the full cache, capacity,
  ownership, closure-table, and failure frame there. Closure projection reads
  at the immutable actual descriptor kind and widens exactly along
  `AbiKind.refines` to the generated callee parameter kind, preserving the
  physical Wasm lane. The resident W7 helper already performs this raw slot
  load, so its implementation is unchanged.
- Validation: Lean Beam zero-error checkpoints for all changed root and Talos
  proof modules; focused root and Talos dependency cones; `git diff --check`;
  complete `make check` with 633 native/LCNF cases, 1,266/1,266 results, and
  zero findings; the 9/9 direct machine suite; and all 3,125
  `make talos-check` jobs.

## Previous completed integration lease

- Milestone: `W6-CERTIFICATE-FREE-LAZY-EXPORT-CORRECTNESS`.
- Integration owner: `wasm-proof`; the user retained the W6 owner as
  integration owner for the public compiler-proof boundary.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`.
- Published stack: hereditary lazy export correctness `1f483a13`, localized
  lazy publication-kind admission `b8bbe5a7`, and ready mailbox `307ab145`,
  based directly on `main` through `a8b127dc`.
- Lease boundary: satisfied. The production generated-operation bundle,
  declaration induction, recursive named-call implementation, and public
  partial-correctness theorem now admit concrete lazy-cache hits and misses.
  A miss selects the actual lowered/adapted nullary initializer and derives
  its target execution from the nested finite source derivation. Non-heap
  publication evidence is local to each admitted source miss, so the public
  theorem requires no target run, recursive callee certificate, or separate
  module-wide result-kind oracle. No shared semantic Wasm ABI, lowering,
  validator, adapter, concrete-runtime, cache, closure-table, or interpreter
  contract changed.
- Validation: Lean Beam zero-error checkpoints for the proof and contract
  modules; focused 3,104-job dependency cones; `git diff --check`; complete
  `make check` with 642 unique cases and 1,844/1,844 equal comparisons; Talos
  setup at `a01d01c`; and all 3,125 `make talos-check` jobs.

## Previous completed integration lease

- Milestone: `ILLUMINATE-SELECTION-PLAYER-V4`.
- Integration owner: `wasm-gen`; the user authorized the generation owner to
  continue with the completed W7 selection package.
- Integration branch/worktree: `integration/closure-ownership` in
  `.worktrees/integration-closure-ownership`.
- Published stack: generation-ready resident-array helpers `ddf83417`, the
  selection-only adapter/package and acceptance suite `e15f4027`, and ready
  mailbox `0a485fdd`, rebased directly on `main` at `c4a9aa09`.
- Lease boundary: satisfied. FIR compiles the exact read-only Illuminate
  `initialSelectionLive` and `transitionSelectionLive` entries. The v4 adapter
  keeps SVG, patch bindings, and parameter strings in JavaScript; retains only
  the timeline selection graph and fixed state below a persistent checkpoint;
  and clears and exactly rewinds per-dispatch scratch. The accepted full-action
  v3 artifact remains byte-identical. `Array.uget`, `Array.uset`, and
  `Array.replicate` are generation-ready with standalone external-engine
  coverage; their W6 refinement proofs remain a separate follow-up.
- Artifact: immutable package
  `integration/illuminate-player/_build/illuminate-selection-player-packages/ab177f502816-006dc1d1db18-650b4cef2360a5144098`,
  55,518 bytes, SHA-256
  `0371d430f2b04dab6ad7e545c22aa591bb177fc853f366d77aeae8a4c3ac5474`,
  with zero function imports, zero memory imports, module-owned memory, and six
  public functions. The 10,000-tick stress exactly restores checkpoint 1,792
  with peak frontier 2,512. The large morph resident graph is 648 bytes versus
  997,480 bytes in v3.
- Validation: Lean Beam zero-error checkpoints and focused dependency cones;
  `git diff --check`; complete `make check` with 642 unique cases and
  1,844/1,844 equal comparisons; Talos setup at `a01d01c`; all 3,125
  `make talos-check` jobs; the complete deterministic W7 artifact gate; two
  byte-identical v3/v4 package publications with complete checksums; 106/106
  legacy/FIR-v3/FIR-v4 trace matches after host materialization; 16/16
  dashboard-data checks; and flat-frontier, two-player, failure, disposal,
  binary64-boundary, and ownership tests.

## Previous completed integration lease

- Milestone: `W6-HEREDITARY-EXACT-RESULT-STRUCTURAL-CORE`.
- Integration owner: `wasm-proof`; the user retained the W6 owner as
  integration owner for this certificate-free compiler-proof slice.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`.
- Published stack: W6 functional head `d907ef42` and ready mailbox
  `464e086f`, based directly on `main` at `6061b90c`.
- Lease boundary: satisfied. The finite hereditary source judgment now records
  the compiler-derived returned-local ABI and its refinement to the enclosing
  declaration result. Structural target correctness follows every finite
  hereditary code spine under explicit generated-operation laws, returns the
  exact declared ABI, preserves arbitrary caller-owned budget slack, and is
  packaged as the cache-aware declaration theorem with entry-to-exit
  transports. No target execution or translation certificate is a premise;
  no shared semantic Wasm ABI, lowering, validator, adapter, concrete-runtime,
  cache, closure-table, or interpreter contract changed.
- Validation: Lean Beam zero-error checkpoint; focused 3,103-job dependency
  cone; `git diff --check`; Talos setup at `a01d01c`; complete `make check`
  with 642 unique cases and 1,844/1,844 equal comparisons; and all 3,125
  `make talos-check` jobs.

## Previous completed integration lease

- Milestone: `W7-REUSABLE-SOURCE-AND-BATCHED-ILLUMINATE-ENCODER`.
- Integration owner: `wasm-gen`; the user assigned the generation owner to
  integrate the ready W7 stack after the previous lease completed.
- Integration branch/worktree: `integration/closure-ownership` in
  `.worktrees/integration-closure-ownership`.
- Published stack: reusable multi-entry source capture `1996d2d5`, generic
  rewind-safe cache elimination `eeb6cabe`, batched persistent animation
  encoding `5c571398`, and ready mailbox `4234cbea`, based directly on `main`
  at `f0ee6857`.
- Lease boundary: satisfied. Final-LCNF source capture can retain multiple
  requested entries and their exact transitive closure. Rewind-safe lazy-cache
  elimination is fail-closed and preserves/remaps unrelated resident globals.
  Illuminate consumes both W7 APIs and measures its persistent animation graph
  before encoding it into one exact resident allocation. Adapter v3, input
  layout v3, ownership v2, concrete layouts, resident-helper signatures, and
  generated Wasm bytes are unchanged.
- Artifact: immutable package
  `integration/illuminate-player/_build/illuminate-player-packages/5c571398dc46-006dc1d1db18-8be7788263f52afe63e4`,
  50,203 bytes, SHA-256
  `b36cfaf21175a40bfb5156e527057700eed56609bd8f2b8f91e68914c254158e`,
  with zero imports and six public functions. Persistent allocator calls fall
  from 94--9,547 to exactly 11 while the 10,000-dispatch frontier plateau is
  unchanged. Across 16 dashboard examples, the order-balanced benchmark's
  aggregate encode median falls from 0.1516205 ms to 0.1094375 ms; the
  997,480-byte example falls from 6.165221 ms to 5.172888 ms.
- Validation: Lean Beam zero-diagnostic checkpoints; focused dependency cones;
  `git diff --check`; complete `make check` with 642 unique cases and
  1,844/1,844 equal comparisons; all 3,125 Talos jobs; complete W7 artifact,
  engine, determinism, and concrete-readiness gate; two byte-identical
  Illuminate package publications with complete checksums; 105/105 locally
  available trace matches; 10,000-tick flat-frontier stress; and action
  equality for all 256 old/new benchmark samples.

## Previous completed integration lease

- Milestone: `W6-DIRECT-HEREDITARY-SOURCE-EVALUATION`.
- Integration owner: `wasm-proof`; the user retained the W6 owner as
  integration owner for this certificate-free compiler-proof slice.
- Integration branch/worktree: `integration/closure-ownership` in
  `.worktrees/integration-closure-ownership`.
- Published stack: W6 functional head `cbb0f0d1` and ready mailbox
  `6fe75308`, based directly on `main` at `c882cdc8`.
- Lease boundary: satisfied. `ReuseCapacityDirectHereditaryCodeEvaluates`
  is the source-recursive finite-evaluation object for direct named calls. Its
  direct-call constructor carries finite evaluation of both the callee body
  and caller continuation; the proof reconstructs the real interpreter call
  prefix and erases the richer derivation to the existing exact
  `SourceCodeResult`. The derivation contains no target program, store,
  witness, execution, or translation certificate. No semantic Wasm ABI,
  lowering, validator, interpreter, adapter, or concrete-runtime contract
  changed.
- Validation: Lean Beam update/refresh/sync/save for the proof and contract
  modules; focused compiler-proof dependency cones; `git diff --check`;
  `make talos-setup`; complete `make check` with 642 unique cases and
  1,844/1,844 equal comparisons, zero findings, and 108 valid bug cards; and
  all 3,125 Talos jobs.

## Previous completed integration lease

- Milestone: `ILLUMINATE-LIVE-PLAYER`.
- Integration owner: `wasm-gen`; the user authorized the generation owner to
  follow the short landing sequence after the prior W6 lease completed.
- Integration branch/worktree: `integration/closure-ownership` in
  `.worktrees/integration-closure-ownership`.
- Published stack: W7 functional head `b72f2bfa` and ready mailbox `e5d9cd65`,
  rebased directly on `main` at `a07defe0`.
- Lease boundary: satisfied. The final-LCNF package compiles the real
  `Illuminate.AnimationPlayer.initialLive` and `transitionLive` entries into a
  self-contained, module-owned Wasm module. The v3 browser adapter shares one
  compiled `WebAssembly.Module`, owns one instance per opaque player, retains
  the animation and state below a persistent checkpoint, and clears and
  rewinds per-dispatch scratch without exposing raw addresses. The new
  generation-ready `fir_heap_rewind [uint32] -> []` helper leaves the existing
  monotonic `fir_heap_set_frontier` contract unchanged; its W6 refinement proof
  remains a separate non-blocking follow-up.
- Artifact: immutable package
  `integration/illuminate-player/_build/illuminate-player-packages/b72f2bfa9e7d-006dc1d1db18-8103ef218b8dc6ff4f00`,
  50,203 bytes, SHA-256
  `b36cfaf21175a40bfb5156e527057700eed56609bd8f2b8f91e68914c254158e`,
  with zero function imports, zero memory imports, and six public functions.
  The 10,000-tick stress holds the exact 1,872-byte checkpoint with a constant
  704-byte scratch high-water and 2,576-byte peak frontier.
- Validation: Lean Beam zero-diagnostic checkpoints; focused deterministic
  package publication twice with identical bytes and complete checksums;
  105/105 local legacy/FIR trace matches; `git diff --check`; complete
  `make check` with 642 unique cases and 1,844/1,844 equal comparisons; Talos
  setup at `a01d01c`; all 3,125 `make talos-check` jobs; and the complete W7
  artifact, engine, determinism, and concrete-readiness gate.

## Previous completed integration lease

- Milestone: `W6-DIRECT-CALLEE-EXACT-BUDGET-INDUCTION`.
- Integration owner: `wasm-proof`; the user retained the W6 owner as
  integration owner for this certificate-free compiler-proof slice.
- Integration branch/worktree: `integration/closure-ownership` in
  `.worktrees/integration-closure-ownership`.
- Published stack: W6 functional head `e05c9110` and ready mailbox
  `178f67a7`, based directly on `main` at `dcb7d6b3`.
- Lease boundary: satisfied. The structural call's already established
  `stepCost <= remainingBytes` fact now survives the direct-call proof
  interface. It weakens the generated callee entry to the finite source
  body's exact cost; the production argument relation proves the adapted
  callee arity; and finite callee evaluation plus the uniform operation laws
  yields the cache-aware successful-declaration package used by the caller.
  This is the first production recursive induction step. Its execution input
  is a source-semantic partial-correctness premise, not target execution or a
  translation certificate. No shared semantic, ABI, lowering, or concrete-
  runtime contract changed. Bug card
  `FIR-BUG-wasm-none-direct-callee-budget-premise` is fixed.
- Validation: Lean Beam update/sync/save for the proof module and refreshed
  contract importer, focused compiler-proof dependency cones, bug-card
  validation, `git diff --check`, `make talos-setup`, complete `make check`
  (642 unique cases and 1,844/1,844 equal comparisons with zero findings), and
  all 3,125 Talos jobs.

## Previous completed integration lease

- Milestone: `W6-GENERATED-CALLEE-LOCALS`.
- Integration owner: `wasm-proof`; the user retained the W6 owner as
  integration owner for this certificate-free compiler-proof slice.
- Integration branch/worktree: `integration/closure-ownership` in
  `.worktrees/integration-closure-ownership`.
- Published stack: W6 functional head `7916298d` and ready mailbox
  `9a2b3f0e`, based directly on `main` at `aecae9a4`.
- Lease boundary: satisfied. Production `declarationParameterKinds?`,
  `addDeclarationParams`, and emitted-function equations prove the exact
  source-order parameter binding row. The actual `bindParams` result and
  caller argument relation then construct `EnvLocalsRelated` for the generated
  callee's `toLocals` frame. No hygiene premise, target execution, translation
  certificate, or semantic/runtime contract is added.
- Validation: Lean Beam update/sync/save for the two proof modules and contract
  importer, focused compiler-proof dependency cones, `git diff --check`,
  `make talos-setup`, complete `make check`, and all 3,125 Talos jobs.

## Previous completed integration lease

- Milestone: `W6-CALLEE-ARGUMENT-REFINEMENT`.
- Integration owner: `wasm-proof`; the user retained the W6 owner as
  integration owner for this certificate-free compiler-proof slice.
- Integration branch/worktree: `integration/closure-ownership` in
  `.worktrees/integration-closure-ownership`.
- Published stack: W6 functional head `73492cd9` and ready mailbox
  `837dcf05`, based directly on `main` at `298682a7`.
- Lease boundary: satisfied. An existing physical/source argument relation
  now transports across the production validator's complete pointwise ABI
  refinement decision. Every selected generated internal declaration also
  retains the parameter-identifier uniqueness fact derived from its actual
  successful `lowerSupported` validation. These proof-only facts change no
  lowering, validator, semantic Wasm ABI, or concrete-runtime contract and
  require neither target execution nor translation certificates.
- Validation: Lean Beam update/sync/save (with the prescribed importer refresh
  after rebase), focused compiler-proof dependency cones,
  `git diff --check`, `make talos-setup`, complete `make check`, and all 3,125
  Talos jobs.

## Completed integration lease

- Milestone: `WASM-DECLARATION-PARAMETER-UNIQUENESS`.
- Integration owner: `wasm-proof`; the W6 owner retained the integration lease
  because the callee-entry proof exposed this shared support-domain bug.
- Integration branch/worktree: `integration/closure-ownership` in
  `.worktrees/integration-closure-ownership`.
- Published stack: queue/card head `03547684` followed by isolated contract
  repair `dfa8153e`, based directly on `main` at `b2ecf2a4`.
- Lease boundary: satisfied. `supportedDecl` rejects duplicate same-scope
  declaration parameter identifiers before lowering. The regression preserves
  the previous raw invalid module as an oracle while proving
  `lowerSupported` rejects it. Existing valid programs, the semantic Wasm ABI,
  and concrete-runtime contracts are unchanged; W6 and W7 rebase before
  dependent work.
- Validation: Lean Beam update/sync/save for `Fir.Wasm.WellFormed` and
  `Fir.Wasm.Examples`, focused builds and bug-card validation,
  `git diff --check`, complete `make check` with 1,844/1,844 comparisons equal
  and zero findings, and all 3,125 Talos jobs.

## Previous completed integration lease

- Milestone: `W6-CALLEE-PARAMETER-ROWS`.
- Integration owner: `wasm-proof`; the user retained the W6 owner as
  integration owner for this short certificate-free compiler-proof slice.
- Integration branch/worktree: `main` in the root worktree.
- Published stack: W6 functional head `a83651c4` and ready mailbox `a0374752`,
  based directly on `main` at `d69e0252`.
- Lease boundary: satisfied. Each production-generated internal declaration
  now retains the exact `addDeclarationParams` row and its identity with the
  emitted symbolic parameters. Direct-call evidence retains the validator's
  effective parameter/result kinds and refinement equations. These are static
  production facts needed to initialize recursive callee frames; they contain
  no target execution or translation certificate and change no semantic Wasm
  ABI or concrete-runtime contract.
- Validation: Lean Beam update/sync/save for both edited proof modules,
  focused compiler-proof dependency cones, `git diff --check`, complete
  `make check` with 1,844/1,844 comparisons equal and zero findings, and all
  3,125 Talos jobs.

## Earlier completed integration lease

- Milestone: `W6-GENERATED-DECLARATION-FAMILY`.
- Integration owner: `wasm-proof`; the user retained the W6 owner as
  integration owner for this short certificate-free compiler-proof slice.
- Integration branch/worktree: `main` in the root worktree.
- Published stack: W6 functional head `e7993ecf` and ready mailbox `331c7ca0`,
  based directly on `main` at `09689696`.
- Lease boundary: satisfied. One successful production `lowerSupported` and
  `adapt` pair constructs `ConcreteGeneratedDeclarationFamily`, which
  universally selects every value-returning internal declaration with its
  independently computed compiler context and exact symbolic/concrete row.
  The family contains static compiler evidence only—no target execution or
  translation certificate—and changes no semantic Wasm ABI or concrete-runtime
  contract.
- Validation: Lean Beam update/sync/save for both edited proof modules,
  focused compiler-proof dependency cones, `git diff --check`, complete
  `make check` with 1,844/1,844 comparisons equal and zero findings, and all
  3,125 Talos jobs.

## Older completed integration lease

- Milestone: `W6-GENERATED-LOCAL-LAYOUT`.
- Integration owner: `wasm-proof`; the user retained the W6 owner as
  integration owner for this short certificate-free compiler-proof slice.
- Integration branch/worktree: `main` in the root worktree.
- Published stack: W6 functional head `bf4eabdb` and ready mailbox `151c582c`,
  based directly on `main` at `c2ea914a`.
- Lease boundary: satisfied. `lowerDecl` constructs one canonical emitted
  parameter-plus-body-local row and uses it for symbolic lookup. The generated
  declaration selector proves local-number and ABI-kind alignment from that
  row, with no caller-supplied layout certificate or hygiene premise. No
  semantic Wasm ABI or concrete-runtime contract changed.
- Validation: Lean Beam sync/save, focused compiler/proof dependency cones,
  `git diff --check`, complete `make check` with 1,844/1,844 comparisons equal
  and zero findings, and all 3,125 Talos jobs, both before and after rebasing
  onto the final base. W7 must rebase and run its artifact-specific gate
  because production lowering changed.

## Still older completed integration lease

- Milestone: `ILLUMINATE-TALOS-ADAPTER`.
- Integration owner: `wasm-proof`; the user reassigned the integration lease
  so the W6 owner could validate and land the exact cross-lane unblocker.
- Integration branch/worktree: `integration/closure-ownership` in
  `.worktrees/integration-closure-ownership`.
- Published stack: shared Float vocabulary `e39d0bbb` and unsigned i32
  remainder `78f3a9fc`, followed by W6 functional head `d31fad3e` and ready
  mailbox `c28955a5`.
- Lease boundary: satisfied. `FirTalos.Adapter` maps the complete released
  resident timestamp instruction cone to the corresponding Talos machine
  operations. The regression executes the adapted Float/i64 machine through
  arithmetic, comparison, shifts/bitwise operations, and unsigned conversions
  to the exact result `i64 42`; the resident arithmetic oracle also includes
  the released `i32.rem_u` step. No shared semantic or concrete-runtime
  contract changed, and later refinement theorems for W7's nine Illuminate
  helpers remain separate work.
- Validation: Lean Beam sync/save with zero diagnostics; focused adapter,
  example, and correctness builds; `git diff --check`; complete `make check`
  with 1,844/1,844 comparisons equal and zero findings; and all 3,125 Talos
  jobs. W7 may now rebase and finish its own artifact/Illuminate acceptance.

## Much older completed integration lease

- Milestone: `W7-PRETTYM-COLD-ENTRY-STACK-SAFETY`.
- Integration owner: `wasm-gen`; the user assigned this short integration
  lease after the preceding cross-lane lease had completed. The owner returns
  to the generation lane when this board update and the validated stack land.
- Integration branch/worktree: `integration/closure-ownership` in
  `.worktrees/integration-closure-ownership`, reused as the clean integration
  worktree rather than creating additional coordination infrastructure.
- Published W7 stack: functional head `4404aba0` plus ready mailbox
  `7f122148`, based directly on `main` at `26ed9fff`.
- Lease boundary: satisfied. The W7 artifact eliminates direct self-tail-call
  growth after lowering, makes the reported cold 2,047-node `prettyM` case the
  package's first execution, and republishes the zero-function-import artifact
  atomically. It changes no shared ABI, final LCNF, resident-helper signature,
  concrete-runtime layout, or W6 contract.
- Validation: Lean Beam sync/save; focused `lake build`; fresh cold 2,047-node,
  1,026-node grouped, and 32,767-node stress checks; `git diff --check`;
  complete `make check` (1,844/1,844 comparisons equal); all 3,125 Talos jobs;
  and the complete deterministic artifact/package gate pass. Artifact
  `prettyM-current-releases/4404aba07aa9-c040c75c6ef0cf70` is 104,833 bytes
  with digest
  `bb9ebbfe6e19dba3221a5a8bb16becbedd3014cc5f4a5f112927a94b35341792`.

## Oldest retained completed integration lease

- Milestone: `CLOSURE-APPLICATION-OWNERSHIP`.
- Integration owner: `wasm-gen`; the temporary lease is complete and the
  owner has returned to the generation lane.
- Integration branch/worktree: `integration/closure-ownership` in
  `.worktrees/integration-closure-ownership`.
- Published linked/accepted closure stack: proof/runtime head `229640de` on
  `main`, plus rebased W7 ready head `fdaa8bd1`. It composes corrected contract
  head `89fda41a`, LCNF
  proof functional head `1640c7d4`, LCNF ready mailbox `52ad964a`, W6
  functional head `b28feab9`, W7 adapter `fd6a51e3`, regression head
  `56d18362`, and all three ready mailboxes. Standalone ownership
  commit `528fdd1a` is the rebased identity
  of proof-base provenance `dbd7d934` and W7 provenance `d392e194`.
  Standalone external-runtime repair `89fda41a`, replayed from historical
  validation commit `2f301de5`, makes executable and relational external
  calls consume the post-application `waiting.runtime`. Both proof lanes are
  green on the composed contract; they do not base new proof work on the W7
  branch.
- Lease boundary: satisfied; the complete closure stack is `linked/accepted`.
- Scope: publish the stable contract base, validate and land lane handoffs in
  dependency order, rebase W7, then hand fixture admission to test-fixtures.
  The lease grants no permission to edit proof-, W6-, or validation-owned
  implementation files.

The live dependency order is:

```text
linked/accepted contract/pass-proof/W6 stack 229640de on main
  -> linked/accepted rebased W7 adapter fdaa8bd1
  -> test-fixtures admission of 32 scalar-closure cases
```

Each active agent owns exactly one record under `coordination/lanes/`.
Integration reads those committed records directly from the lane branches and
is the only writer of this board. This is intentionally a Markdown protocol,
not a coordination program.

## Current landing gate

This section is authoritative for the current integration boundary; older
candidate hashes in the lane and contract tables remain historical provenance
until their stacks land and must not be used as current feature-branch
identities.

- `W6-RANKED-FINITE-TRACE-SIMULATION-BOUNDARY` is linked/accepted through
  active record `f463519c`, W6 functional head `115fd2a1`, and ready mailbox
  `a7a33083`, based directly on `main` at `ef8a16eb`. Generic heterogeneous
  observed weak simulation now supplies exact finite-prefix transport and a
  rank for zero-target-step matches. The concrete W6 specialization proves
  that every finite LCNF `ExecSteps` prefix has a finite resumable target
  prefix with exactly related world and trace, without assuming source
  termination or accepting a caller certificate. Lean Beam, the final
  3,127-job Talos cone, all 1,844 repository comparisons on the immediately
  preceding documentation-only base, all 113 bug-card validations, and all
  3,127 Talos jobs pass. Next W6 work defines the structured resumable Wasm
  configuration and proves its finite terminating adequacy to Talos
  `Wasm.run`, before instantiating the compiler relation and rank from the
  existing operation laws.

- `W6-DERIVED-CLOSURE-RESOLVER-PACKAGING` is linked/accepted through active
  record `d00a26ce`, W6 functional head `bea8c53a`, and ready mailbox
  `9c9ae995`, based directly on `main` at `480c15e7`. The proof now inverts
  successful adaptation of the actual nested dispatch program, reconstructs
  the exact compiler candidate list and matcher host rows, and uses that
  derived package at every recursive closure site. The public theorem
  `ConcreteSupportedExport.correct_reuseCapacityProductionHereditary` has no
  resolver/certificate argument and still derives the matching terminating
  Wasm run, final runtime, and semantic value from every admitted finite
  source execution. Lean Beam, the focused 3,104-job cone, all 1,844
  repository comparisons, all 113 bug-card validations, and all 3,125 Talos
  jobs pass. The next W6 milestone states and proves finite-trace weak
  simulation so divergence can be handled without assuming source
  termination.

- `W6-STATIC-CLOSURE-CANDIDATE-RESOLUTION` is linked/accepted through bug-card
  report `1d55e858`, W6 functional head `9f6c5a05`, resolution `f4bf542e`, and
  ready mailbox `fcc1525d`, based directly on `main` at `9dab5f3c`. Static
  candidate rows now contain only compiler, adapter, and host-resolution
  facts; matcher execution is proved at the actual related live closure
  address. This closes
  `FIR-BUG-wasm-none-closure-resolver-invalid-address-totality` without
  weakening trapping behavior for invalid addresses. Both the one-layer and
  recursive whole-export theorems use the repaired boundary. Lean Beam, the
  focused 3,104-job cone, all 1,844 repository comparisons, all 113 bug-card
  validations, and all 3,125 Talos jobs pass. Next W6 work derives the static
  candidate-adapter environment directly from lowering/adaptation
  completeness, before the separate trace/coinductive extension.

- `W7-UPSTREAM-GENERIC-OBJECT-FAMILY-ABI` is linked/accepted through isolated
  shared contract `bd7a5e55`, W7 consumer `a13fa2ad`, Illuminate inventory
  ratchet `e5a8612b`, and ready mailbox `dfe6da0b`, based directly on `main` at
  `cdb8c4f3`. Named calls, control results, and symbolic stack admission now
  use Lean's generic object-family physical ABI instead of application-specific
  final-LCNF repairs. The semantic/proof refinement relation remains
  directional, scalar and erased lanes remain exact, and no concrete layout
  changed. The complete root, 3,125-job Talos, PrettyFormat, and Illuminate
  gates pass; Illuminate v3/v4 retain zero imports, all 106 checked-in traces
  agree, and both 10,000-dispatch tests retain flat post-rewind frontiers.

- `W6-RECURSIVE-WHOLE-EXPORT-CORRECTNESS` is linked/accepted through W6
  functional head `d8d5e607` and ready mailbox `de79fe52`, based directly on
  `main` at `de1c7ca7`. `correct_reuseCapacityProductionHereditary` proves
  finite partial correctness directly for the generated export: arbitrary
  finite nesting of named and exactly saturated closure calls returns the same
  runtime and semantic value as the source execution. The structural proof
  starts at the root and recursively follows actual compiler rows, while
  executable resolver metadata carries no target behavior theorem. Lean Beam,
  the focused 3,104-job cone, all 1,844 repository comparisons, and all 3,125
  Talos jobs pass. Next W6 work may package resolver metadata more
  automatically and state the separate trace/coinductive extension.

- `W6-RECURSIVE-GENERATED-CLOSURE-INDUCTION` is linked/accepted through W6
  functional head `feea71dc` and ready mailbox `40456ea0`, rebased directly on
  `main` at `db1295ab`. Every finite recursive generated declaration run now
  has a structurally derived target execution, including recursively nested
  named calls and saturated closure calls, with exact result, cache, world,
  budget, and exit-ABI obligations. Executable generated-row candidate
  enumeration remains metadata rather than a correctness certificate. Lean
  Beam, the focused 3,104-job cone, all 1,844 repository comparisons, and all
  3,125 Talos jobs pass. The next W6 slice preserves these recursive call
  payloads through the root-export adapter and exposes the public theorem.

- `W6-RECURSIVE-PRODUCTION-CLOSURE-PROOF-BOUNDARY` is linked/accepted
  through W6 functional head `cd8cd485` and ready mailbox `f6a09d46`, based
  directly on `main` at `a8f8ec0d`. The target induction is now explicit:
  every actual generated compiler row must refine every finite
  `ReuseCapacityProductionHereditaryCodeEvaluates` derivation from an ordinary
  concrete entry frame, and cumulative closure-allocation persistence derives
  the closure-ABI exit form. `GeneratedSaturatedClosureCandidateResolvers`
  supplies only executable per-row candidate enumeration and carries no
  source or target behavior theorem. Lean Beam, the focused 3,103-job cone,
  all 3,125 Talos jobs, and all 1,844 repository comparisons pass. W6 next
  proves this induction structurally by adding the saturated-closure case to
  the existing certificate-free compiler theorem, then exposes the recursive
  public export theorem.

- `W6-RECURSIVE-PRODUCTION-CLOSURE-SOURCE-EVALUATION` is linked/accepted
  through W6 functional head `a9c8ccfd` and ready mailbox `81b64c9a`, based
  directly on `main` at `6db0646a`.
  `ReuseCapacityProductionHereditaryCodeEvaluates` admits both named and
  exactly saturated closure calls recursively in their generated
  declaration-local contexts, so finite closure nesting is unbounded. Its
  source-step reconstruction and erasure theorem yield the exact public
  interpreter judgment. No constructor contains a target program, target
  store, refinement witness, target execution, or translation certificate.
  Lean Beam, the focused 3,105-job cone, all 3,125 Talos jobs, and all 1,844
  repository comparisons pass. Its exact generated-row target boundary is
  linked in `W6-RECURSIVE-PRODUCTION-CLOSURE-PROOF-BOUNDARY`.

- `W6-PRODUCTION-CLOSURE-EXPORT-PARTIAL-CORRECTNESS` is linked/accepted
  through W6 functional head `034b6330` and ready mailbox `15ebdcac`, based
  directly on `main` at `d8244e79`. `ProductionHereditaryCallSupported`
  combines generated named calls with exactly saturated closure applications,
  and the public export theorem proves that every finite execution in the
  current production fragment is matched by a terminating generated Wasm
  export with the same runtime/value observation. The proof lifts the closure
  law through the ordinary whole-cache frame from entry ABI alignment and
  cumulative closure-allocation persistence; no target execution or per-call
  target certificate is assumed. Exit ABI alignment is retained. Lean Beam,
  the focused 3,105-job cone, all 3,125 Talos jobs, and all 1,844 repository
  comparisons pass. The admitted closure callee is presently a
  direct-hereditary derivation, making the one-closure-layer frontier explicit;
  W6 next generalizes nested closure applications and connects concrete fixture
  derivations to this public theorem.

- `W6-CLOSURE-ALLOCATION-PERSISTENCE` is linked/accepted through W6
  functional head `7943fdfa`, based directly on `main` at `18af585a`. All
  ordinary concrete runtime operations now carry a compositional proof that
  post-state closure descriptors were already present in the pre-state, and
  `ClosureAllocationsAbiAligned.ofPersistent` turns that fact into ABI-frame
  preservation. W6 next threads the same fact through external operations,
  lifts direct/effect/external generated laws to the ABI frame, and derives
  `DirectHereditaryGeneratedDeclarationAbiInduction` from those compiler laws.

- `W6-SATURATED-CLOSURE-HEREDITARY-RUNTIME-LAW` is linked/accepted through W6
  functional head `bca03085`, based directly on `main` at `5307f77d`. The
  selected matcher may consume the source closure; capture projection,
  generated argument assembly, and the callee all start from its real
  successor store and semantic call runtime. Exact compiler-candidate
  inversion derives the selected call body and complete physical
  capture-plus-argument row. The new production runtime theorem accepts no
  unchanged-store equation, per-call body theorem, argument assembly, or
  target execution certificate. Its only remaining global premises are the
  executable candidate resolver and the program-wide ABI-preserving generated
  declaration induction. Lean Beam, focused dependency cones, all 3,125 Talos
  jobs, and all 1,844 repository comparisons pass. W6 next proves those two
  global premises, beginning with generated-operation preservation of the
  program-indexed closure allocation ABI invariant.

- `W6-DIRECT-HEREDITARY-SOURCE-EVALUATION` is linked/accepted through W6
  functional head `cbb0f0d1` and ready mailbox `6fe75308`, based directly on
  `c882cdc8`. Direct named calls now have a genuine source-recursive finite
  evaluation derivation carrying nested callee-body and caller-continuation
  executions. It reconstructs the actual interpreter call prefix and yields
  the exact source result without target execution, witnesses, or translation
  certificates. The complete root and Talos gates pass. W6 next makes the
  production direct-call runtime law consume this hereditary payload, selects
  the generated callee row, and applies its induction hypothesis to eliminate
  the opaque `DirectInternalCallDeclarationInduction` premise before adding
  saturated-closure and lazy-miss constructors.

- `ILLUMINATE-LIVE-PLAYER` is linked/accepted through W7 functional head
  `b72f2bfa` and ready mailbox `e5d9cd65`, based directly on `a07defe0`. The
  immutable v3 package has zero imports, module-owned memory, independent
  per-player instances, persistent animation/state storage, exact scratch
  rewind, and bounded 10,000-tick memory. Illuminate may now stage the package
  for its authoritative 106-trace and live-dashboard acceptance gates. W6 may
  independently prove `fir_heap_rewind`; that proof is not claimed by W7 and
  does not block generation acceptance.

- `W6-DIRECT-CALLEE-EXACT-BUDGET-INDUCTION` is linked/accepted through W6
  functional head `e05c9110` and ready mailbox `178f67a7`, based directly on
  `dcb7d6b3`. The production direct-call theorem retains the enclosing call's
  budget-fit fact, constructs the generated callee frame at the finite source
  body's exact cost, proves the adapted physical arity, and derives the full
  cache-aware successful-declaration package from finite source evaluation and
  uniform operation laws. No target execution, translation certificate, or
  semantic/runtime contract was added. The complete root and Talos gates pass.
  W6 next defines a source-only hereditary finite-evaluation relation carrying
  nested callee and continuation derivations, then recurses over it before
  adding saturated-closure and lazy-miss constructors.

- `W6-CALLEE-ARGUMENT-REFINEMENT` is linked/accepted through W6 functional
  head `73492cd9` and ready mailbox `837dcf05`, based directly on `298682a7`.
  `ConstructorArgumentsRelated.ofKindsRefine` reinterprets the unchanged
  physical/source argument row at the generated callee's exact parameter ABI
  using the validator's pointwise refinement fact. The generated internal row
  also carries the declaration-parameter uniqueness fact proved from the
  production `lowerSupported` traversal, closing the malformed duplicate-
  binding case at the recursive proof boundary. No execution certificate or
  semantic/runtime contract changed. The complete root and Talos gates pass.
  W6 next proves exact source-order parameter/local identity, constructs the
  empty-facts callee-entry frame, and begins the finite-execution hereditary
  induction.

- `ILLUMINATE-TALOS-ADAPTER` is linked/accepted through W6 functional head
  `d31fad3e` and ready mailbox `c28955a5`, based directly on released numeric
  contract head `78f3a9fc`. The adapter now covers `f64.const`, unsigned
  `i32.rem`, the resident i64 bit/shift/comparison operations, f64
  arithmetic/comparisons/rounding, and the unsigned i32/i64/f64 conversion
  chain. Its executable Talos regression returns exact `i64 42`, the complete
  W6 proof cone builds, and integration revalidated all 1,844 repository
  comparisons plus all 3,125 Talos jobs. This removes W7 mailbox `8a98a702`'s
  sole blocker without claiming the separate refinement theorems for its nine
  Illuminate helpers. W7 may rebase `wasm/generation`, run its artifact and
  Illuminate acceptance gates, republish, and mark its mailbox ready.

- `W6-GENERATED-LOCAL-LAYOUT` is linked/accepted through W6 functional head
  `bf4eabdb` and ready mailbox `151c582c`, based directly on `c2ea914a`.
  Production lowering, symbolic lookup, emitted parameters/locals, and numeric
  adaptation now share one canonical binding row. Consequently
  `ConcreteGeneratedDeclaration.exists_ofSupportedPipeline` derives
  `LocalLayoutAligned` internally and no longer accepts a layout certificate
  or declaration-hygiene premise. All 1,844 repository comparisons and all
  3,125 Talos jobs pass. W7 must rebase and confirm its deterministic artifact.

- `W6-GENERATED-DECLARATION-FAMILY` is linked/accepted through W6 functional
  head `e7993ecf` and ready mailbox `331c7ca0`, based directly on `09689696`.
  `ConcreteGeneratedDeclarationFamily.ofSupportedPipeline` assembles all
  value-returning internal declarations from the production lowering and
  adapter equations while preserving each declaration's local compiler
  context. It introduces no target-execution certificate and changes no
  semantic ABI/runtime contract. All 1,844 repository comparisons and all
  3,125 Talos jobs pass. W6 next proves the dynamic hereditary family by
  well-founded induction over admitted finite source executions, supplies it
  to named calls, saturated closures, and lazy misses, then exposes the clean
  whole-export partial-correctness theorem.

- `W6-CALLEE-PARAMETER-ROWS` is linked/accepted through W6 functional head
  `a83651c4` and ready mailbox `a0374752`, based directly on `d69e0252`.
  `ConcreteGeneratedInternalDeclaration` retains the exact production
  parameter-local row and proves that it is the emitted function parameter
  row. `DirectInternalCallSite` retains the validator's argument/parameter
  and callee/result refinement facts. This closes the static compiler-data
  boundary needed to construct recursive callee-entry frames, without adding
  execution certificates or changing semantic ABI/runtime contracts. All
  1,844 repository comparisons and all 3,125 Talos jobs pass. W6 next derives
  the entry value relation and starts the well-founded dynamic hereditary
  proof.

- `WASM-DECLARATION-PARAMETER-UNIQUENESS` is linked/accepted through isolated
  contract head `dfa8153e`, after queue/card head `03547684`, based directly
  on `b2ecf2a4`. `supportedDecl` now rejects duplicate same-scope declaration
  parameter identifiers. The regression demonstrates that the previous raw
  lowerer collapsed two source parameters to one symbolic Wasm parameter and
  produced an invalid call stack, while `lowerSupported` now rejects that
  malformed program. Bug card
  `FIR-BUG-wasm-none-duplicate-declaration-parameters` is fixed. All 1,844
  repository comparisons and all 3,125 Talos jobs pass. W6 and W7 rebase on
  the released support-domain contract before continuing.

- `SCALAR-CLOSURE-ABI-ADMISSION` is linked/accepted through W6 functional head
  `cf1ed73f` and ready mailbox head `4013a6ba`. The lowering decision is
  structural and shared by every production and proof-side consumer. The
  concrete boxing theorem derives the precise tagged UInt8 result from the
  existing scalar relation, while the public correctness roadmap continues to
  state a general certificate-free compiler simulation theorem. The unfenced
  scalar-closure probe passes all 32 cases and all 96 directed comparisons
  with zero findings. W7 independently reproduced the same public-compiler
  and real-engine result under ready mailbox `6f5b5b5c`: all 64 emitted
  products were consumed and no W7 implementation or artifact changed.
  Test-fixtures may now remove the `wasm-generation-pending` fences.

- W7 functional head `4404aba0` and ready mailbox `7f122148` are
  `linked/accepted`. The final closed `prettyM` modules now rewrite validated
  direct self-tail calls into parameter reassignment plus a structured Wasm
  loop, so the engine stack no longer grows with the formatter worklist. Cold
  balanced documents with 2,047 and 32,767 nodes and the reported 1,026-node
  grouped shape pass before any warm-up. The canonical artifact remains
  self-contained with zero function imports and unchanged public ABI; its
  digest is
  `bb9ebbfe6e19dba3221a5a8bb16becbedd3014cc5f4a5f112927a94b35341792`.
  `FIR-BUG-wasm-none-prettyM-cold-entry-call-stack-overflow` is fixed. A
  correctness theorem for the post-lowering transform is a separate possible
  W6 follow-up and does not invalidate any resident-helper proof.
- Validation facade repair `5987c17e` accepts the exact source export plus the
  canonical bit-exact integer-lane facade for floating signatures, while
  retaining the singleton source-export requirement for non-floating entries.
  Lean Beam, `lake lean FirValidationWasm.lean`, the complete root gate, and
  direct Node execution of the validation-only one-use and two-use mixed
  closure products pass. The corresponding validation bug is fixed; fixture
  admission remains separate from this provider repair.
- `CLOSURE-APPLICATION-OWNERSHIP` is green through the shared contract, LCNF
  pass-proof, W6 concrete-runtime refinement, and W7 executable adapter.
  Corrected runtime
  contract `89fda41a`, LCNF proof functional head `1640c7d4`, and W6
  functional head `b28feab9` are composed under ready head `c8e2eb5d`. The
  pass proof relates
  persistent, exclusive-transfer, and shared-decrement/retain applications
  across AlphaEqv, SimpCase, and ElimDead, including reachability-aware
  runtime proofs, terminal faults, and external waiting-state execution. It
  resolves `FIR-BUG-impure-none-closure-application-external-runtime` with an
  executable regression. Integration revalidated the explicit 34-job
  `Fir.LeanIR.Passes.ElimDeadExamples` cone and the full root `make check`:
  122 validator tests and all 1,844 backend comparisons pass, bug-card
  validation passes, and the trusted-assumption gate reports exactly the one
  registered axiom. W6 implements the same persistent, exclusive-transfer,
  and shared-retain boundary through the concrete Talos matcher/projection
  runtime and follows the repaired external waiting-state runtime. Independent
  integration validation passes `git diff --check`, the complete root gate,
  and a fresh pinned-Talos build of all 3,131 jobs. The stack is therefore
  `linked/accepted` on `main` at `229640de`. W7 then dropped the patch-equivalent
  historical contract commit `d392e194`, rebased adapter `2ed6deb4` as
  `fd6a51e3`, and resolved the stale packaged semantic-host expectation in
  `56d18362`. The exact W7 head passes `git diff --check`, the root gate, all
  3,125 Talos jobs, and the complete deterministic artifact/package gate.
  Text and styled `prettyM` remain at zero function imports; the 104,788-byte
  styled digest remains
  `e7ccd1ac678900e0f6583a0d2251b0ef4d43de0b388d18033bbc86344eed4af7`.
  The next independent action is test-fixtures admission of the 32 queued
  scalar-closure cases.

- Validation's validated pre-record coordination head is `3ae6c37d`, with
  functional head `96eec154` on semantic base `fff91175` and coordination head
  `cfa17d81`. The current functional validation boundary on `main` is
  `c05e85d9`, so the long validation branch is fifty-seven commits behind and
  one hundred twelve
  commits ahead. Its older commits `a2907a66`,
  `7c87e6ec`, `bb387042`, `9171fdd6`, and `cb03e9ab` have been superseded by
  current-main landings `15b8727e`, `e08784b3`, `6ab2efed`, `e7f2b457`,
  `9f067817`, and `3853a923`. The next long-branch rebase drops their duplicated
  mechanisms; it preserves the long-only Float/IO domain declarations as a
  later additive calibration after their shared contracts land.
- Rebased native/LCNF run
  `92b727e4a1d82ccfb3a9f419e28f9afd880ccd43ca1b1f0b985dcaa0874e19cb`
  passes 1,008/1,008. Immutable evidence
  `30ffef11f503b580bedcebcbb5e3f1a9e1d018931beeacdcff769c1402c077cc`
  verifies offline and produces native-to-LCNF attestation evidence
  `d5f45f4be4a2dfb82696ab8f479b48726b5a10465565ba3c8c105b6d17f4b529`
  under unchanged semantic contract
  `4b22ce16a4d906ebae0a68a2fb7e76f7edaee085df36e7451ebb6387e4c681cd`.
  Direct run
  `181d002006e4fe4d2e32c9f228cb917b8c181e547b113095c121f7f44d0e5ab9`
  passes 9/9. Coverage identity
  `a69c8067b69038d096e58393ea2784ba32e2063249d595885afc37d91c48dc25`
  retains all 1,017 comparisons, 9,939 steps, 193 tag floors, 152 semantic
  domains, and every ownership floor with zero findings.
- Main checkpoint `41f40efd` independently passes its complete 581-case
  native/LCNF/V8 baseline at run
  `6b0adcc9d017167bc42be2841ae86cdffad70737724c51cd39bcf7ae3f9581e2`,
  evidence
  `4b8368999394c1b74855d68dcae7eba915b34c6e6d36c8c5d2b380a2db4892e2`.
  All three edges are equal, all 1,162 compiler-product reads are confirmed by
  `strace`, and the 581 native-to-V8 cases meet the 581-case global oracle
  floor. The retained 67-case protocol-v4 float/mixed triangle is an additive
  frontier, not the total real-engine baseline. Functional `main` at `0971181c`
  passes the complete `make check`, including the same 581-case triangle plus
  thirty-two source-only native/LCNF cases and its 622-case composed coverage index.
  The index rederives exact tag-to-case attribution from retained corpus
  evidence and enforces 41 per-tier semantic floors plus 116 conjunctive
  domains: all 3,411 required tag-attributions and 1,623 domain memberships are
  present. Forty-six matching source and V8 domains pin arithmetic boundaries,
  external families,
  failures, closures/control flow, effects, ownership, mutation, and text/byte
  behavior; two direct-machine domains pin recursive release and reset/reuse.
  It also supplies enforceable `portable` and `exact` equivalence gates for two
  independently verified evidence graphs. The current protocol-v4 attestor
  correctly rejects the protocol-v3 baseline evidence as an unsupported
  version, so it is strong runtime evidence but not a current global oracle
  attestation; that v4 claim still waits for W7.
- Current-main landing `e7f2b457`/`9f067817` closes the comparison-provenance
  gap. Every successful validation run atomically publishes a self-hashed
  receipt naming its exact append-only run/evidence/matrix snapshot; receipt
  verification rejects symlinks, path escape, identity substitution, and
  disagreement with the fully verified source graph. The root gate now records
  comparison attestations only from that immutable snapshot and rechecks the
  resulting aggregate offline. The rebased complete `make check` passes 122
  harness tests, 593 native/LCNF cases, 9 direct cases, the 581-case
  native/LCNF/V8 triangle, all 103 semantic domains, bug cards, trusted
  assumptions, and placeholder policy. Its latest retained V8 receipt is
  `7745f51feec5dc76a85a7120ce169f28aeae9d227fe78c5db6516db5a26fc90c`;
  run `1cfcf94879bc5ffc01425965b89a82ec8ad9c13b05a495e691a879ca55c33913`
  names source evidence
  `d0e40b223316777475dcbd41fed5e4cbaf4a4a6bde0330e852aa2af09b9ae218`
  and matrix
  `4a24c5ff4d0def34591480cb8c017489bf276823a73d7461c439fbbf4ce9bf15`.
  The three-edge comparison envelope has stable contract
  `e2d5bed981aea99d01d1f370c1411e44e972da4d28a60e1f3e3077b1af6930bf`,
  evidence
  `dcfbdc189797f569808b9d1afeee6471904603f4bd6d3b90270d192cb2e2868e`,
  and 1,162 witnessed native-oracle comparisons under policy
  `e11ddcfc5fd9bff44f46a4eb593a47bb5905796c6ea48ab1661ab96e6d219e31`.
- Current-main landing `3853a923` fixes
  `FIR-BUG-impure-none-bool-entry-scalar-abi`: runner-supplied `Bool` arguments
  now use Lean's unboxed `UInt8` final-LCNF entry ABI. Both Boolean values pass
  native comparison through an exact compiler-generated
  `box`/`pap`/`unbox`/branch trace. The pre-repair two-case run
  `fcd103e5fdf020e697e49d2450a4088d46e3c595f413849cef04f18772ddfde5`
  stops after `admin:invoke-name, form:box` with `expected-scalar`; immutable
  evidence
  `9b30f4e9e20272d6ca313d4a0bef3989514f4e79116e5c8db9fa497a0f2e6fb1`
  records both mismatches before the fix. Strict plan-level `excludeTags`
  now lets source-oracle coverage advance without pretending an unready
  compiler case ran in V8; online and offline verification both reject a
  selected excluded case. The two fixtures carry `wasm-generation-pending`
  because W7's public compiler surface returns the typed `unsupportedCode`
  error before emitting a product. This is an explicit future admission
  handoff, not a request to overlap W7's active compiler work.
- Current-main landing `8ea9f75b` generalizes that boundary into a ten-case
  unsigned entry-ABI matrix for `UInt8`, `UInt16`, `UInt32`, `UInt64`, and
  `USize` at zero and maximum. Each fixture crosses the same polymorphic
  generic-application and partial-application path, distinguishes captured
  from applied arguments, and pins an exact 17-form/27-step trace with two
  boxes, one `pap`, three `fap`, one `fvar`, one `inc`, three `dec`, one
  `unbox`, and five returns. All ten agree with the native Lean oracle. A
  representative W7 public-compiler probe still returns typed
  `unsupportedCode`, so the matrix joins the two Boolean fixtures behind the
  verified `wasm-generation-pending` plan fence instead of claiming V8
  execution. Coverage identity
  `4610894624ca64aff2bd6aac8af4e9a2d24d084f2d9a2a35dc22ef9ce2be248b`
  ratchets the source tier to 593 cases and the composed gate to 602 unique
  cases, 1,764 comparisons, and 5,110 interpreter steps with zero findings.
- Current-main landing `0971181c` adds the signed counterpart: twenty
  `Int8`/`Int16`/`Int32`/`Int64`/`ISize` entry-ABI cases at minimum, negative
  one, zero, and maximum. Captured and applied operands are deliberately
  distinct, every case pins the same exact 17-form/27-step partial-application
  trace, and a source guard checks each raw two's-complement scalar encoding.
  All twenty agree with native Lean. A representative W7 public-compiler probe
  still returns typed `unsupportedCode`; no W7 source changed, and these cases
  join the two Boolean and ten unsigned cases behind the explicit
  `wasm-generation-pending` fence. Explicit `signed`/`unsigned` attribution
  keeps the two entry-ABI matrices disjoint. The complete post-proof rebase
  gate passes 613 native/LCNF cases, 9 direct cases, and the unchanged 581-case
  native/LCNF/V8 triangle: 622 unique cases, 1,784 equal comparisons, and 5,650
  interpreter steps with zero findings. Native run
  `e545b9946cc88ac4abd52434aadf3793a5e66474a3016b6966fcec8119241be3`
  has evidence
  `f665d601de5c986fb0f2b8193f0494ee26489b80562a60b3a28d10a138daab80`,
  receipt hash
  `675a17eeb1010beef72c40a75dbabab03784acc6686f5deb5ab6e6e265f6ea0f`,
  and matrix hash
  `b5db1890d95fc52a3613ba76052ef4c0cab0cac01d537934bbc9a8f12f16dd6f`.
  V8 run
  `edf688173c01869d931315c2bf94465dc49a6c133b9eba7e9e6b568f29dacd93`
  has evidence
  `5d088a1f65b29844f8dbf7198a1053def8533153631ceb3f91bb485908cf23f0`,
  receipt hash
  `d105f76750ec19a9f9e12e088e1ddc549b3c0f17d8597f2403f21bcb6e8508cb`,
  and matrix hash
  `92746a186358033707e2b67a05a067a384dc62b6fd61729b6835256106d88ef5`.
  The three-edge attestation evidence is
  `87127d87d576cae3cfe0cda6e0d374821dfbedc82ada8a81f2cc32dc91f5879d`
  under contract
  `ac8551d05c2a0fa07906491d0bb7e143e600dc1094df1a875be47cd5710c9e73`;
  the coverage-index hash is
  `d68bff2432aeac98d3a76ea1e3b0099a7f4689374bfbe599320866e52c5bc69d`.
- Current-main landing `c05e85d9` adds the complementary signed result-ABI
  matrix: twenty argument-free `Int8`/`Int16`/`Int32`/`Int64`/`ISize`
  entries return minimum, negative one, zero, or maximum from the raw unsigned
  structure field. Each LCNF path is pinned to exactly `lit`/`return` plus the
  three invocation/cache/completion administrative transitions, and an
  independent decoder guard checks all twenty two's-complement payloads. W7's
  existing public compiler accepts every entry without a source change; all
  twenty pass native/LCNF/V8 triangulation and the recorder opens all forty
  focused compiler products. The full post-rebase gate passes 633 native/LCNF
  cases, 9 direct cases, and 601 native/LCNF/V8 cases: 642 unique cases, 1,243
  tier cases, 1,844 equal comparisons, and 5,750 interpreter transitions with
  zero findings. All 51 tag floors (3,994 memberships) and 142 semantic domains
  (1,803 memberships) are exact. Native run
  `eaf0a710c87093615162a007dc1d46e2b231d5b52f853ccc16391bc753ed9291`
  has evidence
  `b2f8e89d34ae47b76aaed9001e103540547560a8bcdbd2636aed08b4dbfc7d76`,
  receipt identity
  `0270e3549ed9671e7e4bda2e548a3816a1bde59646e979c1d5863768b3549fd2`,
  and matrix hash
  `c33739400ca57bde90671de647e3c97a19cceb312521e7ae6868f7d43ac3bc54`.
  V8 run
  `63f16267d477c11d4cbb85fa4101ff0e0a7078f53b979c3b479aa2b861c18537`
  has evidence
  `fb6cf0659c3d962f299def7a1a993c75cf1685df2ad0afd48135fcc0e91c9f03`,
  receipt identity
  `c8d65721350ccbb9f969bbcb13a771a16875e8ff825f3f7a3101b83beb27c328`,
  and matrix hash
  `105c51c9b046898cc314ff83e41fe660a379270d195842768749d01bbf528054`.
  Three-edge attestation evidence
  `9798e135fc45efcf73a2b7cd5b04ac5720de9191c40c687ee251c96e31e0c7cc`
  has contract
  `8cb65225d54fb00214cc4ed0f66de537aa2af2aad5b9cd2257bb00ebc1925ef6`;
  coverage identity is
  `44f9cb11afd6064ae99aa3f675b18d6429e928e7a6e9a68bb829365e01a7d55d`.
  No bug card was needed, no W7-owned file changed, and the thirty-two pending
  scalar-closure fixtures remain unchanged.
- The first shared-contract commit in the long lane-4 stack, `7053d748`,
  passes the full Lean build, examples, harness tests, native/LCNF baseline,
  and direct tier in isolation. Its only `make check` stop is the W7-owned
  exhaustive match at `Fir/Wasm/Emit/Manifest.lean:149,255,280`, before V8
  executes. Independent validation-infrastructure commits may continue to be
  extracted and landed early, but the first remaining shared integration slice
  is still the float scalar contract plus W7's manifest handoff.
- The whole lane-4 stack still needs its successive shared-contract boundaries
  re-probed after rebasing. The last pre-rebase probe stopped exactly at
  `AlphaEqvCode.lean:2209,2358,2360,2616` plus
  `SimpCaseRelation.lean:427,1248,1250,1317,1319`; those locations must be
  re-probed after the next validation rebase rather than assumed current.
  Proof commits `7c0bb6c3`, `28aa7930`, and documentation checkpoint
  `405d910f` are now on `main`: captured fixed arguments are recovered from
  heap ownership, full and re-partial value invocation preserve the source
  carrier, and the ownership-strengthened internal dispatcher covers code,
  yielded, named, and value controls. Proof handoff `ba15b0dc`/`349a8286`/
  `2f94f5a0` is now on `main`: it states the source foreign-response ownership
  contract, preserves it across external waiting/resumption steps, and packages
  the source-owned simulation for downstream consumers.
  Follow-up `3723e145` separates client static/source-target preservation from
  the concrete source ownership carrier: the new current-state exact relation
  advances both along the selected non-lockstep paths, and the checked
  allocation-plus-three-writes fixture reaches `LoweringCorrect` through the
  new compiler-facing contract.
  Follow-up `25cc1ceb` makes that ownership parameter operationally
  significant: the checked concrete reset/reuse fixture transports the
  source carrier into reset readiness, derives post-reset heap freshness from
  `HeapOwnershipBelowFrontier`, and reaches `LoweringCorrect` through a direct
  source-owned exact contract without enumerating the post-reset heap.
  Checkpoint `83bdedd5` factors that last argument into generic source-owned
  reset-readiness bridges. A locally successful reset now inherits
  post-state heap freshness directly from the maintained source carrier, for
  both empty-target and target-ledger/source-only-closure shapes; the concrete
  reset/reuse client consumes the generic bridge.
  Proof landing `4e882842` combines source ownership with the exact target
  allocation ledger in one non-lockstep simulation and compiler-facing
  contract. Source ownership advances independently of the chosen target path;
  the concrete nonempty-target reset/reuse client derives reset freshness from
  that carrier and reaches `LoweringCorrect`. Its post-rebase dependency build
  and complete root gate pass.
  Follow-up `6060a918` factors the retained target residual, live binding, and
  allocation frontier into one local target-prefix invariant shared by
  deleted reset and concrete reuse. Their duplicated finite target-state case
  analyses are removed, and closure/token provenance is now independent of a
  concrete ledger frontier.
  Proof landing `f5814ec6` removes the retained-prefix target finite graph
  altogether.  Its three-phase allocation/control invariant is initialized
  at entry, preserved by every target step, and abstracts all
  post-allocation states behind the retained live binding, exact frontier,
  and non-allocating terminal controls.  Both exact contracts consume this
  invariant and retain the checked `LoweringCorrect` endpoint.
  Proof landing `3c071252` extracts the program-independent
  `TargetSingletonLiveReturnAt` interface and its generic target-ledger
  exclusion theorem. The retained-prefix client now supplies only its binder,
  mapped owner, frontier, and singleton-prefix fact; both deleted reset and
  reuse consume the shared theorem instead of a fixture-local target shape.
  Proof landing `c904f3e8` factors that calculation through the arbitrary
  `TargetMappedOwnerPrefix` interface. Every target-prefix address now carries
  a proof-visible source owner and forward mapping; pointwise owner exclusion
  generically yields source-only ledger provenance, while the one-cell fixture
  is only an adapter.
  Proof landing `40aebeeb` replaces the retained-prefix fixture's ten-state
  source reachability graph with the reusable hereditary
  `SourceLocalReadinessPlan`. Eight ordinary states now expose target-independent
  source runtime/ownership readiness directly; only deleted reset and concrete
  reuse remain ledger-sensitive local nodes. Both ledger-exact contracts consume
  the plan through its one-step closure and retain the existing checked
  `LoweringCorrect` endpoint. The post-rebase Beam checkpoints report zero
  errors, the 34-module dependency build passes, and the complete root gate
  passes 633 native/LCNF cases, 9 direct cases, and 601 native/LCNF/V8 cases:
  642 unique cases and 1,844 equal comparisons with zero findings. No shared
  semantic contract or bug card changed.
- Shared float runtime and proofs are landed on `main` through `8a8d1387`.
  W6 handoff `8a8d1387` on base `ae995ba8` adapts concrete boxing to the
  heap-only float representation; the integrated stack passes `make check`
  (633 native/LCNF, 9 direct, 601 V8, 1,844/1,844 comparisons) and
  `make talos-check` (3,123 jobs). Both `main` and `wasm/talos-runtime` are
  clean at that boundary.
- Released contract `8ad80ad3` supplies the fail-closed
  `bitExactFloatTransport` consumer contract independently of the queued Lean
  float stack. It selects an integer-lane Wasm facade, preserves all raw f32/f64
  bits as `BigInt`, rejects missing or malformed capabilities, and passes the
  complete root gate. Integration consumer `57f13122` now selects that facade
  in the canonical validation runner and passes 613 native/LCNF cases, all 581
  compiler-admitted V8 cases, and 1,784/1,784 comparisons. W7's clean facade
  and consumer checkpoint is `e5c67f54`; its next action is to rebase after the
  queued Lean float contracts land.
- W7 ready head `fdaa8bd1` is rebased directly on landed proof/runtime stack
  `229640de`. It passes `make check` (642 unique cases, 1,844/1,844
  comparisons), `make talos-check` (3,125 jobs), and the complete deterministic
  artifact gate. Its text and styled `prettyM` modules have zero function
  imports; packaged release `prettyM-current-releases/56d183620ef6-18387878afbd3b7b`
  publishes the 104,788-byte styled artifact digest
  `e7ccd1ac678900e0f6583a0d2251b0ef4d43de0b388d18033bbc86344eed4af7`.
  Exact Float32/Float64 signed-zero, infinity, quiet/signaling-NaN, maximum
  payload, argument, result, manifest, concrete-host, browser-client, and
  native-oracle paths all pass without JavaScript numeric coercion.
- W6 proof handoff `c82554fb` is landed on `main`, with functional head
  `f215c995` on W7-compatible base `fb18c01f`. The concrete compiler boundary
  retains the phase's top-level name uniqueness, derives exact internal-call
  indices from the executable lower/adapt tables, and makes production named
  calls consume correctness of their nested finite hereditary source
  derivation. The call site supplies no target index, target execution, or
  translation certificate. Lean Beam is green, `make check` passes 642 unique
  cases and 1,844/1,844 comparisons, and all 3,125 Talos jobs pass.

## Lane snapshot

Lane rows name their own landed commits; the board intentionally has no
moving global snapshot hash.

| Lane | Owner handle | Branch | Status | Current slice | Contract impact |
|---|---|---|---|---|---|
| Integration | integration owner | `integration/closure-ownership` | released | `WASM-DECLARATION-PARAMETER-UNIQUENESS` is green at isolated contract head `dfa8153e`; W6 and W7 rebase after main landing. | Narrows `WasmSupported` only for malformed duplicate binders. Semantic ABI and runtime contracts are unchanged. |
| Lean pass proof | pass-proof owner | `proof/simpcase` | released | Ready mailbox head `52ad964a`, functional head `1640c7d4`, on corrected contract base `89fda41a` relates persistent, exclusive-transfer, and shared-retain closure application across AlphaEqv, SimpCase, and ElimDead. The 34-job examples cone and full root gate pass. | Changes no shared contract. The external waiting-runtime bug is resolved with a proof regression and landed in stack `229640de`. |
| W6 runtime proof | W6 owner | `wasm/talos-runtime` | released | Ready mailbox `a7a33083`, functional head `115fd2a1`, on base `ef8a16eb`, establishes the ranked heterogeneous finite-trace simulation framework and its exact LCNF-to-resumable-concrete specialization. | No shared semantic or runtime contract changed. The final 3,127-job Talos cone passes. Next define a structured resumable Wasm configuration, prove finite terminating adequacy to Talos `Wasm.run`, and instantiate the compiler relation/rank from W6 operation laws. |
| W7 generation | generation owner | `wasm/generation` | released | Ready mailbox `dfe6da0b`, functional head `e5a8612b`, on base `cdb8c4f3`, replaces application-specific final-LCNF kind repairs with the generic Lean object-family call ABI and publishes reviewed PrettyFormat and Illuminate v3/v4 artifacts. | Shared contract `bd7a5e55` makes `object`, `tagged`, and `tobject` compiler-call compatible without changing directional semantic refinement or concrete layout. W6 rebases and consumes the stable generic Array/weak-Inhabited `tobject` signatures in its next proof checkpoint. |
| Compiler-native Wasm | integration owner | `wasm/lcnf-c` | parked | Landed checkpoint `a4855402` adds a separately packaged C/Emscripten `Std.Format.prettyM` facade on top of the optimized final-LCNF-to-C route from `2760e3e0`. The browser adapter shares the compact `Format` request and exact `{text, events}` trace contract with W7's FIR-native facade while retaining a private bulk wire, verified Emscripten loader, full pinned Lean runtime, and independent package. The differential suite compares Unicode, grouping, nesting, tags, arbitrary-precision values, initial columns, malformed requests, repeated calls, and a one-MiB UTF-8 transfer through both engines | No shared semantic contract changed and the packages remain physically independent. The lane consumes `Std.Format.prettyM`, final impure LCNF, and Lean's C ABI without changing the symbolic Wasm, W6 concrete-runtime, or W7 resident-runtime surfaces. Resume with controlled sampled profiling of the facade wire and generated C before accepting a runtime optimization |
| Validation | validation owner | `validation/float-corpus` | active | Clean coordination head `cfa17d81` retains the long 1,008-case native/LCNF calibration. Current-main validation covers 633 native/LCNF cases, 601 V8 cases, 642 unique cases, 1,844 comparisons, 5,750 interpreter transitions, 51 semantic-tag floors, and 142 conjunctive domains. | Test-fixtures may now rebase and admit the 32 scalar-closure cases. The long validation branch rebases separately; alias, termination, IO, and stream-capture contracts remain isolated. |

## Resident-helper bridge

| Helper or artifact | Generation commit | Contract base | State | Proof owner | Artifact digest |
|---|---|---|---|---|---|
| Existing resident helper set through closure matching | landed on `main` | recorded in Talos plan | generation-ready | W6 owner | recorded by individual manifests |
| Resident allocator, constructors, and styled `prettyM` through immediate Naturals | `64831f6` | `40f41c0` | generation-ready | W6 owner at the later contract bridge | styled Wasm `5d14b3fd2b1eb93de344ee69c6117e539eeed320c857248eb0fd4691b9d9e5d2` |
| Standalone immediate-Natural and UTF-8 String literals | `64831f6` | current W6 object layouts | generation-ready | W6 owner | Wasm `ab63fa578576748ff3ea8230986cf908d7285c54bc840bb60fec5fc7fa978473` |
| Bit-exact float source probes and styled zero-import `prettyM` package | W7 ready head `fdaa8bd1`; package source `56d18362` | landed closure proof/runtime stack `229640de` | linked/accepted | W6 float and closure refinements landed | styled Wasm `e7ccd1ac678900e0f6583a0d2251b0ef4d43de0b388d18033bbc86344eed4af7` |
| Generic object-family calls and resident Array/weak-Inhabited results | `a13fa2ad` | shared call-ABI contract `bd7a5e55` | generation-ready | W6 owner for the later concrete refinement bridge | styled PrettyFormat `c928d30adb3d39f7409e7091b4e1f13289aac35c02b34d761062c8a8f3e74b60`; Illuminate v3 `a4de0ec22d50c5070dbfa90969dc95c41be6f747955f60c8f9620baeafefbfa5`; v4 `1c3064d4ee5b9ea0f96055b03e50e8477d29ce6f2313c23c9dcfc83d314eecd8` |

## Contract queue

| ID | Producer | Consumers | Status | Standalone commit | Effect |
|---|---|---|---|---|---|
| `LANE-W6-W7-SPLIT` | integration | W6, W7, harness | released | `9cb483f` | Gives W6 and W7 independent branches and worktrees |
| `RESET-ERASED-RELEASE` | integration | pass proof, W6, validation | released | `373b0a9` | Reset treats erased ownership slots as no-ops; proof adaptation `8c2fff6`, W6 adaptation `afd7ab0`, and validation observation `3b82b0b` are landed |
| `W7-RESIDENT-ALLOCATOR` | W7 | W6, integration | released | `21f382c` | Zero-import allocator and styled package are generation-ready; allocator installation preserves the current 177-import `prettyM` frontier, and W6 owns the later bridge proof |
| `W7-CLOSURE-DESCRIPTORS` | W7 | W6, W7, integration, artifact clients | released | `40f41c0` | Retains the duplicate-free capture-kind table after `partialApply` imports are removed, so closure header `aux3` remains stable; W6 must rebase before W7 consumes it in the resident closure allocator |
| `W7-RESIDENT-LITERALS` | W7 | W6, integration, artifact clients | released | `64831f6` | Adds a zero-import literal fixture, internalizes immediate Naturals in linked `prettyM`, retains Strings until their JavaScript consumers become resident, and advances text/styled checkpoints to 152/153 imports |
| `FLOAT-SCALAR-RUNTIME` | integration/validation | pass proof, W6, W7, validation | released | landed stack through `8a8d1387` | Adds bit-exact `float32Bits`/`float64Bits`, heap-only boxes, stable box-kind/layout signatures, exact ABI adapters, and concrete/proof refinements without the unrelated closure-ownership stack. The integrated stack passes `make check` and all 3,123 Talos jobs. W7 consumes it in candidate `2b4d9d23`. |
| `WASM-FLOAT-REINTERPRET` | integration | W6, W7, Talos adapter | released | landed stack through `8a8d1387` | Symbolic, binary, Talos-adapter, runtime, and proof support for `i32.reinterpret_f32`, `i64.reinterpret_f64`, `f32.reinterpret_i32`, and `f64.reinterpret_i64` is landed. W7's integer-lane facade preserves signaling-NaN payloads across JavaScript without numeric coercion. |
| `ILLUMINATE-FLOAT-MACHINE` | integration | W7, W6 | released | `e39d0bbb` | Adds only the typed symbolic and binary Wasm operations needed to implement Lean 4.32 Float subtraction/division/multiplication/comparison, round-away-from-zero, saturating `toUInt64`, and Nat-to-Float conversion. W7 consumes the vocabulary in resident helpers; the later W6 bridge proves those helpers against the concrete runtime contracts. |
| `ILLUMINATE-NAT-MOD-MACHINE` | integration | W7, W6 | candidate | current `integration/closure-ownership` functional head | Adds unsigned i32 remainder for W7's checked immediate/one-limb `Nat.mod` helper, avoiding input-dependent linear subtraction on large timestamp jumps. |
| `BIT-EXACT-FLOAT-MANIFEST-TRANSPORT` | integration | W7, validation, artifact clients | released | contract `8ad80ad3`; canonical validation consumer `57f13122` | Defines the version-1 `wasm-reinterpret-i32-i64` capability, exact entry selection, integer-lane argument/result codecs, and semantic observation bridge. Floating manifests without the capability and capabilities with unknown fields, versions, encodings, entries, arities, kinds, or ranges fail closed. The standalone suite covers signed zero, infinities, quiet/signaling NaNs, maximal payloads, mixed signatures, and every malformed constructor path without JavaScript numeric coercion; the root validation runner now consumes the facade and passes the complete 613-case native/LCNF plus 581-case V8 gate. |
| `CLOSURE-APPLICATION-OWNERSHIP` | integration/validation | pass proof, W6, W7, validation | released | landed proof/runtime stack `229640de`; corrected contract `89fda41a`; proof `1640c7d4`; W6 `b28feab9`; ownership `528fdd1a`; W7 adapter `fd6a51e3` and ready head `fdaa8bd1` | Matches Lean's `lean_apply_*` boundary: an exclusive closure transfers fixed arguments and is freed non-recursively; a shared closure drops one reference and retains each fixed heap argument. Pass, concrete-runtime, and executable-adapter layers are green and linked/accepted. |
| `EXTERNAL-WAITING-RUNTIME` | integration/validation | pass proof, W6, validation | released | landed stack `229640de`; standalone repair `89fda41a`; proof `1640c7d4`; W6 `b28feab9`; historical validation provenance `2f301de5` | `Step.external`, `executeStep`, soundness, and the Talos frame refinement use the post-core-step `waiting.runtime`, so external responses cannot resurrect a consumed closure or discard shared closure decrements and retained captures. `FIR-BUG-impure-none-closure-application-external-runtime` is fixed with executable and proof regressions. |
| `SCALAR-CLOSURE-ABI-ADMISSION` | W6/shared lowering | W7, validation, integration | released | functional head `cf1ed73f`; ready head `4013a6ba`; bug card `FIR-BUG-wasm-none-generic-scalar-closure-admission` | A raw `tobject` parameter is refined to erased only after structural final-LCNF use analysis proves exact forwarding to a statically known erased parameter. UInt8 boxes use the precise tagged kind, justified by the concrete scalar-boxing theorem. Production lowering, supported lowering, closure dispatch, and the general compiler proof share this row. All 32 formerly fenced cases pass the three-edge probe; W7 and validation consume the landed boundary unchanged. |
| `WASM-DECLARATION-PARAMETER-UNIQUENESS` | integration/W6 proof | W6, W7, validation | released | queue/card `03547684`; isolated contract `dfa8153e`; bug card `FIR-BUG-wasm-none-duplicate-declaration-parameters` | Adds duplicate-free same-scope declaration parameters to `supportedDecl`. This aligns validator parameter kinds with the deduplicating symbolic-local row and prevents an accepted program from lowering to an invalid call signature. Existing well-formed generated programs are unaffected; consumers rebase after landing. |
| `WASM-DECLARATION-NAME-UNIQUENESS` | W6 proof | W6 compiler-correctness clients | released | isolated proof contract `b6030300`; functional proof `f215c995`; bug card `FIR-BUG-wasm-none-supported-export-declaration-name-uniqueness` | Retains the existing phase-level `Program.NamesUnique` fact at `ConcreteSupportedExport`, proving that source lookup, symbolic function selection, and adapter numeric lookup identify the same internal declaration. No lowering, validator, ABI, runtime, or interpreter behavior changes. |
| `CLOSURE-PROJECTION-KIND-REFINEMENT` | W6 proof/runtime | W6 compiler correctness, W7 resident projection, validation | released | functional head `625d4883`; ready mailbox `22d15cf3`; bug card `FIR-BUG-wasm-none-closure-projection-kind-refinement` | A closure retains its captured argument's precise descriptor kind, while generated callee entry may request the wider target-parameter kind. Live and post-application projection accept exactly `actualKind.refines expectedKind`, read at the actual descriptor kind, and preserve the physical lane while widening `PhysicalValueRel`. W7's resident helper already loads the same raw slot and requires no implementation change. |
| `WASM-LEAN-OBJECT-FAMILY-CALL-ABI` | W7/shared lowering | W6, W7, validation, artifact clients | released | isolated contract `bd7a5e55`; W7 consumer `a13fa2ad`; package ratchet `e5a8612b` | Follows Lean's generic call representation: `object`, `tagged`, and `tobject` are mutually compatible at named-call, result, and symbolic-stack boundaries, while scalar and erased lanes stay exact. Directional semantic/proof refinement and every concrete layout remain unchanged. W7 removes caller-name repairs and preserves captured `tobject` helper results; W6 rebases before proving the stable signatures. |
| `ARGUMENT-ALIAS-MATERIALIZATION` | integration/validation | W7, V8 adapter, W6 refinement | active | `181a098f` | Adds a canonical target-sorted root-to-later-argument alias graph to every corpus descriptor. LCNF allocates each root once and retains one owned reference per aliased argument; malformed, chained, non-heap, schema-mismatched, and datum-mismatched graphs fail closed. The V8 adapter requires one compiler-manifest heap location per root with exact initial multiplicity and tests reference counts two and three plus two independent roots. W7 should thread `argumentAliases` through compiler invocation only after its current slice, then admit the three queued alias fixtures; W6 owns any later concrete refinement, not this validation implementation. |
| `NATIVE-TERMINATION-SUPERVISION` | integration/validation | native adapter, LCNF adapter, W7/V8, Talos runners | active | `6fef4802`; divergence `6f0487ee`; typed policy `9e00c614`; source exit `8618f1f1` | Adds `timeoutMs` plus the backend-neutral `processTermination` enum: `protocol`, `timeoutDivergence`, or `sourceExit`. Native timeout is a typed backend timeout unless opted into divergence; ordinary nonzero status and signals remain crashes unless an exact source-exit fixture opts in, and signals always remain crashes. LCNF promotes only same-step, well-typed `Source.exitNat` terminal evidence under `sourceExit`, without changing the canonical interpreter result theorem. The divergence fixture pins 256 steps; source-exit fixtures pin statuses zero/seven and one exact external step. Retained V8 evidence excludes both. W7 or Talos should consume this policy only when admitting corresponding real-engine cases; no compiler-side work is requested now. |
| `EFFECTFUL-NATIVE-ORACLE` | integration/validation | native and direct-native adapters; future V8/Talos adapter authors | active | `b3f4f5d9` | Replaces `Case.native : Unit → ValidationDatum` with a delayed `Unit → IO ValidationDatum` action and makes semantic effect/stderr drains independent of a successful return value. Existing pure fixtures lift explicitly and the current 699 source plus 9 direct observations pass. This is the foundation for comparing true Lean `IO.Error` exceptions and source output; it changes no descriptor, compiler ABI, canonical interpreter theorem, or W6/W7 implementation surface. |
| `SOURCE-ENTRY-RESULT` | integration/validation | LCNF adapter, W7/V8 adapter, Talos runners | active | `dff585cc`; dependent fixtures `f99d2c6a` | Adds portable `entryKind = value | io` to corpus requests and descriptors. For `io`, the LCNF adapter appends exactly one erased `RealWorld` argument and decodes `EStateM.Result IO.Error α`; the native oracle runs the actual source action. The dependent fixtures compare a returned `IO Nat` and exact `IO.userError`, fixing `FIR-BUG-validation-none-io-entry-world-result`. W7 and Talos should consume the field only when admitting compiler-generated IO cases; no compiler work is requested before that boundary. |
| `LEAN-IO-ERROR-NORMALIZATION` | integration/validation | native and LCNF adapters; future W7/V8 and Talos adapters | active | `939b8144`; exhaustive implementation and fixtures `daaafbe7` | Normalizes every Lean `IO.Error` constructor to a stable kebab-case kind plus the exact Lean `IO.Error.toString` message. LCNF reconstructs all 19 constructor layouts, including optional filenames and scalar OS codes; unknown tags and malformed payloads fail closed. Nineteen exact constructor cases plus one post-failure-effect case pass against native. W7 and Talos consume this mapping only when compiler-generated IO cases are admitted; no compiler-side work is requested now. |
| `NATIVE-SOURCE-STREAM-CAPTURE` | integration/validation | native and LCNF adapters; future W7/V8 and Talos adapters | active | `57f3a7c5`; dependent fixtures `1762979a` | Captures genuine UTF-8 Lean stdout/stderr through write-only `IO.FS.Stream`s while retaining inherited process stderr for low-level panic backtraces. The native adapter requires exactly one nonempty JSONL protocol line and checks capture diagnostics; LCNF projects validation-owned output externals in execution order. Four exact fixtures cover ordered stdout, ordered stderr, effect-before-output, and output-before-IO-error, including Unicode and NUL. W7 and Talos should consume the observation fields only when their compiler-generated paths are ready; this queues no compiler-side work. |

## Update format

Send one record per lane update:

```text
lane:
owner:
branch:
base:
head:
status:
slice:
contract-impact: none | <short description>
checks:
bug-cards: none | <IDs>
handoff/follow-up:
```

For a resident helper, also include:

```text
helper:
signature:
contract-base:
artifact-digest:
bridge-state: generation-ready | contract-proved | linked/accepted
```

The board reports coordination state; it does not replace clean worktrees,
tested commits, or the handoff requirements in `AGENTS.md`.
