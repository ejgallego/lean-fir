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

- Milestone: `MULTI-LANE-CONSOLIDATION-20260814`.
- Integration owner: `wasm-gen`, resuming the integration lease for the
  lean-zip regeneration by explicit user assignment after W6 completed its
  serialized proof landing. The lease covers landing coordination only;
  feature ownership remains with each lane.
- Accepted baseline: `main` contains the complete
  `W7-ILLUMINATE-SELECTION-CATALOG-EXPORT` stack through tracked lane head
  `5081015a` and the independently isolated
  `TOOLING-FINAL-FUNCTION-INDEX-PROTOCOL` through `7d0d9b3b`, followed by the
  `S11-REPEATED-ARRAY-CHILD-FIDELITY` fixture stack through `5d673ad3` and its
  W7 concrete-product classification through `bccfc240`. The optional generic
  runtime-link function-evidence API is accepted at `52a98a6f`. W7-2's
  source-module replay repair and shared immutable publisher are accepted
  through `912bf68a`, and the Flat source identity is repinned to the published
  Verso 4.33 contract at `8199b6d7`. The resident linker's persistent planning
  view is accepted at `17d576fb`, followed by indexed resident dead-code
  reachability at `7b9d523a`. The lean-zip final-function sidecar package is
  accepted through tracked handoff `31035d5e` (functional head `752d2187`),
  followed by indexed final-LCNF capture ownership at `3dc7b0ee`. The bounded
  optimized-function tooling and its root fail-closed gate are accepted through
  `fa3105f7`, followed by the resident Array hot-path history at `372826cf`.
  W6 scalar-field layout admission and bit-exact Float32/Float field refinement
  are accepted through tracked proof handoff `3f038b71` (functional heads
  `e2249d03` and `cb04d7ee`). Cached recursive-owner persistence is accepted
  through functional fixture `a6543da1` and rebased tracked status `7b02b7d5`;
  the deterministic semantic-Wasm publication repair and closed regression are
  accepted through `d15e32d4`. The native cached Level-1 lean-zip generator is
  accepted at `4aa78f93`. W7's exact-source catalog, canonical immediate-Nat
  addition, reusable immediate-Nat dispatcher, and allocation-free immediate
  `Nat.mod` are accepted through tracked handoff `04003bd6` (functional heads
  `75b11c0c`, `fe586cec`, `6320a410`, and `8cb9cd82`).
  The complete scalar Wasm vocabulary is accepted at `43ab6619`, and W7's
  direct fixed-width/USize consumer is accepted through tracked handoff
  `e52ad4b3` (functional head `bda81d3a`). W7's direct Float/conversion
  consumer is accepted through tracked handoff `c3e0ba1a` (functional head
  `dc3d70af`); the remaining compiled math frontier is recorded explicitly.
  W7's faithful source-compiled `Float.ofNat` and `Float.ofScientific` closure
  is accepted through tracked handoff `da09b857` (functional head `ffbd7139`),
  including the isolated per-source-unit capture contract at `d1786ba4`.
  The Illuminate functional generation head is `4b84f35b`; the package itself
  remains local-only until its consumer authorizes publication. W7's genuine
  platform-libm frontier is closed through tracked handoff `8695a69c`
  (functional head `0c5dda71`) with a six-only provider and deterministic,
  zero-import linked acceptance module. W6's certificate-free resident Nat and
  proof-indexed Array-admission stack is accepted through tracked handoff
  `e1bd9722` (functional head `2231901a`): the actual adapted immediate
  `Nat.add` call chain now refines to the concrete host contract, while
  promoted naturals and the compiler-to-admission bridge remain explicit
  follow-ups. The canonical lean-zip raw consumer is regenerated on the v2
  libm surface through tracked handoff `78e5da9a` (functional head
  `7903b7f1`), with source-compiled Float construction, an exact one-function
  `Float.log2` symbolic frontier, and a zero-import final package. Its stored
  and Level-1 companions are republished from persistent FIR-local source
  views through tracked handoff `7a3163e5` (functional head `5e30208f`), with
  reviewed byte-only ratchets and unchanged semantic inventories. Illuminate's
  full-action and selection players are provider-free through tracked handoff
  `a45de4c9` (functional head `1b1668f1`): both source-compile upstream Float
  construction, start at the module's 1,024-byte heap base, and retain zero
  imports without the legacy standard-math provider. The HitScene-family
  consumers follow through tracked handoff `f42285d8` (functional head
  `3ba58f87`): both use exact module-wise source capture, link only their
  five-function platform-libm frontier through `fir.standard-libm/v2`, and
  finish with zero imports. The now-unreferenced `fir.standard-math/v1`
  provider is retired. W7's generic native-source-boundary repair follows
  through tracked handoff `b36d9d98` (functional head `65f4a57c`): postponed
  entry modules keep their exact final-LCNF groups, ordinary imported roots are
  final-pass captured separately, and the linked closure is reachability
  pruned. HitScene production now uses this repaired hybrid path. The Verso
  HTML clean-check dependency repair is accepted through tracked handoff
  `3767af90` (functional head `c4051bff`), so its native oracle no longer
  depends on a pre-existing `VersoSlides.Pretty` build product. W7's generic
  immediate-Nat decision dispatch is accepted through tracked handoff
  `9c0a73a5` (functional head `9dd5ea7a`): two canonical immediate words use
  direct equality/unsigned order, while promoted, heap-backed, persistent, and
  arbitrary-limb values retain the checked magnitude path. Lean-zip's closure
  inventories and ABI are unchanged; its exact-release profiles improve by
  27--31% with identical bytes and a flat frontier. W7's direct tagged-Nat to
  `USize` conversion follows through tracked handoff `80bb2dd1` (functional
  head `c12dba9c`): immediate inputs bypass generic validation, while the
  checked fallback now accepts arbitrary-limb Nats and preserves Lean's
  modulo-`2^64` semantics. Lean-zip improves by another 19--22% with identical
  bytes and a flat frontier. W7's immediate `Nat.mul` dispatch follows through
  tracked handoff `71203523` (functional head `0811a912`): two tagged payloads
  multiply exactly in Wasm `i64`, while promoted, mixed, arbitrary-limb, and
  malformed values retain the checked generic path. Lean-zip improves by a
  further 13--15%, with identical compressed bytes and a flat frontier. W7's
  direct tagged `Nat.sub` follows through tracked handoff `f21c97e6`
  (functional head `2e9040e0`): tagged-word order and arithmetic implement
  exact truncated subtraction without allocation, while all other inputs
  retain the checked arbitrary-precision walkers. Lean-zip improves by another
  24--26%, again with identical compressed bytes and a flat frontier.
- Landing order:
  1. W7-2's Verso source-module replay repair and generic immutable-package
     publisher are accepted in that order through `912bf68a`.
  2. The optimized final-function index protocol is accepted through clean
     isolated head `7d0d9b3b`, and bounded selected-function views plus the
     fail-closed root tooling gates are accepted through `fa3105f7`. CPU
     profiling, the compiled-Array probe, and the queued mailbox-protocol
     adaptation stay separately reviewable; the combined tooling history
     remains outside the integration queue. The independently reviewed Array
     hot-path history is accepted at `372826cf`.
  3. W7-1's lean-zip function-sidecar consumer is accepted through
     `31035d5e`. W7-2 may hand the validated exact-head Flat package to the
     Verso owner; the Illuminate selection export is also complete.
  4. The isolated persistent resident-linker planning view is accepted at
     `17d576fb`, and indexed resident dead-code reachability is accepted at
     `7b9d523a`. Indexed final-LCNF capture ownership is accepted at
     `3dc7b0ee`; later profiling/tooling surfaces remain separate slices.
  5. W6 scalar-field layout admission lands before the additive bit-exact
     Float32/Float field refinement, through tracked proof head `3f038b71`.
     Neither slice changes W7's generator contract.
  6. The cached recursive-owner fixtures land before the validation-provider
     cache repair and its cold complete artifact gate. The native Level-1
     driver then lands independently at `4aa78f93`. W7-1's immediate-Nat and
     catalog stack is accepted afterward through `04003bd6`; its executable
     helpers are generation-ready while W6 refinements remain separately
     queued in `W7-W6-20260814-007` and `W7-W6-20260814-008`. The complete core
     scalar Wasm vocabulary is accepted afterward at `43ab6619`;
     W7's direct fixed-width/USize resident-helper consumer is accepted through
     `e52ad4b3`, while W6 refinements remain separately tracked.
     W7's direct Float/conversion consumer follows at `c3e0ba1a`; it changes
     no helper signature or proof contract, so W6 refinement remains a
     separate queue item.
  7. W7's isolated source-unit capture API lands first at `d1786ba4`, followed
     by the source-compiled Float closure, deterministic artifact gate, and
     strict numeric-checkpoint selection through tracked handoff `da09b857`.
     W6 refinement of the additive resident Nat/Int operations remains
     independent; concrete layouts and helper ABI kinds are unchanged. The
     separately compiled six-function libm provider follows through tracked
     handoff `8695a69c`; it preserves the existing external names and binary64
     signatures, so no W6 adaptation is required for integration.
  8. W6's proof-only Array admission and resident Nat stack follows through
     tracked handoff `e1bd9722`. It consumes the landed W7 helper bodies and
     proves the actual adapted bounded `Nat.add` path without changing the
     shared ABI, concrete layout, helper signatures, or W7-owned sources.
  9. The lean-zip raw consumer then regenerates through tracked handoff
     `78e5da9a` after rebasing over the accepted W6 proof stack. The proof-only
     delta leaves its executable identities byte-identical.
  10. Lean-zip stored and Level-1 package ratchets follow through tracked
      handoff `7a3163e5`; persistent `.deps/source-views` replace all
      periodically cleaned source-view defaults without changing compilation
      semantics or ownership.
  11. Illuminate's full-action and selection consumers follow through tracked
      handoff `a45de4c9`. Their already-closed resident modules use generic
      fail-closed Binaryen cleanup directly; no C provider or 64 KiB runtime
      reservation remains.
  12. HitScene and SpatialHitScene follow through tracked handoff `f42285d8`.
      Their exact five-function opaque platform-libm frontiers link through
      the accepted standard-libm/v2 provider, after which the unused legacy
      standard-math/v1 provider is deleted.
  13. The generic source-boundary repair follows through tracked handoff
      `b36d9d98`. HitScene migrates from grouped imported dependencies to exact
      postponed entry-module replay plus individually captured ordinary roots;
      SpatialHitScene's multi-entry synthetic path remains unchanged pending a
      separate consumer review.
  14. The Verso HTML clean-check repair follows through tracked handoff
      `3767af90`; the package gate explicitly builds its declared source
      library before invoking the native oracle.
  15. W7's immediate-Nat equality/order dispatch follows through tracked
      handoff `9c0a73a5`. Its zero-import lean-zip package and exact function
      sidecar are generation-ready; W6 refinement remains independently queued
      in `W7-W6-20260820-001`, and the lean-zip lane retains Chrome/FIR-C
      performance acceptance.
  16. W7's tagged-Nat to `USize` dispatch follows through tracked handoff
      `80bb2dd1`. The helper signatures and layout are unchanged; W6 refinement
      remains independent, while the corrected arbitrary-limb fallback is
      guarded by the resident fixed-width real-engine fixture.
  17. W7's tagged/tagged `Nat.mul` dispatch follows through tracked handoff
      `71203523`. The helper signature, canonical Nat representation, and
      checked arbitrary-precision fallback are unchanged; W6 refinement is
      queued independently, while real-Wasm fixtures cover nonallocating and
      promoted tagged products, arbitrary limbs, ownership, and malformed
      operands.
  18. W7's tagged/tagged `Nat.sub` dispatch follows through tracked handoff
      `f21c97e6`. The helper signature, canonical Nat representation, and
      checked arbitrary-precision fallback are unchanged; W6 refinement is
      queued independently, while real-Wasm fixtures cover saturation at zero,
      tagged boundaries, no allocation, arbitrary limbs, stack safety, and
      malformed operands.
- Serialization rule: while the integration owner is validating one rebased
  candidate, other lanes may continue on their branches but do not
  fast-forward `main`. This prevents proof-only commits from repeatedly
  invalidating long deterministic package and external-engine gates.
- Not ready: W6 promoted/heap-backed `Nat.add`, the operation-specific
  `StateRelated` successor for full resident replacement, and the
  integration-owned compiler-to-Array-admission bridge remain open. Verso
  consumption of the local-only exact-head Flat package and
  its mailbox closure remain client-owned; no compatibility alias was added in
  FIR. The Array panic-observation fixture audit is accepted and parked behind
  the existing shared-observation bug card; it has no feature landing. Later
  tooling surfaces remain on their combined development branch until each has
  an independently authorized head. SpatialHitScene's multi-entry synthetic
  capture has not yet been assessed for the repaired hybrid API. W6 refinement
  of the newly accepted immediate-Nat decision branch remains open under
  `W7-W6-20260820-001`; proof adaptation for the accepted `USize.ofNat` body is
  also queued independently. Proof adaptation for the accepted immediate
  `Nat.mul` and `Nat.sub` bodies is queued separately as well. None blocks
  generation acceptance because no helper signature or shared layout changed.
- Publication boundary: local integration and the already-authorized `main`
  push only. No feature push, PR, external package publication, worktree
  removal, or branch deletion is implied by this lease.

## Latest completed integration lease

- Milestone: `W7-IMMEDIATE-NAT-SUB`.
- Integration owner: `wasm-gen`, accepting its own clean tracked handoff
  `f21c97e6`; the functional head is `2e9040e0` on `4fea3692`.
- Change: resident `Nat.sub` dispatches two canonical tagged Nats before its
  checked arbitrary-precision body. Tagged object words preserve unsigned
  payload order; subtracting them and restoring the tag computes the exact
  difference, while the underflow case returns tagged zero. The branch
  allocates nothing.
- Contracts: no Lean semantics, semantic Wasm ABI, helper signature, concrete
  representation, source entry, adapter API, ownership, or arena contract
  changed. Lean-zip remains 769 captured declarations, 139 externals, 630
  source functions, 2,782 pre-optimization helpers, and 2,305 final functions.
- Acceptance: exact-contract profile medians improve from 190.94/187.20 ms to
  141.08/142.32 ms, about 26%/24%. `Nat.sub` combined self samples fall about
  75% and magnitude-low samples about 98%, with identical compressed bytes and
  a flat frontier. The focused real-Wasm big-numeric fixture, deterministic
  package gate, five inputs across levels 1--10, `make check`, all 3,162 Talos
  jobs, and the complete W7 artifact gate pass.
- Artifact: clean package
  `.deps/evidence/lean-zip-numeric/natsub-clean-package` has package ID
  `2e9040e01ee4-273d0d6cd9ca-c3a99b3c7a6a4ef61fe1`; its 936,202-byte
  zero-import Wasm SHA-256 is
  `8aa5a302e328b1b60cc8a5d2f41998e831547d114022336ca3c64cbeb11711e6`,
  and its 999,568-byte sidecar SHA-256 is
  `a245a858c1297f90e7b584b47489361f5f7aec394c6380ecb7cbc9f24580d5ff`.
- Result: local `main` advances through `f21c97e6`. The package remains local
  for lean-zip acceptance; W6 proof adaptation is queued separately.

## Previous completed integration lease

- Milestone: `W7-IMMEDIATE-NAT-MUL`.
- Integration owner: `wasm-gen`, accepting its own clean tracked handoff
  `71203523`; the functional head is `0811a912` on `5c9449e9`.
- Change: resident `Nat.mul` dispatches two canonical tagged Nats through
  direct `i64.mul`, then uses the existing canonical natural constructor.
  Products that remain immediate allocate nothing; larger products promote,
  and every non-tagged or malformed input retains the checked generic path.
- Contracts: no Lean semantics, semantic Wasm ABI, helper signature, concrete
  representation, source entry, adapter API, ownership, or arena contract
  changed. Lean-zip remains 769 captured declarations, 139 externals, 630
  source functions, 2,782 pre-optimization helpers, and 2,305 final functions.
- Acceptance: exact-contract profile medians improve from 219.84/220.72 ms to
  190.94/187.20 ms. `Nat.mul` self samples fall from 901 to 57, about 94%,
  with identical compressed bytes and a flat frontier. The focused real-Wasm
  arithmetic fixture, deterministic package gate, five inputs across levels
  1--10, `make check`, all 3,162 Talos jobs, and the complete W7 artifact gate
  pass.
- Artifact: clean package
  `.deps/evidence/lean-zip-numeric/natmul-clean-package` has package ID
  `0811a9121bcb-273d0d6cd9ca-2a356c8efc03281f8e97`; its 936,147-byte
  zero-import Wasm SHA-256 is
  `4bba5f05b5559996624df992592f64ffe9b631e81621c9ffc9afaa9ef461de19`,
  and its 999,568-byte sidecar SHA-256 is
  `ca3a93079144b8e4fbff53a0503a6a89b4edd14fa4f20499083cba2ee8be37cf`.
- Result: local `main` advances through `71203523`. The package remains local
  for lean-zip acceptance; W6 proof adaptation is queued separately.

## Previous completed integration lease

- Milestone: `W7-IMMEDIATE-NAT-TO-USIZE`.
- Integration owner: `wasm-gen`, accepting its own clean tracked handoff
  `80bb2dd1`; the functional head is `c12dba9c` on `7637dd95`.
- Change: resident `USize.ofNat` and `USize.ofNatLT` decode canonical tagged
  Nats directly into the `i64` lane. Promoted and arbitrary-limb values take
  the checked `ResidentBigNumeric` path; the latter now reduce modulo `2^64`
  rather than trapping.
- Contracts: no Lean semantics, semantic Wasm ABI, helper signature, concrete
  representation, source entry, adapter API, ownership, or arena contract
  changed. Lean-zip remains 769 captured declarations, 139 externals, 630
  source functions, 2,782 pre-optimization helpers, and 2,305 final functions.
- Acceptance: exact-contract profile medians improve from 270.49/284.03 ms to
  219.84/220.72 ms. `USize.ofNat` self samples fall about 61%, with identical
  compressed bytes and a flat frontier. The immediate/promoted/arbitrary-limb
  real-Wasm fixture, deterministic package gate, five inputs across levels
  1--10, `make check`, all 3,162 Talos jobs, and the complete W7 artifact gate
  pass. Bug card `FIR-BUG-wasm-none-usize-ofnat-arbitrary-natural` is fixed.
- Artifact: clean package
  `.deps/evidence/lean-zip-numeric/usize-clean-package` has package ID
  `c12dba9c6197-273d0d6cd9ca-a2e10ca4130c28c1ac4b`; its 936,077-byte
  zero-import Wasm SHA-256 is
  `ba9eb0be837382a3586310ac40e4a9e6a1868605ac87db40986923ff3a247637`,
  and its 999,568-byte sidecar SHA-256 is
  `f1ac6dd38b8b068ddd85b1cdc52ba561c04a4524c9f2dde1e93647dc059d11b5`.
- Result: local `main` advances through `80bb2dd1`. The package remains local
  for lean-zip acceptance; W6 proof adaptation is queued separately.

## Previous completed integration lease

- Milestone: `W7-VERSO-HTML-CLEAN-CHECK`.
- Integration owner: `wasm-gen`, accepting its own clean tracked handoff
  `3767af90`; the functional head is `c4051bff` on `b2c81e94`.
- Change: the Verso HTML package gate now builds `VersoHtmlSource` together
  with `VersoFirHtml.Compile`, ensuring the later native oracle can import
  `VersoSlides.Pretty` without a warm checkout. Current generic runtime code
  changes only the complete linked byte count from 145,114 to 145,219; every
  semantic inventory count and ordered hash is unchanged.
- Contracts: no Lean semantic, semantic Wasm ABI, resident-helper signature,
  symbolic-module, W6 proof contract, source entry, adapter API, or ownership
  contract changed. The package remains zero-import with module-owned memory,
  five function exports plus memory, 74 source functions, 421 resident helpers,
  and 495 complete functions.
- Acceptance: a separate clean FIR worktree with persistent local scratch
  passed the source-library/compiler build, deterministic double publication,
  complete checksums, package smoke, eight native/Wasm HTML cases, bounded
  growth, 32 repeated calls, malformed annotation rejection, and the source
  package validator. `make check` reports 2,121/2,121 equal comparisons; all
  3,162 Talos jobs and the complete W7 artifact gate pass.
- Artifact: clean FIR producer `c4051bff` and clean Verso source
  `eb8d2b8fcf14` produce immutable package
  `integration/verso-html/_build/verso-html-packages/c4051bff324b-eb8d2b8fcf14-f9c47a3710629f0517e5`.
  Its 145,219-byte Wasm has SHA-256
  `78d38136fa6d8f9b236757b2e06820af8903c60622661a66f5219d52ae92a471`.
- Result: local `main` advances through `3767af90`; no external package is
  published. The next W7 milestone is the evidence-driven generic numeric
  investigation requested in `ROOT-FIR-20260820-001`.

## Previous completed integration lease

- Milestone: `W7-NATIVE-SOURCE-BOUNDARY-HITSCENE`.
- Integration owner: `wasm-gen`, accepting its own clean tracked handoff
  `b36d9d98`; the functional head is `65f4a57c` on `1b8a5a11`.
- Change: `compileEntryIndividuallyInternalized` now preserves the source units
  made available by Lean's final compiler pipeline. It replays a postponed
  public entry's exact module groups, compiles recursively discovered ordinary
  imported roots through fresh final-impure capture, and reachability-prunes
  the merged graph. HitScene production consumes the generic hybrid path. The
  postponed-source-view builder also supports deterministic rebuilds after
  Lean made prior interface artifacts read-only.
- Contracts: no Lean semantic, semantic Wasm ABI, resident-helper signature,
  symbolic-module, or W6 proof contract changed. HitScene retains its public
  production/diagnostic query API, bit-exact coordinates, module-owned memory,
  persistent checkpoint, copied results, scratch rewind, disposal, and exact
  `fir.standard-libm/v2` frontier.
- Acceptance: the positive individual HitScene probe records 313 reachable
  declarations, 53 reviewed externals, 261 base functions, zero unsupported
  declarations, successful admission, and successful lowering. The package
  passes all 301 fixture queries and 10,000 flat-frontier queries, deterministic
  repeat generation/link, and complete checksums. `make check` reports
  2,121/2,121 equal comparisons; all 3,162 Talos jobs and the complete W7
  artifact gate pass, including 704 native/LCNF/V8 cases, 44/44 concrete
  artifacts, and 15/15 source probes. All scratch remained in persistent
  worktree-local storage.
- Artifact: clean FIR producer `65f4a57c` and clean Illuminate source
  `88dcfee895a5` produce immutable package
  `integration/illuminate-hit-scene/_build/illuminate-hit-scene-8c890b70828ec3b2`.
  Its 64,217-byte zero-import module has SHA-256
  `0a59717fef0dafb2fac65e0cbc44c39b5116ab5bd30796be4b1853e1e25d7480`;
  package SHA-256 is
  `8c890b70828ec3b2e426251b2a7049ce00896d9d7cf17332bcfd33ce90ca28c5`.
- Result: local `main` advances through `b36d9d98`. Bug card
  `FIR-BUG-wasm-none-individual-hit-scene-generated-helper-admission` is fixed
  without an admission weakening or declaration-specific shim. No external
  package is published.

## Previous completed integration lease

- Milestone: `W7-ILLUMINATE-HIT-SCENE-STANDARD-LIBM`.
- Integration owner: `wasm-gen`, accepting its own clean tracked handoff
  `f42285d8`; the functional head is `3ba58f87` on `5b2ba581`.
- Change: HitScene now replays the exact postponed groups for its source entry
  module and internalizes ordinary imported modules through FIR's generic
  final-LCNF dependency capture. HitScene and SpatialHitScene link exactly
  `Float.acos`, `Float.cos`, `Float.cbrt`, `Float.sin`, and `Float.atan2`
  through `fir.standard-libm/v2`. The broad legacy `math-runtime.c` provider
  and `fir.standard-math/v1` capability are removed after the active-consumer
  scan reached zero.
- Contracts: no Lean semantic, semantic Wasm ABI, resident-helper signature,
  symbolic-module, or W6 proof contract changed. Public production and
  diagnostic query APIs, bit-exact coordinate transport, module-owned memory,
  persistent scene checkpoint, copied results, scratch rewind, and disposal
  remain unchanged.
- Acceptance: HitScene passes 301 fixture queries and 10,000 flat-frontier
  queries; SpatialHitScene passes 1,009 fixture queries and 10,000
  flat-frontier queries. Both publish byte-identically twice and verify their
  complete checksum sets. `make check` reports 2,121/2,121 equal comparisons;
  all 3,162 Talos jobs and the complete W7 artifact gate pass. All scratch
  storage stayed in the persistent worktree-local `.deps` tree.
- Artifacts: HitScene's 67,556-byte module has SHA-256
  `35f037a7eb65d9aa05ffaf79dfe1d9966a899333f08bd14b25c5d210727b25ef`
  and package SHA-256
  `57c165649b6d247dadcf03c626a54bc0b93efcb5c6f6685cbfa0cc2f86601722`.
  SpatialHitScene's 77,725-byte module has SHA-256
  `9b86dd2b380ff4841af0517b66ec9b34e0cf312863641ecdf073ca8e2021c2b0`
  and package SHA-256
  `f80f8fbb4c9789144824e61cf6a4707b46a8d25ffabf527a66813fc105e73120`.
  Both own memory and have zero function and memory imports.
- Result: local `main` advances through `f42285d8`. The confirmed individual
  capture ABI discrepancy is recorded in
  `FIR-BUG-wasm-none-individual-hit-scene-generated-helper-admission`; the
  production path has zero unsupported declarations. No external package is
  published.

## Previous completed integration lease

- Milestone: `W7-ILLUMINATE-PROVIDER-FREE-SOURCE-FLOAT`.
- Integration owner: `wasm-gen`, accepting its own clean tracked handoff
  `a45de4c9`; the functional head is `1b1668f1` on `54165c6a`.
- Change: the real Illuminate full-action and selection final-LCNF closures now
  compile upstream `Float.ofNat` and `Float.ofScientific` through FIR's generic
  source path. Their package generators optimize the already import-free
  resident modules directly and no longer build or link the bounded C provider.
  Adapters validate the exact 1,024-byte module heap base instead of advancing
  every fresh instance past a 65,536-byte provider reservation.
- Contracts: no Lean semantic, Wasm ABI, resident-helper, symbolic-module, or
  proof contract changed. Package-local ownership metadata advances to
  `persistent-checkpoint/v3` and `fir.closed-resident-runtime/v1`; public APIs,
  structured entries, exports, bit-exact Float transport, persistent
  checkpoints, copied outputs, and disposal remain unchanged.
- Acceptance: both packages publish byte-identically twice, all source and
  packaged smokes pass, all 107 legacy/full-action/selection traces agree, and
  both 10,000-call arena tests remain flat. `make check` reports 2,121/2,121
  equal comparisons; all 3,162 Talos jobs and the complete W7 artifact gate
  pass. No bug card was needed.
- Artifacts: the 37,287-byte full-action module has SHA-256
  `25e3f3ec476b7bb9cc650d89b3664c1a55880b44fde54576078278f5e2e87643`;
  the 40,398-byte selection module has SHA-256
  `9a5364ac0e4f78559f29089e9005820c9a9246850d1d19d04ba35671e997eefd`.
  Both own memory and have zero function and memory imports.
- Result: local `main` advances through `a45de4c9`. No external package is
  published. The next W7 consumer slice audits HitScene and SpatialHitScene,
  after which the legacy `fir.standard-math/v1` contract can be retired if no
  consumers remain.

## Previous completed integration lease

- Milestone: `W7-LEAN-ZIP-PERSISTENT-SOURCE-VIEWS`.
- Integration owner: `wasm-gen`, accepting its own clean tracked handoff
  `7a3163e5`; the functional head is `5e30208f` on `27de2d1f`.
- Change: lean-zip stored and Level-1 package setup now uses persistent,
  ignored, FIR-worktree-local `.deps/source-views` checkouts. Their exact final
  byte ratchets advance to the current deterministic outputs after the
  accepted scalar/runtime stack. The W7 roadmap now reflects the accepted
  Array, Nat, scalar, source-Float, and adapter milestones and current raw
  closure inventory.
- Contracts: none. Declaration, source-function, resident-helper, import,
  runtime-operation, ABI, cache-floor, scratch-rewind, and ownership
  inventories are unchanged.
- Acceptance: repeated generation, stored and Level-1 native/Wasm
  differentials, zero-import adapters, persistent-cache and scratch checks,
  package smokes, and six exporter tests pass. `make check` reports
  2,121/2,121 equal comparisons; all 3,162 Talos jobs and the complete W7
  artifact/concrete gate pass. No bug card was needed.
- Artifacts: the 12,779-byte stored module is SHA-256
  `9b9630dba3d5d04913b2e95647e8613596672bd1d3c4a7373a5c33ec32773e25`.
  The 331,043-byte Level-1 module is SHA-256
  `fcccdfaf024d78c35e37152a338a2ae75cf035d28390d274dd8a4497abb6d6b3`.
  Both own memory and have zero function and memory imports.
- Result: local `main` advances through `7a3163e5`. No feature branch or
  external package was published. The next W7 slice migrates Illuminate
  selection from `fir.standard-math/v1` to source-compiled Float.

## Previous completed integration lease

- Milestone: `W7-LEAN-ZIP-STANDARD-LIBM-V2`.
- Integration owner: `wasm-gen`, accepting its own clean tracked handoff
  `78e5da9a`; the functional head is `7903b7f1` on the accepted W6 proof
  baseline `a1a1f375`.
- Change: the canonical `Zip.Wasm.compressRaw` consumer now compiles Lean's
  real `Float.ofNat` and `Float.ofScientific` definitions from final LCNF and
  retains exactly `Float.log2` at its reviewed symbolic frontier. It links
  that frontier through `fir.standard-libm/v2`; the adapter and immutable
  package carry the corresponding reservation and numeric-policy capability.
- Contracts: no shared semantic contract changed. The raw input layout,
  public entry, module-memory ABI, allocator/frontier/rewind exports,
  persistent-cache plus scratch-checkpoint ownership, and package schema are
  unchanged. This is a consumer regeneration of already accepted W7 surfaces.
- Acceptance: the 157-job lean-zip/FIR cone and repeated generation pass. Five
  native/Wasm inputs at compression levels 1 through 10, independent inflate,
  the zero-import ByteArray adapter, persistent-cache/scratch reclamation,
  function evidence, checksums, and package smoke all pass. `make check`
  reports 2,121/2,121 equal comparisons with zero findings; all 3,148 Talos
  jobs and the complete deterministic W7 artifact gate pass. No bug card was
  needed.
- Artifact: clean producer `b9f6adb4` publishes immutable local package
  `integration/lean-zip/_build/lean-zip-raw-packages/b9f6adb4e6e0-273d0d6cd9ca-37190072c618e2a0e56f`,
  selected by `integration/lean-zip/_build/lean-zip-raw-current`. Its
  936,001-byte Wasm is SHA-256
  `b0eaf85bb2ae2691329a966e8c01a80b661799919291b32358368e147a2cff3d`;
  it owns memory and has zero function and memory imports. The final 2,305
  functions comprise 390 Lean-source and 1,915 resident-helper functions.
- Result: local `main` advances through `78e5da9a`. The package remains a local
  immutable handoff; no feature branch or package was published externally.
  The unrelated legacy stored-package byte-size ratchet remains a separate
  metadata review.

## Previous completed integration lease

- Milestone: `W6-RESIDENT-NAT-ARRAY-ADMISSION`.
- Integration owner: `wasm-proof`, taking over the active consolidation lease
  from `wasm-gen` by explicit user assignment and accepting its own clean W6
  tracked handoff `e1bd9722`; the functional head is `2231901a` and its base is
  the previous `main` at `f5cfd054`.
- Change: the concrete-runtime proof layer now factors the immediate-Nat scalar
  fragments, adapted-body/terminal-suffix bridge, scratch-memory retyping, and
  defined-function call composition. The actual generated `Nat.add` function
  composes the shared dispatcher, `naturalSum`, and `makeNatural` bodies and
  returns the exact canonical tagged result for bounded sums. Proof-indexed
  Nat/USize Array admission derives live layout bounds and reconstructs the
  selected semantic element.
- Contracts: none. No helper signature, semantic ABI, concrete layout,
  ownership rule, source semantics, compiler relation, or W7-owned source
  changed.
- Acceptance: fresh Lean Beam update/sync/save reported zero diagnostics; the
  focused 3,162-job Talos cone, `git diff --check`, complete `make check`,
  `make talos-setup`, and complete 3,162-job `make talos-check` all passed on
  the direct `f5cfd054` descendant. No new bug card was needed.
- Result: local `main` advances through `e1bd9722`. The integration backlog is
  clear: the W7 mailbox contains a live consumer request rather than a ready
  landing, and the other tracked lane branches contain no unlanded descendant
  of `main`. Promoted Nat arithmetic, full resident replacement, and compiler
  admission remain future proof work rather than pending integration.

## Previous completed integration lease

- Milestone: `W7-STANDARD-LIBM-FRONTIER`.
- Integration owner: `wasm-gen`, accepting its own clean tracked handoff
  `8695a69c` on `main`; the functional head is `0c5dda71`.
- Change: FIR now closes Lean's six genuine opaque Float externals through the
  same platform-libm boundary used upstream. A six-function-only Emscripten
  provider supplies `Float.sin`, `Float.cos`, `Float.acos`, `Float.atan2`,
  `Float.cbrt`, and `Float.log2`; the existing exact-name/signature linker
  internalizes it and retains only the caller's public exports. Core-Wasm
  Float helpers and source-compiled `Float.ofNat`/`Float.ofScientific` remain
  outside this provider.
- Contracts: no shared semantic contract changes. The additive
  `fir.standard-libm/v2` package capability records the existing six binary64
  signatures, the 65536-byte Emscripten low-memory reservation, and the
  platform-libm special-value/bounded-error policy. Legacy
  `fir.standard-math/v1` remains available for packages awaiting regeneration.
- Acceptance: Lean Beam reports zero diagnostics. The focused 93-job Lake
  cone, `git diff --check`, complete `make check` (704 source cases, nine direct
  machines, 2,121/2,121 comparisons), all 3,148 Talos jobs, and the complete
  deterministic resident/prettyM artifact gate pass. The libm gate checks
  exact signed-zero/infinity/domain behavior, NaN classification, binary64 bit
  transport, and a bounded finite-result comparison against an independent
  JavaScript libm. No bug card was needed.
- Artifact: the 486-byte frontier has exactly six `lean.extern` function
  imports. The 11,516-byte provider links to an 11,454-byte, module-memory,
  zero-import module at SHA-256
  `f5e516e1f237c3dd641317338e445844fc20c8cbefcc26f21deb501cb29cdd4f`.
  It exports six bit-lane probes plus memory and is byte-identical across
  repeated builds.
- Result: local `main` advances through `8695a69c`. No external package was
  published. Consumer packages may now regenerate, inspect their remaining
  import subset, select v2, and retire the heap-aware v1 compatibility runtime.

## Previous completed integration lease

- Milestone: `W7-SOURCE-FLOAT-CONSTRUCTION`.
- Integration owner: `wasm-gen`, accepting its own clean tracked handoff
  `da09b857` on `main` at `8952b76c`; the functional head is `ffbd7139`.
- Change: FIR now compiles Lean's real `Float.ofNat` and
  `Float.ofScientific` definitions from final LCNF and closes their full
  arbitrary-precision Nat/Int/BitVec model with resident helpers. Generic
  `Nat.shiftRight`, `Nat.lor`, fixed-width Natural conversion, `Int.negSucc`,
  `Int.neg`, and `Int.decLe` cover the exact reachable closure. Only the six
  genuine libm operations remain at the compiled math frontier.
- Shared contract: isolated commit `d1786ba4` adds
  `Source.compileEntryIndividuallyInternalized`. Imported roots compile in the
  same ordinary source-unit shape as upstream; a caller-owned specialization
  is regenerated with its generic companions through final capture. Existing
  capture APIs, semantic ABI, concrete layouts, arena ownership, and W6 proof
  contracts are unchanged.
- Acceptance: Lean Beam reports zero diagnostics on the final repair. The
  focused 115-job Lake cone, `git diff --check`, complete `make check` (704
  source cases, nine direct machines, 2,121/2,121 comparisons), all 3,148
  Talos jobs, and the complete deterministic resident/prettyM artifact gate
  pass. No bug card was needed.
- Artifact: the zero-import, module-memory source Float fixture is 71,419
  bytes at SHA-256
  `a7403b5326ad2ced4bb6524e1fd1dd718d987ab32d99183f98fee97939846d9d`.
  It captures 144 declarations, retains 113 source functions and 333 resident
  helpers, and checks fast/slow decimal paths, subnormals, overflow, malformed
  layouts, and arbitrary Naturals bit-exactly against a native Lean oracle.
- Result: local `main` advances through `da09b857`. The acceptance artifact is
  not an externally published package; interested consumers should regenerate
  their closed application to retire the version-1 C conversion frontier.

## Latest completed integration lease

- Milestone: `W7-DIRECT-FLOAT-SCALARS`.
- Integration owner: `wasm-gen`, accepting its own clean tracked handoff
  `c3e0ba1a` on `main` at `ba6b1c31`; the functional head is `dc3d70af`.
- Change: resident linking now consumes every standard Float/conversion
  external with an exact core-Wasm meaning: `UInt64.toFloat`, Float
  add/subtract/multiply/divide, negate, equality and ordering, absolute value,
  square root, and floor. Available linking emits only helpers selected by the
  source closure. `Float.round` retains the Lean-specific floor/ceiling
  implementation because Lean rounds halves away from zero while Wasm
  `f64.nearest` uses ties-to-even.
- Contracts: none. This consumes symbolic-Wasm contract `43ab6619` without
  changing source semantics, ABI kinds, concrete layouts, ownership,
  resident-helper signatures, or W6 proof obligations. The existing opaque
  math frontier is now partitioned canonically between exact scalar helpers
  and compiled-math helpers.
- Acceptance: Lean Beam sync/save is clean for both W7 modules and the nested
  artifact driver. `git diff --check`, complete `make check` (704 source cases,
  nine direct machines, the 704-case V8 triangle, and 2,121/2,121
  comparisons), all 3,148 Talos jobs, and the complete resident/prettyM
  artifact gate pass. The focused zero-import, module-memory Float artifact is
  5,673 bytes and checks all 15 helpers, including signed zero, NaN bits,
  saturation, half boundaries, scratch restoration, and immediate/heap Nat.
- Result: `Float.ofNat`, `Float.ofScientific`, `Float.sin`, `Float.cos`,
  `Float.acos`, `Float.atan2`, `Float.cbrt`, and `Float.log2` are the exact
  remaining compiled-math frontier. No external package was published and no
  bug card was needed.

## Previous completed integration lease

- Milestone: `W7-DIRECT-FIXED-WIDTH-SCALARS`.
- Integration owner: `wasm-gen`, accepting its own clean tracked handoff
  `e52ad4b3` on the released scalar-surface baseline `f3b24d80`; the functional
  head is `bda81d3a`.
- Change: fixed-width and USize resident helpers now use the released core Wasm
  comparison, arithmetic, bit, shift, CLZ, CTZ, multiply, and unsigned
  remainder operations. `UInt64.mod` and `USize.mod` retain an explicit
  zero-divisor branch so Lean's `n % 0 = n` semantics do not become Wasm's
  trapping `i64.rem_u` semantics. Structural guards reject reintroduced
  fixed-width/USize scalar loops.
- Contracts: none. This consumes symbolic-Wasm contract `43ab6619` without
  changing source semantics, ABI kinds, concrete layouts, ownership,
  resident-helper signatures, or W6 proof obligations.
- Acceptance: Lean Beam sync/save is clean. `git diff --check`, complete
  `make check` (704 source cases, nine direct machines, the 704-case V8
  triangle, and 2,121/2,121 comparisons), all 3,148 Talos jobs, and the full
  resident/prettyM artifact gate pass. The focused zero-import fixed-width
  module passes every export, edge cases, scratch restoration, and 1,000
  deterministic `UInt64.mod` differential cases.
- Result: the fixed-width artifact shrinks from 13,433 to 11,608 bytes
  (13.6%). Seven order-balanced V8 rounds show median improvements of 2.822x
  for `UInt64.mod`, 2.713x for `UInt64.mul`, and 1.103x for `UInt64.ctzFast`.
  No external package was published and no bug card was needed.

## Previous completed integration lease

- Milestone: `WASM-CORE-SCALAR-SURFACE`.
- Integration owner: `wasm-gen`, publishing the isolated shared contract from
  `integration/wasm-core-scalar-surface` at `43ab6619`, after queue commit
  `8484c0be`.
- Change: completes FIR's typed core scalar instruction vocabulary, binary
  encoding, validation, and Talos adaptation for the i32/i64 and f32/f64
  arithmetic, comparison, bit, conversion, and scalar-memory families. The
  executable fixture exports and invokes every one of the 163 scalar cases in
  a real JavaScript engine; it is a semantic gate rather than a byte-only
  encoder check.
- Contracts: the symbolic Wasm surface advances atomically. Table/reference
  calls, GC, exceptions, SIMD, atomics, and bulk memory remain explicitly
  separate Wasm subsystems. The semantic ABI, concrete runtime layouts,
  ownership rules, and resident-helper signatures are unchanged.
- Acceptance: Lean Beam sync/save reports zero diagnostics for every edited
  Lean module; `git diff --check`, complete `make check`, the 163-case Node
  scalar gate, all 3,154 Talos jobs, and the complete resident/prettyM artifact
  gate pass. No W6 proof adaptation or bug card was required.
- Result: W7 rebases before replacing hand-synthesized scalar loops with the
  released instructions. W6 may rebase without a proof or runtime change.

## Previous completed integration lease

- Milestone: `W7-IMMEDIATE-NAT-DISPATCH`.
- Integration owner: `wasm-gen`, accepting its own clean tracked handoff
  `04003bd6` on `main` at `dc550aa8`; functional heads are `75b11c0c` for
  immediate addition, `fe586cec` for the exact-source catalog producer,
  `6320a410` for package ratchets, and `8cb9cd82` for shared dispatch plus
  immediate remainder.
- Change: binary Nat helpers now share one canonical two-immediate tag test and
  payload decoder. `Nat.add` retains its prior immediate and arbitrary-
  precision bodies through that dispatcher. `Nat.mod` preserves `n % 0 = n`
  and otherwise uses unsigned remainder for two immediate operands, returning
  a canonical immediate without allocation; mixed and heap-backed operands
  retain the former checked arbitrary-precision path.
- Contracts: none. The semantic ABI, concrete Nat representation, ownership,
  resident-helper signatures, source semantics, and malformed-input boundary
  are unchanged. W6 refinement remains independently queued; integration
  records these helpers as generation-ready, not yet contract-proved.
- Acceptance: Lean Beam saves both edited modules with zero diagnostics. The
  focused zero-import artifact covers immediate zero/boundary/result-class/no-
  allocation cases, malformed heap traps, and arbitrary-precision values.
  Exact-source stored, Level-1, and raw package gates pass deterministic double
  generation, 5 inputs across 10 levels, independent inflate, function
  evidence, cache/scratch reclamation, and smoke. Complete `make check` passes
  704 source cases, nine direct machines, the 704-case V8 triangle, and
  2,121/2,121 comparisons; all 3,148 Talos jobs and the complete artifact gate
  pass.
- Artifacts: stored remains 12,794 bytes. Level-1 is 331,815 bytes at
  `0336448af3860aa8d7bdff9e29ad934e23cfcc44902cd8306bf5c209e3841aa2`.
  Raw is 902,526 bytes at
  `68d0f17dfd8641a458687d68972308a1af7766c04cea7834904f87b6f4064c70`,
  with zero imports and unchanged source/helper/function counts.
- Bug cards: none.
- Result: local `main` advances through `04003bd6`. W7 next audits the missing
  symbolic Wasm instruction surface before selecting another scalar slice.

## Latest completed integration lease

- Milestone: `W7-NATIVE-CACHED-LEVEL1-GENERATOR`.
- Integration owner: `wasm-gen`, accepting compiler-performance handoff
  `4aa78f93` directly on the deterministic-publication baseline `4d336565`.
- Change: lean-zip now persists the exact existing `captureLevel1` result in a
  project-local olean environment extension and invokes a native generator
  executable twice for package determinism. It retains the existing capture,
  lowering, resident-linking, encoding, adapter, and package contracts rather
  than creating a second compiler pipeline.
- Evidence: direct hot native runs take 1.40--1.43 seconds; package-internal
  generation takes 1.03--1.04 seconds, compared with the prior 21.75-second
  command path. The integration rerun completes both native generations in
  728 and 733 ms. The zero-import artifact remains 331,580 bytes at SHA-256
  `7801d626bff56fed22ac588de0775cce4f0322553d81eeec5bfba249b09d7ebe`,
  with 404 captured declarations, 108 reviewed externals, 296 retained source
  functions, 1,068 resident helpers, and 1,364 total functions.
- Contracts: none. This changes the integration-local compilation driver and
  closure ratchets only; source semantics, final-LCNF capture contents,
  semantic ABI, runtime/layout, ownership, resident-helper signatures, W6
  proofs, imports, and exports are unchanged.
- Acceptance: Lean Beam and the focused 214-job Lake cone pass. Native/Wasm
  stored and Level-1 differentials, adapter checks, scratch and persistent
  reclamation, two-run determinism, and immutable package smoke pass. The lane
  also reports clean `git diff --check`, complete `make check`, all 3,148 Talos
  jobs, and the complete W7 artifact gate passing.
- Bug cards: none.
- Result: local `main` advances through `4aa78f93`. W7-1 has rebased its
  independent resident Nat-add and catalog work on this compiler baseline.

## Latest completed integration lease

- Milestone: `S12-CACHED-RECURSIVE-PERSISTENCE-E3`.
- Integration owner: `wasm-gen`, accepting functional fixture `a6543da1`,
  tracked semantic handoff `4733a08e`, deterministic-publication repair
  `4d336565`, rebased final fixture status `7b02b7d5`, and bug-card closure
  `d15e32d4`.
- Change: two source cases retain a cached constructor owner and its recursive
  String/large-Nat child across a cache miss and hit, then distinguish skipped
  from taken child mutation. Semantic-Wasm provider commands bypass Lake's
  artifact cache because their command elaborator publishes external product
  files; ordinary FIR compilation retains the shared artifact cache.
- Contracts: none. The fixtures strengthen coverage of existing cache,
  persistence, and copy-on-write semantics. The provider repair changes only
  deterministic validation-product publication and weakens no file, checksum,
  semantic, runtime, or concrete-execution check.
- Acceptance: Lean Beam is clean. Complete `make check` passes 704 source
  cases, nine direct machines, 704 V8 triangles, and 2,121/2,121 comparisons;
  all 3,148 Talos jobs pass. One cold complete W7 artifact invocation passes
  both deterministic publication attempts. The concrete checker executes
  642/704 products, including both new cases, with the exact unchanged 62-case
  initial-ByteArray blocker inventory.
- Bug cards: `FIR-BUG-wasm-none-cached-heap-persistence` remains fixed and its
  regression is strengthened;
  `FIR-BUG-wasm-none-validation-product-cold-publication` is fixed and pinned
  by the provider-contract regression.
- Result: local `main` advances through `d15e32d4`; E3 may continue with an
  undominated cached-graph topology as a later independent fixture slice.

## Latest completed integration lease

- Milestone: `W6-SCALAR-FIELD-FLOAT-ADMISSION`.
- Integration owner: `wasm-gen`, rebasing the W6 stack directly on accepted
  `main` at `58a97c72` and accepting scalar-layout functional commit
  `e2249d03` followed by bit-exact Float32/Float functional commit `cb04d7ee`;
  tracked proof handoff is `3f038b71`.
- Change: structured validation now names the source-typing boundary needed for
  packed scalar field access. Concrete projection, mutation, heap, ownership,
  persistence, cache, resolver/compiler, simulation, and fault proofs now cover
  Float32 and Float using exact raw bits. Direct examples preserve Float32
  negative zero and a noncanonical Float NaN without host conversion.
- Contracts: none. This proves the already-landed raw-bit scalar, ABI, and
  packed-layout contracts and changes no source semantics, production
  validator, physical layout, symbolic instruction, resident-helper signature,
  emitted code, or W7 generation surface.
- Acceptance: Lean Beam passes the scalar-validation and downstream
  compiler/cache/simulation/fault cone with zero errors; the focused batch cone
  passes 3,124 jobs. `git diff --check`, complete `make check` (702 source
  cases, nine direct machines, the 702-case V8 triangle, 2,115/2,115 equal
  comparisons, zero findings), and all 3,148 Talos jobs pass.
- Bug cards: `FIR-BUG-wasm-none-float-runtime-gap` is fixed;
  `FIR-BUG-wasm-none-scalar-field-layout-admission` records the remaining
  production source-typing invariant rather than weakening admission.
- Result: local `main` advances through `3f038b71`. W7 may add generated
  raw-bit Float32/Float field fixtures without an ABI or runtime adaptation.

## Latest completed integration lease

- Milestone: `TOOLING-ARRAY-RUNTIME-HISTORY`.
- Integration owner: `wasm-gen`, rebasing the tooling owner's documentation
  commit `a227cd8d` as `372826cf` directly on the accepted bounded-function
  tooling baseline.
- Change: `docs/tooling/ARRAY_RUNTIME_HISTORY.md` separates element-addressing,
  Array-object validation, and proof-index validation costs, records the
  checked/public versus trusted compiled boundary, and explains why current
  lean-zip profiles point next to resident numeric work rather than Array.
- Contracts: none. This is source-backed architecture history only and changes
  no executable, proof, generator, runtime, package, or build surface.
- Acceptance: `git diff --check` and complete `make check` pass with 702 source
  cases, nine direct machines, the 702-case V8 triangle, 711 unique cases,
  2,115/2,115 equal comparisons, zero findings, and 25/25 mailbox tests.
- Result: local `main` advances through `372826cf`; the compiled Array
  microprobe remains a separate slice behind the accepted function-view API.

## Latest completed integration lease

- Milestone: `TOOLING-BOUNDED-FUNCTION-VIEW`.
- Integration owner: `wasm-gen`, applying tooling commits `b4787fa7` and
  `7be4b61e` in order as `402be2d1` and `633a2eec` on accepted `main` at
  `3957b08c`, then adding isolated root-build wiring at `fa3105f7`. The tooling
  owner's branch was not rewritten.
- Change: dependency-free parser/selector tests now run in ordinary root
  `check`; an explicit `tooling-check` target forwards `FIR_BINARYEN_DIR` and
  fails closed on missing tools, revision drift, skipped tests, or test
  failures. The new bounded `view` command extracts one final optimized
  function, resolves its imported and defined call targets through the release
  sidecar, classifies instruction/call families, and caps its WAT excerpt
  without rewriting or materializing the whole release module.
- Evidence: the dependency-free tier passes 7/7 tests. The missing-tool case
  rejects as required; pinned Binaryen `version 128
  (version_127-18-g2eb472cd6)` passes all 4/4 integration tests with zero
  skips. The reviewed lean-zip release view contains 22,297 instructions and
  926 resolved direct calls with no unattributed targets and unchanged release
  SHA-256. Complete root `make check` passes 125 harness tests, 702 source
  cases, nine direct machines, the 702-case V8 triangle, 711 unique cases,
  2,115/2,115 equal comparisons, 7,602 steps, 186 active bug cards, zero
  findings, and 25/25 mailbox tests.
- Contracts: none. This changes diagnostic tooling and build gates only; it
  does not change source semantics, generation, lowering, semantic ABI,
  runtime/layout, ownership, resident-helper signatures, packages, executable
  artifacts, or W6 proofs.
- Result: local `main` advances through `fa3105f7`. The integration branch and
  acceptance record remain local-only; no push, PR, package publication,
  branch deletion, or worktree removal is authorized by this lease.

## Latest completed integration lease

- Milestone: `W7-FINAL-LCNF-CAPTURE-INDEXING`.
- Integration owner: `wasm-gen`, accepting isolated commit `3dc7b0ee` after
  the lean-zip function-evidence package and its board correction at
  `ccd8304d`. The active W7 worktree had no overlapping `CompilerPrivate.lean`
  or `Source.lean` change at integration time.
- Change: generated-compiler cache reset now builds hash indexes for source
  roots and selected-module declarations, replacing nested membership scans
  while preserving the captured declaration and external inventories.
- Evidence: the measured Level-1 capture decreases from 18.504s in a 21.463s
  capture timeline to 2.977s in the final production sample; cache reset
  decreases from 18.504s to 1.574s. The complete production sample takes
  8.169s, including 2.344s lower/base encode, 2.317s link, and 0.531s final
  encode. The 331,580-byte linked Wasm remains byte-identical at SHA-256
  `d440dfc326cb62785cc909a5c58b04344046e179602b53114e70682358fd3d59`.
- Contracts: none. Source capture results, lowering, semantic ABI,
  runtime/layout, ownership, resident-helper signatures, W6 proofs, and linked
  artifact bytes are unchanged.
- Acceptance: Lean Beam, `git diff --check`, complete `make check`,
  `make talos-setup`, all 3,148 Talos jobs, and the complete
  artifact/browser/differential gate pass.
- Result: `main` advances through `3dc7b0ee` and is remotely reachable. W7-1
  rebases its next independent generation slice on this accepted baseline
  before handoff.

## Latest completed integration lease

- Milestone: `W7-LEAN-ZIP-FINAL-FUNCTION-EVIDENCE`.
- Integration owner: `wasm-gen`, consuming the clean `wasm/generation`
  handoff on accepted `main` at `652b482a`. The rebased functional head is
  `752d2187`; the tracked handoff is accepted through `31035d5e`.
- Package: `package-raw.mjs` produces and verifies
  `lean-zip-raw.wasm.functions.json` through the accepted evidence-preserving
  linker, requires evidence-enabled and ordinary release bytes to match, and
  binds the sidecar in BUILD v3, SHA256SUMS, the immutable package fingerprint,
  and package smoke. The adapter and Wasm runtime do not load the sidecar.
- Artifact identity: the complete zero-import module remains 902,411 bytes at
  SHA-256 `d3992d5b5e5a4bd11edb93f48e0b95fbc2148a1c0b7c87b395d208e4a61e44cc`.
  The 943,785-byte sidecar has SHA-256
  `0948c7497690ffaf61a6bc7f4a441846099e8c7d03c3a8d6cd00e98a694536ab`
  and indexes all 2,171 final functions: 354 Lean source, 1,811 resident
  helpers, and six explicit optimizer-or-linked-runtime functions. The exact
  immutable package is
  `integration/lean-zip/_build/lean-zip-raw-packages/752d2187b0cc-30737b4e2ebf-e1f5126677666dcf26b2`,
  generated at the functional head and selected by the canonical local pointer.
- Contracts: only the client-specific diagnostic package schema advances from
  `fir.lean-zip.raw.build/v2` to v3. Adapter API, input/output layout,
  ownership/reclamation, source semantics, semantic ABI, zero-import six-export
  module, runtime/layout, resident-helper signatures, W6 proofs, and executable
  Wasm identity are unchanged.
- Acceptance: two complete internal generations and repeated clean publication
  are byte-identical; function-sidecar verification, five inputs at every level
  1--10, native/Wasm byte equality, independent inflate, zero imports,
  persistent-cache ownership/rewind, and package smoke pass. Complete combined
  `make check` passes with 702 source cases, nine direct machines, 702 V8
  triangles, 711 unique cases, 2,115/2,115 equal comparisons, 7,602 steps,
  186 active bug cards, zero findings, and 25/25 mailbox tests. All 3,148 Talos
  jobs and the complete W7 artifact gate pass. One transient worktree-local
  `products.json` publication error did not reproduce in the immediate focused
  retry or subsequent complete gate and produced no semantic finding.
- Bug cards: none.
- Result: `main` fast-forwards through `31035d5e`; acceptance commit
  `ca6fe5d0` is remotely reachable under the active main-publication lease. The
  immutable package itself remains local-only. Fresh-output catalog publication
  and later performance work remain independent slices.

## Latest completed integration lease

- Milestone: `W7-RESIDENT-DEAD-CODE-INDEXING`.
- Integration owner: `wasm-gen`, accepting isolated commit `7b9d523a` on
  accepted `main` at `bd38983f` after confirming no overlap with the active
  lean-zip package files.
- Change: resident dead-code pruning now uses indexed function, import, and
  reachable sets plus indexed initializer remapping, replacing repeated linear
  membership and lookup scans.
- Evidence: the clean Level-1 pruning sample decreases from 642ms to 165ms;
  the full production sample completes in 22.883s with a 3.239s linker. The
  linked module remains byte-identical at 331,580 bytes and SHA-256
  `d440dfc326cb62785cc909a5c58b04344046e179602b53114e70682358fd3d59`.
- Contracts: none. Source semantics, semantic ABI, linked artifact identity,
  runtime/layout, ownership, resident-helper signatures, and W6 proof surfaces
  are unchanged.
- Acceptance: Lean Beam, `git diff --check`, complete `make check`,
  `make talos-setup`, all 3,148 Talos jobs, and the complete
  artifact/browser/differential gate pass.
- Result: `main` advances through `7b9d523a`; W7-1 rebases its independent
  lean-zip function-sidecar package before integration. The next capture
  profiling request remains unacknowledged and therefore outside this lease.

## Latest completed integration lease

- Milestone: `W7-RESIDENT-LINKER-PERSISTENT-PLAN`.
- Integration owner: `wasm-gen`, accepting isolated commit `17d576fb` on
  `main` at `07bb4961` after confirming no overlap with the active lean-zip
  package files or W7-2's Flat source pin.
- Change: contiguous non-materializing helper-family steps now share one
  persistent skeleton/probe planning view. Generated helpers remain
  materialized for later families, source bodies are rewritten once, and
  runtime operations are recollected once in final function order. This
  removes repeated header/probe reconstruction and suffix-plan composition.
- Evidence: alternating Level-1 measurements report linker time decreasing
  from 6.426s and 7.513s controls to 4.799s candidates. Control and candidate
  linked Wasm are byte-identical at 331,580 bytes and SHA-256
  `d440dfc326cb62785cc909a5c58b04344046e179602b53114e70682358fd3d59`.
- Contracts: none. Source semantics, semantic ABI, public linker output,
  runtime/layout, ownership, resident-helper signatures, and W6 proof surfaces
  are unchanged.
- Acceptance: Lean Beam, `git diff --check`, complete `make check`,
  `make talos-setup`, all 3,148 Talos jobs, and the complete
  artifact/browser/differential gate pass.
- Result: `main` advances through `17d576fb`; W7-1 rebases its independent
  lean-zip function-sidecar package before integration.

## Latest completed integration lease

- Milestone: `W7-VERSO-FLAT-4.33-SOURCE-PIN`.
- Integration owner: `wasm-gen`, consuming the clean one-commit W7-2 slice
  `8199b6d7` on accepted `main` at `f204a8b8`.
- Source identity: Flat now pins published Verso revision
  `eb8d2b8fcf145810996ad388d701e9337cfe1ceb`, reachable from
  `ejgallego/upgrade/fir-html-lean-4.33`, and exact `VersoSlides/Pretty.lean`
  SHA-256 `bf4271d690b523d5709d19331568c27f2dcb42b0d9ee253dbc30205a5a336c8e`.
  The input layout remains `lean-4.33-Std.Format.compact/v1`.
- Artifact: immutable package
  `integration/verso-flat/_build/verso-flat-packages/8199b6d7415b-eb8d2b8fcf14-1ceeef2286e5150490bc`
  contains the unchanged 121,192-byte Wasm module at SHA-256
  `06a7af99e5cd46ab394c7cf1686d470fbfe100416a1b8b315024067160d58cb2`.
  It retains 51 source functions, 345 resident helpers, zero imports, and the
  intended five function exports plus module-owned memory.
- Contracts: no compiler, semantic ABI, runtime, ownership, resident-helper,
  or W6 proof contract changed. Only the exact externally published source pin
  and digest changed; no compatibility alias or validator weakening was added.
- Acceptance: the complete Flat gate publishes twice with deterministic
  identity, verifies checksums and smoke, passes the corrected Verso source
  validator, nine native/Wasm cases, 1 MiB UTF-8, the 2,047-node balanced and
  256-break grouped stack shapes, 32 repeated calls, timing, and malformed
  input checks. `git diff --check`, complete `make check` (711 unique cases,
  2,115/2,115 equal comparisons, zero findings, 186 active bug cards, and
  25/25 mailbox tests), all 3,148 Talos jobs, and the complete W7 artifact gate
  also pass on exact head.
- Result: `main` fast-forwards through `8199b6d7`; the immutable package remains
  local-only for Verso acceptance.

## Latest completed integration lease

- Milestone: `W7-VERSO-MODULE-REPLAY-AND-IMMUTABLE-PUBLISHER`.
- Integration owner: `wasm-gen`, consuming the clean
  `wasm/package-verifier` handoff on accepted `main` at `f2dc8d0b`. The bug-card
  head is `122d85ac`, the semantic/generator head is `1e9faedf`, and the
  functional publisher head is `912bf68a`.
- Semantic repair: postponed source replay now preserves the source module's
  Lean specialization and SCC boundary before compiling unresolved prebuilt
  dependencies in a fresh unit. Ordinary Wasm plus FIR's direct-self loop
  lowering passes the Flat balanced 2,047-node and grouped 256-break stack
  shapes; the rejected generic `return_call` experiment is absent.
- Publication: Flat and HTML share a thin immutable-package utility with exact
  ordered checksum inventories, identity-collision rejection, atomic directory
  publication, and atomic current pointers. The semantic prefix is independent
  of this publisher.
- Contracts: none. Source semantics, the semantic Wasm ABI, concrete
  runtime/layout, ownership, resident-helper signatures, and W6 proofs are
  unchanged. The external Verso 4.33 validator remains source-owner work;
  previously validated packages remain client-test evidence until regenerated
  at this exact FIR head.
- Acceptance: `git diff --check`, Lean Beam refresh for the generator and both
  compile facades, five package-tool tests, Node syntax checks, and the focused
  source dependency cone pass. Complete `make check` passes with 702 source
  cases, nine direct machines, 702 V8 triangles, 711 unique cases,
  2,115/2,115 equal comparisons, 7,602 steps, 186 active bug cards, zero
  findings, and 25/25 mailbox tests. All 3,148 Talos jobs and the complete W7
  artifact gate pass on the exact rebased head, including deterministic
  prettyM publication, 640/702 admitted concrete products, and 44/44 concrete
  readiness artifacts.
- Bug card: `FIR-BUG-wasm-none-verso-flat-isolated-closure-stack-overflow` is
  fixed by the source-module replay boundary.
- Result: `main` fast-forwards through `912bf68a`. W7-1's lean-zip function
  sidecar and W7-2's exact-head Flat/HTML regeneration are now independent next
  slices.

## Latest completed integration lease

- Milestone: `WASM-RUNTIME-LINK-FUNCTION-EVIDENCE`.
- Integration owner: `wasm-gen`, publishing isolated shared-linker commit
  `52a98a6f` on accepted base `258f83d4` before its lean-zip package consumer.
- Interface: `integration/wasm-runtime/link-runtime.mjs` retains its unchanged
  three-argument default and optionally accepts paired `--function-inventory`
  and `--function-sidecar` arguments. The evidence path uses tooling's accepted
  prepare/restamp/optimize API across merge, meta-DCE, and the final optimizer;
  it rejects a missing half or unknown option and publishes the sidecar only
  after verification.
- Release invariant: the linker always produces the ordinary stripped module,
  independently produces the evidence-enabled stripped module, and requires
  exact byte equality before returning. Temporary identity names therefore
  cannot alter the application artifact.
- Real probe: the 1,570,637-byte lean-zip frontier plus standard math runtime
  reproduces the accepted 902,411-byte zero-import release at SHA-256
  `d3992d5b5e5a4bd11edb93f48e0b95fbc2148a1c0b7c87b395d208e4a61e44cc`.
  The validated sidecar indexes all 2,171 final functions: 354 surviving Lean
  source functions, 1,811 resident helpers, and six explicitly unattributed
  optimizer/linked-runtime functions.
- Contracts: this adds an optional shared linker API but changes no default
  output, semantic Wasm ABI, source semantics, concrete runtime/layout,
  ownership rule, resident-helper signature, package schema, or W6 theorem.
  W7 rebases before consuming it.
- Acceptance: `git diff --check` and Node syntax validation pass; the real
  zero-import link, final sidecar validation, and byte-identity check pass.
  Complete `make check` passes with 702 source cases across native/LCNF/V8,
  711 unique cases, 2,115 equal comparisons, zero findings, and 25/25 mailbox
  tests.
- Result: `main` advances through `52a98a6f`; W7 may checksum the sidecar as
  non-runtime immutable package evidence.

## Latest completed integration lease

- Milestone: `W7-S11-CONCRETE-BYTEARRAY-BOUNDARY`.
- Integration owner: `wasm-gen`, consuming its clean `wasm/generation`
  handoff based directly on accepted `main` at `6d835059`. The functional W7
  head is `931cd226`; the tracked ready handoff is `bccfc240`.
- Classification: `repeated-byte-array-child-array-set-shared` joins the exact
  concrete-product blocker inventory because its transferred initial graph
  contains a `ByteArray` shared by the outside field and both generic Array
  slots. The semantic native/LCNF/V8 fixture remains admitted and unchanged;
  no resident helper, external shim, fallback, or value-only fence was added.
- Contracts: none. The concrete product continues to execute supported initial
  runtime graphs and reject the existing initial-ByteArray layout boundary.
  Source semantics, fixture admission, validation protocol, interpreter,
  concrete runtime/layout, symbolic Wasm, ownership, resident signatures, and
  W6 proofs are unchanged.
- Acceptance: focused concrete execution passes with 640/702 products executed
  and exactly 62 initial-ByteArray-blocked. Complete `make check` passes with
  125 harness tests, 702 source cases, nine direct machines, 702 V8 triangles,
  2,115/2,115 equal comparisons, 7,602 steps, 185 bug cards, and zero findings.
  All 3,148 Talos jobs and the complete W7 artifact gate pass, including
  deterministic prettyM artifacts, the full 702-case V8/concrete gate, and
  44/44 concrete readiness artifacts.
- Result: `main` fast-forwards through `bccfc240`. The two exact validation-host
  external gaps and the separately parked panic-observation bridge remain
  follow-ups; this classification required no new bug card.

## Latest completed integration lease

- Milestone: `S11-REPEATED-ARRAY-CHILD-FIDELITY`.
- Integration owner: `wasm-gen`, consuming the clean `test-fixtures` handoff
  based directly on accepted `main` at `dbe40b79`. The functional fixture head
  is `13a8998f`; the tracked ready handoff is `5d673ad3`.
- Fixture: one runner-materialized input shares a `ByteArray` between an
  outside field and both slots of a generic Array. Source retains the original
  Array across `Array.set!`, mutates the outside child through `ByteArray.set!`,
  and returns the original Array, updated Array, and copied mutation. The exact
  24-transition LCNF/external path and nested-alias graph are pinned.
- Harness repair: the Python protocol mirror now descends through the `array`
  branch already present in protocol v3, retaining the shared `seq` datum
  representation. No wire shape, alias rule, source semantics, interpreter,
  runtime, generation, artifact, or proof contract changed.
- Acceptance: Lean Beam reports zero diagnostics. The focused native/LCNF/V8
  triangle passes 3/3 with the exact path and both products opened under
  strace. `git diff --check`, complete `make check` (125 harness tests, 702
  source cases, nine direct machines, 702 V8 triangles, 2,115/2,115 equal
  comparisons, 7,602 steps, 185 bug cards, and zero findings), and all 3,148
  Talos jobs pass.
- Bug cards: `FIR-BUG-validation-none-array-nested-alias-manifest` is fixed;
  `FIR-BUG-impure-none-array-mkempty-validation-external` and
  `FIR-BUG-impure-none-array-getinternal-validation-external` remain exact
  shared validation-host follow-ups. The separately parked S10 panic audit is
  not in this landing.
- Result: `main` fast-forwards through `5d673ad3`. W7 next adds only the narrow
  concrete-product blocker classification for the initial `ByteArray` graph.

## Latest completed integration lease

- Milestone: `TOOLING-FINAL-FUNCTION-INDEX-PROTOCOL`.
- Integration owner: `tooling`, explicitly authorized to consume its own clean
  isolated handoff for this slice. The branch
  `tooling/function-index-protocol` was based directly on `main` at `88d12da7`;
  its functional and handoff head is `7d0d9b3b`.
- Scope: release-hashed final-function capture, sidecar validation and
  inspection, plus Binaryen's import-aware final namespace (`fimport$N` for
  imports and import-excluding ordinals for definitions). Final call-graph
  edges resolve through that namespace while public selection remains in
  absolute Wasm index space. CPU profiling, selected-function views, the
  compiled-Array probe, mailbox adaptation, benchmark policy, W7 packages,
  compiler code, and runtime code are not part of this landing.
- Contracts: none. The slice adds artifact-local tooling and changes no FIR
  semantics, concrete runtime, resident-helper signature, symbolic Wasm, ABI,
  ownership rule, package contract, or coordination protocol.
- Acceptance: the imported/minified Binaryen suite passes 3/3 and proves that
  evidence-enabled and ordinary stripped output are byte-identical; sidecars
  bind the final artifact hash, exact import classification, body sizes, call
  edges, and exports. The existing 2,346,345-byte lean-zip production artifact
  with 27 function imports, 5,306 definitions, and 5,333 total final functions
  verifies successfully. The earlier 6,938/6,965 figures describe the complete
  pre-Binaryen linker inventory, not this optimized release namespace.
  `git diff --check` and complete `make check` pass with 125 harness tests,
  710 unique cases, 2,112/2,112 equal comparisons, zero findings, 182 active
  bug cards, and 25 mailbox tests.
- Result: `main` fast-forwards through `7d0d9b3b`. W7 may now consume the
  accepted sidecar protocol; the combined tooling branch remains unchanged and
  its later surfaces remain independently queued.

## Latest completed integration lease

- Milestone: `W7-ILLUMINATE-SELECTION-CATALOG-EXPORT`.
- Integration owner: `wasm-gen`, temporarily consuming its own clean
  `wasm/generation` handoff based directly on `main` at `300f8ab8`. The
  functional generation head is `4b84f35b`; the accepted lane-mailbox head is
  `5081015a`.
- Publication boundary: the executable generic command accepts one fresh
  caller-owned output and exact clean `producer` and `illuminate` checkouts.
  It rejects dependency packages, unknown or duplicate roles, dirty or wrong
  revisions, and existing or symbolic output; it verifies the exact six-file
  checksum inventory and runs package-local smoke before and after its atomic
  directory move.
- Artifact: the immutable selection package at
  `integration/illuminate-player/_build/illuminate-selection-player-packages/4b84f35bc327-6f16cdc3d432-d8aff69ccdf23c05db5d`
  contains a 35,370-byte complete module with SHA-256
  `22f295c5f249d1bd6e04e80bee10406f8e7d31a5bc7dcbec29131a7bb78896cd`,
  module-owned memory, zero function and memory imports, and the intended seven
  public functions plus memory. The exact caller-owned acceptance copy is
  `/tmp/fir-selection-export-4b84f35b`.
- Contracts: none. Adapter API v5 / hot-event v2, source inventories, ownership,
  scratch rewind, input layout, source semantics, concrete runtime, symbolic
  Wasm, and W6 theorem surfaces are unchanged. The v3 and selection complete
  modules merely ratchet the already-accepted proof-indexed resident Array
  helper bodies and now pin their full SHA-256 identities.
- Acceptance: focused exporter tests pass 6/6. Exact generic export passes
  deterministic two-pass v3 and selection publication, all six events, 10,000
  flat-frontier ticks, 107 legacy/v3/selection traces, checksums, and package
  smokes. `git diff --check`, complete `make check` (125 tests, 710 unique
  cases, 2,112/2,112 comparisons, zero findings, 182 active bug cards, and 25
  mailbox tests), all 3,148 Talos jobs, and the complete W7 artifact gate pass.
- Result: `main` fast-forwards through `5081015a`. Consumer notification names
  the exact accepted command and local-only package; W7-2 and tooling remain
  independent queued handoffs.

## Latest completed integration lease

- Milestone: `W6-OBJECT-FIELD-TYPING-ADMISSION`.
- Integration owner: `wasm-gen`, temporarily consuming the clean
  `wasm/talos-runtime` handoff based directly on `main` at `05ada0bd`. The
  functional proof head is `4bf39b80`; the accepted lane-mailbox head is
  `fe01cd1a`.
- Static admission: inversion of residual production validation supplies the
  ordinary object lane, the selected FVar payload lane or canonical erased
  lane, and the existing `isObjectField` classification.
- Dynamic admission: one successful source `.oset` step supplies the live
  constructor cell, semantic update, and exact slot bound. The new
  `ConcreteObjectFieldKindAligned` source-typing boundary supplies only the
  missing equality between the selected payload ABI kind and descriptor slot.
  Both FVar and erased current-step cases then use the existing concrete
  mutation admission without inspecting target execution or storing a
  translation certificate.
- Compiler discrepancy: production raw-LCNF validation does not yet establish
  descriptor-slot kind alignment. Bug card
  `FIR-BUG-wasm-none-object-field-kind-admission` is confirmed; this proof
  slice deliberately does not claim to fix the accepted compiler domain.
- Contracts: none. Source semantics, production validation, concrete
  layout/runtime, symbolic Wasm, semantic ABI, resident-helper signatures,
  emitted code, and W7 generation surfaces are unchanged.
- Acceptance: the focused proof cone passes 3,124 jobs. On the final base,
  `git diff --check`, complete `make check` (125 tests, 710 unique cases,
  2,112/2,112 comparisons, zero findings, 182 active bug cards, and 25 mailbox
  tests), and all 3,148 W6 Talos jobs pass.
- Result: `main` fast-forwards through `fe01cd1a` plus this acceptance record.
  Any production-validator or source-typing repair is a future isolated shared
  contract; packed scalar mutation remains dependent on
  `ScalarFieldMutationSafe` layout evidence.

## Latest completed integration lease

- Milestone: `W7-LEAN-ZIP-CACHE-ISOLATED-CLOSURE-RATCHET`.
- Integration owner: `root`, consuming the clean `wasm/generation` handoff
  rebased directly on `main` at `bebc9b53`. The functional generation head is
  `a2a1373f`; the accepted lane-mailbox head is `123c34e4`.
- Closure contract: the reviewed post-cache-isolation lean-zip closure contains
  662 captured declarations, 128 reviewed externals, 534 retained source
  functions, 2,598 resident helpers, and 3,132 complete functions. The package
  gate now pins SHA-256 identities for all four ordered inventories as well as
  their counts and Wasm sizes.
- Artifact: the immutable raw-compression package at
  `integration/lean-zip/_build/lean-zip-raw-packages/b3eefa8e3de3-30737b4e2ebf-9ff10a697177758c87ec`
  contains a 902,411-byte complete module with SHA-256
  `d3992d5b5e5a4bd11edb93f48e0b95fbc2148a1c0b7c87b395d208e4a61e44cc`,
  zero function imports, zero memory imports, module-owned memory, and all ten
  compression levels.
- Contracts: none. This hardens only the lean-zip integration's closure and
  immutable-package ratchet. Source semantics, production validation,
  concrete layout/runtime, symbolic Wasm, semantic ABI, resident-helper
  signatures, and W6 theorem surfaces are unchanged.
- Acceptance: `git diff --check`, complete `make check` (125 tests, 710 unique
  cases, 2,112/2,112 comparisons), all 3,148 Talos jobs, and the complete W7
  artifact gate pass on the final base. Exact-head package generation again
  passes repeated generation, five native/Wasm cases at ten levels,
  zero-import linking, cache/scratch rewind, checksums, and smoke. Bug card
  `FIR-BUG-wasm-none-lean-zip-raw-cache-isolation-ratchet` is fixed.
- Result: `main` fast-forwards through `123c34e4` plus this acceptance record.
  The stable W7 integration lease is released. W6 may now rebase its committed
  object-field typing-admission slice before the next proof handoff.

## Latest completed integration lease

- Milestone: `W6-VALIDATED-USIZE-FIELD-ADMISSION`.
- Integration owner: `root`, consuming the clean `wasm/talos-runtime`
  handoff based directly on `main` at `5ad696a9`. The functional proof head is
  `c56aa2ff`; the accepted lane-mailbox head is `6f4da03b`.
- Static admission: inversion of the real residual validator supplies the
  exact object-local and USize-local compiler guards for a current `.uset`
  node.
- Dynamic admission: one successful source update exposes the semantic heap
  reference, live constructor cell, USize field payload, and the exact
  absolute object-plus-USize slot bounds. These source facts assemble the
  existing `USizeFieldEffectSupported` premise without inspecting target
  execution or storing a translation certificate.
- Contracts: none. Source semantics, production validation, concrete
  layout/runtime, symbolic Wasm, semantic ABI, resident helper signatures,
  emitted code, and W7 artifacts are unchanged.
- Acceptance: Lean Beam update/sync/save reports zero diagnostics. The focused
  `FirTalos.ConcreteStructuredValidation` cone passes 3,124 jobs;
  `git diff --check`, complete `make check` (125 tests, 710 unique cases,
  2,112/2,112 comparisons, 25 mailbox tests), and all 3,148 W6 Talos jobs
  pass. No bug card was required.
- Result: `main` fast-forwards through `6f4da03b` plus this acceptance record.
  W6 next derives object-field descriptor alignment from retained source
  invariants, while packed scalar mutation remains explicitly dependent on
  `ScalarFieldMutationSafe` layout evidence.

## Latest completed integration lease

- Milestone: `W6-VALIDATED-CONSTRUCTOR-TAG-ADMISSION`.
- Integration owner: `root`, consuming the clean `wasm/talos-runtime`
  handoff based directly on `main` at `49b56a0d`. The functional proof head is
  `e8def3a8`; the accepted lane-mailbox head is `7f7e51fa`.
- Static admission: inversion of the real residual validator now supplies
  both `tag < UInt32.size` and the exact ordinary-object compiler local for a
  current `.setTag` node.
- Dynamic admission: one successful source step exposes the heap reference,
  live constructor cell, constructor payload, and semantic tag update. These
  source facts assemble the existing `ConstructorTagEffectSupported` premise
  without inspecting target execution or storing a translation certificate.
- Contracts: this proof consumes `WASM-SETTAG-UINT32-ADMISSION` at isolated
  commit `982ed402`; it adds no contract change. Source semantics, production
  validation, concrete layout/runtime, symbolic Wasm, semantic ABI, resident
  helper signatures, emitted code, and W7 artifacts are unchanged.
- Acceptance: Lean Beam update/sync/save reports zero diagnostics. The focused
  `FirTalos.ConcreteStructuredValidation` cone passes 3,124 jobs;
  `git diff --check`, complete `make check` (125 tests, 710 unique cases,
  2,112/2,112 comparisons), and all 3,148 W6 Talos jobs pass. Bug card
  `FIR-BUG-wasm-none-settag-uint32-admission` is fixed.
- Result: `main` fast-forwards through `7f7e51fa` plus this acceptance record.
  W6 next derives field-mutation admission and isolates only any genuinely
  missing source typing/layout premise.

## Latest completed integration lease

- Milestone: `WASM-SETTAG-UINT32-ADMISSION`.
- Integration owner: `root`, publishing the isolated shared-validator commit
  `982ed402` on base `7a52a8e0` before its W6 proof consumer.
- Admission boundary: production validation now requires every source
  `.setTag` value to satisfy `tag < UInt32.size`. This makes the unbounded
  source `Nat` agree exactly with the wasm32 constructor-header write instead
  of admitting values that `UInt32.ofNat` would silently wrap.
- Regression surface: `oversizedSetTagProgram` uses the first excluded value,
  `UInt32.size`, and is rejected both by `supportedProgram` and by
  `lowerSupported` with the declaration-local validation error. Existing
  compiler-generated programs are unaffected.
- Contracts: this narrows only the shared production-validation domain. It
  changes no source semantics, symbolic instruction, semantic ABI, concrete
  layout/runtime, resident-helper signature, emitted code, or artifact format.
  W6 derives the concrete tag-width premise from this accepted-source fact;
  W7 and validation rebase without implementation adaptation.
- Acceptance: Lean Beam reports zero diagnostics for both edited modules and
  the focused `Fir.Wasm.Examples` build passes. `git diff --check`, complete
  `make check` (125 tests, 710 unique cases, 2,112/2,112 comparisons), and all
  3,154 Talos jobs pass. Bug card
  `FIR-BUG-wasm-none-settag-uint32-admission` records the discovered mismatch.
- Result: `main` fast-forwards through `982ed402` plus this release record.
  W6 rebases and consumes the validator equation in the aligned current-step
  relation; W7 rebases before any dependent validator work.

## Latest completed integration lease

- Milestone: `W7-PROOF-INDEXED-RESIDENT-ARRAY-BOUNDS`.
- Integration owner: `root`, consuming the clean `wasm/generation` handoff
  rebased directly on `main` at `04413f79`. The functional generation head is
  `e9629e37`; the accepted mailbox head is `f93c49db`.
- Local Array principle: version-pinned, well-typed closed applications use
  Lean's trusted proof-indexed hot path. `getInternal`, `uget`, `get`, `set`,
  `uset`, and `swap` consume the resident representation invariant and their
  erased bounds proofs without revalidating headers or branching dynamically.
  Trusted Nat indices use the exact `lean_unbox` shift shape; trusted USize
  indices narrow directly. Public/raw helpers remain checked, and dynamic
  `get!`/`set!` retain their bounds and default-result behavior.
- Global semantic rule: FIR follows the exact upstream API/runtime behavior
  for the selected Lean toolchain at well-typed internal call sites. Foreign
  raw-memory boundaries may validate representation once, but internal
  generation does not add defensive checks or traps absent from upstream.
  General lower-level FIR bounds-fault semantics are unchanged. Ownership,
  uniqueness, copy-on-write, allocation, element release, and recursive
  release remain observable and unchanged.
- Regression surface: compile-time guards reject former bounds instruction
  sequences in trusted helpers and freeze direct Nat/USize decode shapes. A
  zero-import typed closed Array module exercises the trusted path. The real
  lean-zip closure retains 662 declarations, 128 reviewed externals, 2,598
  resident helpers, zero unsupported declarations, and zero runtime
  operations; five cases at ten compression levels match native Lean with
  flat cache/checkpoint frontiers.
- Acceptance: Lean Beam reports zero diagnostics and the focused Array cone
  passes. After the final rebase, `git diff --check`, complete `make check`
  (125 tests, 710 unique cases, 2,112/2,112 comparisons), all 3,148 Talos
  jobs, and the complete deterministic W7 artifact gate pass, including 701
  native/LCNF/V8 cases and the concrete readiness checks. A/B timings were
  noisy and the complete linked artifact grew, so no performance or size win
  is claimed.
- Follow-ups: `FIR-BUG-wasm-none-array-panic-observation` records the missing
  recoverable panic observation for dynamic out-of-bounds calls;
  `FIR-BUG-wasm-none-lean-zip-raw-cache-isolation-ratchet` records the stale
  exact closure ratchet and blocks only package publication. W6 refinement
  audits remain independent in `W7-W6-20260814-001` and
  `W7-W6-20260814-002`; generation acceptance does not claim those theorems.
- Result: `main` fast-forwards through `f93c49db`. W7 next reviews the
  post-G2 lean-zip closure inventory and publishes the zero-import package,
  while the dynamic panic-observation design stays a separate semantic slice.

## Latest completed integration lease

- Milestone: `W7-PRODUCTION-SELECTION-DISPATCH`.
- Integration owner: `root`, consuming the clean `wasm/generation` handoff
  rebased directly on `main` at `2b9d160e`. The functional generation head is
  `b4f24fbf`; the accepted mailbox head is `3702b5c3`.
- Adapter split: Illuminate selection-player adapter API v5 / hot-event v2
  makes `dispatchTick` the clock-free production path and exposes
  `dispatchTickTimed` for explicit timing and memory diagnostics. Both invoke
  the same bit-exact scalar Wasm entry, preserve checkpoint and poisoning
  behavior, and return equal copied selections. Production ticks perform no
  clock reads and return no timing or memory object.
- Source-compiler repair: regeneration exposed reuse of an imported
  `Option Nat` specialization owned by Lean's delaborator, which pulled an
  unrelated metaprogramming closure into the synthetic unit. FIR now preserves
  imported declaration mappings but clears imported specialization and
  closed-term caches for each isolated final-LCNF compiler unit, allowing
  Lean's ordinary pipeline to regenerate helpers under the selected caller.
  Noncomputable declarations are also rejected before source-root promotion.
  Bug card: `FIR-BUG-wasm-none-final-capture-imported-specialization-reuse`.
- Artifact: the clean handoff package contains 111 captured declarations, 81
  retained source functions, and 209 resident helpers. Complete Wasm is 35,240
  bytes with SHA-256
  `4f538ee895c3c730c1cd237d52d0d0f93101af758d732b3c1d0c161c50c97e83`,
  module-owned memory, zero imports, and seven function exports. The v3
  compatibility package remains zero-import and passes the same source gate.
- Acceptance: Lean Beam guided the Lean iterations; the final batch source
  cone passes. `git diff --check`, complete `make check`, all 3,148 Talos jobs,
  and the complete deterministic W7 artifact gate pass. The clean-head
  Illuminate gate passes exact closure assertions, repeat publication,
  checksums, package smokes, 10,000-event flat-frontier tests, and all 107
  legacy/v3/selection generic/scalar-tick traces. Eight order-balanced rounds
  per workload produce identical action digests and a consistent production
  median advantage; absolute sub-millisecond samples remain scheduler-noisy.
- Result: `main` fast-forwards through `3702b5c3`. W7 next republishes the
  immutable selection package from accepted `main`, notifies the Illuminate
  client of adapter API v5 / hot-event v2, then starts only G3's already-
  duplicated checksum-verifier and atomic-installer surface. Static
  simple-ground research remains parked.

## Latest completed integration lease

- Milestone: `W6-VALIDATED-LAZY-CACHE-PUBLICATION`.
- Integration owner: `root`, consuming the clean `wasm/talos-runtime`
  handoff based directly on `main` at `2e4cb265`. The functional proof head
  is `f9beb034`; the accepted mailbox head is `bdcc778a`.
- Validated administrative state: the branch-exact global relation now
  includes the existing concrete external-bind boundary, strengthened with
  validation of the pending caller continuation and exact agreement between
  its validated, production-supported, and hereditary resource tails.
- Publication coverage: a validated yielded lazy caller may carry arbitrary
  target-only case-label prefixes. After those labels unwind, one source
  cache-publication step matches the established seven-step Wasm protocol:
  the concrete host cache is updated, its value and initialized flag are
  published to the paired globals, and the source `.cache` marker is removed.
  The successor retains the same bind validation, caller ABI spine, resource
  budget, ownership, closure tables, and lazy-cache refinement.
- Contracts: none. This is a W6 proof-only extension over the unchanged
  source semantics, production lazy-cache/external-bind relation, concrete
  runtime and resource contracts, symbolic Wasm, and W7 generation surface.
- Acceptance: Lean Beam update/sync/save reports zero diagnostics; direct
  compilation of `FirTalos.ConcreteStructuredValidation` and `FirTalos`
  passes all 3,148 jobs. `git diff --check`, complete `make check` (125 tests,
  710 unique cases, 2,112/2,112 equal comparisons), and all 3,148 Talos jobs
  pass. No bug card was required.
- Result: `main` fast-forwards through `bdcc778a`. W6 next closes validated
  external-bind resumption into ordinary compiler code, then proves
  validator-derived current-step admission before assembling the universal
  one-step and finite-trace theorems.

## Latest completed integration lease

- Milestone: `W6-VALIDATED-YIELDED-BIND-RESUMPTION`.
- Integration owner: `root`, consuming the clean `wasm/talos-runtime`
  handoff rebased directly on `main` at `7e5f31f3`. The functional proof head
  is `8262bd21`; the accepted mailbox head is `6cfb6d8e`.
- Relation repair: the previous static/resource agreement and suspended
  validation proofs hid caller result ABIs independently. Their constructors
  built matching stacks, but proof irrelevance did not expose the equality
  needed when a yielded callee restored its caller. The strengthened W6
  relation carries a branch-exact caller-ABI spine as a non-proof index and
  preserves that alignment through every existing active, ready, entry,
  case-label, and returned transition.
- Resumption coverage: a yielded direct call now takes the exact two target
  steps and re-enters its validated caller continuation. Saturated calls do
  the same after the exact matcher-count-plus-five target path. Arbitrary
  target-only case-label prefixes unwind first without changing the source
  caller or its validation. Lazy cache-marker publication remains a separate
  administrative branch rather than being weakened into this theorem.
- Contracts: none. This is a proof-only strengthening over unchanged source
  validation, concrete runtime/resource, compiler, symbolic Wasm, and W7
  generation contracts.
- Acceptance: Lean Beam update/sync/save reports zero diagnostics; direct
  compilation of `FirTalos.ConcreteStructuredValidation` and `FirTalos`
  passes all 3,148 jobs. After rebasing, `git diff --check`, the same direct
  build, complete `make check` (125 tests, 710 unique cases, 2,112/2,112 equal
  comparisons), and all 3,148 Talos jobs pass. No bug card was required.
- Result: `main` fast-forwards through `6cfb6d8e`. W6 next proves validated
  lazy-cache publication and external-bind resumption, then closes
  validator-derived current-step admission before assembling the universal
  one-step and finite-trace theorems.

## Latest completed integration lease

- Milestone: `W7-TRUSTED-RESIDENT-ARRAY-HOT-CALLS`.
- Integration owner: `root`, consuming the clean `wasm/generation` handoff
  rebased directly on `main` at `0172e5ea`. The functional runtime head is
  `da721bc3`; the accepted mailbox head is `15a43513`.
- Runtime split: standalone and raw/public Array helpers retain the complete
  address/header validator and malformed-address traps. Typed closed
  applications select explicitly trusted helpers that consume the accepted
  resident Array representation invariant. Lean guards prove that each
  trusted body is exactly its checked counterpart after removing the common
  validator prefix; bounds, reference counting, uniqueness, copy-on-write,
  allocation, and recursive release remain byte-identical.
- Linker boundary: checked strict/available policies remain available, while
  the closed-application family alone selects trusted available Array calls.
  The policy rejects mixed checked/trusted Array modes. No semantic operation,
  concrete layout, symbolic-Wasm instruction, ownership rule, helper
  signature, or application ABI changed.
- Evidence: malformed raw Array input still traps. The exact zero-import
  lean-zip levels 1--10 package, native output, independent inflate,
  persistent/scratch ownership, repeat generation, and order-balanced scaling
  probes pass with identical digests and flat frontiers. Four-KiB inputs were
  neutral; paired raw-entry medians improved about 2.6% at 64 KiB and 1.9% at
  256 KiB. Resident frontier shrank by 2,276 bytes, while complete linked Wasm
  grew by 6,263 bytes, so this is not recorded as a binary-size win.
- Acceptance: Lean Beam sync/save reports zero diagnostics; the focused linker
  cone, `git diff --check`, complete `make check` (125 tests, 710 unique cases,
  2,112/2,112 equal comparisons), all 3,148 Talos jobs, and the complete
  deterministic W7 artifact gate pass. No bug card was required.
- Result: `main` fast-forwards through `15a43513`. The independent W6
  theorem-side audit of the trusted representation premise remains in mailbox
  thread `W7-W6-20260814-001`; generation acceptance neither claims nor
  changes that refinement theorem. W7 next republishes lean-zip from accepted
  `main`, then resumes the production/diagnostic adapter split.

## Latest completed integration lease

- Milestone: `W6-VALIDATED-STRUCTURED-CONTROL`.
- Integration owner: `root`, consuming the clean `wasm/talos-runtime`
  handoff based directly on `main` at `85481c67`. The functional proof head is
  `d11bab61`; the accepted mailbox head is `20692b18`.
- Closed validation relation: active generated code retains the executable
  source validator's residual join/local/case/sharing state, while every
  suspended caller retains validation of its exact continuation. The relation
  strengthens the production compiler/resource relation without storing a
  future source step, target path, termination witness, or translation
  certificate.
- Local control coverage: direct lets, persistent and ordinary ownership,
  deletion, constructor tags, object/erased/USize/scalar field mutation, and
  default/object/UInt8 case selection preserve the closed relation. Case
  selection follows the exact constructor or default arm chosen by the source
  interpreter and tracks the corresponding guarded-join fact update.
- Recursive calls and results: direct named calls and saturated closure calls
  retain validated caller continuations across staging, reconstruct root
  validation from the selected generated callee declaration on entry, and
  preserve validation beneath the exact call/matcher-label stack. Validated
  returns now reach a closed yielded state carrying the suspended validation
  stack required for resumption.
- Contracts: none. This is a W6 proof-only strengthening over the accepted
  validator, generated-row, concrete runtime/resource, symbolic Wasm, and W7
  closure allocator surfaces.
- Acceptance: Lean Beam update/sync/save reports zero errors; direct batch
  compilation of `FirTalos.ConcreteStructuredValidation` and its `FirTalos`
  importer passes all 3,148 jobs. `git diff --check`, complete `make check`
  (125 tests, 710 unique cases, 2,112/2,112 equal comparisons), and all 3,148
  Talos jobs pass. No new bug card was required.
- Result: `main` fast-forwards through the clean W6 mailbox. W6 next proves
  validated pop/resumption for yielded direct and saturated callers, then
  covers lazy/external administrative branches and closes validator-derived
  current-step admission before assembling the universal one-step and
  finite-trace theorems.

## Latest completed integration lease

- Milestone: `W7-CONSOLIDATED-RESIDENT-CLOSURE-ALLOCATORS`.
- Integration owner: `root`, consuming the clean W7-2 stack on
  `wasm/closure-allocation-consolidation`. The stack is based directly on
  `main` at `3fee77f6` and lands through tested head `10dca27f`.
- Runtime generation: the 3,131 lean-zip `partialApply` operations now share
  569 resident allocator helpers by typed capture/result shape. Each call site
  supplies stable target ID and arity; descriptor, fixed count, closure layout,
  and ownership remain unchanged. Lean-zip complete functions fall from 5,839
  to 3,277 and helpers from 5,265 to 2,703. Complete zero-import Wasm falls
  from 1,753,310 to 1,622,609 bytes; styled prettyM falls from 143,042 to
  119,843 bytes with byte-identical behavior and neutral runtime measurements.
- Generic linker cleanup: the rewrite planner now records any `CallTarget` to
  an instruction sequence, composes expanding rewrites in policy order, and
  retains runtime operations introduced directly by replacement sequences.
  A guard proves planned allocator/partial-application linking emits exactly
  the same bytes as the materialized diagnostic path. The obsolete public
  single-operation helper builder and retired float-capture error variant are
  removed; live closure documentation and diagnostics match current support.
- Acceptance: Lean Beam sync/save reports zero diagnostics. The focused
  resident closure fixture, deterministic raw lean-zip levels 1 through 10
  package, native/Wasm differential, independent inflate, and scratch/cache
  reclamation gates pass. `git diff --check`, complete `make check` (125
  harness tests, 701 native/LCNF/V8 source cases, 9 direct-machine cases,
  2,112/2,112 aggregate comparisons), all 3,148 Talos jobs, and the complete
  deterministic W7 artifact gate pass. No new bug card was required.
- Result: `main` fast-forwards through `10dca27f`. The primary W7 Array
  hot-path audit may rebase on this accepted head. W6's semantic partialApply
  and concrete closure-layout proofs are unchanged; future direct emitted
  helper proofs consume the new private shape-shared helper ABI.

## Latest completed integration lease

- Milestone: `W6-SHARED-RESIDENT-ARRAY-COPY-REFINEMENT`.
- Integration owner: `root`, consuming the clean `wasm/talos-runtime`
  handoff based on accepted generic-Array main `515bf401`. The functional
  proof head is `0b3f466c`; the accepted mailbox head is `e8800c2c`.
- Shared push: W6 retains the complete old live prefix in semantic/concrete
  order, allocates and relates a fresh Array, transfers the pushed argument
  without retaining it, publishes the pushed Array, and only then consumes
  one reference to the old shared or persistent Array.
- Shared pop: W6 retains and publishes exactly `elements.pop`, including the
  uniform empty case, before consuming one source reference. Consequently the
  removed last element receives no compensating retain and spare capacity
  never becomes semantic ownership.
- Refinement frame: both paths extend the allocation witness, preserve closure
  allocations and every pre-existing physical allocation extent, expose the
  exact fresh semantic reference and source/fresh address distinction, retain
  complete live-heap refinement through the final decrement, and preserve the
  post-allocation heap frontier exactly.
- Contracts: none. The stack consumes the accepted
  `HeapObject.array elements capacity` and resident `ARRY` layout contracts;
  it changes no shared semantics, emitted-helper signature, compiler,
  symbolic-Wasm, or W7 generation surface.
- Acceptance: Lean Beam update/sync/save and direct root/Talos compilation of
  `Fir.Wasm.Concrete.ArrayCopyCorrectness` pass. `git diff --check`, complete
  `make check` (125 tests), `make talos-setup`, and all 3,148 Talos jobs pass.
  No bug card was required.
- Result: `main` fast-forwards through the clean W6 mailbox. W6 next connects
  the complete resident copy-path contracts to compiler-facing finite-trace
  current-step admission when emitted Array calls enter that structured proof
  surface. Active-data-segment initialization remains conditional on a
  nonempty segment entering W6's proof model.

## Latest completed integration lease

- Milestone: `VALIDATION-GENERIC-ARRAY`.
- Integration owner: `root`, assembling the isolated shared contract and its
  W7, W6, and pass-proof consumers on `integration/generic-array`. The
  canonical contract commit is `71471a5d`; the accepted functional head is
  `2f6fc869`.
- Shared semantics: `HeapObject.array elements capacity` owns exactly its live
  element prefix, while spare capacity remains representation state. The
  validation schema gains a physical `.array element` form distinct from
  `.seq`/List, and the Wasm boundary maps it to the existing resident
  `opaque/ARRY/size/capacity/tobject-slots` layout. Oracle observations expose
  both live elements and physical capacity without making capacity semantic.
- Proof adaptation: the pass relation covers Array ownership and explicitly
  rejects Arrays at constructor-only and closure-only operations. W6 relates
  semantic Arrays to the concrete resident layout and proves allocation,
  reads, replacement, swap, size transitions, unique push/pop, recursive
  release and release faults, reset/reuse framing, and the required impossible
  non-scalar/non-constructor cases.
- Acceptance: Lean Beam reports zero diagnostics for the edited pass and fault
  proofs. `git diff --check`, complete `make check`, all 3,147 Talos jobs, and
  the deterministic artifact gate pass. The root gate covers 125 harness
  tests, 701 source cases, 9 direct-machine cases, 710 unique cases, and
  2,112/2,112 equal comparisons. The artifact gate covers all 701 validation
  cases, 44/44 concrete artifacts, resident-helper checks, and two byte-exact
  package builds.
- Result: the generic Array contract and all current proof/runtime/generation
  consumers are linked/accepted. No bug card was required. W6 next continues
  shared/persistent allocation-and-copy refinement for Array push/pop; W7 may
  continue its independent resident-runtime work after checkpointing and
  rebasing its in-progress worktree.

## Latest completed integration lease

- Milestone: `WASM-ACTIVE-DATA-SEGMENTS`.
- Integration owner: `root`. The standalone shared-contract commit
  `c8770e42` extends the symbolic Wasm module and binary emitter with ordered,
  active memory-zero data segments carrying a constant wasm32 offset and raw
  bytes.
- Validation and compatibility: a module without memory cannot contain a data
  segment, and every segment must fit its declared initial memory. The field
  defaults to empty, so existing producers, artifacts, and proof-side modules
  retain their previous bytes and behavior.
- Acceptance: Lean Beam reports zero diagnostics for the changed Lean cone.
  The real-engine regression observes the exact initialized bytes. `git diff
  --check`, complete `make check`, `make talos-setup`, all 3,144 Talos jobs,
  and the complete deterministic artifact gate pass. The root gate covers 125
  harness tests, 676 native/LCNF/V8 cases, 9 direct-machine cases, 685 unique
  cases, and 2,037/2,037 equal comparisons.
- Consumers: W7 rebases before implementing fail-closed materialization of
  eligible immutable closed compiler constants into module-owned persistent
  memory. W6 needs a separate initialization/refinement theorem when a
  nonempty data-segment module enters its proof surface; no current W6 theorem
  or artifact changed.

## Latest completed integration lease

- Milestone: `W7-CONSTANT-TIME-RESIDENT-ARRAY-INDEXING`.
- Integration owner: `root`, consuming the wasm-gen slice on
  `wasm/generation`. It is based directly on accepted `main` at `7ee984fb`,
  with functional head `1d79658d` and clean ready mailbox `9284f4ce`.
- Generic runtime repair: resident Array reads, sets, and swaps now compute
  `array + headerBytes + index * 8` in constant time instead of advancing an
  eight-byte cursor `index` times. A Lean guard freezes the accepted W6
  object-lane width. Ownership, bounds/default behavior, unique reuse, shared
  copy-on-write, recursive release, helper signatures, and public ABI are
  unchanged.
- Performance evidence: on the characterized 1 KiB structured level-6 raw
  workload, cold execution fell from 917.5 ms to 195.6 ms; warm samples fell
  from 30.0/28.6/27.6 ms to 11.7/8.9/7.3 ms. Persistent and scratch frontier
  growth are byte-identical. The raw complete module shrank by 217 bytes,
  Level-1 by 177 bytes, and the stored control by 16 bytes without changing
  declaration, source-function, or helper inventories.
- Packages: the refreshed stored, Level-1, and raw levels 1 through 10 modules
  are zero-import and module-owned. Raw is 1,753,310 bytes with SHA-256
  `0686e69684c187b1b14415f0f3b88fe4ce28514c97f8aac003fbd7359f15b838`;
  Level-1 is 508,531 bytes with SHA-256
  `cec08523e4abf4b9555db565952903b5b693c3a1af7ef698117a2ebefc4230de`.
- Acceptance: Lean Beam reports zero diagnostics and a saved source hash of
  `45ae8eb173783ec9`. The standalone resident Array artifact, deterministic
  package emission, native/Wasm and independent-inflate checks, cache/scratch
  ownership checks, `git diff --check`, complete `make check`, all 3,144 Talos
  jobs, and the full deterministic artifact gate pass. The root gate covers
  125 harness tests, 676 source cases, 9 direct-machine cases, 685 unique cases,
  and 2,037/2,037 equal comparisons.
- Result: `main` accepts the clean W7 slice through mailbox head `9284f4ce`.
  No W6 or LCNF-proof adaptation is required. The larger generic Array semantic
  contract remains parked for its proof consumers; wasm-gen-2 independently
  characterizes the remaining per-call-site closure allocator code-size debt.

## Latest completed integration lease

- Milestone: `W7-LAZY-CACHE-LEAN-ZIP-PACKAGES`.
- Integration owner: `root`, consuming the wasm-gen slice on
  `wasm/generation`. The branch was based directly on accepted `main` at
  `0ebc8b42`, with raw functional prefix `85022516`, Level-1 functional head
  `2cb6dfee`, and clean ready mailbox `9cb30157`.
- Runtime protocol: object-valued compiler constants remain at their ordinary
  lazy use sites. A cold cache publication advances a private persistent heap
  floor, and `fir_heap_rewind` clamps scratch rewinds to that floor. The former
  eager closure walk remains available only through APIs explicitly named
  unsafe for diagnostic use; production raw and Level-1 packages use ordinary
  lazy linking.
- Packages: raw DEFLATE levels 1 through 10 and the migrated Level-1 entry are
  zero-import modules with module-owned memory, one application entry, four
  arena controls, and memory. Raw retains 574 source functions and 5,265
  classified helpers in 1,753,527 bytes; Level-1 retains 324 source functions
  and 1,552 helpers in 508,708 bytes. Removing eager initialization reduced
  Level-1 by 3,076 base bytes and 2,259 complete bytes.
- Acceptance: Lean Beam reports zero diagnostics for the edited runtime/linker
  modules. Node and Chrome package smokes prove monotonic cold publication and
  exactly flat immediate warm rewinds. Native/Wasm raw equality plus independent
  inflate passes five inputs at all ten levels; Level-1 equality passes five
  inputs. `git diff --check`, complete `make check`, all 3,144 Talos jobs, and
  the deterministic artifact gate pass. The root gate covers 125 harness
  tests, 676 source cases, 9 direct-machine cases, a 676-case native/LCNF/V8
  triangle, 685 unique cases, and 2,037/2,037 equal comparisons.
- Result: `main` accepts the clean W7 stack through mailbox head `9cb30157`.
  W6 proves the stable cache-floor behavior independently. W7 next applies the
  already-characterized constant-time resident Array indexing optimization,
  then republishes packages whose exact bytes change.

## Latest completed integration lease

- Milestone: `W6-RESIDUAL-STRUCTURED-VALIDATION`.
- Integration owner: `wasm-proof`, continuing the user-authorized integration
  lease. The accepted stack is based directly on `main` at `a6f4510e`, with
  isolated shared contract `72856600`, functional proof head `42fb2d5d`, and
  ready mailbox `c07eaf4b`.
- Proof-visible production validator: `supportedCodeWithJoins` is now a total
  syntax traversal with defining equations. Its explicit alternative-list
  traversal is proved extensionally equal to the former `Array.all` check, so
  the production acceptance Boolean is preserved. W7 and validation consumers
  rebase on the landed contract but require no implementation adaptation.
- Residual invariant API: `ConcreteStructuredValidationFocus` retains the exact
  current join/local/result/case/sharing judgment, reconstructs the real root
  from `ConcreteSupportedFunction.validatedBodyAt`, and exposes checked
  inversions or continuation laws for `let`, join/jump, cases and selected
  alternatives, ownership, deletion, tag mutation, and all field mutations.
  It stores static compiler validation, not future execution evidence.
- Acceptance: Lean Beam update/sync/save reports zero proof errors for the
  validator and residual proof module; downstream refresh is green. The direct
  3,121-job target build, `git diff --check`, complete `make check`,
  `make talos-setup`, and serial 3,144-job Talos gate pass. The root gate covers
  125 harness tests, 685 unique cases, 2,037/2,037 equal comparisons, all
  coverage/oracle checks, 169 active bug cards, and the trusted-assumption
  audit.
- Result: `main` accepts the clean W6 stack through mailbox head `c07eaf4b`.
  `FIR-BUG-wasm-none-structured-validation-provenance` now remains only at the
  relation-attachment boundary. Exact return inversion confirmed the separate
  `FIR-BUG-wasm-none-return-admission-refinement-direction`: production proves
  `leanCompatible`, while current admission overrequires directional
  `refines`.

## Latest completed integration lease

- Milestone: `W6-STRUCTURED-VALIDATION-PROVENANCE`.
- Integration owner: `wasm-proof`, continuing the user-authorized integration
  lease. The proof slice is based on accepted `main` at `7fd2d2d9`, with
  functional head `f459d5b1`; no shared semantic, generated-code, or executable
  runtime contract changed.
- Compiler provenance: every `ConcreteSupportedFunction` now retains the exact
  source declaration/body selected by production lowering, its declaration
  lookup, and the exact effective result ABI. Generated internal rows preserve
  the same identity across direct, saturated, and lazy calls.
- Validation theorem: `ConcreteSupportedFunction.validatedBodyAt` reconstructs
  the real root `supportedCode` judgment implied by `WasmSupported`, indexed by
  the active result equality already carried by the global structured relation.
  `ConcreteStructuredCompilerCurrentStepAdmission.code` now receives that
  equality instead of dropping it at the compiler-proof boundary.
- Acceptance: Lean Beam update/sync/save reports zero proof errors for all four
  affected proof modules; the direct 3,120-job target build, `git diff --check`,
  complete `make check`, `make talos-setup`, and all 3,143 Talos jobs pass.
  The root gate includes 125 interpreter-harness tests and all coverage,
  native-oracle, bug-card, placeholder, and trusted-assumption checks.
- Result: `main` accepts the clean W6 stack through mailbox head `9269b57f`.
  `FIR-BUG-wasm-none-structured-validation-provenance` remains confirmed: the
  next slice retains and advances residual local/join/case/sharing validation
  state alongside `ConcreteStructuredCodeCoreRel`, then derives the universal
  current-node admission constructors without a recursive caller certificate.

## Latest completed integration lease

- Milestone: `W6-FINITE-TRACE-RESOURCE-BOUNDARY`.
- Integration owner: `wasm-proof`, continuing the user-authorized integration
  lease. The proof slice is based on accepted `main` at `8bcafc05`, with
  functional head `379d8202`; no shared semantic or executable runtime
  contract changed.
- Compiler law: `ConcreteStructuredCompilerCurrentStepAdmission` recovers the
  current ordinary node's source/compiler admission and exact allocation cost
  without a target path, future execution, termination premise, or memory
  claim.
- Resource law: `ConcreteStructuredCurrentStepAddressSpaceSafety` separately
  requires that the admitted cost fit the retained wasm32 budget. Their
  composition reconstructs the runnable classifier and finite-trace package;
  the legacy coverage package is only a compatibility pair.
- Export boundary:
  `ConcreteSupportedExport.finiteTraceCorrect_of_currentStepAdmission` is the
  preferred theorem and exposes compiler admission and finite-memory safety as
  visibly independent hypotheses. `FIR-BUG-wasm-none-finite-trace-address-space-safety`
  is fixed: an unconditional compiler proof can no longer inherit the
  impossible weakened-budget obligation.
- Acceptance: Lean Beam update/sync/save reports zero proof errors; the direct
  3,120-job target build, `git diff --check`, complete `make check`,
  `make talos-setup`, and all 3,143 Talos jobs pass. The root gate covers 125
  harness tests, 676 source cases, 9 direct-machine cases, a 676-case
  native/LCNF/V8 triangle, 685 unique cases, 2,037/2,037 equal comparisons,
  7,341 machine steps, 167 active bug cards, and zero findings.
- Result: `main` may fast-forward through the clean W6 mailbox. W6 next proves
  compiler admission for the currently implemented fragment, with join/jump
  control and other operation widenings explicit, then chooses a resource-safe
  execution invariant or an explicitly budgeted finite-prefix theorem.

## Latest completed integration lease

- Milestone: `W7-GENERIC-CONTAINER-BOXING`.
- Integration owner: `root`, consuming the wasm-gen-2 slice on
  `wasm/generic-container-boxing`. The implementation rebased without conflict
  onto accepted `main` at `e6980062`, with clean functional head `bff62c1e`;
  the standalone boxed-Bool schema contract is `a348f8ac`.
- Contract and lowering: `ValidationSchema.boxed` now admits logical `Bool`.
  Final LCNF represents the payload as `UInt8` zero or one while retaining the
  object-valued box required by generic fields. Input materialization, source
  ABI classification, semantic Wasm loading, and result decoding all use that
  existing box/unbox convention and reject non-Boolean byte payloads.
- Regression: seven real-source cases cover `List UInt8`, `List Bool`, and
  `List Float` reads/round trips plus `Option Bool`, `Option UInt64`, and
  `Except String Float` result construction. Together they exercise tagged
  small integers, heap wide integers, bit-exact heap floats, generic input
  projection/unboxing, and generic result construction/boxing. The concrete
  initial-runtime host now accepts the same manifest-level boxed objects and
  checks scalar kind, payload, auxiliary layout, and floating-point bits.
- Acceptance: Lean Beam update/sync/refresh/save reports zero errors for every
  edited Lean module; focused native/LCNF/V8 and concrete execution probes pass;
  `git diff --check`, complete `make check`, all 3,143 Talos jobs, and the
  complete deterministic artifact gate pass after rebase. The root gate covers
  125 harness tests, 676 source cases, 9 direct-machine cases, a 676-case
  native/LCNF/V8 triangle, 685 unique cases, 2,037/2,037 equal comparisons,
  7,341 machine steps, 167 active bug cards, and zero findings.
- Result: `VALIDATION-BOXED-BOOL-SCHEMA` is released with its validation and
  W7 consumers. This closes all scalar types currently modeled inside generic
  constructor fields. Generic `Array α` remains a separate future contract:
  the validation schema and semantic runtime do not yet contain a generic
  Array heap representation, so it was not papered over by this slice.

- Milestone: `W6-STRUCTURED-ACTIVE-RESULT-INDEX`.
- Integration owner: `wasm-proof`, continuing the user-authorized integration
  lease. The proof slice rebased without conflict onto accepted `main` at
  `a348f8ac`, with functional head `0946ec49`; no shared semantic or executable
  runtime contract changed.
- Exact result index: every `ConcreteSupportedFunction` now retains the first
  symbolic result lane. Supported and runnable global outcomes require that
  lane to equal the active `functionResult`, so the ranked simulation no
  longer ranges over caller-selected malformed ABI indices.
- Calls and returns: production generated rows identify their exact effective
  result lane. Direct calls separately retain the public declared lane used to
  select the source declaration, while direct, saturated, and lazy call entry
  switch to the effective generated lane. Supported caller frames save the
  caller equality and return/pop restores it.
- Export boundary: `ConcreteSupportedExport.supportedGlobalRoot` selects the
  supported function's lane and accepts no result-kind argument.
  `FIR-BUG-wasm-none-structured-active-result-index` is fixed.
- Acceptance: Lean Beam update/sync/save reports zero errors for all four
  modified proof modules; the targeted resumable-Wasm cone, `git diff --check`,
  complete `make check`, `make talos-setup`, and all 3,143 Talos jobs pass
  before and after rebase. The post-rebase root gate covers 125 harness tests,
  669 source cases, 9 direct-machine cases, a 669-case native/LCNF/V8 triangle,
  678 unique cases, 2,016/2,016 equal comparisons, 7,303 machine steps, 167
  active bug cards, and zero findings.
- Result: `main` may fast-forward through the clean W6 mailbox. W6 next splits
  compiler-derived current-node admission from finite wasm32 address-space
  safety, then closes a resource-safe whole simulation or explicitly budgeted
  finite-prefix theorem. Heap-valued lazy miss publication and target-only loop
  unwinding remain independent widenings.

## Latest completed integration lease

- Milestone: `W7-VALIDATION-BOXED-SCALAR-LAYOUT`.
- Integration owner: `root`, consuming the wasm-gen-2 slice on
  `wasm/nested-boxed-scalar-layout`. The implementation rebased without
  conflict onto accepted `main` at `ceec6a59`, with clean functional head
  `1d3c23d1`; the standalone validation-schema contract is `64903ee7`.
- Contract and lowering: `ValidationSchema.boxed` marks the physical object
  representation of a logically scalar fixed-width integer, `USize`,
  `Float32`, or `Float`. LCNF input materialization uses the existing
  final-LCNF `box` operation, result decoding uses `unbox`, and packed concrete
  scalar fields continue to use their ordinary unboxed schemas. This removes
  constructor-name heuristics without changing `ValidationDatum`, the
  symbolic-Wasm surface, concrete layouts, or resident-helper signatures.
- Regression: real-source fixtures cover a tagged boxed `UInt8` nested beside
  a `ByteArray` and a heap boxed `UInt8` returned after a closure reads the
  captured array. Manifest parsing, source ABI classification, semantic host
  loading, and V8 decoding also cover heap `UInt64` and bit-exact heap
  `Float`, while mismatched scalar kinds and tagged floating values fail
  closed. `FIR-BUG-validation-none-nested-boxed-scalar-result` is fixed.
- Acceptance: Lean Beam reports zero diagnostics for every edited Lean module;
  focused native/LCNF/V8 tests pass; `git diff --check`, complete `make check`,
  all 3,143 Talos jobs, and the complete artifact gate pass after rebase. The
  root gate covers 125 harness tests, 669 source cases, 9 direct-machine cases,
  a 669-case native/LCNF/V8 triangle, 678 unique cases, 2,016/2,016 equal
  comparisons, 7,303 machine steps, 167 active bug cards, and zero findings.
  The concrete artifact runner executes 608 cases and retains its existing 61
  ByteArray-blocked inventory; the semantic generated-Wasm triangle executes
  both new fixtures.
- Result: `VALIDATION-BOXED-SCALAR-SCHEMA` is released with its W7/validation
  consumers. Generic constructor fields can now carry boxed scalar values
  according to final-LCNF representation, completing the schema-derived packed
  constructor and nested-alias materialization sequence.

## Latest completed integration lease

- Milestone: `W6-STRUCTURED-EXPORT-ROOT`.
- Integration owner: `wasm-proof`, continuing the user-authorized integration
  lease. The proof slice rebased without conflict onto accepted `main` at
  `64903ee7`, with functional head `d9d74fdf` and clean ready mailbox
  `b7ec16b5`; no shared semantic or executable runtime contract changed.
- Export root: `ConcreteSupportedExport.supportedGlobalRootAt` constructs the
  admission-free strong relation at the actual compiler-produced source and
  structured-Wasm entries from the ordinary concrete cache/ABI frame. Both
  hereditary caller stacks start canonically empty; no source evaluation,
  target path, termination evidence, or future admission is accepted.
- Finite-trace bridge: the export-facing theorem composes that root with the
  ranked current-step classifier. Audit of the remaining coverage obligation
  separates compiler-derived current-node admission from finite wasm32
  address-space safety; lowering alone cannot prove that a positive allocation
  fits an arbitrarily weakened budget or an indefinitely allocating execution.
  `FIR-BUG-wasm-none-finite-trace-address-space-safety` records the resource
  boundary. `FIR-BUG-wasm-none-structured-active-result-index` records that the
  strong relation must still retain the selected symbolic function's exact
  singleton result ABI before universal admission is non-vacuous.
- Acceptance: Lean Beam update/sync/save reports zero errors and save-ready
  hashes `233c4ea0d8a6361a` for `ConcreteStructuredSimulation` and
  `111a1c8fc10ffd39` for `ConcreteResumableWasm`; `git diff --check`, complete
  `make check`, `make talos-setup`, and all 3,143 Talos jobs pass before and
  after rebase. The post-rebase root gate covers 125 harness tests, 667 source
  cases, 9 direct-machine cases, a 667-case native/LCNF/V8 triangle, 676 unique
  cases, 2,010/2,010 equal comparisons, 7,271 machine steps, 167 active bug
  cards, and zero findings.
- Result: `main` fast-forwards through the clean W6 mailbox. W6 next indexes the
  strong relation by the active generated function's actual result ABI, then
  separates compiler admission from address-space safety and closes either a
  resource-safe whole simulation or an explicitly budgeted finite-prefix
  theorem. Heap-valued lazy miss publication and target-only loop unwinding
  remain independent widenings.

## Latest completed integration lease

- Milestone: `W6-POINTWISE-LAZY-CACHE`.
- Integration owner: `wasm-proof`, continuing the user-authorized integration
  lease. The proof slice rebased without conflict onto accepted `main` at
  `3e63192d`, with functional head `47abc3f6` and clean ready mailbox
  `a91cb594`; no shared semantic or executable runtime contract changed.
- Pointwise proof: current-node admission now covers compiler-generated cache
  hits and admitted empty non-heap misses. Staging takes one source step with
  target stutter. Hits take one source lookup and four exact target steps to
  the shared bind protocol. Misses take one source and three target steps into
  the compiler-selected generated initializer.
- Hereditary return: miss entry pushes an exact lazy caller in both resource
  and supported stacks. A related non-heap callee yield then takes one source
  publication step and seven exact target steps for call return, concrete
  `cacheSet`, value/flag global publication, conditional exit, and value
  reload before the ordinary bind rule resumes the caller. The proof restores
  cache, ownership, budget, closure-table, ABI, and supported-caller
  invariants without an initializer evaluation or termination premise.
- Acceptance: Lean Beam update/sync/save reports zero errors and save-ready
  source hash `dc74789b10667059`; the 3,120-job focused simulation/importer
  cone, `git diff --check`, `make talos-setup` at `0e05edbc`, all 3,143 Talos
  jobs, and complete `make check` pass after rebase. The root gate covers 125
  harness tests, 666 source cases, 9 direct-machine cases, 666
  native/LCNF/V8 cases, 675 unique cases, 2,007/2,007 equal comparisons,
  7,252 machine steps, and zero findings. No bug card was required.
- Result: `main` fast-forwards through the clean W6 mailbox. W6 next proves
  production current-step coverage and the canonical export root needed by
  `ConcreteFiniteTraceCorrect`. Heap-valued miss publication remains a
  separate facts-aware widening; target-only loop unwinding remains later.

## Latest completed integration lease

- Milestone: `W6-POINTWISE-ARBITRARY-CASE-TABLES`.
- Integration owner: `wasm-proof`, continuing the user-authorized integration
  lease. The coherent proof checkpoint rebased without conflict onto accepted
  `main` at `8d97e6bd`, with functional head `5bcc92bd` and clean ready
  mailbox `85d8945e`; no shared semantic or executable runtime contract
  changed.
- Pointwise proof: current-node admission now covers every normalized
  object-constructor and scalar-`UInt8` table. The successful source step
  supplies the actual selected arm; production compiler inversion constructs
  an exact target prefix of five steps per tested object tag or four per
  tested byte, without retaining branch choice or execution evidence in
  admission.
- Administrative and rank closure: each executed test adds one target-only
  case-label layer to the resource and supported stacks. Nested calls and
  direct/saturated return-pop preserve and then unwind all such layers. If no
  test executes, the chain theorem proves that the source table is
  default-only and derives the strict compiler-silence-rank decrease required
  by the weak simulation.
- Acceptance: Lean Beam update/sync/save reports zero errors and save-ready
  source hash `cbf737c76a3fc6c3`; the 3,120-job focused simulation/importer
  cone, `git diff --check`, `make talos-setup` at `0e05edbc`, all 3,143 Talos
  jobs, and complete `make check` pass after rebase. The root gate covers 123
  harness tests, 661 source cases, 9 direct-machine cases, 661 native/LCNF/V8
  cases, 670 unique cases, 1,992/1,992 equal comparisons, 7,176 machine steps,
  and zero findings. No bug card was required.
- Result: `main` fast-forwards through the clean W6 mailbox. W6 next adds the
  generated lazy-cache hit and non-heap miss protocols to the pointwise
  relation, then closes remaining production current-step coverage and the
  canonical export root.

## Latest completed integration lease

- Milestone: `W6-POINTWISE-SINGLETON-OBJECT-CASE`.
- Integration owner: `wasm-proof`, continuing the user-authorized integration
  lease. The proof stack rebased without regression onto accepted `main` at
  `3a67ccc0`, with functional head `88613614` and clean ready mailbox
  `786669f2`; no shared semantic or executable runtime contract changed.
- Pointwise proof: source/compiler-only current-node admission now covers a
  normalized singleton object-constructor case. The exact five-step generated
  `getTag`/tag-comparison/conditional prefix selects the source arm while
  preserving the module-stable supported-global relation.
- Administrative closure: the target-only case label is represented in the
  frame, suspended-resource, and supported-frame relations without inventing
  a source frame or storing future execution evidence. Yielded return-pop
  recursively discharges any such case-label layers before consuming the
  underlying direct or saturated caller, so calls nested in a selected arm
  compose with the existing hereditary stack theorem.
- Acceptance: Lean Beam update/sync/save reports zero errors and save-ready
  source hash `28b35f0f4f07b0f7`; the 3,120-job focused simulation/importer
  cone, `git diff --check`, `make talos-setup` at `0e05edbc`, all 3,143 Talos
  jobs, and complete `make check` pass before and after rebase. The root gate
  covers 661 source cases, 9 direct-machine cases, 661 native/LCNF/V8 cases,
  670 unique cases, 1,992/1,992 equal comparisons, 7,176 machine steps, and
  zero findings. No bug card was required.
- Result: `main` fast-forwards through the clean W6 mailbox. W6 next
  generalizes this relation layer to arbitrary normalized object-constructor
  and scalar-`UInt8` case tables, then admits lazy/cache control and closes the
  remaining production current-step coverage plus canonical export root.

## Latest completed integration lease

- Milestone: `W7-ILLUMINATE-SPATIAL-HIT-SCENE`.
- Integration owner: `root`, continuing the user-authorized short W7 lease.
  The Spatial stack rebased onto the accepted resident-container audit at
  `f65205c8`, with clean functional head `afc8b885` and ready mailbox
  `f8f0b412`; patch-equivalent Level1 history was dropped rather than replayed.
- Source boundary: FIR compiles the real Lean 4.33
  `Illuminate.SpatialHitScene.ofHitScene` and `query` definitions from the
  clean, hash-pinned Illuminate source view. A thin borrowed query façade uses
  Lean's generated ownership convention for a scene retained below the
  instance checkpoint; no spatial algorithm is duplicated in FIR or the
  browser adapter.
- Artifact: immutable package
  `integration/illuminate-spatial-hit-scene/_build/illuminate-spatial-hit-scene-06a9c64aaa7f61c7`.
  The 96,006-byte complete Wasm has SHA-256 `366d84059bd0d0ff`, zero imports,
  module-owned memory, two application functions, four arena controls, and
  memory. Deterministic frontier and complete-link repetition passed.
- Acceptance: Node and Chrome each pass all 1,009 shared-oracle queries and
  10,000 flat-frontier queries, with bit-exact coordinates, independent
  scenes, disposal/error coverage, and exact checksums. Lean Beam and the
  focused 73-job source cone pass. Complete `make check`, all 3,143 Talos jobs,
  and the exhaustive browser artifact gate pass with 670 unique cases,
  1,992/1,992 equal comparisons, 43 concrete artifacts, 15 source probes, and
  zero findings. `FIR-BUG-wasm-none-spatial-hit-scene-retained-query-root` is
  fixed.
- Result: `main` fast-forwards through the ready W7 mailbox and this lease is
  released. W7 next develops generic persistent lazy-cache initialization,
  beginning with lean-zip's focused `distanceCodeCacheProbe` before rerunning
  the complete Level1 compressor.

## Latest completed integration lease

- Milestone: `W7-RESIDENT-CONTAINER-OWNERSHIP-AUDIT`.
- Integration owner: `root`, consuming the wasm-gen-2 handoff on
  `wasm/array-ownership-audit`. The patch-equivalent ready head was rebased
  directly on accepted `main` at `bad7b4ba` as functional head `fba1ad8c`;
  no shared signature, layout, symbolic-Wasm, or proof contract changed.
- Runtime repair: resident `Array.swap` now follows upstream Lean's
  ensure-exclusive/copy-on-write path even when both valid indices are equal.
  Both owned and borrowed `Array.get!` variants retain the out-of-bounds
  `Inhabited` fallback before returning it, while in-bounds borrowed lookup
  remains non-retaining.
- Audit boundary: Array, packed ByteArray, String, and List-to-container paths
  are ratcheted across unique, shared, persistent, empty/no-op, self-alias,
  growth, read, mutation, and bounds behavior. ByteArray preserves the
  upstream distinction between `srcOff > size` and the exclusive empty copy at
  `srcOff == size`.
- Acceptance: Lean Beam reported zero diagnostics for the resident Array
  module. Focused resident Array/ByteArray/String Node and V8 artifacts,
  `git diff --check`, complete `make check`, all 3,143 Talos jobs, and the full
  deterministic artifact gate passed. The gate covered 670 unique cases,
  1,992/1,992 equal comparisons, 44 concrete artifacts, and 15 source probes.
  Bug cards `FIR-BUG-wasm-none-array-swap-equal-index-ownership` and
  `FIR-BUG-wasm-none-array-get-bang-default-ownership` are fixed.
- Result: `main` fast-forwards through the clean audit head and the lease is
  released. W7 rebases and republishes Spatial HitScene on this runtime before
  starting the generic persistent lazy-cache initialization slice.

## Latest completed integration lease

- Milestone: `W6-POINTWISE-CONSTRUCTOR-FIELD-MUTATION`.
- Integration owner: `wasm-proof`, continuing the user-authorized integration
  lease. The slice is based directly on accepted `main` at `d73fb90a`, with
  functional head `50909de2` and clean ready mailbox `0ee94f86`; no shared
  semantic or executable runtime contract changes.
- Pointwise proof: source/compiler-only current-node admission now covers
  successful constructor-tag, FVar object-field, erased object-field,
  `USize`-field, and packed-integer scalar-field mutation. It reconstructs the
  canonical source step and derives the exact generated structured-Wasm path:
  two target steps for tags and three for each field writer.
- Resource closure: the low-level mutation theorems are polymorphic in the
  active join-label stack. Existing concrete-runtime refinements preserve the
  witness, heap frontier, entry-relative capacity/cache/closure resource
  scope, and aligned suspended supported frames. The shared relation-level
  transport is proof-only; neither admission nor the recursive relation stores
  source/target execution evidence, and successor code remains admission-free.
- Acceptance: Lean Beam update/sync/save reports zero errors and save-ready
  source hash `7097e0e6188662c7`; the 3,120-job focused simulation/importer cone,
  `git diff --check`, `make talos-setup` at `0e05edbc`, all 3,143 Talos jobs,
  and complete `make check` pass. The root gate covers 661 source cases, 9
  direct-machine cases, 661 native/LCNF/V8 cases, 670 unique cases,
  1,992/1,992 equal comparisons, 7,176 machine steps, and zero findings. No
  bug card was required.
- Result: `main` fast-forwards through the clean W6 mailbox. Broader case and
  lazy/cache control are the next pointwise families, followed by remaining
  production current-step coverage and canonical export-root construction.

## Latest completed integration lease

- Milestone: `W6-POINTWISE-EXPLICIT-DELETE`.
- Integration owner: `wasm-proof`, continuing the user-authorized integration
  lease. The slice is based directly on accepted `main` at `3d7803a0`, with
  functional head `c9608bf7` and clean ready mailbox `e2a892e0`; no shared
  semantic or executable runtime contract changes.
- Pointwise proof: source/compiler-only delete admission constructs the
  canonical source effect step and the production compiler/runtime proofs
  derive its exact two-instruction `local.get; call` structured-Wasm path. The
  admission-free continuation preserves the active entry-relative resource
  scope and aligned suspended caller stack, so the module-stable supported
  global relation is restored.
- Erased boundary: the same theorem covers ordinary live-object deletion and
  the accepted erased-value/physical-zero no-op. It consumes the existing
  concrete delete refinement without weakening ordinary object decoding and
  stores neither source nor target execution evidence in admission.
- Acceptance: Lean Beam update/sync/save reports zero errors and save-ready
  source hash `835837af6ea37b24`; the 3,120-job focused simulation/importer cone,
  `git diff --check`, `make talos-setup` at `0e05edbc`, all 3,143 Talos jobs,
  and complete `make check` pass. The root gate covers 661 source cases, 9
  direct-machine cases, 661 native/LCNF/V8 cases, 670 unique cases,
  1,992/1,992 equal comparisons, 7,176 machine steps, and zero findings. No
  bug card was required.
- Result: `main` fast-forwards through the clean W6 mailbox. Constructor-tag
  mutation is the next pointwise family, followed by field mutation, broader
  cases/lazy-cache control, production coverage, and the canonical export root.

## Latest completed integration lease

- Milestone: `W6-POINTWISE-ORDINARY-OWNERSHIP`.
- Integration owner: `wasm-proof`, taking the user-authorized integration
  lease after completing the W6 slice. The complete W6 stack was rebased
  directly on accepted `main` at `7b07ebdc`; functional head `cf7ad7c5` and
  clean ready mailbox `044eedde` change no shared semantic or executable
  runtime contract.
- Simulation closure: the certificate-free strong relation now packages the
  finite-trace bridge and derives its global current-step classifier from one
  source-local compiler coverage law. Ordinary nonpersistent increment and
  recursive decrement are both admitted from source/compiler facts alone and
  preserve the same module-stable pointwise relation across their exact
  two-instruction `local.get; call` target prefixes.
- Ownership proof: increment and decrement reconstruct the canonical source
  successor, concrete heap transition, entry-relative capacity/cache/closure
  resource scope, and aligned suspended caller stack. Recursive owned-graph
  release is discharged by the existing decrement refinement and
  ordinary-persistence transports; neither admission stores a source or target
  execution certificate.
- Acceptance: Lean Beam update/sync/save reports zero errors and a save-ready
  module; the 3,120-job focused simulation/importer cone passes. After the W7
  Level1 publication landed, the seven-commit W6 stack rebased conflict-free
  and passed `git diff --check`, `make talos-setup` at `0e05edbc`, all 3,143
  Talos jobs, and complete `make check`: 661 source cases, 9 direct-machine
  cases, 661 native/LCNF/V8 cases, 670 unique cases, 1,992/1,992 equal
  comparisons, 7,176 machine steps, and zero findings. No bug card was
  required.
- Result: `main` fast-forwards through the clean W6 mailbox. W6 next adds
  explicit deletion to the pointwise relation, then tag/field mutation and the
  remaining production current-step coverage plus canonical export-root
  construction.

## Latest completed integration lease

- Milestone: `W7-LEVEL1-EXTERN-BOUNDARY-PUBLICATION`.
- Integration owner: `root`, reconciling the clean `wasm/capture-upstream`
  capture handoff with the completed `wasm/generation` Level-1 publication on
  branch `integration/level1-capture`. The stack is based on accepted main
  `3cfddfc0`; clean functional head `ba380dd9` includes the exact regenerated
  closure ratchet.
- Capture/runtime slice: Lean's ordinary final-LCNF pipeline still generates
  each required `_boxed` adapter locally, after which FIR restores the original
  environment `@[extern]` declaration to its resident-runtime boundary. The
  linked closure also includes the accepted source-provider fixed-width
  rewrite, arbitrary-precision `Nat.mod`, persistent big-numeric admission,
  mixed constructor provenance, and revision-safe exhaustive artifact gates.
- Production evidence: the real Lean 4.33 `Zip.Wasm.compressLevel1` capture
  contains 432 declarations and 108 reviewed externals. It retains 324 source
  functions, links 1,552 resident helpers, and emits 1,876 functions with zero
  unsupported declarations, function imports, memory imports, or residual
  runtime operations. Native/Wasm output agrees on all five production cases,
  and both Node and Chrome exercise the packed ByteArray adapter with scratch
  rewind.
- Artifact: immutable Level-1 package
  `integration/lean-zip/_build/lean-zip-level1-packages/ba380dd90385-30737b4e2ebf-1179fc8ac6fc54fe83d0`;
  canonical pointer `integration/lean-zip/_build/lean-zip-level1-current`.
  Complete Wasm is 501,668 bytes with SHA-256
  `592f1abcf1a4044e721135967476550043e283d57bf4ff30454e6fcaf30bc079`;
  base Wasm is 212,709 bytes with SHA-256
  `d4ff5ce46affba6e6319109b4fc4b525f8a2078b5f7c990501dbcfb66ab484d8`.
- Contracts and discrepancies: no shared semantic, concrete-layout,
  symbolic-Wasm, or W6 proof contract changed. Eight W7 bug cards covering
  capture, fixed-width selection, Nat modulo, persistent numerics, constructor
  provenance, and stale artifact checkpoints are fixed. Generic Nat-heavy
  allocation remains a performance follow-up: a 4 KiB repeated input can grow
  the scratch frontier by about 2.98 GB before the successful rewind.
- Acceptance: Lean dependency cones and the exact Level-1 closure probe pass;
  `git diff --check` and `make check` pass with 670 unique cases and
  1,992/1,992 equal comparisons; worktree-local Talos setup and all 3,149 jobs
  pass; the complete deterministic Talos artifact gate passes; and the
  lean-zip gate passes native oracles, deterministic double publication,
  checksums, Node, Chrome, zero-import assertions, and scratch reclamation.
- Result: `main` fast-forwards through the reconciled green stack and this
  acceptance record; the integration lease is released. W7 may next profile
  the remaining Level-1 allocation amplification or resume the independent
  Array/spatial-HitScene generation backlog.

## Latest completed integration lease

- Milestone: `FIR-SCOPED-LAKE-ARTIFACT-CACHE`.
- Integration owner: `test-fixtures`, consuming the compile-performance
  handoff `af3ed1e0` and hardening it on branch
  `integration/fir-scoped-cache`; functional head `6597c4ce` is based on the
  accepted Level1 container frontier `9dc37c59`.
- Cache boundary: every FIR worktree shares only Lake 4.33's content-addressed
  artifact cache under repository-local `.lake_cache/<toolchain>`. The helper
  resolves the current worktree's `lean-toolchain`, the Git common directory
  locates the shared repository root, and both cache boundaries are mode 700.
  `.lake`, `.beam`, and `.deps` remain private to each lane. Make targets export
  the cache automatically; direct Lake and Lean Beam commands use the exact
  environment command in `AGENTS.md`.
- Contracts and discrepancies: no semantic contract, proof, runtime,
  compiler, corpus case, or W6/W7-owned implementation changed. The standalone
  Talos environment-prefix candidate `aa9e0191` is superseded because the root
  Makefile exports the same scoped environment to nested workspaces. No bug
  card was required.
- Acceptance: a cold self-contained Talos admission passed all 3,149 jobs in
  9m59.743s, including the 592s `Interpreter.Wasm.SmallStep` target. A fresh
  detached consumer then restored the 22-job root build in 0.206s and the full
  Talos cone in 8.033s. Representative 27MB simulation and 80MB interpreter
  artifacts are read-only hard links to the scoped cache. `git diff --check`
  and complete `make check` pass with 670 unique cases, 1,992/1,992 equal
  comparisons, 7,176 machine steps, all semantic coverage floors, 150 active
  bug cards, and exactly one registered trusted axiom.
- Result: the 4.2GB Lean 4.33 namespace contains 21,793 artifacts and can be
  audited or retired independently of other Lean projects. Per-lane Talos
  dependency checkout and mathlib unpack remain lane-local and cost about
  6.4GB; reducing that footprint is a separate task and must not introduce
  shared mutable package state.

## Latest completed integration lease

- Milestone: `W7-LEVEL1-BYTEARRAY-STRING-NAT-FRONTIER`.
- Integration owner: `wasm-gen-2`, acting under the user-authorized temporary
  integration lease. Branch `wasm/gen-bytearray-level1` was rebased on
  accepted local main `af3ed1e0`; the clean functional head is `b923b4dc`.
- Runtime slice: `8087adf3` internalizes the eight ByteArray operations used by
  the real Level-1 compressor, `89cca9ee` internalizes UTF-8
  `String.ofList`, and `b923b4dc` internalizes arbitrary-precision `Nat.mul`,
  `Nat.pow`, `Nat.land`, and `Nat.div`. The generic closed-application linker
  selects the Nat family after the accepted arbitrary-precision base.
- Semantics: ByteArray preserves packed little-endian data, geometric growth,
  and unique/shared/persistent ownership. `String.ofList` validates Unicode,
  allocates one exact UTF-8 result, and consumes its list spine. Nat operations
  accept immediate, promoted, and multi-limb values without wasm32 narrowing;
  division by zero and exponentiation corner cases match Lean. Inputs are
  borrowed and all walkers use structured loops.
- Production evidence: the real Lean 4.33 `Zip.Wasm.compressLevel1` closure
  captures 391 declarations and 110 externals with zero unsupported
  declarations. Resident linking leaves zero runtime operations and exactly
  two ordinary imports:
  `List.foldl._at_.Array.appendList.spec_0._redArg` and
  `List.zipWith._at_.List.zip.spec_0._redArg`. On the accepted linear-linker
  base, phases measure 15.723s capture, 2.973s lowering, and 5.418s linking;
  the same closure linked in 43.141s before the linear-linker landing.
- Artifacts: the standalone ByteArray, String, and Nat fixtures are
  zero-import/module-memory modules of 9,861, 17,734, and 15,405 bytes. The Nat
  SHA-256 is
  `d0ecc0ecc9432678aab649391731da8d2981ad1352941fd2d47b0942b15c61e3`;
  repeated generation is byte-identical.
- Contracts and discrepancies: no shared semantic, concrete-layout, or
  symbolic-Wasm contract changed. All three executable families are W7
  generation-ready; W6 refinement remains separate. Bug cards
  `FIR-BUG-wasm-none-lean-zip-byte-array-import-frontier`,
  `FIR-BUG-wasm-none-lean-zip-string-of-list-import-frontier`, and
  `FIR-BUG-wasm-none-lean-zip-nat-arithmetic-import-frontier` are fixed.
- Acceptance: Lean Beam saves all edited Lean modules with zero diagnostics;
  focused Node/V8 ownership and arbitrary-precision differential clients pass;
  `git diff --check` and complete `make check` pass with 670 unique cases,
  1,992/1,992 equal comparisons, zero findings, and 150 valid bug cards;
  Talos setup and all 3,143 Talos jobs pass; and the complete deterministic
  artifact gate passes resident helpers, both prettyM packages, and the
  661-case native/LCNF/V8 triangle.
- Result: `main` fast-forwards through the dependency-ordered three-commit
  stack and this acceptance record; the lease is released. The two generated
  List specializations are the complete remaining Level-1 generation frontier.

## Latest completed integration lease

- Milestone: `W7-GENERIC-LEVEL1-STANDARD-RUNTIME-FRONTIER`.
- Integration owner: `wasm-gen`, acting under the user-authorized integration
  lease. Branch `wasm/generation` was rebased on accepted local main
  `0c1e5b91` and landed through clean ready mailbox `1a00ba85`; functional
  head `9bd136d7` changes no shared contract or W6-owned file.
- Runtime slice: the complete fixed-width and USize frontier is resident,
  including 61 zero-import helpers and `USize.repr`. Generic Array lookup,
  update, swap, List conversion, and the wasm32/Lean64 platform-width helper
  preserve unique/shared/persistent ownership without host fallbacks.
- Production evidence: the real Lean 4.33 `Zip.Wasm.compressLevel1` closure
  remains 391 declarations and 110 externals with zero unsupported
  declarations and zero runtime operations. Its ordinary import frontier
  moves from 47 to 15 while the complete linked module reaches 1,730
  functions. On the final indexed-validator base, measured phases are 54.040s
  capture, 13.876s lowering, and 108.402s resident linking; link time is 9.6%
  below the immediately preceding transaction-boundary baseline.
- Contracts and discrepancies: no shared contract changed. The executable
  helpers are generation-ready; W6 refinement remains separate. The
  fixed-width frontier card is fixed. The remaining container-frontier card
  names exactly eight ByteArray, four Nat, two generated List, and one String
  import. No semantic workaround or new discrepancy was introduced.
- Acceptance: Lean Beam and focused dependency-cone builds pass; standalone
  zero-import Node ownership/differential fixtures pass; `git diff --check`
  and complete `make check` pass with 670 unique cases and 1,992/1,992 equal
  comparisons; all 3,143 Talos jobs pass; and the complete deterministic
  artifact gate passes resident helpers, double generation, packages,
  checksums, browser/stack safety, the repeated 661-case V8 triangle, 44/44
  concrete artifacts, and 15/15 source probes. The explicit concrete fence is
  608/661 executed with exactly 53 ByteArray-layout blockers. The final
  cache-only rebase additionally regenerates the exact 14,558-byte zero-import
  Array fixture through the writable user toolchain cache and its Node
  ownership suite passes.
- Result: `main` fast-forwards through the clean W7 handoff and this acceptance
  record. ByteArray closure continues independently on
  `wasm/gen-bytearray-level1`; W7 next addresses the principled generic Nat,
  String, and generated-List frontier before publishing Level1.

## Latest completed integration lease

- Milestone: `ELIMDEAD-GENERIC-LOCAL-LEDGER-OPERATIONS`.
- Integration owner: `lcnf-proof`, acting under the user-authorized temporary
  integration lease. Branch `proof/simpcase` was rebased on accepted local
  main `a25713a6` and landed through clean ready mailbox `5cae5958`;
  functional head `5c607e0e` changes no shared contract.
- Proof slice: `DeletedLedgerLetLocalReadyAt` packages one deleted reset or
  concrete-token reuse with its source-only ownership bridges. Generic target
  live-prefix premises derive ordinary and source-owned ledger readiness;
  the retained-prefix fixture now consumes that interface through a singleton
  adapter instead of classifying reset/reuse as whole-program states.
- Lean 4.33 compatibility: two pre-existing ledger-owner projection examples
  make `id` reduction explicit. This is an elaboration repair only and does
  not alter the relation, interpreter, or compiler semantics.
- Contracts and discrepancies: none. The slice is proof-owned and introduces
  no bug card, semantic workaround, new axiom, or W6/W7 dependency.
- Acceptance: Lean Beam reports zero errors for both edited modules (source
  hashes `088ed97b5359b156` and `373fe5f8586eff26`); the 34-job examples cone,
  `git diff --check`, and complete `make check` pass. The final gate covers 670
  unique cases, 1,992/1,992 equal comparisons, 7,176 machine steps, 160/160
  semantic-tag floors, 253/253 semantic-domain floors, 146 active bug cards,
  and exactly one registered trusted axiom.
- Result: `main` fast-forwards through the clean handoff and this acceptance
  record; the lease is released. The next proof task derives the target
  live-prefix premise for multi-location residual/control states, then removes
  the singleton retained-prefix adapter from the next source-plan fixture.

## Latest completed integration lease

- Milestone: `VALIDATION-S9-DICTIONARY-OWNERSHIP`.
- Integration owner: `test-fixtures`, acting under the user-authorized
  integration lease for this fixture-only milestone. The lane branch was
  rebased on accepted local main `66aeb6d1` and landed through clean ready head
  `5937df70`; functional head `84ef07e9` changes no shared contract.
- Semantic pair: a runtime class dictionary holds mutator and observer method
  closures that capture the same `ByteArray`. The unique path consumes the
  owner before mutation and returns `[42, 127, 128, 255]`; the retained path
  preserves the owner across mutation, invokes the observer sibling, and
  returns the updated copy paired with original-byte observation `0`.
- Executed evidence: complete 42/71-transition paths pin two `pap` forms,
  dictionary and owner construction, method projection, indirect `fvar`
  invocation, ownership increments/decrements, and exact external order. The
  retained path executes `ByteArray.set!`, `ByteArray.get!`, `UInt8.toNat`
  after mutation; the unique path executes only `ByteArray.set!` after sibling
  release.
- Discrepancy: the rejected implicit-class formulation exposed
  `FIR-BUG-impure-none-dictionary-specialization-capture`. Isolated final-LCNF
  capture retains opaque external stubs instead of generated method
  specialization bodies. The generated names were not allowlisted; the
  admitted runtime experiment uses a named non-class owner boundary.
- Contracts: none. The slice consumes the linked closure-application,
  aggregate, ByteArray, compiler, and real-engine surfaces while active proof,
  W6, W7, error, exception, and source-stream contracts remain fenced.
- Acceptance: Lean Beam update/sync/save at version 6 with zero diagnostics;
  dependency-cone build; focused native/LCNF and native/LCNF/V8 probes;
  `git diff --check`; and complete `make check`. The final snapshot has 661
  source cases, 670 unique cases, 1,331 tier cases, 1,992/1,992 equal
  comparisons, 7,176 interpreter steps, 160/160 tag floors, 253/253 semantic
  domains, 1,322 native-oracle witnesses, and zero findings. V8 opened all
  1,322 products under strace; 146 bug cards validate.
- Result: `main` fast-forwards through the clean handoff and this acceptance
  record. S9 is the dictionary sibling-lifetime baseline. Further E2 work must
  add a polymorphic runtime-shape signature not dominated by S9 or scalar ABI
  coverage.

## Latest completed integration lease

- Milestone: `VALIDATION-S8-AGGREGATE-ERASURE-OWNERSHIP`.
- Integration owner: `test-fixtures`, acting under the user-authorized
  integration lease for this fixture-only milestone. The lane branch was
  already based on accepted main `ad3bea73` and landed through clean ready
  head `91a38725`; functional head `15f04191` changes no shared contract.
- Semantic pair: a proof-bearing outer owner contains `Option ByteArray` and
  supplies its nested payload to a real partial application. The released
  path consumes the owner before application and returns updated
  `[42, 127, 128, 255]`; the retained path keeps the complete owner live across
  application and returns both unchanged `[0, 127, 128, 255]` and the updated
  copy. Final LCNF constructs two runtime fields from the three source fields,
  statically witnessing proof erasure.
- Executed evidence: complete 37/48-transition paths pin construction,
  `Option.some` case selection and projection, `pap`, `fvar`, ownership
  increments/decrements, and exactly one `ByteArray.set!` dispatch. A noinline
  post-application observer forces the retained path to keep the outer owner,
  rather than merely a hoisted inner projection, live across mutation.
- Contracts: none. The slice consumes accepted aggregate, erased-field,
  closure-application, ByteArray, compiler, and real-engine surfaces while
  leaving the active argument-alias, effectful-native-oracle, IO-error,
  exception, and source-stream contracts fenced.
- Acceptance: Lean Beam update/sync/save at version 6 with zero diagnostics;
  dependency-cone build; focused native/LCNF/V8 probes; `git diff --check`;
  and complete `make check`. The final snapshot has 659 source cases, 668
  unique cases, 1,327 tier cases, 1,986/1,986 equal comparisons, 7,063
  interpreter steps, 146/146 tag floors, 249/249 semantic domains, 1,318
  native-oracle witnesses, and zero findings. V8 opened all 1,318 products
  under strace. No bug card was required.
- Result: `main` fast-forwards through the clean handoff and this acceptance
  record. S8 is the aggregate-erasure lifetime baseline. Another E1 shape is
  admitted only if narrowing finds a new execution signature; otherwise the
  fixture lane advances to E2 dictionary traffic or B2 application shapes.

## Latest completed integration lease

- Milestone: `VALIDATION-S7-ESCAPING-CLOSURE-OWNERSHIP`.
- Integration owner: `test-fixtures`, acting under the user-authorized
  integration lease for this fixture-only milestone. The lane branch was
  rebased on accepted main `d286e41a` and landed through clean ready head
  `1cfcb9b8`; functional head `d695bd66` changes no shared contract.
- Semantic pair: both cases return a closure-bearing owner from a noinline
  maker before later application. Unique transfer consumes the sole captured
  ByteArray and returns `[42, 127, 128, 255]`; the shared path retains an
  outside alias and returns both unchanged `[0, 127, 128, 255]` and the updated
  copy.
- Executed evidence: complete 27/29-transition LCNF paths pin the named maker
  `fap`, its `pap` and `return`, the later `fvar` closure invocation, and one
  `ByteArray.set!`. The unique path executes zero ownership increments; the
  shared path adds exactly one `inc` and its result-pair `ctor`. A smaller bare
  function candidate was rejected because eta-normalization erased the return
  boundary and duplicated an existing execution signature.
- Contracts: none. The slice consumes accepted closure application, ByteArray,
  compiler, and real-engine surfaces while leaving the active argument-alias,
  effectful-native-oracle, IO-error, exception, and source-stream contracts
  fenced.
- Acceptance: post-rebase Lean Beam refresh/save with zero diagnostics;
  focused pinned native/LCNF and native/LCNF/V8 probes; `git diff --check`; and
  complete `make check`. The final snapshot has 657 source cases, 666 unique
  cases, 1,323 tier cases, 1,980/1,980 equal comparisons, 6,978 interpreter
  steps, 138/138 tag floors, 245/245 semantic domains, 1,314 native-oracle
  witnesses, and zero findings. V8 opened all 1,314 products under strace. No
  bug card was required.
- Result: `main` fast-forwards through the clean handoff and this acceptance
  record. S7 lands the first source-generated returned-closure ownership
  boundary; E1 aggregate/erasure is the next fixture-only portfolio candidate.

## Latest completed integration lease

- Milestone: `W7-GENERIC-LEVEL1-RUNTIME-AND-FIXED-WIDTH-FRONTIER`.
- Integration owner: `wasm-gen`; branch `wasm/generation` was rebased directly
  on `main` at `8051df3c`, with functional head `45ee2ff9` and clean ready
  mailbox `3178f37c`.
- Production closure: the generic single-unit source path captures the real
  Lean 4.33 `Zip.Wasm.compressLevel1` final-LCNF closure as 391 declarations
  and 110 externals, with no copied compressor and no unsupported
  declarations. Resident linking now reports linking errors separately from a
  successful empty runtime-operation frontier.
- Runtime closure: object-family closure calls, capability-sensitive
  fallbacks, scalar projections/boxing, and promoted literals reduce the
  unresolved runtime-operation inventory from 55 to zero. The first generic
  fixed-width slice adds 30 exact helpers, reducing ordinary declaration
  imports from 77 to 47 and increasing resident functions from 1,666 to
  1,696. It preserves the exact final-LCNF distinction between tagged
  `UInt8.toNat`/`UInt16.toNat` and tobject `UInt32.toNat` results.
- Contracts: no shared contract changed. The executable helper signatures are
  generation-ready; W6 refinement remains separate. The post-rebase artifact
  adaptation only ratchets the two newly accepted ByteArray ownership cases
  into the explicit 47-case layout blocker inventory.
- Acceptance: Lean Beam refresh/save with zero errors; `git diff --check`;
  complete `make check` with 655 source cases, 664 unique cases, 1,974/1,974
  equal comparisons, and zero findings; Talos setup at `0e05edbc` and all
  3,143 Talos jobs; and the complete deterministic artifact/package gate.
  The zero-import fixed-width fixture exports all 35 helpers in 7,793 bytes;
  prettyM and PrettyTrace reproduce at 138,755 and 142,833 bytes.
- Result: `main` fast-forwards through the clean W7 mailbox. The active card
  `FIR-BUG-wasm-none-lean-zip-fixed-width-import-frontier` tracks the remaining
  25 fixed-width/USize imports; another 22 Array/ByteArray/Nat/List/String/
  platform imports follow before Level1 package publication. Generic compiler
  latency profiling proceeds independently on `perf/compilation-perf`.

## Latest completed integration lease

- Milestone: `VALIDATION-S6-NONLOCAL-CLOSURE-OWNERSHIP`.
- Integration owner: `test-fixtures`, acting under the user-authorized
  integration lease for this fixture-only milestone. The lane branch was
  `validation/closure-ownership-fixtures` from `f996628c` through ready head
  `e48e70d7`; functional head `4a17f43b` changes no shared contract.
- Semantic pair: both cases capture the input `ByteArray` in a real partial
  application, read through it, cross the linked `recordByteArray` effect, and
  read again. Final use releases the capture before the effect and observes
  byte `42` from the returned array. Retained use preserves the capture across
  the effect, invokes the closure afterward, and observes the original byte
  `0`, making incorrect shared mutation observable.
- Executed evidence: the complete final/retained LCNF paths contain 39/54
  transitions, one/two `fvar`, one/two `inc`, and two/four `dec`. Both pin the
  exact five-dispatch order `ByteArray.get!`, `UInt8.toNat`,
  `recordByteArrayImpl`, `ByteArray.get!`, `UInt8.toNat` plus exact event-time
  original/updated ByteArray snapshots.
- Contracts: none. The slice consumes accepted closure-application ownership,
  effect projection, and V8 provider behavior. It neither consumes nor
  duplicates the active argument-alias, IO-entry, error, or source-stream
  contracts; their queued fixtures remain fenced.
- Acceptance: Lean Beam update/sync/save at version 5 with zero diagnostics;
  focused native/LCNF and native/LCNF/V8 probes; `git diff --check`; dependency
  cone build; and complete `make check`. The final snapshot has 655 source
  cases, 664 unique cases, 1,319 tier cases, 1,974/1,974 equal comparisons,
  6,922 interpreter steps, 132/132 tag floors, 241/241 semantic domains, 1,310
  native-oracle witnesses, and zero findings. V8 opened all 1,310 products
  under strace. No bug card was required.
- Result: `main` fast-forwards through the clean ready handoff and this
  acceptance record. S6 becomes the landed nonlocal-memory baseline; caught
  exceptions and explicit argument-alias materialization remain behind their
  named shared contracts.

## Latest completed integration lease

- Milestone: `WASM-LEAN-OBJECT-FAMILY-CLOSURE-ABI`.
- Integration owner: `wasm-gen` acting under the shared-compiler integration
  lease; the isolated branch was `integration/object-family-closure-call`
  from `88ea55dd` through `b2d6f45c`.
- Compiler contract: ordinary arguments supplied to an allocated closure and
  its saturated result now use the same symmetric Lean object-family call ABI
  as named calls and joins. Capture descriptors and semantic refinement remain
  directional; scalar and erased lanes remain exact.
- Proof bridge: the shared ABI records that directional refinement implies
  Lean call compatibility, so the existing W6 closure-resolution hypotheses
  prove the widened compiler admission without changing W6-owned contracts.
- Regression: a generic `[tobject, tobject]` closure application resolves a
  target with `[object, object]` parameters and emits a valid module, while a
  `UInt32` argument remains rejected. Bug card
  `FIR-BUG-wasm-none-generic-object-family-closure-call-admission` is fixed.
- Production confirmation: this removes the last unsupported declaration in
  the 391-declaration `Zip.Wasm.compressLevel1` final-LCNF closure. The exact
  resident-helper inventory is the next W7 probe.
- Acceptance: Lean Beam update/sync/save with zero errors; `git diff --check`;
  complete `make check` through 662 unique cases and 1,968/1,968 comparisons;
  and all 3,143 Talos jobs. The deterministic artifact gate reaches its strict
  prettyM closure-inventory ratchet: the reviewed count moves from 40 to 42,
  which W7 updates as the immediate consumer adaptation before republishing.
- Result: `main` fast-forwards to `b2d6f45c`; W7 rebases, ratchets the exact
  artifact inventory, reruns the complete gate, and then resumes Level1.

## Latest completed integration lease

- Milestone: `FINAL-LCNF-GENERATED-NAME-ISOLATION`.
- Integration owner: `wasm-gen` acting under the shared-compiler integration
  lease; the functional branch was `integration/level1-capture-u8` from
  `3f7bcbc8` through `8f872e1d`.
- Compiler contract: each generic isolated final-LCNF compilation now forgets
  imported module mappings for generated closed terms and specializations in
  the source modules being recompiled, then clears the corresponding Lean
  compiler caches. Ordinary source declarations and unrelated modules retain
  their mappings.
- Regression: `Fir.Wasm.Emit.SourceClosedFixture.packedTable` reproduces the
  former generated-name ABI collision on the unpatched base and is compiled
  through the public generic capture API by `SourceExamples`. Bug card
  `FIR-BUG-wasm-none-final-capture-generated-name-abi` is fixed.
- Production confirmation: the repaired generic API captures the real
  `Zip.Wasm.compressLevel1` entry as 391 declarations and 110 externals. Its
  former `UInt8`/object ABI failure is gone; lowering now reaches one ordinary
  unsupported declaration, `List.MergeSort.Internal.mergeTR.go`, which is the
  next W7 admission slice.
- Acceptance: Lean Beam update/sync with zero errors; focused dependency cone;
  `git diff --check`; complete `make check` with 122 harness tests, 662 unique
  cases, and 1,968/1,968 comparisons; all 3,149 Talos jobs; and the complete
  deterministic artifact gate. The prettyM binaries reproduced at 122,384 and
  126,462 bytes.
- Result: `main` fast-forwards to `8f872e1d`. W7 rebases its Level1 probe and
  continues through the generic single-unit API; the module-wise API remains
  reserved for source views containing deferred compiler groups.

## Latest completed integration lease

- Milestone: `W7-RESIDENT-CONTAINER-OWNERSHIP`.
- Integration owner: `wasm-gen`; this lease aligns the executable resident
  Array and String families with Lean's uniqueness and copy-on-write model.
- Integration branch/worktree: `wasm/generation` in
  `.worktrees/wasm-generation`, rebased directly on `main` at `e37175ba`.
- Published stack: generic Array ownership `6592e2cb`, String and conversion
  ownership `114a4840`, and clean ready mailbox `282e2f30`.
- Runtime behavior: module-created Arrays and Strings are live refcount-one
  values. Exclusive capacity-fitting mutation preserves address and frontier;
  shared and persistent values copy. Array release recursively releases its
  live child prefix. String capacity is derived from allocation extent without
  changing its frozen header. `ByteArray.mk` accepts and consumes live Arrays.
- Contracts: the Array and String executable helper semantics are
  generation-ready. W6 refinement remains deliberately separate; no symbolic
  Wasm, interpreter, or shared source-semantics contract changed.
- Acceptance: Lean Beam was green on the String and ByteArray modules; focused
  real-engine fixtures passed for all three repaired discrepancies;
  `git diff --check`; complete `make check` with 122 harness tests, 662 unique
  cases, and 1,968/1,968 comparisons; all 3,143 Talos jobs; and the complete
  deterministic artifact/package gate including the 653-case V8 triangle.
- Result: `main` fast-forwards through the clean W7 mailbox. W7 next implements
  the exact packed ByteArray mutation surface required by
  `Zip.Wasm.compressRaw`/Level1, then `Array.swap`; `FloatArray` remains a
  distinct packed-layout slice.

## Latest completed integration lease

- Milestone: `W6-STAGED-EXTERNAL-RUNNABLE-CLOSURE`.
- Integration owner: `wasm-proof`; this lease adds the first non-erased
  runtime family to the certificate-free, module-stable one-source-step
  theorem without collapsing its source protocol.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`, based directly on `main` at `e7288dfc`.
- Published stack: active-slice record `07e09c1c`, functional proof head
  `36a67502`, and clean ready mailbox `a5d4e7fb`.
- Current-node admission: `ConcreteStructuredCodeStepAdmission` is now
  parameterized by the installed external implementation and admits the
  proved pure Int, Nat, and scalar result families at their exact
  response-selected allocation cost. It stores no future execution.
- Staged protocol: `ConcreteStructuredExternalCallReadyCoreRel` and
  `ConcreteStructuredExternalBindCoreRel` expose the source request/import/
  bind phases individually. The imported call transports the complete
  entry-relative facts, cache, witness, closure tables, ABI alignment, and
  caller stack while preserving the pre-bind fact map. The generated
  destination write then erases exactly the shadowed destination fact and
  returns to ordinary compiled code.
- Strong closure: both intermediate states are constructors of the open and
  runnable outcome sums. Staging, imported call, and bind each take one
  ordinary source step, construct the exact finite structured-Wasm path, and
  return the same aligned supported global relation. Empty compiled argument
  prefixes use the existing strict compiler-control-rank descent.
- Contracts: none. This slice changes W6 proof admission/intermediate
  relations and W6 roadmaps only; it changes no compiler/runtime semantics,
  concrete layout, symbolic-Wasm surface, or resident-helper signature.
- Acceptance: Talos setup at `0e05edbc`; Lean Beam update/sync/save at version
  8 with zero errors; direct `FirTalos.ConcreteStructuredSimulation` build
  (3,119 jobs); `git diff --check`; complete `make check` with 122 harness
  tests, 662 unique cases, and 1,968/1,968 equal comparisons; and all 3,143
  Talos jobs. No bug card was required.
- Result: `main` fast-forwards through the clean ready mailbox. W6 next
  packages root/current-node admission into the public certificate-free
  finite-prefix theorem; subsequent operation families are admission
  widenings rather than changes to the theorem's shape.

## Latest completed integration lease

- Milestone: `W6-SILENT-RUNNABLE-WIDENING`.
- Integration owner: `wasm-proof`; this lease extends the certificate-free,
  module-stable one-source-step theorem across compiler-erased case and
  ownership operations.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`, based directly on `main` at `872d061d`.
- Published stack: active-slice record `af2e9539`, functional proof head
  `0a7f8866`, and clean ready mailbox `4348302a`.
- Current-node admission: `ConcreteStructuredCodeStepAdmission` now admits
  default-only cases and persistent `inc`/`dec` at exact cost zero. It stores
  only the static current-node shape; the successful ordinary source step
  reconstructs the unique selected default branch dynamically.
- Strong closure: the three resource-indexed pointwise laws take one source
  step against a reflexive target path, preserve the concrete resource core
  and aligned supported caller stack through exact frame equality, and
  strictly decrease `compilerStructuredControlRank`. Both pointwise and
  module-wide runnable dispatchers return the same admission-free supported
  global relation.
- Contracts: none. This slice changes W6 proof admission and roadmaps only; it
  changes no compiler/runtime semantics, concrete layout, symbolic-Wasm
  surface, or resident-helper signature.
- Acceptance: Talos setup at `0e05edbc`; Lean Beam update/sync/save at version
  24 with zero errors; direct `FirTalos.ConcreteStructuredSimulation` build
  (3,119 jobs); `git diff --check`; complete `make check` with 122 harness
  tests, 662 unique cases, and 1,968/1,968 equal comparisons; and all 3,143
  Talos jobs. No bug card was required.
- Result: `main` fast-forwards through the clean ready mailbox. W6 next adds a
  non-erased family to this current-node boundary, preferably the staged pure
  external protocol with resource-indexed ready/bind relations, before
  packaging the public certificate-free finite-prefix theorem.

## Latest completed integration lease

- Milestone: `W6-STRONG-RUNNABLE-CONTROL-CLOSURE`.
- Integration owner: `wasm-proof`; this lease closes the first
  constructor-complete, module-stable one-source-step theorem for the strong
  compiler relation without adding future-execution certificates.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`, based directly on `main` at `4d9668a1`.
- Published stack: active-slice record `420270c0`, functional proof head
  `716cc1f1`, and clean ready mailbox `5814b810`.
- Strong pointwise closure:
  `ConcreteStructuredCodePointwiseRel.advance_supportedGlobal` transports the
  aligned static/resource caller stack through direct values and returns and
  preserves it across generated named and saturated call staging. Exact frame
  equalities are exposed by the direct-value and return classifiers rather
  than assumed by the global relation.
- Branch-complete relation: `ConcreteStructuredRunnableOutcome` combines
  ordinary code, named-call ready, saturated-call ready, and returned control
  with the exact aligned stack evidence needed by that branch. Ordinary code
  contains only its current-node admission and budget; no successor admission,
  callee evaluation, termination proof, or target execution path is stored.
- Module-wide theorem: `ConcreteStructuredRunnableGlobalOutcome` hides the
  active generated function, entry anchor, budget, and result ABI. It forgets
  to `ConcreteStructuredSupportedGlobalOutcome`, preserves exact observations,
  and advances every ordinary source step through a finite structured-Wasm
  path back to the supported global relation. Empty target paths are permitted
  only with strict `compilerStructuredControlRank` descent.
- Contracts: none. This slice changes W6 proof code and W6 roadmaps only; it
  changes no compiler/runtime semantics, concrete layout, symbolic-Wasm
  surface, or resident-helper signature.
- Acceptance: Talos setup at `0e05edbc`; Lean Beam update/sync/save at version
  16 with zero errors; direct `FirTalos.ConcreteStructuredSimulation` build
  (3,119 jobs); `git diff --check`; complete `make check` with 122 harness
  tests and native/V8 validation; and all 3,143 Talos jobs. No bug card was
  required.
- Result: `main` fast-forwards through the clean ready mailbox. W6 next widens
  the runnable control sum over the already proved external, lazy/cache, case,
  and effect laws, then packages the fresh source-local classifier into the
  public ranked finite-prefix simulation.

## Latest completed integration lease

- Milestone: `W6-SUPPORTED-GENERATED-CALL-STACK`.
- Integration owner: `wasm-proof`; this lease makes generated call entry and
  return recursively stable across arbitrarily nested supported callers.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`, rebased directly on `main` at `a03b034f`.
- Published stack: active-slice record `40bc4ca6`, functional proof head
  `e3f946b8`, Lean 4.33 suffix-contract alignment `bf92264b`, and clean ready
  mailbox `2b528bd0`.
- Static/dynamic alignment: `ConcreteStructuredSupportedFrameStack` retains
  each suspended caller's supported-function identity, canonical cache table,
  result ABI, and exact generated continuation-with-suffix proof. Its `Agrees`
  relation ties that stack constructor-by-constructor to the existing dynamic
  resource stack over the same source and structured-Wasm frames.
- Transition closure: direct and exactly saturated generated calls push both
  descriptions at entry. A yielded callee follows the established exact
  direct or matcher-label pop path, reconstructs the caller core, and restores
  `ConcreteStructuredSupportedGlobalOutcome`; the empty/root return is
  impossible for a nonterminal source successor. No rule evaluates a callee
  as a whole or assumes termination.
- Contracts: none. This slice changes W6 proof code and W6 roadmaps only; it
  changes no compiler/runtime semantics, concrete layout, symbolic-Wasm
  surface, or resident-helper signature.
- Acceptance: Talos setup at `0e05edbc`; Lean Beam update/sync/save with zero
  errors; direct `FirTalos.ConcreteStructuredSimulation` build (3,119 jobs);
  `git diff --check`; complete `make check` with 122 harness tests, 662 unique
  cases, 1,968/1,968 equal comparisons, 6,829 machine steps, and zero
  findings; and all 3,143 Talos jobs. No bug card was required.
- Result: `main` fast-forwards through the clean ready mailbox. W6 next proves
  the relation-wide pointwise advance theorem over direct values, staged and
  entered generated calls, and returns, then widens the dispatcher to the
  already proved external, lazy, case, effect, and ranked silent-step laws.

## Latest completed integration lease

- Milestone: `LEAN-4.33-UPGRADE`.
- Integration owner: `integration`; this was the special one-off release lane
  for moving the repository, Talos bridge, and published browser contracts to
  Lean 4.33.
- Integration branch/worktree: `upgrade/lean-4.33` in
  `.worktrees/lean-4.33`, based on `41cd4b29` and fast-forwarded to `main` at
  `476f001b`.
- Toolchain and compiler surface: all live FIR toolchains, trusted-source
  hashes, pass proofs, concrete-runtime proofs, generated-artifact validators,
  and package contracts now target Lean 4.33.0. The migration preserves the
  semantic Wasm ABI, concrete layouts, and resident-helper signatures while
  updating the versioned compact-Format contract to
  `lean-4.33-Std.Format.compact/v1`.
- Talos: FIR pins official-repository commit `0e05edbc` from
  `codex/update-lean-4-33`; the complete FIR/Talos cone passes all 3,143 jobs.
  Talos upstream PR #172 remains the follow-up for replacing that branch pin
  with a merged upstream revision.
- Verso: the compiler-neutral HTML producer is published at fork commit
  `eb8d2b8f` on `ejgallego/upgrade/fir-html-lean-4.33`. The checked package is
  a 187,855-byte zero-import module with 93 source functions and 631 resident
  helpers; its Wasm digest remains
  `ce63b4fd71abddda8aa5795a57ab7849666f8029b501a015ee3e3c714a3eec1c`.
  Upstreaming that producer surface is the follow-up that removes the fork
  branch pin.
- Acceptance: Lean Beam update/sync/save with zero errors on each migrated
  proof cone; `git diff --check`; complete `make check` with 122 unit tests,
  662 unique validation cases, and 1,968/1,968 equal comparisons; all 3,143
  Talos jobs; the deterministic artifact gate; and the published Verso HTML
  gate with 8/8 native/Wasm cases, bounded growth, 32 repeated calls, and
  malformed-input rejection. No bug card was required.
- Result: `main` and `origin/main` are `476f001b`. Every surviving feature lane
  must rebase on that shared 4.33 contract before continuing. Historical bug
  cards, completed leases, plans, and performance records retain their original
  4.32 provenance and are not live toolchain declarations.

## Latest completed integration lease

- Milestone: `W6-POINTWISE-SATURATED-CALL-CORE`.
- Integration owner: `wasm-proof`; this lease connects exactly saturated
  closure calls to the nonterminating pointwise core without evaluating a
  callee as a whole.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`, rebased directly on `main` at `bc30ac44`.
- Published stack: active-slice record `1e39b836`, functional proof head
  `fe962816`, and clean ready mailbox `0810738b`.
- Local staging: state-indexed current-node admission classifies generated
  exactly saturated calls at cost zero. One source staging step matches a
  reflexive target path and strictly decreases `compilerStructuredControlRank`.
- Dynamic entry: `ConcreteStructuredSaturatedCallReadyCoreRel.advance_enter`
  derives matcher selection, closure ownership consumption, captured/new
  argument assembly, and generated callee entry from the compiler and concrete
  runtime contracts. It pushes the saved caller resource scope and result ABI
  in one hereditary constructor and starts a fresh callee core.
- Return: saturated bind pop exposes the resumed compiler focus after the exact
  matcher-label unwind, restores the caller heap/cache/resource scope, and
  reconstructs the caller code core. No staging, entry, or pop rule assumes
  that the selected callee returns.
- Contracts: none. The slice changes W6 proof code, W6 roadmaps, and the W6
  mailbox only; it changes no compiler/runtime semantics, concrete layout,
  symbolic-Wasm instruction, or resident-helper signature.
- Acceptance: Lean Beam update/sync/save with zero errors and three linter
  warnings; direct `FirTalos.ConcreteStructuredSimulation` build (3,110 jobs);
  `git diff --check`; complete `make check` including 122 interpreter tests,
  662 unique validation cases, and 1,968/1,968 comparisons; Talos setup at
  `a01d01c`; and all 3,133 Talos jobs. The complete gate was repeated after the
  clean rebase. No bug card was required.
- Result: `main` fast-forwards through the ready mailbox. W6 next assembles the
  relation-wide one-source-step classifier/advance theorem, attaching fresh
  local admission only after a dynamic successor is known.

## Latest completed integration lease

- Milestone: `W6-POINTWISE-DIRECT-CALL-CORE`.
- Integration owner: `wasm-proof`; this lease connects generated named calls
  to the nonterminating pointwise core without evaluating a callee as a whole.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`, rebased directly on `main` at `0966e35f`.
- Published stack: active-slice record `62f6d358`, functional proof head
  `37f5f6bb`, and clean ready mailbox `0c4f2101`.
- Local admission: `ConcreteStructuredCodeStepAdmission` is now indexed by the
  current runtime and environment and admits a generated named call at exact
  current-step cost zero. It still contains no successor admission, future
  budget, dynamic result, endpoint, target path, or evaluation derivation.
- Direct-call closure: compiler-derived staging constructs the semantic and
  physical arguments plus exact target prefix and enters
  `ConcreteStructuredDirectCallReadyCoreRel`. The entry rule takes one source
  and one target step, pushes the caller scope, starts the callee core with
  empty local reuse facts, and records the declared callee-result refinement.
  Direct bind pop restores the caller core through the accepted resource
  transport law. No rule assumes that the callee terminates.
- Hereditary ABI invariant: active and suspended function-result kinds now
  live in the same direct/saturated constructors as their resource scopes.
  This prevents ABI metadata from disagreeing with the call protocol without
  introducing a parallel proof stack or execution certificate.
- Contracts: none. The slice changes W6 proof code, W6 roadmaps, and the W6
  mailbox only; it changes no compiler/runtime semantics, concrete layout,
  symbolic-Wasm instruction, or resident-helper signature.
- Acceptance: Lean Beam update/sync/save with zero errors; direct
  `FirTalos.ConcreteStructuredSimulation` build (3,110 jobs);
  `git diff --check`; complete `make check` including 122 interpreter tests;
  Talos setup at `a01d01c`; and all 3,133 Talos jobs. No bug card was required.
- Result: `main` fast-forwards through the ready mailbox. W6 next repeats this
  construction for exactly saturated closure calls, then assembles the
  relation-wide control sum and fresh successor-admission classifier.

## Latest completed integration lease

- Milestone: `W6-POINTWISE-LOCAL-ADMISSION`.
- Integration owner: `wasm-proof`; this corrective lease keeps the pointwise
  relation compatible with recursive and nonterminating source programs by
  removing future-execution evidence from admission.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`, rebased directly on `main` at `db76e35a`.
- Published stack: active-slice record `183b6573`, functional proof head
  `f812e73f`, and clean ready mailbox `369b25a0`.
- Accepted boundary: `ConcreteStructuredCodeStepAdmission` classifies only
  the current source node, supported operation family, and exact current-step
  allocation requirement. It stores no successor admission, future
  fact/budget transfer, execution path, endpoint, or evaluation derivation.
  An admission stack or future allocation reserve is explicitly excluded
  because it would encode state-dependent future execution and act as the
  certificate the main theorem is meant not to require.
- Preserved invariant: `ConcreteStructuredCodeCoreRel` combines the actual
  compiler focus, hereditary resource stack, and result-ABI compatibility
  independently of the current operation family. It projects exact
  observations and the compiler-derived control/stack relation. The direct
  value law constructs the exact finite target path and successor core; return
  classification remains terminal/direct-bind/saturated-bind.
- Contracts: none. The slice changes W6 proof code, W6 roadmaps, and the W6
  mailbox only; it changes no compiler/runtime semantics, concrete layout,
  symbolic-Wasm instruction, or resident-helper signature.
- Acceptance: Lean Beam update/sync/save with zero errors and one pre-existing
  warning; direct `FirTalos.ConcreteStructuredSimulation` build;
  `git diff --check`; complete `make check` including 122 interpreter tests;
  Talos setup at `a01d01c`; and all 3,133 Talos jobs. No bug card was required.
- Result: `main` fast-forwards through the ready mailbox. W6 next proves direct
  and saturated call staging, entry, and return against the core, attaching
  fresh local admission only after each dynamic successor is known.

## Latest completed integration lease

- Milestone: `W6-POINTWISE-ADMISSION-CORE`.
- Integration owner: `wasm-proof`; this lease replaces the first terminating
  hereditary-evaluator dependency with a source-only pointwise compiler
  relation.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`, rebased directly on `main` at `2d24f623` after the
  Verso HTML publication and mutated-constructor validation repair.
- Published stack: active-slice record `0191141b`, functional proof head
  `56a3e15d`, and clean ready mailbox `22204d0d`.
- Accepted admission: `ConcreteStructuredCodeAdmission` records structural
  source coverage, deterministic reuse-fact transfer, remaining allocation
  budget, covered source continuations, and return ABI compatibility. It
  contains no runtime step, final value or state, target path, or terminating
  evaluation derivation.
- Pointwise relation: `ConcreteStructuredCodePointwiseRel` combines the real
  compiler/adaptor focus, hereditary entry-relative resource stack, and
  source-only admission under one generated-function specification. Its root
  constructor starts at canonical empty stacks. The direct-value rule uses
  the production runtime law to construct the exact target path and complete
  successor relation. The return rule derives its dynamic lookup from the
  supplied successful source step and classifies the target as terminal,
  direct-bind, or saturated-bind using the existing recursive frame stack.
- Contracts: none. The slice changes W6 proof code, W6 roadmaps, and the W6
  mailbox only; it changes no compiler/runtime semantics, concrete layout,
  symbolic-Wasm instruction, or resident-helper signature.
- Acceptance: post-rebase Lean Beam update/sync/save with zero errors; direct
  `FirTalos.ConcreteStructuredSimulation` build (3,110 jobs);
  `git diff --check`; complete `make check` including 122 unit tests and the
  native/LCNF/Wasm validation gates; Talos setup at `a01d01c`; and all 3,133
  Talos jobs. No bug card was required.
- Result: `main` fast-forwards through the ready mailbox. W6 next carries
  source-only continuation admission through direct and saturated call
  push/pop, then widens the relation-wide `advance` dispatcher to the already
  proved external, lazy, case, effect, and ranked silent-step families.

## Latest completed integration lease

- Milestone: `W6-POINTWISE-RESOURCE-STACK`.
- Integration owner: `wasm-proof`; this lease assembles the exact call-scope
  resource laws into the recursive stack component of the finite-prefix
  simulation relation.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`, rebased directly on `main` at `bf00e5c9` after the
  grow/delete release-fixture acceptance.
- Published stack: active-slice record `d87858db`, functional proof head
  `1f57b48d`, and clean ready mailbox `c3ba7830`.
- Accepted proof: `ConcreteStructuredSuspendedResourceStack` chains saved
  caller scopes so every adjacent caller/callee pair shares the exact
  runtime/store/witness entry boundary by construction.
  `ConcreteStructuredResourceStack` pairs that chain with the active scope;
  its `frameRel` projection transports every saved caller to the current heap
  and reconstructs the accepted `ConcreteStructuredFrameRel`.
- Transition closure: generated direct and saturated entries push the unified
  resource stack. Both bind-return protocols compose the active callee into
  the saved caller, erase exactly the result fact, restore the caller's outer
  scope, expose the older chain, and construct the successor
  `ConcreteStructuredStackRel`. No whole-callee evaluation or termination
  premise is introduced.
- Contracts: none. The slice changes W6 proof code, W6 roadmaps, and the W6
  mailbox only; it changes no compiler/runtime semantics, concrete layout,
  symbolic-Wasm instruction, or resident-helper signature.
- Acceptance: pre- and post-rebase Lean Beam update/sync/save with zero
  errors; direct `FirTalos.ConcreteStructuredSimulation` build (3,110 jobs);
  `git diff --check`; Talos setup at `a01d01c`; all 3,133 Talos jobs; and
  complete post-rebase `make check` with 653/653 native/LCNF/V8 cases,
  1,968/1,968 equal backend comparisons, 662 unique cases, 6,829 interpreter
  steps, 124 tag floors, 233 semantic domains, and zero findings. No bug card
  was required.
- Result: `main` fast-forwards through the ready mailbox. W6 next defines the
  source-only pointwise admission classifier over the combined
  control/resource relation and begins its local successor-preservation proof.

## Latest completed integration lease

- Milestone: `W7-VERSO-HTML-PUBLICATION`.
- Integration owner: `wasm-gen`; this lease closes the real Verso complete-HTML
  compilation boundary and publishes the reusable package before W7 begins the
  generic package-tooling backlog.
- Integration branch/worktree: `wasm/generation` in
  `.worktrees/wasm-generation`, rebased directly on `main` at `260ce30a` after
  the accepted pointwise-resource-stack proof and grow/delete fixture slices.
- Published stack: generation-ready helper commit `57ae699e`, package source
  head `8c7dfdd7`, and clean ready mailbox `22540610`.
- Accepted generation: FIR captures the real
  `VersoSlides.Pretty.formatHtmlForRuntime` final-LCNF closure from clean Verso
  revision `2ee1c804`, preserving upstream specializations. The closure has 128
  captured declarations, 31 reviewed externals, 93 retained source functions,
  631 resident helpers, 724 complete functions, zero runtime operations or lazy
  initializers, and three resident globals.
- Resident frontier: generic selection adds `Array.pop`, `UInt32.decEq`,
  `String.append`, `String.push`, `String.Pos.next`, and `String.decodeChar`.
  Partial String internalization now links only supported operations actually
  present in a closure; the historical strict frontier remains stable. These
  signatures are generation-ready and their W6 concrete refinements remain a
  separate bridge milestone.
- Package: API `fir.prettyM.html.browser/v1` accepts compact Lean 4.32
  `Std.Format` plus `Array TaggedAnnotation` and returns a copied
  `EscapedHtmlString` under `verso-token-html/v1`. The 187,855-byte complete
  Wasm has SHA-256
  `ce63b4fd71abddda8aa5795a57ab7849666f8029b501a015ee3e3c714a3eec1c`,
  zero imports, five function exports, and module-owned memory. The immutable
  directory is
  `integration/verso-html/_build/verso-html-packages/8c7dfdd79f89-2ee1c804106b-f991e46bebfce2bb4e45`.
- Concrete validation repair: constructor fields are physically untyped and
  may change from an object address to a tagged immediate after `objectSet`.
  The artifact observer now updates descriptor field kinds after mutation,
  fixing `FIR-BUG-wasm-none-concrete-validation-tagged-ctor-field`; it changes
  no concrete-runtime or semantic ABI contract.
- Acceptance: Lean Beam checkpoints with zero diagnostics; deterministic
  double publication; SHA256SUMS, Node, native/Wasm 8/8, malformed-input,
  bounded-growth, repeated-call, Verso-validator, and Chrome checks; complete
  resident artifact gate including 608/653 concrete products with 45 explicit
  ByteArray blocks and deterministic 44/44 concrete artifacts; `make check`
  with 653 source/V8 cases, 9 direct machines, 662 unique cases, and
  1,968/1,968 equal comparisons; and all 3,133 Talos jobs.
- Result: `main` fast-forwards through the ready mailbox. The Verso source owner
  should replace character-at-a-time immutable HTML escaping before the
  deferred one-MiB throughput gate. W7 next takes the small generic immutable
  package verifier/atomic-installer slice, then descriptor-driven browser
  package generation and a shared benchmark schema.

## Latest completed integration lease

- Milestone: `VALIDATION-GROW-DELETE-RELEASE-S5C`.
- Integration owner: `test-fixtures`; the user authorized this lane to take
  the integration role when needed.
- Integration branch/worktree: `validation/closure-ownership-fixtures` in
  `.worktrees/validation-closure-ownership-fixtures`, rebased directly on
  `main` at `43a5c14e` after the accepted W6 pointwise call-resource stack.
- Published stack: planning seed `e90d24c6`, functional fixture/coverage head
  `072e90d7`, and clean ready mailbox `0deba715`.
- Candidate search: the first big-to-small-to-big candidate was rejected by
  the dominance filter. Source-generated execution did not retain capacity,
  and the interpreter model has no independent capacity state, so that history
  could not support a semantic coverage claim.
- Accepted fixtures: a two-field seed/leaf owner grows to a three-scalar-field
  variant while a leaf alias survives outside. Both paths execute one `del`.
  Unique-owner release makes the leaf reusable and executes one later `oset`;
  retaining the owner stops release before the leaf and forces allocation with
  zero `oset`. Complete 66- and 74-step traces pin the distinction.
- Contracts: none. This is fixture, exact-trace, oracle-floor,
  coverage-policy, roadmap, and validation documentation work only. It neither
  changes nor requests compiler, W6, W7, proof, concrete-runtime, symbolic-Wasm,
  or resident-helper work.
- Acceptance: Lean Beam update/sync/save with zero diagnostics; focused pinned
  native/LCNF and native/LCNF/real-V8 matrices; `lake --rehash build`; repeated
  `git diff --check`; and complete `make check` both before and after rebasing
  over W6. The accepted baseline has 653/653 source native/LCNF/V8 cases, 9/9
  direct ownership machines, 1,306 native-oracle witnesses, 662 unique cases,
  1,315 tier cases, 1,968/1,968 equal indexed comparisons, 6,829 interpreter
  steps, 124 tag floors, 233 semantic domains, and zero findings. No bug card
  was required.
- Result: `main` fast-forwards through the ready mailbox and the fixture lane
  is released. The next fixture slice uses the same coverage-guided filter to
  select the smallest undominated lifetime interaction outside the now-covered
  replacement/release matrix; native Lean remains the admission oracle.

## Latest completed integration lease

- Milestone: `W6-POINTWISE-CALL-RESOURCES`.
- Integration owner: `wasm-proof`; this lease closes the resource half of the
  non-terminating direct and saturated call boundaries.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`, based directly on `main` at `5d4a9b3d` after the
  recursive structured-stack acceptance.
- Published stack: active-slice record `54ddd98f`, functional proof head
  `382998c4`, and clean ready mailbox `eeac39b6`.
- Accepted proof: `ConcreteStructuredCurrentResource` packages the active
  function's entry-relative facts, allocation budget, cache, ownership, and
  closure-ABI invariants. `ConcreteStructuredResourceScope` exposes the exact
  runtime/store/witness triple at generated function entry. Direct and
  saturated calls preserve the suspended caller and start a fresh callee
  scope at that exact boundary.
- Return composition: the common certificate-free `restoreCaller` theorem
  folds an arbitrary finite callee resource evolution into the suspended
  caller, provided the returned value is related and the generated local write
  succeeds. Both direct and saturated return protocols now erase exactly the
  bound result fact, restore the caller's complete resource invariant, and pop
  the structural frame. No callee evaluation, termination premise, target
  path, or body certificate is assumed.
- Contracts: none. The slice changes W6 proof code, W6 roadmaps, and the W6
  mailbox only; it changes no compiler/runtime semantics, concrete layout,
  symbolic-Wasm instruction, or resident-helper signature.
- Acceptance: Lean Beam update/sync/save with zero errors; direct build of
  `FirTalos.ConcreteStructuredSimulation` (3,110 jobs); `git diff --check`;
  Talos setup at `a01d01c`; all 3,133 Talos jobs; and complete `make check`
  with 651/651 native/LCNF/V8 cases, 1,962/1,962 equal backend comparisons,
  660 unique cases, 6,689 interpreter steps, 122 tag floors, 227 semantic
  domains, and zero findings. No bug card was required.
- Result: `main` fast-forwards through the ready mailbox. W6 next indexes the
  exact active and suspended scopes as a recursive resource stack over
  `ConcreteStructuredFrameRel`, then starts the source-only pointwise
  admission classifier and relation-wide successor preservation proof.

## Latest completed integration lease

- Milestone: `W6-POINTWISE-RECURSIVE-STACK`.
- Integration owner: `wasm-proof`; this lease adds the recursive saved-frame
  component required by the certificate-free finite-prefix simulation.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`, rebased directly on `main` at `414c68cd` after the
  repeated-child release-fixture acceptance.
- Published stack: active-slice record `a223642b`, functional proof head
  `3a0508ae`, and clean ready mailbox `79fb8347`.
- Accepted proof: `ConcreteStructuredFrameRel` recursively relates suspended
  source binds to the exact generated direct-call frame or saturated
  call-plus-matcher-label protocol. The head carries the caller's expected ABI
  kind and every saved caller is related to the current runtime, concrete
  store, and witness rather than a frozen entry heap. The complete stack
  transports across accumulated runtime effects and classifies a related
  finite-prefix yield as terminal, direct-bind, or saturated-bind control
  without a callee evaluation or termination premise.
- Control closure: `ConcreteStructuredStackRel` joins the frame evidence to all
  ten local compiler-control protocols. Stack-lifted theorems cover named and
  saturated call staging, generated entry, and both return protocols.
  Saturated entry additionally transports older callers across the real
  matcher/closure-consumption update and establishes the generated callee's
  cache frame; callers provide no target program, path, or selection
  certificate.
- Contracts: none. The slice changes W6 proof code, W6 roadmaps, and the W6
  mailbox only; it changes no compiler/runtime semantics, concrete layout,
  symbolic-Wasm instruction, or resident-helper signature.
- Acceptance: Lean Beam update/sync/save with zero errors; forced direct build
  of `FirTalos.ConcreteStructuredSimulation`; `git diff --check` before and
  after rebase; Talos setup at `a01d01c`; all 3,133 Talos jobs; and complete
  post-rebase `make check` with Lean examples and interpreter/Wasm validation.
  No bug card was required.
- Result: `main` fast-forwards through the ready mailbox. W6 next adds the
  parallel resource stack and source-only pointwise admission invariant,
  preserving fact maps, allocation budget, closure ABI, and admission at each
  successor without wrapping the terminating hereditary evaluator. Target-only
  case-label control and the relation-wide `advance` assembly follow.

## Latest completed integration lease

- Milestone: `VALIDATION-REPEATED-CHILD-RELEASE-S5B`.
- Integration owner: `test-fixtures`; the user authorized this lane to take
  the integration role when needed.
- Integration branch/worktree: `validation/closure-ownership-fixtures` in
  `.worktrees/validation-closure-ownership-fixtures`, rebased directly on
  `main` at `1fc7982e` after the accepted W6 saturated-control proof stack and
  again over the integration-lease record at `69c2fd5a`.
- Published stack: planning seed `3f5e60aa`, fixture commit `b9941b62`,
  functional coverage/docs head `3faa01a8`, and resolved clean mailbox
  `e47139b6`.
- Accepted fixtures: one retained leaf occupies both object fields and also
  survives outside. The unique-owner path releases both fields and then
  reuses the leaf; the shared-owner path stops before either field, preserves
  both originals, and allocates the later leaf update. Complete 62- and
  64-step traces pin the distinct projection, increment, decrement,
  constructor, branch, and `oset` paths.
- Selection policy: adversarial ownership candidates now use pairwise factor
  coverage plus mandatory three-way coverage for alias multiplicity, release
  stop boundary, and surviving alias. Portable observations and complete
  executed path signatures eliminate dominated candidates; this adds no new
  generator or orchestration layer.
- Contracts: none. This is fixture, exact-trace, oracle-floor,
  coverage-policy, roadmap, and validation documentation work only.
- Acceptance: Lean Beam update/sync/save with zero diagnostics; focused
  native/LCNF and native/LCNF/real-V8 matrices; `lake --rehash build`; repeated
  `git diff --check`; and complete `make check` both before and after the W6
  rebase. The accepted baseline has 651/651 source native/LCNF/V8 cases, 9/9
  direct ownership machines, 1,302 native-oracle witnesses, 660 unique cases,
  1,311 tier cases, 1,962/1,962 equal indexed comparisons, 6,689 interpreter
  steps, 122 tag floors, 227 semantic domains, and zero findings. No bug card
  was required.
- Result: `main` fast-forwards through the resolved mailbox and the fixture
  lane is released. S5 remains active; coverage-guided selection next targets
  the smallest undominated retained-capacity or grow/delete ownership pair.

## Latest completed integration lease

- Milestone: `W6-SATURATED-PER-STEP-RANK`.
- Integration owner: `wasm-proof`; this short lease closes the final missing
  per-source-step saturated-closure control boundary and establishes the
  structured silence rank used by the forthcoming unified simulation.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`, rebased directly on `main` at `5dfa5778` after the
  mapped-owner proof and recursive-release fixture acceptances.
- Published stack: active-slice record `cd1f713c`, saturated staging proof
  `6d6a34a2`, functional head `fc86daf1`, and ready mailbox `a76c343a`.
- Accepted proof: `ConcreteStructuredControlRel` now has ten constructors.
  The first saturated-call source step stages `.invokeValue` against a
  reflexive target path; the second consumes the closure against an exact
  compiler-derived matcher, capture/argument, and generated-callee-entry path.
  The proof returns the evolved cache frame and matcher store/capacity
  transports and accepts no target program, path, or selection certificate.
- Rank: `compilerStructuredControlRank` is a source-state-only measure that
  combines the code/invocation phase with recursive silence depth. It strictly
  decreases for empty-argument staging, persistent ownership erasure, and
  nested default-only case erasure; the latter now has its own exact
  one-source/zero-target transition theorem.
- Contracts: none. The stack changes only W6-owned proof code and roadmap
  documentation; it changes no shared semantic, concrete-runtime,
  resident-helper, or symbolic-Wasm contract.
- Acceptance: `git diff --check`; post-rebase Lean Beam update/sync with zero
  errors; all 3,133 Talos jobs; and complete post-rebase `make check` with
  649/649 source, LCNF, and V8 cases, 9/9 direct-machine cases, 1,947/1,947
  three-backend results, 1,956/1,956 indexed equal comparisons, 658 unique
  cases, 6,563 machine steps, 116 tag floors, 221 semantic domains, and zero
  findings. Bug-card and trusted-assumption audits pass; no bug card was
  required.
- Result: `main` fast-forwards through the ready mailbox. W6 next defines the
  non-terminating pointwise source-admission/resource relation and assembles
  the relation-wide per-source-step `advance` theorem from the ten local
  control rules and this rank.

## Latest completed integration lease

- Milestone: `VALIDATION-RECURSIVE-RELEASE-S5A`.
- Integration owner: `test-fixtures`; the user previously authorized this
  lane to take the integration role when needed, and the owner waited for the
  preceding mapped-owner proof lease to be accepted and released.
- Integration branch/worktree: `validation/closure-ownership-fixtures` in
  `.worktrees/validation-closure-ownership-fixtures`, rebased directly over
  the accepted proof head and this lease record at `b3be5d1a`.
- Published stack: planning seed `a42a9fec`, functional head `f25d2678`, and
  resolved clean handoff `476b0634`.
- Accepted fixtures: source-compiled recursive release compares a unique
  owner/child chain whose surviving leaf becomes reusable with an outside
  child alias that stops recursion and forces the later leaf update to allocate
  while preserving the original leaf. Complete 63- and 69-step form traces,
  exact ownership counts, and exact `Nat.add` traces retain the distinction.
- Contracts: none. This is fixture, exact-trace, oracle-floor, coverage-policy,
  roadmap, and validation documentation work only.
- Acceptance: Lean Beam update/sync/save with zero diagnostics; focused
  native/LCNF and native/LCNF/real-V8 matrices; dependency builds;
  `git diff --check`; and complete post-proof `make check` with 122 harness
  tests, 649/649 source native/LCNF/V8 cases, 9/9 direct ownership machines,
  1,298 native-oracle witnesses, 658 unique cases, 1,307 tier cases,
  1,956/1,956 equal indexed comparisons, 6,563 interpreter steps, all 116 tag
  floors and 221 semantic domains satisfied, and zero findings, obligation
  failures, or telemetry failures. No bug card was required.
- Result: `main` fast-forwards through the resolved handoff and is pushed before
  further fixture work. S5 remains active; the next compact slice targets
  repeated child aliases and observable release order rather than scalar breadth.

## Latest completed integration lease

- Milestone: `ELIMDEAD-GENERIC-MAPPED-OWNER-READINESS`.
- Integration owner: `lcnf-proof`; the user assigned this lane the temporary
  integration role, and the owner accepted the clean mapped-owner readiness
  handoff after its exact post-W6 rebase gate passed.
- Integration branch/worktree: `proof/simpcase` in
  `.worktrees/proof-simpcase`, rebased directly on `main` at `d6599de8` after
  the W6 external-evidence acceptance and this lease's planning record.
- Published stack: active-slice record `7fc0cd10`, functional head `e54f39d4`,
  and exact validated handoff `38ad84f4`.
- Accepted proof: an arbitrary allocated target prefix covered by
  compiler-live heap binders now derives `TargetMappedOwnerPrefix` uniformly
  from `EnvRelOn`. The retained-prefix reset and reuse clients consume this
  interface instead of manually reconstructing a singleton address mapping.
- Contracts: none. This is proof-only compiler-readiness strengthening; it
  changes no interpreter, runtime, Wasm, or shared semantic contract.
- Acceptance: Lean Beam saves with zero errors; the 34-job dependency cone;
  `git diff --check`; and complete post-rebase `make check` with 122 harness
  tests, 647/647 source and V8 cases, 9/9 direct cases, 656 unique cases,
  1,950/1,950 equal comparisons, 6,431 machine steps, all 106 tag floors and
  215 semantic domains satisfied, zero findings, 129 valid bug cards, and
  exactly one registered trusted axiom. The changed proof files contain no
  `sorry` or `admit`.
- Result: `main` fast-forwards through the validated handoff and is pushed
  before further lane work. The lease is released; the LCNF lane next rebases
  on the acceptance record and replaces the remaining fixture-specific
  reset/reuse classification with generic local operation-shape and ownership
  premises.

## Latest completed integration lease

- Milestone: `W6-CERTIFICATE-FREE-EXTERNAL-EXECUTION`.
- Integration owner: `wasm-proof`; this short lease lands the concrete
  execution proof behind the structured external-call protocol.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`, rebased directly on `main` at `e2064631` after the
  tail-ownership fixture acceptance.
- Published stack: active-slice record `49723b1c`, functional head `145f07cc`,
  and ready mailbox `d3f1a764`.
- Accepted proof: a budgeted pure external frame now derives the typed
  physical arguments, exact concrete external request/result relation,
  evolved store and runtime witness, and residual budget from the existing
  `Nat`, `Int`, and scalar runtime laws. The public progression theorem needs
  no caller-supplied target execution or representation certificate.
- Protocol result: a complete admitted external `let` advances exactly three
  source steps and `targetArguments.length + 2` target steps, returns to the
  compiled continuation, and preserves the exact trace, frames, joins,
  environment, concrete runtime relation, and reduced resource frame.
- Contracts: none. The stack changes only W6-owned proof code and roadmap
  documentation; it changes no shared semantic, concrete-runtime,
  resident-helper, or symbolic-Wasm contract.
- Acceptance: Lean Beam update/sync/save at version 8 with zero errors;
  dependency-cone build of `FirTalos.ConcreteStructuredSimulation`;
  `git diff --check`; all 3,133 Talos jobs; and complete post-rebase
  `make check` with 647/647 source and V8 cases, 9/9 direct cases,
  1,941/1,941 three-backend results, 1,950/1,950 indexed equal comparisons,
  656 unique cases, 6,431 machine steps, 106 tag floors, 215 semantic domains,
  and zero findings. No bug card was required.
- Result: `main` fast-forwards through the ready mailbox. W6 next adds the
  pre-entry saturated-closure staging boundary and then assembles the unified
  ranked per-source-step simulation theorem.

## Latest completed integration lease

- Milestone: `VALIDATION-TAIL-OWNERSHIP-S4-B1`.
- Integration owner: `test-fixtures`; the user authorized this lane to take
  the short lease, and the owner accepted the clean S4/B1 handoff after its
  exact post-rebase cross-lane gate passed.
- Integration branch/worktree: `validation/closure-ownership-fixtures` in
  `.worktrees/validation-closure-ownership-fixtures`, rebased directly on
  `main` at `05ebaab1` after the W6 structured-external proof checkpoint.
- Published stack: planning seed `3fc08865`, functional head `2f93f54e`, and
  ready mailbox `7daee1fa`.
  Two fixtures carry a nested `ByteArray`/`String` owner through three
  tail-recursive mutations. The unique-transfer path performs three `oset`
  updates; the outside-aliased path allocates its first replacement and reuses
  it for the remaining two updates.
- Contracts: none. The stack changes only fixture source, exact trace,
  validation-policy, roadmap, documentation, and this lane's mailbox files;
  it changes no W6, W7, LCNF-proof, or shared semantic contract.
- Acceptance: Lean Beam update/sync/save with zero diagnostics; targeted
  importer build; focused native/LCNF and native/LCNF/real-V8 checks;
  `git diff --check`; and complete pre-rebase and post-rebase `make check`.
  The final candidate has 647/647 source and V8 cases, 9/9 direct cases, 656
  unique cases, 1,950/1,950 equal comparisons, 6,431 machine steps, 106 tag
  floors, 215 conjunctive domains, 1,294 native-oracle witnesses, and zero
  findings.
- Coordination: the W6 checkpoint consumed as the rebase base is already on
  `main`; the fixture stack owns no proof/runtime/compiler file. Other lanes
  rebase on this acceptance before their next integration handoff.
- Result: `main` fast-forwards through this completion record and is pushed
  before further fixture work. S4/B1 is landed/released; the fixture lane next
  designs S5 recursive release/reuse while keeping W7's large-depth tail
  transform probe separate.

## Latest completed integration lease

- Milestone: `W6-STRUCTURED-EXTERNAL-PROTOCOL`.
- Integration owner: `wasm-proof`; this short lease lands the complete
  per-source-step control protocol for generated pure external calls.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`, rebased directly on `main` at `d6a77d9d` after the
  repeated-capture read fixture release.
- Published stack: active-slice record `37c5d31a`, functional head `6ffb9528`,
  and ready mailbox `989ddf2c`.
- Accepted proof: production compilation now advances from ordinary code
  focus through exact compiled-argument staging, a resolved imported call,
  result-local binding, and back to ordinary code focus. The target path
  lengths are respectively the compiled argument count, one, and one, and
  each boundary preserves the concrete store/runtime witness, caller frames,
  local/environment relation, and exact observation law.
- Theorem boundary: `ConcreteStructuredControlRel` now has nine constructors.
  `ConcreteExternalCallEvidence` isolates the remaining runtime/resource
  construction used by the imported-call transition; it is internal proof
  evidence, not a compiler certificate or a premise of the intended public
  correctness theorem.
- Contracts: none. The stack changes only W6-owned proof staging and roadmap
  documentation; it does not change a shared semantic, concrete-runtime,
  resident-helper, or symbolic-Wasm contract.
- Acceptance: Lean Beam update/sync/save with zero errors; forced and
  dependency-cone Lean builds; `git diff --check`; all 3,133 Talos jobs; and
  complete post-rebase `make check` with 645/645 source and V8 cases, 9/9
  direct cases, 1,935/1,935 three-backend results, 1,944/1,944 indexed equal
  comparisons, and zero findings. One native-oracle build timeout was
  transient and the exact rerun passed.
- Result: `main` fast-forwards through the ready mailbox. W6 next derives the
  external-call evidence uniformly from the existing `Nat`, `Int`, and scalar
  runtime laws plus the concrete budget frame, then closes saturated-closure
  pre-entry and assembles the ranked simulation theorem.

## Latest completed integration lease

- Milestone: `VALIDATION-CAPTURE-TOPOLOGY-S3B`.
- Integration owner: `test-fixtures`; the user authorized this lane to act as
  integration owner when needed, and the owner accepted the clean S3b handoff
  after its post-rebase cross-lane gate passed.
- Integration branch/worktree: `validation/closure-ownership-fixtures` in
  `.worktrees/validation-closure-ownership-fixtures`, rebased directly on
  `main` at `473d5ec3` after W7 HitScene v2 acceptance.
- Published stack: functional head `f997949f`, ready mailbox `6e65f2aa`, and
  exact validated lease candidate `fd2b8b6d`.
  Four fixtures compare ignored versus read paths for one ByteArray and one
  allocated constructor/String object repeated across two closure captures
  while a third alias remains outside.
- Contracts: none. The stack changes only fixture, exact trace,
  validation-policy, roadmap, documentation, and this lane's mailbox files;
  it changes no W6, W7, LCNF-proof, or shared semantic contract.
- Acceptance: Lean Beam zero-diagnostic checkpoint; focused native/LCNF and
  native/LCNF/real-V8 checks; `git diff --check`; and complete post-rebase
  `make check` with 645/645 source and V8 cases, 9/9 direct cases, 654 unique
  cases, 1,944/1,944 equal comparisons, 6,184 machine steps, 98 tag floors,
  209 conjunctive domains, 1,290 native-oracle witnesses, and zero findings.
- Coordination: the W7 package consumed by this stack is already on `main`.
  The ready LCNF-proof and W6 mailboxes remain untouched on older bases and
  must rebase before their next integration handoff.
- Result: `main` fast-forwards through this completion record and is pushed
  before further fixture work. S3b is landed/released, and the fixture lane
  proceeds to S4/B1 tail ownership from the accepted alias vocabulary.

## Latest completed integration lease

- Milestone: `W7-ILLUMINATE-HITSCENE-V2`.
- Integration owner: `wasm-gen`; the user approved the published sequence and
  this short lease lands the completed W7 package before the independently
  unblocked Verso HTML slice begins.
- Integration branch/worktree: `wasm/generation` in
  `.worktrees/wasm-generation`, rebased directly on `main` at `be7eb514` after
  the capture-topology fixture release.
- Published stack: HitScene v2 source/package head `74e4be48`, concrete-host
  refinement consumer `f8adc6e6`, exact topology blocker refresh `53c8b917`,
  and ready mailbox `8db5b5a6`.
- Artifact: immutable package
  `integration/illuminate-hit-scene/_build/illuminate-hit-scene-7daab5f2bb96f121`
  records exact Illuminate source `88dcfee8`, layout
  `lean-4.32-Illuminate.HitScene/v2`, a 46,089-byte complete Wasm module with
  SHA-256 `06708aac339cd7f6f7fcbe7c973dc29125e263925635d0311a0571d4428e97b7`,
  zero imports, six function exports, and module-owned memory.
- Contracts: no shared Lean semantic, symbolic Wasm, concrete-runtime, or
  resident-helper contract changes. W7 consumes the accepted directional
  closure-projection refinement; the package advances only its client input
  layout to v2 while retaining browser API and ownership v1.
- Acceptance: deterministic fresh frontier and complete-link publication;
  checksums; 301 fixture and 10,000 flat-frontier queries; production and
  diagnostic paths; `git diff --check`; complete `make check` with 650 unique
  cases and 1,932/1,932 equal comparisons; all 3,133 Talos jobs; and the full
  W7 artifact gate with 600/641 concrete executions plus the exact 41-case
  ByteArray blocker inventory.
- Result: `main` fast-forwards through this completion record. Illuminate may
  consume the immutable path while W7 starts the separately sourced Verso HTML
  zero-import package; the integration lease is released immediately.

## Latest completed integration lease

- Milestone: `VALIDATION-CAPTURE-TOPOLOGY-S3A`.
- Integration owner: `test-fixtures`; the user authorized this lane to take an
  integration lease when needed, and the owner accepted the clean exact
  candidate after its post-rebase integration gate passed.
- Integration branch/worktree: `validation/closure-ownership-fixtures` in
  `.worktrees/validation-closure-ownership-fixtures`, rebased directly on
  `main` at `348977fe` after the W6 unified-control-relation checkpoint.
- Published stack: functional head `b5080fe3`, ready mailbox `ea68bbe2`, and
  exact validated lease candidate `822cc248`.
  It adds a returned-versus-consumed pair in which one `ByteArray` occupies
  two partial-application capture slots while a third alias survives outside
  the closure. Exact 22/27-transition LCNF traces prove real `pap`/`fvar`
  execution, opposite branch paths, and zero/one `ByteArray.set!` dispatches.
- Contracts: none. The candidate changes only fixture, trace,
  validation-policy, roadmap, documentation, and this lane's mailbox files;
  no W6, W7, LCNF-proof, or shared semantic contract is changed.
- Acceptance: clean ready handoff; Lean Beam zero-diagnostic checkpoint;
  targeted importer rebuild; focused native/LCNF and native/LCNF/real-V8
  checks; `git diff --check`; complete post-rebase `make check` with 122
  harness tests, 650 unique cases, 641/641 source and V8 cases, 9/9 direct
  cases, 1,932/1,932 equal comparisons, 6,050 machine steps, all 96 tag floors
  and 201 semantic domains satisfied, and zero findings.
- Result: `main` fast-forwards atomically through this completion record and is
  pushed before S3b begins. Other lanes rebase before their next handoff; the
  fixture lane proceeds to ignore/read topology from the landed base.

## Latest completed integration lease

- Milestone: `VALIDATION-CLOSURE-MULTIPLICITY-S2`.
- Integration owner: `test-fixtures`; the user authorized this lane to take the
  short lease needed to land its green fixture stack promptly, and the owner
  accepted the exact candidate after the complete integration gate passed.
- Integration branch/worktree: `validation/closure-ownership-fixtures` in
  `.worktrees/validation-closure-ownership-fixtures`, rebased directly on
  `main` at `2d96f7a1`.
- Published stack: functional head `0fec2b0f`, ready mailbox `2be3d484`, and
  exact validated lease candidate `9b16ee55`.
  It completes the zero/one/two/three-use mixed-closure matrix, pins exact
  14/36/62/87-step LCNF traces, distinguishes shared-intermediate and
  unique-final applications, and raises the native-oracle and coverage floors.
- Coordination repair: update the mailbox routing README from the historical
  `validation/float-corpus` branch to the actual fixture branch. This changes
  no executable or semantic surface.
- Contracts: none. The functional candidate changes only fixture, trace,
  validation-policy, roadmap, and documentation files; no W6, W7, LCNF-proof,
  or shared semantic contract is changed.
- Acceptance: clean tree; Lean Beam zero-diagnostic checkpoint; focused
  native/LCNF and native/LCNF/real-V8 checks; `git diff --check`; complete
  `make check` with 122 harness tests, 648 unique cases, 639/639 source and V8
  cases, 9/9 direct cases, 1,926/1,926 equal comparisons, 6,001 machine steps,
  all 88 tag floors and 193 semantic domains satisfied, and zero findings.
- Result: `main` fast-forwards atomically through this completion record and is
  pushed before S3 begins. Other lanes rebase before their next handoff; the
  fixture lane proceeds to S3 capture alias topology from the landed base.

## Latest completed integration lease

- Milestone: `VALIDATION-SEMANTIC-FIDELITY-BASELINE`.
- Integration owner: `test-fixtures`; the user assigned this lane the lease and
  it landed the prepared native-oracle fixture and executable-roadmap stack
  before S2 closure-multiplicity work begins.
- Integration branch/worktree: `validation/closure-ownership-fixtures` in
  `.worktrees/validation-closure-ownership-fixtures`, rebased directly on
  `main` at `cf0b6e89`.
- Published stack: functional head `b20eb671`, ready mailbox `b3ff066f`, and
  exact validated lease candidate `1d1a6883`.
  It admits the 32 scalar closures, mixed one-use/two-use ownership pair, and
  outside-alias ByteArray read/mutate pair; retains exact LCNF evidence; and
  publishes the executable semantic-fidelity roadmap and coverage ratchets.
- Contracts: none. The candidate changes only test-fixture, validation-plan,
  discrepancy-record, and documentation files; it does not change W6, W7,
  LCNF-proof, or shared semantic surfaces. Other lanes rebase after landing,
  but no proof or compiler contract is invalidated.
- Validation: clean tree; `git diff --check`; complete `make check` with 122
  harness tests, 646 unique cases, 637/637 native/LCNF/V8 cases, 9/9 direct
  machine cases, 1,920/1,920 equal comparisons, 5,900 machine steps, all 73
  tag floors and 183 conjunctive domains satisfied, and zero findings.
- Result: `main` fast-forwards atomically through this completion record. Other
  lanes rebase before their next handoff; the fixture lane starts S2 from the
  landed base.

## Latest completed integration lease

- Milestone: `W7-VERSO-FLAT-PUBLICATION-AND-HTML-PROBE`.
- Integration owner: `wasm-gen`; the lease published the accepted Flat
  package source pin and preserved the complete-HTML boundary as a reproducible
  fail-closed diagnostic.
- Integration branch/worktree: `wasm/generation` in
  `.worktrees/wasm-generation`, rebased directly on `main` at `71890121`.
- Published stack: Flat pin `c852e06a`, HTML functional head `95ccd21c`, and
  ready mailbox `1002e638`.
- Flat artifact: the immutable package
  `a4dce92bc6e1-3dbc9ef4fa5a-7d16ade417a24f50058e` contains a 154,635-byte
  zero-import module with SHA-256 `60a70d63a38d230f37c04e1a88bad264a69cd9b23215b1ba859bd6dd125f0b0e`.
  Deterministic publication, checksums, Node, Chrome, and the Verso validator
  pass. Its exact FIR source commit is remotely reachable from
  `origin/publish-verso-flat-a4dce92b`.
- HTML finding: module-wise postponed capture compiles the exact published
  `formatHtmlForRuntime` source quickly and emits a stable 32,407-byte base
  module. Resident linking correctly rejects its 52-name precompiled-core
  frontier. The source needs an explicit specialized HTML state monad/join and
  escaping loop before zero-import publication; the boundary is recorded by
  `FIR-BUG-impure-none-generated-external-source-ancestor`.
- ABI finding: the actual HTML physical signature is
  `[tobject, object, tobject, tobject, tobject] -> object`; the annotation Array
  parameter is physically `object`.
- Contracts: no shared semantic, concrete-runtime, resident-helper, existing
  artifact, or browser API contract changed.
- Validation: Lean Beam and focused source-view builds; `git diff --check`;
  complete `make check` with 642 covered cases and 1,844/1,844 comparisons;
  all 3,133 Talos jobs; the complete Talos artifact gate; and the accepted Flat
  deterministic/Node/Chrome/Verso gates.
- Remaining boundary: Verso owns the semantic-neutral HTML source refactor.
  W7 resumes HTML packaging when that published source commit is available;
  W6 may continue independently.

## Latest completed integration lease

- Milestone: `W7-GENERIC-FLAT-PREREQUISITE`.
- Integration owner: `wasm-gen`; the lease closed the package-specific Flat
  runtime policy and made the shared closed-application path safe for generic
  self-tail lowering.
- Integration branch/worktree: `wasm/generation` in
  `.worktrees/wasm-generation`, rebased directly on `main` at `81c03c98`.
- Published stack: runtime/compiler head `29e52f4b`, Flat functional head
  `f289322a`, and ready mailbox `1847d5ea`.
- Accepted generation surface: `closedApplicationPolicy` now selects complete
  String and fail-closed fallback families only when the captured closure
  retains them, prepares the generic arena, and applies optional validated
  direct-self-tail lowering. Flat now supplies only its public entry to that
  shared path; it no longer carries a handwritten 14-step resident policy.
- Tail-call correctness: a differential HitScene failure showed that looped
  activations retained non-parameter locals that a real Wasm call initializes
  to zero. The transform now performs structured control-flow-aware definite
  assignment and resets only locals observable before assignment. The fix is
  recorded by `FIR-BUG-wasm-none-self-tail-local-reinitialization`; all 301
  HitScene oracle queries and 10,000 flat-frontier queries pass.
- Provenance: Flat publication now forces Lake reconfiguration, fixing
  `FIR-BUG-wasm-none-flat-source-view-stale-reconfiguration`. FIR cannot
  reconstruct the exact generated final-LCNF names of an already compiled
  source ancestor; that toolchain limitation is recorded by
  `FIR-BUG-impure-none-generated-external-source-ancestor`.
- Artifact evidence: player is 29,018 bytes, selection is 31,787 bytes,
  HitScene is 45,621 bytes, and provisional Flat is 154,635 bytes; all four
  modules have zero imports. Flat retains 64 source functions and 504 generic
  resident helpers with zero lazy initializers, down from 82/574 and 23.
- Validation: Lean Beam update/sync/save and focused builds; `git diff
  --check`; exact final-base `make check` with 642 covered cases and
  1,844/1,844 comparisons; all 3,133 `make talos-check` jobs; the Talos
  artifact gate; deterministic player, selection, HitScene, and provisional
  Flat package gates; native/Wasm, 1 MiB UTF-8, cold-stack, repeated-call, and
  package-validator checks.
- Remaining boundary: accepted Flat publication is waiting, not blocked, on a
  remotely resolvable Verso commit containing the already-proven
  semantic-neutral `Pretty.lean` refactor from local commit `e9ae2ed6`. W7 may
  repin and publish immediately after that source handoff. W6 may rebase on the
  accepted stack and continue; no W6-owned file or proof contract changed.

## Latest completed integration lease

- Milestone: `W6-STRUCTURED-PURE-EXTERNAL-RESULTS`.
- Integration owner: `wasm-proof`; this connects the pure external-result
  constructor to the recursive W6.7e structured simulation.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`, based directly on `main` at `4d4e5b4c`.
- Published stack: active-slice record `54671278`, functional head `cbe31a53`,
  and ready mailbox `f1fbe340`.
- Accepted proof: `ConcreteStructuredCodeFocus.reachesYield_reuseBudgetedDirectPureExternalCalls_generated`
  handles every admitted pure `Nat`, `Int`, and scalar external result at
  arbitrary finite nesting with generated named calls. The source path is the
  interpreter's exact three-step request protocol. The target path executes
  compiled arguments, one resolver-proved imported declaration call, and the
  generated destination write; the runtime theorem constructs its exact
  execution and evolved heap witness.
- Compiler boundary: `PureExternalSupported.structuredFlatProgram` derives
  the entire target shape from production compilation, adaptation, external
  declaration resolution, and import alignment. The caller supplies no target
  path, execution certificate, numeric target index, or resolver package.
- State boundary: the evolved entry-relative cache/resource invariant, final
  ABI refinement, and exact outer source/target frames are retained. Until
  the case/join slice, the admitted fragment records its empty source join
  environment explicitly.
- Remaining boundary: connect lazy-cache hit/miss prefixes next, followed by
  case/join, effect, saturated-closure, and target-only administrative paths.
- Contracts: no shared semantic, symbolic Wasm, concrete-runtime, ABI,
  resident-helper, or artifact contract changed.
- Validation: Lean Beam save version 45 at source hash
  `eaac3110f293de68`; forced direct recompilation; focused 3,110-job
  dependency-cone build; `git diff --check`; complete `make check` with 642
  covered cases and 1,844/1,844 backend comparisons; Talos setup pinned at
  `a01d01c`; and all 3,133 `make talos-check` jobs.

## Latest completed integration lease

- Milestone: `W6-STRUCTURED-RECURSIVE-NAMED-CALLS`.
- Integration owner: `wasm-proof`; this closes generated named-call recursion
  in the current W6.7e admitted language.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`, based directly on `main` at `7fb2c8ee`.
- Published stack: active-slice record `d33a0fa1`, functional head `c7551259`,
  and ready mailbox `c0ebc550`.
- Accepted proof: `ConcreteStructuredCodeFocus.reachesYield_reuseBudgetedDirectCalls_generated`
  handles arbitrary finite nesting of compiler-generated named calls. It
  enters the exact generated callee row, recursively simulates its admitted
  body, transports the evolved cache/resource witness across the saved caller
  frame, performs the checked result-local update, and resumes the generated
  continuation with exact source and target frame restoration. The caller
  supplies no target trace, callee execution package, or certificate.
- Supporting boundary: direct flat-prefix and return lemmas now retain exact
  frame equalities; call entry records the stored caller locals; bind return
  exposes the checked update; and
  `ReuseCapacityEntryRelativeFrame.restoreDirectCaller` reconstructs the
  caller's full cache/resource invariant after callee execution.
- Remaining boundary: admit supported pure external results next, followed by
  lazy/cache, case, effect, and saturated-closure transitions.
- Contracts: no shared semantic, symbolic Wasm, concrete-runtime, ABI,
  resident-helper, or artifact contract changed.
- Validation: Lean Beam save at source hash `adc1663391effd55`; forced direct
  recompilation; focused 3,110-job dependency-cone build; `git diff --check`;
  complete `make check` with 642 covered cases and 1,844/1,844 backend
  comparisons; Talos setup pinned at `a01d01c`; and all 3,133
  `make talos-check` jobs.

## Latest completed integration lease

- Milestone: `W6-STRUCTURED-DIRECT-SPINE`.
- Integration owner: `wasm-proof`; this is the first complete recursive body
  fragment of W6.7e.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`, based directly on `main` at `0746d195`.
- Published stack: functional head `1b0dfc7d` and ready mailbox `9a8c47cb`.
- Accepted proof: production `compileArgs`, compiler/adapter inversion, and
  runtime-call alignment establish one `ReuseCapacityDirectTargetFlat` law
  for every operation in `ReuseBudgetedDirectSupported`. The generic theorem
  `ConcreteStructuredCodeFocus.reachesYield_of_reuseCapacityCodeEvaluates`
  inducts over the finite source-only resource evaluation, composes exact
  source steps with exact structured-Wasm paths, and ends at a related source
  yield and target return while exposing both path lengths. Its concrete
  specialization uses the existing `ConcreteReuseCapacityFrame` and runtime
  refinement theorem; callers provide no target trace, translation
  certificate, or target-execution premise.
- Remaining boundary: lift this direct spine through the accepted
  entry-relative saved-frame relation for recursive internal calls, then
  extend the ranked relation across external, lazy/cache, case, and effect
  transitions.
- Contracts: no shared semantic, symbolic Wasm, concrete-runtime, ABI,
  resident-helper, or artifact contract changed.
- Validation: Lean Beam save at source hash `0ccfa27a700936d4`; forced direct
  recompilation; focused 3,110-job dependency-cone build; `git diff --check`;
  complete `make check` with 642 covered cases and 1,844/1,844 backend
  comparisons; Talos setup pinned at `a01d01c`; and all 3,133
  `make talos-check` jobs.

## Latest completed integration lease

- Milestone: `W6-STRUCTURED-FLAT-PREFIX`.
- Integration owner: `wasm-proof`; this is the first recursive direct-body
  transition of W6.7e.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`, based directly on `main` at `85cc4c15`.
- Published stack: active-slice record `b654688d`, functional head `62069562`,
  and ready mailbox `9ffe7641`.
- Accepted proof: existing concrete runtime WP laws now produce exact
  successful Talos outcomes without a caller-supplied execution witness.
  `StructuredWasmFlatProgram.finitePathWithSuffix` reifies such outcomes as
  one structured-machine step per straight-line instruction beneath arbitrary
  residual code and saved frames. `ConcreteStructuredCodeFocus.advance_flatLet`
  matches one direct source `let`, preserves operand/frame suffixes, and
  reconstructs the recursively compiled continuation focus. Executable
  compiler/adapter inversion discharges flatness for immediate literals and
  local aliases.
- Remaining boundary: extend the compiler-derived flatness proof across the
  remaining direct runtime-import families, fold the transition into the
  resource-indexed code induction, then nest the accepted saved-caller
  relation recursively for internal calls.
- Contracts: no shared semantic, symbolic Wasm, concrete-runtime, ABI,
  resident-helper, or artifact contract changed.
- Validation: Lean Beam green saves with source hashes `5a117d1bfce21995`
  and `e43cbd52f5f3aafe`; forced direct recompilation; focused 3,110-job
  dependency-cone build; `git diff --check`; complete `make check`; Talos
  pinned at `a01d01c`; and all 3,133 `make talos-check` jobs.

## Latest completed integration lease

- Milestone: `W6-STRUCTURED-CALLER-TRANSPORT`.
- Integration owner: `wasm-proof`; this is the hereditary call-scope bridge
  of W6.7e.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`, based directly on `main` at `77efa825`.
- Published stack: active-slice record `6a66e5d0`, functional head `30f3152a`,
  and ready mailbox `99babfe3`.
- Accepted proof: `ReuseCapacityCodeEntryTransports.savedStateRelated`
  reconstructs a suspended caller relation at the evolved callee
  runtime/store/witness by combining the current callee runtime relation with
  the accumulated witness transport. It does not require entry and exit
  stores to be equal. Direct call entry constructs the canonical
  entry-relative cache frame, and `bindFrame_of_yield_cacheFrame` consumes its
  evolved form at a related callee yield to establish the accepted structured
  bind-frame focus.
- Remaining boundary: the semantic transport bridge is closed. The next
  W6.7e slice is the structural callee-body simulation that threads the
  entry-relative cache frame and exact saved-frame suffix through each
  admitted source constructor, recursively nesting the same relation for
  internal calls.
- Contracts: no shared semantic, symbolic Wasm, concrete-runtime, ABI,
  resident-helper, or artifact contract changed.
- Validation: Lean Beam update/sync/save with zero diagnostics; forced direct
  source recompilation; focused 3,111-job dependency-cone build; `git diff
  --check`; complete `make check` with 642 validation cases and 1,844/1,844
  backend comparisons; Talos pinned at `a01d01c`; and all 3,133
  `make talos-check` jobs.

## Latest completed integration lease

- Milestone: `W6-STRUCTURED-DIRECT-CALL-ENTRY`.
- Integration owner: `wasm-proof`; this is the generated call-entry slice of
  W6.7e.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`, based directly on `main` at `9594e9ce`.
- Published stack: active-slice record `16e3025c`, functional head `7e2e8004`,
  and ready mailbox `9c052c16`.
- Accepted proof: `ConcreteStructuredCodeFocus.advance_directCall_stage`
  inverts the production two-stage compiler, executes the exact generated
  local-read/erased-zero argument prefix, and reaches the real generated call
  instruction without assuming target execution evidence or a translation
  certificate. `ConcreteStructuredDirectCallReadyFocus.advance_enter` matches
  one source dispatcher step with the actual `StructuredWasmStep.enterCall`
  transition and establishes the generated callee code focus.
- Frame boundary: call entry records the exact saved source bind and target
  Wasm call frames. The target frame retains the post-argument caller locals,
  as prescribed by Wasm. Caller runtime/local invariants remain separate from
  the callee focus so the next slice can transport them soundly across callee
  allocation and effects before establishing the accepted bind-frame return
  relation.
- Contracts: no shared semantic, symbolic Wasm, concrete-runtime, ABI,
  resident-helper, or artifact contract changed.
- Validation: Lean Beam dependency refresh and save with zero diagnostics;
  forced direct source recompilation; focused 3,111-job dependency-cone build;
  `git diff --check`; complete `make check` with 642 validation cases and
  1,844/1,844 backend comparisons; Talos pinned at `a01d01c`; and all 3,133
  `make talos-check` jobs.

## Latest completed integration lease

- Milestone: `W6-STRUCTURED-BIND-FRAME`.
- Integration owner: `wasm-proof`; this is the first continuation-stack slice
  of W6.7e.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`, based directly on `main` at `3e362ba0`.
- Published stack: active-slice record `6cbe5ec2`, functional head `dd375d94`,
  and ready mailbox `c7347f52`.
- Accepted proof: `ConcreteStructuredBindFrameFocus` precisely relates a
  yielded source bind frame to a returning structured target with a one-result
  call frame and generated result-local write. Its restoration theorem matches
  one source bind-resume step by exactly two target steps (`returnCall`, then
  `localSet`), restores the caller operand tail, and re-establishes
  `ConcreteStructuredCodeFocus` for the continuation with the semantic result
  bound in the source environment.
- Frame boundary: code and yield focus now retain
  `ConcreteLocalFrameAligned`, making the compiler-assigned destination
  local's writability an explicit invariant. The deterministic wrapper derives
  the exact source successor from a generic successful source-step premise.
  Establishing this relation from compiled direct-call entry is the next
  W6.7e slice; label/loop administrative unwinding and apply/cache frames
  remain later layers.
- Contracts: no shared semantic, symbolic Wasm, concrete-runtime, ABI,
  resident-helper, or artifact contract changed.
- Validation: Lean Beam update/sync/save with zero diagnostics; focused 3,107-
  job dependency-cone build; `git diff --check`; complete `make check` with 642
  validation cases and 1,844/1,844 backend comparisons; Talos pinned at
  `a01d01c`; and all 3,133 `make talos-check` jobs.

## Latest completed integration lease

- Milestone: `W6-STRUCTURED-RETURN-SIMULATION`.
- Integration owner: `wasm-proof`; this is the first positive target-path
  slice of W6.7e.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`, based directly on `main` at `230d805a`.
- Published stack: active-slice record `05b29e67`, functional head `ab58cd2e`,
  and ready mailbox `95ce391f`.
- Accepted proof: `ConcreteStructuredYieldFocus` relates yielded source control
  to explicit structured-Wasm return control while retaining the concrete
  runtime/local relation, exact observations, and an ABI-indexed
  `PhysicalValueRel` for the returned word. `advance_return` inverts the real
  two-stage compiler, resolves the generated local, and matches one source
  return by exactly two target steps: `local.get` and `ret`.
- Compiler boundary: `advance_return_of_step` derives the source lookup and
  yielded value from the successful source-step premise supplied by generic
  weak simulation. No target execution evidence, source lookup, translation
  certificate, or return representation choice is added to the public
  relation. Continuation-frame correspondence remains the next W6.7e layer.
- Contracts: no shared semantic, symbolic Wasm, concrete-runtime, ABI,
  resident-helper, or artifact contract changed.
- Validation: Lean Beam update/sync/save with zero diagnostics; focused 3,107-
  job dependency-cone build; `git diff --check`; complete `make check` with 642
  validation cases and 1,844/1,844 backend comparisons; Talos pinned at
  `a01d01c`; and all 3,133 `make talos-check` jobs.

## Latest completed integration lease

- Milestone: `W6-COMPILER-RELATION-SILENT-OWNERSHIP`.
- Integration owner: `wasm-proof`; this is the first accepted W6.7e
  compiler-relation slice.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`, based directly on `main` at `5429510c`.
- Published stack: functional head `e05013ab` and ready mailbox `3c9c55a5`.
- Accepted proof: `ConcreteStructuredCodeFocus` relates a source code focus to
  its real two-stage adapted structured-Wasm program, exact target control,
  locals, and store, and the established concrete `StateRelated` runtime
  relation. The relation itself derives exact finite-prefix observation
  agreement. Leading persistent increment/decrement operations take one real
  source step, require a reflexive structured target path, restore the compiler
  focus, and strictly decrease `compilerCodeSilenceRank`.
- Boundary: this slice intentionally leaves continuation-stack correspondence
  to the next relation layer. It neither assumes target execution evidence nor
  weakens source admission, the semantic ABI, or the concrete-runtime
  relation. The next slice adds the first positive structured target path for
  source return through the adapted result local and `ret`.
- Contracts: no shared semantic, symbolic Wasm, concrete-runtime, ABI,
  resident-helper, or artifact contract changed.
- Validation: Lean Beam update/sync/save with zero diagnostics; focused 3,107-
  job dependency-cone build; `git diff --check`; complete `make check` with 642
  validation cases and 1,844/1,844 backend comparisons; Talos pinned at
  `a01d01c`; and all 3,133 `make talos-check` jobs.

## Latest completed integration lease

- Milestone: `W6-STRUCTURED-TERMINAL-ADEQUACY`.
- Integration owner: `wasm-proof`; the user retained the W6 owner as
  integration owner for the certificate-free compiler proof.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`, based directly on `main` at `f161a37f`.
- Published stack: active-slice record `26cde178`, W6 functional head
  `2557bcbe`, and ready mailbox `13eed416`.
- Accepted theorem: `StructuredWasmStep.finitePath_run_of_adapt` collapses any
  finite structured-machine path from a canonical adapted-function entry to a
  halted empty-frame state into the exact Talos `Wasm.run` final store and
  normalized result stack, uniformly above one finite fuel bound. Explicit
  continuation semantics and one-step collapse cover internal calls, labels,
  conditionals, loop restart, outward branches, and returns.
- Compiler boundary: successful `FirTalos.adapt` proves the adapter's
  zero-parameter-loop invariant. Structured-step preservation derives every
  path arity obligation automatically; no representation choice, translation
  certificate, or manually supplied module-shape premise reaches the eventual
  public compiler theorem. W6.7e must now construct the structured target path
  from source execution and restore the compiler relation.
- Contracts: no shared semantic, symbolic Wasm, concrete-runtime, ABI,
  resident-helper, or artifact contract changed.
- Validation: Lean Beam green save; focused dependency-cone builds before and
  after rebase; `git diff --check`; complete `make check` with 642 validation
  cases and 1,844/1,844 backend comparisons; Talos pinned at `a01d01c`; and all
  3,132 `make talos-check` jobs.

## Latest completed integration lease

- Milestone: `W7-GENERIC-BUILD-CLOSURE`.
- Integration owner: `wasm-gen`; the user asked to remove application-specific
  build/runtime shortcuts before resuming interface adaptation.
- Integration branch/worktree: `wasm/generation` in
  `.worktrees/wasm-generation`, based directly on `main` at `aa3940b6`.
- Published stack: active-slice record `0143a5f6`, generic build/runtime head
  `1ab73d0e`, and ready mailbox `02fa20ee`.
- Accepted build closure: consumer packages still compile their real final-LCNF
  source closures. Exact Illuminate declaration-name rewrites and the captured
  `Float.ofNat` source-body substitution are gone. Checked declaration/signature
  selection retains the standard external frontier, generic pure-lazy arena
  preparation removes source globals, and one shared standard-math linker closes
  the full player, selection player, and HitScene modules without host imports.
- Runtime ownership: package capability `fir.standard-math/v1` documents the
  linked runtime's 65,536-byte low-memory reservation. Adapters validate that
  record and advance the FIR arena before encoding. This fixes
  `FIR-BUG-wasm-none-external-runtime-arena-overlap`, where the former 1,024-byte
  initial frontier could overlap linked C runtime data. No shared semantic ABI,
  concrete layout, or resident-helper signature changed.
- Published artifacts: clean `1ab73d0e` PrettyM, full-player, and selection-player
  packages remain zero-import; the deterministic HitScene package inventory is
  `0fc210079c4346847bdcf06e67a9b09f51e036cc5de75f4ce8697e49abf8e6a3`
  around the unchanged 45,595-byte zero-import Wasm. Exact local pointers and
  hashes are recorded in `coordination/lanes/wasm-gen.md`.
- Validation: Lean Beam checkpoints; focused dependency cones;
  `git diff --check`; root `make check` with 642 cases and 1,844/1,844
  comparisons; all 3,131 Talos jobs; the complete deterministic resident-
  artifact gate; 107 full/selection player trace comparisons; 301 HitScene
  oracle queries; and 10,000-call flat-frontier ownership smokes for every
  persistent consumer.

## Parked integration lease

- Milestone: `WASM-OBJECT-CARRIER-PROVENANCE`.
- Integration owner: `wasm-gen`; this is the principled successor to the
  accepted HitScene result-admission compromise.
- Integration branch/worktree: `integration/object-provenance` in
  `.worktrees/integration-object-provenance`, based on `main` at `4d91fb0d`.
- Lease boundary: separate the physical Wasm carrier used at compiler-generated
  call/control-flow boundaries from the semantic provenance required by heap,
  tagged, ownership, projection, and mutation operations. Preserve the current
  accepted behavior while introducing the replacement alongside it; do not
  weaken `AbiKind.refines` or make arbitrary `tobject` values heap objects.
- First slice: freeze the existing relations and consumers in
  `docs/wasm-object-carrier-provenance-plan.md`, then add executable positive
  and negative examples before changing the shared ABI surface.
- Lane coordination: the integration owner owns changes to the shared ABI,
  lowerer, well-formedness gate, and symbolic surface. W6 continues independent
  proof work until a standalone contract commit is ready; W7 may prepare the
  generation-side analysis and fixtures but must not duplicate the shared
  relation on its lane branch.
- Acceptance: the replacement must explain ordinary call, return, join, partial
  capture, closure dispatch, lazy-cache, and dereference/mutation sites; retain
  the accepted HitScene and Flat examples; pass root, Talos, and deterministic
  resident-artifact gates before superseding the compromise.
- Publication prerequisite: satisfied by the integrated
  `W7-ILLUMINATE-HITSCENE-PACKAGE` stack below. Rebase
  `integration/object-provenance` on the resulting `main` before interface
  adaptation resumes.

## Previous completed integration lease

- Milestone: `W7-ILLUMINATE-HITSCENE-PACKAGE`.
- Integration owner: `wasm-gen`; the user asked to close the publication
  backlog before resuming object-carrier/provenance interface adaptation.
- Integration branch/worktree: `wasm/generation` in
  `.worktrees/wasm-generation`, based directly on `main` at `31b9290c`.
- Published stack: resident ownership/cache repair `48605780`, immutable
  package implementation `da69d378`, bug-card schema follow-up `a8db316e`, and
  standalone layout/artifact separation `5a4fc4e0`.
- Package identity: real clean Illuminate source entry
  `Illuminate.HitScene.query` at `af088e313eaa`; 45,595-byte complete Wasm with
  SHA-256 `960979c729bc119988abba24046c4bccd294f3346300d6d20ce53175b5f062d6`;
  zero imports; six function exports plus module-owned memory; canonical local
  pointer `integration/illuminate-hit-scene/_build/illuminate-hit-scene-current`.
- Runtime closure: 159 captured declarations, 34 reviewed externals, 439
  resident-frontier functions, and 15 Float/C-libm imports before the final
  self-contained merge. Float captures use the existing fixed closure slots;
  successful matcher/projection sequences implement application ownership;
  rewindable lazy initializers reuse recursive persistence publication without
  retaining module roots. Runtime signatures and concrete layout are unchanged.
- Ownership evidence: one instance per opaque scene, 4,336 encoded scene bytes
  below checkpoint 69,872, copied results, scratch rewind on success/failure,
  301 oracle queries, 10,000 flat-frontier repeats, independent instances, and
  disposal/malformed-input checks.
- Validation: zero-diagnostic Lean Beam checkpoints; focused dependency cones;
  `git diff --check`; `make check` with 642 cases and 1,844/1,844 equal
  comparisons; all 3,131 Talos jobs; clean repeated HitScene frontier and
  complete-runtime bytes; package checksums/smoke; and the complete
  deterministic resident-artifact gate with 44/44 readiness artifacts, 15/15
  source probes, and the 601-case V8 triangle.
- Proof boundary: W7 supplies the executable helpers and accepted package. W6
  retains the separate implementation-to-concrete-runtime proof for resident
  closure application and may audit the fresh-persistent lazy-initializer
  transform against the existing cache proof cone.

## Latest completed integration lease

- Milestone: `W7-HITSCENE-PARTIAL-APPLICATION-ADMISSION`.
- Integration owner: `wasm-gen`; the user assigned W7 the temporary lease to
  land the exact postponed-LCNF HitScene capture checkpoint and isolate the
  shared result-kind/partial-application admission repair.
- Integration branch/worktree: `integration/hitscene-admission` in
  `.worktrees/integration-hitscene-admission`, with shared contract base
  `0792847b` on `main`.
- Lease boundary: land the green W7 source-capture checkpoint, then repair
  `FIR-BUG-wasm-none-endpoint-partial-application-admission` without an
  Illuminate-specific exception. Prefer preserving the precise heap-object
  result of the generated boxed Float constant through its nullary call/cache
  boundary. Any alternative that broadens closure capture/projection
  compatibility requires W6 review before landing.
- Published stack: compiler contract `c93bf226`, HitScene diagnostics
  `14242c49`, provisional client handoff `db698bdd`, W6 proof adaptation
  `ac81f18d`, W6 ready mailbox `5b5d2a87`, and precise source-artifact ratchet
  `c447a413`.
- Accepted contract: `c93bf226`, followed by HitScene diagnostics at
  `14242c49`. Straight-line internal declarations may expose a proved result
  refinement of a public `tobject` annotation; named-call locals, emitted
  results, and lazy-cache value lanes preserve that exact kind. Directional
  `AbiKind.refines`, closure compatibility, and concrete layouts are unchanged.
- W6 acceptance: the concrete lazy-cache and recursive generated-declaration
  proof cone distinguishes the target result kind from the coarser call-site
  annotation while retaining exact physical cache-slot decoding. No
  `AbiKind.refines`, closure-compatibility, or concrete-layout rule was
  weakened.
- Validation: Lean Beam clean saves; `git diff --check`; root `make check` with
  642 unique cases and 1844/1844 equal comparisons; all 3,131 Talos jobs; exact
  HitScene capture with 159 declarations, 34 externals, and zero unsupported;
  and the complete deterministic resident-artifact gate, including 15/15
  source probes, 44/44 readiness artifacts, PrettyFormat stress, and the
  601-case V8 triangle.
- Client handoff: `db698bdd` documents the exact source pin,
  reproduction commands, expected inventory, and output digests for the
  accepted compiler-admission demo. It is explicitly not an executable Wasm
  package; resident linking and application staging remain the next W7 slice.

## Previous completed integration lease

- Milestone: `W7-FLAT-RESIDENT-PACKAGE`.
- Integration owner: `wasm-gen`; the user assigned the W7 owner the temporary
  lease to land the generation-ready resident helpers and separate Verso Flat
  package machinery after the shared compiler admission reached `main`.
- Integration branch/worktree: `integration/flat-publication` in
  `.worktrees/integration-flat-publication`, based directly on `main` at
  `18d38ba9`.
- Published stack: active-slice record `4dd90837`, isolated helper/linker head
  `061a1db0`, package head `e1e904d6`, and formatting follow-up `3b76ab67`.
- Lease boundary: satisfied. W7 supplies generation-ready resident UInt8
  boxing/unboxing, UInt32 unboxing, tagged closure projections, and batched
  whole-module runtime/linker rewriting including loops. The deterministic
  Verso Flat package machinery compiles the real
  `VersoSlides.Pretty.formatRenderedForRuntime` entry with zero imports,
  module-owned memory, and the five intended function exports. These helpers
  do not claim W6 refinement proofs. The executable package remains explicitly
  provisional until the Verso owner publishes the clean capture refactor on a
  remote-resolvable commit; its local source hash is not accepted provenance.
- Artifact identity: 164,441-byte Wasm with SHA-256
  `cb4092061337d29f44c3444560b0bcbfaa2ea275ef256cae7a9cf7de7612ba35`;
  113 captured declarations, 24 reviewed pre-link externals, 82 retained source
  functions, 574 resident helpers, 656 total functions, 23 lazy cache
  initializers, one resident global, and zero unresolved runtime operations.
- Validation: Lean Beam clean saves during development; `git diff --check`;
  complete `make check` with 642 unique cases, 1,844/1,844 equal comparisons,
  and 116 bug cards; all 3,131 `make talos-check` jobs; complete deterministic
  resident-artifact gate with 44/44 readiness artifacts, 15/15 source probes,
  and the 601-case V8 matrix; two deterministic package publications; exact
  native/Wasm, Node, stress, checksum, source-validator, and Chrome checks.

## Previous completed integration lease

- Milestone: `W6-FINITE-TRACE-ROADMAP-ALIGNMENT`.
- Integration owner: `wasm-proof`; the user retained the W6 owner as
  integration owner for this documentation checkpoint.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`, based directly on `main` at `14cc46ad`.
- Published stack: active-slice record `90a89664`, documentation functional
  head `e46a5b86`, and ready mailbox `d70ef62d`.
- Lease boundary: satisfied. `PLAN.md`, `README.md`, and
  `W6-THEOREM-ROADMAP.md` now use the same W6.7 completion ladder. Generic
  ranked finite-prefix theory, instruction-boundary Talos adequacy, and the
  explicit emitted structured target are complete. Structured terminal
  adequacy is next; construction of the compiler relation and silence rank is
  the largest remaining proof; certificate-free public packaging and
  terminating/divergence consequences follow. Backward simulation, admission
  widening, and W7 resident-helper acceptance remain explicit later work. No
  source, proof, semantic/runtime contract, ABI, helper, or artifact changed.
- Validation: `git diff --check`; complete `make check` with 642 unique cases,
  1,844/1,844 equal comparisons, zero findings, and 115 active bug cards; and
  all 3,131 `make talos-check` jobs.

## Previous completed integration lease

- Milestone: `W7-FLAT-PUBLICATION` shared compiler admission.
- Integration owner: `wasm-gen`; the user assigned the W7 owner the temporary
  integration lease for the two shared compiler-admission repairs required by
  the separate Verso Flat artifact.
- Integration branch/worktree: `integration/flat-publication` in
  `.worktrees/integration-flat-publication`, based directly on `main` at
  `f47ee553`.
- Published stack: active-slice record `a5024916`, bug-card record
  `d18cf57d`, and functional head `05f8c385`.
- Lease boundary: satisfied. Local joins now use the same Lean-compatible
  object-family transfer relation as calls. Boxing accepts either generic
  `tobject` or exactly the representation selected by
  `boxResultKind type .tobject`; scalar and erased lanes remain exact, and the
  malformed UInt64-to-object case remains rejected. A former object-sharing
  guard negative fixture is intentionally positive because both branches use
  the common object ABI. No concrete layout, runtime helper signature, or W6
  proof file changed.
- Validation: Lean Beam zero-error/zero-warning saves for all three changed
  modules; focused 13-job `Fir.Wasm.Examples` build; `git diff --check`;
  complete `make check` with 642 unique cases and 1,844/1,844 equal
  comparisons; Talos pinned at `a01d01c`; all 3,137 `make talos-check` jobs;
  and the complete deterministic resident-artifact gate, including 44/44
  readiness cases, 15/15 source probes, and the 601-case V8 matrix.

## Previous completed integration lease

- Milestone: `W6-EMITTED-WASM-FRAME-STACK-MACHINE`.
- Integration owner: `wasm-proof`; the user retained the W6 owner as
  integration owner for the certificate-free compiler proof.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`.
- Published stack: active-slice record `b8fe230f`, W6 functional head
  `dbecabba`, and ready mailbox `119fea21`, based directly on `main` at
  `56d1c09c`.
- Lease boundary: satisfied. The generated target now has an explicit
  structured-control small-step state with a frame stack and distinct
  running, breaking, returning, and halted modes. Atomic and imported calls
  delegate to Talos; internal calls, block/loop/conditional entry, normal
  exits, loop restart, outward branch propagation, return unwinding, and
  terminal fallthrough are reified as target steps. The concrete generated
  trace boundary now selects this machine. The next proof must show that a
  finite terminal structured path collapses to the exact corresponding Talos
  run; that theorem is not claimed at this checkpoint. No shared semantics,
  symbolic Wasm instruction, concrete layout/runtime operation, resident
  helper, or artifact changed.
- Validation: Lean Beam zero-error/zero-warning saves for the structured
  machine and concrete packaging modules; focused and umbrella 3,131-job
  Talos dependency cone; `git diff --check`; complete `make check` on the
  unchanged 642-case and 1,844-comparison corpus; Talos pinned at `a01d01c`;
  and all 3,131 `make talos-check` jobs.

## Previous completed integration lease

- Milestone: `W6-EMITTED-WASM-FRAME-COLLAPSE-LAWS`.
- Integration owner: `wasm-proof`; the user retained the W6 owner as
  integration owner for the certificate-free compiler proof.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`.
- Published stack: active-slice record `5d3f8725`, W6 functional head
  `0f466b9c`, and ready mailbox `6bf9807e`, based directly on `main` at
  `b1aa9a95`.
- Lease boundary: satisfied. The adapted emitted control grammar is now
  explicit: direct calls, zero-arity blocks/loops/conditionals, indexed
  branches, `.ret`, and ordinary atomics. Local collapse laws reconstruct an
  exact outer Talos instruction transition from a finite internal callee
  ending at generated `.ret`, block fallthrough or `br 0`, loop fallthrough,
  and either selected conditional body. Generic finite-prefix break/`br`
  adequacy supplies the basis for outward propagation. These paths belong to
  the target semantics and are not caller correctness certificates. No
  shared semantics, symbolic Wasm instruction, concrete layout/runtime
  operation, resident helper, or artifact changed.
- Validation: Lean Beam zero-error/zero-warning saves for both changed proof
  modules; focused and umbrella 3,130-job Talos dependency cone;
  `git diff --check`; complete `make check` on the unchanged 642-case and
  1,844-comparison corpus; Talos pinned at `a01d01c`; and all 3,130
  `make talos-check` jobs.

## Previous completed integration lease

- Milestone: `W6-INSTRUCTION-BOUNDARY-WASM-ADEQUACY`.
- Integration owner: `wasm-proof`; the user retained the W6 owner as
  integration owner for the certificate-free compiler proof.
- Integration branch/worktree: `wasm/talos-runtime` in
  `.worktrees/wasm-talos`.
- Published stack: active-slice record `dba73afb`, W6 functional head
  `defe31ea`, and ready mailbox `cab4bcfc`, based directly on `main` at
  `b4b33102`.
- Lease boundary: satisfied. The first concrete target for ranked trace
  simulation retains the Talos store, locals, and residual outer program.
  Each target step is justified by an actual finite `execOne` fallthrough;
  every finite path has one common fuel threshold above which it agrees
  exactly with residual Talos `exec`. Completed fallthrough, general return,
  and the compiler-emitted `.ret` exit recover the exact successful
  `Wasm.run` result. The W6 host packaging supplies this machine directly to
  `ConcreteRankedTraceSimulation`. Calls and structured control remain atomic
  at this checkpoint, so internal divergence is explicitly left to the next
  reified-frame slice. No shared semantics, symbolic Wasm instruction,
  concrete layout/runtime operation, resident helper, or artifact changed.
- Validation: Lean Beam zero-error/zero-warning saves for both new proof
  modules; focused and umbrella 3,129-job Talos dependency cone;
  `git diff --check`; complete `make check` on the unchanged 642-case and
  1,844-comparison corpus; Talos setup at `a01d01c`; and all 3,129
  `make talos-check` jobs.

## Previous completed integration lease

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

- `W6-FINITE-TRACE-ROADMAP-ALIGNMENT` is linked/accepted through active
  record `90a89664`, documentation functional head `e46a5b86`, and ready
  mailbox `d70ef62d`, based directly on `main` at `14cc46ad`. The three W6
  planning documents now agree on stages W6.7a–g and their acceptance
  boundaries. All 1,844 repository comparisons and all 3,131 Talos jobs pass.
  W6 remains parked; resume only with W6.7d structured terminal adequacy and
  its reachable frame-stack/arity invariant.

- `W6-EMITTED-WASM-FRAME-STACK-MACHINE` is linked/accepted through active
  record `b8fe230f`, W6 functional head `dbecabba`, and ready mailbox
  `119fea21`, based directly on `main` at `56d1c09c`. Generated execution now
  uses an explicit structured-control frame stack with reified internal calls,
  blocks, loops, conditionals, branch propagation, return unwinding, and
  halting; atomic and imported calls retain the existing exact Talos boundary.
  Lean Beam, the 3,131-job Talos cone, all 1,844 repository comparisons, and
  all 3,131 Talos jobs pass. W6 is parked at this clean checkpoint. On resume,
  prove that finite terminal structured paths collapse to exact Talos runs,
  then construct the compiler relation and silence rank from the existing W6
  operation laws.

- `W6-EMITTED-WASM-FRAME-COLLAPSE-LAWS` is linked/accepted through active
  record `5d3f8725`, W6 functional head `0f466b9c`, and ready mailbox
  `6bf9807e`, based directly on `main` at `b1aa9a95`. Finite internal calls,
  block exits, loop fallthrough, and selected conditional bodies now collapse
  to exact outer Talos instruction steps, while finite `br` adequacy exposes
  the continuation needed for outward propagation. Lean Beam, the 3,130-job
  Talos cone, all 1,844 repository comparisons, and all 3,130 Talos jobs pass.
  Next W6 work packages these local laws into the explicit frame-stack
  small-step machine and adds loop restart and outward branch transitions.

- `W6-INSTRUCTION-BOUNDARY-WASM-ADEQUACY` is linked/accepted through active
  record `dba73afb`, W6 functional head `defe31ea`, and ready mailbox
  `cab4bcfc`, based directly on `main` at `b4b33102`. A concrete resumable
  state retains store, locals, and residual outer program; exact finite paths
  collapse above one common fuel bound to Talos `exec`, and both fallthrough
  and the compiler-emitted `.ret` recover the exact successful `Wasm.run`.
  The W6 concrete host packages this machine for ranked trace simulation.
  Lean Beam, the 3,129-job Talos cone, all 1,844 repository comparisons, and
  all 3,129 Talos jobs pass. The next W6 slice reifies call and
  structured-control frames so divergence inside an atomic instruction also
  produces target progress, then constructs the compiler relation and rank
  from existing W6 operation laws.

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
- `W6-POINTWISE-CODE-ADVANCE` is linked/accepted through W6 functional head
  `19778649` and ready mailbox `9ea2b57d`, based on `2a870967`. The first
  relation-wide ordinary-code theorem covers return, direct values, generated
  named calls, and exactly saturated closure calls. From one source
  `executeStep` it constructs the finite structured-Wasm path and production
  callee row internally, returns an admission-free code/direct-ready/
  saturated-ready/returned successor, and proves compiler-rank descent for
  every empty target path. It assumes neither callee termination nor future
  execution certificates. The saturated admission bug card
  `FIR-BUG-wasm-none-pointwise-saturated-admission` is fixed by retaining exact
  runtime resolution and shared-capture capacity only at the current node.
  Lean Beam and the 3,110-job focused cone pass, `make check` passes all 662
  unique cases and 1,968 comparisons, and all 3,133 Talos jobs pass. W6 next
  closes ready/entry/return outcomes under the global relation before widening
  the same step law to external, lazy, case, and effect nodes.
- `W6-GLOBAL-CALL-ENTRY` is linked/accepted through W6 functional head
  `1bc6eb40` and ready mailbox `1ecd63f3`, based on `59ea914f`.
  `ConcreteStructuredGlobalOutcome` hides the active generated function,
  entry anchor, ABI indices, and resource budget, giving the pointwise code
  law a module-stable conclusion. Named and exactly saturated ready states
  take only the ordinary source step and enter the selected generated callee
  in that same relation; the saturated rule reconstructs closure consumption
  internally, and each production row re-anchors the full supported-function
  contract at the callee. No future admission, callee evaluation, termination
  premise, or execution certificate is stored. Lean Beam and the 3,110-job
  focused cone pass, `make check` passes all 662 unique cases and 1,968
  comparisons, and all 3,133 Talos jobs pass. W6 next retains static supported
  caller identity across the hereditary resource stack and closes direct and
  saturated return-pop transitions globally.

## Lane snapshot

Lane rows name their own landed commits; the board intentionally has no
moving global snapshot hash.

The shared lane baseline is now Lean 4.33 at `476f001b`. Lane heads recorded
below that do not name this base must rebase before new proof, generation, or
validation work continues; their historical handoff text remains unchanged.

| Lane | Owner handle | Branch | Status | Current slice | Contract impact |
|---|---|---|---|---|---|
| Integration | integration owner | `upgrade/lean-4.33` | released | `LEAN-4.33-UPGRADE` landed at `476f001b`; the temporary lane may be retired after publication. | Moves the shared toolchain, compiler-source contracts, and versioned compact-Format package surface to Lean 4.33 without changing the semantic Wasm ABI, concrete layout, or resident-helper signatures. |
| Lean pass proof | pass-proof owner | `proof/simpcase` | released | Ready mailbox `5cae5958`, functional head `5c607e0e`, on accepted base `a25713a6` packages deleted reset/reuse as generic local ledger operations and derives ordinary/source-owned readiness from live-prefix premises. The retained-prefix fixture no longer uses a finite special-state classifier. | Changes no shared contract. The 34-job examples cone and full root gate pass; next generalize the target live-prefix derivation beyond the singleton adapter. |
| W6 runtime proof | W6 owner | `wasm/talos-runtime` | released | Ready mailbox `c07eaf4b`, functional head `42fb2d5d`, on base `a6f4510e` makes production validation proof-visible and supplies the root plus residual join/local/case/sharing transition API. Next attach that state to active/suspended relations and repair return admission's compatibility direction. | Shared validator contract `72856600` replaces an opaque partial traversal with an extensionally equivalent total traversal; consumers rebase without code adaptation. Lean Beam, the 3,121-job focused cone, full root gate with 125 harness tests, 685 unique cases and 2,037 comparisons, and all 3,144 Talos jobs pass. |
| W7 generation | generation owner | `wasm/generation` | released | Tracked handoff `04003bd6`, functional head `8cb9cd82`, on base `dc550aa8` lands the exact-source lean-zip catalog, immediate `Nat.add`, reusable binary immediate-Nat dispatch, and allocation-free immediate `Nat.mod`. | No shared contract changes. Generation is ready; W6 refinements remain queued in `W7-W6-20260814-007` and `W7-W6-20260814-008`. |
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
| Generic Array/scalar/String HTML frontier: `Array.pop`, `UInt32.decEq`, `String.append`, `String.push`, `String.Pos.next`, `String.decodeChar` | `57ae699e` | `260ce30a`; existing concrete layouts and semantic ABI | generation-ready | W6 owner for later concrete refinement | Verso complete HTML `ce63b4fd71abddda8aa5795a57ab7849666f8029b501a015ee3e3c714a3eec1c` |
| Canonical immediate binary Nat dispatch for `Nat.add` and `Nat.mod` | `75b11c0c`, `8cb9cd82`; tracked handoff `04003bd6` | `dc550aa8`; unchanged Nat layout, ownership, and helper signatures | generation-ready | W6 owner via `W7-W6-20260814-007` and `W7-W6-20260814-008` | raw lean-zip `68d0f17dfd8641a458687d68972308a1af7766c04cea7834904f87b6f4064c70` |

## Contract queue

| ID | Producer | Consumers | Status | Standalone commit | Effect |
|---|---|---|---|---|---|
| `WASM-CORE-SCALAR-SURFACE` | integration | W6, W7, validation, binary/Talos adapters | released | isolated contract `43ab6619`; queue `8484c0be` | Completes FIR's typed scalar core vocabulary rather than synthesizing standard machine operations in resident helpers: all wasm32/wasm64 integer arithmetic, comparison, bitwise, shift/rotate/count operations; the f32/f64 arithmetic, unary, comparison, constant, and scalar-memory families; all scalar integer memory widths; and the core numeric conversion, sign-extension, saturating-conversion, and reinterpretation families. The binary encoder, symbolic validator, Talos adapter, and executable 163-case opcode fixture advance atomically. Table/reference calls, GC, exceptions, SIMD, atomics, and bulk-memory remain separately modelled subsystems, not silently claimed by this scalar contract. W7 rebases before resident-helper loop removal in separate consumer commits; W6 requires no proof adaptation. |
| `WASM-SETTAG-UINT32-ADMISSION` | integration/W6 proof | W6, W7, validation | released | isolated contract `982ed402`; proof consumer `e8def3a8`; mailbox `7f7e51fa`; bug card `FIR-BUG-wasm-none-settag-uint32-admission` fixed | Requires every production-accepted source `.setTag` value to satisfy `tag < UInt32.size`, matching the unbounded source `Nat` to the concrete wasm32 header instead of silently wrapping. The first excluded value has a fail-closed `supportedProgram`/`lowerSupported` regression. W6 now derives the exact compiler local, range, live-constructor shape, and semantic update from validation plus one successful source step. W7 and validation rebase without generated-code, ABI, runtime, layout, helper-signature, or artifact adaptation. |
| `WASM-STRUCTURED-VALIDATION-TOTALITY` | W6/integration | W6, W7, validation | released | isolated contract `72856600`; proof consumer `42fb2d5d`; mailbox `c07eaf4b` | Replaces opaque partial `supportedCodeWithJoins` recursion with a terminating traversal and an explicit alternative-list helper. The helper is proved extensionally equal to the former `Array.all` check, preserving production acceptance while exposing equations needed by the compiler-correctness proof. W7 and validation rebase; no generated code, semantic ABI, concrete runtime, or artifact adaptation is required. |
| `LEAN-4.33-UPGRADE` | integration | pass proof, W6, W7, validation, artifact clients | released | landed stack through `476f001b`; Verso source `eb8d2b8f`; Talos pin `0e05edbc` | Moves every live FIR toolchain and versioned package contract to Lean 4.33.0 while preserving the semantic Wasm ABI, concrete layout, and resident-helper signatures. All surviving lanes rebase before continuing; historical 4.32 records remain provenance. |
| `LANE-W6-W7-SPLIT` | integration | W6, W7, harness | released | `9cb483f` | Gives W6 and W7 independent branches and worktrees |
| `RESET-ERASED-RELEASE` | integration | pass proof, W6, validation | released | `373b0a9` | Reset treats erased ownership slots as no-ops; proof adaptation `8c2fff6`, W6 adaptation `afd7ab0`, and validation observation `3b82b0b` are landed |
| `W7-RESIDENT-ALLOCATOR` | W7 | W6, integration | released | `21f382c` | Zero-import allocator and styled package are generation-ready; allocator installation preserves the current 177-import `prettyM` frontier, and W6 owns the later bridge proof |
| `W7-CLOSURE-DESCRIPTORS` | W7 | W6, W7, integration, artifact clients | released | `40f41c0` | Retains the duplicate-free capture-kind table after `partialApply` imports are removed, so closure header `aux3` remains stable; W6 must rebase before W7 consumes it in the resident closure allocator |
| `W7-RESIDENT-LITERALS` | W7 | W6, integration, artifact clients | released | `64831f6` | Adds a zero-import literal fixture, internalizes immediate Naturals in linked `prettyM`, retains Strings until their JavaScript consumers become resident, and advances text/styled checkpoints to 152/153 imports |
| `W7-GENERIC-ARRAY-STRING-HTML-FRONTIER` | W7 | W6, integration, artifact clients | released | `57ae699e` | Adds the six generic Array/scalar/String resident signatures required by the real Verso HTML closure and makes partial String selection capability-sensitive. Generation and real-engine acceptance are complete; W6 refinement remains separately tracked. |
| `FLOAT-SCALAR-RUNTIME` | integration/validation | pass proof, W6, W7, validation | released | landed stack through `8a8d1387` | Adds bit-exact `float32Bits`/`float64Bits`, heap-only boxes, stable box-kind/layout signatures, exact ABI adapters, and concrete/proof refinements without the unrelated closure-ownership stack. The integrated stack passes `make check` and all 3,123 Talos jobs. W7 consumes it in candidate `2b4d9d23`. |
| `WASM-FLOAT-REINTERPRET` | integration | W6, W7, Talos adapter | released | landed stack through `8a8d1387` | Symbolic, binary, Talos-adapter, runtime, and proof support for `i32.reinterpret_f32`, `i64.reinterpret_f64`, `f32.reinterpret_i32`, and `f64.reinterpret_i64` is landed. W7's integer-lane facade preserves signaling-NaN payloads across JavaScript without numeric coercion. |
| `ILLUMINATE-FLOAT-MACHINE` | integration | W7, W6 | released | `e39d0bbb` | Adds only the typed symbolic and binary Wasm operations needed to implement Lean 4.32 Float subtraction/division/multiplication/comparison, round-away-from-zero, saturating `toUInt64`, and Nat-to-Float conversion. W7 consumes the vocabulary in resident helpers; the later W6 bridge proves those helpers against the concrete runtime contracts. |
| `ILLUMINATE-NAT-MOD-MACHINE` | integration | W7, W6 | released | symbolic unsigned i32 remainder plus W7 consumer `8cb9cd82` | Supplies unsigned i32 remainder to the generic two-immediate `Nat.mod` branch while retaining the arbitrary-precision checked fallback. W6 refinement remains separately queued. |
| `BIT-EXACT-FLOAT-MANIFEST-TRANSPORT` | integration | W7, validation, artifact clients | released | contract `8ad80ad3`; canonical validation consumer `57f13122` | Defines the version-1 `wasm-reinterpret-i32-i64` capability, exact entry selection, integer-lane argument/result codecs, and semantic observation bridge. Floating manifests without the capability and capabilities with unknown fields, versions, encodings, entries, arities, kinds, or ranges fail closed. The standalone suite covers signed zero, infinities, quiet/signaling NaNs, maximal payloads, mixed signatures, and every malformed constructor path without JavaScript numeric coercion; the root validation runner now consumes the facade and passes the complete 613-case native/LCNF plus 581-case V8 gate. |
| `CLOSURE-APPLICATION-OWNERSHIP` | integration/validation | pass proof, W6, W7, validation | released | landed proof/runtime stack `229640de`; corrected contract `89fda41a`; proof `1640c7d4`; W6 `b28feab9`; ownership `528fdd1a`; W7 adapter `fd6a51e3` and ready head `fdaa8bd1` | Matches Lean's `lean_apply_*` boundary: an exclusive closure transfers fixed arguments and is freed non-recursively; a shared closure drops one reference and retains each fixed heap argument. Pass, concrete-runtime, and executable-adapter layers are green and linked/accepted. |
| `EXTERNAL-WAITING-RUNTIME` | integration/validation | pass proof, W6, validation | released | landed stack `229640de`; standalone repair `89fda41a`; proof `1640c7d4`; W6 `b28feab9`; historical validation provenance `2f301de5` | `Step.external`, `executeStep`, soundness, and the Talos frame refinement use the post-core-step `waiting.runtime`, so external responses cannot resurrect a consumed closure or discard shared closure decrements and retained captures. `FIR-BUG-impure-none-closure-application-external-runtime` is fixed with executable and proof regressions. |
| `SCALAR-CLOSURE-ABI-ADMISSION` | W6/shared lowering | W7, validation, integration | released | functional head `cf1ed73f`; ready head `4013a6ba`; bug card `FIR-BUG-wasm-none-generic-scalar-closure-admission` | A raw `tobject` parameter is refined to erased only after structural final-LCNF use analysis proves exact forwarding to a statically known erased parameter. UInt8 boxes use the precise tagged kind, justified by the concrete scalar-boxing theorem. Production lowering, supported lowering, closure dispatch, and the general compiler proof share this row. All 32 formerly fenced cases pass the three-edge probe; W7 and validation consume the landed boundary unchanged. |
| `WASM-DECLARATION-PARAMETER-UNIQUENESS` | integration/W6 proof | W6, W7, validation | released | queue/card `03547684`; isolated contract `dfa8153e`; bug card `FIR-BUG-wasm-none-duplicate-declaration-parameters` | Adds duplicate-free same-scope declaration parameters to `supportedDecl`. This aligns validator parameter kinds with the deduplicating symbolic-local row and prevents an accepted program from lowering to an invalid call signature. Existing well-formed generated programs are unaffected; consumers rebase after landing. |
| `WASM-DECLARATION-NAME-UNIQUENESS` | W6 proof | W6 compiler-correctness clients | released | isolated proof contract `b6030300`; functional proof `f215c995`; bug card `FIR-BUG-wasm-none-supported-export-declaration-name-uniqueness` | Retains the existing phase-level `Program.NamesUnique` fact at `ConcreteSupportedExport`, proving that source lookup, symbolic function selection, and adapter numeric lookup identify the same internal declaration. No lowering, validator, ABI, runtime, or interpreter behavior changes. |
| `CLOSURE-PROJECTION-KIND-REFINEMENT` | W6 proof/runtime | W6 compiler correctness, W7 resident projection, validation | released | functional head `625d4883`; ready mailbox `22d15cf3`; bug card `FIR-BUG-wasm-none-closure-projection-kind-refinement` | A closure retains its captured argument's precise descriptor kind, while generated callee entry may request the wider target-parameter kind. Live and post-application projection accept exactly `actualKind.refines expectedKind`, read at the actual descriptor kind, and preserve the physical lane while widening `PhysicalValueRel`. W7's resident helper already loads the same raw slot and requires no implementation change. |
| `WASM-LEAN-OBJECT-FAMILY-CALL-ABI` | W7/shared lowering | W6, W7, validation, artifact clients | released | initial contract `bd7a5e55`; W7 consumer `a13fa2ad`; package ratchet `e5a8612b`; closure-call extension `b2d6f45c` | Follows Lean's generic call representation: `object`, `tagged`, and `tobject` are mutually compatible at named calls, joins, results, symbolic-stack boundaries, and ordinary allocated-closure invocation, while scalar and erased lanes stay exact. Directional semantic/proof refinement, closure capture descriptors, and every concrete layout remain unchanged. The shared refinement-to-call-compatibility lemma keeps the existing W6 closure-resolution proof hypotheses sufficient. W7 removes caller-name repairs, preserves captured `tobject` helper results, and ratchets the reviewed prettyM closure inventory from 40 to 42 before continuing Level1. |
| `VALIDATION-BOXED-SCALAR-SCHEMA` | integration/validation | LCNF validator, W7/V8 adapter, validation fixtures | released | standalone schema `64903ee7`; consumer `1d3c23d1` | Adds an explicit physical `.boxed` marker around a logical fixed-width, `USize`, or floating-point scalar schema. It distinguishes generic object fields such as `Prod`'s boxed `UInt8` from concrete packed scalar fields without constructor-name heuristics or changing `ValidationDatum`. LCNF materialization and decoding, Wasm ABI classification, manifests, the semantic host, and V8 validation now implement Lean's existing final-LCNF `box`/`unbox` representation; tagged integer and heap integer/float regressions pass. |
| `VALIDATION-BOXED-BOOL-SCHEMA` | integration/validation | LCNF validator, W7/V8 adapter, validation fixtures | released | standalone schema `a348f8ac`; consumer `bff62c1e` | Extends the physical `.boxed` marker to logical `Bool`, whose specialized final-LCNF lane is `UInt8` but whose value is boxed when stored in a generic `List`, `Option`, `Except`, or other polymorphic object field. Consumers use the existing `UInt8` box/unbox representation and preserve logical `.bool` observations; no semantic Wasm, concrete layout, resident-helper, or W6 proof contract changes. |
| `VALIDATION-GENERIC-ARRAY` | integration/validation | semantic LCNF runtime, pass relations, validation schemas, W7 boundary encoders, concrete host, W6 runtime proofs | released | contract `71471a5d`; accepted functional head `2f6fc869` | Adds `HeapObject.array elements capacity` with ownership of exactly the live element prefix and adds `.array element` as the physical source-Array schema distinct from `.seq`/List. The boundary maps it to W7's existing upstream-aligned resident `opaque/ARRY/size/capacity/tobject-slots` representation. Capacity is representation state; validation observations compare the live elements. Pass relations, concrete layout/runtime/refcount/fault proofs, Talos adapters, and artifact oracles are adapted and linked/accepted. |
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
