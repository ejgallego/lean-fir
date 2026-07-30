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

## Current landing gate

This section is authoritative for the current integration boundary; older
candidate hashes in the lane and contract tables remain historical provenance
until their stacks land and must not be used as current feature-branch
identities.

- Validation's validated pre-record coordination head is `3ae6c37d`, with
  functional head `96eec154` on semantic base `fff91175` and coordination head
  `cfa17d81`. The current functional validation boundary on `main` is
  `6ab2efed`; the combined proof/validation head is `25cc1ceb`, so the long
  validation branch is twenty-two commits behind and one hundred twelve
  commits ahead. Its older commits `a2907a66`,
  `7c87e6ec`, and `bb387042` have been superseded by current-main landings
  `15b8727e`, `e08784b3`, and `6ab2efed`. The next long-branch rebase drops
  their duplicated mechanisms; it preserves the long-only Float/IO domain
  declarations as a later additive calibration after their shared contracts
  land.
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
  `strace`, and the 581 native-to-V8 cases exceed the 413-case global oracle
  floor. The retained 67-case protocol-v4 float/mixed triangle is an additive
  frontier, not the total real-engine baseline. Functional `main` at `6ab2efed`
  passes the complete `make check`, including the same 581-case triangle and
  its 590-case composed coverage index. The index now rederives exact
  tag-to-case attribution from retained corpus evidence and enforces 30
  per-tier semantic floors plus 94 conjunctive domains: all 2,809 required
  tag-attributions and 1,469 domain memberships are present. Forty-six matching
  source and V8 domains pin arithmetic boundaries, external families,
  failures, closures/control flow, effects, ownership, mutation, and text/byte
  behavior; two direct-machine domains pin recursive release and reset/reuse.
  It also supplies enforceable `portable` and `exact` equivalence gates for two
  independently verified evidence graphs. The current protocol-v4 attestor
  correctly rejects the protocol-v3 baseline evidence as an unsupported
  version, so it is strong runtime evidence but not a current global oracle
  attestation; that v4 claim still waits for W7.
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
- W6 is at `acb95426`, one hundred thirty commits ahead and five behind, with
  active owned edits and an untracked W6 bug card. W7 is at `4f694470`,
  twenty-one commits ahead and seven behind, with active generation-consumer
  migration edits and a Float transport bug-card update.
  Integration must not absorb any of those working trees; each lane runs its
  required checks, cleans, and sends the prescribed handoff before landing.
- Current `main` at `8ad80ad3` releases the fail-closed
  `bitExactFloatTransport` consumer contract independently of the queued Lean
  float stack. It selects an integer-lane Wasm facade, preserves all raw f32/f64
  bits as `BigInt`, rejects missing or malformed capabilities, and passes the
  complete 590-case / 1,752-comparison root gate. W7's clean facade checkpoint
  is `3a1610cd`; its next slice rebases onto this release and migrates every
  manifest scalar consumer.

## Lane snapshot

Lane rows name their own landed commits; the board intentionally has no
moving global snapshot hash.

| Lane | Owner handle | Branch | Status | Current slice | Contract impact |
|---|---|---|---|---|---|
| Integration | integration owner | `main` | active | Main contains structured symbolic Wasm loops, Talos lowering, stack-safe resident String walkers, and the checked ledger-aware LCNF correctness endpoint at `6d61e0aa`. The retained-prefix reset/reuse client at `5b9bead7` reaches `LoweringCorrect`; `3f720ba4` extracts environment/ledger laws, `5a437fae` derives reset/reuse operational shapes plus finite-path invariant transport, `3744edf1` adds source-only allocation lifecycle transport, `0041d70c` carries exact heap-binding/reset-token provenance, `7ecdc33b` derives all three deleted-write heap shapes from successful runtime effects, `44b1c2ff` composes those facts into the full root-aware write-readiness contract, `8c6ea3e6` does the same for both reuse-token branches, `475b642b` frames recursive release/reset inside the operand's original owned closure and derives the target-ledger owner frame, `cd09942c` makes that closure certificate compositional across environment, heap, ledger, and paired-allocation transitions, `f29b5a90` derives fresh-frontier exclusion from a reusable heap ownership bound, `7ebfb53c` preserves the bound through replacement, recursive release, reset, and concrete-token reuse, `67183055` derives installed-value bounds from checked evaluation, `b05c62d5` separates target liveness from complete source-environment ownership at deleted operations, `fd4f531f` carries the local ownership invariant through allocation/reuse result binding, `15092e7c` extends it through exact hereditary bind/apply restoration with complete saved bind environments, `ba52212b` preserves it through cache persistence and the checked three-way yielded dispatcher, `a43b7f4c` carries the whole-machine invariant through both deleted-reuse token branches, `1cef5df2`/`23898302` extend and check it for deleted constructor allocation, object-field writes, and reset, `8bde8037`/`475451b9` complete and check deleted-write ownership for absolute-slot `USize` and packed-scalar updates, `597b57ea`/`633d259d` preserve and check retained named/local application ownership across bind-frame pushes and nullary local aliasing, `51494be3`/`89d6a99e` preserve and check root-free retained erased, `USize`, and scalar result binding, `b535c662`/`61fe8259` preserve and check retained object projection, unbox, and sharedness reads, `8e144c34`/`0a5aa2f5` preserve and check retained heap-backed literal and constructor allocation ownership, `6f708f42`/`588146ac` preserve and check retained partial-application closure and heap-box allocation ownership, `0d333649`/`997a8928` complete the retained-family ownership matrix with heap reset plus both reuse-token branches, `fbf34a80`/`fff91175` complete and check source, exact-shadow, and reachable active-code ownership dispatch, `88c85852`/`991c36ee` preserve and check every internal named-invocation successor, and `7c0bb6c3`/`28aa7930` recover closure fixed-argument bounds and complete the ownership-strengthened dispatcher for every internal control. Validation head `1762979a` remains based on the earlier semantic boundary and compares genuine native Lean stdout/stderr without requesting compiler work | Eight isolated shared-contract domains remain queued: float representation, closure ownership, argument aliases, process termination, effectful native-oracle actions, source-entry result boundaries, Lean IO-error normalization, and native source-stream capture. The last four are validation infrastructure; W7/V8 consumes them only when compiler-generated cases are ready. W7's float consumers and fresh V8 execution are complete; integration is now gated by proof-owned `takeClosureApplication`/float-box consumers and W6's concrete float layout/refinement handoff |
| Lean pass proof | pass-proof owner | `proof/simpcase` | active | Landed head `25cc1ceb` adds a direct source-owned exact contract for the checked concrete reset/reuse program. Reset readiness now consumes the maintained source carrier: reset preserves `HeapOwnershipBelowFrontier`, whose generic frontier theorem replaces a concrete post-reset heap enumeration. The endpoint reaches whole-program `LoweringCorrect` under the source foreign-ownership law. | Generalize the ownership-consuming readiness interface from finite fixtures to static compiler typing/local-shape preservation, starting with a reusable reset/reuse invariant that does not enumerate the source execution graph. After lane 4 rebases its shared contracts, also re-probe the focused `SimpCaseRelation` and `AlphaEqvCode` consumers rather than assuming their historical locations remain exact. |
| W6 runtime proof | W6 owner | `wasm/talos-runtime` | active | Clean committed head `62872f62`, three main commits behind at this checkpoint, continues the independent cache/refinement proof stack | Publish the standalone Float32/Float boxed-kind codes, packed storage/projection/mutation support, resolver support, and `HeapRefinement` cases consumed by W7; also complete the closure-application audit. W6 owns implementation-to-concrete-host theorems, not validation adapters or the W7 compiler |
| W7 generation | generation owner | `wasm/generation` | active | Clean checkpoint `3a1610cd` generates and validates canonical integer-lane f32/f64 facades and emits the versioned `bitExactFloatTransport` manifest capability. Earlier slices exhaustively emit and consume `float32Bits`/`float64Bits`, accept raw-bit command arguments, and execute exact Float32/Float values through the semantic and concrete hosts. The styled `prettyM` package owns/exports memory, has zero imports, and preserves `PrettyTrace` styling. | Rebase onto released consumer contract `8ad80ad3`, then migrate all semantic, concrete, module, browser-worker, and validation-case manifest consumers and extend the real-engine corpus to signaling NaNs. The queued Lean float/closure stack still needs proof-owned `AlphaEqvCode` adaptation and W6 concrete refinement before the final artifact becomes `linked/accepted`. |
| Compiler-native Wasm | integration owner | `wasm/lcnf-c` | parked | Landed checkpoint `a4855402` adds a separately packaged C/Emscripten `Std.Format.prettyM` facade on top of the optimized final-LCNF-to-C route from `2760e3e0`. The browser adapter shares the compact `Format` request and exact `{text, events}` trace contract with W7's FIR-native facade while retaining a private bulk wire, verified Emscripten loader, full pinned Lean runtime, and independent package. The differential suite compares Unicode, grouping, nesting, tags, arbitrary-precision values, initial columns, malformed requests, repeated calls, and a one-MiB UTF-8 transfer through both engines | No shared semantic contract changed and the packages remain physically independent. The lane consumes `Std.Format.prettyM`, final impure LCNF, and Lean's C ABI without changing the symbolic Wasm, W6 concrete-runtime, or W7 resident-runtime surfaces. Resume with controlled sampled profiling of the facade wire and generated C before accepting a runtime optimization |
| Validation | validation owner | `validation/float-corpus` | active | Clean coordination head `cfa17d81`, with validated functional head `96eec154` on semantic base `fff91175`, is eighteen functional commits behind and one hundred twelve ahead of current `main`. Its 1,008-case native/LCNF run and 9-case direct-machine run verify offline with zero findings; the composed long-stack index retains 1,017 comparisons, 9,939 interpreter steps, 193 semantic-tag floors, and 152 semantic domains. Current-main extractions `e08784b3` and `6ab2efed` independently land retained-corpus tag attribution, 30 semantic floors, and 94 conjunctive domains over the green 590-case native/LCNF/direct/V8 checkpoint. | The next long-branch rebase drops duplicated mechanisms from `a2907a66`, `7c87e6ec`, and `bb387042`, already superseded by `15b8727e`, `e08784b3`, and `6ab2efed`; it retains long-only Float/IO domains as an additive post-contract calibration. Shared float, closure, alias, termination, IO, and stream-capture contracts remain isolated and require the recorded proof/W6/W7 handoffs before integration. |

## Resident-helper bridge

| Helper or artifact | Generation commit | Contract base | State | Proof owner | Artifact digest |
|---|---|---|---|---|---|
| Existing resident helper set through closure matching | landed on `main` | recorded in Talos plan | generation-ready | W6 owner | recorded by individual manifests |
| Resident allocator, constructors, and styled `prettyM` through immediate Naturals | `64831f6` | `40f41c0` | generation-ready | W6 owner at the later contract bridge | styled Wasm `5d14b3fd2b1eb93de344ee69c6117e539eeed320c857248eb0fd4691b9d9e5d2` |
| Standalone immediate-Natural and UTF-8 String literals | `64831f6` | current W6 object layouts | generation-ready | W6 owner | Wasm `ab63fa578576748ff3ea8230986cf908d7285c54bc840bb60fec5fc7fa978473` |
| Bit-exact float source probes and styled zero-import `prettyM` package | candidate `517a2d04` before coordination-only rebase | integration float/closure stack through `984086b5`; W6 float box layout pending | generation-ready | W6 owner for concrete refinement | styled Wasm `e7ccd1ac678900e0f6583a0d2251b0ef4d43de0b388d18033bbc86344eed4af7` |

## Contract queue

| ID | Producer | Consumers | Status | Standalone commit | Effect |
|---|---|---|---|---|---|
| `LANE-W6-W7-SPLIT` | integration | W6, W7, harness | released | `9cb483f` | Gives W6 and W7 independent branches and worktrees |
| `RESET-ERASED-RELEASE` | integration | pass proof, W6, validation | released | `373b0a9` | Reset treats erased ownership slots as no-ops; proof adaptation `8c2fff6`, W6 adaptation `afd7ab0`, and validation observation `3b82b0b` are landed |
| `W7-RESIDENT-ALLOCATOR` | W7 | W6, integration | released | `21f382c` | Zero-import allocator and styled package are generation-ready; allocator installation preserves the current 177-import `prettyM` frontier, and W6 owns the later bridge proof |
| `W7-CLOSURE-DESCRIPTORS` | W7 | W6, W7, integration, artifact clients | released | `40f41c0` | Retains the duplicate-free capture-kind table after `partialApply` imports are removed, so closure header `aux3` remains stable; W6 must rebase before W7 consumes it in the resident closure allocator |
| `W7-RESIDENT-LITERALS` | W7 | W6, integration, artifact clients | released | `64831f6` | Adds a zero-import literal fixture, internalizes immediate Naturals in linked `prettyM`, retains Strings until their JavaScript consumers become resident, and advances text/styled checkpoints to 152/153 imports |
| `FLOAT-SCALAR-RUNTIME` | integration/validation | pass proof, W6, W7, validation | active | `0f5762db`; heap-only box extension `0e7ab46e`; boundary/oracle closure through `984086b5` | Adds bit-exact `float32Bits`/`float64Bits`, typed schemas, LCNF codecs, heap-only boxes, exact semantic adapters, and fail-closed native-oracle products. W7's manifest, command, concrete-host, source-probe, Node, Chrome, and V8 consumers are generation-ready. Pass proof still owns the `boxUsesTaggedRepresentation` branches; W6 owns the stable box-kind/layout signatures and concrete refinement before the artifact can become `linked/accepted`. |
| `WASM-FLOAT-REINTERPRET` | integration | W6, W7, Talos adapter | active | candidate `37288f87` on base `c5584f4e` | Adds symbolic and binary support for Wasm opcodes `i32.reinterpret_f32`, `i64.reinterpret_f64`, `f32.reinterpret_i32`, and `f64.reinterpret_i64`, with exact physical-lane validation and guards. `make check` is green. `make talos-check` reaches the expected exhaustive-match failure in W6-owned `FirTalos.Adapter.lean:69`; map the four cases to Talos's existing `.i32ReinterpretF32`, `.i64ReinterpretF64`, `.f32ReinterpretI32`, and `.f64ReinterpretI64`. After that adapter handoff, W7 consumes the contract in an integer-lane facade that preserves signaling-NaN payloads across JavaScript. |
| `BIT-EXACT-FLOAT-MANIFEST-TRANSPORT` | integration | W7, validation, artifact clients | released | `8ad80ad3` | Defines the version-1 `wasm-reinterpret-i32-i64` capability, exact entry selection, integer-lane argument/result codecs, and semantic observation bridge. Floating manifests without the capability and capabilities with unknown fields, versions, encodings, entries, arities, kinds, or ranges fail closed. The standalone suite covers signed zero, infinities, quiet/signaling NaNs, maximal payloads, mixed signatures, and every malformed constructor path without JavaScript numeric coercion. |
| `CLOSURE-APPLICATION-OWNERSHIP` | integration/validation | pass proof, W6, W7, validation | active | `4e481e43`; adapter transfer `7de1f2ba`; interpreter carrier `7c0bb6c3`/`28aa7930` | Matches Lean's `lean_apply_*` boundary: an exclusive closure transfers fixed arguments and is freed non-recursively; a shared closure drops one reference and retains each fixed heap argument. Exact twice-application coverage fixes `FIR-BUG-impure-none-shared-closure-capture-transfer`. W7's concrete host implements and tests the transfer. The pass proof now recovers fixed-argument bounds and preserves every internal value-call successor; focused shared-stack relatedness adaptations still remain. W6 owns concrete refinement. |
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
