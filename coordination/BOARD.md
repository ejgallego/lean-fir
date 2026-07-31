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
  `0971181c`; the combined proof/validation head is `0971181c`, so the long
  validation branch is fifty commits behind and one hundred twelve
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
- W6 has advanced its committed head to `13958eb4`, one hundred
  thirty-four commits ahead and seven behind functional `main`; its worktree
  currently has two uncommitted W6-owned proof edits, and no formal
  integration handoff has been published. W7 is clean at `e5c67f54`,
  twenty-two commits ahead and thirty-seven behind functional `main`; its exact
  float manifest-execution handoff and required check report have not been
  published.
  Integration must not absorb any of those working trees; each lane runs its
  required checks, cleans, and sends the prescribed handoff before landing.
- Released contract `8ad80ad3` supplies the fail-closed
  `bitExactFloatTransport` consumer contract independently of the queued Lean
  float stack. It selects an integer-lane Wasm facade, preserves all raw f32/f64
  bits as `BigInt`, rejects missing or malformed capabilities, and passes the
  complete root gate. Integration consumer `57f13122` now selects that facade
  in the canonical validation runner and passes 613 native/LCNF cases, all 581
  compiler-admitted V8 cases, and 1,784/1,784 comparisons. W7's clean facade
  and consumer checkpoint is `e5c67f54`; its next action is to rebase after the
  queued Lean float contracts land.
- Integration has split the required Lean float contract from the unrelated
  closure-ownership queue on `integration/float-runtime-contract`, current head
  `3215be10` on base `57f13122`. Commits `2aa27f87`, `5dcb1e03`, and
  `3215be10` add bit-exact scalar constructors, heap-only float boxes, and the
  shared ABI boundary; W7 handoff `1f16caf6` keeps manifest matches exhaustive.
  The current four-commit candidate passes `make check` with 613 native/LCNF
  cases, all 581 V8 cases, 1,784/1,784 comparisons, every coverage floor, all
  bug-card checks, and the trusted-assumption gate; it also passes
  `git diff --check` and `lake build Fir.Wasm.Emit.Examples`.
  `make talos-check` now isolates the remaining owned work: the pass-proof lane
  must adapt `ElimDeadRuntimeRel.lean:8909-9218` to
  `boxUsesTaggedRepresentation`, and W6 must add both float alternatives in
  `Concrete/HeapRefinement.lean:35,116,136`. No integration or W7 file is
  currently blocking that Talos build.

## Lane snapshot

Lane rows name their own landed commits; the board intentionally has no
moving global snapshot hash.

| Lane | Owner handle | Branch | Status | Current slice | Contract impact |
|---|---|---|---|---|---|
| Integration | integration owner | `main` | active | Main contains structured symbolic Wasm loops, Talos lowering, stack-safe resident String walkers, and the checked ledger-aware LCNF correctness endpoint at `6d61e0aa`. The retained-prefix reset/reuse client at `5b9bead7` reaches `LoweringCorrect`; `3f720ba4` extracts environment/ledger laws, `5a437fae` derives reset/reuse operational shapes plus finite-path invariant transport, `3744edf1` adds source-only allocation lifecycle transport, `0041d70c` carries exact heap-binding/reset-token provenance, `7ecdc33b` derives all three deleted-write heap shapes from successful runtime effects, `44b1c2ff` composes those facts into the full root-aware write-readiness contract, `8c6ea3e6` does the same for both reuse-token branches, `475b642b` frames recursive release/reset inside the operand's original owned closure and derives the target-ledger owner frame, `cd09942c` makes that closure certificate compositional across environment, heap, ledger, and paired-allocation transitions, `f29b5a90` derives fresh-frontier exclusion from a reusable heap ownership bound, `7ebfb53c` preserves the bound through replacement, recursive release, reset, and concrete-token reuse, `67183055` derives installed-value bounds from checked evaluation, `b05c62d5` separates target liveness from complete source-environment ownership at deleted operations, `fd4f531f` carries the local ownership invariant through allocation/reuse result binding, `15092e7c` extends it through exact hereditary bind/apply restoration with complete saved bind environments, `ba52212b` preserves it through cache persistence and the checked three-way yielded dispatcher, `a43b7f4c` carries the whole-machine invariant through both deleted-reuse token branches, `1cef5df2`/`23898302` extend and check it for deleted constructor allocation, object-field writes, and reset, `8bde8037`/`475451b9` complete and check deleted-write ownership for absolute-slot `USize` and packed-scalar updates, `597b57ea`/`633d259d` preserve and check retained named/local application ownership across bind-frame pushes and nullary local aliasing, `51494be3`/`89d6a99e` preserve and check root-free retained erased, `USize`, and scalar result binding, `b535c662`/`61fe8259` preserve and check retained object projection, unbox, and sharedness reads, `8e144c34`/`0a5aa2f5` preserve and check retained heap-backed literal and constructor allocation ownership, `6f708f42`/`588146ac` preserve and check retained partial-application closure and heap-box allocation ownership, `0d333649`/`997a8928` complete the retained-family ownership matrix with heap reset plus both reuse-token branches, `fbf34a80`/`fff91175` complete and check source, exact-shadow, and reachable active-code ownership dispatch, `88c85852`/`991c36ee` preserve and check every internal named-invocation successor, and `7c0bb6c3`/`28aa7930` recover closure fixed-argument bounds and complete the ownership-strengthened dispatcher for every internal control. Validation at `0971181c` gates 613 native/LCNF cases and all 581 compiler-admitted V8 cases through immutable receipts, offline comparison attestations, and strict plan admission fences while the long-only IO/Float frontier remains isolated. | Eight isolated shared-contract domains remain queued: float representation, closure ownership, argument aliases, process termination, effectful native-oracle actions, source-entry result boundaries, Lean IO-error normalization, and native source-stream capture. The last four are validation infrastructure; W7/V8 consumes them only when compiler-generated cases are ready. Thirty-two scalar closure fixtures are explicitly tagged `wasm-generation-pending`; W7 need not overlap its compiler work, and later admission only removes that fence after external-engine checks. W7's float consumers and fresh V8 execution are complete; integration is now gated by proof-owned `takeClosureApplication`/float-box consumers and W6's concrete float layout/refinement handoff. |
| Lean pass proof | pass-proof owner | `proof/simpcase` | active | Functional proof head `c904f3e8` is on `main`, and the clean proof worktree is aligned. The combined source-owned/ledger simulation remains checked through `LoweringCorrect`. The target side uses a step-preserved three-phase allocation/control invariant rather than any finite target execution graph. Its singleton live-return facts now adapt to the arbitrary `TargetMappedOwnerPrefix`; the generic theorem excludes any source location distinct from every proof-visible owner of an arbitrary mapped target prefix. The post-rebase gate passes 622 unique cases, 1,784/1,784 comparisons, all coverage floors, 84 bug cards, and exactly one registered trusted axiom. | After reassessment, derive `TargetMappedOwnerPrefix` from arbitrary exact checked compiler residuals and replace the remaining finite source reset/reuse classification with generic operation-shape/ownership premises. When the queued float runtime contract lands, separately adapt the proof-owned `ElimDeadRuntimeRel.lean:8909-9218` consumer to `boxUsesTaggedRepresentation`. |
| W6 runtime proof | W6 owner | `wasm/talos-runtime` | active | Committed head `13958eb4`, one hundred thirty-four commits ahead and seven behind functional `main`, separates recursive callee contexts in the concrete compiler-correctness stack; its worktree currently has two uncommitted W6-owned proof edits. | Rebase, add both float alternatives required by `Fir/Wasm/Concrete/HeapRefinement.lean:35,116,136` against `integration/float-runtime-contract`, run/report the required full and Talos checks, and publish a formal handoff before integration. Float32/Float boxed-kind codes, packed storage/projection/mutation support, resolver support, and the closure-application audit remain W6-owned; W6 owns implementation-to-concrete-host theorems, not validation adapters or the W7 compiler. |
| W7 generation | generation owner | `wasm/generation` | active | Clean committed head `e5c67f54`, thirty-seven commits behind and twenty-two ahead of functional `main`, executes exact Float32/Float64 results through the manifest's integer-lane facade. Earlier clean checkpoints expose the versioned `bitExactFloatTransport` capability; manifest handoff `1f16caf6` is included in the isolated integration candidate. | Rebase after the shared float contract lands and publish the exact check results and formal artifact handoff; the commit is observed, not yet accepted. The thirty-two scalar closure cases are only future `wasm-generation-pending` admission probes and require no overlap now. The queued Lean float/closure stack still needs proof-owned float-box adaptation and W6 concrete refinement before the final artifact becomes `linked/accepted`. |
| Compiler-native Wasm | integration owner | `wasm/lcnf-c` | parked | Landed checkpoint `a4855402` adds a separately packaged C/Emscripten `Std.Format.prettyM` facade on top of the optimized final-LCNF-to-C route from `2760e3e0`. The browser adapter shares the compact `Format` request and exact `{text, events}` trace contract with W7's FIR-native facade while retaining a private bulk wire, verified Emscripten loader, full pinned Lean runtime, and independent package. The differential suite compares Unicode, grouping, nesting, tags, arbitrary-precision values, initial columns, malformed requests, repeated calls, and a one-MiB UTF-8 transfer through both engines | No shared semantic contract changed and the packages remain physically independent. The lane consumes `Std.Format.prettyM`, final impure LCNF, and Lean's C ABI without changing the symbolic Wasm, W6 concrete-runtime, or W7 resident-runtime surfaces. Resume with controlled sampled profiling of the facade wire and generated C before accepting a runtime optimization |
| Validation | validation owner | `validation/float-corpus` | active | Clean coordination head `cfa17d81`, with validated functional head `96eec154` on semantic base `fff91175`, is fifty commits behind and one hundred twelve ahead of functional `main` at `0971181c`. Its 1,008-case native/LCNF run and 9-case direct-machine run verify offline with zero findings; the composed long-stack index retains 1,017 comparisons, 9,939 interpreter steps, 193 semantic-tag floors, and 152 semantic domains. Current-main extractions `e08784b3`, `6ab2efed`, `e7f2b457`, `9f067817`, `3853a923`, `8ea9f75b`, and `0971181c` independently land retained-corpus attribution, immutable evidence/attestations, the Bool plus unsigned and signed scalar entry ABIs, 41 semantic floors, 116 conjunctive domains, 613 native/LCNF cases, and the enforced 581-case native-oracle V8 gate. | The next long-branch rebase drops duplicated mechanisms from `a2907a66`, `7c87e6ec`, `bb387042`, `9171fdd6`, and `cb03e9ab`, already superseded by `15b8727e`, `e08784b3`, `6ab2efed`, `e7f2b457`, `9f067817`, and `3853a923`; it retains long-only Float/IO domains as an additive post-contract calibration. Shared float, closure, alias, termination, IO, and stream-capture contracts remain isolated and require the recorded proof/W6/W7 handoffs before integration. |

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
| `FLOAT-SCALAR-RUNTIME` | integration/validation | pass proof, W6, W7, validation | active | current split candidate `2aa27f87` + heap-only box `5dcb1e03` + W7 manifest `1f16caf6` + boundary `3215be10`, on base `57f13122` | Adds bit-exact `float32Bits`/`float64Bits`, heap-only boxes, exhaustive manifest values, and the exact shared ABI boundary without the unrelated closure-ownership stack. The current candidate passes the complete `make check` gate (613 native/LCNF, 581 V8, 1,784/1,784 comparisons). Pass proof owns `ElimDeadRuntimeRel.lean:8909-9218`; W6 owns `Concrete/HeapRefinement.lean:35,116,136`, stable box-kind/layout signatures, and concrete refinement before the contract lands or the artifact becomes `linked/accepted`. |
| `WASM-FLOAT-REINTERPRET` | integration | W6, W7, Talos adapter | active | candidate `37288f87` on base `c5584f4e` | Adds symbolic and binary support for Wasm opcodes `i32.reinterpret_f32`, `i64.reinterpret_f64`, `f32.reinterpret_i32`, and `f64.reinterpret_i64`, with exact physical-lane validation and guards. `make check` is green. `make talos-check` reaches the expected exhaustive-match failure in W6-owned `FirTalos.Adapter.lean:69`; map the four cases to Talos's existing `.i32ReinterpretF32`, `.i64ReinterpretF64`, `.f32ReinterpretI32`, and `.f64ReinterpretI64`. After that adapter handoff, W7 consumes the contract in an integer-lane facade that preserves signaling-NaN payloads across JavaScript. |
| `BIT-EXACT-FLOAT-MANIFEST-TRANSPORT` | integration | W7, validation, artifact clients | released | contract `8ad80ad3`; canonical validation consumer `57f13122` | Defines the version-1 `wasm-reinterpret-i32-i64` capability, exact entry selection, integer-lane argument/result codecs, and semantic observation bridge. Floating manifests without the capability and capabilities with unknown fields, versions, encodings, entries, arities, kinds, or ranges fail closed. The standalone suite covers signed zero, infinities, quiet/signaling NaNs, maximal payloads, mixed signatures, and every malformed constructor path without JavaScript numeric coercion; the root validation runner now consumes the facade and passes the complete 613-case native/LCNF plus 581-case V8 gate. |
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
