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

## Lane snapshot

Lane rows name their own landed commits; the board intentionally has no
moving global snapshot hash.

| Lane | Owner handle | Branch | Status | Current slice | Contract impact |
|---|---|---|---|---|---|
| Integration | integration owner | `main` | active | Main contains structured symbolic Wasm loops, Talos lowering, stack-safe resident String walkers, and the checked ledger-aware LCNF correctness endpoint at `6d61e0aa`. The retained-prefix reset/reuse client at `5b9bead7` reaches `LoweringCorrect`; `3f720ba4` extracts environment/ledger laws, `5a437fae` derives reset/reuse operational shapes plus finite-path invariant transport, `3744edf1` adds source-only allocation lifecycle transport, `0041d70c` carries exact heap-binding/reset-token provenance, `7ecdc33b` derives all three deleted-write heap shapes from successful runtime effects, `44b1c2ff` composes those facts into the full root-aware write-readiness contract, `8c6ea3e6` does the same for both reuse-token branches, `475b642b` frames recursive release/reset inside the operand's original owned closure and derives the target-ledger owner frame, `cd09942c` makes that closure certificate compositional across environment, heap, ledger, and paired-allocation transitions, `f29b5a90` derives fresh-frontier exclusion from a reusable heap ownership bound, `7ebfb53c` preserves the bound through replacement, recursive release, reset, and concrete-token reuse, `67183055` derives installed-value bounds from checked evaluation, `b05c62d5` separates target liveness from complete source-environment ownership at deleted operations, `fd4f531f` carries the local ownership invariant through allocation/reuse result binding, `15092e7c` extends it through exact hereditary bind/apply restoration with complete saved bind environments, `ba52212b` preserves it through cache persistence and the checked three-way yielded dispatcher, `a43b7f4c` carries the whole-machine invariant through both deleted-reuse token branches, `1cef5df2`/`23898302` extend and check it for deleted constructor allocation, object-field writes, and reset, `8bde8037`/`475451b9` complete and check deleted-write ownership for absolute-slot `USize` and packed-scalar updates, and `597b57ea`/`633d259d` preserve and check retained named/local application ownership across bind-frame pushes and nullary local aliasing. Validation head `1762979a` remains based on the earlier semantic boundary and compares genuine native Lean stdout/stderr without requesting compiler work | Eight isolated shared-contract domains remain queued: float representation, closure ownership, argument aliases, process termination, effectful native-oracle actions, source-entry result boundaries, Lean IO-error normalization, and native source-stream capture. The last four are validation infrastructure; W7/V8 consumes them only when compiler-generated cases are ready. W7's float consumers and fresh V8 execution are complete; integration is now gated by proof-owned `takeClosureApplication`/float-box consumers and W6's concrete float layout/refinement handoff |
| Lean pass proof | pass-proof owner | `proof/simpcase` | active | `597b57ea` introduces one runtime-neutral let-action ownership seam and proves retained `.fap` and `.fvar` preservation through value binding, invocation control changes, and bind-frame pushes; `633d259d` checks exact named invocation and nullary local aliasing fixtures | Preserve ownership across the remaining retained active-code result-producing families, then strengthen the global exact active-code dispatcher and combine it with the compositional source-only closure certificate. The focused validation-stack consumers remain `SimpCaseRelation.lean:427` and `AlphaEqvCode.lean:2209,2358-2360` |
| W6 runtime proof | W6 owner | `wasm/talos-runtime` | active | Clean committed head `62872f62`, three main commits behind at this checkpoint, continues the independent cache/refinement proof stack | Publish the standalone Float32/Float boxed-kind codes, packed storage/projection/mutation support, resolver support, and `HeapRefinement` cases consumed by W7; also complete the closure-application audit. W6 owns implementation-to-concrete-host theorems, not validation adapters or the W7 compiler |
| W7 generation | generation owner | `wasm/generation` | ready | Generation-ready candidate `517a2d04` before this coordination-only rebase exhaustively emits and consumes `float32Bits`/`float64Bits`, accepts raw-bit command arguments, and executes exact Float32/Float values through the semantic and concrete hosts. The 104,788-byte styled `prettyM` package owns/exports memory, has zero imports, and preserves `PrettyTrace` styling | Full artifact/Node/Chrome/native-oracle checks pass. Fresh retained V8 evidence `11284cc4f04bf308b78f2b3757d4bd8c2ea9c96ec637455bdfc37062333a5fff` has 1,743/1,743 successful backend results, 581/581 equality for every native/LCNF/V8 pair, and zero findings. Integration still waits for the proof and W6 contract consumers; provisional W7 float box codes are not `linked/accepted` until W6 publishes the layout contract |
| Validation | validation owner | `validation/float-corpus` | ready | Clean head `1762979a`, based directly on semantic main boundary `968ef169` and one coordination-only checkpoint behind, captures genuine native Lean stdout/stderr and compares four exact ordered-output fixtures after exhaustively normalizing Lean IO errors. Run `3eca941cc887bfc6193d453ec8d09370a0547902cb7284602392fd95e1d481b0` passes 699/699 native/LCNF cases; evidence `732aa9c60c6d4ec33e146b2fde0058029838c7fc5a7bca39591ebe1a24159013` verifies offline. The direct tier passes 9/9 at run `4a5b6433d3be535ca72402c044881061ce2a8adbeb8b367be3fdee8e5b33bc99`, evidence `2f4fd85f93c82269b84e454fdacb273f6ee13b1c4e14f9727a6f0668a862a1f9` | Shared contracts are isolated at `15a003f9`/`522ccf73`, `4a3f9eaf`, `181a098f`, `6fef4802`/`6f0487ee`/`9e00c614`/`8618f1f1`, `b3f4f5d9`, `dff585cc`, `939b8144`, and `57f3a7c5`; dependent coverage ends at `1762979a`. Harness tests are 128/128. The combined index pins 708 unique cases, 1,289 tier cases, 1,870/1,870 comparisons, 6,118 interpreter steps, 59 semantic-tag floors, and zero findings. `make check` still stops only at `AlphaEqvCode.lean:2209,2358-2360`; the fresh V8 attempt stops in W7-owned `Manifest.lean:149,255,280` before executing cases |

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
| `CLOSURE-APPLICATION-OWNERSHIP` | integration/validation | pass proof, W6, W7, validation | active | `4e481e43`; adapter transfer `7de1f2ba` | Matches Lean's `lean_apply_*` boundary: an exclusive closure transfers fixed arguments and is freed non-recursively; a shared closure drops one reference and retains each fixed heap argument. Exact twice-application coverage fixes `FIR-BUG-impure-none-shared-closure-capture-transfer`. W7's concrete host implements and tests the transfer. Pass proof owns the focused relatedness/preservation adaptations; W6 owns concrete refinement. |
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
