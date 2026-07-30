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
| Integration | integration owner | `main` | active | Main contains structured symbolic Wasm loops, Talos lowering, stack-safe resident String walkers, and the checked ledger-aware LCNF correctness endpoint at `6d61e0aa`. The retained-prefix reset/reuse client at `5b9bead7` reaches `LoweringCorrect`; `3f720ba4` extracts environment/ledger laws, `5a437fae` derives reset/reuse operational shapes plus finite-path invariant transport, `3744edf1` adds source-only allocation lifecycle transport, `0041d70c` carries exact heap-binding/reset-token provenance, `7ecdc33b` derives all three deleted-write heap shapes from successful runtime effects, and `44b1c2ff` composes those facts into the full root-aware write-readiness contract. Validation head `1762979a` remains based on the earlier semantic boundary and compares genuine native Lean stdout/stderr without requesting compiler work | Eight isolated shared-contract domains remain queued: float representation, closure ownership, argument aliases, process termination, effectful native-oracle actions, source-entry result boundaries, Lean IO-error normalization, and native source-stream capture. The last four are validation infrastructure; W7/V8 consumes them only when compiler-generated cases are ready. The umbrella check remains gated by queued proof-owned `takeClosureApplication` consumers; a fresh V8 rebuild is independently gated by W7's exhaustive float manifest cases |
| Lean pass proof | pass-proof owner | `proof/simpcase` | active | `44b1c2ff` gives object, absolute-slot `USize`, and packed-scalar writes a compiler-facing bridge from source-only binding, operand evaluation, successful mutation, and runtime relatedness to the complete root-aware readiness certificate. The nonempty-ledger and exact closed-write clients use it, eliminating their hand-built heap-cell, constructor, liveness, and bounds witnesses | Next derive and preserve the compiler typing/ownership facts that guarantee write/reset/reuse operand evaluation and operation success along arbitrary checked executions, eliminating finite fixture enumeration. The focused validation-stack consumers remain `SimpCaseRelation.lean:427` and `AlphaEqvCode.lean:2209,2358-2360` |
| W6 runtime proof | W6 owner | `wasm/talos-runtime` | active | Clean committed head `6f58d9d6`, seven main commits behind after this coordination checkpoint, composes typed unbox correctness | Continue concrete refinement and the closure-application audit in W6-owned files, then rebase before handoff. W6 owns implementation-to-concrete-host theorems, not validation adapters or the W7 compiler |
| W7 generation | generation owner | `wasm/generation` | active | Clean committed head `0e1a564a`, nineteen main commits behind after this coordination checkpoint, retains the stack-safe resident `prettyM` String walker and stress fixture | Rebase before the next handoff, then add exhaustive `float32Bits`/`float64Bits` manifest consumers at `Manifest.lean:149,255,280`. Consume termination, IO-entry/error, or stream-capture contracts only when admitting corresponding compiler-generated real-engine cases; do not implement lane-4 source projection in W7 |
| Validation | validation owner | `validation/float-corpus` | ready | Clean head `1762979a`, based directly on semantic main boundary `968ef169` and one coordination-only checkpoint behind, captures genuine native Lean stdout/stderr and compares four exact ordered-output fixtures after exhaustively normalizing Lean IO errors. Run `3eca941cc887bfc6193d453ec8d09370a0547902cb7284602392fd95e1d481b0` passes 699/699 native/LCNF cases; evidence `732aa9c60c6d4ec33e146b2fde0058029838c7fc5a7bca39591ebe1a24159013` verifies offline. The direct tier passes 9/9 at run `4a5b6433d3be535ca72402c044881061ce2a8adbeb8b367be3fdee8e5b33bc99`, evidence `2f4fd85f93c82269b84e454fdacb273f6ee13b1c4e14f9727a6f0668a862a1f9` | Shared contracts are isolated at `15a003f9`/`522ccf73`, `4a3f9eaf`, `181a098f`, `6fef4802`/`6f0487ee`/`9e00c614`/`8618f1f1`, `b3f4f5d9`, `dff585cc`, `939b8144`, and `57f3a7c5`; dependent coverage ends at `1762979a`. Harness tests are 128/128. The combined index pins 708 unique cases, 1,289 tier cases, 1,870/1,870 comparisons, 6,118 interpreter steps, 59 semantic-tag floors, and zero findings. `make check` still stops only at `AlphaEqvCode.lean:2209,2358-2360`; the fresh V8 attempt stops in W7-owned `Manifest.lean:149,255,280` before executing cases |

## Resident-helper bridge

| Helper or artifact | Generation commit | Contract base | State | Proof owner | Artifact digest |
|---|---|---|---|---|---|
| Existing resident helper set through closure matching | landed on `main` | recorded in Talos plan | generation-ready | W6 owner | recorded by individual manifests |
| Resident allocator, constructors, and styled `prettyM` through immediate Naturals | `64831f6` | `40f41c0` | generation-ready | W6 owner at the later contract bridge | styled Wasm `5d14b3fd2b1eb93de344ee69c6117e539eeed320c857248eb0fd4691b9d9e5d2` |
| Standalone immediate-Natural and UTF-8 String literals | `64831f6` | current W6 object layouts | generation-ready | W6 owner | Wasm `ab63fa578576748ff3ea8230986cf908d7285c54bc840bb60fec5fc7fa978473` |

## Contract queue

| ID | Producer | Consumers | Status | Standalone commit | Effect |
|---|---|---|---|---|---|
| `LANE-W6-W7-SPLIT` | integration | W6, W7, harness | released | `9cb483f` | Gives W6 and W7 independent branches and worktrees |
| `RESET-ERASED-RELEASE` | integration | pass proof, W6, validation | released | `373b0a9` | Reset treats erased ownership slots as no-ops; proof adaptation `8c2fff6`, W6 adaptation `afd7ab0`, and validation observation `3b82b0b` are landed |
| `W7-RESIDENT-ALLOCATOR` | W7 | W6, integration | released | `21f382c` | Zero-import allocator and styled package are generation-ready; allocator installation preserves the current 177-import `prettyM` frontier, and W6 owns the later bridge proof |
| `W7-CLOSURE-DESCRIPTORS` | W7 | W6, W7, integration, artifact clients | released | `40f41c0` | Retains the duplicate-free capture-kind table after `partialApply` imports are removed, so closure header `aux3` remains stable; W6 must rebase before W7 consumes it in the resident closure allocator |
| `W7-RESIDENT-LITERALS` | W7 | W6, integration, artifact clients | released | `64831f6` | Adds a zero-import literal fixture, internalizes immediate Naturals in linked `prettyM`, retains Strings until their JavaScript consumers become resident, and advances text/styled checkpoints to 152/153 imports |
| `FLOAT-SCALAR-RUNTIME` | integration/validation | pass proof, W6, W7, validation | active | `15a003f9`; source-accurate extension `522ccf73` | Adds bit-exact `float32Bits`/`float64Bits`, typed schemas, and LCNF codecs. Compiler-generated `dec[ref]` proves that `Float32` and `Float` boxes are always heap objects, so `522ccf73` uses `boxUsesTaggedRepresentation` and rejects tagged floating boxes. `FIR-BUG-impure-none-float-box-tagging` is fixed; the earlier tagged-decoder diagnosis is closed-not-a-bug. Validation head `1762979a` passes 699/699. Pass proof must branch on the predicate at `ElimDeadRuntimeRel.lean:8863-9172`; W7 must extend `Manifest.lean:149,255,280`; W6 owns corresponding concrete refinement. |
| `CLOSURE-APPLICATION-OWNERSHIP` | integration/validation | pass proof, W6, W7, validation | active | `4a3f9eaf` | Matches Lean's `lean_apply_*` boundary: an exclusive closure transfers fixed arguments and is freed non-recursively; a shared closure drops one reference and retains each fixed heap argument. Exact twice-application coverage fixes `FIR-BUG-impure-none-shared-closure-capture-transfer`. Pass proof owns the focused relatedness/preservation adaptations above; W6 owns concrete refinement; W7 waits for that signature/refinement handoff rather than changing compiler work speculatively. |
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
