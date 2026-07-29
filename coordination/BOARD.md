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
| Integration | integration owner | `main` | active | Main contains structured symbolic Wasm loops, Talos lowering, stack-safe resident String walkers, and ledger-aware matching through the generic runtime-neutral erased/deleted layer at `cea47e55`. Validation head `3202ebf4` remains based on the earlier documented boundary and exhaustively compares Lean IO errors without requesting compiler work | Seven isolated shared-contract domains remain queued: float representation, closure ownership, argument aliases, process termination, effectful native-oracle actions, source-entry result boundaries, and Lean IO-error normalization. The last three are validation infrastructure; W7/V8 consumes them only when compiler-generated IO cases are ready. The umbrella check remains gated by the queued `takeClosureApplication` proof consumers; the retained V8 rebuild is independently gated by W7's exhaustive float manifest cases |
| Lean pass proof | pass-proof owner | `proof/simpcase` | active | Runtime-neutral ledger matching is integrated at `cea47e55`: paired/source-only determinism, retained erased lets, generic deleted runtime-neutral lets, and exact traversal wrappers all preserve the carried target allocation history | Continue retained copies/projections, control/application steps, existing-address mutations, and allocation-capable external responses, then assemble the unified ledger-aware dispatcher and entry-indexed ownership invariant. Also adapt `box` proofs to `boxUsesTaggedRepresentation` in `ElimDeadRuntimeRel.lean:8863-9172` and prove the queued `takeClosureApplication` consumers before the validation stack lands |
| W6 runtime proof | W6 owner | `wasm/talos-runtime` | active | Committed head `e836053b`, based on the earlier main boundary and three commits behind after this coordination checkpoint, composes `isShared` direct correctness; a W6-owned continuation edits `ConcreteCompilerCorrectness.lean`, `ConcreteResolver.lean`, and `ConcreteSupportedExportCorrectness.lean` | Continue the concrete refinement and closure-application audit in W6-owned files, checkpoint, and rebase before handoff. W6 owns implementation-to-concrete-host theorems, not the validation adapters or the W7 compiler |
| W7 generation | generation owner | `wasm/generation` | active | The stack-safe resident `prettyM` String walker and stress fixture are integrated on `main` at `7d9c1ad9` and `0e1a564a`; the clean generation branch is eight main commits behind after this coordination checkpoint | Rebase before the next handoff, then add the exhaustive `float32Bits`/`float64Bits` manifest consumers at `Manifest.lean:149,255,280`. Consume `processTermination`, `entryKind`, and IO-error normalization only when admitting corresponding compiler-generated real-engine cases; do not implement lane-4 source projection in W7 |
| Validation | validation owner | `validation/float-corpus` | ready | Clean head `3202ebf4`, based on semantic boundary `1fc5b136` and one coordination-only main commit behind after this checkpoint, reconstructs all 19 Lean `IO.Error` constructors and retains an exact effect that precedes an exception. Run `5ddf925f5f609226828eee37427c2cdfb3652e020597e25f185961b78fc15bcc` passes 695/695 native/LCNF cases; evidence `b0a8a31ec931f68128c8d83f5bb6cbc943cd7821bb7d875af7d1a7f32c8f7e57` verifies offline. The direct tier passes 9/9 at run `dfb51e8df2beaf53a1a6fd1ff7a2c0115e5678244d0a8737852d9ad72e1f29d8`, evidence `43c13f1435823ce57a92d73c376f94702ad14871a921746b66a3432aa7fe3a09` | Shared contracts are isolated at `e33090e5`/`95d6f64f`, `88565d76`, `8be831fc`, `048247d5`/`831c5475`, `2595e45b`, `e5889fcb`, and `05798764`; exhaustive dependent coverage is at `3202ebf4`. Harness tests are 127/127. The combined index pins 704 unique cases, 1,866/1,866 comparisons, 6,047 interpreter steps, 50 semantic-tag floors, and zero findings. `make check` still stops only at the queued proof-owned `takeClosureApplication` consumers in `AlphaEqvCode.lean:2209,2358-2360` |

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
| `FLOAT-SCALAR-RUNTIME` | integration/validation | pass proof, W6, W7, validation | active | `e33090e5`; source-accurate extension `95d6f64f` | Adds bit-exact `float32Bits`/`float64Bits`, typed schemas, and LCNF codecs. Compiler-generated `dec[ref]` proves that `Float32` and `Float` boxes are always heap objects, so `95d6f64f` replaces payload-only boxing with `boxUsesTaggedRepresentation` and restores rejection of tagged floating boxes. `FIR-BUG-impure-none-float-box-tagging` is fixed; the earlier tagged-decoder diagnosis is closed-not-a-bug. Validation head `3202ebf4` passes 695/695. Pass proof must branch on the new predicate at `ElimDeadRuntimeRel.lean:8863-9172`; W7 must extend `Manifest.lean:149,255,280`; W6 owns the corresponding concrete refinement. |
| `CLOSURE-APPLICATION-OWNERSHIP` | integration/validation | pass proof, W6, W7, validation | active | `88565d76` | Matches Lean's `lean_apply_*` boundary: an exclusive closure transfers fixed arguments and is freed non-recursively; a shared closure drops one reference and retains each fixed heap argument. Exact twice-application coverage fixes `FIR-BUG-impure-none-shared-closure-capture-transfer`. Pass proof owns the relatedness/preservation adaptations at the focused failures above; W6 owns concrete refinement; W7 waits for that signature/refinement handoff rather than changing compiler work speculatively. |
| `ARGUMENT-ALIAS-MATERIALIZATION` | integration/validation | W7, V8 adapter, W6 refinement | active | `8be831fc` | Adds a canonical target-sorted root-to-later-argument alias graph to every corpus descriptor. LCNF allocates each root once and retains one owned reference per aliased argument; malformed, chained, non-heap, schema-mismatched, and datum-mismatched graphs fail closed. The V8 adapter requires one compiler-manifest heap location per root with exact initial multiplicity and now tests reference counts two and three plus two independent roots. W7 should thread `argumentAliases` through `compileValidationInvocation` and `withValidationInvocation` after its current compiler slice, then admit `effect-record-aliased-byte-array-arguments`, `effect-record-triply-aliased-byte-array-arguments`, and `effect-record-two-aliased-byte-array-groups`; W6 owns any later concrete refinement, not this validation implementation. |
| `NATIVE-TERMINATION-SUPERVISION` | integration/validation | native adapter, LCNF adapter, W7/V8, Talos runners | active | `048247d5`; typed policy `831c5475` | Adds `timeoutMs` plus the backend-neutral `processTermination` enum: `protocol`, `timeoutDivergence`, or `sourceExit`. Native timeout is a typed backend timeout unless opted into divergence; ordinary nonzero status and signals remain crashes unless an exact source-exit fixture opts in, and signals always remain crashes. LCNF promotes only same-step, well-typed `Source.exitNat` terminal evidence under `sourceExit`, without changing the canonical interpreter result theorem. The divergence fixture at `6c627d82` pins 256 steps; source-exit fixture `1fc76e87` pins statuses zero/seven and one exact external step. Retained V8 evidence excludes both. W7 or Talos should consume this policy only when admitting corresponding real-engine cases; no compiler-side work is requested now. |
| `EFFECTFUL-NATIVE-ORACLE` | integration/validation | native and direct-native adapters; future V8/Talos adapter authors | active | `2595e45b` | Replaces `Case.native : Unit → ValidationDatum` with a delayed `Unit → IO ValidationDatum` action and makes semantic effect/stderr drains independent of a successful return value. Existing pure fixtures lift explicitly and all 695 source plus 9 direct observations pass. This is the foundation for comparing true Lean `IO.Error` exceptions and source output; it changes no descriptor, compiler ABI, canonical interpreter theorem, or W6/W7 implementation surface. |
| `SOURCE-ENTRY-RESULT` | integration/validation | LCNF adapter, W7/V8 adapter, Talos runners | active | `e5889fcb` | Adds portable `entryKind = value | io` to corpus requests and descriptors. For `io`, the LCNF adapter appends exactly one erased `RealWorld` argument and decodes `EStateM.Result IO.Error α`; the native oracle runs the actual source action. Dependent fixtures at `1f3fda10` compare a returned `IO Nat` and an exact `IO.userError`, fixing `FIR-BUG-validation-none-io-entry-world-result`. W7 and Talos should consume the field only when admitting compiler-generated IO cases; no compiler work is requested before that boundary. |
| `LEAN-IO-ERROR-NORMALIZATION` | integration/validation | native and LCNF adapters; future W7/V8 and Talos adapters | active | `05798764`; exhaustive implementation and fixtures `3202ebf4` | Normalizes every Lean `IO.Error` constructor to a stable kebab-case kind plus the exact Lean `IO.Error.toString` message. LCNF reconstructs all 19 constructor layouts, including optional filenames and scalar OS codes; unknown tags and malformed payloads fail closed. Nineteen exact constructor cases plus one post-failure-effect case pass against native. W7 and Talos consume this mapping only when compiler-generated IO cases are admitted; no compiler-side work is requested now. |

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
