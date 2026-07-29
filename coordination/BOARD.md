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
| Integration | integration owner | `main` | active | Main is green through the proof-relevant target-allocation-ledger carrier checkpoint `5352db0`. Validation head `2253f50` is rebased onto documentation checkpoint `cf7831b` and advances the ready stack to 669 native/LCNF cases, including Lean panic default-return and semantic-stderr validation | Three isolated shared contracts are ready but not yet eligible as one stack for `main`: the older float/closure consumers and the argument-alias consumer below must adapt first. Later validation-only coverage/effect/mutation/panic commits do not add consumer work and may ride the same green integration stack |
| Lean pass proof | pass-proof owner | `proof/simpcase` | active | Integrated head `5352db0` carries `TargetAllocationLedger` as proof-relevant runtime history: empty initialization, source-only preservation, paired-allocation extension using the returned renaming, machine-state exposure/forgetting, and a migrated non-empty-target fixture | Thread `SomeLedgerBinderReadyReachableMachineRelated` through the non-lockstep step matcher, then define the ledger-aware entry-indexed exact ownership invariant and derive edge-specific facts. Afterwards adapt `box` proofs to `boxUsesTaggedRepresentation` in `ElimDeadRuntimeRel.lean:8863-9172` without adding floating cases to `scalarFromType`; separately prove `takeClosureApplication` preservation/relatedness for `SimpCaseRelation.lean:427` and `AlphaEqvCode.lean:2209,2358-2360` |
| W6 runtime proof | W6 owner | `wasm/talos-runtime` | active | Ordered constructor case dispatch is landed at `911f358`; `ConcreteCompilerCorrectness.lean` contains the current follow-on work | Extend the already-float-aware concrete relation with the missing exhaustive `HeapRefinement.lean` cases at 35, 116, and 136. Audit closure application against `takeClosureApplication` after the current checkpoint; W6 owns the concrete refinement, not the validation implementation |
| W7 generation | generation owner | `wasm/generation` | active | Arbitrary numeric styling coverage is clean at `0f2e412`, including the production browser adapter and numeric `prettyM` work | Add the exhaustive `float32Bits`/`float64Bits` manifest consumers at `Manifest.lean:149,255,280` when rebasing the next generation slice. For closure application, consume the stable signature only after W6 states the refinement boundary; do not overlap compiler work already in flight |
| Validation | validation owner | `validation/float-corpus` | ready | Clean head `2253f50` retains the float/closure/mixed-layout, conditional-mutation, and argument-alias stack, then adds stable Lean panic ABI and real-process stderr cross-checking at `b1f87ca` plus durable failure coverage at `2253f50`. Run `45c7146aa1b17dbd3cfbfdf6dd6fd6c6c43cb4960558de82a1c4677bfb8f636d` compares 669/669 observations equal; evidence `2f96f23376e262d01a56c468618391d675f38f098900ec97304bfa6230940583` verifies offline | Shared contracts remain isolated at `790fed4`, `c52fafc`, and `11351cd`; codec `615118d`, fixtures `beefd24`, semantic coverage `09c7056`, conditional effects `a6f35a3`, conditional mutation `d9471c4`, alias fixtures `9b5b9e4`/`7b8b979`, and panic `b1f87ca`/`2253f50` are dependent slices. Harness tests are 121/121; index `5fc4354` composes 678 unique cases and 1840/1840 equal comparisons, 5676 interpreter steps, and 37/37 semantic floors. The retained 581-case V8 matrix verifies offline and intentionally excludes the alias and panic cases; no panic compiler work is requested before W7 is ready. A fresh rebuild still stops at the already-queued float cases in `Fir/Wasm/Emit/Manifest.lean:149,255,280`. `make check` still stops only at the queued closure proof consumer |

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
| `FLOAT-SCALAR-RUNTIME` | integration/validation | pass proof, W6, W7, validation | active | `2ef0c3a`; source-accurate extension `790fed4` | Adds bit-exact `float32Bits`/`float64Bits`, typed schemas, and LCNF codecs. Compiler-generated `dec[ref]` proves that `Float32` and `Float` boxes are always heap objects, so `790fed4` replaces payload-only boxing with `boxUsesTaggedRepresentation` and restores rejection of tagged floating boxes. `FIR-BUG-impure-none-float-box-tagging` is fixed; the earlier tagged-decoder diagnosis is closed-not-a-bug. Validation head `2253f50` passes 669/669. Pass proof must branch on the new predicate at `ElimDeadRuntimeRel.lean:8863-9172`; W7 must extend `Manifest.lean:149,255,280`; W6 must extend `HeapRefinement.lean:35,116,136`. |
| `CLOSURE-APPLICATION-OWNERSHIP` | integration/validation | pass proof, W6, W7, validation | active | `c52fafc` | Matches Lean's `lean_apply_*` boundary: an exclusive closure transfers fixed arguments and is freed non-recursively; a shared closure drops one reference and retains each fixed heap argument. Exact twice-application coverage fixes `FIR-BUG-impure-none-shared-closure-capture-transfer`. Pass proof owns the relatedness/preservation adaptations at the focused failures above; W6 owns concrete refinement; W7 waits for that signature/refinement handoff rather than changing compiler work speculatively. |
| `ARGUMENT-ALIAS-MATERIALIZATION` | integration/validation | W7, V8 adapter, W6 refinement | active | `11351cd` | Adds a canonical target-sorted root-to-later-argument alias graph to every corpus descriptor. LCNF allocates each root once and retains one owned reference per aliased argument; malformed, chained, non-heap, schema-mismatched, and datum-mismatched graphs fail closed. The V8 adapter requires one compiler-manifest heap location per root with exact initial multiplicity and now tests reference counts two and three plus two independent roots. W7 should thread `argumentAliases` through `compileValidationInvocation` and `withValidationInvocation` after its current compiler slice, then admit `effect-record-aliased-byte-array-arguments`, `effect-record-triply-aliased-byte-array-arguments`, and `effect-record-two-aliased-byte-array-groups`; W6 owns any later concrete refinement, not this validation implementation. |

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
