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
| Integration | integration owner | `main` | active | Main is green through ledger-aware literal matching documentation checkpoint `d5d0612`. Validation head `b9834ea` is rebased onto it and advances the ready stack to 670 native/LCNF cases, including ordered repeated-panic and native-stderr multiplicity validation | Three isolated shared contracts are ready but not yet eligible as one stack for `main`: the older float/closure consumers and the argument-alias consumer below must adapt first. Later validation-only coverage/effect/mutation/panic commits do not add consumer work and may ride the same green integration stack |
| Lean pass proof | pass-proof owner | `proof/simpcase` | active | Integrated head `d5d0612` records ledger-aware retained/deleted literal matching; the worktree has the next owned `ElimDeadMachineRel.lean` slice in progress | Extend the same result/matcher pattern to constructors, PAPs, boxes, and failed-token reuse; then cover no-allocation and external-response branches and assemble the unified ledger-aware dispatcher. Afterwards define the entry-indexed exact ownership invariant, adapt `box` proofs to `boxUsesTaggedRepresentation` in `ElimDeadRuntimeRel.lean:8863-9172`, and prove the queued `takeClosureApplication` consumers |
| W6 runtime proof | W6 owner | `wasm/talos-runtime` | active | Clean head `7229910` proves ordinary recursive decrement structure after the increment, persistent-ownership, scalar-case, and constructor-case checkpoints | Extend the already-float-aware concrete relation with the missing exhaustive `HeapRefinement.lean` cases at 35, 116, and 136. Audit closure application against `takeClosureApplication` after the current checkpoint; W6 owns the concrete refinement, not the validation implementation |
| W7 generation | generation owner | `wasm/generation` | active | Arbitrary numeric styling coverage is clean at `0f2e412`, including the production browser adapter and numeric `prettyM` work | Add the exhaustive `float32Bits`/`float64Bits` manifest consumers at `Manifest.lean:149,255,280` when rebasing the next generation slice. For closure application, consume the stable signature only after W6 states the refinement boundary; do not overlap compiler work already in flight |
| Validation | validation owner | `validation/float-corpus` | ready | Clean head `b9834ea` retains the float/closure/mixed-layout, conditional-mutation, and argument-alias stack, then validates one and two real Lean panics with ordered semantic-stderr fragments. Run `47cabb81fbc24ee1fb28cb1cb5bd72d87cc64be87e61bf2e7cca109c4d311f1f` compares 670/670 observations equal; evidence `a5efb08bd7679bdab61e96e938ffb69d068a5375faa52a795d7665d1785b3369` verifies offline | Shared contracts remain isolated at `bccfc65`, `f53a3a4`, and `790a18e`; the ordered-panic implementation is `89206b1`, coverage is `418f25c`, and repaired evidence is `b9834ea`. Harness tests are 122/122; index `600c9c0` composes 679 unique cases and 1841/1841 equal comparisons, 5690 interpreter steps, and 38/38 semantic floors. The retained 581-case V8 matrix verifies offline and intentionally excludes alias and panic cases; no panic compiler work is requested before W7 is ready. A fresh rebuild still stops at the already-queued float cases in `Fir/Wasm/Emit/Manifest.lean:149,255,280`. `make check` still stops only at the queued closure proof consumer |

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
| `FLOAT-SCALAR-RUNTIME` | integration/validation | pass proof, W6, W7, validation | active | `b29d8d5`; source-accurate extension `bccfc65` | Adds bit-exact `float32Bits`/`float64Bits`, typed schemas, and LCNF codecs. Compiler-generated `dec[ref]` proves that `Float32` and `Float` boxes are always heap objects, so `bccfc65` replaces payload-only boxing with `boxUsesTaggedRepresentation` and restores rejection of tagged floating boxes. `FIR-BUG-impure-none-float-box-tagging` is fixed; the earlier tagged-decoder diagnosis is closed-not-a-bug. Validation head `b9834ea` passes 670/670. Pass proof must branch on the new predicate at `ElimDeadRuntimeRel.lean:8863-9172`; W7 must extend `Manifest.lean:149,255,280`; W6 must extend `HeapRefinement.lean:35,116,136`. |
| `CLOSURE-APPLICATION-OWNERSHIP` | integration/validation | pass proof, W6, W7, validation | active | `f53a3a4` | Matches Lean's `lean_apply_*` boundary: an exclusive closure transfers fixed arguments and is freed non-recursively; a shared closure drops one reference and retains each fixed heap argument. Exact twice-application coverage fixes `FIR-BUG-impure-none-shared-closure-capture-transfer`. Pass proof owns the relatedness/preservation adaptations at the focused failures above; W6 owns concrete refinement; W7 waits for that signature/refinement handoff rather than changing compiler work speculatively. |
| `ARGUMENT-ALIAS-MATERIALIZATION` | integration/validation | W7, V8 adapter, W6 refinement | active | `790a18e` | Adds a canonical target-sorted root-to-later-argument alias graph to every corpus descriptor. LCNF allocates each root once and retains one owned reference per aliased argument; malformed, chained, non-heap, schema-mismatched, and datum-mismatched graphs fail closed. The V8 adapter requires one compiler-manifest heap location per root with exact initial multiplicity and now tests reference counts two and three plus two independent roots. W7 should thread `argumentAliases` through `compileValidationInvocation` and `withValidationInvocation` after its current compiler slice, then admit `effect-record-aliased-byte-array-arguments`, `effect-record-triply-aliased-byte-array-arguments`, and `effect-record-two-aliased-byte-array-groups`; W6 owns any later concrete refinement, not this validation implementation. |

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
