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
| Integration | integration owner | `main` | active | Main is green through structured symbolic Wasm loops and Talos lowering at `5ead06c`. Validation head `34c33b4` is rebased onto that boundary and advances the ready stack to 671 native/LCNF cases with typed process supervision and a real divergence witness | Four isolated shared contracts are ready but not yet eligible as one stack for `main`: the older float/closure/argument-alias consumers and the native-termination consumer boundary below must be acknowledged. Dependent validation-only effect, mutation, panic, and divergence fixtures add no proof-lane work |
| Lean pass proof | pass-proof owner | `proof/simpcase` | active | Clean one-ahead head `1d164df` proves ledger-aware partial-application matching after the integrated literal and constructor checkpoints | Continue with boxes, failed-token reuse, existing-address, and external-response branches, then assemble the unified ledger-aware dispatcher. Afterwards define the entry-indexed exact ownership invariant, adapt `box` proofs to `boxUsesTaggedRepresentation` in `ElimDeadRuntimeRel.lean:8863-9172`, and prove the queued `takeClosureApplication` consumers |
| W6 runtime proof | W6 owner | `wasm/talos-runtime` | active | Head `9c6d8ca` composes structural ownership effects; the next mutation/refinement work is uncommitted only in W6-owned concrete-runtime files | Extend the already-float-aware concrete relation with the missing exhaustive `HeapRefinement.lean` cases at 35, 116, and 136. Audit closure application against `takeClosureApplication` after the current checkpoint; W6 owns the concrete refinement, not the validation implementation |
| W7 generation | generation owner | `wasm/generation` | active | Clean one-ahead head `837695c` makes resident String walkers stack-safe after numeric styling and structured loops landed on `main` | Add the exhaustive `float32Bits`/`float64Bits` manifest consumers at `Manifest.lean:149,255,280` when rebasing the next generation slice. Consume the termination policy only when admitting a real-engine case; the current source divergence fixture requests no speculative compiler work |
| Validation | validation owner | `validation/float-corpus` | ready | Clean head `34c33b4` retains the float/closure/mixed-layout, conditional-mutation, argument-alias, and ordered-panic stack, then adds isolated termination supervision at `2d8cabb` and the exact tail-divergence fixture at `34c33b4`. Run `4c8ea49d9393d7cd7d428fc57ff9d965a4ef1378a9e9d141056ea01822689060` compares 671/671 observations equal; evidence `fe4191145f80f6aab466ad048fa9e41b132a1a4324c9abfd94b6819c6f3f892f` verifies offline | Shared contracts remain isolated at `8070bcf`, `edbb9d1`, `54af365`, and `2d8cabb`. Harness tests are 125/125; index `76e252a` composes 680 unique cases and 1842/1842 equal comparisons, 5946 interpreter steps, and 41/41 semantic floors. The retained 581-case V8 matrix verifies offline and intentionally excludes alias, panic, and divergence cases. `make check` still stops only at the queued `takeClosureApplication` proof consumer in `AlphaEqvCode.lean:2209,2358-2360` |

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
| `FLOAT-SCALAR-RUNTIME` | integration/validation | pass proof, W6, W7, validation | active | `74ec190`; source-accurate extension `8070bcf` | Adds bit-exact `float32Bits`/`float64Bits`, typed schemas, and LCNF codecs. Compiler-generated `dec[ref]` proves that `Float32` and `Float` boxes are always heap objects, so `8070bcf` replaces payload-only boxing with `boxUsesTaggedRepresentation` and restores rejection of tagged floating boxes. `FIR-BUG-impure-none-float-box-tagging` is fixed; the earlier tagged-decoder diagnosis is closed-not-a-bug. Validation head `34c33b4` passes 671/671. Pass proof must branch on the new predicate at `ElimDeadRuntimeRel.lean:8863-9172`; W7 must extend `Manifest.lean:149,255,280`; W6 must extend `HeapRefinement.lean:35,116,136`. |
| `CLOSURE-APPLICATION-OWNERSHIP` | integration/validation | pass proof, W6, W7, validation | active | `edbb9d1` | Matches Lean's `lean_apply_*` boundary: an exclusive closure transfers fixed arguments and is freed non-recursively; a shared closure drops one reference and retains each fixed heap argument. Exact twice-application coverage fixes `FIR-BUG-impure-none-shared-closure-capture-transfer`. Pass proof owns the relatedness/preservation adaptations at the focused failures above; W6 owns concrete refinement; W7 waits for that signature/refinement handoff rather than changing compiler work speculatively. |
| `ARGUMENT-ALIAS-MATERIALIZATION` | integration/validation | W7, V8 adapter, W6 refinement | active | `54af365` | Adds a canonical target-sorted root-to-later-argument alias graph to every corpus descriptor. LCNF allocates each root once and retains one owned reference per aliased argument; malformed, chained, non-heap, schema-mismatched, and datum-mismatched graphs fail closed. The V8 adapter requires one compiler-manifest heap location per root with exact initial multiplicity and now tests reference counts two and three plus two independent roots. W7 should thread `argumentAliases` through `compileValidationInvocation` and `withValidationInvocation` after its current compiler slice, then admit `effect-record-aliased-byte-array-arguments`, `effect-record-triply-aliased-byte-array-arguments`, and `effect-record-two-aliased-byte-array-groups`; W6 owns any later concrete refinement, not this validation implementation. |
| `NATIVE-TERMINATION-SUPERVISION` | integration/validation | native adapter, LCNF adapter, W7/V8, Talos runners | active | `2d8cabb` | Adds manifest fields `timeoutMs` and `timeoutIsDivergence`. Native wall-clock timeout is a typed backend timeout unless explicitly promoted to semantic `diverged`; nonzero and signal-derived status is retained as backend `crash`. LCNF promotes fuel exhaustion only for the same opt-in and otherwise preserves `outOfFuel`. The dependent `failure-tail-divergence` fixture at `34c33b4` pins 256 steps and 64 exact `cases`/`lit`/`fap` repetitions. Retained V8 evidence excludes it; W7 or Talos should consume this policy only when admitting a corresponding real-engine case. |

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
