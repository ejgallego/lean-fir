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
| Integration | integration owner | `main` | active | Main is green through the strict reset/reuse compiler package checkpoint `25cf93a`. Validation head `df73718` is rebased through its documentation checkpoint `ec13535` and advances the ready stack to 665 native/LCNF cases with evidence-derived semantic coverage floors | Three isolated shared contracts are ready but not yet eligible as one stack for `main`: the older float/closure consumers and the argument-alias consumer below must adapt first. Later validation-only coverage/effect/mutation commits do not add consumer work and may ride the same green integration stack |
| Lean pass proof | pass-proof owner | `proof/simpcase` | active | Integrated head `25cf93a` migrates the one-cell reset/reuse fixture to an exact ownership contract and gives both it and the owned-child fixture checked whole-program equations, strict `ElimDeadCompilerAdmissibleRun` packages, and compiler-facing `LoweringCorrect` endpoints | Derive unmapped/source-only locations from an auditable compiler ownership invariant and exercise the bridge with a non-empty target. Afterwards adapt `box` proofs to `boxUsesTaggedRepresentation` in `ElimDeadRuntimeRel.lean:8863-9172` without adding floating cases to `scalarFromType`; separately prove `takeClosureApplication` preservation/relatedness for `SimpCaseRelation.lean:427` and `AlphaEqvCode.lean:2209,2358-2360` |
| W6 runtime proof | W6 owner | `wasm/talos-runtime` | active | Ordered constructor case dispatch is landed at `911f358`; `ConcreteCompilerCorrectness.lean` contains the current follow-on work | Extend the already-float-aware concrete relation with the missing exhaustive `HeapRefinement.lean` cases at 35, 116, and 136. Audit closure application against `takeClosureApplication` after the current checkpoint; W6 owns the concrete refinement, not the validation implementation |
| W7 generation | generation owner | `wasm/generation` | active | Arbitrary numeric styling coverage is clean at `0f2e412`, including the production browser adapter and numeric `prettyM` work | Add the exhaustive `float32Bits`/`float64Bits` manifest consumers at `Manifest.lean:149,255,280` when rebasing the next generation slice. For closure application, consume the stable signature only after W6 states the refinement boundary; do not overlap compiler work already in flight |
| Validation | validation owner | `validation/float-corpus` | ready | Clean head `df73718` retains the float/closure/mixed-layout and conditional-mutation stack, then adds canonical runner-supplied heap-argument identity at `8621f02` and an exact native/LCNF copy-on-write fixture at `9a19b39`. Run `8a2ce06946255d901cb3391d7f5abd71f355c5084a38f4a6e6b2612a1e47e29e` compares 665/665 observations equal; evidence `116e9453db6954fb1876c980d1ff5ce19c63d6da77f7823d5cf0c77e258b6050` verifies offline | Shared contracts remain isolated at `d2adb82`, `be4c959`, and `8621f02`; codec `c604209`, fixtures `88c9f5d`, semantic coverage `c3fcd2e`, conditional effects `3589bbd`, conditional mutation `61bd97a`, and aliased-argument fixture `9a19b39` are dependent slices. Harness tests are 119/119; index `89bed79` composes 674 unique cases and 1836/1836 equal comparisons, 5628 interpreter steps, and 34/34 semantic floors. The retained 581-case V8 matrix verifies offline and deliberately excludes the alias case; its adapter now fails closed on distinct locations or the wrong initial reference count. `make check` still stops only at the queued closure proof consumer |

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
| `FLOAT-SCALAR-RUNTIME` | integration/validation | pass proof, W6, W7, validation | active | `0f04761`; source-accurate extension `d2adb82` | Adds bit-exact `float32Bits`/`float64Bits`, typed schemas, and LCNF codecs. Compiler-generated `dec[ref]` proves that `Float32` and `Float` boxes are always heap objects, so `d2adb82` replaces payload-only boxing with `boxUsesTaggedRepresentation` and restores rejection of tagged floating boxes. `FIR-BUG-impure-none-float-box-tagging` is fixed; the earlier tagged-decoder diagnosis is closed-not-a-bug. Validation head `df73718` passes 665/665. Pass proof must branch on the new predicate at `ElimDeadRuntimeRel.lean:8863-9172`; W7 must extend `Manifest.lean:149,255,280`; W6 must extend `HeapRefinement.lean:35,116,136`. |
| `CLOSURE-APPLICATION-OWNERSHIP` | integration/validation | pass proof, W6, W7, validation | active | `be4c959` | Matches Lean's `lean_apply_*` boundary: an exclusive closure transfers fixed arguments and is freed non-recursively; a shared closure drops one reference and retains each fixed heap argument. Exact twice-application coverage fixes `FIR-BUG-impure-none-shared-closure-capture-transfer`. Pass proof owns the relatedness/preservation adaptations at the focused failures above; W6 owns concrete refinement; W7 waits for that signature/refinement handoff rather than changing compiler work speculatively. |
| `ARGUMENT-ALIAS-MATERIALIZATION` | integration/validation | W7, V8 adapter, W6 refinement | active | `8621f02` | Adds a canonical target-sorted root-to-later-argument alias graph to every corpus descriptor. LCNF allocates each root once and retains one owned reference per aliased argument; malformed, chained, non-heap, schema-mismatched, and datum-mismatched graphs fail closed. The V8 adapter already requires one compiler-manifest heap location with the exact initial reference count. W7 should thread `argumentAliases` through `compileValidationInvocation` and `withValidationInvocation` after its current compiler slice, then admit `effect-record-aliased-byte-array-arguments`; W6 owns any later concrete refinement, not this validation implementation. |

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
