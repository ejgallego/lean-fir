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
| Integration | integration owner | `main` | active | Main is green through the elimDead static-to-dynamic ownership checkpoint `294d8b9`. Validation head `7c8c4b8` remains based on the earlier ownership checkpoint and advances the ready stack to 664 native/LCNF cases with evidence-derived semantic coverage floors | Two isolated shared contracts are ready but not yet eligible for `main`: the pass-proof, W6, and W7 consumers below must adapt first. The later validation-only coverage/effect/mutation commits do not add consumer work and may ride the same green integration stack |
| Lean pass proof | pass-proof owner | `proof/simpcase` | active | Integrated head `294d8b9` separates root-independent local certificates from dynamic ownership for deleted object/usize/scalar writes, concrete reuse, and reset; unmapped and empty-target bridges now discharge the one-cell and owned-child fixtures | Package these laws into reusable exact-ownership-contract combinators and derive unmapped/source-only locations from compiler ownership invariants. Then adapt `box` proofs to `boxUsesTaggedRepresentation` in `ElimDeadRuntimeRel.lean:8863-9172` without adding floating cases to `scalarFromType`; separately prove `takeClosureApplication` preservation/relatedness for `SimpCaseRelation.lean:427` and `AlphaEqvCode.lean:2209,2358-2360` |
| W6 runtime proof | W6 owner | `wasm/talos-runtime` | active | Ordered constructor case dispatch is landed at `911f358`; `ConcreteCompilerCorrectness.lean` contains the current follow-on work | Extend the already-float-aware concrete relation with the missing exhaustive `HeapRefinement.lean` cases at 35, 116, and 136. Audit closure application against `takeClosureApplication` after the current checkpoint; W6 owns the concrete refinement, not the validation implementation |
| W7 generation | generation owner | `wasm/generation` | active | Arbitrary numeric styling coverage is clean at `0f2e412`, including the production browser adapter and numeric `prettyM` work | Add the exhaustive `float32Bits`/`float64Bits` manifest consumers at `Manifest.lean:149,255,280` when rebasing the next generation slice. For closure application, consume the stable signature only after W6 states the refinement boundary; do not overlap compiler work already in flight |
| Validation | validation owner | `validation/float-corpus` | ready | Clean head `7c8c4b8` retains the float/closure/mixed-layout stack and adds a four-case taken/skipped × unique/shared ByteArray mutation matrix at `66cb800`, with exact form traces, zero/one external dispatch, alias preservation, and 30 additional interpreter steps. Run `3e0c1035cd4507fa3c753e08d5c4221ae7412c05a90641e6c0ad0e9acae81391` compares 664/664 native and LCNF observations equal; evidence `95bc3203a598cca4862f34086024996a5e8e969cef89f2c77b7621d83244255b` verifies offline | Shared contracts remain isolated at `d8bbf82` and `009d2bb`; codec `17197d8`, fixtures `ab88bc6`, semantic coverage `a0e9c5f`, conditional effects `1d37068`, and conditional mutation `66cb800` are dependent validation slices. Harness tests are 118/118; index `d31e0f5` composes 673 unique cases and 1835/1835 equal comparisons while satisfying 33/33 semantic floors. The retained 581-case V8 matrix verifies offline and excludes the new cases; a fresh provider rebuild stops at the queued W7 float-manifest consumer. `make check` still stops at the queued closure proof consumer |

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
| `FLOAT-SCALAR-RUNTIME` | integration/validation | pass proof, W6, W7, validation | active | `0f04761`; source-accurate extension `d8bbf82` | Adds bit-exact `float32Bits`/`float64Bits`, typed schemas, and LCNF codecs. Compiler-generated `dec[ref]` proves that `Float32` and `Float` boxes are always heap objects, so `d8bbf82` replaces payload-only boxing with `boxUsesTaggedRepresentation` and restores rejection of tagged floating boxes. `FIR-BUG-impure-none-float-box-tagging` is fixed; the earlier tagged-decoder diagnosis is closed-not-a-bug. Validation head `7c8c4b8` passes 664/664. Pass proof must branch on the new predicate at `ElimDeadRuntimeRel.lean:8863-9172`; W7 must extend `Manifest.lean:149,255,280`; W6 must extend `HeapRefinement.lean:35,116,136`. |
| `CLOSURE-APPLICATION-OWNERSHIP` | integration/validation | pass proof, W6, W7, validation | active | `009d2bb` | Matches Lean's `lean_apply_*` boundary: an exclusive closure transfers fixed arguments and is freed non-recursively; a shared closure drops one reference and retains each fixed heap argument. Exact twice-application coverage fixes `FIR-BUG-impure-none-shared-closure-capture-transfer`. Pass proof owns the relatedness/preservation adaptations at the focused failures above; W6 owns concrete refinement; W7 waits for that signature/refinement handoff rather than changing compiler work speculatively. |

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
