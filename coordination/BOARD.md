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
| Integration | integration owner | `integration/wasm-lanes` | active | Integrated W7's closed resident `prettyM` runtime through `071fcbc`, exact-provenance pass proofs through `a29d480`, and the complete exact signed validation family as `5305358`; the `FLOAT-SCALAR-RUNTIME` shared-contract audit is active | Float scalar values will extend the shared runtime and observation domain; proof, W6, W7, and validation consumers must rebase and discharge their recorded impacts after the isolated contract lands |
| Lean pass proof | pass-proof owner | `proof/simpcase` | active | Hereditary control-flow readiness through named invocation and yielded steps is landed through `0e0cf0b`; worktree is clean | Independent of W7 generation; branch only needs the latest W7 landing before its next handoff |
| W6 runtime proof | W6 owner | `wasm/talos-runtime` | active | Partial-closure capacity is proved at clean head `5095ac3`; the branch contains the stable closure-descriptor contract | W7 may consume the released descriptor table now; W6 remains the proof owner and rebases on current `main` before its next handoff |
| W7 generation | generation owner | `wasm/generation` | active | Resident cache publication, numeric operations, String operations, and fallbacks are landed through the zero-import `prettyM` checkpoint `071fcbc` | Uses released W6/W7 contracts; the owner must report the next generation helper and any new contract impact before handoff |
| Validation | validation owner | `validation/interpreter-corpus` | active | The complete exact signed Int8/Int16/Int32/Int64/ISize family and all 20 directed conversions are landed through `5305358`: 581 source cases, 590 unique cases, 1,752 comparisons, and zero native/LCNF/V8 findings; the float scalar runtime gap is the next native-oracle slice | Produces `FLOAT-SCALAR-RUNTIME` with integration: bit-exact `Float32`/`Float` values become shared observations, then validation adds source-compiled native/LCNF/V8 fixtures without changing W6/W7-owned implementations |

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
| `FLOAT-SCALAR-RUNTIME` | integration/validation | pass proof, W6, W7, validation | active | pending | Extend the integration-owned `ScalarValue` and observation/runtime codecs with bit-exact `Float32` and `Float` lanes. Pass proofs must cover the new relation cases; W6 must relate them to existing `float32Bits`/`float64Bits` concrete values and audit scalar layout/boxing; W7 must audit typed float locals, calls, stores, and emitted manifests; validation will add native-oracle identity, conversion, arithmetic, comparison, exceptional-bit-pattern, boxing, and field-mutation cases, with V8 consuming raw bits rather than JSON numbers. No W6/W7-owned implementation changes are part of the producer commit. |

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
