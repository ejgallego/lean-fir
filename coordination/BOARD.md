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
| Integration | integration owner | `main` | active | Main contains structured symbolic Wasm loops, Talos lowering, stack-safe resident String walkers, and ledger-aware matching through concrete-token existing-address reuse at `fd18613b`. Validation head `6818e6dd` is based on the earlier `aae41229` boundary and adds true Lean `IO` return/error comparison without requesting compiler work | Six isolated shared-contract domains remain queued: float representation, closure ownership, argument aliases, process termination, effectful native-oracle actions, and source-entry result boundaries. The last two are validation infrastructure; W7/V8 consumes them only when compiler-generated IO cases are ready. The umbrella check remains gated by the queued `takeClosureApplication` proof consumers; the retained V8 rebuild is independently gated by W7's exhaustive float manifest cases |
| Lean pass proof | pass-proof owner | `proof/simpcase` | active | Clean head `fd18613b` is integrated on `main`. Ledger-aware exact matching now covers literals, constructors, partial applications, boxes, failed-token reuse, and both retained and deleted concrete-token reuse; successful in-place reuse preserves the target frontier and transports its owner ledger across the hidden renaming extension | Continue with the remaining no-allocation and external-response ledger branches, then assemble the unified ledger-aware dispatcher and entry-indexed ownership invariant. Also adapt `box` proofs to `boxUsesTaggedRepresentation` in `ElimDeadRuntimeRel.lean:8863-9172` and prove the queued `takeClosureApplication` consumers before the validation stack lands |
| W6 runtime proof | W6 owner | `wasm/talos-runtime` | active | Clean head `dfb239ff`, based on semantic boundary `aae41229` and one coordination-only main commit behind, composes scalar field mutation correctness after constructor-tag, object-field, erased-field, usize-field, and structural ownership checkpoints | Continue the concrete refinement and closure-application audit in W6-owned files. W6 owns implementation-to-concrete-host theorems, not the validation adapters or the W7 compiler |
| W7 generation | generation owner | `wasm/generation` | active | The stack-safe resident `prettyM` String walker and stress fixture are integrated on `main` at `7d9c1ad9` and `0e1a564a`; the clean generation branch is five main commits behind, including the newest coordination checkpoint | Rebase before the next handoff, then add the exhaustive `float32Bits`/`float64Bits` manifest consumers at `Manifest.lean:149,255,280`. Consume `processTermination` and `entryKind` only when admitting corresponding compiler-generated real-engine cases; do not implement lane-4 source projection in W7 |
| Validation | validation owner | `validation/float-corpus` | ready | Clean head `6818e6dd`, based on semantic boundary `aae41229` and one coordination-only main commit behind by design, compares genuine Lean IO returns and `IO.userError` exceptions. Run `bd194eea9016865c0625f4dfab12ed3647542cd89fd6f76da8457f3c40211361` passes 675/675 native/LCNF cases; evidence `b6ec3416e6f7d3a9875fde2f5c36063bfefe6ba74f0ee5bf4c7a8336c5c0c13f` verifies offline. The direct tier passes 9/9 at run `79072ab9537b31cc3cb09bc253881736883275c960ff379d883e4859c8fc3b54`, evidence `18c273de9ad3d86bb6a1fd198aee40ec626333c02027ec255ca75204517aea98` | Shared contracts are isolated at `65208ef4`/`9862bbc9`, `37a873b7`, `0572b151`, `698ce417`/`e1805acc`, `910416a9`, and `bbb7fcb8`. Harness tests are 127/127. `FIR-BUG-validation-none-io-entry-world-result` is fixed by typed `entryKind` projection and dependent fixtures at `6818e6dd`. `make check` still stops only at the queued proof-owned `takeClosureApplication` consumers in `AlphaEqvCode.lean:2209,2358-2360` |

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
| `FLOAT-SCALAR-RUNTIME` | integration/validation | pass proof, W6, W7, validation | active | `65208ef4`; source-accurate extension `9862bbc9` | Adds bit-exact `float32Bits`/`float64Bits`, typed schemas, and LCNF codecs. Compiler-generated `dec[ref]` proves that `Float32` and `Float` boxes are always heap objects, so `9862bbc9` replaces payload-only boxing with `boxUsesTaggedRepresentation` and restores rejection of tagged floating boxes. `FIR-BUG-impure-none-float-box-tagging` is fixed; the earlier tagged-decoder diagnosis is closed-not-a-bug. Validation head `6818e6dd` passes 675/675. Pass proof must branch on the new predicate at `ElimDeadRuntimeRel.lean:8863-9172`; W7 must extend `Manifest.lean:149,255,280`; W6 owns the corresponding concrete refinement. |
| `CLOSURE-APPLICATION-OWNERSHIP` | integration/validation | pass proof, W6, W7, validation | active | `37a873b7` | Matches Lean's `lean_apply_*` boundary: an exclusive closure transfers fixed arguments and is freed non-recursively; a shared closure drops one reference and retains each fixed heap argument. Exact twice-application coverage fixes `FIR-BUG-impure-none-shared-closure-capture-transfer`. Pass proof owns the relatedness/preservation adaptations at the focused failures above; W6 owns concrete refinement; W7 waits for that signature/refinement handoff rather than changing compiler work speculatively. |
| `ARGUMENT-ALIAS-MATERIALIZATION` | integration/validation | W7, V8 adapter, W6 refinement | active | `0572b151` | Adds a canonical target-sorted root-to-later-argument alias graph to every corpus descriptor. LCNF allocates each root once and retains one owned reference per aliased argument; malformed, chained, non-heap, schema-mismatched, and datum-mismatched graphs fail closed. The V8 adapter requires one compiler-manifest heap location per root with exact initial multiplicity and now tests reference counts two and three plus two independent roots. W7 should thread `argumentAliases` through `compileValidationInvocation` and `withValidationInvocation` after its current compiler slice, then admit `effect-record-aliased-byte-array-arguments`, `effect-record-triply-aliased-byte-array-arguments`, and `effect-record-two-aliased-byte-array-groups`; W6 owns any later concrete refinement, not this validation implementation. |
| `NATIVE-TERMINATION-SUPERVISION` | integration/validation | native adapter, LCNF adapter, W7/V8, Talos runners | active | `698ce417`; typed policy `e1805acc` | Adds `timeoutMs` plus the backend-neutral `processTermination` enum: `protocol`, `timeoutDivergence`, or `sourceExit`. Native timeout is a typed backend timeout unless opted into divergence; ordinary nonzero status and signals remain crashes unless an exact source-exit fixture opts in, and signals always remain crashes. LCNF promotes only same-step, well-typed `Source.exitNat` terminal evidence under `sourceExit`, without changing the canonical interpreter result theorem. The divergence fixture at `c1f779d8` pins 256 steps; source-exit fixture `39438394` pins statuses zero/seven and one exact external step. Retained V8 evidence excludes both. W7 or Talos should consume this policy only when admitting corresponding real-engine cases; no compiler-side work is requested now. |
| `EFFECTFUL-NATIVE-ORACLE` | integration/validation | native and direct-native adapters; future V8/Talos adapter authors | active | `910416a9` | Replaces `Case.native : Unit → ValidationDatum` with a delayed `Unit → IO ValidationDatum` action and makes semantic effect/stderr drains independent of a successful return value. Existing pure fixtures lift explicitly and all 675 source plus 9 direct observations pass. This is the foundation for comparing true Lean `IO.Error` exceptions and source output; it changes no descriptor, compiler ABI, canonical interpreter theorem, or W6/W7 implementation surface. |
| `SOURCE-ENTRY-RESULT` | integration/validation | LCNF adapter, W7/V8 adapter, Talos runners | active | `bbb7fcb8` | Adds portable `entryKind = value | io` to corpus requests and descriptors. For `io`, the LCNF adapter appends exactly one erased `RealWorld` argument and decodes `EStateM.Result IO.Error α`; the native oracle runs the actual source action. Dependent fixtures at `6818e6dd` compare a returned `IO Nat` and an exact `IO.userError`, fixing `FIR-BUG-validation-none-io-entry-world-result`. W7 and Talos should consume the field only when admitting compiler-generated IO cases; no compiler work is requested before that boundary. |

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
