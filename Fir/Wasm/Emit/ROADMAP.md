# FIR-native Wasm generation roadmap

This is the current W7 roadmap. It is intentionally a forward-looking queue,
not a history of every artifact FIR has published. Accepted milestone details
remain in `coordination/BOARD.md`; client-specific contracts remain beside
their integration packages.

## Mission

Compile a real Lean declaration and its exact final-LCNF closure into a
deterministic, self-contained Wasm module with:

- module-owned memory and no host implementation of Lean semantics;
- a reviewed, fail-closed external frontier and zero imports in the complete
  package whenever the resident runtime supports the closure;
- Lean-compatible object layout, boxing, uniqueness, ownership, and floating
  point behavior;
- a small structured boundary rather than JSON or an application rewrite;
- reproducible package metadata, checksums, Node/browser execution, and a
  native oracle; and
- a stable handoff from generation-ready W7 helpers to their independent W6
  refinement proofs.

The source of truth remains final LCNF. FIR should follow upstream Lean
classification and lowering APIs instead of rebuilding an older IR pipeline
or introducing declaration-name shims.

## Current milestone

The feasibility question is closed. FIR now compiles and packages several
substantial, exact-source Lean closures:

| Workload | What it establishes |
|---|---|
| `prettyM` | recursive algebraic data, strings, closures, styling traces, and stack-safe rendering |
| Illuminate selection player | retained input graphs, bit-exact ticks, repeated dispatch, and rewind-safe instance ownership |
| Illuminate HitScene and SpatialHitScene | retained query structures, two implementations of one oracle, and flat repeated-query memory |
| Verso Flat and HTML | real structured render results and authenticated external source closures |
| lean-zip | packed ByteArrays, unique updates, arbitrary Nat/Int work, generic Arrays, deep closure use, and compute-heavy DEFLATE levels 1--10 |

The accepted lean-zip raw package is the new scaling reference: 702 captured
declarations, zero unsupported declarations, a reviewed three-declaration
math frontier before complete linking, zero imports in the complete module,
module-owned memory, exact native output, and all ten compression levels.
This is the point at which W7 moves from runtime closure discovery to generic
compiler quality.

## Ordered queue

### G1. Land consolidated closure allocation

Integrate the ready generic stack on
`wasm/closure-allocation-consolidation` through `052866ca`:

- group `partialApply` allocation helpers by physical capture/result shape;
- pass target identity and arity as data to the shared typed helper;
- keep descriptor layout, source ABI, ownership, and dispatch semantics
  unchanged; and
- materialize this expanding rewrite family at the safe linker boundary.

Recorded lean-zip effect:

- 3,131 semantic partial applications become 569 typed allocator helpers;
- complete functions fall from 5,839 to 3,277;
- resident helpers fall from 5,265 to 2,703;
- resident frontier falls from 3,265,131 to 2,639,643 bytes; and
- complete Wasm falls from 1,753,310 to 1,622,609 bytes, with zero imports.

After integration, regenerate the immutable stored, Level-1, and raw
lean-zip packages on accepted `main`, update exact inventory/size ratchets,
and rerun levels 1--10 through native, independent inflate, Node, and browser
checks. Package identities must be derived only after the compiler slice
lands.

### G2. Separate production and diagnostic adapter costs

Finish the pending Illuminate selection-player request with an actually
timing-free `dispatchTick` and a separate diagnostic `dispatchTickTimed`.
Both operations must invoke the same compiled Lean transition and preserve
the existing persistent checkpoint, poisoning, bit-exact timestamp, and flat
10,000-tick frontier contracts.

Use an interleaved fixed-event benchmark with digest equality, warmups, median,
and p95. This slice is useful beyond Illuminate: production adapters should
not pay for clocks, timing objects, or memory diagnostics unless requested.

### G3. Extract only the proven common package surface

HitScene, the selection player, Verso, and lean-zip now repeat enough package
logic to justify a small shared surface. Extract, in this order:

1. a capability-driven checksum verifier and atomic installer;
2. a declarative package descriptor for immutable publication; and
3. bounded codec hooks plus common production/diagnostic phase names.

This is deliberately not a build framework or coordination service. Extract
only behavior already duplicated by at least two accepted packages. Keep
workload semantics, oracle comparisons, and memory limits in each integration.
Require existing packages to retain their public API and either reproduce
their bytes or explain an intentional metadata-version change.

The optional shared descriptor vocabulary is
`browser-benchmarks/source-package/v1`; it describes provenance, producer,
verifier, operations, ownership, and phase names, not application behavior.

### G4. Continue generic compilation by evidence

For each new real-source closure:

1. capture the exact declaration closure and review unsupported declarations,
   externals, runtime operations, and ABI signatures;
2. add a semantic fixture and bug card before compensating for a discrepancy;
3. implement the smallest generic resident/compiler capability;
4. run the standalone helper in a real Wasm engine;
5. link the real package and freeze its inventory; and
6. publish only after the generic slice is accepted on `main`.

Do not preemptively add `FloatArray`, `DataArray`, DOM, callback, or other
families. Add them when a real closure reaches them. Continue using the
accepted Array/ByteArray/String ownership matrix as the container baseline.

## Parked optimization research

### Static simple-ground images

The backend mechanism is checkpointed on
`wasm/simple-ground-image-experiment` at `23589d5a`. The focused zero-import
fixture proves active-data placement, W6-layout serialization, allocator-floor
coordination, lazy publication, and flat rewind.

When resumed, discard the prototype's local syntactic classifier. Consume
Lean's upstream final-LCNF `SimpleGroundExpr` / `getSimpleGroundExpr`
classification and implement only the FIR-specific W6 serializer and
relocations. Resume when profiling again identifies cold construction of
eligible ground graphs as a leading cost; do not opt a production package in
before that gate.

### Linker and build-time optimization

The accepted linear capture/lowering improvements remain the baseline. The
closure-consolidation candidate records approximately 28.9 s capture, 34.2 s
lowering, and 30.3 s linking for lean-zip raw. Profile before changing the
linker. In particular, add variable-length batched rewrite plans only if the
materialized expanding-family boundary becomes a demonstrated leading cost.

## Canonical example policy

Keep the catalog thin:

- resident micro-artifacts test one generic helper or invariant;
- `prettyM` is the compact structured-runtime regression;
- Illuminate selection is the retained live-adapter regression;
- HitScene/SpatialHitScene are retained-query and cross-implementation
  regressions;
- Verso Flat/HTML are structured renderer regressions; and
- lean-zip is the scale, packed-data, uniqueness, and compute regression.

Older package versions and provisional probes are historical evidence, not
active roadmap entries. Do not add a permanent example unless it covers a
materially new compiler/runtime shape.

## Gate for every generation slice

A W7 handoff reports exact source and FIR identities, captured declarations,
reviewed externals and resident helpers, imports/exports, Wasm sizes and
digests, ownership policy, and all package paths. It passes:

- Lean Beam during Lean iteration and the focused final dependency cone;
- `git diff --check` and `make check`;
- `make talos-check` after Talos setup;
- `bash integration/talos/artifact/check.sh` for W7 artifact changes;
- deterministic repeat generation;
- native/Wasm semantic equality and application-specific differential tests;
- Node and browser smoke for published Web packages; and
- clean branch/worktree handoff through `coordination/lanes/wasm-gen.md`.

Generation readiness does not claim the W6 refinement theorem. New or changed
helper signatures are handed to W6 explicitly and remain separate until proof
acceptance.

## Non-goals

- Reviving Lean IR as the source pipeline.
- Reimplementing application algorithms in FIR or JavaScript.
- Undocumented host runtime fallbacks in a complete package.
- Freezing a broad application ABI before repeated consumers require it.
- Building a package framework, daemon, or coordination system around a
  hypothetical future need.
- Mixing static-ground research into unrelated correctness or publication
  slices.
