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

The accepted lean-zip raw package established the scaling reference. After the
accepted compiler-unit cache-isolation repair, its reviewed closure contains
662 captured declarations, 534 retained source functions, and 2,598 resident
helpers, with zero unsupported declarations, a reviewed three-declaration math
frontier before complete linking, zero imports in the complete module,
module-owned memory, exact native output, and all ten compression levels. The
package contract pins ordered-inventory hashes as well as counts and byte
lengths. This is the point at which W7 moves from runtime closure discovery to
generic compiler quality.

## Ordered queue

### G1. Consolidated closure allocation (accepted)

The generic stack was accepted on `main` at `85481c67` with functional head
`10dca27f`:

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

### G1a. Align resident Array hot calls with Lean's trusted runtime path (accepted)

The trusted-call split was accepted on `main` at `7e5f31f3` with functional
head `da721bc3`.

Lean's native Array primitives trust the typed runtime representation. Its
dynamically checked APIs retain index handling, while proof-indexed APIs trust
their erased bounds proofs and proceed directly to access or copy-on-write
mutation. FIR's first
resident Array implementation instead combined an O(index) address walk with a
complete raw-header validator on every operation. Commit `1d79658d` was FIR's
first O(1) address implementation; there was no earlier retained fast O(1)
version. The later ownership repair `6592e2cb` expanded the common validator to
cover live/persistent flags, reference counts, reserved lanes, and capacity,
but did not introduce the validator itself.

The accepted first slice kept checked standalone/public helper bodies for
raw-memory diagnostics. Closed typed applications consumed the resident Array
invariant and omitted the common validator prefix, but deliberately retained
the existing bounds branches pending the upstream audit. Reference counting,
uniqueness, copy-on-write, allocation, and recursive release remained
unchanged. The slice was validated with a
malformed-boundary trap, exact symbolic suffix guards, the real lean-zip
native/inflate matrix, and order-balanced scaling evidence rather than a single
absolute-time threshold. W6 separately audits that its accepted Array
refinement supplies the trusted representation premise.

The first order-balanced lean-zip measurements show the intended modest
effect rather than a new algorithmic speedup. Four-KiB inputs were neutral;
for deterministic random inputs the paired median raw-entry reduction was
5.47 ms at 64 KiB (210.33 to 206.06 ms, about 2.6%) and 15.39 ms at 256 KiB
(825.62 to 812.06 ms, about 1.9%), with all eight AB/BA pairs improving at
both sizes. Output hashes and post-rewind frontiers were identical. The
resident frontier shrank from 2,639,643 to 2,637,367 bytes, while the complete
linked module grew from 1,622,609 to 1,628,872 bytes; therefore this slice is
not a binary-size win and should not be described as closing lean-zip's larger
native-performance gap.

### G1b. Consume proof-indexed Array bounds like upstream Lean

The version-pinned upstream rule is local and explicit. Representation trust
and index policy are separate dimensions:

- foreign/public helper calls validate transferred Array and index values;
- dynamically checked Lean APIs preserve their exact bounds and panic/default
  behavior; and
- `getInternal`, `uget`, `set`, `uset`, and `swap` consume their erased proofs,
  directly unbox or narrow the index, and do not branch on bounds.

The trusted implementation must preserve owned versus borrowed reads,
uniqueness, copy-on-write, child retention/release, allocation, and capacity
behavior exactly. Generated-shape guards reject proof-index decoder calls and
the former bounds sequences in trusted bodies. A closed trusted resident module
must validate and encode with zero imports, while the checked standalone module
continues trapping malformed foreign inputs. Real-source differential and
lean-zip package checks provide execution evidence; W6 separately discharges
the representation, canonical immediate-Nat, and erased-bounds premises.

The first same-main lean-zip probe held final-LCNF capture and all linker
inventories constant at 662 declarations, 128 reviewed externals, 534 retained
source functions, 2,598 resident helpers, 3,132 complete functions, and zero
runtime operations. Five native/Wasm cases at all ten compression levels,
zero-import linking, cache/checkpoint ownership, output hashes, and flat
frontiers passed. The frontier Wasm decreased by 201 bytes (1,570,838 to
1,570,637); the externally linked complete file changed from 899,613 to
902,411 bytes, so this is not presently a complete-binary size win.
Order-balanced random-input execution was noisy and inconclusive: four paired
64-KiB medians had a median delta of about -8.94 ms, while four 256-KiB pairs
had a median delta of about +32.98 ms. Treat the upstream-faithful instruction
shape as the result; do not claim a workload speedup from these samples.

### G1c. Fast-path canonical immediate natural addition

Lean's tagged immediate `Nat` representation makes the common two-immediate
case locally decidable without scanning arbitrary-precision magnitudes. The
accepted generation candidate checks both physical tags at the start of
`Nat.add`, decodes their 31-bit payloads, supplies zero high limbs to the
existing natural-sum constructor, and returns through the same object retyping
path. Mixed and heap-backed operands retain the previous validation,
multi-limb, allocation, and ownership implementation byte-for-byte. This is a
generic representation path, not a lean-zip specialization or a relaxation of
the public malformed-input boundary.

Focused Wasm cases cover sums below, at, and above the immediate boundary, two
maximal immediates, mixed immediate/heap operands, and two heap operands. The
complete lean-zip matrix preserves exact native/Wasm bytes, zero imports, and
flat scratch reclamation. Two checked 256-KiB seeded-random profiles improve
from 1799.46 to 516.80 ms/call and from 1709.47 to 504.61 ms/call (3.48x and
3.39x); the structured control improves from 173.64 to 96.84 ms/call (1.79x).
`fir_big_ext_Nat_add` self time improves about 6.5x in both random runs, while
the magnitude and validation helpers also fall substantially. The work is
removed rather than shifted.

The source and pre-optimization linker inventories remain unchanged. The raw
release grows by 51 bytes and retains one additional resident helper because
`fir_numeric_natural_sum`, formerly inlined from its sole surviving use, now
has two. W6 separately adapts the existing arbitrary-precision addition proof
to the immediate branch; the signature and concrete runtime contract are
unchanged.

### G2. Separate production and diagnostic adapter costs

Finish the pending Illuminate selection-player request with an actually
timing-free `dispatchTick` and a separate diagnostic `dispatchTickTimed`.
Both operations must invoke the same compiled Lean transition and preserve
the existing persistent checkpoint, poisoning, bit-exact timestamp, and flat
10,000-tick frontier contracts.

Use an interleaved fixed-event benchmark with digest equality, warmups, median,
and p95. This slice is useful beyond Illuminate: production adapters should
not pay for clocks, timing objects, or memory diagnostics unless requested.

The generation-ready implementation exposes clock-free `dispatchTick` at
adapter API v5 / hot-event capability v2 and retains `dispatchTickTimed` as the
explicit diagnostic path. Package and source smokes prove that production
ticks perform no clock reads, return no timing or memory object, use the same
bit-exact scalar Wasm entry, and leave the checkpoint flat across 10,000 calls.
All 107 legacy/v3/selection generic/scalar-tick traces agree.

Eight AB/BA rounds with 240 measured events per mode and workload recorded
identical action digests. Median whole-callback time changed from 0.00463 to
0.00373 ms for “Pause-driven slide show” (MAD 0.00018 to 0.00014 ms) and from
0.00430 to 0.00359 ms for “Morphing arrows and final loop” (MAD 0.00015 to
0.00017 ms). The first p95 improved from 0.00597 to 0.00448 ms; the second was
noisy and changed from 0.00547 to 0.00582 ms. These are adapter-overhead
measurements, not a claim that the compiled Lean transition became faster.

Regeneration also exposed and fixed a generic compiler-unit isolation bug:
final-LCNF capture reused an imported `Option Nat` specialization owned by
Lean's delaborator. Synthetic FIR units now clear imported specialization and
closed-term caches while retaining direct imported declaration mappings, so
Lean generates helpers in the selected source unit. The selection artifact is
35,240 bytes with 111 captured declarations, 209 resident helpers, zero
imports, and seven function exports.

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
