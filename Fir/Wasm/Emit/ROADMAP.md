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
accepted compiler-unit cache isolation, source-Float compilation, direct scalar
helpers, and standard-libm v2 migration, its reviewed closure contains 769
captured declarations, 630 retained source functions, and 2,782 resident
helpers, with zero unsupported declarations. `Float.ofNat` and
`Float.ofScientific` compile from final LCNF; exactly `Float.log2` remains at
the symbolic frontier and is internalized by the standard libm provider. The
936,001-byte complete module has 2,305 final functions, zero imports,
module-owned memory, exact native output, and all ten compression levels. The
package contract pins ordered-inventory hashes as well as counts and byte
lengths. This is the point at which W7 moves from runtime closure discovery to
generic compiler quality.

## Ordered queue

### Compiler organization refresh (2026-09-09)

Keep final impure LCNF, symbolic Wasm, resident helpers, and Binaryen. The
reviewed CG sequence is: production/validation dependency extraction (CG-01),
canonical driver preserving source-unit providers (CG-02), indexed existing
analyses (CG-03), then incremental explicit resident contributions (CG-04).
The first generated-code experiment is separately scoped CG-05: apply the
constructor allocator's established scratch-free return, then selective
initialization, to closures. Poisoned recycled-memory tests and W6 review
precede acceptance; no performance gain is assumed from source shape alone.

CG-01 begins from accepted main `d5e0b5ca`. See `Fir/Compiler/README.md` for
the production/validation boundary and compatibility policy. Capture algorithms,
source-unit identities, eager diagnostic formatting, helper bodies, and all
semantic contracts remain unchanged. The source import graph drops from 21
FIR modules to 16 (including the source module); this is dependency evidence,
not a measured build-time or runtime improvement. Byte-identical emission and
the complete existing W7 gates are the acceptance boundary for the extraction.

CG-05A (2026-09-09) removes only closure allocator scratch result transport,
reusing the constructor helper's typed unsigned extend/wrap bridge. Capture
stores, full-allocation zeroing, headers, descriptors, signatures and ownership
remain unchanged. A generated-body guard freezes that prefix and the one-local
memory-free result suffix. The external-engine fixture now includes bit-exact
mixed captures and poisoned checkpoint reallocation with full extent, reserved
memory, retained-prefix and suffix-canary checks.

On the existing standalone helper shapes, raw bodies shrink by 46 bytes each;
the pinned closed-module Binaryen profile removes the bridge and the optimized
bodies shrink by 24 bytes each. The old optimized bodies still contained two
scratch loads and two scratch stores. The enlarged test module is not a fair
whole-module size comparison because it adds a mixed-capture facade/helper.
These are code-shape measurements, not workload timing results. CG-05B selective
initialization stays separate, as does W6's implementation refinement review.

The complete artifact gate on functional `87d766a1` regenerates prettyM at
86,690 bytes (previously 87,840): exactly 25 closure bodies lose 46 bytes each.
The captured LCNF, 322-function inventory, 269 function export names/indices,
zero imports and memory/ownership contract are unchanged. No workload timing
or fresh browser campaign is claimed. The immutable local package is recorded
in the W7 handoff; external client pointers are not moved by this slice.

CG-05B (2026-09-09) removes only closure zero stores overwritten by the
unchanged header/capture stages. The 32-byte header is completely written;
physical i64/f64 captures fill their eight-byte slots. Only physical i32/f32
slot high words need explicit zeroing. Helper signatures, allocation extent,
metadata, ownership and the accepted scratch-free suffix are unchanged.
Independent guards enumerate the remaining offsets, including the mixed
capture's eight high words. This is separate from W6's CG-05A suffix decision.

The expanded standalone fixture compares 81 full allocation snapshots against
the accepted full-zero path, including real last-reference release into a
two-block reuse chain. Header-only exclusion, canonical dead headers, private
nonempty links, flat recycled frontier, retained inputs, canaries, all result
lanes and bit-exact float patterns are checked. Raw and pinned-optimized
variants pass; removing one required high-word store in an ignored negative
control makes the poison check fail. Existing release helpers are linked only
in the artifact fixture, not imported by the production allocation emitter.

With identical fixture/export inventory, raw Wasm shrinks 6,286 -> 5,128 bytes
and optimized Wasm 3,353 -> 2,980. Distinct optimized helper shapes are:

| Capture shape | Body bytes before -> after | Store instructions before -> after |
| --- | --- | --- |
| empty | 122 -> 66 | 16 -> 8 |
| tobject/UInt8/USize | 185 -> 101 | 25 -> 13 |
| Float32/Float | 164 -> 87 | 22 -> 11 |
| mixed eleven captures | 355 -> 201 | 49 -> 27 |

Binaryen already merges physically identical result-lane helpers in both
versions; do not sum alias rows as distinct optimized bodies. These are
instruction/size measurements, not runtime speed claims. Exact standalone
baseline/candidate binaries and toolkit-derived shape inventories are retained
under `.deps/cg05b/`; the standard full gates and narrow W6 initialization
review remain the acceptance boundary. No shared layout or W6 file changes.

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

### G1b. Consume proof-indexed Array bounds like upstream Lean (accepted)

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

### G1c. Fast-path canonical immediate natural addition (accepted)

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

### G1d. Reusable canonical immediate-Nat dispatch (accepted)

The representation check and payload decode are now a small shared code-
generation surface rather than a `Nat.add`-local instruction sequence. Binary
Nat operations can select two canonical tagged immediates, run a typed local
kernel, and retain their existing checked arbitrary-precision implementation
unchanged for every mixed or heap-backed pair.

`Nat.mod` is the first additional consumer. Its immediate branch preserves Lean's
`n % 0 = n`; for a nonzero immediate divisor, unsigned machine remainder is
strictly below the 31-bit divisor and is therefore returned canonically without
allocation. Focused external-engine checks cover zero, boundary payloads,
result representation, no frontier growth, and the existing arbitrary-
precision matrix. This changes neither the public signature nor the malformed-
heap fallback boundary; W6 owns the corresponding branch refinement.

### G1e. Direct core-Wasm fixed-width helpers (accepted)

The released complete scalar instruction surface removes the historical need
to synthesize fixed-width operations from split 32-bit halves and structured
loops. The resident `UInt8`, `UInt16`, `UInt32`, `UInt64`, and `USize` helpers
now use direct core Wasm comparison, bitwise, shift, count, multiplication, and
remainder instructions. `UInt64.mod` and `USize.mod` retain an explicit zero-
divisor branch because Lean specifies `n % 0 = n`, while `i64.rem_u` traps.

Symbolic guards require the helper family to contain no structured scalar
loops and pin the native CLZ, CTZ, multiplication, and remainder operations.
The zero-import fixed-width artifact decreases from 13,433 to 11,608 bytes.
Seven order-balanced V8 rounds give median speedups of 2.82x for `UInt64.mod`
and 2.71x for `UInt64.mul`; `UInt64.ctzFast` improves 1.10x because the common
call and ABI-retagging cost dominates that small operation. All focused,
native/LCNF/V8, Talos, and deterministic package checks preserve exact results.

### G1f. Direct core-Wasm Float and conversion helpers (accepted)

The same scalar surface now closes the standard externals that have exact core
Wasm meanings: `UInt64.toFloat`, Float add/subtract/multiply/divide, negate,
equality and ordering, absolute value, square root, and floor. Existing
`Float.toUInt64` remains the saturating unsigned conversion, and the available
linker emits only helpers actually referenced by the source closure.

`Float.round` deliberately remains a floor/ceiling synthesis. Lean rounds
halves away from zero and preserves signed zero, whereas Wasm `nearest` uses
ties-to-even. The six transcendental operations remain in the checked standard
math runtime; they are not approximated with scalar instructions. A zero-import
fixture covers all resident scalar helpers, exact NaN sign/payload behavior for
negate/absolute value, signed zero, saturation, infinities, half boundaries,
scratch restoration, and immediate/heap `UInt64.toNat` results.

`Float.ofNat` and `Float.ofScientific` now follow a separate, faithful source
path. FIR compiles Lean's exposed definitions as ordinary LCNF source units,
regenerating caller-owned specializations with their generic companions, then
closes the resulting arbitrary-precision Nat/Int/BitVec model with resident
helpers. The deterministic 71,419-byte acceptance artifact has module-owned
memory, zero imports, bit-exact integer-lane facades, and native-oracle cases
covering the fast boundary, slow model path, subnormals, overflow, and Naturals
beyond 64 bits. This work also removed the one-limb restrictions from
`Nat.shiftRight` and fixed-width `ofNat` conversions; the C conversion exports
remain only as a version-1 compatibility surface for packages not yet rebuilt.

### G1g. Typed checked natural-addition results (generation-ready)

Every `Nat.add` exit now crosses the symbolic `.uint32`/`.tobject` distinction
with the typed unsigned-word round trip. The immediate exit is valid by the
canonical tagged-pair dispatch. The checked one-limb exit validates both
operands and returns the canonical result of `naturalSum`; the multi-limb exit
returns the live Natural allocated and populated by the checked limb writer.
No exit needs linear-memory address zero as a type-changing scratch slot.

A source-shape guard rejects any future typed-object scratch load in
`natAddFunction`. The standalone real-Wasm matrix covers tagged, promoted,
mixed, arbitrary-limb, carry-growth, malformed-input, and 8,192-limb cases.
The exact lean-zip release removes 19 instructions, three memory loads, and
three scratch-only stores from `fir_big_ext_Nat_add`, shrinking that body by 40
bytes while preserving every call edge, import, output hash, and arena
frontier. Representative timing and sampled attribution overlap, so this slice
makes no workload speed claim. W6 proof adaptation remains the acceptance
boundary.

### G1h. Decrement shared references before cold metadata decoding (generation-ready)

Lean's common release path needs only the live/persistent flags and reference
count before it can decrement a shared object and return. FIR previously
decoded object kind and all four auxiliary header words before making that
decision. The generation-ready implementation now reads the flags once,
probes the terminal header word to preserve the complete-header memory-boundary
trap, and loads the reference count. Kind and auxiliary metadata move to the
persistent or last-reference branches that interpret them. The helper
signature, 32-byte header contract, closure descriptors, recursive release,
and ownership behavior are unchanged.

Generated-shape guards pin the terminal-word probe at the start of the live
path and the reference-count load at the start of the ordinary path. The
external-engine release matrix additionally checks that a live shared object
with only the first 16 header bytes present still traps; persistent objects
retain their count, and last-reference constructor, closure, Array, String,
and Natural cases retain their recursive-release behavior.

The deterministic result is five fewer header reads on the common live,
nonpersistent, shared-reference path. `fir_dec_once` grows by 17 bytes in
prettyM and 10 bytes in lean-zip because the cold-path control is split rather
than duplicated. Its median normalized V8 self share changes from 9.55% to
8.12% in prettyM and from 14.24% to 13.59% in lean-zip. Two independent sets
of eight alternating AB/BA rounds preserve exact output digests and frontiers.
The combined paired median changes are -14.41 ms for prettyM, with 12/16 pairs
improving, and -31.90 ms for lean-zip, with 9/16 improving. Dispersion is high,
especially for lean-zip, so these are directional workload results rather than
a precise end-to-end speedup claim. W6 proof adaptation remains the acceptance
boundary.

### G1i. Prune closed closure dispatch to source `pap` targets (generation-ready)

Generic FIR modules must be prepared to apply a closure supplied through an
opaque host boundary, so their generated dispatch retains every declaration in
the captured closure table. Data-only Web packages have a stronger boundary:
JavaScript transfers fresh Arrays, Strings, structures, and scalars, but never
a pre-existing Lean closure. For that boundary, every dynamically applied
target is allocated by a final-LCNF `pap` node in the captured program.

The new opt-in source API records that boundary explicitly. After ordinary
lowering it collects the exact `pap` target set, structurally removes other
compiler-generated closure matcher branches, rebuilds the runtime-operation
and import frontier, and validates the result. It fails closed if a residual
closure target is not in the source set. The generic source API remains
unchanged for opaque closure ingress, and the stable W6 `closureDispatch` and
`closureDescriptors` tables remain byte-for-byte unchanged as proof/ABI
metadata.

The prettyM source uses 11 targets instead of the 1,019-candidate all-target
product: 394 matcher branches remain and 625 are removed. Its complete Wasm
falls from 120,756 to 84,161 bytes (30.3%). The lean-zip source uses 23 targets
instead of the 439-declaration dispatch universe: 734 branches remain and
10,888 are removed. Its pre-link runtime operations fall from 9,908 to 954,
the complete module from 936,082 to 393,070 bytes (58.0%), and final functions
from 2,305 to 508 (78.0%). Exact output, zero imports, deterministic generation,
all ten compression levels, lazy-cache publication, and flat scratch rewind
remain unchanged.

This first slice deliberately runs after ordinary all-target lowering. It is a
package-size and load/validation-complexity win, not yet a lowering-time win.
The next shared W6/W7 step may thread the same finite target set into closure
lowering so the compiler never constructs the removed candidates; that move
must preserve the generic opaque-boundary path and receive the corresponding
proof adaptation.

### G1j. Keep checked decrement scalar gates in compiled callers (generation-ready)

Upstream Lean's `lean_dec` performs the scalar/tag test inline and enters the
cold recursive release routine only for a heap reference. FIR previously sent
every checked decrement through `fir_dec_once`, including tagged Nat values
and the checked erased-zero sentinel. Resident container helpers still need
the complete public helper, but compiler-generated release wrappers can follow
the upstream split without changing their signature or heap behavior.

Checked wrappers now classify tagged immediates and zero once before the
possibly repeated decrement sequence. Those values return without calling the
recursive helper. Ordinary, shared, persistent, promoted-Nat, malformed, and
last-reference values retain the existing `fir_dec_once` path; unchecked
wrappers are byte-for-byte direct calls, and a zero-amount decrement remains a
no-op without inspecting its argument. Generated-shape guards pin all three
cases.

On the exact 256-KiB seeded-random level-6 lean-zip workload, two
artifact-bound profiles reduce median `fir_dec_once` Wasm-self share from
15.81% to 1.61%; the retained checked wrapper accounts for 1.72%, for a 79%
combined decrement-path reduction. The final module falls from 393,275 to
384,533 bytes even though one 22-byte wrapper survives, because the optimizer
removes 8,763 bytes from matched callers. Sixteen diagnostics-off alternating
AB/BA pairs move the median exported-entry time from 94.80 ms to 92.54 ms
(-2.4%); 15/16 pairs improve and the paired median is -2.36 ms. Exact output,
all ten levels, zero imports, and the flat 9,237,304-byte frontier remain
unchanged. W6 proof review remains the acceptance boundary.

### G1k. Return trusted ByteArray sizes through the typed result bridge (generation-ready)

The source compiler already proves the closed-call argument is a resident
ByteArray before selecting its trusted helper. That helper now keeps its
existing `< 2^31` size trap and returns the tagged Nat with the same typed
extend/tag/wrap bridge as direct Nat/USize results. It no longer borrows the
scratch slot solely to reclassify the physical word. The checked public helper,
input validation, helper signature, object layout, and ownership contract are
unchanged; generated-shape guards pin both bodies and the trusted local set.

On the exact 256-KiB seeded-random level-6 lean-zip workload, 32
diagnostics-off alternating AB/BA pairs move median exported-entry time from
88.64 ms to 86.62 ms (-2.3%); 30/32 pairs improve and the paired median is
-1.75 ms. Two artifact-bound profiles have comparable-diagnostic quality,
exact output, and a flat 9,237,304-byte frontier. Binaryen removes
`fir_ext_ByteArray_size` from the optimized module. The final artifact grows
from 384,533 to 387,598 bytes (+0.8%) because the direct sequence is duplicated
into callers, while the final function count falls from 505 to 504 and imports
remain zero. W6 proof review remains the acceptance boundary.
### G1l. Lower closed closure dispatch from its finite source target set (proof review)

The opt-in closed-boundary compiler now supplies the final-LCNF `pap` target
set at `compileClosureDispatch`, so impossible matcher bodies are never
constructed. The generic `lowerSupported` path remains all-target. The closed
module derives `closureDispatch` and `closureDescriptors` from its retained
operations: raw lean-zip uses 23 dispatch rows and 38 descriptor rows instead
of the generic 439 and 194. These IDs are module-local; the boundary accepts no
pre-existing closure object or external header ID.

An exact raw lean-zip comparison normalizes only those two metadata arrays and
then requires the early module to equal generic lowering followed by G1i's
structural pass. Encoded normalized bytes are also equal. In the first
controlled candidate run, generic lowering took 30,929 ms and finite-target
lowering 18,443 ms, while removing 10,888 candidates and retaining 734. Host
load varied substantially during the experiment, so this establishes the
mechanism and a directional generation win rather than a precise percentage.

W6 review remains the integration boundary: its refinement must state the
closed-ingress premise and use the module's exact retained dispatch/descriptor
tables. No helper signature, heap layout, closure header layout, or generic
opaque-ingress behavior changes.

### G1l. Align trusted Array mutation setup with upstream Lean (generation-ready)

Upstream `lean_array_uset` converts a valid Array to its runtime address and
uses `lean_is_exclusive`, whose hot test is the reference count. FIR's trusted
mutation helpers previously round-tripped the Array word through scratch memory
and rechecked both flags and reference count even though typed closed execution
already carries the resident Array invariant. Trusted `push`, `pop`, `uset`,
`set`, `set!`, and `swap` now use the typed extend/wrap address bridge and the
single `refCount == 1` classifier. Checked/public helpers keep their former
scratch retype and flag-aware test. Unique updates, shared copies, ownership
transfers, and release behavior are unchanged and remain covered by exact
generated-shape guards and the source/V8 ownership corpus.

For lean-zip level 6, `fir_ext_Array_set` shrinks from 386 to 344 bytes, the
frontier from 669,017 to 668,657 bytes, and the complete zero-import module
from 387,598 to 387,379 bytes. Two sequential artifact-bound profiles move the
helper's median normalized Wasm-self share from 3.46% to 3.17% (about 8.5%),
while exact output and the flat 9,237,304-byte frontier remain unchanged.
Elapsed measurements were bimodal under concurrent host load and co-resident
module order changed their sign, so this is accepted as upstream-aligned code
shape without an end-to-end timing claim. W6 must connect the trusted resident
Array premise to the refcount-only classifier before contract acceptance.

### G1m. Initialize only unwritten constructor storage (generation-ready)

Resident constructor allocation previously zeroed every 32-bit word in the
fresh extent and then immediately overwrote all eight header words plus the low
word of every object slot. The helper now writes those values directly and
zeros only bytes whose initialized value is semantically zero: each object
slot's high word and the contiguous USize/scalar/alignment suffix. Constructor
layout, helper signatures, allocation extent, field order, and every final byte
remain unchanged.

The standalone artifact rewinds the module-owned arena, poisons the entire
64-byte reused extent with `0xff`, reallocates, and checks all 16 words: exact
header, object values, object-slot high words, packed scalar storage, alignment,
frontier, and scratch restoration. This avoids relying on WebAssembly's fresh
zeroed memory. Lean Beam, all 713 repository cases and 2,121/2,121 comparisons,
all 3,172 Talos jobs, deterministic regeneration, browser stack stress, and the
complete artifact gate pass on current main.

The resident constructor fixture shrinks from 1,015 to 981 bytes. The exact
current-main prettyM module shrinks from 88,223 bytes (SHA-256
`93462b3d47f7aac07a88576a5613f84459659abc18cbd24ea2d32e418b6248ad`)
to 85,418 bytes (SHA-256
`47dd699a4553d600611b68cd4deeeb9d8ba4ba1a2cf5429e45d0fe681d5169c8`),
a 2,805-byte / 3.18% reduction with zero imports. Sixteen fresh-process pairs
were directionally favorable in 10 cases, but host dispersion was too large
for an end-to-end speed claim. Exact code size and poisoned-reuse semantics,
not noisy elapsed time, are the acceptance evidence.

### G1n. Inline the upstream `USize.toNat` scalar branch (generation-ready)

Upstream `lean_usize_to_nat` tags values at or below the small-Nat boundary in
its static-inline wrapper and calls the out-of-line constructor only for wider
values. FIR now makes the same split at compiled call sites. The resident
`fir_ext_USize_toNat` helper remains the complete checked cold path and retains
its public signature, large-value allocation, and malformed-boundary behavior.
The direct linker selects `USize.ofNat` and `USize.toNat` caller rules
independently, so importing one does not reserve or apply the other rule.

The exact lean-zip closure remains 769 captured declarations, 630 source
functions, 830 resident helpers, and 504 final functions with zero imports.
One matched screening profile moves the helper from 33/1,236 Wasm-self samples
(2.67%) to zero in 1,461. Eight order-balanced process pairs give a directional
paired median of -3.94 ms with 6/8 improving; the complete module grows from
396,588 to 406,574 bytes (+2.52%). Native/Wasm output, all ten compression
levels, lazy-cache ownership, and the flat 9,237,304-byte frontier remain exact.
W6 proof review of the caller branch remains the separate acceptance boundary.

### G1o. Return constructor addresses through the typed result bridge (generation-ready)

Heap constructor helpers already receive a valid, aligned wasm32 address from
the resident allocator. They previously borrowed address zero to save one
scratch word, store the address, reload it through the declared object-family
result lane, and restore the scratch word. The helper now uses the established
typed extend/wrap bridge: extend the raw `i32` word to `i64`, then wrap it back
to the statically declared `.object` or `.tobject` result. Binaryen erases this
physical round trip. Constructor allocation, final bytes, layout, signatures,
ownership, and the module-owned frontier are unchanged; address zero is never
touched.

The generated-shape guard pins the one-local helper, exact four-instruction
return suffix, and absence of loads. The standalone zero-import constructor
fixture still covers immediate and heap constructors, poisoned 64-byte arena
reuse, exact headers and fields, memory growth, and the untouched reserved
word. It shrinks from 981 to 935 bytes. On the exact early-closure prettyM
candidate, the plain module shrinks from 79,969 to 79,002 bytes and the styled
trace from 83,521 to 82,370 bytes, retaining 314 final functions; instruction
origins fall from 24,151 to 23,901. Deterministic generation, checksum and
package verification, browser and raw clients, styled traces, stack stress,
the native/LCNF/V8 differential cone, concrete readiness, and ownership checks
all pass. These are exact code-shape and size results, not a runtime-speed
claim. The future W6 resident-constructor implementation proof should target
this scratch-free suffix; no stable concrete contract changed.

### G1p. Inline the upstream `Nat.shiftRight` scalar branch (generation-ready)

Upstream `lean_nat_shiftr` tests both Nat operands in its static-inline wrapper.
Two immediate operands are unboxed and shifted directly; a count at least the
machine word width returns zero, while any heap operand enters the complete
arbitrary-precision fallback. FIR now reproduces that split at compiled call
sites. The Wasm32 arm guards `count < 32` before `i32.shr_u`, avoiding Wasm's
modulo-32 shift-count behavior. `fir_ext_Nat_shiftRight` remains unchanged and
available for promoted, multi-limb, mixed, malformed, and public-helper calls.

A durable zero-import resident Nat artifact probe covers an actual rewritten
caller at counts 0, 1, 30, 31, 32, and 33 using the maximum immediate payload
and exact tagged result words. The native/LCNF/V8 corpus retains its four
multi-limb input/count cases, so both the caller arm and cold fallback have
real-engine evidence. The exact lean-zip closure and final inventory remain
769 captured declarations, 630 source functions, 830 resident helpers, 504
final functions, and zero imports. The frontier grows from 724,108 to 730,514
bytes and the complete module from 406,574 to 407,831 bytes (+0.31%) in the
isolated before/after experiment. Rebased after the scratch-free constructor
bridge, the combined ratcheted package is 728,808 frontier bytes and 407,516
complete bytes.

Two checked exact-release profiles move `fir_ext_Nat_shiftRight` from 290/320
self samples and a 5.86% median Wasm-self share to zero samples in both
candidates. The helper remains in the final artifact for heap fallbacks rather
than being optimized away. Eight diagnostics-off AB/BA process pairs move the
median of per-process medians from 175.34 ms (MAD 1.59) to 158.61 ms (MAD
0.55), a 9.5% reduction; the paired median is -17.04 ms and all eight pairs
improve. Exact compressed output and the flat 9,237,304-byte frontier remain
unchanged. W6 proof review of the tagged-pair and word-width branches remains
the separate acceptance boundary.

### G1q. Inline the profiled Nat and trusted Array caller paths (generation-ready)

The next exact lean-zip profile identified four generic resident boundaries:
`Nat.add`, `Nat.mod`, `Nat.land`, and trusted `Array.set`. FIR now applies the
same caller/cold-helper split used by Lean 4.32's inline C API. Tagged Nat pairs
compute addition, remainder, and bitwise AND in the caller; addition overflow
and every heap/mixed pair reconstruct the original helper arguments and enter
the complete arbitrary-precision fallback. Remainder by tagged zero returns
the dividend, matching `Nat.mod n 0`. Trusted `Array.set` mutates only an
exclusive refcount-one array, decrements the replaced object, and sends
persistent/shared inputs through the complete copy fallback. Checked-mode
`Array.set` lowering and all public helpers remain unchanged.

The implementation is a generic resident-linker rewrite and contains no
lean-zip declaration names. Zero-import artifact probes execute each rewritten
Nat caller's tagged and heap/overflow arms, plus exclusive and shared trusted
Array callers. The exact release package retains 769 captured declarations,
630 source functions, 830 resident helpers, 504 final functions, and zero
imports. The complete module grows from 407,516 to 454,918 bytes (+11.63%) and
the frontier from 728,808 to 849,251 bytes; this is the deliberate code-size
cost of applying the upstream inline convention at every eligible caller.

Two checked artifact-bound profiles move `fir_big_ext_Nat_add`,
`fir_ext_Nat_mod`, `fir_ext_Array_set`, and `fir_ext_Nat_land` from a combined
18.23% median Wasm-self share to zero samples in both candidates. Eight
diagnostics-off AB/BA process pairs on the 256-KiB seeded-random level-6
workload move the median of per-process medians from 79.46 ms (MAD 0.69) to
54.20 ms (MAD 1.05), a 31.8% reduction; the paired median is -24.44 ms and all
eight pairs improve. Exact compressed output, levels 1 through 10, the
persistent-cache/scratch-rewind contract, and deterministic publication remain
unchanged. W6 proof review of the three tagged Nat branches and the trusted
exclusive/shared Array split remains a separate acceptance boundary.

### G1r. Apply checked decrement gates inside resident callers (generation-ready)

Resident Array, ByteArray, String, and Nat helpers now use the same
caller-local tagged/erased-zero classification as upstream `lean_dec` and
FIR's compiled checked wrappers. Typed heap-only `.object` values keep their
direct decrement path. The public `fir_dec_once` signature and complete
recursive body remain unchanged, preserving the current W6 proof boundary.

On the exact 256-KiB level-6 lean-zip workload, steady dynamic helper entries
fall from 1,222,005 to 169,608 and tagged no-op entries from 1,195,723 to
143,326. Two exact-artifact profiles move median `fir_dec_once` self share from
4.16% to 1.81%. Sixteen unprofiled order-balanced AB/BA rounds improve 16/16,
with median steady call time moving from 33.097 ms to 30.979 ms and a -6.38%
paired median. The final zero-import module grows by 1,321 bytes (0.36%); exact
output, imports/exports, and the flat rewind frontier are unchanged.

### G2. Separate production and diagnostic adapter costs (accepted)

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

The first slice is accepted. `integration/package-tools/verified-package.mjs`
checks the exact regular-file/checksum inventory, declared BUILD schema and
capability versions, artifact length and digest, import counts, memory owner,
descriptor closure, and public Wasm exports. Its fresh-output installer stages
beside the caller-owned destination, runs the package-local smoke before and
after atomic rename, and removes rejected output. HitScene v2 and the selection
player supply only small declarative policies; their existing semantic and
flat-frontier smokes remain unchanged. Exact install replays reproduced every
accepted file byte-for-byte, including the 64,217-byte HitScene module and the
40,398-byte selection module, both with zero imports and module-owned memory.
The two producers now also reuse the accepted immutable publisher, whose new
validation hook runs before either an immutable directory or current link is
exposed.

This is deliberately not a build framework or coordination service. Extract
only behavior already duplicated by at least two accepted packages. Keep
workload semantics, oracle comparisons, and memory limits in each integration.
Require existing packages to retain their public API and either reproduce
their bytes or explain an intentional metadata-version change.

The optional shared descriptor vocabulary is
`browser-benchmarks/source-package/v1`; it describes provenance, producer,
verifier, operations, ownership, and phase names, not application behavior.
The producer-side draft is now implemented as a read-only descriptor derived
from an already verified package. It normalizes exact source commits and
relevant-file digests, the producing project/backend/Lean identity and Wasm
artifact, verifier-backed acceptance, the checksum/smoke/evidence contract,
production versus diagnostic operations with versioned input/result contracts,
startup/initialization/per-call fields, and complete transfer plus arena
ownership. It rejects incomplete provenance, checksum drift, operation drift,
duplicate fields, unbound evidence, malformed Lean identity, and ownership
facts inconsistent with the accepted BUILD metadata.

HitScene v2 and selection-player v3 exercise the draft without changing their
BUILD schemas, inventories, package identifiers, or bytes. The first review
snapshots live only under the ignored worktree-local
`.deps/source-package-review/`: HitScene is 4,290 bytes with SHA-256
`dad988f4e24142a89f6b25d941ba4de081728fa49cc70e714454cd895df3c26d`;
selection is 4,523 bytes with SHA-256
`6aabb23f8073b682c75f6b01d68aa2994a4781b98ded91daec511b283e0f87b5`.
Verso and lean-zip accepted the boundary and requested exact Lean identity,
verifier-backed acceptance, versioned operation input/result contracts,
separate startup and lazy-initialization fields, checksummed producer evidence,
and explicit public-input/encoded-input/output transfer ownership. The current
consumer-review candidate adds those facts without embedding application
schemas: operation contracts are identifiers owned by the versioned adapter
API, while startup and initialization inventories remain producer-named public
fields rather than a universal timing ontology.

Both completed reviews prefer a checksummed `SOURCE_PACKAGE.json` sibling with
a small BUILD pointer. Illuminate review is still outstanding, so publication
remains deferred. Adding the sibling, changing BUILD metadata, and creating new
immutable package identities must be a separate atomic-publication slice after
all three consumers agree.

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

### Compact upstream-aligned object representation

FIR's current 32-byte self-describing W6 header remains the checked executable
and proof baseline. Caller-local paths such as `getTag` can follow upstream
Lean's static-inline behavior without changing that representation; they are
not evidence that a layout migration is already justified.

When allocation, frontier growth, or cache locality again dominates a real
package profile, evaluate a compact production representation aligned with
Lean's optimized object headers. Require before/after allocation counts,
frontier bytes, binary size, and external-engine timing on at least prettyM and
lean-zip. Any accepted design must preserve tags, boxing, uniqueness,
recursive release, persistent caches, and malformed-boundary behavior through
one explicit concrete-layout contract. Treat the W6 relation and proofs, W7
allocator/encoders/reclamation, browser adapters, and package layouts as one
coordinated migration; do not introduce a second unproved production layout or
a client-specific compact encoding.

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
