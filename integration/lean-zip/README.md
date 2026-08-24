# FIR-native lean-zip bring-up

This integration compiles the real Lean 4.32-compatible entries

```lean
Zip.Wasm.compressStored : ByteArray → ByteArray
Zip.Wasm.compressLevel1 : ByteArray → ByteArray
Zip.Wasm.compressRaw : ByteArray → UInt8 → ByteArray
```

from lean-zip commit `273d0d6cd9cab77c7f3489b0b0b1f6e543315d21`.
The stored entry is the minimal boundary control. Level-1 is the first
production matcher/emitter slice. FIR reads clean source checkouts and writes
every build product locally; it never consumes lean-zip's `.lake` products.

This revision uses Lean's legacy module syntax. FIR therefore captures its real
declarations through the generic single-unit final-LCNF path; module-wise replay
is reserved for sources containing `module` / `public section` boundaries.

Create persistent clean source views under FIR's ignored, worktree-local
`.deps/source-views/` directory, then run the closure probe. Do not use `/tmp`:

```sh
fir_root="$(git rev-parse --show-toplevel)"
mkdir -p "$fir_root/.deps/source-views"
git clone --no-local --no-checkout /path/to/lean-zip \
  "$fir_root/.deps/source-views/lean-zip"
git -C "$fir_root/.deps/source-views/lean-zip" checkout --detach \
  273d0d6cd9cab77c7f3489b0b0b1f6e543315d21
git clone --no-local --no-checkout /path/to/zipCommon \
  "$fir_root/.deps/source-views/zip-common"
git -C "$fir_root/.deps/source-views/zip-common" checkout --detach \
  4425bab1f9522307d77e8d485bc536149ba31c36

lake --keep-toolchain --reconfigure \
  -KleanZipRoot="$fir_root/.deps/source-views/lean-zip" \
  -KzipCommonRoot="$fir_root/.deps/source-views/zip-common" \
  build LeanZipFir.Compile leanZipFirLevel1Artifact
lake --keep-toolchain env lean Probe.lean
lake --keep-toolchain env lean ProbeLevel1.lean
lake --keep-toolchain env lean ProbeRaw.lean
```

The Level-1 package generator stores its expensive final-LCNF source capture
in `LeanZipFir.CapturedLevel1.olean`, then runs lowering and resident linking
as native code. From this directory, the hot command is
`.lake/build/bin/leanZipFirLevel1Artifact`; it prints one linear millisecond
timeline covering module load, cached capture lookup, lowering/base encoding,
resident linking/final encoding, and output writes. Lake's content-addressed
artifact cache can restore the capture checkpoint across FIR worktrees.

The produced artifact is not a host-backed ByteArray facade. `ByteArray.size`,
`ByteArray.mk`, `ByteArray.emptyWithCapacity`, and `ByteArray.copySlice` run in
the Wasm module over a packed resident representation. JavaScript copies input
and output bytes at the boundary; no raw address escapes.

The v2 layout also preserves Lean's ownership behavior. Fresh resident
ByteArrays are live, nonpersistent values with reference count one.
`copySlice` mutates such a destination in place exactly when its capacity is
sufficient; shared or persistent destinations are copied and one consumed
ordinary reference is decremented. Boundary inputs remain persistent borrowed
values and therefore cannot be mutated by compiled Lean.

Run the complete deterministic, native-oracle, Node, and optional browser gate:

```sh
LEAN_ZIP_ROOT="$fir_root/.deps/source-views/lean-zip" \
ZIP_COMMON_ROOT="$fir_root/.deps/source-views/zip-common" \
FIR_BROWSER=google-chrome \
./check.sh
```

`package.mjs`, `package-raw.mjs`, and `check.sh` use those persistent FIR-local
source views by default. Environment overrides remain available for another
equally persistent clean checkout.

Immutable packages are under `_build/lean-zip-stored-packages/` and
`_build/lean-zip-level1-packages/`; the production levels 1–10 package is
produced by `node package-raw.mjs` under `_build/lean-zip-raw-packages/`.
Their atomic canonical pointers end in `-current`. Every package is checksummed
and can run `node smoke.mjs` without the FIR or lean-zip source trees.

Catalog consumers should use the fail-closed fresh-output entry rather than
the direct-use aliases above:

```sh
integration/lean-zip/export-raw-package.mjs \
  --output /caller/controlled/fir-native \
  --checkout producer=/exact/clean/fir \
  --checkout client=/exact/clean/lean-zip \
  --checkout zip-common=/exact/clean/zipCommon
```

The exporter accepts exactly those three source roles and no dependency
packages. It verifies clean worktree roots and the revisions in
`raw-source-contract.json`, stages atomically beside the requested output,
checks the exact regular-file inventory and all hashes, and runs the
package-local smoke before returning. The output must not already exist.

The raw package also carries `lean-zip-raw.wasm.functions.json`, a versioned
index for every function in the final optimized module. The producer tracks
function identities through runtime linking, dead-code elimination, and the
final Binaryen optimizer, then requires the evidence-enabled release bytes to
equal the ordinary release bytes exactly. `BUILD.json` and `SHA256SUMS` bind
the sidecar to the Wasm hash, function/import counts, origin counts, and exact
export indices. It is diagnostic package metadata only: neither the adapter nor
the Wasm module loads it during execution.

Do not advance the raw canonical pointer while validating a dirty or stale-base
branch. `FIR_RAW_PACKAGE_PREVIEW_DIR=$fir_root/.deps/previews/PATH` selects an
explicit persistent preview destination and suppresses canonical publication;
dirty previews additionally require the existing
`FIR_ALLOW_DIRTY_PACKAGE=1` acknowledgment.

The browser/Node API is:

```js
const adapter = await createLeanZipStoredAdapter({ bytes, descriptor });
const { bytes: compressed, timings, memory } =
  adapter.compressStored(inputBytes);

const level1 = await createLeanZipLevel1Adapter({ bytes, descriptor });
const level1Result = level1.compressLevel1(inputBytes);

const raw = await createLeanZipRawAdapter({ bytes, descriptor });
const rawResult = raw.compressRaw(inputBytes, level); // level in 1..10
```

Every call uses a scratch checkpoint: the adapter copies the result, rewinds
the module-owned arena even on failure, and exposes no Wasm address.

Level-1 and the levels 1--10 raw dispatcher preserve Lean's compiler-generated
lazy constants at their original use sites. When a cold call publishes an
object cache, the resident runtime recursively marks its graph persistent and
advances a monotonic rewind floor through the published prefix. The adapters
accept that one-time checkpoint growth; repeating the same call is required to
rewind flat to the resulting floor. This avoids forcing panic-only fallback
constants that are present in the captured closure but unreachable in ordinary
execution. `adapter.initialization` therefore reports no eager initializer;
cold first-use cache work is included honestly in the entry's execute timing.

Both public wrappers reuse the same versioned ByteArray encoder, decoder,
module validator, timing, and scratch-ownership implementation. Level-1 has
zero imports and is suitable for correctness testing in Node and browsers.
Generic resident operations and closure execution remain optimization targets;
`BUILD.json` makes no cross-runtime performance claim.

The raw producer compiles Lean's `Float.ofNat` and `Float.ofScientific`
definitions from final LCNF, retains exactly `Float.log2` at its reviewed
frontier, and closes it with the pinned standard libm runtime. Its published
module has zero imports. The browser adapter
reserves `STANDARD_LIBM_RUNTIME_RESERVED_MEMORY_BYTES` before lazy-cache
publication or Lean allocation, and the package records both frontier and
complete identities plus the runtime source, contract, and Emscripten identity.

The exact source-Float raw closure is ratcheted in
`raw-closure-contract.json`: 769 captured declarations, 139 reviewed
externals, 630 retained source functions, 23 final-LCNF partial-application
targets, 830 resident helpers, and 1,460 complete pre-optimization functions.
In addition to counts and Wasm byte lengths, the contract pins SHA-256 digests
of the ordered external, source-function, source-closure-target,
resident-helper, and complete-function inventories. This prevents a same-count
closure change from passing the package gate without review.

The same contract ratchets the final optimized artifact at 504 functions and
zero function imports, with 228 surviving Lean-source functions, 276 resident
helpers, and no optimizer-or-linked-runtime functions. The function index
digest and sidecar digest make an index-preserving but identity-changing
release a reviewed package change rather than an unnoticed one.

The additional final helper is `fir_numeric_natural_sum`: the generic
immediate-`Nat.add` branch gives it a second surviving use, so Binaryen no
longer inlines away its former sole use. No source declaration or
pre-optimization helper was added. On the checked 256-KiB level-6 corpus, the
branch preserves exact compressed bytes while reducing seeded-random raw-entry
time by 3.48x and 3.39x in two profiles and structured-input time by 1.79x.
`fir_big_ext_Nat_add` self time falls by about 6.5x on both random profiles;
the validation and magnitude helpers fall as well rather than absorbing the
removed work.

The arbitrary-precision decision helpers likewise dispatch two canonical
tagged immediates directly through Wasm unsigned comparisons. Promoted and
heap-backed operands retain the checked generic magnitude path. On the same
256-KiB seeded-random level-6 profile contract, this lowers median raw-entry
time from 391.71/387.83 ms to 270.49/284.03 ms in two captures. Generic compare
self samples fall by 89.8%, magnitude low/high by 62.8%/76.2%, and natural
validation by 75.7%, with identical compressed bytes and a flat frontier.

`USize.ofNat` and `USize.ofNatLT` now decode a canonical tagged Nat directly
to the Wasm `i64` lane. Promoted and arbitrary-limb Nats use the generic
checked big-numeric accessors, including Lean's modulo-`2^64` behavior for
values wider than one limb. Against the preceding decision-helper package,
the same profile contract lowers median raw-entry time from 270.49/284.03 ms
to 219.84/220.72 ms, a further reduction of about 19%/22%. The helper's
combined self samples fall by about 61%; compressed bytes remain identical
and the post-call frontier remains flat at 9,237,304 bytes.

`Nat.mul` uses the same representation dispatcher for two tagged inputs. Their
31-bit payloads are widened and multiplied with Wasm `i64.mul`; the existing
natural constructor returns either a tagged result or the canonical promoted
one-limb representation. Every promoted, mixed, or arbitrary-limb input still
uses the checked multiplication implementation. Against the preceding
`USize.ofNat` package, level-6 medians fall from 219.84/220.72 ms to
190.94/187.20 ms, another reduction of about 13%/15%. `fir_ext_Nat_mul` self
samples fall by about 94%, with identical compressed bytes and the same flat
9,237,304-byte frontier.

`Nat.sub` likewise dispatches two canonical tagged operands before its checked
arbitrary-precision path. Tagged object words preserve payload order, and
subtracting the words then adding the tag computes exact truncated subtraction
without decoding or allocation; `left < right` returns tagged zero. Promoted,
mixed, arbitrary-limb, and malformed inputs retain full validation. Against
the preceding `Nat.mul` package, level-6 medians fall from 190.94/187.20 ms to
141.08/142.32 ms, about 26%/24%. `fir_big_ext_Nat_sub` combined self samples
fall by about 75% and magnitude-low samples by about 98%, with identical
compressed bytes and the same flat 9,237,304-byte frontier.

The immediate arm of `USize.ofNat` and `USize.ofNatLT` now returns the decoded
payload directly as the symbolic `.usize` result of `i64.extend_i32_u`. It no
longer stores and reloads the same physical `i64` lane through scratch memory
solely to change its semantic ABI kind. The boxed-Nat arm is unchanged: it
still validates and reduces the complete limb sequence modulo `2^64`. On eight
order-balanced unprofiled process rounds against the preceding `Nat.sub`
package, the median of steady-state medians changed from 143.16 ms
(MAD 0.46 ms) to 140.26 ms (MAD 0.72 ms), about 2.0%. In clean CPU profiles,
`fir_ext_USize_ofNat` self samples changed from 735 to 132/128, about 82%, while
`fir_dec_once` remained independent. Output bytes and the flat 9,237,304-byte
post-call frontier were unchanged.

`USize.toNat` now mirrors Lean's generic runtime path for canonical immediates:
values below `2^31` are tagged directly in the Wasm object lane, without a
scratch-memory retype or a call to the natural constructor. Values at or above
the boundary retain the existing checked constructor, including promoted
results. Against the preceding direct-`USize.ofNat` package, eight
order-balanced unprofiled process rounds changed the median of steady-state
medians from 137.91 ms (MAD 0.47 ms) to 130.66 ms (MAD 1.42 ms), about 5.3%.
`fir_ext_USize_toNat` self samples changed from 104 to 24/28, while generic
natural-constructor samples changed from 84 to 29/31. Compressed bytes and the
flat 9,237,304-byte post-call frontier were unchanged.

The checked one-limb and multi-limb exits of `Nat.add` now use the same typed
object-word round trip as its immediate exit. Both checked exits first validate
their inputs and then return either `fir_numeric_natural_sum`'s canonical Nat
or the live object allocated by `fir_big_numeric_allocate`; borrowing linear-
memory address zero solely to retype either word was redundant. The final
`fir_big_ext_Nat_add` body decreases from 268 to 228 bytes and from 130 to 111
instructions. Its three scratch loads and three scratch-only stores disappear;
the remaining two stores write a genuine carry limb. The frontier module
decreases from 1,619,431 to 1,619,339 bytes and the complete module from
936,112 to 936,072 bytes, with all closure counts, calls, imports, and semantic
outputs unchanged.

This is a deterministic code-shape and ownership improvement, not a measured
lean-zip speedup. Eight order-balanced 256-KiB level-6 rounds gave internal
execute medians of 124.15 ms before and 124.48 ms after (+0.27%, within noise),
while whole-process medians moved in the opposite direction by -0.61%. Two
artifact-bound V8 profiles likewise placed `Nat.add` at overlapping 3.60% and
3.50% median Wasm-self shares. Every run preserved the exact compressed-byte
hash and flat 9,237,304-byte frontier.

The shared-reference path in `fir_dec_once` now follows Lean's release shape
more closely: after the live check it loads the persistent flag and reference
count before decoding cold object metadata. A terminal-header-word probe keeps
the previous complete-header bounds trap. The final helper grows by 10 bytes,
the frontier from 1,619,339 to 1,619,356 bytes, and the externally linked
module from 936,072 to 936,082 bytes; inventories, imports, compressed output,
and the flat 9,237,304-byte frontier remain unchanged. In four artifact-bound
profiles its median normalized self share changes from 14.24% to 13.59%.
Across sixteen order-balanced level-6 pairs the paired median is -31.90 ms,
but only 9/16 pairs improve and dispersion is high, so the accepted result is
the five removed common-path header reads rather than an end-to-end speedup
claim.

The raw package declares a closed heap-closure boundary: its JavaScript input
encoder transfers ByteArrays and the compression level, never a pre-existing
Lean closure object. FIR therefore collects the 23 targets of actual
final-LCNF `pap` nodes and removes generated matcher branches for every other
captured declaration before resident linking. The generic opaque-closure
compiler API remains unchanged, and W6 closure descriptor/dispatch metadata is
retained for proof and ABI consumers. The package ratchet checks the ordered
target inventory and its digest. Compared with the preceding all-target
package, the complete module decreases from 936,082 to 393,070 bytes and from
2,305 to 508 final functions; exact compressed output, zero imports, lazy
constant publication, and the flat 9,237,304-byte rewind frontier are
unchanged. This post-lowering slice does not yet reduce all-target lowering
time.

Checked compiler-generated decrements now mirror upstream `lean_dec`: tagged
immediates and the checked erased-zero sentinel are classified in the compiled
caller, while heap references retain the complete `fir_dec_once` path.
Unprofiled alternating level-6 pairs move from a 94.80 ms median to 92.54 ms
(-2.4%, 15/16 improving), while two artifact-bound profiles reduce the combined
checked-wrapper plus `fir_dec_once` share by about 79%. The exact module falls
from 393,275 to 384,533 bytes; compressed output, imports, and the flat
9,237,304-byte frontier are unchanged.

The trusted `ByteArray.size` helper now returns its range-checked tagged Nat
through the typed object-word bridge already used by direct Nat/USize results.
It no longer stores and reloads the same physical word through scratch memory
solely to reclassify it as tagged. The checked public helper is unchanged, and
the trusted path retains the exact `< 2^31` trap before constructing the tag.
Binaryen consequently removes `fir_ext_ByteArray_size` from the final module.

Against the accepted checked-decrement package, 32 diagnostics-off alternating
AB/BA level-6 pairs move median exported-entry time from 88.64 ms to 86.62 ms
(-2.3%); 30/32 pairs improve and the paired median is -1.75 ms. Two
artifact-bound profiles preserve the exact compressed digest and flat
9,237,304-byte frontier, with no sampled `ByteArray.size` helper. The final
module grows from 384,533 to 387,598 bytes (+3,065, 0.8%) because Binaryen
duplicates the small direct size sequence into callers, while the final
function inventory decreases from 505 to 504 and remains zero-import.

Trusted Array mutations now mirror the setup of upstream `lean_array_uset`.
Their already-validated Array object is converted to its raw address through
the typed extend/wrap bridge instead of four scratch-memory operations, and
exclusivity is classified by the single `refCount == 1` header test used by
`lean_is_exclusive`. Checked/public helpers retain the prior scratch retype and
flag-aware exclusivity test. Unique and shared copy-on-write bodies, retained
element increments, replaced-element decrements, and consumed-array handling
are unchanged. The generated-shape guards cover `push`, `pop`, `uset`, `set`,
`set!`, and `swap`.

In the level-6 artifact, `fir_ext_Array_set` shrinks from 386 to 344 bytes, the
frontier from 669,017 to 668,657 bytes, and the complete module from 387,598 to
387,379 bytes. Two sequential artifact-bound profiles move its median
normalized Wasm-self share from 3.46% to 3.17% (about 8.5%) with exact output
and the same flat 9,237,304-byte frontier. Host timing was strongly bimodal
across separate processes and changed sign with co-resident module compilation
order, so this slice makes no end-to-end speedup claim.

`USize.ofNat` now has the same caller/cold-helper split as Lean's generic C
runtime: a call-site scalar-tag test decodes the overwhelmingly common tagged
Nat directly, while heap Nats still enter the checked resident helper. The
resident linker carries each inline rule's target, replacement, and fresh-local
requirements through persistent planning; it does not rely on Binaryen's broad
inlining threshold. On the same 256-KiB seeded-random level-6 workload,
`fir_ext_USize_ofNat` moves from 7.80% median Wasm-self share to no samples in
two artifact-bound profiles. Sixteen order-balanced separate-process pairs move
the median exported-entry time from 103.20 ms to 92.13 ms (-10.7%, 14/16 pairs
improving). The complete module grows from 387,379 to 396,588 bytes (+2.38%);
the global inliner probe needed a 1.07-MiB module to remove the same hot
boundary. Exact compressed output and the flat 9,237,304-byte frontier remain
unchanged.

`USize.toNat` now uses the symmetric upstream caller/cold-helper split. Values
below `2^31` are tagged directly at each compiled call site; larger values and
the public helper retain the complete checked natural-constructor path. One
matched screening profile moves `fir_ext_USize_toNat` from 33/1,236 Wasm-self
samples (2.67%) to no samples in 1,461, confirming that the work is removed
rather than shifted into the helper. Eight diagnostics-off AB/BA process pairs
move the median of per-process medians from 88.61 ms to 83.52 ms (-5.7%); the
paired median is -3.94 ms and 6/8 pairs improve. Host performance modes remain
visible, so this is directional elapsed evidence rather than a stable headline
claim. The reviewed closure inventories are unchanged, while the frontier grows
from 697,558 to 724,108 bytes and the complete module from 396,588 to 406,574
bytes (+2.52%). Exact compressed output and the flat 9,237,304-byte frontier
remain unchanged.

`Nat.shiftRight` now follows upstream's caller/cold-helper split as well. When
both operands are tagged Nats, the compiled caller unboxes them and performs a
direct Wasm32 shift. Counts at least 32 return tagged zero before reaching
`i32.shr_u`; this guard is required because core Wasm otherwise reduces the
count modulo 32. Any promoted, multi-limb, mixed, or malformed operand still
enters the unchanged `fir_ext_Nat_shiftRight` helper.

A durable zero-import resident Nat artifact probe passes an actual rewritten
caller at counts 0, 1, 30, 31, 32, and 33 using the maximum tagged payload and
exact raw result words, while the repository V8 corpus retains its four
multi-limb fallback cases. Two checked exact-release profiles move the helper
from 290/320 self samples and a 5.86% median Wasm-self share to no samples in
either candidate profile; the helper remains present for cold heap fallbacks.
Eight diagnostics-off AB/BA process pairs move the median of per-process
medians from 175.34 ms (MAD 1.59) to 158.61 ms (MAD 0.55), a 9.5% reduction;
the paired median is -17.04 ms and 8/8 pairs improve. The frontier grows from
724,108 to 730,514 bytes and the complete module from 406,574 to 407,831 bytes
(+0.31%) in the isolated experiment. After rebasing on the scratch-free
constructor-result bridge, the combined ratcheted package is 728,808 frontier
bytes and 407,516 complete bytes. Closure counts, exact compressed output, zero
imports, and the flat 9,237,304-byte frontier remain unchanged.

The following runtime-hotspot batch extends that upstream caller/cold-helper
split to `Nat.add`, `Nat.mod`, `Nat.land`, and trusted `Array.set`. Immediate
Nat pairs stay in the compiled caller, while overflow and heap/mixed values use
the unchanged arbitrary-precision helpers. Exclusive trusted arrays replace
their element in place and decrement the old object; shared or persistent
arrays use the complete copy fallback. This is generic FIR lowering rather
than a specialization of `Zip.Native.Deflate.lzMatchP`.

Two exact-release profiles remove all samples from the four old helper
boundaries, whose baseline median shares summed to 18.23% of Wasm self time.
Eight diagnostics-off AB/BA fresh-process pairs on the seeded-random 256-KiB,
level-6 workload move the median of process medians from 79.46 ms (MAD 0.69)
to 54.20 ms (MAD 1.05); the paired median is -24.44 ms and 8/8 pairs improve.
The complete zero-import module grows from 407,516 to 454,918 bytes (+11.63%)
and the frontier from 728,808 to 849,251 bytes. The closure counts remain 769
captured declarations, 630 retained source functions, 830 resident helpers,
and 504 final functions. All ten compression levels, native/Wasm differential
checks, deterministic packaging, and persistent-cache/scratch reclamation
remain exact.

The typed-Nat follow-up moves `Nat.decLt`, saturating `Nat.sub`, and the
non-overflowing arm of `Nat.mul` into those compiled callers. Each rewrite now
registers its full semantic FIR signature, including distinctions such as
`tobject`, `tagged`, `uint8`, and `usize`; the resident linker rejects missing,
duplicate, or signature-incompatible registrations before rewriting, and the
ordinary symbolic validator still checks every replacement body at its actual
caller stack boundary. Heap, mixed, and multiplication-overflow cases retain
the complete arbitrary-precision helpers.

Eight order-balanced fresh-process pairs against the preceding hotspot package
all improve on the seeded-random 256-KiB level-6 workload. The reported median
of process medians moves from 64.12 ms to 52.55 ms, with a -11.16 ms paired
median (about 18%). Two exact-release profiles remove the former `Nat.decLt`,
`Nat.sub`, and `Nat.mul` helper frames, whose preceding median shares were
4.48%, 4.12%, and 3.34%. The complete zero-import module grows from 454,918
to 478,669 bytes and the frontier from 849,251 to 918,680 bytes. Exact output,
all ten compression levels, and the flat 9,228,136-byte post-rewind frontier
remain unchanged.

An immediate-`Nat.decLe` caller rewrite was evaluated on top of this package
and rejected. It removed the sampled `fir_big_ext_Nat_decLe` frame, but eight
order-balanced fresh-process pairs were neutral: the baseline and candidate
medians were 45.24 ms and 45.36 ms, the paired median was +0.45 ms, and only
4/8 pairs improved. The candidate also grew the complete module by 9,640 bytes
and the frontier by 29,075 bytes. This negative result keeps target selection
at the representative workload boundary: the next investigation is the
dominant `Zip.Native.Deflate.lzMatchP` body and its ownership traffic, not
further unprofiled comparison inlining.

For performance characterization, `array-scaling-bench.mjs` runs one
diagnostics-free, warmed level-6 workload and emits raw execute samples, input
and output hashes, and the post-rewind frontier. It is a measurement seed, not
an absolute-time test: compare identified baseline and candidate packages with
an order-balanced harness and retain the raw process rows. The `random` family
exercises the Array-heavy matcher path at caller-selected sizes; `structured`
retains the deterministic mixed-text control.
