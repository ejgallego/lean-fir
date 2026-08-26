# FIR-native lean-zip bring-up

This integration compiles the real Lean 4.33 entries

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

Ordinary raw publication is intentionally single-pass: one final-LCNF capture
and lowering produces an immutable base artifact, resident linking derives the
frontier from that value, and the external runtime closes the module once. The
result JSON reports monotonic `prepareMs`, `generateMs`,
`verifyAndPublishMs`, and `totalMs` intervals. It does not include timings in
`BUILD.json`, so package identity remains deterministic.

Run the slower, explicitly opt-in source-diagnostic and byte-for-byte repeat
generation gate with:

```sh
node check-raw-determinism.mjs
```

That command additionally runs `ProbeRaw.lean`, generates the complete module
twice, and compares the frontier, final module, descriptor, libm runtime, and
function sidecar. Its default preview lives under the current worktree's
ignored `.deps/previews/`; it never advances the canonical package pointer.

On exact FIR base `b52710d2`, the former ordinary topology measured 165.226s:
1.093s preparation, 48.394s probe, 55.732s first complete generation, 58.598s
repeat generation, and 1.409s verification/publication. The single-pass
candidate measured 45.974s: 0.988s preparation, 43.565s generation, and
1.421s verification/publication. This is a 72.2% build-latency reduction
(3.59x throughput), not a generated-Wasm runtime claim. The explicit
diagnostic/determinism mode remains available and measured 142.824s.

Selecting the first and only captured artifact exposed
`FIR-BUG-wasm-none-repeated-final-capture-code-shape`: the former redundant
second capture had a different optimized shape despite an identical source,
function, call, ABI, import, and ownership inventory. The deterministic
single-capture release is 366,826 bytes, 375 bytes smaller than that historical
second-capture release, and passes the complete 50-way native/Wasm/inflate
differential plus scratch-reclamation checks.

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

An upstream-shaped checked-increment factoring experiment was also rejected
for this performance lane. It let each compiler-generated one-reference
wrapper classify tagged immediates and sent heap references to the complete
shared `fir_inc_once` implementation. This consolidated duplicated heap logic:
the raw frontier fell from 918,680 to 820,724 bytes (-10.7%) and the final
zero-import module from 478,669 to 414,781 bytes (-13.3%). The final function
count rose from 504 to 505 because the 103-byte cold helper remained alongside
the 15-byte `fir_inc_0` wrapper.

Two artifact-bound screening profiles moved `fir_inc_0` from a 2.70% median
Wasm-self share to 0.16%; `fir_inc_once` contributed another 0.16%. However,
thirty-two order-balanced fresh-process pairs were elapsed-time neutral:
baseline and candidate medians were 40.77 ms and 40.70 ms, the paired median
was +0.05 ms, and exactly 16/32 pairs improved. Exact compressed output and the
flat 9,237,304-byte frontier were unchanged. The emitter change was therefore
discarded under the lane's representative-performance acceptance rule; its
code-size result remains evidence for a future size-oriented policy.

Fixed-width i32 results now preserve their physical lane through the typed
`i64.extend_i32_u` / `i32.wrap_i64` bridge instead of borrowing linear-memory
address zero to change semantic ABI kind. This provider-level path covers the
UInt8, UInt16, and UInt32 result families, including Boolean decisions and
object/tagged conversions. The i64 retype path is deliberately unchanged and
retains its scratch save/restore sequence at this checkpoint.

In the exact level-6 release, `Zip.Native.Deflate.lzMatchP` shrinks from 36,982
to 31,706 bytes and from 18,123 to 15,869 instructions. Its memory operations
fall from 1,056 to 272: all 205 fixed-width i64 scratch loads and stores
disappear, while the nine unrelated i64 loads and nine stores remain. The
frontier decreases from 820,883 to 818,855 bytes and the complete zero-import
module from 414,753 to 367,176 bytes. Final DCE/inlining removes
`fir_ext_UInt32_toNat`, `Zip.Native.Deflate.niceLen`, and
`Zip.Native.Deflate.goodMatch`, leaving 501 final functions without changing
the captured or pre-optimization inventories.

The shared provider improvement also reduces the stored-control package from
12,678 to 12,418 bytes and the Level-1 package from 195,273 to 193,661 bytes.
Their captured declarations, closure targets, source functions, resident
helpers, imports, and exports remain unchanged.

Thirty-two diagnostics-off AB/BA fresh-process pairs preserve the exact output
digest and flat 9,237,304-byte frontier while moving median exported-entry time
from 41.50 ms (MAD 1.79) to 39.07 ms (MAD 2.19). The paired median is -2.15 ms
(-5.3%) and 21/32 pairs improve; the two order halves independently have
-1.96 ms and -2.15 ms paired medians. Two exact-artifact profiles reproduce
the predicted code-shape movement; `lzMatchP` remains the dominant caller at
about 51% of Wasm self time rather than shifting the removed scratch traffic
into another helper.

The resident `ByteArray.pushUInt64LE` helper now also mirrors Lean's native
wide-push reuse path. After the ordinary capacity and uniqueness checks, an
exclusive buffer with at least eight bytes of remaining capacity receives one
unaligned `i64.store`; counts below eight may write into private capacity slack,
which a later logical extension overwrites before exposing it. Exact-capacity,
growth, and shared inputs retain the byte-wise path, so copy-on-write and the
public logical size are unchanged. Focused resident tests cover counts 0--8,
tight and slack capacity, shared and growing inputs, and subsequent pushes that
overwrite every speculative slack byte.

This adds one branch and 25 bytes to the complete module (367,176 to 367,201)
while leaving the 501-function, zero-import closure unchanged. Four comparable
exact-artifact profiles move `fir_ext_ByteArray_pushUInt64LE` from a 3.04% to a
2.51% median share of Wasm self samples. Thirty-two diagnostics-off AB/BA
fresh-process pairs preserve the exact compressed digest and flat frontier:
median exported-entry time moves from 38.27 ms (MAD 1.37) to 38.01 ms (MAD
1.88), with a -0.143 ms paired median (-0.37%) and 19/32 improving pairs. Both
round halves and both execution orders have negative paired medians, so the
small improvement is accepted without treating it as a larger performance
claim.

Trusted `Array.set!` now follows upstream `lean_array_set` at its Nat-index
boundary. The checked/public helper still validates the full arbitrary-width
Natural representation. A typed final-LCNF caller instead tests the immediate
tag, unboxes only a scalar index, and treats every heap Natural as out of
bounds; no wasm32-resident Array can have a heap-Nat-sized valid index. Scalar
in-bounds and out-of-bounds cases, heap-Nat rejection, unique reuse, shared
copy-on-write, and replacement release have direct zero-import coverage.

This alignment removes `fir_numeric_validate_natural` from the trusted
helper's direct callees and reduces that helper from 407 to 377 bytes. The
single-pass complete module decreases from 366,826 to 366,796 bytes while
retaining 501 functions, zero imports, exact compressed output, and the flat
rewind frontier. It is accepted for upstream fidelity and smaller code shape,
not as an elapsed-time win: the prior 32-pair experiment measured a +0.17 ms
paired median (+0.44%) with 14/32 improving pairs, below the benchmark's
resolution for a helper contributing about one percent of sampled execution.

The fixed-width i64 successor removes the remaining private scratch-memory
retype. Same-kind `UInt64` results now return directly. `UInt64.toUSize`, whose
physical i64 lane is unchanged but whose semantic ABI kind differs, crosses a
typed `i64 -> f64 -> i64` reinterpret pair that Binaryen erases. This mirrors
Lean's native scalar convention without changing any declaration signature,
layout, ownership rule, validation path, or observable bits.

On the exact post-`Array.set!` package, this reduces
`Zip.Native.Deflate.chooseSplitsHeuristicPUPacked` from 9,542 to 6,634 bytes
and from 4,699 to 3,410 instructions. Its 220 `i64.load` and 220 `i64.store`
sites fall to the 26 loads and 26 stores belonging to real data access; total
memory operations fall from 464 to 76 and direct calls from 282 to 265. The
complete zero-import module decreases from 366,796 to 359,760 bytes and from
501 to 500 functions. The captured and pre-optimization inventories remain
unchanged; final optimization also makes
`Zip.Native.BitWriter.dropBytesU` dead. The same generic change reduces the
Level-1 package from 193,694 to 193,150 bytes; the 12,418-byte stored package
is byte-identical.

Two independent diagnostics-off campaigns of 32 order-balanced fresh-process
pairs preserve the exact output and flat 9,237,304-byte frontier. Their paired
medians are respectively -0.495 ms (-1.22%, 21/32 wins) and -0.443 ms (-1.21%,
20/32 wins). Across all 64 pairs the paired median is -0.477 ms (-1.22%), with
41/64 wins; both execution-order buckets improve. Three of four 16-pair blocks
improve, while the first block is +0.509 ms, so this is a modest workload win
with observed host drift rather than a larger throughput claim. Four fresh
exact-artifact profiles retain the same top-five hotspot ranking and introduce
no replacement hotspot. `chooseSplitsHeuristicPUPacked` remains about 9--10%
of normalized Wasm self samples because the whole workload also moves; the
exact function view above, rather than the noisy share, establishes removal of
the targeted scratch traffic.

The next generic slice aligns final-LCNF constructor discrimination with
upstream `lean_obj_tag`. Typed `.getTag` callers now test the immediate bit and
read an ordinary constructor's `aux0` tag directly; non-constructor heap
families retain the complete checked `fir_getTag` call. The standalone helper
is unchanged at 111 bytes and remains out of line with 53 static cold callers.
Its checked null, alignment, liveness, kind, persistence, and promoted-tag
behavior therefore remains available at the runtime boundary.

Exact one-call/two-call V8 trace subtraction on a 256-byte steady invocation
reduces dynamic `fir_getTag` calls from 37,810 to zero. The original calls
returned tag one 37,076 times and tag zero 734 times, confirming the profiled
List/constructor common path rather than a client-specific value pattern. Four
fresh exact-artifact profiles contain no `fir_getTag` self samples and retain
the same leading workload functions without a replacement resident hotspot.

The caller-local path is an intentional code-size tradeoff. The complete
zero-import module grows from 359,760 to 366,313 bytes and the frontier from
818,241 to 830,433 bytes, while the 500 final functions, 630 source functions,
830 resident helpers, imports, exports, output bytes, and flat 9,237,304-byte
frontier remain unchanged. The same rewrite grows the reviewed Level-1
complete module from 193,150 to 198,424 bytes without changing its base module,
declaration/helper inventories, imports, or exports. Two independent
diagnostics-off campaigns of 32
order-balanced fresh-process pairs give a combined -0.350 ms paired median,
median ratio 0.990802 (about -0.92%), and 43/64 wins. Both invocation-order
buckets improve. Treat this as a modest generic runtime win, not an algorithmic
compression improvement.

Checked releases inside resident Array, ByteArray, String, and Nat helpers now
reuse the same caller-local scalar/erased-zero gate as compiler-generated
`lean_dec` wrappers. Typed `.object` values remain direct heap decrements;
`.tobject` values enter `fir_dec_once` only when they are actual heap
references. The stable helper signature and its recursive body are unchanged,
so this is a caller-shape optimization rather than a new release ABI.

On one steady 256-KiB seeded-random level-6 call, exact instrumentation reduces
dynamic `fir_dec_once` entries from 1,222,005 to 169,608. Tagged no-op entries
fall from 1,195,723 to 143,326; the retained tagged calls are chiefly the still
generic recursive container-release path. Two exact-artifact profiles move the
helper's median normalized Wasm-self share from 4.16% to 1.81% without changing
the output digest or flat 9,237,304-byte frontier. Sixteen unprofiled,
order-balanced AB/BA rounds with fresh instances move median steady call time
from 33.097 ms to 30.979 ms; every round improves and the paired median is
-2.096 ms (-6.38%).

The inline gates trade a small amount of code for the avoided cold-helper
entries: the complete zero-import module grows from 366,313 to 367,634 bytes
(+1,321, 0.36%) and the frontier from 830,433 to 832,753 bytes. The base module,
500 final functions, 630 source functions, 830 resident helpers, imports,
exports, compressed bytes, and ownership frontier are unchanged.
The same deterministic code-shape change grows the stored-block artifact from
12,418 to 12,444 bytes and the Level-1 artifact from 198,424 to 199,468 bytes;
their base modules and reviewed closure inventories remain unchanged.

The remaining compiler-generated `fir_release_0` boundary is a distinct
code-placement problem. On the exact 367,634-byte artifact above, a six-run
bound V8 profile places its median normalized Wasm-self share at 1.61% and
`fir_dec_once` at 1.46%. Exact copied-WAT instrumentation counts 11,196,054
wrapper entries on one steady 256-KiB level-6 call. Only 8,989 enter
`fir_dec_once`; 11,187,065 (99.92%) return from the scalar/erased-zero gate.
The forwarded roots comprise 7,855 shared references, 1,050 terminal
references, and 84 persistent references. Instrumentation preserves the exact
compressed output and memory observations through first, warmup, eight steady
calls, and all ten compression levels.

The dynamic traffic is highly concentrated even though the final module has
4,369 static calls across 149 functions. `Zip.Native.Deflate.lzMatchP`
contributes 8,878,038 entries per call, `chainWalkPackedUBelow._redArg`
1,197,396, and `tokenFreqsPTA` 1,048,426; together they account for 99.36%.
The first function is 31,857 bytes, far beyond V8's default 5,000-node Wasm
inlining budget. A diagnostic run with V8 Wasm inlining disabled widens the
advantage of caller-local gates, confirming that ordinary engine inlining
masks part, but not all, of this boundary cost.

A copied-final-WAT ceiling inlined the checked gate at 4,347 of 4,369 sites.
After applying the same final optimizer to both sides, it grows the module
from 365,803 to 432,338 bytes (+18.2%). Thirty-two diagnostics-off AB/BA pairs
improve in 29 rounds, with a 0.8733 paired median ratio (about 12.7% faster).
That global shape is not accepted because its code-size cost is disproportionate.
A second, explicitly diagnostic profile-guided ceiling gates only the three
dominant functions: 599 sites, 374,918 bytes (+2.49%), 29/32 improving pairs,
and a 0.8655 paired median ratio (about 13.5% faster). This establishes that
the opportunity is concentrated; it is not permission to add a declaration
allowlist or a lean-zip-specific rewrite. A production successor needs a
generic hot-call-site/code-placement policy, or a source-level upstream-shaped
candidate whose post-optimizer size is materially smaller.

Two generic placement experiments were subsequently rejected. To avoid the
known repeated-capture code-shape variation, both start from the exact W7-1
pre-optimizer frontier; its unmodified runtime link reproduces the canonical
367,634-byte module byte for byte. A pre-optimizer source-body-size policy is
cheap (the 100,000-character threshold adds 803 bytes), but a named final
profile shows that Binaryen later recreates the dominant `lzMatchP ->
fir_release_0` edge. The policy therefore acts at the wrong phase. Applying the
same generic policy to already optimized functions reaches the edge: a
1,000,000-character threshold selects two functions and rewrites 1,898 sites.
Against a paired disassembly/reassembly control it adds 28,530 bytes (+7.6%)
and sixteen warmed AB/BA pairs have a 0.8954 paired median ratio (about 10.5%
faster, 11/16 wins); both order buckets improve. Two named profiles reduce the
wrapper's median Wasm-self share from 1.81% to 0.43%. The size cost rejects this
otherwise successful mechanism.

Binaryen's native `--always-inline-max-function-size` knob does not supply the
missing selective policy. Threshold eight adds 8,047 bytes (+2.19%) and passes
the repeated-call and levels 1--10 semantic comparison, but sixteen warmed
AB/BA pairs are neutral: paired ratio 0.9962, 9/16 wins, with the two order
buckets disagreeing (0.9823 versus 1.0370). Thresholds four through six screen
neutral, while ten regresses. The next production experiment should eliminate
releases using representation/ownership facts, or use an explicit generic
profile-guided placement mechanism; neither static body size nor a global
inliner threshold is justified by this evidence.

The first representation-aware release slice preserves the exact ABI kind of
compiler locals through resident release linking. A one-capture census of the
raw closure found 4,865 static decrement sites: 4,526 `tobject`, 337 `object`,
and two `tagged`. Of these, 45 checked `object` sites can select the existing
unchecked decrement operation and the two checked `tagged` sites are proven
no-ops. All mixed `tobject` sites remain checked. The transformation is generic,
matches only the compiler-produced adjacent `localGet`/decrement shape, and
recurses through blocks, loops, and branches; every other instruction sequence
is retained unchanged.

The resulting zero-import raw module is 367,442 bytes versus the preceding
367,634-byte package and retains 500 functions, 225 Lean-source functions, 275
resident helpers, the public exports, output bytes, and the flat ownership
frontier. Its 50-way native/Wasm/inflate differential and persistent-cache plus
scratch-reclamation checks pass. Sixteen order-balanced fresh-process pairs are
neutral (paired median ratio 1.0074, 7/16 improving), so this slice makes no
runtime-performance claim. The comparison also crosses the already documented
final-LCNF recapture code-shape boundary; only same-capture evidence could
attribute such a small timing change to this rewrite.

An exact copied-final-WAT operand probe then classified every dynamic
`fir_release_0` argument without changing the release operation itself. The
diagnostic reserved a disjoint counter region below the transferred heap,
checked byte-identical compression and identical frontier observations against
an uninstrumented reassembly, and retained the production module identity
`9a23c8db...dac42a` as its source. On one warm steady 256-KiB seeded-random
level-6 call, 11,187,065 of 11,196,054 wrapper arguments are tagged immediates
(99.9197%) and 8,989 are heap references. Of 413 active final-Wasm call sites,
374 observe only tagged values, 36 only heap references, and three observe both;
the genuinely mixed sites are List/Huffman element projections and contribute
only 1,883 calls (0.0168%). A second 100-call sweep over the five raw-smoke
inputs, levels 1--10, and cold plus warm calls activates 924 sites but finds the
same three mixed sites. Both diagnostics have zero erased-zero arguments.

This is workload evidence, not permission to change the remaining `tobject`
locals to `tagged`. Many hot operands are `Nat` values: they stay immediate for
the measured input bounds but Lean permits their boxed representation. Removing
their checked release therefore needs a proved range/provenance fact, not a
profile-derived type. The final optimizer does expose two exact odd-constant
release sites accounting for 262,002 steady calls (2.34%); eliminating such
constants is semantically exact, but that bounded gain alone does not justify a
new custom post-link publication stage. The next generic compiler experiment
should test whether existing typed scalar/range information can survive to
release sites, while retaining the three genuinely mixed projection sites and
all unproved `Nat` paths.

The next slice adds that generic transfer surface to typed call-site rewrites.
A provider may state a conditional result refinement over the original local
operand kinds; the linker applies it only to an immediately assigned compiler
local with no other definition, iterating to a fixed point for eligible call
chains. `Nat.sub` supplies the first rule: `left - right ≤ left`, so a tagged
left operand implies a tagged result for every representation of `right`.
Unrecognized instruction shapes, multiply assigned locals, and calls with a
coarse left operand retain `tobject`. Because persistent planning installs
release helpers before later big-numeric helpers, the linker propagates the
complete policy's reviewed result facts once before any ownership operation is
materialized; group-local propagation remains as a conservative second pass.

On the raw lean-zip closure this changes the symbolic `fir_release_0` census
from 4,478 to 4,329 sites. The existing exact-representation specialization
accounts for 47 sites and the new `Nat.sub` transfer removes another 102;
all 109 unproved `Nat.sub`-derived sites remain `tobject`. The final zero-import
module shrinks from 367,442 to 366,723 bytes (719 bytes), and the pre-optimizer
frontier shrinks from 832,339 to 831,737 bytes. The candidate hash is
`da1e7209afa8995f170d79c461fb253d39b3b4e61a64942f044115e6ce187696`.
The 50-way native/Wasm/inflate differential and persistent-cache plus scratch
reclamation gate pass unchanged.

Sixteen fresh-process, order-balanced 256-KiB level-6 pairs report baseline
35.491 ms (MAD 0.386) and candidate 34.835 ms (MAD 0.314), with a 0.9801 paired
median ratio, 15/16 improving pairs, and agreeing order buckets (0.9811 and
0.9801). This is a useful roughly 2% screen, not an attributable performance
claim: the comparison uses separately captured final-LCNF artifacts and crosses
the documented recapture code-shape boundary. The exact accepted claims are
the semantic range transfer, removed symbolic releases, smaller artifact, and
green differential/ownership gates.

`Nat.land` provides the next reviewed range transfer: `left &&& right ≤ right`.
When the right operand is statically `tagged`, the result therefore fits the
complete immediate payload range even if the left operand is heap-backed. The
resident arbitrary-precision fallback constructs its bounded result through
`fir_numeric_make_natural`, so the physical result is canonical tagged form as
well. A provider guard retains that exact operand condition, and the external
engine fixture covers the mixed heap-left/tagged-right fallback explicitly.

The raw closure has 34 eligible `Nat.land` source call sites accounting for 52
checked result releases; the two calls with a coarse right operand retain their
two checks. The symbolic `fir_release_0` census consequently falls from 4,329
to 4,277. Against the current Float32-integrated baseline, the pre-optimizer
frontier falls from 831,806 to 831,513 bytes and the final zero-import module
from 366,765 to 366,523 bytes. Its SHA-256 is
`1a225c0d074cef5cbaa1f49a498e469d9037d5ffa05910ce62dc67a9a0a20eec`;
all 50 native/Wasm/inflate comparisons and persistent-cache plus scratch
reclamation checks pass unchanged.

Sixteen fresh-process, order-balanced 256-KiB level-6 pairs gave a 0.9362
paired median ratio with 10/16 improving, but high dispersion and materially
different baseline-first and candidate-first buckets (0.8562 versus 0.9531).
This separately captured screen is inconclusive and makes no attributable
runtime-performance claim. The accepted evidence is the semantic bound, exact
52-site ownership reduction, smaller artifact, and green differential gate.

The next range slice keeps scalar bounds separate from ABI kinds. A generic
`fitsTaggedNat` fact may cross an ABI-preserving operation without claiming
that its scalar result has an object ABI: a tagged input to `USize.ofNat`
produces a `.usize` carrying that fact, and `USize.toNat` consumes the fact to
refine its object result to `.tagged`. The same fixed-point analysis still
requires immediately assigned compiler locals, a single reviewed definition,
and exact provider conditions. Coarse or multiply assigned values retain their
ordinary ABI kind and checked release.

The raw closure contains 378 direct `USize.ofNat`/`USize.toNat` chains whose
results account for 380 checked releases. Exactly 114 begin with a statically
tagged Nat (all from the already reviewed tagged `ByteArray.size` surface), so
only those 114 releases disappear; the other 266 remain conservative. The
symbolic `fir_release_0` census falls from 4,277 to 4,163. The pre-optimizer
frontier decreases from 831,513 to 830,857 bytes and the final zero-import
module from 366,523 to 365,682 bytes. Its SHA-256 is
`3780a49aaf5027c3ca33aa055e9575ef0c5e0fa1a15573a02fffb916515dce22`;
all 50 native/Wasm/inflate comparisons and persistent-cache plus scratch
reclamation checks pass unchanged.

Two independent diagnostics-off campaigns total 32 order-balanced,
fresh-process 256-KiB level-6 pairs. Baseline and candidate medians are 34.264
ms (MAD 1.318) and 31.936 ms (MAD 0.417); the paired median is -2.249 ms with a
0.9343 ratio, 24/32 improving pairs, and agreeing baseline-first/candidate-first
ratios of 0.9368 and 0.9325. This is strong directional evidence for removing
the round-trip release traffic, but not yet an attributable headline: the two
artifacts were produced by separate source captures and cross the documented
final-LCNF recapture boundary. Exact accepted claims remain the generic fact
transfer, 114-site reduction, smaller module, and green semantic/ownership
gates.

For performance characterization, `array-scaling-bench.mjs` runs one
diagnostics-free, warmed level-6 workload and emits raw execute samples, input
and output hashes, and the post-rewind frontier. It is a measurement seed, not
an absolute-time test: compare identified baseline and candidate packages with
an order-balanced harness and retain the raw process rows. The `random` family
exercises the Array-heavy matcher path at caller-selected sizes; `structured`
retains the deterministic mixed-text control.
