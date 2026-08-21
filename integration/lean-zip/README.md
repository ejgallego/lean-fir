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
externals, 630 retained source functions, 2,782 resident helpers, and 3,412
complete functions. In addition to counts and Wasm byte lengths, the contract
pins SHA-256 digests of the ordered external, source-function, resident-helper,
and complete-function inventories. This prevents a same-count closure change
from passing the package gate without review.

The same contract ratchets the final optimized artifact at 2,305 functions and
zero function imports, with 390 surviving Lean-source functions, 1,915
resident helpers, and no optimizer-or-linked-runtime functions. The function
index digest and sidecar digest make an index-preserving but identity-changing
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

For performance characterization, `array-scaling-bench.mjs` runs one
diagnostics-free, warmed level-6 workload and emits raw execute samples, input
and output hashes, and the post-rewind frontier. It is a measurement seed, not
an absolute-time test: compare identified baseline and candidate packages with
an order-balanced harness and retain the raw process rows. The `random` family
exercises the Array-heavy matcher path at caller-selected sizes; `structured`
retains the deterministic mixed-text control.
