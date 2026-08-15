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

Create clean source views, then run the closure probe:

```sh
git -C /path/to/lean-zip worktree add --detach /tmp/fir-lean-zip-273d \
  273d0d6cd9cab77c7f3489b0b0b1f6e543315d21
git -C /path/to/zipCommon worktree add --detach /tmp/fir-zip-common-4425 \
  4425bab1f9522307d77e8d485bc536149ba31c36

lake --keep-toolchain --reconfigure \
  -KleanZipRoot=/tmp/fir-lean-zip-273d \
  -KzipCommonRoot=/tmp/fir-zip-common-4425 \
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
LEAN_ZIP_ROOT=/tmp/fir-lean-zip-273d \
ZIP_COMMON_ROOT=/tmp/fir-zip-common-4425 \
FIR_BROWSER=google-chrome \
./check.sh
```

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
branch. `FIR_RAW_PACKAGE_PREVIEW_DIR=/tmp/PATH` selects an explicit preview
destination and suppresses canonical publication; dirty previews additionally
require the existing `FIR_ALLOW_DIRTY_PACKAGE=1` acknowledgment.

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

The raw producer retains exactly `Float.ofNat`, `Float.ofScientific`, and
`Float.log2` at its reviewed frontier and closes them with the pinned standard
math runtime. Its published module has zero imports. The browser adapter
reserves `STANDARD_MATH_RUNTIME_RESERVED_MEMORY_BYTES` before lazy-cache
publication or Lean allocation, and the package records both frontier and
complete identities plus the runtime source, contract, and Emscripten identity.

The exact post-isolation raw closure is ratcheted in
`raw-closure-contract.json`: 662 captured declarations, 128 reviewed
externals, 534 retained source functions, 2,598 resident helpers, and 3,132
complete functions. In addition to counts and Wasm byte lengths, the contract
pins SHA-256 digests of the ordered external, source-function, resident-helper,
and complete-function inventories. This prevents a same-count closure change
from passing the package gate without review.

The same contract ratchets the final optimized artifact at 2,172 functions and
zero function imports, with 354 surviving Lean-source functions, 1,812
resident helpers, and six optimizer-or-linked-runtime functions. The function
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

For performance characterization, `array-scaling-bench.mjs` runs one
diagnostics-free, warmed level-6 workload and emits raw execute samples, input
and output hashes, and the post-rewind frontier. It is a measurement seed, not
an absolute-time test: compare identified baseline and candidate packages with
an order-balanced harness and retain the raw process rows. The `random` family
exercises the Array-heavy matcher path at caller-selected sizes; `structured`
retains the deterministic mixed-text control.
