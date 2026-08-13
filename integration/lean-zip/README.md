# FIR-native lean-zip bring-up

This integration compiles the real Lean 4.32-compatible entries

```lean
Zip.Wasm.compressStored : ByteArray → ByteArray
Zip.Wasm.compressLevel1 : ByteArray → ByteArray
```

from lean-zip commit `30737b4e2ebfd0fc889f0b2e265aae0635d668a1`.
The stored entry is the minimal boundary control. Level-1 is the first
production matcher/emitter slice. FIR reads clean source checkouts and writes
every build product locally; it never consumes lean-zip's `.lake` products.

This revision uses Lean's legacy module syntax. FIR therefore captures its real
declarations through the generic single-unit final-LCNF path; module-wise replay
is reserved for sources containing `module` / `public section` boundaries.

Create clean source views, then run the closure probe:

```sh
git -C /path/to/lean-zip worktree add --detach /tmp/fir-lean-zip-30737 \
  30737b4e2ebfd0fc889f0b2e265aae0635d668a1
git -C /path/to/zipCommon worktree add --detach /tmp/fir-zip-common-4425 \
  4425bab1f9522307d77e8d485bc536149ba31c36

lake --keep-toolchain --reconfigure \
  -KleanZipRoot=/tmp/fir-lean-zip-30737 \
  -KzipCommonRoot=/tmp/fir-zip-common-4425 \
  build LeanZipFir.Compile
lake --keep-toolchain env lean Probe.lean
lake --keep-toolchain env lean ProbeLevel1.lean
```

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
LEAN_ZIP_ROOT=/tmp/fir-lean-zip-30737 \
ZIP_COMMON_ROOT=/tmp/fir-zip-common-4425 \
FIR_BROWSER=google-chrome \
./check.sh
```

Immutable packages are under `_build/lean-zip-stored-packages/` and
`_build/lean-zip-level1-packages/`. Their atomic canonical pointers are
`_build/lean-zip-stored-current` and `_build/lean-zip-level1-current`. Each
package contains seven checksummed files and can run `node smoke.mjs` without
the FIR or lean-zip source trees.

The browser/Node API is:

```js
const adapter = await createLeanZipStoredAdapter({ bytes, descriptor });
const { bytes: compressed, timings, memory } =
  adapter.compressStored(inputBytes);

const level1 = await createLeanZipLevel1Adapter({ bytes, descriptor });
const level1Result = level1.compressLevel1(inputBytes);
```

Every call uses a scratch checkpoint: the adapter copies the result, rewinds
the module-owned arena even on failure, and exposes no Wasm address.

Level-1 additionally preserves Lean's compiler-generated lazy constants. The
adapter calls the module's idempotent `fir_initialize_persistent_caches` entry
once at instance creation, retains the recursively persistent cache graphs
below the resulting frontier, and uses that frontier as the lower bound for
all later scratch rewinds. `adapter.initialization` reports the initial and
checkpoint frontiers plus initialization/idempotence timings; per-call timing
continues to cover only encoding, execution, decoding, and total call time.

Both public wrappers reuse the same versioned ByteArray encoder, decoder,
module validator, timing, and scratch-ownership implementation. Level-1 has
zero imports and is suitable for correctness testing in Node and browsers. It
is not yet a performance artifact: generic resident Nat and closure execution
remain allocation-heavy, and `BUILD.json` records that limitation explicitly.
