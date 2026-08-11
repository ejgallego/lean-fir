# FIR-native lean-zip bring-up

This integration compiles the real Lean 4.32-compatible entry

```lean
Zip.Wasm.compressStored : ByteArray → ByteArray
```

from lean-zip commit `30737b4e2ebfd0fc889f0b2e265aae0635d668a1`.
It is the first vertical slice toward the production
`Zip.Wasm.compressRaw : ByteArray → UInt8 → ByteArray` artifact. FIR reads
clean source checkouts and writes every build product locally; it never consumes
lean-zip's `.lake` products.

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

The immutable packages are under `_build/lean-zip-stored-packages/`, and the
atomic canonical pointer is `_build/lean-zip-stored-current`. A consumer needs
only the six files in that directory and can run `node smoke.mjs`.

The browser/Node API is:

```js
const adapter = await createLeanZipStoredAdapter({ bytes, descriptor });
const { bytes: compressed, timings, memory } =
  adapter.compressStored(inputBytes);
```

Every call uses a scratch checkpoint: the adapter copies the result, rewinds
the module-owned arena even on failure, and exposes no Wasm address.
