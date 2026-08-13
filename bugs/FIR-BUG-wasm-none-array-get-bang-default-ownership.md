---
id: FIR-BUG-wasm-none-array-get-bang-default-ownership
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-08-13
reproduction: integration/talos/artifact/resident-array-client.mjs
regression: integration/talos/artifact/resident-array-client.mjs
---

# Summary

The resident implementations of both `Array.get!Internal` and
`Array.get!InternalBorrowed` return the borrowed `Inhabited` default directly
when the index is out of bounds.

## Minimal reproduction

Allocate an ordinary default object with reference count one and an empty
resident Array. Call either resident `get!` helper with index zero. FIR returns
the default address while leaving its reference count at one.

## Exact commands

```sh
cd integration/talos/artifact
lake exe fir-wasm-artifact resident-arrays _build/resident-arrays.wasm
node run-resident-arrays.mjs _build/resident-arrays.wasm
```

## Expected semantics

Lean 4.33's `lean_array_get` and `lean_array_get_borrowed` both increment the
borrowed default before passing it to the consuming `lean_array_get_panic`.
The returned fallback therefore owns one additional reference, even for the
compiler-only borrowed helper.

## Actual behavior

`ResidentArray.getBody` returns `defaultParam` directly on the default branch
for both helpers.

## Proof or differential evidence

The exact toolchain `include/lean/lean.h` calls `lean_inc(def_val)` in both
out-of-bounds branches. Lean's LCNF explicit-RC pass additionally records that
a continued result may be derived from either the Array or the `Inhabited`
argument.

## Semantic impact

If the caller releases the returned fallback according to its dynamic owned
path, FIR can retire an object still owned by the `Inhabited` parent. More
generally, FIR's reference-count state diverges from native Lean immediately
after a recoverable out-of-bounds access.

## Classification and triage

This is a generic resident Array ownership discrepancy. It is independent of
application adapters and applies to any compiled `a[i]!` whose panic handler
allows execution to continue.

## Workaround

None. Do not retain defaults at a source or JavaScript boundary to compensate.

## Upstream tracking

none

## Resolution and regression

The default branch now calls the resident increment helper before returning
the fallback. This mirrors the exact upstream `lean_inc(def_val)` operation
for both externs while remaining a no-op for immediate defaults.

The resident Array artifact now exports both `get!` variants for direct
external-engine coverage. The client checks owned and borrowed fallback
retention, releases the dynamic fallback reference, and separately ratchets
their distinct in-bounds behavior: owned lookup increments the element while
borrowed lookup does not.
