---
id: FIR-BUG-impure-none-byte-array-mk-validation-external
status: candidate
classification: validation-harness
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: impure
pass: none
discovered-by: differential-test
first-seen: 2026-08-23
reproduction: bugs/FIR-BUG-impure-none-byte-array-mk-validation-external.md
regression: none
---

# Summary

Compiler-produced construction of a `ByteArray` from an ordinary
`Array UInt8` calls `ByteArray.mk`, but the LCNF validation interpreter does
not implement or allowlist that runtime external.

## Minimal reproduction

Build an Array only through already modeled operations, then wrap it as a
ByteArray in a nullary declaration:

```lean
@[noinline]
def cachedSharedByteArrayOwner : CachedSharedByteArrayOwner :=
  let data : Array UInt8 :=
    ((((Array.emptyWithCapacity 4).push 0).push 127).push 128).push 255
  let child : ByteArray := ⟨data⟩
  { left := child, right := child, payload := 18446744073709551616 }
```

## Exact commands

```sh
python3 scripts/validate_interpreters.py \
  --plan validation-plans/native-lcnf.json \
  --out-dir _build/validation-e3c-explicit \
  --case cached-shared-byte-array-dag-reuse-skipped \
  --case cached-shared-byte-array-dag-reuse-taken
```

## Expected semantics

Native Lean builds `[0, 127, 128, 255]`, publishes the repeated-child owner
in the nullary cache, preserves an outside alias, and returns either the
unchanged child or the copy-on-write update `[0, 127, 255, 255]`. A second
cache read returns the original complete graph.

## Actual behavior

Native Lean returns the expected complete graph on both paths. LCNF executes
`Array.emptyWithCapacity` and four `Array.push` operations, then faults with
`externalFailure ByteArray.mk "external is not in the validation allowlist"`.
No cache publication, owner projection, or `ByteArray.set!` mutation executes.

## Proof or differential evidence

The skipped path's exact dispatched prefix is
`Array.emptyWithCapacity,Array.push,Array.push,Array.push,Array.push,ByteArray.mk`.
The reported form prefix reaches the `extern` for `ByteArray.mk` and lacks
the required cache, projection, branch, construction, and completion suffix.
This is independent of
`FIR-BUG-impure-none-array-mkempty-validation-external`: the reproducer
deliberately avoids Array literal syntax and reaches the later wrapper
operation.

## Semantic impact

The validation interpreter cannot execute ordinary source construction of a
ByteArray from an already valid Array. This blocks native-oracle coverage of
nullary cached ByteArray initialization and any ownership path that constructs
the wrapper inside the compiled source instead of materializing it as a
validation input.

## Classification and triage

This is provisionally a validation-harness coverage gap. Final LCNF names
`ByteArray.mk` by design, and the resident Wasm runtime already has a helper
and ownership tests for the operation. The LCNF validation implementation and
semantic Wasm external registry need one shared ownership contract before the
external is admitted.

## Workaround

Materialize ByteArray inputs through the existing validation schema when the
fixture does not test construction. No faithful workaround exists for a
nullary cached ByteArray whose value must be created inside compiled source.

## Upstream tracking

none

## Resolution and regression

Unresolved. After both validation candidates implement the operation, restore
a source-built ByteArray case that pins construction, cache publication,
copy-on-write mutation, and the second cache hit against native Lean.
