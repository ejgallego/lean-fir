---
id: FIR-BUG-wasm-none-array-panic-observation
status: confirmed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: upstream-runtime-audit
first-seen: 2026-08-14
reproduction: integration/talos/artifact/resident-array-client.mjs
regression: integration/talos/artifact/resident-array-client.mjs
---

# Summary

The resident `Array.get!Internal`, `Array.get!InternalBorrowed`, and
`Array.set!` implementations preserve the upstream fallback value and
ownership behavior on an out-of-bounds index but omit the corresponding Lean
runtime panic observation.

## Minimal reproduction

Call either resident `get!` helper on an empty Array, or call resident `set!`
with an index equal to the Array size. The operation returns the retained
default or original Array as expected, but emits no equivalent of
`lean_array_get_panic` or `lean_array_set_panic`.

## Exact commands

```sh
cd integration/talos/artifact
lake exe fir-wasm-artifact resident-arrays _build/resident-arrays.wasm
node run-resident-arrays.mjs _build/resident-arrays.wasm
```

The existing client covers the fallback values and ownership state. Extend it
with the eventual versioned panic-observation surface to expose this missing
effect.

## Expected semantics

Lean 4.33's `lean_array_get` and `lean_array_get_borrowed` increment the
fallback and call `lean_array_get_panic`. `lean_array_set` calls
`lean_array_set_panic`, which consumes the replacement and returns the original
Array after reporting the bounds failure. Execution continues after both
runtime panic helpers.

## Actual behavior

`ResidentArray.getBangBody` increments and returns the default directly.
`ResidentArray.decodeSetBangIndex` releases the replacement and returns the
original Array directly. No resident observation records or reports the panic.

## Proof or differential evidence

The exact v4.33 toolchain header routes the two out-of-bounds branches through
the exported panic helpers. The resident external-engine regression confirms
the correct returned addresses and reference counts, demonstrating that only
the panic observation is absent.

## Semantic impact

Programs that observe Lean runtime panic diagnostics distinguish native Lean
from FIR even though their recovered values agree. Replacing the missing
observation with `unreachable` would also be wrong because upstream returns and
continues execution.

## Classification and triage

This is a generic resident-runtime observation gap. It is independent of the
proof-indexed Array hot path: those operations cannot reach an out-of-bounds
case in a well-typed execution. Integration must first choose a zero-import,
versioned representation of recoverable runtime panic observations.

## Workaround

None. Do not trap, silently change the returned value, or add an undocumented
host logging import.

## Upstream tracking

none

## Resolution and regression

unresolved
