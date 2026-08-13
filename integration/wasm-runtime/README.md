# Shared Wasm external runtime

This directory closes standard Lean external declarations left by FIR's
resident linker. It is application-independent: source capture retains known
opaque declarations, resident helpers consume the subset they implement, and
`link-runtime.mjs` merges the remaining checked `lean.extern` imports with the
separately compiled runtime while preserving exactly the frontier exports.

`math-runtime.c` implements the Lean 4.33 Float/libm boundary and reads FIR's
module-owned Lean object representation directly. `Float.ofNat` and
`Float.ofScientific` currently accept canonical Naturals with at most one
64-bit limb; `Float.ofScientific` accepts decimal exponents through 20. Inputs
outside that declared runtime capability trap rather than invoking a host
fallback.

`contract.mjs` is the single packaging-side description of this runtime. In
particular, it declares a 65536-byte low-memory reservation for the compiled C
data and stack. Complete-package metadata carries that value, and adapters must
advance a fresh FIR heap frontier to it before allocating Lean values.

The linker discovers the intended public surface from the frontier module. It
normalizes Emscripten's imported-memory maximum, links by exact external name
and Wasm signature, and preserves the frontier's multivalue feature. A binary
`wasm-metadce` graph roots the exact frontier `(name, kind)` export inventory;
this removes runtime-only exports without a size-amplifying WAT roundtrip. The
linker rejects residual imports and requires both the private and optimized
complete modules to preserve the frontier export inventory exactly.
