# Shared Wasm external runtime

This directory closes standard Lean external declarations left by FIR's
resident linker. It is application-independent: source capture retains known
opaque declarations, resident helpers consume the subset they implement, and
`link-runtime.mjs` merges the remaining checked `lean.extern` imports with the
separately compiled runtime while preserving exactly the frontier exports.

`math-runtime.c` implements the Lean 4.33 libm boundary and reads FIR's
module-owned Lean object representation directly. Its version-1 compatibility
surface still contains the historical `Float.ofNat` and `Float.ofScientific`
providers for older frontier packages; those providers accept Naturals with at
most one 64-bit limb and decimal exponents through 20, trapping outside that
declared capability.

Generic closed applications no longer retain those two declarations at the C
frontier. `Fir.Wasm.Emit.ResidentFloatSource` compiles Lean's exposed
`Float.ofNat` and `Float.ofScientific` definitions through LCNF, and resident
Nat/Int/BitVec/Float helpers close their complete arbitrary-precision model
path. The Talos `source-float-conversions` artifact is zero-import and checks
fast/slow paths, subnormals, overflow, arbitrary Naturals, and exact result
bits against a native Lean oracle. The legacy contract remains versioned here
until packages that still consume it are regenerated.

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
