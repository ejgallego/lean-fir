# Shared Wasm external runtime

This directory closes standard Lean external declarations left by FIR's
resident linker. It is application-independent: source capture retains known
opaque declarations, resident helpers consume the subset they implement, and
`link-runtime.mjs` merges the remaining checked `lean.extern` imports with the
separately compiled runtime while preserving exactly the frontier exports.

`libm-runtime.c` is the current generic implementation of Lean's six genuine
platform-libm externals. It accepts and returns only binary64 lanes. Ordinary
finite results follow the linked Wasm libc implementation and may differ from
another platform's libc by a few ULPs; special-value behavior and ABI bit
transport are checked explicitly. This is the same portability boundary Lean
upstream chooses for these opaque declarations.

`math-runtime.c` implements the older Lean 4.33 math boundary and reads FIR's
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
bits against a native Lean oracle. Illuminate's full-action and selection
players consume this source path directly; the legacy contract remains
versioned here only for packages that have not yet been regenerated.

`contract.mjs` describes the separately compiled C runtime. In particular, it
declares a 65536-byte low-memory reservation for the compiled C data and stack.
Only packages that actually link that provider carry the reservation and
advance their FIR heap frontier past it.

Provider-free resident modules use `optimize-closed-module.mjs`. It accepts an
already import-free module, applies the same closed-world Binaryen cleanup used
after external linking, and rejects any import or export-surface change. It
uses only its caller-supplied input and output paths; it creates no temporary
directory.

The linker discovers the intended public surface from the frontier module. It
normalizes Emscripten's imported-memory maximum, links by exact external name
and Wasm signature, and preserves the frontier's multivalue feature. A binary
`wasm-metadce` graph roots the exact frontier `(name, kind)` export inventory;
this removes runtime-only exports without a size-amplifying WAT roundtrip. The
linker rejects residual imports and requires both the private and optimized
complete modules to preserve the frontier export inventory exactly.
