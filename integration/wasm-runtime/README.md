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

Generic closed applications do not retain `Float.ofNat` or
`Float.ofScientific` at the C frontier.
`Fir.Wasm.Emit.ResidentFloatSource` compiles Lean's exposed `Float.ofNat` and
`Float.ofScientific` definitions through LCNF, and resident
Nat/Int/BitVec/Float helpers close their complete arbitrary-precision model
path. The Talos `source-float-conversions` artifact is zero-import and checks
fast/slow paths, subnormals, overflow, arbitrary Naturals, and exact result
bits against a native Lean oracle. Illuminate's full-action, selection,
HitScene, and SpatialHitScene packages consume this source path directly. The
former `fir.standard-math/v1` compatibility provider has no active consumers
and has been retired.

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
