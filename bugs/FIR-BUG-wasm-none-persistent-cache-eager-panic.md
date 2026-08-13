---
id: FIR-BUG-wasm-none-persistent-cache-eager-panic
status: candidate
classification: compiler
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: source-closure-test
first-seen: 2026-08-13
reproduction: integration/lean-zip/raw-smoke.mjs
regression: Fir/Wasm/Emit/ResidentCache.lean
---

# Summary

The persistent-cache initializer eagerly forces every compiler lazy constant.
A valid application closure may contain an error-path constant whose evaluation
panics, so instance initialization can trap even when the public call would
never reach that path.

## Minimal reproduction

Compile and link `Zip.Wasm.compressRaw`, reserve the standard runtime's first
65,536 bytes, then call `fir_initialize_persistent_caches` before allocating an
input. The initializer forces
`Zip.Native.Deflate.l7RegionUniquePermille._lam_2._closed_0`, whose body calls
`outOfBounds._redArg` and then `panicCore`.

## Exact commands

From `integration/lean-zip`, run:

```text
FIR_ALLOW_DIRTY_PACKAGE=1 \
FIR_RAW_PACKAGE_PREVIEW_DIR=/tmp/lean-zip-raw-preview \
node package-raw.mjs
```

The producer reaches `raw-smoke.mjs` after deterministic frontier and complete
generation, then traps in the exported persistent initializer.

## Expected semantics

Opting into persistent cache storage must not change which lazy constants are
evaluated before a public entry call. In particular, a panic-only fallback that
is unreachable for valid input must remain unforced.

## Actual behavior

`persistentCacheInitializerFunction` iterates over every
`module.initializers` entry and emits an unconditional cache miss for each
uninitialized global. The raw module grows its frontier from 65,536 to
5,738,472 bytes before trapping. Repeating with a 65,528-byte frontier traps at
the same source stack, so this is not external-runtime reservation overlap.

The unoptimized merged stack maps exactly to:

```text
fir_initialize_persistent_caches
Zip.Native.Deflate.l7RegionUniquePermille._lam_2._closed_0
outOfBounds._redArg
fir_ext_panicCore
```

## Proof or differential evidence

The native oracle accepts the smoke inputs. The FIR raw frontier has zero
runtime operations and only the three reviewed math imports; its linked module
has zero imports and exact exports. The trap occurs before the adapter encodes
the first input or invokes `Zip.Wasm.compressRaw`.

## Semantic impact

Eager cache population changes Lean's lazy-constant evaluation behavior and
can make otherwise valid programs fail at instance creation. A package-specific
initializer denylist would hide the semantic problem and is not acceptable.

## Classification and triage

This is generic resident-cache generation work. Preserve a rewind-safe
persistent-cache region without unconditionally evaluating panic-producing or
effectful lazy constants. The regression should include one ordinary cached
object that survives scratch rewind and one unreachable panic-only lazy
constant that remains unforced during initialization.

## Workaround

None compatible with the current scratch-rewind and global-cache ownership
contract.

## Upstream tracking

none

## Resolution and regression

Pending.
