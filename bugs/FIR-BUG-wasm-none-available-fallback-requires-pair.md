---
id: FIR-BUG-wasm-none-available-fallback-requires-pair
status: fixed
classification: compiler
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: source-closure-test
first-seen: 2026-08-12
reproduction: integration/lean-zip/ProbeLevel1.lean
regression: Fir/Wasm/Emit/ResidentFallback.lean
---

# Summary

The capability-sensitive fallback linker invokes the strict historical
prettyM pair linker when either fallback declaration is present. Generic
source closures retaining only `panicCore` therefore fail while asking for the
absent `instInhabitedOfMonad._redArg` declaration.

## Minimal reproduction

Capture and lower `Zip.Wasm.compressLevel1`, then apply the generic closed
application resident policy. After closure allocation succeeds, linking stops
at `ResidentFallback.LinkError.missingExternal
instInhabitedOfMonad._redArg` even though only `panicCore` is imported.

## Exact commands

Run the `ProbeLevel1.lean` command documented by
`integration/lean-zip/README.md` and inspect
`integration/lean-zip/_build/level1-probe.json`.

## Expected semantics

`internalizeAvailable` internalizes exactly the supported fallback imports
present in a generic module. The strict `internalize` entry remains available
for prettyM's reviewed two-declaration frontier.

## Actual behavior

Presence of either declaration delegates to `internalize`, which requires one
import of both declarations and fails on a valid single-member frontier.

## Proof or differential evidence

The Level-1 capture contains 110 reviewed externals and includes `panicCore`
but not `instInhabitedOfMonad._redArg`. Compiler admission and lowering are
otherwise complete: 391 declarations and zero unsupported declarations.

## Semantic impact

Generic closed applications cannot reuse the fail-closed fallback family
unless their external closure happens to match prettyM's historical pair.

## Classification and triage

W7 resident-link selection. No fallback behavior or symbolic Wasm contract
changes; only capability-sensitive family selection was incorrectly strict.

## Workaround

None. Do not retain an unreachable declaration merely to satisfy a package
unrelated to the source closure.

## Upstream tracking

none

## Resolution and regression

`internalizeSelected` now checks, rewrites, installs, and exports exactly a
supplied fallback subset. Strict `internalize` retains the complete pair;
`internalizeAvailable` filters the current module imports. Lean regressions
cover the empty, panic-only, inhabited-only, and strict-pair frontiers. The
real Level-1 resident-link probe passes this boundary and reaches zero
remaining runtime operations.
