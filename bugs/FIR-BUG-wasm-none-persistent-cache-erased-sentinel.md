---
id: FIR-BUG-wasm-none-persistent-cache-erased-sentinel
status: fixed
classification: compiler
lean-toolchain: leanprover/lean4:v4.34.0-rc2
lean-revision: 6a10ac8c22beadecabdbb0919c2b50214762f91d
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-09-01
reproduction: integration/vbp-verso-viewer/check.sh
regression: integration/talos/artifact/resident-cache-client.mjs
---

# Summary

The Wasm-resident persistent-cache marker traps when a closure descriptor
contains an erased capture. Final LCNF stores that capture as canonical word
zero; FIR's concrete persistence semantics treats zero as a sentinel no-op,
but `fir_mark_persistent` attempts to interpret it as a heap address.

## Minimal reproduction

Compile the exact VBP Verso viewer package after admitting Lean 4.34's
`ExplicitBoxing` `tagged -> void` wrapper shape. Synchronous component entry
then reaches cache publication for `Except.instMonad._closed_9` and traps in
`fir_mark_persistent` through resident helper `fir_cache_set_1259`.

The cached `Monad` graph contains `Except.instMonad._closed_8`, whose final
LCNF body is:

```text
let _x.1 := pap Except.bind erased
return _x.1
```

The partial application has descriptor `[erased]`; its only physical capture
is canonical word zero.

## Exact commands

From `integration/talos/artifact`, build and execute the resident-cache
artifact:

```sh
lake build fir-wasm-artifact
.lake/build/bin/fir-wasm-artifact resident-cache _build/resident-cache.wasm
node run-resident-cache.mjs _build/resident-cache.wasm
```

The original package-level reproducer is
`integration/vbp-verso-viewer/check.sh` on the explicit-boxing integration
candidate recorded in mailbox event `ROOT-W7-20260901-006`.

## Expected semantics

Recursive persistence must treat immediate values and the canonical erased
sentinel as exact no-ops. This is already the behavior of
`Fir.Wasm.Concrete.markPersistentFuel`, whose `Word32.classify` branch accepts
both `.immediate` and `.sentinel` without reading a heap header.

The containing closure and constructor graph should become persistent, while
the erased capture remains unchanged.

## Actual behavior

`ResidentCache.markPersistentFunction` returns early for odd tagged words, but
does not recognize word zero. It proceeds to the below-heap-base check and
traps. The resident-cache client additionally ratchets this stale behavior by
expecting `resident_cache_set(0)` to trap.

## Proof or differential evidence

`Fir.Wasm.Concrete.markPersistentFuel` already classifies canonical zero as a
sentinel and returns without changing the heap. The corrected standalone
resident-cache artifact publishes both a zero root and a closure containing an
erased zero capture; the former returns zero and the latter marks the enclosing
root persistent without trapping. The full native/LCNF/V8 differential matrix
continues to compare 721 cases successfully across all three backend pairs.

## Semantic impact

Any eliminated or persistent lazy cache whose reachable closure graph captures
an erased or void lane can trap during publication. The issue is generic and
was merely hidden behind the earlier closure-dispatch omission.

## Classification and triage

This is a W7 resident-runtime mismatch against the existing concrete runtime,
not a package-specific adapter problem. Repair `fir_mark_persistent` to accept
canonical zero before attempting heap validation, retain traps for other
misaligned or below-heap addresses, and replace the stale zero-trap test with
root and nested-erased-capture no-op coverage.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

`ResidentCache.markPersistentFunction` now returns immediately for canonical
word zero before applying heap-base and alignment validation. This matches the
existing concrete `Word32.sentinel` persistence semantics without admitting
any other invalid even word.

The resident-cache artifact uses a second closure descriptor containing one
erased capture. Its Node regression publishes that closure with physical zero
in the captured slot and verifies the containing root becomes persistent. The
former zero-trap expectation is replaced by an exact zero no-op assertion;
misaligned, noncanonical-dead, unknown-descriptor, descriptor-count, and field-
limit cases continue to trap.
