---
id: FIR-BUG-wasm-none-eliminated-lazy-cache-amplification
status: confirmed
classification: compiler
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: resident-runtime-test
first-seen: 2026-08-13
reproduction: integration/lean-zip/level1-smoke.mjs
regression: Fir/Wasm/Emit/ResidentCache.lean
---

# Summary

`ResidentCache.eliminateLazyInitializers` makes every use of a compiler lazy
constant reconstruct its complete value graph in the current scratch arena.
This is safe for rewindable packages but can turn an otherwise cached
production table into repeated linear work and unbounded per-call arena
growth.

## Minimal reproduction

Compile `Zip.Wasm.compressLevel1` and compress the comparison-page 83-byte
input. Its matcher and emitter repeatedly read Lean's cached 32,769-entry
`Zip.Native.Deflate.distCodeWordBytes` table. After lazy-cache elimination,
every read calls the original table initializer again.

## Exact commands

```sh
cd integration/lean-zip
node level1-smoke.mjs
```

The focused source-side reproducer supplied by lean-zip is
`Zip.Wasm.distanceCodeCacheProbe`; repeated input bytes intentionally access
the same real production cache.

## Expected semantics

A self-contained instance-lifetime arena may initialize compiler lazy
constants once, mark every cached object graph recursively persistent, and
retain the cache roots below a stable checkpoint. Public-call input and result
scratch can then be rewound to that checkpoint without invalidating a cache.

## Actual behavior

The arena preparation transform removes every compiler cache flag/value global
and rewrites a hit/miss sequence to an unconditional initializer call followed
by persistence publication. The Level-1 profile attributes 84.9% of inclusive
time to the eliminated distance-code constant and records 935,103,808 bytes of
scratch growth for an 83-byte input before rewind.

## Proof or differential evidence

The output remains byte-equal to native DEFLATE and independently inflates,
so this is not a value mismatch. A named V8 profile attributes 56.1% of
inclusive time to rebuilding the 32,769-entry array and the leading self-time
to resident `Array.uset`, `Array.push`, and `Array.uget`. Unprofiled Chrome
execution takes about 46.7 seconds for the 83-byte input.

## Semantic impact

Lean's observable result is preserved, but a compiler optimization essential
to practical execution is lost. Large lazy constants can make small valid
inputs consume hundreds of megabytes or gigabytes and take tens of seconds,
which makes otherwise supported compiled programs unusable.

## Classification and triage

This is a generic W7 arena-generation defect. The source LCNF contains the
correct lazy cache protocol, and the resident runtime already implements and
W6 proves recursive cache persistence. The loss is introduced only by FIR's
rewindable-arena preparation policy.

## Workaround

None. Do not precompute the production table in JavaScript, special-case the
lean-zip declaration, or disable scratch rewind.

## Upstream tracking

none

## Resolution and regression

Pending. The repair will preserve the compiler cache globals, synthesize an
idempotent module initializer from their exact typed layout, run it before
input allocation, and establish its post-initialization frontier as the lower
bound for every public-call rewind. The focused cache probe must agree with the
native oracle, initialize once, and retain a flat checkpoint across repeats
before the complete Level-1 path is accepted.
