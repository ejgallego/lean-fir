---
id: FIR-BUG-wasm-none-eliminated-lazy-cache-amplification
status: fixed
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

The former eager initializer repair preserved the compiler's exact typed
flag/value globals and synthesized the exported, idempotent
`fir_initialize_persistent_caches` entry. Each miss calls the original
initializer, publishes recursive persistence through the existing cache-set
helper, stores the value, and sets its initialized flag while leaving existing
cache-eliminating packages unchanged.

The augmented zero-import resident-cache artifact proves the two-region
protocol in Node and Chrome: initialization allocates a persistent constructor
graph once, a second initialization leaves the frontier unchanged, scratch is
allocated at the checkpoint, rewind restores it, and the cached root remains
valid.

The real Level-1 package now retains its compiler cache and passes the complete
five-case native differential. For an 83-byte representative, a local run
changed from roughly 46.7 seconds and 935,103,808 scratch bytes to about 15 ms
of entry execution and 525,584 scratch bytes after a one-time 8,031,880-byte
cache initialization. The exact `distanceCodeCacheProbe` at lean-zip source
revision `74e4826cee362d815a11c213894f072ced5e6b0a` additionally passes four
native-oracle cases twice each, including 4,096 repeated bytes, while every
call returns to the same persistent checkpoint.

The later lazy cache-floor repair supersedes that production design. The eager
helper is now named `installUnsafeEagerPersistentInitializer` and remains only
for the diagnostic fixture; accepted packages publish caches lazily.
