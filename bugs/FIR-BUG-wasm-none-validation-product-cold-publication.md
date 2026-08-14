---
id: FIR-BUG-wasm-none-validation-product-cold-publication
status: confirmed
classification: validation-harness
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-08-14
reproduction: integration/talos/artifact/check.sh
regression: none
---

# Summary

The W7 artifact gate can consume a freshly rebuilt semantic-Wasm product
bundle before `products.json` or one of its named module products is visible
as a regular file, although an immediate standalone validation retry succeeds.

## Minimal reproduction

On the cached recursive-persistence fixture head `4733a08e`, run the complete
artifact gate after its source and prettyM build phases have changed the local
build state. The embedded `make validate-v8` fails before engine execution,
first naming an existing module manifest and on a second full run naming
`products.json`. Both files are regular immediately after the failure.

## Exact commands

```sh
bash integration/talos/artifact/check.sh
make validate-v8
node integration/talos/artifact/check-concrete-validation-products.mjs \
  _build/validation-v8
```

The first command failed twice with `lean-wasm-semantic product is not a
regular file`. Each immediate second command passed all 704 native/LCNF/V8
cases, and the concrete checker then passed 642 executed cases with the exact
unchanged 62-case ByteArray blocker inventory.

## Expected semantics

Provider publication must make the bundle manifest and every checksummed
product visible atomically before validation consumes it. A complete artifact
gate should not require a warm standalone validation invocation.

## Actual behavior

The first full artifact invocation reported the existing
`aggregate-erased-before-closure-application.wasm.json` product as not a
regular file. After a successful standalone retry, a second complete artifact
invocation instead reported `products.json`. Inspection immediately after
each failure found the named path as a regular file, and the standalone retry
opened and verified all 1,408 products.

## Proof or differential evidence

Before the artifact invocation, complete `make check` passed 704 source cases,
the 704-case V8 triangle, and 2,121/2,121 comparisons. The focused retry passed
all 704 engine cases and the concrete checker executed both new cached
String/Nat persistence cases against their canonical V8 observations. No
observation mismatch or concrete-runtime blocker was produced.

## Semantic impact

No program-semantic discrepancy is known. The race prevents the required W7
artifact command from being a reliable single-pass integration gate and can
mask the later concrete-product classification step.

## Classification and triage

This is a validation-harness publication or replay-ordering defect. It is
reproducible only through the complete artifact orchestration so far; direct
`make validate-v8` is stable. The exact producer/consumer ordering boundary
still needs isolation. Do not weaken regular-file or checksum validation.

## Workaround

An immediate standalone `make validate-v8` followed by
`check-concrete-validation-products.mjs` completes successfully, but this is
diagnostic only and is not an accepted permanent gate change.

## Upstream tracking

none

## Resolution and regression

unresolved
