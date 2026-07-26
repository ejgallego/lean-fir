---
id: FIR-BUG-wasm-none-resident-result-location-registry
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-07-26
reproduction: integration/talos/artifact/prettyM-package/smoke.mjs
regression: integration/talos/artifact/prettyM-package/smoke.mjs
---

# Summary

The styled prettyM decoder rejects a valid Wasm-resident result constructor
because it assumes every heap address has a JavaScript allocator location.

## Minimal reproduction

Package the styled `Std.Format.prettyM` artifact after internalizing its 27
`allocCtor` operations, then run the package smoke test. The final
`PrettyTrace` pair is allocated by a resident constructor helper, while the
decoder first sends its physical result through `ConcreteHost.decode`.

## Exact commands

From `integration/talos/artifact` after generating the styled constructor
checkpoint:

```sh
./package-pretty-format.sh --no-build
```

## Expected semantics

The raw package facade returns a wasm32 object word. Its decoder should verify
that the word names a live constructor in module-owned memory and decode that
address directly, regardless of whether Wasm or a remaining host handler
allocated it.

## Actual behavior

`decodeConcretePrettyTrace` calls `ConcreteHost.decode("object", result)`.
That generic semantic-observation path requires an entry in
`addressLocations`, which is populated only by `ConcreteHost.allocate`.
It therefore fails with `concrete address ... has no logical location` for the
valid resident result.

## Proof or differential evidence

The styled module validates, reports 157 function imports and no `allocCtor`
imports, and reaches result decoding after completing prettyM. Its returned
word points at a live constructor header in the shared module-owned memory;
only the host bookkeeping lookup fails.

## Semantic impact

Raw consumers cannot decode any heap result first allocated by Wasm, blocking
the styled package as soon as result construction becomes resident. The
generated representation itself is not implicated.

## Classification and triage

This is a `wasm-adapter` defect. The package intentionally exposes raw Lean
words, but its styled decoder accidentally routes that word through a
host-allocation-specific observation registry.

## Workaround

The styled decoder consumes the raw wasm32 heap address directly, as specified
by the package facade.

## Upstream tracking

none

## Resolution and regression

`decodeConcretePrettyTrace` now classifies the physical result word and reads
the constructor at its unsigned wasm32 address without consulting the
JavaScript allocator's logical-location registry. The package smoke test and
browser Fetch worker both decode the resident result and compare its full
styling-event stream with the native Lean oracle.
