---
id: FIR-BUG-wasm-none-vbp-smoke-js-resource-result
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.34.0-rc2
lean-revision: 6a10ac8c22beadecabdbb0919c2b50214762f91d
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-09-01
reproduction: integration/vbp-verso-viewer/check.sh
regression: integration/vbp-verso-viewer/package-smoke.mjs
---

# Summary

The VBP viewer smoke host returns raw JavaScript payloads from VIR nullable
operations whose reviewed protocol result is an owned `Js` resource.

## Minimal reproduction

Run the exact VBP viewer package smoke far enough to evaluate
`Lean.Vir.Browser.Performance.usedHeapBytes?`. The fake
`js.nullable.isNull` binding returns a raw Boolean. FIR correctly stores that
host result as an opaque resource; the subsequent explicit
`Lean.Vir.JsValue.toBool` conversion resolves it and calls `js.bool.value`
with the raw Boolean rather than the fake host's resource wrapper.

## Exact commands

```sh
bash integration/vbp-verso-viewer/check.sh
```

## Expected semantics

The fake host must mirror VIR's reviewed resource protocol. Both
`js.nullable.isNull` and `js.nullable.value` return owned `Js` resources;
explicit `JsValue.toBool` and the other value conversions are the operations
that decode those resources into Lean-owned values.

## Actual behavior

`js.nullable.isNull` returns a primitive Boolean and `js.nullable.value`
returns its unwrapped payload. This removes one host-resource layer and makes
the next explicit conversion observe a value of the wrong shape.

## Proof or differential evidence

VIR's pinned `createJsValueHostBindings` implementation returns
`resources.resourceForValue(...)` from both nullable operations. The FIR smoke
failed in `js.bool.value` with `typeof value === "boolean"` where its fake
resource wrapper was expected.

## Semantic impact

This does not change emitted Wasm or FIR's physical ABI. It prevented the
package smoke from exercising the production host-resource lifecycle after
the resident-cache sentinel repair.

## Classification and triage

This is a package acceptance-host discrepancy. Align the fake bindings with
the pinned VIR protocol instead of changing generated code or weakening the
adapter's resource checks.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

The fake nullable bindings now return fresh resource wrappers for both the
Boolean null test and the extracted non-null payload. The exact package smoke
therefore preserves the same two-stage resource/conversion boundary as VIR's
browser host.
