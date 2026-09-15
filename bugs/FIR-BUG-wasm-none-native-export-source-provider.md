---
id: FIR-BUG-wasm-none-native-export-source-provider
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.34.0-rc2
lean-revision: 6a10ac8c22beadecabdbb0919c2b50214762f91d
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-09-15
reproduction: integration/vbp-native-session-probe/LowerModuleProduct.lean
regression: integration/vbp-native-session-probe/module-product-check.sh
---

# Summary

FIR's renderer module-product assembler treats every named `@[extern]` as a
terminal native boundary. Some of these symbols are provided by ordinary Lean
`@[export]` declarations. Upstream native linking connects these declarations;
FIR's Lean-name-based source closure currently omits that symbol-resolution edge.

## Minimal reproduction

Lean 4.34's `Init.Data.String.Bootstrap` declares
`Substring.Raw.Internal.takeWhile` with `@[extern "lean_substring_takewhile"]`.
`Init.Data.String.Substring` defines `Substring.Raw.Internal.takeWhileImpl`
with `@[export lean_substring_takewhile]`. The real renderer reaches the former.
Its FIR source closure stops at the extern instead of including the provider.

## Exact commands

```sh
bash integration/vbp-native-session-probe/module-product-check.sh --isolated --lower
```

## Expected semantics

Resolve a native symbol against actual upstream export metadata, capture the
provider in its owning module, and check the final compiled interface before
linking. Native symbols without a Lean provider remain explicit imports. This
does not authorize choosing an arbitrary Lean fallback body for an extern.

## Actual behavior

The deterministic 47-module / 1,506-body closure lowers to valid base Wasm but
resident linking leaves 28 imports. Twelve are the intentional VIR boundary;
many String/Substring entries among the other imports have upstream Lean export
providers. No accepted linked renderer package is emitted.

## Proof or differential evidence

Upstream `Lean.getExportNameFor?` exposes the `export` attribute. The final-LCNF
C emitter's `toCName` emits that exact symbol for the provider; its external-call
path uses `getExternEntryFor` with the C backend for the imported symbol. The declarations
above use the identical symbol. The fixture's diagnostic also queries the real
renderer environment for matching export metadata and compiled signatures.

## Semantic impact

This is an omitted source-provider edge and a generation blocker, not a
demonstrated wrong execution result. Host/runtime admission remains fail-closed.

## Classification and triage

Generic FIR native-symbol resolution gap, not a VBP source issue. Resolve symbols
and compiled interfaces; do not infer providers from an `Impl` name suffix.

## Workaround

None. Do not reimplement the upstream Substring functions in JavaScript or FIR
resident instruction lists to hide the missing Lean provider edge.

## Upstream tracking

None. The extern/export pairing is intentional upstream bootstrap architecture.

## Resolution and regression

`Fir.Wasm.Emit.NativeSymbol` implements generic metadata-based provider selection
and exact interface-checked linking through typed forwarding functions. The
renderer closes 16 native-symbol edges; all twelve previously missing exported
Lean providers disappear from the linker frontier (28 -> 17 imports, including
one newly exposed raw atEnd alias). Two fresh products/lowerings agree, metadata
and symbolic rejection controls pass, and the standalone Node forwarding test
passes. Remaining native primitives and host execution are separate.

The real traversal also confirms that an importing
environment need not expose the implementation expression (for example
`String.Internal.containsImpl`, exported by `Init.Data.String.Search`). Do not
require a `defnInfo` view in the importer: require its compiled signature, then
check actual captured code and export metadata in the owning module. Keep
source-unit and explicit native/VIR boundary tests intact.
