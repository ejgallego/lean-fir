---
id: FIR-BUG-wasm-none-vir-verso-bridge-closure-admission
status: active
classification: compiler
lean-toolchain: leanprover/lean4:v4.34.0-rc2
lean-revision: 6a10ac8c22beadecabdbb0919c2b50214762f91d
phase: wasm
pass: none
discovered-by: source-closure-test
first-seen: 2026-08-31
reproduction: Fir/Wasm/Emit/Source.lean
regression: none
---

# Summary

The exact two-entry VIR Verso viewer closure captures successfully from
ordinary Lean 4.34 sources, but Wasm admission rejects a generated closure in
`Lean.Vir.Infoview.ReactRpcWidget.bridgeComponent` as `unsupportedCode`.

## Minimal reproduction

At VIR commit `676e04ae5b6f098c84e3afb97cdde8792dcc49da` with Verso
commit `99e9df791e46ec647f81d98b109965f166b9b6b4`, compile these roots with
`Fir.Wasm.Emit.Source.compileEntriesIndividuallyInternalized`:

- `Lean.Vir.Verso.Infoview.Widget.mount`
- `Lean.Vir.Verso.Infoview.Widget.unmount`

Retain the 44 `@[vir_js]` host declarations and their compiler-generated
`_boxed` adapters, plus FIR's ordinary closed-application external frontier.
The exact source capture contains 1,786 declarations and 151 externals.

## Expected semantics

The generated closure should pass the same structural Wasm admission used by
the existing source examples, lower to symbolic Wasm, and retain the reviewed
VIR JavaScript host frontier for resident linking and package validation.

## Actual behavior

`compileModuleArtifactWithExports` returns:

```text
Fir.Wasm.Emit.Source.CompileError.lowering
  (Fir.Wasm.SupportedLoweringError.validation
    (Fir.Wasm.ValidationError.unsupportedCode
      `_private.Vir.Infoview.RpcWidget.0.Lean.Vir.Infoview.ReactRpcWidget.bridgeComponent._at_.Lean.Vir.Infoview.ReactRpcWidget.mount._at_.Lean.Vir.Verso.Infoview.Widget.mount.spec_0.spec_0._lam_0))
```

No Wasm module or browser execution is reached.

## Proof or differential evidence

VIR's exact native package generator is green for the same roots and reports
1,443 Lean IR declarations, 110 native extern declarations, 44 JavaScript host
imports, and no missing declarations or native registrations. FIR's exact
final-LCNF capture completes before admission fails.

## Semantic impact

The reusable Verso viewer cannot yet be published as a FIR-native browser
package. Any admission repair must remain generic because the declaration is
a compiler-generated closure from ordinary higher-order source, not a
viewer-specific helper.

## Classification and triage

This is W7 compiler admission work. Determine which conjunct of
`supportedDecl` or `reuseCapacitySafeCode` rejects the exact declaration, then
align it with the already-supported compiler-produced closure convention. Do
not fence the declaration, match its generated name, or weaken unrelated ABI
and ownership checks.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Pending.
