---
id: FIR-BUG-wasm-none-module-local-extern-frontier
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.34.0-rc2
lean-revision: 6a10ac8c22beadecabdbb0919c2b50214762f91d
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-09-15
reproduction: integration/vbp-native-session-probe/ModuleProduct.lean
regression: integration/vbp-native-session-probe/module-product-check.sh
---

# Summary

The new isolated worker incorrectly equated upstream's imported-signature list
with every external implementation in a selected module closure. A declaration
owned by the current module can itself have `DeclValue.extern`.

## Minimal reproduction

Capture `Init.Data.Repr` and select `Nat.reprFast`. Its real module contains
`USize.repr`, declared with `@[extern "lean_string_of_usize"]`. The upstream
collector partitions by module ownership, not by code-versus-extern value.

## Exact commands

```sh
bash integration/vbp-native-session-probe/module-product-check.sh --isolated --once
```

## Expected semantics

Use the actual declaration value to retain native boundaries, including
module-local externs. Preserve the separate imported-signature list as such.

## Actual behavior

The initial worker captures 121 groups / 268 declarations for Init.Data.Repr,
then rejects the first selection with `worker external inventory mismatch`.
The renderer stays at its original 151 bodies / 41 interfaces.

## Proof or differential evidence

Lean `LCNF.EmitUtil.collectUsedDecls` first consults `getLocalImpureDecl?` and
returns that Decl regardless of its value constructor; only nonlocal names go
into `extSigs`. `Init/Data/Repr.lean` defines the native-attributed USize.repr.
The preexisting serial module-product adapter classifies by DeclValue already.

## Semantic impact

An incorrect worker admission assumption blocks capture; no emitted Wasm or
runtime/proof discrepancy is claimed.

## Classification and triage

FIR worker data classification, not VBP source or a Lean bug. Fix generically.

## Workaround

None; do not special-case Nat.reprFast, USize.repr or a VBP declaration.

## Upstream tracking

None. Upstream behavior is intentional and unchanged.

## Resolution and regression

The worker now inventories extern implementations by `DeclValue.extern`, retaining
module-local externs from canonical owning groups independently of imported
signatures. The original traversal passes Init.Data.Repr and reaches source
closure (47 modules / 1506 bodies / 125 native or VIR interfaces). The isolated
gate asserts that USize.repr remains the native `lean_string_of_usize` boundary;
no name-based implementation exception was added.
