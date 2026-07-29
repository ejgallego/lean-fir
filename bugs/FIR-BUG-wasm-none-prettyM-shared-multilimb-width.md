---
id: FIR-BUG-wasm-none-prettyM-shared-multilimb-width
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 91dfa94a3cfc8b126cbc0317acda88c9e4d34462
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-07-29
reproduction: integration/talos/artifact/check-prettyM-browser-adapter.mjs
regression: integration/talos/artifact/check-prettyM-browser-adapter.mjs
---

# Summary

The versioned arbitrary-precision Natural validator rejects a canonical
multi-limb width after compiled `prettyM` increments its reference count.

## Minimal reproduction

Construct `Format.group (Format.text "x" ++ Format.line)` in module-owned
memory, pass the canonical W6 Natural representation of `2^63` as the width,
and invoke the zero-import styled `prettyM` facade. The same facade accepts
`2^63 - 1`, and the standalone arbitrary-precision helpers accept larger
multi-limb Naturals.

## Exact commands

From the repository root after producing the closed styled artifact:

```sh
integration/talos/artifact/package-pretty-format.sh --no-build
```

## Expected semantics

`Std.Format.prettyM` is pure in its width argument. A live nonpersistent
Natural with a positive reference count is valid whether unique or shared.
The linked helper should therefore render `"x "` for both widths.

## Actual behavior

The `2^63` call traps in `fir_big_numeric_validate_natural`, reached through
`fir_big_ext_Int_ofNat`. Reduction across boundary values shows that
`2^63 - 1` succeeds and the first canonical big-Natural representation traps.

## Proof or differential evidence

The browser adapter package smoke reuses the same compact input and compares
the exact styled trace. Direct export-index inspection maps the first trapping
frame to `fir_big_numeric_validate_natural`. Its ordinary-object validation
requires reference count exactly one, while the compiled caller has
incremented the reused width.

## Semantic impact

Linked `prettyM` does not yet accept arbitrary valid Lean Natural widths even
though the standalone W7 helper corpus covers arbitrary-precision arithmetic.
Other pure versioned Nat/Int helpers can reject valid shared heap inputs for
the same reason.

## Classification and triage

This is a W7 resident-helper validation bug. The W6 concrete representation is
unchanged; the helper should retain the nonpersistent/live requirement while
accepting any nonzero ordinary reference count.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

The versioned arbitrary-precision validator now requires a live
nonpersistent object with a nonzero reference count instead of requiring
exactly one. The production browser-adapter smoke passes the same compact
format first with width 80 and then with a 131-bit width, verifies the exact
styled trace both times, and checks that the resident frontier remains
monotone across calls.
