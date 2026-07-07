# FIR

FIR is an early research workspace for formalizing a small, usable model of
Lean compiler IR semantics and, later, relating that model to WebAssembly
semantics.

The current v1 target is a tiny subset of impure `Lean.Compiler.LCNF`, not the
older lower `Lean.IR` layer. See `docs/research.md` for the current research
notes and rationale.

## Requirements

- Lean toolchain: `leanprover/lean4:v4.31.0`
- Lake from the pinned Lean toolchain
- `rg` for the placeholder scan
- Optional: `lean-beam` for fast Lean diagnostics

## Common Commands

```sh
lake build
lake env lean Fir/LeanIR/Examples.lean
lake lean Inspect
rg -n "sorry|admit" Fir docs Inspect
```

Or use the Makefile:

```sh
make check
make beam
```

`make check` runs the build, examples, inspection entrypoint, and placeholder
scan. `make beam` syncs the Lean source modules and `Inspect` through Lean
Beam.

## Layout

- `Fir/LeanIR/LCNFCore.lean`: executable evaluator, supported-fragment
  predicate, big-step relation, and basic theorems.
- `Fir/LeanIR/Examples.lean`: small examples for literal returns, erased lets,
  nested lets, shadowing, and unsupported operations.
- `Inspect`: minimal `lake lean Inspect` entrypoint for a quick supported/eval
  status report plus current compiler-emitted LCNF shapes for tiny samples.
- `docs/research.md`: Lean IR and Wasm formalization research notes.
