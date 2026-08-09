---
id: FIR-BUG-wasm-none-pretty-state-refinement
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-07-20
reproduction: Fir/Wasm/PrettyFormat.lean#prettyRaw
regression: Fir/Wasm/Emit/SourceExamples.lean
---

# Summary

The monomorphic `Std.Format.prettyM` worker passes its concrete formatting
state recursively after recovering it through a polymorphic object projection.
Final impure LCNF classifies that argument as `tobject`, while the specialized
worker's concrete state parameter requires `object`.

## Minimal reproduction

Compile `Fir.Wasm.PrettyFormat.prettyRaw` through final impure LCNF and run
`Fir.Wasm.validateSupported` over its complete dependency closure. The first
rejected declaration is the generated specialization of `Std.Format.be`.

## Exact commands

```sh
lake build Fir.Wasm.Emit.SourceExamples
```

## Expected semantics

The support gate should mirror upstream Lean's object-family calling
representation for compiler-produced calls while continuing to reject
unrelated scalar lanes.

## Actual behavior

The recursive worker has semantic parameter kinds

```text
[tobject, tobject, object]
```

but one generated call supplies

```text
[tobject, tobject, tobject]
```

and `supportedNamedCall` rejects the call.

## Proof or differential evidence

The first concrete-state experiment produced a closure with 60 declarations
and 24 imported signatures. All imported signatures were ABI-supported, but
the monomorphic `be` worker and its unreachable panic fallback specialization
failed `supportedDecl`.

The checked raw-carrier facade now has 23 external helper declarations and
passes the `be` worker. Before the narrowly checked panic-result refinement,
its only unsupported declaration is the unreachable panic specialization.
The complete internalized artifact executes in V8 and agrees with native
`Std.Format.pretty` on the tracked nested-line example.

## Semantic impact

Without upstream-compatible object-family calls, the direct concrete-state
facade cannot generate executable Wasm for Lean's standard pretty-printing
algorithm even though it has a fully known input and result ABI.

## Classification and triage

This is a `wasm-adapter` issue. The source value is concretely heap-backed, but
the fail-closed support analysis loses that fact across a polymorphic object
projection before the recursive named call.

## Workaround

The original Wasm facade used `Nat` as a raw `tobject` state carrier and
confined the conversion to `unsafeCast`. That workaround has been removed.

## Upstream tracking

Current upstream Lean's direct final-LCNF emitter maps every object-family
kind to `lean_object*` at calls, assignments, and returns. FIR now mirrors
that generic calling rule while preserving the semantic kind annotations used
by ownership operations and proofs.

## Resolution and regression

Both plain and styled facades now thread their concrete state structures
directly, with no `unsafeCast` or raw `Nat` carrier. The untouched final-LCNF
closure has zero unsupported declarations, including the former panic/weak
specialization site, and passes the focused source build. The resident
artifact gate retains the native/V8 differential execution check.
