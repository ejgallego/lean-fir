---
id: FIR-BUG-wasm-none-pretty-state-refinement
status: confirmed
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

The support gate should retain enough exact provenance to recognize that the
projected state is a `Fir.Wasm.PrettyFormat.State` constructor and therefore a
heap object at the recursive call. Unrelated `tobject` values must remain
unable to satisfy an `object` parameter.

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

The direct concrete-state facade cannot generate executable Wasm for Lean's
standard pretty-printing algorithm even though it has a fully known
four-object input ABI and object result ABI. The raw-carrier facade avoids the
generic provenance gap without weakening admission for unrelated values.

## Classification and triage

This is a `wasm-adapter` issue. The source value is concretely heap-backed, but
the fail-closed support analysis loses that fact across a polymorphic object
projection before the recursive named call.

## Workaround

The Wasm `prettyM` facade uses `Nat` as a raw `tobject` state carrier and
confines the conversion to `unsafeCast` at the local formatting-state
boundary. This preserves the ordinary low-level `Format` input representation
without asking final LCNF to recover heap provenance from the polymorphic
product projection. The generic provenance gap remains fail-closed.

## Upstream tracking

none

## Resolution and regression

The generic adapter issue remains unresolved. `Fir/Wasm/Emit/SourceExamples.lean`
guards the raw facade inventory and proves that only the unreachable panic
specialization needs the separate checked refinement; the artifact fixture
then executes the resulting renderer from JavaScript.
