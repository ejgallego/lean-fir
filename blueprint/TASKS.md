# Two concrete contribution packets for owner review

These packets are drafted against FIR `81bb0e2ab` on Lean 4.34.0-rc2.
Their statements are already present in production. The requested work is a
replacement proof with a smaller trusted dependency set. They are unassigned
and await W6 scope review; no external publication has occurred.

The source files are authoritative. The signatures below are transcribed for
review. Use the same definitions and all existing hypotheses. Do not import the
old result as the proof of its replacement: its generated axioms would remain.

## T1: scalar decoding without native evaluation axioms

**Existing declaration:** `Fir.Wasm.Concrete.scalarFromType_boxedScalarKind` in
[`BoxingCorrectness.lean`](../Fir/Wasm/Concrete/BoxingCorrectness.lean).

Within `namespace Fir.Wasm.Concrete`, with `open Fir.LeanIR.Impure`:

```text
theorem scalarFromType_boxedScalarKind (kind : BoxedScalarKind) (payload : UInt64)
    (allowed : kind.allowsTaggedRepresentation = true) :
    scalarFromType kind.semanticType payload =
      .ok (BoxedScalar.ofPayload kind payload).semanticValue
```

**Meaning:** for every scalar kind permitted by the tagged-representation
policy, decoding the payload at that kind's semantic type returns the same
semantic scalar value as the concrete payload model.

**Available ingredients:** `BoxedScalarKind.semanticType`,
`BoxedScalarKind.allowsTaggedRepresentation`, `BoxedScalar.ofPayload`,
`BoxedScalar.semanticValue`, and the case equations of `scalarFromType`.
The existing proof already splits the scalar kinds. Replace its native checks
of the fixed Lean type expressions with kernel-checked reasoning.

**Consumer and measurable result:** scalar unboxing refinement in the same
module. The public compiler-export trust inventory contains ten generated
axioms under this theorem's name. Completion removes those dependencies at the
actual audited consumers, with no new nonstandard axioms and no changed type.
Measure the complete updated endpoint sets; do not merely delete inventory
strings or count the standalone replacement as integrated.

## T2: scalar boxing policy without native evaluation axioms

**Existing declaration:** `Fir.Wasm.Concrete.boxUsesTaggedRepresentation_boxedScalar`
in the same module.

Within `namespace Fir.Wasm.Concrete`, with `open Fir.LeanIR.Impure`:

```text
theorem boxUsesTaggedRepresentation_boxedScalar (scalar : BoxedScalar) :
    boxUsesTaggedRepresentation scalar.kind.semanticType scalar.payload =
      (scalar.kind.allowsTaggedRepresentation &&
        decide (scalar.payload.toNat ≤ maxTaggedPayload))
```

**Meaning:** the source type-specific boxing rule agrees with the concrete
scalar-kind policy and payload bound, including heap-only kinds.

**Available ingredients:** the `BoxedScalar` constructors and their `kind` and
`payload` projections, `BoxedScalarKind.semanticType`,
`BoxedScalarKind.allowsTaggedRepresentation`, and
`Fir.LeanIR.Impure.boxUsesTaggedRepresentation`. The existing proof reduces a
fixed type guard by cases; the replacement should justify that guard through
kernel reduction or structural type-expression facts.

**Consumer and measurable result:** semantic boxing decomposition and scalar
boxing refinement in the same module. The public compiler-export inventory
contains seven generated axioms under this theorem's name. Completion removes
them at the audited consumers while preserving the theorem's simp behavior and
all production definitions.

## Common environment, checks and delivery

- Environment: the immutable FIR commit above, its `lean-toolchain` and official
  `tooling/talos-434` manifests; the Blueprint dependency pin is in this
  directory's manifest. Follow the root cache/TMPDIR policy.
- Write scope to request from W6: the selected proof in
  `Fir/Wasm/Concrete/BoxingCorrectness.lean`, exact affected trust inventory
  entries, and a focused regression if needed. W6 serializes overlapping edits.
- Permitted transitive proof axioms: at most `propext`, `Classical.choice`, and
  `Quot.sound` for each replacement. No `native_decide` escape, new assumption,
  altered scalar policy or source exclusion.
- Focused check: `lake build Fir.Wasm.Concrete.BoxingCorrectness`; inspect exact
  axiom sets for both replacement and its intended consumer in the pinned
  environment. Owner integration runs `make check`, `make talos-setup`,
  `make talos-check`, and reviews the exact inventory delta.
- Deliver: proof patch, short mathematical explanation, exact tested commit,
  measured axiom changes and the consumer that uses the replacement.

These two tasks may share small type-expression facts and should be coordinated
if worked concurrently. A failed portable Prove2Me environment setup should be
recorded as an integration finding; it must not lead to substituting unrelated
copies of FIR definitions.

## Blueprint status question exposed by these tasks

Both existing declarations are formalized and already usable. A new proof of
the same proposition can still be valuable because it removes trust debt.
An ordinary open/proved node status cannot represent that task by itself.
Should a contribution target be a separate proof alternative with a trust
policy, a refinement obligation attached to the declaration, or a project-level
task that references it? Keep this question open while testing the upcoming
integration; do not label the existing theorem mathematically unproved.
