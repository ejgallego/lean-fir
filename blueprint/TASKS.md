# Scalar-boxing trust-reduction candidates

These packets were drafted against FIR `81bb0e2ab` on Lean 4.34.0-rc2. W6
reviewed them at pilot head `e5d56dffd` in `W6-ROOT-20260928-011`. The existing
declarations are already proved and usable; the proposal is to reduce their
trusted dependencies, not to prove previously unproved behavior.

**Readiness decision:** the original full T1 and T2 replacements are blocked,
not ready for a proof lease. Both depend on opaque `Lean.Expr.eqv` through
`BEq Lean.Expr`, used by `scalarFromType` and `boxUsesTaggedRepresentation`.
At this pinned Lean source (`Lean/Expr.lean:809–812`), ordinary reduction or
structural reasoning does not expose the needed equality equation. No suitable
proof-facing law was found, and no new bridge axiom is authorized. Changing
the runtime classifier would be a separate shared-contract decision.

The only smaller candidate currently ready to scope is T1's impossible
UInt64-branch elimination below. It is unassigned and has not had its exact
compiled dependency delta audited. It is trust reduction, not completion of
full T1. No proof lease or source change is implied by this packet.

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

**Current blocker:** the UInt8/16/32 cases ask the opaque `Expr.eqv` Boolean
tests in `scalarFromType` to distinguish fixed type expressions. The existing
case split and theorem statement do not make those tests definitionally
decidable. Replacing `native_decide` with `decide`, unfolding scalar kinds, or
structural inequality arguments does not solve that interface gap.

**Consumer and measurable result:** scalar unboxing refinement in the same
module. The public compiler-export trust inventory contains ten generated
axioms under this theorem's name. Completion removes those dependencies at the
actual audited consumers, with no new nonstandard axioms and no changed type.
Measure the complete updated endpoint sets; do not merely delete inventory
strings or count the standalone replacement as integrated.

### T1 narrow candidate: eliminate the impossible UInt64 case

`BoxedScalarKind.allowsTaggedRepresentation` is definitionally `false` for
`.uint64`, while T1 assumes it is `true`. The existing UInt64 branch currently
uses four `native_decide` checks despite this contradictory premise. A
candidate local proof is:

```lean
| uint64 =>
    simp [BoxedScalarKind.allowsTaggedRepresentation] at allowed
```

W6 estimates this may reduce the declaration's generated dependencies from
ten to six and remove the four unreachable-branch assumptions at its audited
consumers. This is an expected delta, not a measured result. It does not remove
the opaque-equality blocker in the remaining UInt8/16/32 cases and does not
make full T1 ready.

**Acceptance before calling this task complete:** build the focused module under
the pinned toolchain, measure exact generated axiom sets for the theorem and
affected consumers, account for generated-name renumbering, and review the
exact inventory delta. Do not widen allowlists or claim standard-axiom-only
T1. Root has not issued a proof lease.

## T2: scalar boxing policy without native evaluation axioms

**Existing declaration:** `Fir.Wasm.Concrete.boxUsesTaggedRepresentation_boxedScalar`
in the same module.

**Readiness: blocked.** Its source type guard reaches the same opaque
`Expr.eqv` interface. Its existing seven generated dependencies remain an
audited trust policy; this packet is not a ready-to-prove task under the
current ingredients. Reopen it only with an independently justified
proof-facing equation/law or a separately reviewed shared-contract change.

Within `namespace Fir.Wasm.Concrete`, with `open Fir.LeanIR.Impure`:

```text
theorem boxUsesTaggedRepresentation_boxedScalar (scalar : BoxedScalar) :
    boxUsesTaggedRepresentation scalar.kind.semanticType scalar.payload =
      (scalar.kind.allowsTaggedRepresentation &&
        decide (scalar.payload.toNat ≤ maxTaggedPayload))
```

**Meaning:** the source type-specific boxing rule agrees with the concrete
scalar-kind policy and payload bound, including heap-only kinds.

**Interface gap:** the `BoxedScalar` projections and scalar-kind policies are
available, but they do not prove how opaque `Expr.eqv` evaluates on the fixed
type expressions. A kernel-only replacement cannot be assigned until that
missing proof interface is supplied and reviewed. No bridge axiom is proposed.

**Consumer and measurable result:** semantic boxing decomposition and scalar
boxing refinement in the same module. The public compiler-export inventory
contains seven generated axioms under this theorem's name. Completion removes
them at the audited consumers while preserving the theorem's simp behavior and
all production definitions.

## Common environment, checks and delivery

- Environment: the immutable FIR commit above, its `lean-toolchain` and official
  `tooling/talos-434` manifests; the Blueprint dependency pin is in this
  directory's manifest. Follow the root cache/TMPDIR policy.
- A future T1-narrow lease would cover only the UInt64 branch of
  `scalarFromType_boxedScalarKind` plus its exact affected trust inventory;
  it is not granted here. Any full T1/T2 proof or runtime-classifier change
  needs a new scope decision. W6 serializes overlapping edits.
- For a future full replacement, permitted transitive proof axioms are at most
  `propext`, `Classical.choice`, and `Quot.sound`; no `native_decide` escape,
  new assumption, altered scalar policy or source exclusion. The narrower T1
  candidate deliberately leaves the remaining six generated dependencies
  under the existing audited policy; it is not a full replacement.
- For the T1 narrow candidate: run `lake build Fir.Wasm.Concrete.BoxingCorrectness`,
  then exact theorem/consumer axiom audits and review the measured inventory
  delta. Full T1/T2 acceptance remains dormant until the opaque-equality
  interface blocker is resolved. Any later integration runs the normal
  `make check`, `make talos-setup`, and `make talos-check` gates.
- Deliver: proof patch, short mathematical explanation, exact tested commit,
  measured axiom changes and the consumer that uses the replacement.

The proposed T1 narrow task is not concurrent with a T2 task; T2 is blocked.
A failed portable Prove2Me environment setup should be recorded as an
integration finding; it must not lead to substituting unrelated copies of FIR
definitions.

## Blueprint status question exposed by these tasks

Both existing declarations are formalized and usable, although they carry
audited trust debt. The full replacement tasks are blocked by a missing proof
interface, while T1's unreachable UInt64 branch is a smaller unassigned trust
reduction. An ordinary open/proved node status cannot represent those
distinctions. Keep separate task readiness, theorem status, trust policy and
integration status; do not label either existing theorem mathematically
unproved.
