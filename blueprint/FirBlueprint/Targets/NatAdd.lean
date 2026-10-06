import Batteries.Tactic.OpenPrivate
import Fir.Validation.LCNF
import FirTalos.ConcreteRuntime

/-! A source-handler contract slice, independent of the draft global external
specification. Production modules must not import Blueprint targets. -/

open private externalNat natBinaryExternal natAddExternal validationExternals
  from Fir.Validation.LCNF

namespace FirBlueprint.Targets

open Fir.LeanIR.Impure FirTalos.Concrete

/-- Mathematical natural arguments accepted by the source validation decoder.
The heap case requires an actual successful live-cell lookup. This is not yet
a claim that every such value satisfies a compiler ABI or runtime invariant. -/
inductive NatArgument (before : RuntimeState) : Value → Nat → Prop where
  | tagged (payload : UInt64) :
      NatArgument before (.object (.tagged payload)) payload.toNat
  | heap (location : Location) (cell : HeapCell) (value : Nat)
      (live : getLiveCell before location = .ok cell)
      (natural : cell.object = .natural value) :
      NatArgument before (.object (.heap location)) value

/-- The arithmetic request domain, defined without calling the implementation.
Metadata is deliberately unrestricted: the source handler ignores it. Compiler
metadata alignment is a separate obligation, not a consequence of this domain. -/
def NatAddInputs (request : ExternalRequest) (before : RuntimeState)
    (left right : Nat) : Prop :=
  request.name = ``Nat.add ∧
    ∃ leftValue rightValue,
      request.args = #[leftValue, rightValue] ∧
      NatArgument before leftValue left ∧ NatArgument before rightValue right

/-- Precise successful-response clause for source Nat addition. It specifies
the sum and the complete canonical response, including allocation and world.
It is a clause for one operation, not a specification of all external calls. -/
def NatAddResponse (request : ExternalRequest) (before : RuntimeState)
    (response : ExternalResponse) : Prop :=
  ∃ left right, NatAddInputs request before left right ∧
    response = semanticNaturalExternalResponse before (left + right)

private theorem NatArgument.decode {before : RuntimeState} {value : Value}
    {natural : Nat} (request : ExternalRequest)
    (argument : NatArgument before value natural) :
    externalNat request before value = .ok natural := by
  cases argument with
  | tagged payload => rfl
  | heap location cell value live natural =>
    simp [externalNat, live, natural, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- The actual validation dispatcher succeeds on every request in the
arithmetic domain and returns its specified response. This supplies both
availability and response correctness, not only correctness conditional on
an assumed successful call. Private handler access is confined to this adapter. -/
theorem validation_natAdd {request : ExternalRequest} {before : RuntimeState}
    {left right : Nat} (inputs : NatAddInputs request before left right) :
    let response := semanticNaturalExternalResponse before (left + right)
    validationExternals.call request before = .ok response ∧
      NatAddResponse request before response := by
  constructor
  · obtain ⟨name, leftValue, rightValue, arguments, leftArg, rightArg⟩ := inputs
    have world : (literal before (.nat (left + right))).1.world = before.world := by
      by_cases small : left + right ≤ maxTaggedPayload <;> simp [literal, alloc, small]
    simp [validationExternals, name, natAddExternal, natBinaryExternal,
      arguments, leftArg.decode request, rightArg.decode request,
      semanticNaturalExternalResponse, Bind.bind, Except.bind, Pure.pure, Except.pure, world]
  · exact ⟨left, right, inputs, rfl⟩

end FirBlueprint.Targets
