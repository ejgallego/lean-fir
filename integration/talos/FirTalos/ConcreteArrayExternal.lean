import FirTalos.ConcreteArrayPublication

/-! Source external contracts for the fresh-Array initializer path. These
specify primitive calls, not a program invariant or a body execution. The
interpreter itself appends each call event; the responses keep world unchanged.
Concrete external admission and emitted-helper execution remain separate. -/

namespace FirTalos.Concrete

open Lean Fir.LeanIR.Impure Fir.Wasm.Concrete

def arrayExternalResponse (runtime : RuntimeState) (value : Value) : ExternalResponse :=
  { value, heap := runtime.heap, nextLocation := runtime.nextLocation,
    world := runtime.world }

/-- Only the fresh empty receiver/single tagged element branch is constrained
for push; shared, full and general-element calls remain unrestricted. The
contract is uniform in source state, capacity, payload and declaration types.
It must ultimately be discharged by the selected external implementation. -/
structure FreshArrayExternalContract (externals : ExternalImpl) : Prop where
  mkEmpty : ∀ (runtime : RuntimeState) (types : Array Expr) (resultType : Expr)
      (capacity : UInt64),
    externals.call {
      name := `Array.mkEmpty, paramTypes := types, resultType,
      args := #[.erased, .object (.tagged capacity)] } runtime =
      .ok (arrayExternalResponse (semanticArrayResult runtime #[] capacity.toNat)
        (.object (.heap runtime.nextLocation)))
  pushFreshTagged : ∀ (runtime : RuntimeState) (types : Array Expr) (resultType : Expr)
      (capacity : Nat) (payload : UInt64), 0 < capacity →
    externals.call {
      name := `Array.push, paramTypes := types, resultType,
      args := #[.erased, .object (.heap runtime.nextLocation),
        .object (.tagged payload)] }
      (semanticArrayResult runtime #[] capacity) =
      .ok (arrayExternalResponse
        (semanticArrayResult runtime #[.object (.tagged payload)] capacity)
        (.object (.heap runtime.nextLocation)))

/-- Executable source interpretation for this bounded Array fragment. It
rejects other requests, including copy-on-write; it is a consistency witness
for the external contract, not the production host or resident implementation. -/
def freshArrayExternals : ExternalImpl where
  call request runtime := do
    if request.name == `Array.mkEmpty then
      match request.args.toList with
      | [.erased, .object (.tagged capacity)] =>
          return arrayExternalResponse (semanticArrayResult runtime #[] capacity.toNat)
            (.object (.heap runtime.nextLocation))
      | _ => throw (.externalFailure request.name "unsupported empty Array arguments")
    else if request.name == `Array.push then
      match request.args.toList with
      | [.erased, .object (.heap location), .object (.tagged payload)] =>
          let cell ← getLiveCell runtime location
          if cell.persistent || cell.rc != 1 then
            throw (.externalFailure request.name "Array receiver is not unique")
          let .array elements capacity := cell.object | throw .expectedObject
          if elements.size < capacity then
            let after ← Fir.LeanIR.Impure.setCell runtime location
              { cell with object := .array (elements.push (.object (.tagged payload))) capacity }
            return arrayExternalResponse after (.object (.heap location))
          else throw (.externalFailure request.name "Array receiver has no spare capacity")
      | _ => throw (.externalFailure request.name "unsupported tagged push arguments")
    else throw (.externalFailure request.name "outside fresh Array fragment")

theorem freshArrayExternals_contract : FreshArrayExternalContract freshArrayExternals := by
  constructor
  · intro runtime types resultType capacity
    rfl
  · intro runtime types resultType capacity payload spare
    simp [freshArrayExternals, semanticArrayResult, semanticArrayCell,
      getLiveCell, findCell?, Fir.LeanIR.Impure.setCell, replaceCell,
      spare, Pure.pure, Except.pure, Bind.bind, Except.bind]

/-- A finite executable prefix supplies the ordinary small-step relation.
No final observation is needed, so clients can retain the full reached state,
including globals and continuation frames. -/
theorem execSteps_of_run_outOfFuel
    {externals : ExternalImpl} {fuel : Nat} {before after : MachineState}
    (execution : run fuel externals before = .outOfFuel after) :
    ExecSteps externals fuel before after := by
  induction fuel generalizing before with
  | zero =>
      have same : before = after := RunResult.outOfFuel.inj execution
      subst after
      exact .refl before
  | succ fuel ih =>
      simp only [run] at execution
      cases step : executeStep externals before with
      | done observation => rw [step] at execution; contradiction
      | next middle =>
          rw [step] at execution
          exact .step step (ih execution)

end FirTalos.Concrete
