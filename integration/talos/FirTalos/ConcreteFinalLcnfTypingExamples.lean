import FirTalos.ConcreteFinalLcnfTyping
import Fir.Validation.LCNF
import Fir.Wasm.WellFormed
import Lean.Elab.Command

/-!
# A real final-LCNF typing fixture

`sumTo` is the first small production-compiler program used while building the
source-semantic admission layer.  It is deliberately more useful than a
closed arithmetic expression: Lean emits a recursive direct call, natural and
Boolean externals, a scalar case, ownership decrements, and two returns.

The regression below does not certify a hand-written copy of that code.  It
asks the installed Lean compiler for final impure LCNF and checks the stable
source facts on which the reusable proof is meant to depend.  Binder names and
individual control-flow nodes remain compiler-private and are intentionally
not pinned.
-/

namespace FirTalos.Concrete.FinalLcnfTypingExamples

open Lean Elab Command

@[noinline]
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => n + 1 + sumTo n

/-- The three unresolved result families in the generated body are already
part of W6's name-indexed pure-external contract. -/
theorem sumTo_external_result_families :
    PureScalarExternalName ``Nat.decEq .uint8 ∧
      PureNaturalExternalName ``Nat.sub ∧
        PureNaturalExternalName ``Nat.add :=
  ⟨.natDecEq, .natSub, .natAdd⟩

/-
The real compiler output for `sumTo` stays within the admitted final-LCNF
surface.  Its only unresolved operations are precisely the pure external
families used by the example: Boolean natural equality and natural
subtraction/addition.  The generated entry preserves the `.tobject` ABI at
both its parameter and result boundaries.
-/
run_cmd do
  let artifact ← liftCoreM <| withoutModifyingEnv <|
    Fir.Validation.Lcnf.compileEntry ``sumTo
  let some entry := artifact.program.findDecl? ``sumTo
    | throwError "sumTo disappeared from final-LCNF capture"
  let parameterKinds := entry.params.mapM fun param =>
    Fir.Wasm.abiValueKind? param.type
  unless parameterKinds == some #[.tobject] do
    throwError "sumTo parameter ABI changed: {repr parameterKinds}"
  unless Fir.Wasm.abiValueKind? entry.type == some .tobject do
    throwError "sumTo result ABI changed: {repr entry.type}"
  let expectedExternals : Array Name := #[``Nat.decEq, ``Nat.sub, ``Nat.add]
  unless artifact.externalNames == expectedExternals do
    throwError "sumTo external family changed: {repr artifact.externalNames}"
  let expectedForms : Array String :=
    #["lit", "fap", "cases", "return", "dec", "extern"]
  unless artifact.forms == expectedForms do
    throwError "sumTo final-LCNF forms changed: {repr artifact.forms}"
  unless Fir.Wasm.supportedDecl artifact.program entry do
    throwError "sumTo entry is outside production Wasm admission"
  match Fir.Wasm.validateSupported artifact.program with
  | .ok _ => pure ()
  | .error error =>
      throwError "sumTo final LCNF failed production Wasm admission: {repr error}"

end FirTalos.Concrete.FinalLcnfTypingExamples
