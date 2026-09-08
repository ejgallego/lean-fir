import FirTalos.TrustAuditCore
import Lean.Elab.Tactic.Decide
import Lean.Elab.GuardMsgs

/-!
Negative tests of compiled dependency inspection. The native example is a
deliberate rejection fixture and is never used to prove a production theorem.
The custom axiom test restores the environment, so it exports no extra axiom.
-/

namespace FirTalos.TrustAudit

open Lean Elab Command

private theorem nativeProbe : (1 : Nat) = 1 := by native_decide

/-- warning: declaration uses `sorry` -/
#guard_msgs in
run_cmd do
  let actual := (← collectAxioms ``nativeProbe).map (·.toString)
  unless actual.any (fun name => name.contains "_native") do
    throwError "native rejection fixture did not introduce a generated axiom"
  if inventoryMatches standardAxioms actual then
    throwError "native-evaluation dependency escaped the strict inventory"
  if inventoryMatches #["sorryAx"] #["sorryAx"] then
    throwError "placeholder axiom was accepted"
  if inventoryMatches #["propext", "propext"] #["propext"] then
    throwError "duplicate inventory was accepted"
  if inventoryMatches #["propext"] #[] then
    throwError "removed dependency escaped exact-inventory review"
  -- Inspect a genuine compiled theorem/axiom edge, then restore the environment.
  withoutModifyingEnv do
    let axiomName := `FirTalos.TrustAudit.temporaryUnexpectedAxiom
    let theoremName := `FirTalos.TrustAudit.temporaryDependentTheorem
    liftCoreM <| addDecl (.axiomDecl {
      name := axiomName, levelParams := [], type := mkConst ``True, isUnsafe := false })
    liftCoreM <| addDecl (.thmDecl {
      name := theoremName, levelParams := [], type := mkConst ``True,
      value := mkConst axiomName })
    check theoremName #[axiomName.toString]
    let accepted ← try
      check theoremName standardAxioms
      pure true
    catch _ => pure false
    if accepted then throwError "unregistered compiled axiom escaped the inventory"
    let placeholderName := `FirTalos.TrustAudit.temporaryPlaceholderTheorem
    liftCoreM <| addDecl (.thmDecl {
      name := placeholderName, levelParams := [], type := mkConst ``True,
      value := mkApp2 (mkConst ``sorryAx [.zero]) (mkConst ``True) (toExpr true) })
    let placeholderAxioms := (← collectAxioms placeholderName).map (·.toString)
    unless placeholderAxioms.contains "sorryAx" do
      throwError "compiled placeholder fixture has no placeholder dependency"
    let placeholderAccepted ← try
      check placeholderName placeholderAxioms
      pure true
    catch _ => pure false
    if placeholderAccepted then throwError "compiled placeholder was allowlisted"
  let missingAccepted ← try
    check `FirTalos.TrustAudit.doesNotExist #[]
    pure true
  catch _ => pure false
  if missingAccepted then throwError "missing endpoint passed as an empty inventory"
  let definitionAccepted ← try
    check ``standardAxioms #[]
    pure true
  catch _ => pure false
  if definitionAccepted then throwError "non-theorem endpoint passed the audit"

end FirTalos.TrustAudit
