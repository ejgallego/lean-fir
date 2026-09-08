import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
Compiled dependency checks used by the W6 proof gate. The expected lists are
exact inventories, not prefix allowlists. Existing native-evaluation debt must
be named individually; `sorryAx` is forbidden even in an expected list.
-/

namespace FirTalos.TrustAudit

open Lean Elab Command

def standardAxioms : Array String :=
  #["propext", "Classical.choice", "Quot.sound"]

def inventoryMatches (expected actual : Array String) : Bool :=
  !expected.contains "sorryAx" && !actual.contains "sorryAx" &&
    decide expected.toList.Nodup && decide actual.toList.Nodup &&
    expected.all actual.contains && actual.all expected.contains

/-- Resolve and inspect an existing theorem before comparing its transitive
axioms. A missing declaration must never pass as an empty dependency set. -/
def check (endpoint : Name) (expected : Array String) : CommandElabM Unit := do
  let some (.thmInfo _) := (← getEnv).find? endpoint |
    throwError "trust audit requires an existing theorem: {endpoint}"
  let actual := (← collectAxioms endpoint).map (·.toString)
  unless inventoryMatches expected actual do
    let added := actual.filter fun name => !expected.contains name
    let removed := expected.filter fun name => !actual.contains name
    throwError "axiom inventory changed for {endpoint}\nunexpected: {added}\nmissing: {removed}\nexpected: {expected}\nactual: {actual}"

end FirTalos.TrustAudit
