import FirTalos.TrustInventory
import FirTalos.TrustAuditTests
import FirTalos.ConcreteObservationSensitivity
import FirTalos.ConcreteTerminalCorrectness
import FirTalos.ConcreteTerminalExtraction
import FirTalos.ConcreteTerminalSimulation
import FirTalos.ConcreteRootResult
import FirTalos.ConcreteRootedDispatch
import FirTalos.ConcreteRootedSimulation
import FirTalos.ConcreteRootedTerminal
import FirTalos.ConcreteSupportedPipeline
import FirTalos.ConcreteSourceValidationTests
import FirTalos.ConcreteLazyPublicationTests
import FirTalos.ConcreteResumableWasm
import FirTalos.ConcretePassComposition
import FirTalos.ConcreteCompilerCorrectness
import FirTalos.ConcreteFaultCorrectness
import FirTalos.ConcreteResidentReplacement
import FirTalos.ConcreteResidentScalarBox
import FirTalos.Correctness.FunctionExamples

/-!
The default Talos umbrella imports this module, so a changed endpoint dependency
rechecks its exact inventory as part of `make talos-check`. The companion
`check-proof-trust.py` additionally forces batch elaboration and audits source
roots, including integration proofs that the root textual gate does not scan.
-/

open Lean Elab Command in
run_cmd do
  for (endpoint, expected) in FirTalos.TrustAudit.endpointInventory do
    FirTalos.TrustAudit.check endpoint expected
    let generated := expected.filter fun name =>
      !FirTalos.TrustAudit.standardAxioms.contains name
    logInfo m!"trust audit: {endpoint}: {expected.size} axioms, {generated.size} recorded generated dependencies"
