import Fir.Wasm.Emit.Source
import Lean.Elab.Command

/-!
Keep this module's imports production-only. A test in SourceExamples itself
cannot detect a dependency regression because that module deliberately loads
the validation harness.
-/

open Lean Elab Command

run_cmd do
  let validationModules := (← getEnv).header.moduleNames.filter fun name =>
    (`Fir.Validation).isPrefixOf name
  unless validationModules.isEmpty do
    throwError "production source compilation imported validation modules: {validationModules}"

-- Legacy capture names are aliases, not a second implementation or a reason
-- for production consumers to import the validation harness.
example : Fir.Validation.Lcnf.Artifact = Fir.Compiler.Lcnf.Artifact := rfl

example : Fir.Validation.Lcnf.compileEntry = Fir.Compiler.Lcnf.compileEntry := rfl

example : Fir.Validation.Lcnf.collectForms = Fir.Compiler.Lcnf.collectForms := rfl

example : Fir.Validation.Lcnf.Artifact.format = Fir.Compiler.Lcnf.Artifact.format := rfl
