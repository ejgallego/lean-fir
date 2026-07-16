import Fir.Wasm.Lower
import Fir.LeanIR.InterpreterExamples

namespace Fir.Wasm

open Lean.Compiler
open Fir.LeanIR.InterpreterExamples

def lowers? (program : Fir.LeanIR.ImpureProgram) : Bool :=
  match lower program with
  | .ok _ => true
  | .error _ => false

#guard lowers? literalProgram
#guard lowers? erasedProgram
#guard lowers? ctorProjectionProgram
#guard lowers? caseProgram
#guard lowers? directCallProgram
#guard lowers? closureCallProgram
#guard lowers? joinProgram
#guard lowers? scalarBoxProgram
#guard lowers? mutationProgram
#guard lowers? usizeProjectionProgram
#guard lowers? objectMutationProgram
#guard lowers? tagMutationProgram
#guard lowers? defaultCaseProgram
#guard lowers? rcProgram
#guard lowers? persistentRcProgram
#guard lowers? resetReuseProgram
#guard lowers? sharedResetProgram
#guard lowers? deletedProgram
#guard lowers? externalProgram

def literalModule? : Option Module :=
  match lower literalProgram with
  | .ok module => some module
  | .error _ => none

#guard literalModule?.any fun module =>
  module.functions.size == 1 &&
  module.exports == #[`main] &&
  module.runtimeOperations.contains (.literal (.nat 42))

def externalModule? : Option Module :=
  match lower externalProgram with
  | .ok module => some module
  | .error _ => none

#guard externalModule?.any fun module =>
  module.functions.size == 1 &&
  module.imports.any (·.declaration? == some `external)

def scalarIdProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `scalarId #[param x u64Type] u64Type (.code (.return x))] }

def scalarIdModule? : Option Module :=
  match lower scalarIdProgram with
  | .ok module => some module
  | .error _ => none

#guard scalarIdModule?.any fun module =>
  module.imports.isEmpty && module.functions.size == 1

end Fir.Wasm
