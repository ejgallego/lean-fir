import FirTalos.ConcreteSourceValidation
import Fir.Wasm.Examples

/-!
Executable specification-sensitivity checks, not proof witnesses. Keep fixture
imports out of the reusable validation and supported-export modules.

The dictionary fixture deliberately admits production lowering after losing
local closure provenance. A successful validator must not be confused with
the stronger `WasmSupported` gate used by the proof interface.
-/

open Fir.Wasm

#guard validateSupported dictionaryPureUnderApplyProgram matches .ok ()
#guard lowerSupported dictionaryPureUnderApplyProgram matches .ok _
#guard !closureFlowSafeProgram dictionaryPureUnderApplyProgram
#guard !supportedProgram dictionaryPureUnderApplyProgram
