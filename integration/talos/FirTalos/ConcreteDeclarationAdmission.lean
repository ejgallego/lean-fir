import FirTalos.ConcreteDeclarationNames
import FirTalos.ConcreteDeclarationValidation
import FirTalos.Correctness.Exports

namespace FirTalos.Concrete

/-- A successfully lowered and symbolically validated module has unique source
declaration names. The name population proof retains duplicates; the actual
validator, rather than a caller-selected certificate, excludes them. -/
theorem namesUnique_of_lower_validateModule
    {program : Fir.LeanIR.ImpureProgram} {source : Fir.Wasm.Module}
    (lowered : Fir.Wasm.lower program = .ok source)
    (validated : Fir.Wasm.validateModule source = .ok ()) :
    program.NamesUnique :=
  namesUnique_of_lower_namesNodup lowered
    (declarationNames_nodup_of_validateModule validated)

/-- The production lowering/adaptation equations already include the complete
declaration-name check. No extra source well-formedness wrapper is required. -/
theorem namesUnique_of_supportedPipeline
    {program : Fir.LeanIR.ImpureProgram} {source : Fir.Wasm.Module}
    {target : AdaptedModule}
    (lowered : Fir.Wasm.lowerSupported program = .ok source)
    (adapted : adapt source = .ok target) :
    program.NamesUnique :=
  namesUnique_of_lower_validateModule
    (LazyCacheGeneratedEnvironment.lower_of_lowerSupported lowered)
    (Correctness.adapt_source_valid adapted)

end FirTalos.Concrete
