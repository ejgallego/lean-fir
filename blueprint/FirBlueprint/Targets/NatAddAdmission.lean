import FirBlueprint.Targets.NatAdd
import FirTalos.ConcreteStructuredSimulation

open private validationExternals from Fir.Validation.LCNF

namespace FirBlueprint.Targets

open Fir.LeanIR.Impure Fir.Wasm Fir.Wasm.Concrete FirTalos.Concrete

/-- Connect the real Nat-addition handler to production natural-result
admission. The caller supplies the existing representation-independent call
shape, natural argument decoding and ABI alignment. The canonical response,
runtime/result equalities and exact result allocation cost are derived here.
Constructing these remaining inputs from validation is a separate open node. -/
theorem validation_natAdd_admission
    {context : Fir.Wasm.Context} {before after : RuntimeState} {env : Env}
    {decl : Lean.Compiler.LCNF.LetDecl .impure} {value : Value}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (site : ExternalCallShape context validationExternals before env decl after value)
    {left right : Nat}
    (inputs : NatAddInputs
      (declarationExternalRequest site.declaration site.semanticArgs) before left right)
    (resultKind : site.resultKind = .tobject)
    (argumentKinds : site.parameterKinds = site.argumentKinds) :
    PureNaturalExternalSupported context validationExternals before env
      decl continuation after value (naturalAllocationBytes (left + right)) := by
  have called := (validation_natAdd inputs).1
  have response : site.response = semanticNaturalExternalResponse before (left + right) :=
    Except.ok.inj (site.semanticCalled.symm.trans called)
  have declarationName : site.declaration.name = site.name := by
    have matching := (Array.find?_eq_some_iff_getElem.mp site.declarationFound).1
    simpa [Fir.LeanIR.Program.findDecl?] using matching
  have name : site.name = ``Nat.add := declarationName.symm.trans inputs.1
  exact .intro site.name site.args site.rawArgumentCode site.argumentCode
    site.argumentKinds site.semanticArgs site.declaration (left + right)
    site.valueEq (by simpa [name] using PureNaturalExternalName.natAdd)
    site.nonempty site.declarationFound site.declarationExternal
    (by simpa [resultKind] using site.valueKind)
    site.argumentsCompiled site.declarationArgumentsCompiled site.argumentsEvaluated
    (by simpa [resultKind, argumentKinds] using site.parameterSignature)
    (by simpa [resultKind] using site.resultCompiled) called
    (by simpa [response] using site.nextRuntimeEq)
    (by simpa [response] using site.sourceValueEq) rfl

end FirBlueprint.Targets
