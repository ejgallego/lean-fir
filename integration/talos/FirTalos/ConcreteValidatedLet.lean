import FirTalos.ConcreteFinalLcnfTyping

namespace FirTalos.Concrete

open Lean Fir.Wasm Fir.Wasm.Concrete Fir.LeanIR.Impure FirTalos.Correctness

/-- Residual compiler alignment already contains the destination-kind evidence
needed to retain validation after a let. No operation-specific execution or
client-supplied local-kind equation is needed for this static fact. -/
theorem ConcreteStructuredAlignedValidationState.afterLet
    {program : Fir.LeanIR.ImpureProgram} {context : Context} {result : AbiKind}
    {decl : Lean.Compiler.LCNF.LetDecl .impure} {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredAlignedValidationState program context result
      (.let decl continuation)) :
    ConcreteStructuredAlignedValidationState program context result continuation := by
  have alignment : ConcreteResidualLocalAlignment context program (.let decl continuation) := by
    rcases validated with ⟨_, _, _, _, _, _, aligned⟩
    exact aligned
  obtain ⟨_, _, _, _, next⟩ := validated.letContinuation (fun supported =>
    alignment.letHead (supportedLetDeclKind?_effectiveLetValueKind supported))
  exact next

/-- Identify the validator-selected lazy call with a known source declaration
and its effective result kind. Compatibility, destination compilation and
nullary parameters are recovered from validation, not separate admission inputs. -/
theorem ConcreteStructuredAlignedValidationState.lazyCall_of_selected
    {program : Fir.LeanIR.ImpureProgram} {context : Context} {result kind : AbiKind}
    {decl : Lean.Compiler.LCNF.LetDecl .impure} {continuation : Lean.Compiler.LCNF.Code .impure}
    {name : Name} {declaration : Lean.Compiler.LCNF.Decl .impure}
    (validated : ConcreteStructuredAlignedValidationState program context result
      (.let decl continuation))
    (contextProgram : context.program = program)
    (valueEq : decl.value = .fap name #[])
    (found : program.findDecl? name = some declaration)
    (selected : effectiveDeclarationResultKind? declaration = some kind) :
    LazyCacheCallSupported context decl name declaration kind := by
  obtain ⟨actual, actualKind, declaredKind, site⟩ :=
    validated.lazyCacheCallCompilerSite contextProgram valueEq
  have declarationEq : actual = declaration := by
    have h := site.targetEq
    rw [contextProgram, found] at h
    exact (Option.some.inj h).symm
  subst actual
  have kindEq : actualKind = kind := Option.some.inj (site.targetResultEq.symm.trans selected)
  subst actualKind
  exact validated.lazyCacheCallSupported contextProgram site

end FirTalos.Concrete
