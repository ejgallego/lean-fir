import FirTalos.ConcreteStructuredSimulation

/-!
# Residual source validation for the structured W6 simulation

`WasmSupported` validates a declaration from its root, while the structured
simulation relates an arbitrary currently executing code node.  This module
retains the executable validator's residual state at that node: local kinds,
join declarations, case facts, and guarded-sharing facts.

The state is not an execution or translation certificate.  Its sole field is
the actual `supportedCodeWithJoins` Boolean judgment, its root is reconstructed
from `ConcreteSupportedFunction.validatedBodyAt`, and the transition theorems
below are inversions of the executable validator equations.
-/

namespace FirTalos.Concrete

open Fir.Wasm
open Fir.LeanIR.Impure

/-- The exact residual state of source validation at one current LCNF node. -/
structure ConcreteStructuredValidationFocus
    (program : Fir.LeanIR.ImpureProgram)
    (joins : Fir.Wasm.JoinPoints)
    (locals : Fir.Wasm.LocalKinds)
    (expectedResult : Option Fir.Wasm.AbiKind)
    (facts : Fir.Wasm.SupportedCaseFacts)
    (sharing : Fir.Wasm.SupportedSharingFacts)
    (code : Lean.Compiler.LCNF.Code .impure) : Prop where
  supported :
    Fir.Wasm.supportedCodeWithJoins program joins locals expectedResult facts
      sharing code = true

/-- Production validation supplies the root residual state at the active
generated function's exact result ABI. -/
theorem ConcreteSupportedFunction.rootValidation
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction target hosts)
    {functionResult : Fir.Wasm.AbiKind}
    (activeResult : spec.sourceResultKind = functionResult) :
    ∃ rootLocals,
      Fir.Wasm.addSupportedDeclarationParams? program spec.sourceDeclaration =
          some rootLocals ∧
        ConcreteStructuredValidationFocus program [] rootLocals
          (some functionResult) [] [] functionCode := by
  obtain ⟨rootLocals, parameters, supported⟩ :=
    spec.validatedBodyAt activeResult
  exact ⟨rootLocals, parameters, ⟨supported⟩⟩

/-- A validated direct `let` exposes the exact kind inserted into the residual
local row and the guarded-sharing update used for its continuation. -/
theorem ConcreteStructuredValidationFocus.let_eq
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing (.let decl continuation)) :
    ∃ kind,
      Fir.Wasm.supportedLetDeclKind? program locals decl = some kind ∧
        ConcreteStructuredValidationFocus program joins
          (Fir.Wasm.insertLocal locals decl.fvarId kind) expectedResult facts
          (match decl.value with
          | .isShared objectId =>
              Fir.Wasm.insertSupportedSharingFact sharing decl.fvarId objectId
          | _ => Fir.Wasm.eraseSupportedSharingFact sharing decl.fvarId)
          continuation := by
  have supported := validated.supported
  simp only [Fir.Wasm.supportedCodeWithJoins] at supported
  cases selected : Fir.Wasm.supportedLetDeclKind? program locals decl with
  | none =>
      rw [selected] at supported
      simp at supported
  | some kind =>
      rw [selected] at supported
      change Fir.Wasm.supportedCodeWithJoins program joins
        (Fir.Wasm.insertLocal locals decl.fvarId kind) expectedResult facts
        (match decl.value with
        | .isShared objectId =>
            Fir.Wasm.insertSupportedSharingFact sharing decl.fvarId objectId
        | _ => Fir.Wasm.eraseSupportedSharingFact sharing decl.fvarId)
        continuation = true at supported
      exact ⟨kind, rfl, ⟨supported⟩⟩

/-- Persistent ownership increments are erased by lowering and preserve the
complete residual validator state. -/
theorem ConcreteStructuredValidationFocus.incPersistent
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {objectId : Lean.FVarId}
    {amount : Nat}
    {check : Bool}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing
      (.inc objectId amount check true continuation)) :
    ConcreteStructuredValidationFocus program joins locals expectedResult facts
      sharing continuation := by
  have supported := validated.supported
  simp only [Fir.Wasm.supportedCodeWithJoins] at supported
  exact ⟨by simpa using supported⟩

/-- Persistent ownership decrements preserve the same residual validator
state. -/
theorem ConcreteStructuredValidationFocus.decPersistent
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {objectId : Lean.FVarId}
    {amount : Nat}
    {check : Bool}
    {objectFields? : Option Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing
      (.dec objectId amount check true objectFields? continuation)) :
    ConcreteStructuredValidationFocus program joins locals expectedResult facts
      sharing continuation := by
  have supported := validated.supported
  simp only [Fir.Wasm.supportedCodeWithJoins] at supported
  exact ⟨by simpa using supported⟩

/-- Both persistent and ordinary increments retain the validator state at
their continuation; the ordinary branch additionally discharges its local
kind guard inside the executable judgment. -/
theorem ConcreteStructuredValidationFocus.incContinuation
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {objectId : Lean.FVarId} {amount : Nat} {check persistent : Bool}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing
      (.inc objectId amount check persistent continuation)) :
    ConcreteStructuredValidationFocus program joins locals expectedResult facts
      sharing continuation := by
  have supported := validated.supported
  cases persistent with
  | false =>
      simp [Fir.Wasm.supportedCodeWithJoins, Bool.and_eq_true] at supported
      exact ⟨supported.2⟩
  | true =>
      simp [Fir.Wasm.supportedCodeWithJoins] at supported
      exact ⟨supported⟩

/-- Both decrement modes retain the same validator state at their
continuation. -/
theorem ConcreteStructuredValidationFocus.decContinuation
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {objectId : Lean.FVarId} {amount : Nat} {check persistent : Bool}
    {objectFields? : Option Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing
      (.dec objectId amount check persistent objectFields? continuation)) :
    ConcreteStructuredValidationFocus program joins locals expectedResult facts
      sharing continuation := by
  have supported := validated.supported
  cases persistent with
  | false =>
      simp [Fir.Wasm.supportedCodeWithJoins, Bool.and_eq_true] at supported
      exact ⟨supported.2⟩
  | true =>
      simp [Fir.Wasm.supportedCodeWithJoins] at supported
      exact ⟨supported⟩

/-- Object-field writes retain the residual state after their executable kind
guards have succeeded. -/
theorem ConcreteStructuredValidationFocus.osetContinuation
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {objectId : Lean.FVarId} {fieldIndex : Nat}
    {arg : Lean.Compiler.LCNF.Arg .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing
      (.oset objectId fieldIndex arg continuation)) :
    ConcreteStructuredValidationFocus program joins locals expectedResult facts
      sharing continuation := by
  have supported := validated.supported
  simp only [Fir.Wasm.supportedCodeWithJoins] at supported
  have continuationSupported :
      Fir.Wasm.supportedCodeWithJoins program joins locals expectedResult facts
        sharing continuation = true := by
    cases continuationFound : Fir.Wasm.supportedCodeWithJoins program joins
        locals expectedResult facts sharing continuation with
    | false => split at supported <;> simp_all
    | true => rfl
  exact ⟨continuationSupported⟩

/-- `USize` field writes preserve the residual validator state. -/
theorem ConcreteStructuredValidationFocus.usetContinuation
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {objectId : Lean.FVarId} {fieldIndex : Nat} {fieldId : Lean.FVarId}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing
      (.uset objectId fieldIndex fieldId continuation)) :
    ConcreteStructuredValidationFocus program joins locals expectedResult facts
      sharing continuation := by
  have supported := validated.supported
  simp only [Fir.Wasm.supportedCodeWithJoins, Bool.and_eq_true] at supported
  exact ⟨supported.2⟩

/-- Packed scalar field writes preserve the residual validator state. -/
theorem ConcreteStructuredValidationFocus.ssetContinuation
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {objectId : Lean.FVarId} {byteOffset fieldIndex : Nat}
    {fieldId : Lean.FVarId} {type : Lean.Expr}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing
      (.sset objectId byteOffset fieldIndex fieldId type continuation)) :
    ConcreteStructuredValidationFocus program joins locals expectedResult facts
      sharing continuation := by
  have supported := validated.supported
  simp only [Fir.Wasm.supportedCodeWithJoins] at supported
  have continuationSupported :
      Fir.Wasm.supportedCodeWithJoins program joins locals expectedResult facts
        sharing continuation = true := by
    cases continuationFound : Fir.Wasm.supportedCodeWithJoins program joins
        locals expectedResult facts sharing continuation with
    | false => split at supported <;> simp_all
    | true => rfl
  exact ⟨continuationSupported⟩

/-- Constructor-tag writes preserve the residual validator state. -/
theorem ConcreteStructuredValidationFocus.setTagContinuation
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {objectId : Lean.FVarId} {tag : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing (.setTag objectId tag continuation)) :
    ConcreteStructuredValidationFocus program joins locals expectedResult facts
      sharing continuation := by
  have supported := validated.supported
  simp only [Fir.Wasm.supportedCodeWithJoins, Bool.and_eq_true] at supported
  exact ⟨supported.2⟩

/-- Explicit deletion preserves the residual validator state. -/
theorem ConcreteStructuredValidationFocus.delContinuation
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {objectId : Lean.FVarId}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing (.del objectId continuation)) :
    ConcreteStructuredValidationFocus program joins locals expectedResult facts
      sharing continuation := by
  have supported := validated.supported
  simp only [Fir.Wasm.supportedCodeWithJoins, Bool.and_eq_true] at supported
  exact ⟨supported.2⟩

/-- Return validation identifies the residual local kind and the exact
compiler-level compatibility check against the active result ABI. -/
theorem ConcreteStructuredValidationFocus.return_eq
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expected : Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {result : Lean.FVarId}
    (validated : ConcreteStructuredValidationFocus program joins locals
      (some expected) facts sharing (.return result)) :
    ∃ actual,
      Fir.Wasm.findLocalKind? locals result = some actual ∧
        actual.leanCompatible expected = true := by
  have supported := validated.supported
  cases actualFound : Fir.Wasm.findLocalKind? locals result with
  | none =>
      simp [Fir.Wasm.supportedCodeWithJoins, actualFound] at supported
  | some actual =>
      refine ⟨actual, rfl, ?_⟩
      simpa [Fir.Wasm.supportedCodeWithJoins, actualFound] using supported

/-- A validated jump retains the selected join declaration, result
compatibility, and the complete path-sensitive argument check. -/
theorem ConcreteStructuredValidationFocus.jump_eq
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {fvarId : Lean.FVarId}
    {args : Array (Lean.Compiler.LCNF.Arg .impure)}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing (.jmp fvarId args)) :
    ∃ decl,
      Fir.Wasm.findJoinPoint? joins fvarId = some decl ∧
        Fir.Wasm.resultKindCompatible
            (Fir.Wasm.abiValueKind? decl.type) expectedResult = true ∧
        Fir.Wasm.supportedJumpArgs locals facts sharing decl args = true := by
  have supported := validated.supported
  simp only [Fir.Wasm.supportedCodeWithJoins] at supported
  cases found : Fir.Wasm.findJoinPoint? joins fvarId with
  | none =>
      simp [found] at supported
  | some decl =>
      refine ⟨decl, rfl, ?_⟩
      simpa [found, Bool.and_eq_true] using supported

/-- Introducing a join validates both its body under the extended join/local
state and its continuation under the extended join state. -/
theorem ConcreteStructuredValidationFocus.join_eq
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {decl : Lean.Compiler.LCNF.FunDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing (.jp decl continuation)) :
    ∃ bodyLocals,
      decl.params.foldlM (init := locals) (fun locals param => do
          let kind ← Fir.Wasm.joinParamAbiKind? decl param
          some (Fir.Wasm.insertLocal locals param.fvarId kind)) =
          some bodyLocals ∧
        Fir.Wasm.abiTypeKnown decl.type = true ∧
        Fir.Wasm.resultKindCompatible (Fir.Wasm.abiValueKind? decl.type)
            expectedResult = true ∧
        ConcreteStructuredValidationFocus program
          ((decl.fvarId, decl) :: joins) bodyLocals
          (Fir.Wasm.abiValueKind? decl.type) [] [] decl.value ∧
        ConcreteStructuredValidationFocus program
          ((decl.fvarId, decl) :: joins) locals expectedResult facts sharing
          continuation := by
  have supported := validated.supported
  simp only [Fir.Wasm.supportedCodeWithJoins] at supported
  cases bodyFound : decl.params.foldlM (init := locals)
      (fun locals param => do
        let kind ← Fir.Wasm.joinParamAbiKind? decl param
        some (Fir.Wasm.insertLocal locals param.fvarId kind)) with
  | none =>
      rw [bodyFound] at supported
      simp at supported
  | some bodyLocals =>
      rw [bodyFound] at supported
      simp only [Bool.and_eq_true] at supported
      exact ⟨bodyLocals, rfl,
        supported.1.1.1, supported.1.1.2,
        ⟨supported.1.2⟩, ⟨supported.2⟩⟩

/-- Case validation exposes the discriminator mode and the executable
all-alternatives judgment from which the selected branch is recovered. -/
theorem ConcreteStructuredValidationFocus.cases_eq
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {cases : Lean.Compiler.LCNF.Cases .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing (.cases cases)) :
    ∃ discrKind mode,
      Fir.Wasm.findLocalKind? locals cases.discr = some discrKind ∧
        Fir.Wasm.supportedCaseDiscriminatorMode? discrKind = some mode ∧
        Fir.Wasm.abiTypeKnown cases.resultType = true ∧
        Fir.Wasm.resultKindCompatible
            (Fir.Wasm.abiValueKind? cases.resultType) expectedResult = true ∧
        Fir.Wasm.supportedAltsWithJoins program joins locals expectedResult
          facts sharing mode cases.discr cases.alts.toList = true := by
  have supported := validated.supported
  simp only [Fir.Wasm.supportedCodeWithJoins] at supported
  simp only [Bool.and_eq_true] at supported
  cases discrFound : Fir.Wasm.findLocalKind? locals cases.discr with
  | none =>
      have impossible := supported.2
      simp [discrFound] at impossible
  | some discrKind =>
      cases modeFound :
          Fir.Wasm.supportedCaseDiscriminatorMode? discrKind with
      | none =>
          have impossible := supported.2
          simp [discrFound, modeFound] at impossible
      | some mode =>
          refine ⟨discrKind, mode, rfl, modeFound,
            supported.1.1, supported.1.2, ?_⟩
          simpa [discrFound, modeFound] using supported.2

/-- A validated constructor alternative selected from a validated case chain
inherits the inserted discriminator fact used by guarded joins. -/
theorem ConcreteStructuredValidationFocus.constructorAlt
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {cases : Lean.Compiler.LCNF.Cases .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing (.cases cases))
    {info : Lean.Compiler.LCNF.CtorInfo}
    {selected : Lean.Compiler.LCNF.Code .impure}
    (member : Lean.Compiler.LCNF.Alt.ctorAlt info selected ∈ cases.alts) :
    ∃ mode,
      Fir.Wasm.caseConstructorTagFits mode info = true ∧
        ConcreteStructuredValidationFocus program joins locals expectedResult
          (Fir.Wasm.insertSupportedCaseFact facts cases.discr info.cidx) sharing
          selected := by
  obtain ⟨discrKind, mode, _discrFound, _modeFound, _resultKnown,
      _resultCompatible, alternatives⟩ := validated.cases_eq
  have selectedSupported := Fir.Wasm.supportedAltWithJoins_of_mem alternatives
    (by simpa using member)
  simp only [Fir.Wasm.supportedAltWithJoins] at selectedSupported
  simp only [Bool.and_eq_true] at selectedSupported
  exact ⟨mode, selectedSupported.1, ⟨selectedSupported.2⟩⟩

/-- A validated default alternative erases any stale discriminator fact. -/
theorem ConcreteStructuredValidationFocus.defaultAlt
    {program : Fir.LeanIR.ImpureProgram}
    {joins : Fir.Wasm.JoinPoints}
    {locals : Fir.Wasm.LocalKinds}
    {expectedResult : Option Fir.Wasm.AbiKind}
    {facts : Fir.Wasm.SupportedCaseFacts}
    {sharing : Fir.Wasm.SupportedSharingFacts}
    {cases : Lean.Compiler.LCNF.Cases .impure}
    (validated : ConcreteStructuredValidationFocus program joins locals
      expectedResult facts sharing (.cases cases))
    {selected : Lean.Compiler.LCNF.Code .impure}
    (member : Lean.Compiler.LCNF.Alt.default selected ∈ cases.alts) :
    ConcreteStructuredValidationFocus program joins locals expectedResult
      (Fir.Wasm.eraseSupportedCaseFact facts cases.discr) sharing selected := by
  obtain ⟨_discrKind, mode, _discrFound, _modeFound, _resultKnown,
      _resultCompatible, alternatives⟩ := validated.cases_eq
  have selectedSupported := Fir.Wasm.supportedAltWithJoins_of_mem alternatives
    (by simpa using member)
  simp only [Fir.Wasm.supportedAltWithJoins] at selectedSupported
  exact ⟨selectedSupported⟩

end FirTalos.Concrete
