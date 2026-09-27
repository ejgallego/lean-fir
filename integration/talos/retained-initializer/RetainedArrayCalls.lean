import RetainedDeclarations
import FirTalos.ConcreteArrayExternalCall
import FirTalos.TrustAuditCore

open Lean Lean.Compiler Fir.Wasm Fir.LeanIR.Impure Fir.Wasm.Concrete
open FirTalos (AdaptedModule LabelContext ExternalOperation)
open FirTalos.Concrete FirTalos.Correctness

namespace RetainedInitializer

noncomputable section

/-! Call admission is extracted from the checked initializer itself. The two
local-row facts and the capacity lookup are entry obligations, not copied
LCNF syntax or a new program-specific execution invariant. -/

def capacityId : FVarId :=
  match RetainedRC2.initializer.value with
  | .code (.let _ (.let capacity _)) => capacity.fvarId
  | _ => default

def mkEmptySite : LCNF.LetDecl .impure :=
  match RetainedRC2.initializer.value with
  | .code (.let _ (.let _ (.let site _))) => site
  | _ => default

def mkEmptyContinuation : LCNF.Code .impure :=
  match RetainedRC2.initializer.value with
  | .code (.let _ (.let _ (.let _ continuation))) => continuation
  | _ => default

def afterMkEmpty (runtime : RuntimeState) : RuntimeState :=
  semanticArrayResult { runtime with trace := runtime.trace.push {
    name := `Array.mkEmpty, args := #[.erased, .object (.tagged 5)],
    result := .object (.heap runtime.nextLocation) } } #[] 5

/-- Closed ABI classification only: upstream `Expr` equality is opaque. No
execution or heap property is entrusted to native evaluation. -/
theorem mkEmptyAbiTypes :
    abiKind? (.const `lcErased []) = .ok (some .erased) ∧
    abiKind? (.const `tobj []) = .ok (some .tobject) ∧
    abiKind? (.const `obj []) = .ok (some .object) := by
  have comparisons :
      ((Expr.const `lcErased [] == LCNF.ImpureType.object) = false) ∧
      ((Expr.const `lcErased [] == LCNF.ImpureType.tagged) = false) ∧
      ((Expr.const `lcErased [] == LCNF.ImpureType.tobject) = false) ∧
      ((Expr.const `lcErased [] == LCNF.ImpureType.erased) = true) ∧
      ((Expr.const `tobj [] == LCNF.ImpureType.object) = false) ∧
      ((Expr.const `tobj [] == LCNF.ImpureType.tagged) = false) ∧
      ((Expr.const `tobj [] == LCNF.ImpureType.tobject) = true) ∧
      ((Expr.const `obj [] == LCNF.ImpureType.object) = true) := by native_decide
  rcases comparisons with ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp [abiKind?, h1, h2, h3, h4, h5, h6, h7, h8, Pure.pure, Except.pure]

/-- The actual captured call widens `tagged` to `tobject`; it does not narrow
an arbitrary object-family carrier. The result is precisely an Array object. -/
def mkEmptyCallShape
    (context : Context) (programEq : context.program = RetainedRC2.program)
    (externals : ExternalImpl) (contract : FreshArrayExternalContract externals)
    (runtime : RuntimeState) (env : Env)
    (capacityKind : findLocalKind? context.localKinds capacityId = some .tagged)
    (resultKind : findLocalKind? context.localKinds mkEmptySite.fvarId = some .object)
    (capacityValue : lookupValue env capacityId = .ok (.object (.tagged 5))) :
    ExternalCallShape context externals runtime env mkEmptySite
      (afterMkEmpty runtime) (.object (.heap runtime.nextLocation)) where
  name := `Array.mkEmpty
  args := #[.erased, .fvar capacityId]
  rawArgumentCode := [.i32Const .erased 0, .localGet capacityId]
  argumentCode := [.i32Const .erased 0, .localGet capacityId]
  argumentKinds := #[.erased, .tagged]
  parameterKinds := #[.erased, .tobject]
  argumentsRefine := by simp [kindsRefine, AbiKind.refines]
  semanticArgs := #[.erased, .object (.tagged 5)]
  declaration := mkEmptyDecl
  resultKind := .object
  response := semanticEmptyArrayResponse runtime 5
  valueEq := rfl
  nonempty := rfl
  declarationFound := by rw [programEq]; exact mkEmptyDecl.findDecl
  declarationExternal := ⟨_, rfl⟩
  valueKind := by
    change checkedAbiKind (.const `obj []) = .ok .object
    simp [checkedAbiKind, abiKind, mkEmptyAbiTypes.2.2,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  argumentsCompiled := by
    simp [compileArgs, compileArg, capacityKind, Bind.bind, Except.bind,
      Pure.pure, Except.pure]
  declarationArgumentsCompiled := by
    simp [compileDeclarationArguments, compileDeclarationArgument,
      checkedDeclarationParamKind, erasedOnlyParameter, mkEmptyDecl,
      checkedAbiKind?, mkEmptyAbiTypes.1, mkEmptyAbiTypes.2.1,
      compileArg, capacityKind, Bind.bind, Except.bind, Pure.pure, Except.pure,
      AbiKind.leanCompatible, AbiKind.refines, AbiKind.isObjectLike]
  argumentsEvaluated := by
    have found : lookup env capacityId = some (.object (.tagged 5)) := by
      cases h : lookup env capacityId <;> simpa [lookupValue, h] using capacityValue
    simp [evalArgs, evalArg, found, Bind.bind, Except.bind, Pure.pure, Except.pure]
  parameterSignature := by
    simp [ExternalTypes.signature, resultKinds, mkEmptyDecl, mkEmptyAbiTypes.1,
      mkEmptyAbiTypes.2.1, mkEmptyAbiTypes.2.2, abiKind,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  resultCompiled := by simp [getLocal, resultKind]
  semanticCalled := by
    exact contract.mkEmpty runtime (mkEmptyDecl.params.map (·.type)) mkEmptyDecl.type 5
  nextRuntimeEq := by
    simp [afterMkEmpty, semanticExternalRuntimeAfter, semanticEmptyArrayResponse,
      arrayExternalResponse, semanticArrayResult, semanticExternalEvent,
      declarationExternalRequest, mkEmptyDecl]
  sourceValueEq := rfl

/-- Three source transitions and the compiler-selected argument prefix followed
by call/bind return to the actual captured continuation. This starts at the
`mkEmpty` let, not at export entry; earlier literal steps and the later push
and cache publication remain separate composition obligations. -/
theorem mkEmpty_stage_call_bind
    {context : Context} (programEq : context.program = RetainedRC2.program)
    {rootCode : LCNF.Code .impure} {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function} {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec : ConcreteSupportedFunction RetainedRC2.program context rootCode
      sourceModule sourceFunction targetModule hosts)
    {externals : ExternalImpl} (contract : FreshArrayExternalContract externals)
    {runtime : RuntimeState} {env : Env} {labels : LabelContext}
    {store : Wasm.Store Host} {locals : Wasm.Locals} {code : Wasm.Program}
    {witness : RefinementWitness} {source : MachineState}
    {target : StructuredWasmState Host} {remainingBytes : Nat}
    (capacityKind : findLocalKind? context.localKinds capacityId = some .tagged)
    (resultKind : findLocalKind? context.localKinds mkEmptySite.fvarId = some .object)
    (capacityValue : lookupValue env capacityId = .ok (.object (.tagged 5)))
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels runtime env (.let mkEmptySite mkEmptyContinuation) store locals code
      witness source target)
    (handler : ∀ request,
      ConcreteExternalRequestRel witness request
        (declarationExternalRequest mkEmptyDecl #[.erased, .object (.tagged 5)]) →
      EmptyArrayHandlerAt store.host.externals request store.host.runtime 5)
    (budget : store.host.runtime.heap.AddressSpaceBudget remainingBytes)
    (fits : residentArrayAllocationBytes 5 ≤ remainingBytes) :
    ∃ prefixLength nextStore nextWitness sourceAfter targetAfter resumedLocals rest,
      ExecSteps externals 3 source sourceAfter ∧
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
        (prefixLength + 2) target targetAfter ∧
      ConcreteStructuredCodeFocus context sourceModule sourceFunction labels
        (afterMkEmpty runtime)
        (bind env mkEmptySite.fvarId (.object (.heap runtime.nextLocation)))
        mkEmptyContinuation nextStore resumedLocals rest nextWitness
        sourceAfter targetAfter ∧
      nextStore.host.runtime.heap.AddressSpaceBudget
        (remainingBytes - residentArrayAllocationBytes 5) ∧
      sourceAfter.joins = source.joins ∧ sourceAfter.frames = source.frames ∧
      targetAfter.frames = target.frames := by
  let site := mkEmptyCallShape context programEq externals contract runtime env
    capacityKind resultKind capacityValue
  obtain ⟨physicalArgs, operation, resolvedKind, targetImport, callIndex, resultIndex,
      targetArguments, rest, sourceStaged, targetStaged, staged, argumentPath, control⟩ :=
    related.advance_external_stage_of_shape spec site localsAligned
  have resolved : resolvedKind = .object := by
    have h := congrArg (fun results : Array AbiKind => results[0]?)
      control.resultSignature
    simpa [control.parameterSignature, site, mkEmptyCallShape] using h.symm
  obtain ⟨concreteArgs, decoded, requestRelated⟩ := control.decodeRequest
  have requestEq : operation.request site.semanticArgs =
      declarationExternalRequest mkEmptyDecl #[.erased, .object (.tagged 5)] := by
    simp [ExternalOperation.request, declarationExternalRequest,
      control.operationName, control.operationMatches.paramTypes,
      control.operationMatches.resultType, site, mkEmptyCallShape, mkEmptyDecl]
  obtain ⟨nextStore, nextWitness, physicalResult, sourceAfter, targetAfter, updated,
      resumedLocals, steps, path, _set, _resumed, focus, residual, joins,
      frames, targetFrames⟩ :=
    control.advance_emptyArray_bind (capacity := 5) rfl rfl
      (fun args decode => by
        have same : args = concreteArgs := Except.ok.inj (decode.symm.trans decoded)
        subst args
        exact handler _ (by simpa [resolved, requestEq] using requestRelated))
      budget fits
  exact ⟨targetArguments.length, nextStore, nextWitness, sourceAfter, targetAfter,
    resumedLocals, rest, .step staged steps, argumentPath.trans path, focus, residual,
    joins, frames, targetFrames⟩

end

end RetainedInitializer

open Lean.Elab.Command in
run_cmd do
  FirTalos.TrustAudit.check `RetainedInitializer.mkEmpty_stage_call_bind
    (FirTalos.TrustAudit.standardAxioms ++ #[
      "RetainedInitializer.mkEmptyAbiTypes._native.native_decide.ax_1_1",
      "_private.Fir.Wasm.Concrete.Memory.0.Fir.Wasm.Concrete.LinearMemory.assembleByte32._native.bv_decide.ax_1_6"])
