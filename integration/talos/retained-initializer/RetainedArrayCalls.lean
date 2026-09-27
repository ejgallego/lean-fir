import RetainedDeclarations
import FirTalos.ConcreteArrayExternalCall
import FirTalos.ConcreteLiteralPrefix
import FirTalos.ConcreteBoxPrefix
import FirTalos.ConcreteArrayPushCall
import FirTalos.ConcretePublicationBind
import FirTalos.ConcreteLazyBodyEntry
import FirTalos.ConcreteGeneratedLocals
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

def initializerBody : LCNF.Code .impure :=
  match RetainedRC2.initializer.value with
  | .code code => code
  | _ => default

def scalarSite : LCNF.LetDecl .impure :=
  match initializerBody with
  | .let site _ => site
  | _ => default

def capacitySite : LCNF.LetDecl .impure :=
  match initializerBody with
  | .let _ (.let site _) => site
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

def boxSite : LCNF.LetDecl .impure :=
  match mkEmptyContinuation with
  | .let site _ => site
  | _ => default

def pushCode : LCNF.Code .impure :=
  match mkEmptyContinuation with
  | .let _ continuation => continuation
  | _ => default

def pushSite : LCNF.LetDecl .impure :=
  match pushCode with
  | .let site _ => site
  | _ => default

def pushContinuation : LCNF.Code .impure :=
  match pushCode with
  | .let _ continuation => continuation
  | _ => default

def arrayEntry (runtime : RuntimeState) : RuntimeState :=
  { runtime with trace := runtime.trace.push {
    name := `Array.mkEmpty, args := #[.erased, .object (.tagged 5)],
    result := .object (.heap runtime.nextLocation) } }

def afterPush (runtime : RuntimeState) : RuntimeState :=
  semanticArrayResult { arrayEntry runtime with trace := (arrayEntry runtime).trace.push {
    name := `Array.push,
    args := #[.erased, .object (.heap runtime.nextLocation), .object (.tagged 0)],
    result := .object (.heap runtime.nextLocation) } } #[.object (.tagged 0)] 5

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

/-- The second external call also uses directional parameter refinement:
the producer's precise tagged box is consumed at the declared tobj parameter. -/
def pushCallShape
    (context : Context) (programEq : context.program = RetainedRC2.program)
    (externals : ExternalImpl) (contract : FreshArrayExternalContract externals)
    (runtime : RuntimeState) (env : Env)
    (arrayKind : findLocalKind? context.localKinds mkEmptySite.fvarId = some .object)
    (boxKind : findLocalKind? context.localKinds boxSite.fvarId = some .tagged)
    (resultKind : findLocalKind? context.localKinds pushSite.fvarId = some .object)
    (arrayValue : lookup env mkEmptySite.fvarId = some (.object (.heap runtime.nextLocation)))
    (boxValue : lookup env boxSite.fvarId = some (.object (.tagged 0))) :
    ExternalCallShape context externals (afterMkEmpty runtime) env pushSite
      (afterPush runtime) (.object (.heap runtime.nextLocation)) where
  name := `Array.push
  args := #[.erased, .fvar mkEmptySite.fvarId, .fvar boxSite.fvarId]
  rawArgumentCode := [.i32Const .erased 0, .localGet mkEmptySite.fvarId, .localGet boxSite.fvarId]
  argumentCode := [.i32Const .erased 0, .localGet mkEmptySite.fvarId, .localGet boxSite.fvarId]
  argumentKinds := #[.erased, .object, .tagged]
  parameterKinds := #[.erased, .object, .tobject]
  argumentsRefine := by simp [kindsRefine, AbiKind.refines]
  semanticArgs := #[.erased, .object (.heap runtime.nextLocation), .object (.tagged 0)]
  declaration := pushDecl
  resultKind := .object
  response := arrayExternalResponse
    (semanticArrayResult (arrayEntry runtime) #[.object (.tagged 0)] 5)
    (.object (.heap runtime.nextLocation))
  valueEq := rfl
  nonempty := rfl
  declarationFound := by rw [programEq]; exact pushDecl.findDecl
  declarationExternal := ⟨_, rfl⟩
  valueKind := by
    change checkedAbiKind (.const `obj []) = .ok .object
    simp [checkedAbiKind, abiKind, mkEmptyAbiTypes.2.2,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  argumentsCompiled := by
    simp [compileArgs, compileArg, arrayKind, boxKind, Bind.bind, Except.bind,
      Pure.pure, Except.pure]
  declarationArgumentsCompiled := by
    simp [compileDeclarationArguments, compileDeclarationArgument,
      checkedDeclarationParamKind, erasedOnlyParameter, pushDecl,
      checkedAbiKind?, mkEmptyAbiTypes.1, mkEmptyAbiTypes.2.1, mkEmptyAbiTypes.2.2,
      compileArg, arrayKind, boxKind, Bind.bind, Except.bind, Pure.pure, Except.pure,
      AbiKind.leanCompatible, AbiKind.refines, AbiKind.isObjectLike]
  argumentsEvaluated := by
    simp [evalArgs, evalArg, arrayValue, boxValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
  parameterSignature := by
    simp [ExternalTypes.signature, resultKinds, pushDecl, mkEmptyAbiTypes.1,
      mkEmptyAbiTypes.2.1, mkEmptyAbiTypes.2.2, abiKind,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  resultCompiled := by simp [getLocal, resultKind]
  semanticCalled := by
    exact contract.pushFreshTagged (arrayEntry runtime)
      (pushDecl.params.map (·.type)) pushDecl.type 5 0 (by decide)
  nextRuntimeEq := by
    simp [afterPush, afterMkEmpty, arrayEntry, semanticExternalRuntimeAfter,
      arrayExternalResponse, semanticArrayResult, semanticExternalEvent,
      declarationExternalRequest, pushDecl]
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
      targetAfter.frames = target.frames ∧
      nextStore.host.externals = store.host.externals ∧
      RuntimeStepTransports runtime (afterMkEmpty runtime) store nextStore witness nextWitness := by
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
      frames, targetFrames, externalsEq, transports⟩ :=
    control.advance_emptyArray_bind (capacity := 5) rfl rfl
      (fun args decode => by
        have same : args = concreteArgs := Except.ok.inj (decode.symm.trans decoded)
        subst args
        exact handler _ (by simpa [resolved, requestEq] using requestRelated))
      budget fits
  exact ⟨targetArguments.length, nextStore, nextWitness, sourceAfter, targetAfter,
    resumedLocals, rest, .step staged steps, argumentPath.trans path, focus, residual,
    joins, frames, targetFrames, externalsEq, transports⟩

/-- The actual push call executes with reconstructed receiver/element words.
The deployment law is restricted to the named three-argument push request. -/
theorem push_stage_call_bind
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
    (arrayKind : findLocalKind? context.localKinds mkEmptySite.fvarId = some .object)
    (boxKind : findLocalKind? context.localKinds boxSite.fvarId = some .tagged)
    (resultKind : findLocalKind? context.localKinds pushSite.fvarId = some .object)
    (arrayValue : lookup env mkEmptySite.fvarId = some (.object (.heap runtime.nextLocation)))
    (boxValue : lookup env boxSite.fvarId = some (.object (.tagged 0)))
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction labels
      (afterMkEmpty runtime) env pushCode store locals code witness source target)
    (handler : ∀ request address word,
      witness.locations.lookup? runtime.nextLocation = some address →
      ValueRel witness .tobject (.word32 word) (.object (.tagged 0)) →
      request.name = `Array.push →
      request.args = #[.word32 Word32.zero, .word32 address, .word32 word] →
      ArrayPushInPlaceHandlerAt store.host.externals request store.host.runtime address word)
    (budget : store.host.runtime.heap.AddressSpaceBudget remainingBytes) :
    ∃ prefixLength nextStore sourceAfter targetAfter resumedLocals rest,
      ExecSteps externals 3 source sourceAfter ∧
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
        (prefixLength + 2) target targetAfter ∧
      ConcreteStructuredCodeFocus context sourceModule sourceFunction labels
        (afterPush runtime) (bind env pushSite.fvarId (.object (.heap runtime.nextLocation)))
        pushContinuation nextStore resumedLocals rest witness sourceAfter targetAfter ∧
      nextStore.host.runtime.heap.AddressSpaceBudget remainingBytes ∧
      sourceAfter.joins = source.joins ∧ sourceAfter.frames = source.frames ∧
      targetAfter.frames = target.frames ∧
      nextStore.host.externals = store.host.externals ∧
      RuntimeStepTransports (afterMkEmpty runtime) (afterPush runtime)
        store nextStore witness witness := by
  let site := pushCallShape context programEq externals contract runtime env
    arrayKind boxKind resultKind arrayValue boxValue
  change ConcreteStructuredCodeFocus _ _ _ _ _ _ (.let pushSite pushContinuation)
    _ _ _ _ _ _ at related
  obtain ⟨physicalArgs, operation, resolvedKind, targetImport, callIndex, resultIndex,
      targetArguments, rest, sourceStaged, targetStaged, staged, argumentPath, control⟩ :=
    related.advance_external_stage_of_shape spec site spec.localsAligned
  obtain ⟨nextStore, physicalResult, sourceAfter, targetAfter, updated, resumedLocals,
      steps, path, _set, _resumed, focus, residual, joins, frames, targetFrames,
      externalsEq, transports⟩ :=
    control.advance_pushFreshTagged_bind (entry := arrayEntry runtime) (payload := 0)
      rfl rfl rfl rfl contract (by decide)
      (fun address word args physicalEq decoded mapped tagged => by
        apply handler _ _ _ mapped tagged
        · exact control.operationName
        · have signature := control.parameterSignature
          change operation.signature =
            { params := #[.erased, .object, .tobject], results := #[.object] } at signature
          rw [signature, physicalEq] at decoded
          simp [decodePhysicalLanes, decodePhysicalLane, physicalOfLane,
            AbiKind.valueType, Bind.bind, Except.bind, Pure.pure, Except.pure] at decoded
          cases decoded
          rfl) budget
  exact ⟨targetArguments.length, nextStore, sourceAfter, targetAfter, resumedLocals,
    rest, .step staged steps, argumentPath.trans path, focus, residual, joins, frames,
    targetFrames, externalsEq, transports⟩

/-- Closed type classification only, following the same audited opaque-Expr
boundary as mkEmptyAbiTypes. No source or target execution is evaluated. -/
theorem literalAbiTypes :
    checkedAbiKind (.const `UInt8 []) = .ok .uint8 ∧
    checkedAbiKind (.const `tagged []) = .ok .tagged := by
  have checked :
      (match checkedAbiKind (.const `UInt8 []) with
        | .ok .uint8 => true | _ => false) = true ∧
      (match checkedAbiKind (.const `tagged []) with
        | .ok .tagged => true | _ => false) = true := by native_decide
  constructor
  · generalize h : checkedAbiKind (.const `UInt8 []) = result at checked ⊢
    cases result with
    | error e => simp at checked
    | ok kind => cases kind <;> simp_all
  · generalize h : checkedAbiKind (.const `tagged []) = result at checked ⊢
    cases result with
    | error e => simp at checked
    | ok kind => cases kind <;> simp_all

/-- Exact source-order binding row of the checked declaration. Only identifiers
are projected from retained syntax; all kinds are proved below from lowering. -/
def initializerBindings : LocalKinds :=
  [(scalarSite.fvarId, .uint8), (capacityId, .tagged), (mkEmptySite.fvarId, .object),
    (boxSite.fvarId, .tagged), (pushSite.fvarId, .object)]

theorem initializer_rawLocals :
    collectLocals [] initializerBody = .ok initializerBindings.reverse := by
  have byteBox : boxResultKind (.const `UInt8 []) .tobject = .tagged :=
    boxResultKind_uint8_tobject
  have objectKind : checkedAbiKind (.const `obj []) = .ok .object := by
    simp [checkedAbiKind, abiKind, mkEmptyAbiTypes.2.2, Bind.bind, Except.bind,
      Pure.pure, Except.pure]
  have carrierKind : checkedAbiKind (.const `tobj []) = .ok .tobject := by
    simp [checkedAbiKind, abiKind, mkEmptyAbiTypes.2.1, Bind.bind, Except.bind,
      Pure.pure, Except.pure]
  change collectLocals [] (.let scalarSite (.let capacitySite (.let mkEmptySite
    (.let boxSite (.let pushSite pushContinuation))))) = _
  simp only [collectLocals, collectLocalKindInsertions, letValueKind,
    scalarSite, capacitySite, mkEmptySite, boxSite, pushSite, pushContinuation,
    initializerBody, mkEmptyContinuation, pushCode, RetainedRC2.initializer.body]
  simp only [literalAbiTypes.1, literalAbiTypes.2, objectKind, carrierKind,
    byteBox, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rfl

theorem initializer_effectiveUpdates :
    collectEffectiveLocalKindUpdates RetainedRC2.program initializerBody =
      .ok initializerBindings := by
  have byteBox : boxResultKind (.const `UInt8 []) .tobject = .tagged :=
    boxResultKind_uint8_tobject
  have objectKind : checkedAbiKind (.const `obj []) = .ok .object := by
    simp [checkedAbiKind, abiKind, mkEmptyAbiTypes.2.2, Bind.bind, Except.bind,
      Pure.pure, Except.pure]
  have carrierKind : checkedAbiKind (.const `tobj []) = .ok .tobject := by
    simp [checkedAbiKind, abiKind, mkEmptyAbiTypes.2.1, Bind.bind, Except.bind,
      Pure.pure, Except.pure]
  change collectEffectiveLocalKindUpdates RetainedRC2.program
    (.let scalarSite (.let capacitySite (.let mkEmptySite
      (.let boxSite (.let pushSite pushContinuation))))) = _
  simp only [collectEffectiveLocalKindUpdates, effectiveLetValueKind, letValueKind,
    scalarSite, capacitySite, mkEmptySite, boxSite, pushSite, pushContinuation,
    initializerBody, mkEmptyContinuation, pushCode, RetainedRC2.initializer.body]
  simp only [literalAbiTypes.1, literalAbiTypes.2, objectKind, carrierKind,
    byteBox, Bind.bind, Except.bind, Pure.pure, Except.pure,
    mkEmptyDecl.findDecl, pushDecl.findDecl]
  simp [effectiveDeclarationResultKind?, mkEmptyDecl, pushDecl, mkEmptyAbiTypes.2.2,
    AbiKind.leanCompatible, AbiKind.refines, initializerBindings, scalarSite,
    capacityId, mkEmptySite, boxSite, pushSite, initializerBody, mkEmptyContinuation, pushCode,
    RetainedRC2.initializer.body]

theorem initializer_bindingKinds
    {context : Context} {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function} {target : AdaptedModule}
    (row : ConcreteGeneratedInternalDeclaration RetainedRC2.program RetainedRC2.initializer
      context initializerBody sourceModule sourceFunction target)
    (unique : RetainedRC2.program.NamesUnique)
    (lowered : lowerSupported RetainedRC2.program = .ok sourceModule) :
    findLocalKind? context.localKinds scalarSite.fvarId = some .uint8 ∧
    findLocalKind? context.localKinds capacityId = some .tagged ∧
    findLocalKind? context.localKinds mkEmptySite.fvarId = some .object ∧
    findLocalKind? context.localKinds boxSite.fvarId = some .tagged ∧
    findLocalKind? context.localKinds pushSite.fvarId = some .object := by
  obtain ⟨actual, kinds⟩ := row.loweredLocals unique lowered
  have params : actual.paramLocals = [] := by
    have h := actual.paramsAdded
    change Except.ok [] = Except.ok actual.paramLocals at h
    exact (Except.ok.inj h).symm
  have raw : actual.rawBodyLocals = initializerBindings.reverse :=
    (Except.ok.inj (actual.localsCollected.symm.trans initializer_rawLocals))
  have refined : actual.bodyLocals = initializerBindings.reverse := by
    have h := actual.localsRefined
    rw [raw, refineNamedCallLocalKinds, initializer_effectiveUpdates] at h
    have unchanged : applyEffectiveLocalKindUpdates initializerBindings.reverse initializerBindings =
        initializerBindings.reverse := by rfl
    simpa [Bind.bind, Except.bind, Pure.pure, Except.pure, unchanged] using h.symm
  have exactKinds : context.localKinds = initializerBindings := by
    rw [kinds]
    change actual.paramLocals.reverse ++ actual.bodyLocals.reverse = _
    simp [params, refined]
  rw [exactKinds]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

def literalEnv (env : Env) : Env :=
  bind (bind env scalarSite.fvarId (.scalar (.uint8 0))) capacityId (.object (.tagged 5))

/-- Start at the checked initializer body rather than at the Array call. The
literal prefix constructs the capacity value and leaves the heap, witness and
handler state unchanged; clients no longer provide the capacity lookup. -/
theorem literals_mkEmpty_stage_call_bind
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
    (scalarKind : findLocalKind? context.localKinds scalarSite.fvarId = some .uint8)
    (capacityKind : findLocalKind? context.localKinds capacityId = some .tagged)
    (resultKind : findLocalKind? context.localKinds mkEmptySite.fvarId = some .object)
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels runtime env initializerBody store locals code witness source target)
    (handler : ∀ request,
      ConcreteExternalRequestRel witness request
        (declarationExternalRequest mkEmptyDecl #[.erased, .object (.tagged 5)]) →
      EmptyArrayHandlerAt store.host.externals request store.host.runtime 5)
    (budget : store.host.runtime.heap.AddressSpaceBudget remainingBytes)
    (fits : residentArrayAllocationBytes 5 ≤ remainingBytes) :
    ∃ prefixLength nextStore nextWitness sourceAfter targetAfter resumedLocals rest,
      ExecSteps externals 5 source sourceAfter ∧
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
        (prefixLength + 6) target targetAfter ∧
      ConcreteStructuredCodeFocus context sourceModule sourceFunction labels
        (afterMkEmpty runtime)
        (bind (literalEnv env) mkEmptySite.fvarId (.object (.heap runtime.nextLocation)))
        mkEmptyContinuation nextStore resumedLocals rest nextWitness sourceAfter targetAfter ∧
      nextStore.host.runtime.heap.AddressSpaceBudget
        (remainingBytes - residentArrayAllocationBytes 5) ∧
      sourceAfter.joins = source.joins ∧ sourceAfter.frames = source.frames ∧
      targetAfter.frames = target.frames ∧
      nextStore.host.externals = store.host.externals ∧
      RuntimeStepTransports runtime (afterMkEmpty runtime) store nextStore witness nextWitness := by
  change ConcreteStructuredCodeFocus _ _ _ _ _ _
    (.let scalarSite (.let capacitySite (.let mkEmptySite mkEmptyContinuation)))
    _ _ _ _ _ _ at related
  have scalarValueKind : letValueKind scalarSite = .ok .uint8 := literalAbiTypes.1
  have capacityValueKind : letValueKind capacitySite = .ok .tagged := literalAbiTypes.2
  have capacityIdEq : capacitySite.fvarId = capacityId := rfl
  obtain ⟨source1, target1, locals1, rest1, step1, path1, focus1, joins1, frames1,
      targetFrames1⟩ := related.advance_immediateLiteral (.uint8 0) rfl scalarValueKind
    (by simp [getLocal, scalarKind]) spec.localsAligned
    (module := targetModule.wasmModule) (hosts := hosts.env) (externals := externals)
  obtain ⟨source2, target2, locals2, rest2, step2, path2, focus2, joins2, frames2,
      targetFrames2⟩ := focus1.advance_smallTaggedNatural spec (value := 5)
    (by decide) rfl capacityValueKind (by simp [getLocal, capacityIdEq, capacityKind])
    (externals := externals)
  obtain ⟨prefixLength, nextStore, nextWitness, sourceAfter, targetAfter,
      resumedLocals, rest, steps, path, focus, residual, joins, frames, targetFrames,
      externalsEq, transports⟩ :=
    mkEmpty_stage_call_bind programEq spec contract capacityKind resultKind
      (by simp [lookupValue, capacityIdEq]) spec.localsAligned focus2 handler budget fits
  refine ⟨prefixLength, nextStore, nextWitness, sourceAfter, targetAfter, resumedLocals,
    rest, .step step1 (.step step2 steps), ?_, focus, residual,
    joins.trans (joins2.trans joins1), frames.trans (frames2.trans frames1),
    targetFrames.trans (targetFrames2.trans targetFrames1), externalsEq, transports⟩
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using path1.trans (path2.trans path)

/-- The six-step real body prefix constructs both Array-push operands. Boxing
preserves the freshly allocated Array, the exact witness, and residual budget. -/
theorem literals_mkEmpty_box
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
    (scalarKind : findLocalKind? context.localKinds scalarSite.fvarId = some .uint8)
    (capacityKind : findLocalKind? context.localKinds capacityId = some .tagged)
    (arrayKind : findLocalKind? context.localKinds mkEmptySite.fvarId = some .object)
    (boxKind : findLocalKind? context.localKinds boxSite.fvarId = some .tagged)
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels runtime env initializerBody store locals code witness source target)
    (handler : ∀ request,
      ConcreteExternalRequestRel witness request
        (declarationExternalRequest mkEmptyDecl #[.erased, .object (.tagged 5)]) →
      EmptyArrayHandlerAt store.host.externals request store.host.runtime 5)
    (budget : store.host.runtime.heap.AddressSpaceBudget remainingBytes)
    (fits : residentArrayAllocationBytes 5 ≤ remainingBytes) :
    ∃ prefixLength nextStore nextWitness sourceAfter targetAfter resumedLocals rest,
      ExecSteps externals 6 source sourceAfter ∧
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
        (prefixLength + 9) target targetAfter ∧
      ConcreteStructuredCodeFocus context sourceModule sourceFunction labels
        (afterMkEmpty runtime)
        (bind (bind (literalEnv env) mkEmptySite.fvarId
          (.object (.heap runtime.nextLocation))) boxSite.fvarId (.object (.tagged 0)))
        pushCode nextStore resumedLocals rest nextWitness sourceAfter targetAfter ∧
      nextStore.host.runtime.heap.AddressSpaceBudget
        (remainingBytes - residentArrayAllocationBytes 5) ∧
      sourceAfter.joins = source.joins ∧ sourceAfter.frames = source.frames ∧
      targetAfter.frames = target.frames ∧
      nextStore.host.externals = store.host.externals ∧
      RuntimeStepTransports runtime (afterMkEmpty runtime) store nextStore witness nextWitness := by
  obtain ⟨prefixLength, nextStore, nextWitness, sourceMid, targetMid, midLocals,
      midCode, prefixSteps, prefixPath, focus, residual, joins, frames, targetFrames,
      externalsEq, transports⟩ :=
    literals_mkEmpty_stage_call_bind programEq spec contract scalarKind capacityKind
      arrayKind related handler budget fits
  change ConcreteStructuredCodeFocus _ _ _ _ _ _ (.let boxSite pushCode)
    _ _ _ _ _ _ at focus
  have valueKind : letValueKind boxSite = .ok .tagged := by
    change (do let kind ← checkedAbiKind (.const `tobj [])
               pure (boxResultKind (.const `UInt8 []) kind)) = .ok .tagged
    simp only [checkedAbiKind, abiKind, mkEmptyAbiTypes.2.1,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact congrArg Except.ok boxResultKind_uint8_tobject
  have scalarLookup : lookup
      (bind (literalEnv env) mkEmptySite.fvarId (.object (.heap runtime.nextLocation)))
      scalarSite.fvarId = some (.scalar (.uint8 0)) := by
    simp [literalEnv, Fir.LeanIR.Impure.bind, lookup, scalarSite, capacityId, mkEmptySite, initializerBody,
      RetainedRC2.initializer]
  obtain ⟨sourceAfter, targetAfter, resumedLocals, rest, step, path, next,
      joins', frames', targetFrames'⟩ := focus.advance_boxUInt8 spec rfl valueKind
    (by simp [getLocal, scalarKind]) literalAbiTypes.1
    (by simp [getLocal, boxKind]) scalarLookup (externals := externals)
  refine ⟨prefixLength, nextStore, nextWitness, sourceAfter, targetAfter, resumedLocals,
    rest, execSteps_trans_exact prefixSteps (.step step (.refl _)), ?_, next, residual,
    joins'.trans joins, frames'.trans frames, targetFrames'.trans targetFrames,
    externalsEq, transports⟩
  simpa [Nat.add_assoc] using prefixPath.trans path

def bodyResultEnv (env : Env) (runtime : RuntimeState) : Env :=
  bind (bind (bind (literalEnv env) mkEmptySite.fvarId
    (.object (.heap runtime.nextLocation))) boxSite.fvarId (.object (.tagged 0)))
    pushSite.fvarId (.object (.heap runtime.nextLocation))

/-- The actual kernel-retained initializer body returns the represented
singleton Array. Neither source execution nor a target path is a premise.
This is the body-to-yield theorem, not yet lazy entry/publication or resident
linking. Both handler equations and finite allocation headroom stay explicit. -/
theorem body_returns
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
    (scalarKind : findLocalKind? context.localKinds scalarSite.fvarId = some .uint8)
    (capacityKind : findLocalKind? context.localKinds capacityId = some .tagged)
    (arrayKind : findLocalKind? context.localKinds mkEmptySite.fvarId = some .object)
    (boxKind : findLocalKind? context.localKinds boxSite.fvarId = some .tagged)
    (resultKind : findLocalKind? context.localKinds pushSite.fvarId = some .object)
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels runtime env initializerBody store locals code witness source target)
    (emptyHandler : ∀ request,
      ConcreteExternalRequestRel witness request
        (declarationExternalRequest mkEmptyDecl #[.erased, .object (.tagged 5)]) →
      EmptyArrayHandlerAt store.host.externals request store.host.runtime 5)
    (pushHandler : ∀ before nextWitness request address word,
      ConcreteRuntimeRel before nextWitness (afterMkEmpty runtime) →
      nextWitness.locations.lookup? runtime.nextLocation = some address →
      ValueRel nextWitness .tobject (.word32 word) (.object (.tagged 0)) →
      request.name = `Array.push →
      request.args = #[.word32 Word32.zero, .word32 address, .word32 word] →
      ArrayPushInPlaceHandlerAt store.host.externals request before address word)
    (budget : store.host.runtime.heap.AddressSpaceBudget remainingBytes)
    (fits : residentArrayAllocationBytes 5 ≤ remainingBytes) :
    ∃ targetSteps nextStore nextWitness resultLocals physical sourceAfter targetAfter,
      ExecSteps externals 10 source sourceAfter ∧
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
        targetSteps target targetAfter ∧
      ConcreteStructuredYieldFocus context sourceFunction (afterPush runtime)
        (bodyResultEnv env runtime) (.object (.heap runtime.nextLocation))
        nextStore resultLocals nextWitness .object physical sourceAfter targetAfter ∧
      nextStore.host.runtime.heap.AddressSpaceBudget
        (remainingBytes - residentArrayAllocationBytes 5) ∧
      sourceAfter.joins = source.joins ∧ sourceAfter.frames = source.frames ∧
      targetAfter.frames = target.frames ∧
      nextStore.host.externals = store.host.externals ∧
      RuntimeStepTransports runtime (afterPush runtime) store nextStore witness nextWitness := by
  obtain ⟨prefixLength, midStore, nextWitness, sourceMid, targetMid, midLocals,
      midCode, prefixSteps, prefixPath, focus, residual, joins, frames, targetFrames,
      externalsEq, prefixTransports⟩ := literals_mkEmpty_box programEq spec contract scalarKind capacityKind
        arrayKind boxKind related emptyHandler budget fits
  have arrayValue : lookup
      (bind (bind (literalEnv env) mkEmptySite.fvarId
        (.object (.heap runtime.nextLocation))) boxSite.fvarId (.object (.tagged 0)))
      mkEmptySite.fvarId = some (.object (.heap runtime.nextLocation)) := by
    simp [Fir.LeanIR.Impure.bind, lookup, boxSite, mkEmptyContinuation, mkEmptySite,
      RetainedRC2.initializer]
  obtain ⟨pushLength, nextStore, sourcePushed, targetPushed, resultLocals, returnCode,
      pushSteps, pushPath, returnFocus, finalBudget, pushJoins, pushFrames, pushTargetFrames,
      pushExternals, pushTransports⟩ :=
    push_stage_call_bind programEq spec contract arrayKind boxKind resultKind arrayValue
      (lookup_bind_self _ _ _) focus
      (fun request address word mapped tagged named args => by
        rw [externalsEq]
        exact pushHandler _ nextWitness request address word focus.stateRelated.1
          mapped tagged named args) residual
  change ConcreteStructuredCodeFocus _ _ _ _ _ _ (.return pushSite.fvarId)
    _ _ _ _ _ _ at returnFocus
  obtain ⟨kind, physical, sourceAfter, targetAfter, compiled, returnStep, returnPath,
      yielded, returnJoins, returnFrames, returnTargetFrames⟩ :=
    returnFocus.advance_return spec.localsAligned (lookup_bind_self _ _ _)
      (externals := externals) (module := targetModule.wasmModule) (hostEnv := hosts.env)
  have kindEq : kind = .object := by
    simpa [getLocal, resultKind] using compiled.symm
  subst kind
  refine ⟨_, nextStore, nextWitness, resultLocals, physical, sourceAfter, targetAfter,
    execSteps_trans_exact prefixSteps
      (execSteps_trans_exact pushSteps (.step returnStep (.refl _))),
    prefixPath.trans (pushPath.trans returnPath), yielded, finalBudget,
    returnJoins.trans (pushJoins.trans joins), returnFrames.trans (pushFrames.trans frames),
    returnTargetFrames.trans (pushTargetFrames.trans targetFrames),
    pushExternals.trans externalsEq, prefixTransports.trans pushTransports⟩

/-- Execute the actual retained body, publish its fresh Array, and resume the
saved caller. The post-body resource scope and publication input are derived,
not premises. Entry still starts after the lazy miss has installed its frames;
connecting that entry is separate from this body-to-caller result. -/
theorem body_publishes_and_resumesCaller
    {callerContext context : Context}
    {callerCode rootCode : LCNF.Code .impure} {sourceModule : Fir.Wasm.Module}
    {callerFunction sourceFunction : Fir.Wasm.Function} {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    (callerSpec : ConcreteSupportedFunction RetainedRC2.program callerContext callerCode
      sourceModule callerFunction targetModule hosts)
    (spec : ConcreteSupportedFunction RetainedRC2.program context rootCode
      sourceModule sourceFunction targetModule hosts)
    {externals : ExternalImpl} (contract : FreshArrayExternalContract externals)
    {outerRuntime runtime : RuntimeState} {outerStore store : Wasm.Store Host}
    {outerWitness witness : RefinementWitness} {callerFacts : ReuseCapacityFacts}
    {callerBytes remainingBytes : Nat} {callerEnv env : Env}
    {callerLocals locals : Wasm.Locals} {labels callerLabels : LabelContext}
    {code rest : Wasm.Program} {source : MachineState} {target : StructuredWasmState Host}
    {cacheIndex cacheSetId resultIndex : Nat} {result : FVarId}
    {continuation : LCNF.Code .impure} {callerJoins : JoinEnv}
    {sourceFrames : List Frame} {frames : List StructuredWasmFrame}
    {functionResult : AbiKind} {callerExpectedResult : Option AbiKind}
    (callerScope : ConcreteStructuredResourceScope callerContext sourceModule callerFunction
      externals outerRuntime outerStore outerWitness callerFacts callerBytes
      runtime callerEnv store callerLocals witness)
    (bodyFrame : ConcreteReuseCapacityCacheAbiFrame context sourceModule sourceFunction
      externals [] remainingBytes runtime env store locals witness)
    (scalarKind : findLocalKind? context.localKinds scalarSite.fvarId = some .uint8)
    (capacityKind : findLocalKind? context.localKinds capacityId = some .tagged)
    (arrayKind : findLocalKind? context.localKinds mkEmptySite.fvarId = some .object)
    (boxKind : findLocalKind? context.localKinds boxSite.fvarId = some .tagged)
    (resultKind : findLocalKind? context.localKinds pushSite.fvarId = some .object)
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction labels
      runtime env initializerBody store locals code witness source target)
    (emptyHandler : ∀ request,
      ConcreteExternalRequestRel witness request
        (declarationExternalRequest mkEmptyDecl #[.erased, .object (.tagged 5)]) →
      EmptyArrayHandlerAt store.host.externals request store.host.runtime 5)
    (pushHandler : ∀ before nextWitness request address word,
      ConcreteRuntimeRel before nextWitness (afterMkEmpty runtime) →
      nextWitness.locations.lookup? runtime.nextLocation = some address →
      ValueRel nextWitness .tobject (.word32 word) (.object (.tagged 0)) →
      request.name = `Array.push →
      request.args = #[.word32 Word32.zero, .word32 address, .word32 word] →
      ArrayPushInPlaceHandlerAt store.host.externals request before address word)
    (fits : residentArrayAllocationBytes 5 ≤ remainingBytes)
    (initializerFound : sourceModule.initializers[cacheIndex]? = some RetainedRC2.initializer.name)
    (signature : (sourceModule.callSignature? (.declaration RetainedRC2.initializer.name)).bind
      (·.results[0]?) = some .object)
    (cacheSetCall : FirTalos.callIndex? sourceModule
      (.runtime (.cacheSet RetainedRC2.initializer.name .object)) = some cacheSetId)
    (sourceStack : source.frames = .cache RetainedRC2.initializer.name ::
      .bind result continuation callerEnv callerJoins :: sourceFrames)
    (targetStack : target.frames =
      .call 1 callerLocals.values callerLocals
        [.call cacheSetId, .globalSet (2 * cacheIndex + 1), .const 1, .globalSet (2 * cacheIndex)] ::
      .label 0 callerLocals.values
        ([.globalGet (2 * cacheIndex + 1), .localSet resultIndex] ++ rest) :: frames)
    (adapted : CodeAdaptedWithSuffix callerContext sourceModule callerFunction callerLabels
      continuation rest)
    (resultFound : FirTalos.findFVar? (functionBindings callerFunction) result = some resultIndex)
    (kindAt : (functionBindings callerFunction)[resultIndex]?.map Prod.snd = some .object)
    (tail : ConcreteStructuredSuspendedResourceStack externals RetainedRC2.program
      outerRuntime outerStore outerWitness functionResult callerExpectedResult sourceFrames frames) :
    ∃ targetSteps nextStore nextWitness resumedLocals sourceAfter targetAfter,
      ExecSteps externals 12 source sourceAfter ∧
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
        targetSteps target targetAfter ∧
      ConcreteStructuredCodeCoreRel RetainedRC2.program callerContext sourceModule callerFunction
        externals callerLabels outerRuntime outerStore outerWitness functionResult callerExpectedResult
        (eraseReuseCapacityFact callerFacts result) (remainingBytes - residentArrayAllocationBytes 5)
        ((afterPush runtime).setGlobal RetainedRC2.initializer.name (.object (.heap runtime.nextLocation)))
        (bind callerEnv result (.object (.heap runtime.nextLocation))) continuation
        nextStore resumedLocals rest nextWitness sourceAfter targetAfter ∧
      sourceAfter.joins = callerJoins ∧ sourceAfter.frames = sourceFrames ∧
      targetAfter.frames = frames := by
  have initialScope := ConcreteStructuredResourceScope.root bodyFrame
  have budget := initialScope.budgetedPureExternal.1.2
  obtain ⟨bodySteps, bodyStore, nextWitness, bodyLocals, physical, sourceReturned,
      targetReturned, sourceBody, targetBody, yielded, residual, _joins,
      sourceFramesEq, targetFramesEq, externalsEq, transports⟩ :=
    body_returns spec.contextProgram spec contract scalarKind capacityKind arrayKind
      boxKind resultKind related emptyHandler pushHandler budget fits
  have bodyScope := initialScope.afterBody_withoutReuseFacts transports externalsEq
    yielded.stateRelated yielded.frameAligned residual
  have closed : HeapRegionClosed runtime.nextLocation (afterPush runtime).heap := by
    apply (HeapRegionClosed.of_liveHeapRel initialScope.stateRelated.1.heap).alloc
      (object := .array #[.object (.tagged 0)] 5) (persistent := false)
      (after := semanticArrayResult runtime #[.object (.tagged 0)] 5) rfl
    simp [HeapObject.ownedValues]
  obtain ⟨runtimeAfter, sourceAfter, targetAfter, resumedLocals, sourceSuffix,
      targetSuffix, core, joins, sourceFrames', targetFrames'⟩ :=
    callerScope.publishFreshCache_bind callerSpec bodyScope
      (spec.contextProgram.trans callerSpec.contextProgram.symm)
      initializerFound signature cacheSetCall yielded.valueRelated closed (Nat.le_refl _)
      (yielded.sourceProgramEq.trans (spec.contextProgram.trans callerSpec.contextProgram.symm))
      yielded.sourceControlEq yielded.sourceRuntimeEq (sourceFramesEq.trans sourceStack)
      adapted resultFound kindAt tail
  have targetEq : targetReturned =
      ⟨bodyStore, .returning (physical :: bodyLocals.values), target.frames⟩ := by
    cases targetReturned
    rw [StructuredWasmState.mk.injEq]
    exact ⟨yielded.targetStoreEq, yielded.targetControlEq, targetFramesEq⟩
  rw [targetEq, targetStack] at targetBody
  exact ⟨_, _, nextWitness, resumedLocals, sourceAfter, targetAfter,
    execSteps_trans_exact sourceBody sourceSuffix, targetBody.trans targetSuffix,
    core, joins, sourceFrames', targetFrames'⟩

/-- A real cold-cache invocation enters the checked initializer, executes its
body, publishes the fresh result, and resumes the saved caller. No body-entry
state, installed stack, callee frame, execution path or post-body scope is a
premise. The generated declaration row and five binding kinds are derived from
production lowering; Array host contracts remain explicit. -/
theorem lazyMiss_publishes_and_resumesCaller
    {callerContext : Context} {callerCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module} {callerFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule} {hosts : ResolvedHosts}
    (callerSpec : ConcreteSupportedFunction RetainedRC2.program callerContext callerCode
      sourceModule callerFunction targetModule hosts)
    {externals : ExternalImpl} (contract : FreshArrayExternalContract externals)
    {outerRuntime runtime : RuntimeState} {outerStore store : Wasm.Store Host}
    {outerWitness witness : RefinementWitness} {facts : ReuseCapacityFacts} {bytes : Nat}
    {callerEnv : Env} {callerLocals : Wasm.Locals} {labels : LabelContext}
    {rest : Wasm.Program} {source : MachineState} {target : StructuredWasmState Host}
    {cacheIndex declarationId cacheSetId resultIndex : Nat} {decl : LCNF.LetDecl .impure}
    {continuation : LCNF.Code .impure} {callerJoins : JoinEnv}
    {sourceFrames : List Frame} {frames : List StructuredWasmFrame}
    {functionResult : AbiKind} {callerExpectedResult : Option AbiKind}
    {call : LazyCacheCallSupported callerContext decl RetainedRC2.initializer.name
      RetainedRC2.initializer .object}
    {generated : LazyCacheGeneratedEnvironment callerContext sourceModule}
    (ready : ConcreteStructuredLazyCallReadyFocus callerContext sourceModule callerFunction labels
      call generated runtime callerEnv continuation callerJoins sourceFrames store callerLocals
      rest frames witness cacheIndex declarationId cacheSetId resultIndex source target)
    (scope : ConcreteStructuredResourceScope callerContext sourceModule callerFunction externals
      outerRuntime outerStore outerWitness facts bytes runtime callerEnv store callerLocals witness)
    (empty : findGlobal? runtime.globals RetainedRC2.initializer.name = none)
    (emptyHandler : ∀ request,
      ConcreteExternalRequestRel witness request
        (declarationExternalRequest mkEmptyDecl #[.erased, .object (.tagged 5)]) →
      EmptyArrayHandlerAt store.host.externals request store.host.runtime 5)
    (pushHandler : ∀ before nextWitness request address word,
      ConcreteRuntimeRel before nextWitness (afterMkEmpty runtime) →
      nextWitness.locations.lookup? runtime.nextLocation = some address →
      ValueRel nextWitness .tobject (.word32 word) (.object (.tagged 0)) →
      request.name = `Array.push →
      request.args = #[.word32 Word32.zero, .word32 address, .word32 word] →
      ArrayPushInPlaceHandlerAt store.host.externals request before address word)
    (fits : residentArrayAllocationBytes 5 ≤ bytes)
    (tail : ConcreteStructuredSuspendedResourceStack externals RetainedRC2.program
      outerRuntime outerStore outerWitness functionResult callerExpectedResult sourceFrames frames) :
    ∃ targetSteps nextStore nextWitness resumedLocals sourceAfter targetAfter,
      ExecSteps externals 13 source sourceAfter ∧
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
        targetSteps target targetAfter ∧
      ConcreteStructuredCodeCoreRel RetainedRC2.program callerContext sourceModule callerFunction
        externals labels outerRuntime outerStore outerWitness functionResult callerExpectedResult
        (eraseReuseCapacityFact facts decl.fvarId) (bytes - residentArrayAllocationBytes 5)
        ((afterPush runtime).setGlobal RetainedRC2.initializer.name (.object (.heap runtime.nextLocation)))
        (bind callerEnv decl.fvarId (.object (.heap runtime.nextLocation))) continuation
        nextStore resumedLocals rest nextWitness sourceAfter targetAfter ∧
      sourceAfter.joins = callerJoins ∧ sourceAfter.frames = sourceFrames ∧
      targetAfter.frames = frames := by
  have caches := generated.cacheNames.trans
    (LazyCacheGeneratedEnvironment.initializers_of_lower
      (LazyCacheGeneratedEnvironment.lower_of_lowerSupported callerSpec.lowered))
  have bodyEq : RetainedRC2.initializer.value = .code initializerBody := rfl
  have classified : abiKind? RetainedRC2.initializer.type = .ok (some .object) :=
    mkEmptyAbiTypes.2.2
  obtain ⟨context, sourceFunction, _contexts, ⟨row⟩⟩ :=
    ConcreteGeneratedInternalDeclaration.exists_ofSupportedPipeline
      callerSpec.contextProgram caches callerSpec.programNamesUnique callerSpec.lowered
      callerSpec.adapted RetainedRC2.initializer.findDecl bodyEq classified
  obtain ⟨scalarKind, capacityKind, arrayKind, boxKind, resultKind⟩ :=
    initializer_bindingKinds row callerSpec.programNamesUnique callerSpec.lowered
  obtain ⟨sourceEntry, targetEntry, sourceStep, targetPath, focus, bodyFrame,
      _joins, sourceStack, targetStack⟩ :=
    ready.enterBody scope callerSpec.contextProgram row empty
  obtain ⟨steps, nextStore, nextWitness, resumedLocals, sourceAfter, targetAfter,
      bodySteps, bodyPath, core, joins, sourceFramesEq, targetFramesEq⟩ :=
    body_publishes_and_resumesCaller callerSpec (row.fromSupportedFunction callerSpec)
      contract scope bodyFrame scalarKind capacityKind arrayKind boxKind resultKind focus
      emptyHandler pushHandler fits ready.initializerFound ready.signature ready.cacheSetCall
      sourceStack targetStack ready.continuationAdapted ready.resultFound ready.resultKindAt tail
  exact ⟨3 + steps, nextStore, nextWitness, resumedLocals, sourceAfter, targetAfter,
    .step sourceStep bodySteps, targetPath.trans bodyPath, core, joins, sourceFramesEq, targetFramesEq⟩

/-- Execute the caller's actual lazy-call let, including its production staging,
the checked initializer, publication and destination binding. The callee package,
local kinds, numeric indices, target suffix and source/target paths are derived.
The compiler-supported call and module-wide cache contract remain explicit. -/
theorem let_publishes_and_resumesCaller
    {callerContext : Context} {callerCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module} {callerFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule} {hosts : ResolvedHosts}
    (callerSpec : ConcreteSupportedFunction RetainedRC2.program callerContext callerCode
      sourceModule callerFunction targetModule hosts)
    {externals : ExternalImpl} (contract : FreshArrayExternalContract externals)
    {outerRuntime runtime : RuntimeState} {outerStore store : Wasm.Store Host}
    {outerWitness witness : RefinementWitness} {facts : ReuseCapacityFacts} {bytes : Nat}
    {callerEnv : Env} {callerLocals : Wasm.Locals} {labels : LabelContext}
    {code : Wasm.Program} {source : MachineState} {target : StructuredWasmState Host}
    {decl : LCNF.LetDecl .impure} {continuation : LCNF.Code .impure}
    {functionResult : AbiKind} {callerExpectedResult : Option AbiKind}
    (related : ConcreteStructuredCodeFocus callerContext sourceModule callerFunction labels
      runtime callerEnv (.let decl continuation) store callerLocals code witness source target)
    (call : LazyCacheCallSupported callerContext decl RetainedRC2.initializer.name
      RetainedRC2.initializer .object)
    (generated : LazyCacheGeneratedEnvironment callerContext sourceModule)
    (scope : ConcreteStructuredResourceScope callerContext sourceModule callerFunction externals
      outerRuntime outerStore outerWitness facts bytes runtime callerEnv store callerLocals witness)
    (empty : findGlobal? runtime.globals RetainedRC2.initializer.name = none)
    (emptyHandler : ∀ request,
      ConcreteExternalRequestRel witness request
        (declarationExternalRequest mkEmptyDecl #[.erased, .object (.tagged 5)]) →
      EmptyArrayHandlerAt store.host.externals request store.host.runtime 5)
    (pushHandler : ∀ before nextWitness request address word,
      ConcreteRuntimeRel before nextWitness (afterMkEmpty runtime) →
      nextWitness.locations.lookup? runtime.nextLocation = some address →
      ValueRel nextWitness .tobject (.word32 word) (.object (.tagged 0)) →
      request.name = `Array.push →
      request.args = #[.word32 Word32.zero, .word32 address, .word32 word] →
      ArrayPushInPlaceHandlerAt store.host.externals request before address word)
    (fits : residentArrayAllocationBytes 5 ≤ bytes)
    (tail : ConcreteStructuredSuspendedResourceStack externals RetainedRC2.program
      outerRuntime outerStore outerWitness functionResult callerExpectedResult
      source.frames target.frames) :
    ∃ targetSteps nextStore nextWitness resumedLocals rest sourceAfter targetAfter,
      ExecSteps externals 14 source sourceAfter ∧
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env)
        targetSteps target targetAfter ∧
      ConcreteStructuredCodeCoreRel RetainedRC2.program callerContext sourceModule callerFunction
        externals labels outerRuntime outerStore outerWitness functionResult callerExpectedResult
        (eraseReuseCapacityFact facts decl.fvarId) (bytes - residentArrayAllocationBytes 5)
        ((afterPush runtime).setGlobal RetainedRC2.initializer.name (.object (.heap runtime.nextLocation)))
        (bind callerEnv decl.fvarId (.object (.heap runtime.nextLocation))) continuation
        nextStore resumedLocals rest nextWitness sourceAfter targetAfter ∧
      sourceAfter.joins = source.joins ∧ sourceAfter.frames = source.frames ∧
      targetAfter.frames = target.frames := by
  obtain ⟨staged, cacheIndex, declarationId, cacheSetId, resultIndex, rest, step, ready⟩ :=
    related.stageLazyCall call generated callerSpec.localsAligned
  obtain ⟨steps, nextStore, nextWitness, resumedLocals, sourceAfter, targetAfter,
      sourceSteps, targetPath, core, joins, sourceFrames, targetFrames⟩ :=
    lazyMiss_publishes_and_resumesCaller callerSpec contract ready scope empty
      emptyHandler pushHandler fits tail
  exact ⟨steps, nextStore, nextWitness, resumedLocals, rest, sourceAfter, targetAfter,
    .step step sourceSteps, targetPath, core, joins, sourceFrames, targetFrames⟩

end

end RetainedInitializer

open Lean.Elab.Command in
run_cmd do
  FirTalos.TrustAudit.check `RetainedInitializer.initializer_bindingKinds
    (FirTalos.TrustAudit.standardAxioms ++ #[
      "RetainedInitializer.literalAbiTypes._native.native_decide.ax_1_8",
      "RetainedInitializer.mkEmptyAbiTypes._native.native_decide.ax_1_1",
      "Fir.Wasm.boxResultKind_uint8_tobject._native.native_decide.ax_1_1"])
  FirTalos.TrustAudit.check `RetainedInitializer.mkEmpty_stage_call_bind
    (FirTalos.TrustAudit.standardAxioms ++ #[
      "RetainedInitializer.mkEmptyAbiTypes._native.native_decide.ax_1_1",
      "_private.Fir.Wasm.Concrete.Memory.0.Fir.Wasm.Concrete.LinearMemory.assembleByte32._native.bv_decide.ax_1_6"])
  FirTalos.TrustAudit.check `RetainedInitializer.literals_mkEmpty_stage_call_bind
    (FirTalos.TrustAudit.standardAxioms ++ #[
      "RetainedInitializer.literalAbiTypes._native.native_decide.ax_1_8",
      "RetainedInitializer.mkEmptyAbiTypes._native.native_decide.ax_1_1",
      "_private.Fir.Wasm.Concrete.Memory.0.Fir.Wasm.Concrete.LinearMemory.assembleByte32._native.bv_decide.ax_1_6"])
  FirTalos.TrustAudit.check `RetainedInitializer.push_stage_call_bind
    (FirTalos.TrustAudit.standardAxioms ++ #[
      "RetainedInitializer.mkEmptyAbiTypes._native.native_decide.ax_1_1",
      "_private.Fir.Wasm.Concrete.Memory.0.Fir.Wasm.Concrete.LinearMemory.assembleByte32._native.bv_decide.ax_1_6"])
  for endpoint in #[`RetainedInitializer.literals_mkEmpty_box, `RetainedInitializer.body_returns,
      `RetainedInitializer.body_publishes_and_resumesCaller,
      `RetainedInitializer.lazyMiss_publishes_and_resumesCaller,
      `RetainedInitializer.let_publishes_and_resumesCaller] do
    FirTalos.TrustAudit.check endpoint
      (FirTalos.TrustAudit.standardAxioms ++ #[
        "RetainedInitializer.literalAbiTypes._native.native_decide.ax_1_8",
        "RetainedInitializer.mkEmptyAbiTypes._native.native_decide.ax_1_1",
        "Fir.Wasm.boxResultKind_uint8_tobject._native.native_decide.ax_1_1",
        "Fir.Wasm.Concrete.boxUsesTaggedRepresentation_boxedScalar._native.native_decide.ax_1_10",
        "Fir.Wasm.Concrete.boxUsesTaggedRepresentation_boxedScalar._native.native_decide.ax_1_11",
        "Fir.Wasm.Concrete.boxUsesTaggedRepresentation_boxedScalar._native.native_decide.ax_1_12",
        "Fir.Wasm.Concrete.boxUsesTaggedRepresentation_boxedScalar._native.native_decide.ax_1_13",
        "Fir.Wasm.Concrete.boxUsesTaggedRepresentation_boxedScalar._native.native_decide.ax_1_14",
        "Fir.Wasm.Concrete.boxUsesTaggedRepresentation_boxedScalar._native.native_decide.ax_1_15",
        "Fir.Wasm.Concrete.boxUsesTaggedRepresentation_boxedScalar._native.native_decide.ax_1_9",
        "_private.Fir.Wasm.Concrete.Memory.0.Fir.Wasm.Concrete.LinearMemory.assembleByte32._native.bv_decide.ax_1_6"])
