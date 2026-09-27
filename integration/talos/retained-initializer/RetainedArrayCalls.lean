import RetainedDeclarations
import FirTalos.ConcreteArrayExternalCall
import FirTalos.ConcreteLiteralPrefix
import FirTalos.ConcreteBoxPrefix
import FirTalos.ConcreteArrayPushCall
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
      nextStore.host.externals = store.host.externals := by
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
      frames, targetFrames, externalsEq⟩ :=
    control.advance_emptyArray_bind (capacity := 5) rfl rfl
      (fun args decode => by
        have same : args = concreteArgs := Except.ok.inj (decode.symm.trans decoded)
        subst args
        exact handler _ (by simpa [resolved, requestEq] using requestRelated))
      budget fits
  exact ⟨targetArguments.length, nextStore, nextWitness, sourceAfter, targetAfter,
    resumedLocals, rest, .step staged steps, argumentPath.trans path, focus, residual,
    joins, frames, targetFrames, externalsEq⟩

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
      targetAfter.frames = target.frames := by
  let site := pushCallShape context programEq externals contract runtime env
    arrayKind boxKind resultKind arrayValue boxValue
  change ConcreteStructuredCodeFocus _ _ _ _ _ _ (.let pushSite pushContinuation)
    _ _ _ _ _ _ at related
  obtain ⟨physicalArgs, operation, resolvedKind, targetImport, callIndex, resultIndex,
      targetArguments, rest, sourceStaged, targetStaged, staged, argumentPath, control⟩ :=
    related.advance_external_stage_of_shape spec site spec.localsAligned
  obtain ⟨nextStore, physicalResult, sourceAfter, targetAfter, updated, resumedLocals,
      steps, path, _set, _resumed, focus, residual, joins, frames, targetFrames⟩ :=
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
    targetFrames⟩

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
      nextStore.host.externals = store.host.externals := by
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
      externalsEq⟩ :=
    mkEmpty_stage_call_bind programEq spec contract capacityKind resultKind
      (by simp [lookupValue, capacityIdEq]) spec.localsAligned focus2 handler budget fits
  refine ⟨prefixLength, nextStore, nextWitness, sourceAfter, targetAfter, resumedLocals,
    rest, .step step1 (.step step2 steps), ?_, focus, residual,
    joins.trans (joins2.trans joins1), frames.trans (frames2.trans frames1),
    targetFrames.trans (targetFrames2.trans targetFrames1), externalsEq⟩
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
      nextStore.host.externals = store.host.externals := by
  obtain ⟨prefixLength, nextStore, nextWitness, sourceMid, targetMid, midLocals,
      midCode, prefixSteps, prefixPath, focus, residual, joins, frames, targetFrames,
      externalsEq⟩ :=
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
    joins'.trans joins, frames'.trans frames, targetFrames'.trans targetFrames, externalsEq⟩
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
      targetAfter.frames = target.frames := by
  obtain ⟨prefixLength, midStore, nextWitness, sourceMid, targetMid, midLocals,
      midCode, prefixSteps, prefixPath, focus, residual, joins, frames, targetFrames,
      externalsEq⟩ := literals_mkEmpty_box programEq spec contract scalarKind capacityKind
        arrayKind boxKind related emptyHandler budget fits
  have arrayValue : lookup
      (bind (bind (literalEnv env) mkEmptySite.fvarId
        (.object (.heap runtime.nextLocation))) boxSite.fvarId (.object (.tagged 0)))
      mkEmptySite.fvarId = some (.object (.heap runtime.nextLocation)) := by
    simp [Fir.LeanIR.Impure.bind, lookup, boxSite, mkEmptyContinuation, mkEmptySite,
      RetainedRC2.initializer]
  obtain ⟨pushLength, nextStore, sourcePushed, targetPushed, resultLocals, returnCode,
      pushSteps, pushPath, returnFocus, finalBudget, pushJoins, pushFrames, pushTargetFrames⟩ :=
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
    returnTargetFrames.trans (pushTargetFrames.trans targetFrames)⟩

end

end RetainedInitializer

open Lean.Elab.Command in
run_cmd do
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
  for endpoint in #[`RetainedInitializer.literals_mkEmpty_box, `RetainedInitializer.body_returns] do
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
