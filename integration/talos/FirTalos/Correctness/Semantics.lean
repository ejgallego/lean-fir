import FirTalos.Correctness.Composition
import FirTalos.Correctness.Locals

namespace FirTalos.Correctness

open Fir.Wasm
open Fir.LeanIR.Impure

/-- The numeric local layout used by the adapter for one lowered function. -/
def functionBindings (sourceFunction : Fir.Wasm.Function) :
    List (Lean.FVarId × AbiKind) :=
  sourceFunction.params.toList ++ sourceFunction.locals.toList

/--
The local W4 simulation invariant. The semantic runtime is retained literally
inside the host state, both structured target-failure channels are clear, the
handle codec is coherent and fresh, and every live source binding decodes from
the compiler-assigned target local.
-/
def StateRelated (sourceFunction : Fir.Wasm.Function)
    (sourceRuntime : RuntimeState) (sourceEnv : Env)
    (targetStore : Wasm.Store RuntimeHost) (targetLocals : Wasm.Locals) : Prop :=
  targetStore.host.runtime = sourceRuntime ∧
    targetStore.host.fault? = none ∧
    targetStore.host.targetFailure? = none ∧
    HandleTableInvariant targetStore.host.handles ∧
    EnvLocalsRelated (functionBindings sourceFunction) sourceEnv
      targetStore.host.handles targetLocals

/--
The source-facing postcondition for a generated return. The physical stack head
decodes to the source value and the pre-existing operand tail is unchanged.
-/
def ReturnPost (sourceRuntime : RuntimeState) (sourceValue : Value)
    (kind : AbiKind) (tail : List Wasm.Value) : Wasm.Assertion RuntimeHost :=
  fun continuation =>
    ∃ targetStore physical,
      continuation = .Return targetStore (physical :: tail) ∧
      targetStore.host.runtime = sourceRuntime ∧
      DecodesValue targetStore.host.handles kind physical sourceValue

/--
Proof-facing semantic judgment for one adapted source code node. It joins the
real two-stage compiler witness, the source/target state invariant, and Talos's
fuel-free total-correctness weakest precondition.
-/
def CodeWP (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module) (sourceFunction : Fir.Wasm.Function)
    (labels : List Lean.FVarId) (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv RuntimeHost)
    (sourceRuntime : RuntimeState) (sourceEnv : Env)
    (code : Lean.Compiler.LCNF.Code .impure) (target : Wasm.Program)
    (targetStore : Wasm.Store RuntimeHost) (targetLocals : Wasm.Locals)
    (tail : List Wasm.Value) (Q : Wasm.Assertion RuntimeHost) : Prop :=
  CodeAdapted context sourceModule sourceFunction labels code target ∧
    StateRelated sourceFunction sourceRuntime sourceEnv targetStore targetLocals ∧
    Wasm.wp module target Q targetStore
      { targetLocals with values := tail } hostEnv

/--
The postcondition installed around either arm of a generated case test. Talos
models `if` bodies as nested programs: ordinary fallthrough and a break out of
the body resume the instructions following the test, while deeper breaks lose
one label level.
-/
def CaseResumePost (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv RuntimeHost) (rest : Wasm.Program)
    (Q : Wasm.Assertion RuntimeHost) (tail : List Wasm.Value) :
    Wasm.Assertion RuntimeHost :=
  fun continuation =>
    match continuation with
    | .Fallthrough nextStore nextLocals =>
        Wasm.wp module rest Q nextStore
          { nextLocals with values := tail } hostEnv
    | .Break 0 nextStore nextLocals =>
        Wasm.wp module rest Q nextStore
          { nextLocals with values := tail } hostEnv
    | .Break (level + 1) nextStore nextLocals =>
        Q (.Break level nextStore nextLocals)
    | other => Q other

/--
Semantic judgment for a constructor-test suffix. Unlike `CodeWP`, the source
side is an alternative list plus the symbolic fallback selected before chain
construction. This makes the recursive proof follow exactly the executable
case compiler.
-/
def CaseChainWP (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module) (sourceFunction : Fir.Wasm.Function)
    (labels : List Lean.FVarId) (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv RuntimeHost)
    (sourceRuntime : RuntimeState) (sourceEnv : Env)
    (discr : Lean.FVarId) (alts : List (Lean.Compiler.LCNF.Alt .impure))
    (fallback : List Fir.Wasm.Instruction) (target : Wasm.Program)
    (targetStore : Wasm.Store RuntimeHost) (targetLocals : Wasm.Locals)
    (tail : List Wasm.Value) (Q : Wasm.Assertion RuntimeHost) : Prop :=
  CaseChainAdapted context sourceModule sourceFunction labels discr alts
      fallback target ∧
    StateRelated sourceFunction sourceRuntime sourceEnv targetStore targetLocals ∧
    Wasm.wp module target Q targetStore
      { targetLocals with values := tail } hostEnv

/-- The direct, non-calling source result of one `let` value computation. -/
def SourceLetResult (context : Fir.Wasm.Context) (sourceRuntime : RuntimeState)
    (sourceEnv : Env) (decl : Lean.Compiler.LCNF.LetDecl .impure)
    (nextRuntime : RuntimeState) (sourceValue : Value) : Prop :=
  let state : MachineState := {
    program := context.program
    control := .code (.return decl.fvarId)
    env := sourceEnv
    runtime := sourceRuntime }
  evalLetValue state decl = .ok (nextRuntime, .value sourceValue)

/-- Exact executable source behavior of an external `let`.  A direct foreign
call takes three interpreter steps: stage the named invocation, perform and
resume the external request, then consume the binding frame and enter the
continuation. -/
def SourceExternalLetResult (context : Fir.Wasm.Context)
    (externals : ExternalImpl) (sourceRuntime : RuntimeState) (sourceEnv : Env)
    (decl : Lean.Compiler.LCNF.LetDecl .impure)
    (continuation : Lean.Compiler.LCNF.Code .impure)
    (nextRuntime : RuntimeState) (sourceValue : Value) : Prop :=
  ExecSteps externals 3 {
      program := context.program
      control := .code (.let decl continuation)
      env := sourceEnv
      runtime := sourceRuntime } {
      program := context.program
      control := .code continuation
      env := bind sourceEnv decl.fvarId sourceValue
      runtime := nextRuntime }

/-- The two executable source paths for a zero-argument declaration. A cache
hit stages and binds the cached value in three steps; a miss additionally
consumes the interpreter's cache frame after evaluating the declaration. -/
inductive LazyCachePath where
  | hit
  | miss
  deriving Inhabited, BEq

def LazyCachePath.sourceSteps : LazyCachePath → Nat
  | .hit => 3
  | .miss => 4

def SourceLazyLetResult (path : LazyCachePath) (context : Fir.Wasm.Context)
    (externals : ExternalImpl) (sourceRuntime : RuntimeState) (sourceEnv : Env)
    (decl : Lean.Compiler.LCNF.LetDecl .impure)
    (continuation : Lean.Compiler.LCNF.Code .impure)
    (nextRuntime : RuntimeState) (sourceValue : Value) : Prop :=
  ExecSteps externals path.sourceSteps {
      program := context.program
      control := .code (.let decl continuation)
      env := sourceEnv
      runtime := sourceRuntime } {
      program := context.program
      control := .code continuation
      env := bind sourceEnv decl.fvarId sourceValue
      runtime := nextRuntime }

/-- Exact terminating source behavior for an internal named call or closure
application. The existential step count admits recursive callees without
placing fuel or a syntactic termination argument in the semantic boundary. -/
def SourceCallLetResult (context : Fir.Wasm.Context)
    (externals : ExternalImpl) (sourceRuntime : RuntimeState) (sourceEnv : Env)
    (decl : Lean.Compiler.LCNF.LetDecl .impure)
    (continuation : Lean.Compiler.LCNF.Code .impure)
    (nextRuntime : RuntimeState) (sourceValue : Value) : Prop :=
  ∃ count, ExecSteps externals count {
      program := context.program
      control := .code (.let decl continuation)
      env := sourceEnv
      runtime := sourceRuntime } {
      program := context.program
      control := .code continuation
      env := bind sourceEnv decl.fvarId sourceValue
      runtime := nextRuntime }

/-- One successful non-binding source instruction step. Quantifying over the
external implementation records that admitted mutation and ownership nodes are
internal runtime effects, not external calls. -/
def SourceEffectResult (context : Fir.Wasm.Context)
    (sourceRuntime nextRuntime : RuntimeState) (sourceEnv : Env)
    (code continuation : Lean.Compiler.LCNF.Code .impure) : Prop :=
  ∀ externals,
    executeStep externals {
        program := context.program
        control := .code code
        env := sourceEnv
        runtime := sourceRuntime } =
      .next {
        program := context.program
        control := .code continuation
        env := sourceEnv
        runtime := nextRuntime }

/-- Target store after one successful semantic host operation. -/
def successfulHostStore (initial : Wasm.Store RuntimeHost)
    (runtime : RuntimeState) (handles : HandleTable) : Wasm.Store RuntimeHost :=
  { initial with host := {
      initial.host with
      runtime
      handles
      fault? := none
      targetFailure? := none } }

/--
Semantic interface for one generated `let` prefix. It records the exact source
value step, preservation of the state relation after binding the result, and a
continuation-polymorphic Talos WP transformer for the adapted value code plus
destination store.
-/
def LetStepSimulates (context : Fir.Wasm.Context)
    (sourceFunction : Fir.Wasm.Function) (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv RuntimeHost)
    (decl : Lean.Compiler.LCNF.LetDecl .impure) (targetValue : Wasm.Program)
    (sourceRuntime nextRuntime : RuntimeState) (sourceEnv : Env)
    (sourceValue : Value)
    (targetStore nextStore : Wasm.Store RuntimeHost)
    (targetLocals nextLocals : Wasm.Locals) (resultIndex : Nat) : Prop :=
  SourceLetResult context sourceRuntime sourceEnv decl nextRuntime sourceValue ∧
    StateRelated sourceFunction sourceRuntime sourceEnv targetStore targetLocals ∧
    StateRelated sourceFunction nextRuntime
      (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals ∧
    ∀ (rest : Wasm.Program) (Q : Wasm.Assertion RuntimeHost)
        (tail : List Wasm.Value),
      Wasm.wp module rest Q nextStore { nextLocals with values := tail } hostEnv →
      Wasm.wp module (targetValue ++ .localSet resultIndex :: rest) Q
        targetStore { targetLocals with values := tail } hostEnv

/-- Semantic interface for one generated external-call `let`.  It mirrors
`LetStepSimulates`, but its source premise uses the installed deterministic
external implementation and the interpreter's complete three-step call
protocol. -/
def ExternalLetStepSimulates (context : Fir.Wasm.Context)
    (sourceFunction : Fir.Wasm.Function) (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv RuntimeHost) (externals : ExternalImpl)
    (decl : Lean.Compiler.LCNF.LetDecl .impure)
    (continuation : Lean.Compiler.LCNF.Code .impure)
    (targetValue : Wasm.Program)
    (sourceRuntime nextRuntime : RuntimeState) (sourceEnv : Env)
    (sourceValue : Value)
    (targetStore nextStore : Wasm.Store RuntimeHost)
    (targetLocals nextLocals : Wasm.Locals) (resultIndex : Nat) : Prop :=
  SourceExternalLetResult context externals sourceRuntime sourceEnv decl
      continuation nextRuntime sourceValue ∧
    StateRelated sourceFunction sourceRuntime sourceEnv targetStore targetLocals ∧
    StateRelated sourceFunction nextRuntime
      (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals ∧
    ∀ (rest : Wasm.Program) (Q : Wasm.Assertion RuntimeHost)
        (tail : List Wasm.Value),
      Wasm.wp module rest Q nextStore { nextLocals with values := tail } hostEnv →
      Wasm.wp module (targetValue ++ .localSet resultIndex :: rest) Q
        targetStore { targetLocals with values := tail } hostEnv

/-- Semantic boundary for lazy zero-argument calls. It records whether the
source took the three-step cache hit or four-step cache miss path while using
one continuation-polymorphic target transformer for the generated globals and
conditional miss body. -/
def LazyLetStepSimulates (path : LazyCachePath) (context : Fir.Wasm.Context)
    (sourceFunction : Fir.Wasm.Function) (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv RuntimeHost) (externals : ExternalImpl)
    (decl : Lean.Compiler.LCNF.LetDecl .impure)
    (continuation : Lean.Compiler.LCNF.Code .impure)
    (targetValue : Wasm.Program)
    (sourceRuntime nextRuntime : RuntimeState) (sourceEnv : Env)
    (sourceValue : Value)
    (targetStore nextStore : Wasm.Store RuntimeHost)
    (targetLocals nextLocals : Wasm.Locals) (resultIndex : Nat) : Prop :=
  SourceLazyLetResult path context externals sourceRuntime sourceEnv decl
      continuation nextRuntime sourceValue ∧
    StateRelated sourceFunction sourceRuntime sourceEnv targetStore targetLocals ∧
    StateRelated sourceFunction nextRuntime
      (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals ∧
    ∀ (rest : Wasm.Program) (Q : Wasm.Assertion RuntimeHost)
        (tail : List Wasm.Value),
      Wasm.wp module rest Q nextStore { nextLocals with values := tail } hostEnv →
      Wasm.wp module (targetValue ++ .localSet resultIndex :: rest) Q
        targetStore { targetLocals with values := tail } hostEnv

/-- Interprocedural semantic boundary for direct calls and generated closure
trampolines. Concrete proofs compose ordinary Wasm call WP with the closure
metadata/capture host rules; source recursion is summarized by its exact
finite `ExecSteps` witness. -/
def CallLetStepSimulates (context : Fir.Wasm.Context)
    (sourceFunction : Fir.Wasm.Function) (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv RuntimeHost) (externals : ExternalImpl)
    (decl : Lean.Compiler.LCNF.LetDecl .impure)
    (continuation : Lean.Compiler.LCNF.Code .impure)
    (targetValue : Wasm.Program)
    (sourceRuntime nextRuntime : RuntimeState) (sourceEnv : Env)
    (sourceValue : Value)
    (targetStore nextStore : Wasm.Store RuntimeHost)
    (targetLocals nextLocals : Wasm.Locals) (resultIndex : Nat) : Prop :=
  SourceCallLetResult context externals sourceRuntime sourceEnv decl
      continuation nextRuntime sourceValue ∧
    StateRelated sourceFunction sourceRuntime sourceEnv targetStore targetLocals ∧
    StateRelated sourceFunction nextRuntime
      (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals ∧
    ∀ (rest : Wasm.Program) (Q : Wasm.Assertion RuntimeHost)
        (tail : List Wasm.Value),
      Wasm.wp module rest Q nextStore { nextLocals with values := tail } hostEnv →
      Wasm.wp module (targetValue ++ .localSet resultIndex :: rest) Q
        targetStore { targetLocals with values := tail } hostEnv

/-- Proof obligation for the miss-only body between the flag test and cached
value load. Runtime/external call rules and atomic global writes discharge this
obligation without reopening the surrounding conditional. -/
def LazyMissBodySimulates
    (module : Wasm.Module) (hostEnv : Wasm.HostEnv RuntimeHost)
    (missBody : Wasm.Program) (valueIndex resultIndex : Nat)
    (targetStore nextStore : Wasm.Store RuntimeHost)
    (targetLocals nextLocals : Wasm.Locals) : Prop :=
  ∀ (rest : Wasm.Program) (Q : Wasm.Assertion RuntimeHost)
      (tail : List Wasm.Value),
    Wasm.wp module rest Q nextStore { nextLocals with values := tail } hostEnv →
    Wasm.wp module missBody
      (fun continuation => match continuation with
        | .Fallthrough bodyStore bodyLocals =>
            Wasm.wp module
              (.globalGet valueIndex :: .localSet resultIndex :: rest)
              Q bodyStore { bodyLocals with values := tail } hostEnv
        | .Break 0 bodyStore bodyLocals =>
            Wasm.wp module
              (.globalGet valueIndex :: .localSet resultIndex :: rest)
              Q bodyStore { bodyLocals with values := tail } hostEnv
        | .Break (level + 1) bodyStore bodyLocals =>
            Q (.Break level bodyStore bodyLocals)
        | other => Q other)
      targetStore { targetLocals with values := tail } hostEnv

theorem lazyLetStepSimulates_hit
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv RuntimeHost}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {missBody : Wasm.Program} {flagIndex valueIndex resultIndex : Nat}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {sourceValue : Value} {targetStore nextStore : Wasm.Store RuntimeHost}
    {targetLocals nextLocals : Wasm.Locals} {cached : Wasm.Value}
    (sourceStep : SourceLazyLetResult .hit context targetStore.host.externals
      sourceRuntime sourceEnv decl continuation nextRuntime sourceValue)
    (stateRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      targetStore targetLocals)
    (hFlag : targetStore.globals.globals[flagIndex]? = some (.i32 1))
    (hValue : targetStore.globals.globals[valueIndex]? = some cached)
    (hSet : targetLocals.set? resultIndex cached = some nextLocals)
    (nextStoreEq : nextStore = targetStore)
    (nextStateRelated : StateRelated sourceFunction nextRuntime
      (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals) :
    LazyLetStepSimulates .hit context sourceFunction module hostEnv
      targetStore.host.externals decl continuation
      [.globalGet flagIndex, .iff 0 0 [] missBody, .globalGet valueIndex]
      sourceRuntime nextRuntime sourceEnv sourceValue targetStore nextStore
      targetLocals nextLocals resultIndex := by
  refine ⟨sourceStep, stateRelated, nextStateRelated, ?_⟩
  intro rest Q tail continued
  subst nextStore
  apply wp_lazy_cache_hit hFlag hValue
  apply wp_localSet_of_set hSet
  exact continued

theorem lazyLetStepSimulates_miss
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv RuntimeHost}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {missBody : Wasm.Program} {flagIndex valueIndex resultIndex : Nat}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {sourceValue : Value} {targetStore nextStore : Wasm.Store RuntimeHost}
    {targetLocals nextLocals : Wasm.Locals}
    (sourceStep : SourceLazyLetResult .miss context targetStore.host.externals
      sourceRuntime sourceEnv decl continuation nextRuntime sourceValue)
    (stateRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      targetStore targetLocals)
    (hFlag : targetStore.globals.globals[flagIndex]? = some (.i32 0))
    (missStep : LazyMissBodySimulates module hostEnv missBody valueIndex
      resultIndex targetStore nextStore targetLocals nextLocals)
    (nextStateRelated : StateRelated sourceFunction nextRuntime
      (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals) :
    LazyLetStepSimulates .miss context sourceFunction module hostEnv
      targetStore.host.externals decl continuation
      [.globalGet flagIndex, .iff 0 0 [] missBody, .globalGet valueIndex]
      sourceRuntime nextRuntime sourceEnv sourceValue targetStore nextStore
      targetLocals nextLocals resultIndex := by
  refine ⟨sourceStep, stateRelated, nextStateRelated, ?_⟩
  intro rest Q tail continued
  apply wp_lazy_cache_miss (rest := .localSet resultIndex :: rest) hFlag
  convert missStep rest Q tail continued using 1
  funext continuation
  cases continuation with
  | Break level bodyStore bodyLocals => cases level <;> rfl
  | _ => rfl

theorem externalLetStepSimulates_of_call
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv RuntimeHost}
    {spec : Wasm.HostSpec RuntimeHost} {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {sourceValue : Value}
    {targetStore nextStore : Wasm.Store RuntimeHost}
    {targetLocals nextLocals : Wasm.Locals} {resultIndex : Nat}
    {indices : List Nat} {physicalArgs : List Wasm.Value}
    (operation : ExternalOperation) (resultKind : AbiKind)
    (semanticArgs : Array Value) (response : ExternalResponse)
    (after : HandleTable) (physicalResult : Wasm.Value)
    (sourceStep : SourceExternalLetResult context targetStore.host.externals
      sourceRuntime sourceEnv decl continuation nextRuntime sourceValue)
    (stateRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      targetStore targetLocals)
    (hGets : List.Forall₂
      (fun index value => targetLocals.get index = some value)
      indices physicalArgs)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some
      (hostContract (.external operation)))
    (hParams : imp.params.length = physicalArgs.length)
    (hResults : imp.results.length = 1)
    (resultSignature : operation.signature.results = #[resultKind])
    (decoded : decodeArgs targetStore.host.handles operation.signature.params
      physicalArgs = .ok semanticArgs)
    (called : targetStore.host.externals.call (operation.request semanticArgs)
      targetStore.host.runtime = .ok response)
    (encoded : encodeValue targetStore.host.handles resultKind response.value =
      .ok (after, physicalResult))
    (hSet : targetLocals.set? resultIndex physicalResult = some nextLocals)
    (nextStoreEq : nextStore = {
      targetStore with host := {
        targetStore.host with
        runtime := applyExternalResponse (operation.request semanticArgs)
          targetStore.host.runtime response
        handles := after
        fault? := none
        targetFailure? := none } })
    (nextStateRelated : StateRelated sourceFunction nextRuntime
      (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals) :
    ExternalLetStepSimulates context sourceFunction module hostEnv
      targetStore.host.externals decl continuation
      (indices.map Wasm.Instruction.localGet ++ [.call id])
      sourceRuntime nextRuntime sourceEnv sourceValue targetStore nextStore
      targetLocals nextLocals resultIndex := by
  refine ⟨sourceStep, stateRelated, nextStateRelated, ?_⟩
  intro rest Q tail continued
  subst nextStore
  simpa [List.append_assoc] using
    (wp_external_let operation resultKind semanticArgs response after
      physicalResult tail hGets hImp hSat hi hContract hParams hResults
      resultSignature decoded called encoded hSet continued)

/-- Semantic interface for one generated no-result effect prefix. It packages
the real compiler/adapter witness, the exact source step, preservation of the
state relation, and a continuation-polymorphic Talos WP transformer. -/
def EffectStepSimulates (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module) (sourceFunction : Fir.Wasm.Function)
    (labels : List Lean.FVarId) (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv RuntimeHost)
    (sourceRuntime nextRuntime : RuntimeState) (sourceEnv : Env)
    (code continuation : Lean.Compiler.LCNF.Code .impure)
    (target targetRest : Wasm.Program)
    (targetStore nextStore : Wasm.Store RuntimeHost)
    (targetLocals : Wasm.Locals) : Prop :=
  SourceEffectResult context sourceRuntime nextRuntime sourceEnv code continuation ∧
    CodeAdapted context sourceModule sourceFunction labels code target ∧
    StateRelated sourceFunction sourceRuntime sourceEnv targetStore targetLocals ∧
    StateRelated sourceFunction nextRuntime sourceEnv nextStore targetLocals ∧
    ∀ (Q : Wasm.Assertion RuntimeHost) (tail : List Wasm.Value),
      Wasm.wp module targetRest Q nextStore
          { targetLocals with values := tail } hostEnv →
        Wasm.wp module target Q targetStore
          { targetLocals with values := tail } hostEnv

/-- Resolve one related source binding at an already known adapter slot/kind. -/
theorem StateRelated.resolve
    {sourceFunction : Fir.Wasm.Function} {sourceRuntime : RuntimeState}
    {sourceEnv : Env} {targetStore : Wasm.Store RuntimeHost}
    {targetLocals : Wasm.Locals} {fvar : Lean.FVarId} {sourceValue : Value}
    {index : Nat} {kind : AbiKind}
    (related :
      StateRelated sourceFunction sourceRuntime sourceEnv targetStore targetLocals)
    (sourceLookup : lookup sourceEnv fvar = some sourceValue)
    (found : findFVar? (functionBindings sourceFunction) fvar = some index)
    (kindAt : (functionBindings sourceFunction)[index]?.map Prod.snd = some kind) :
    ∃ physical,
      targetLocals.get index = some physical ∧
      DecodesValue targetStore.host.handles kind physical sourceValue := by
  rcases related.2.2.2.2 sourceLookup with
    ⟨actualIndex, actualKind, physical, actualFound, actualKindAt,
      targetLookup, decoded⟩
  rw [found] at actualFound
  injection actualFound with indexEq
  subst actualIndex
  rw [kindAt] at actualKindAt
  injection actualKindAt with kindEq
  subst actualKind
  exact ⟨physical, targetLookup, decoded⟩

/-- Clearing already-clear host failure channels is observationally the identity. -/
theorem StateRelated.clearFailures
    {sourceFunction : Fir.Wasm.Function} {sourceRuntime : RuntimeState}
    {sourceEnv : Env} {targetStore : Wasm.Store RuntimeHost}
    {targetLocals : Wasm.Locals}
    (related :
      StateRelated sourceFunction sourceRuntime sourceEnv targetStore targetLocals) :
    { targetStore with host := {
        targetStore.host with
        fault? := none
        targetFailure? := none } } =
      targetStore := by
  rcases targetStore with
    ⟨globals, mem, extraMems, dataSegments, tables, elementSegments, exns,
      gcHeap, host⟩
  rcases host with ⟨runtime, handles, fault, targetFailure⟩
  simp_all [StateRelated]

/-- Base semantic rule for a generated source return. -/
theorem codeWP_return
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv RuntimeHost}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {targetStore : Wasm.Store RuntimeHost} {targetLocals : Wasm.Locals}
    {result : Lean.FVarId} {sourceValue : Value} {kind : AbiKind}
    {resultIndex : Nat} {tail : List Wasm.Value}
    (localCompiled :
      Fir.Wasm.getLocal context result = .ok (.localGet result, kind))
    (resultFound :
      findFVar? (functionBindings sourceFunction) result = some resultIndex)
    (kindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some kind)
    (sourceLookup : lookup sourceEnv result = some sourceValue)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv targetStore targetLocals) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv (.return result)
      [.localGet resultIndex, .ret] targetStore targetLocals tail
      (ReturnPost sourceRuntime sourceValue kind tail) := by
  rcases stateRelated.resolve sourceLookup resultFound kindAt with
    ⟨physical, targetLookup, decoded⟩
  refine ⟨codeAdapted_return localCompiled resultFound, stateRelated, ?_⟩
  rw [Wasm.wp_localGet_cons]
  have targetLookupWithStack :
      ({ targetLocals with values := tail } : Wasm.Locals).get resultIndex =
        some physical := by
    simpa [Wasm.Locals.get] using targetLookup
  simp only [targetLookupWithStack]
  rw [Wasm.wp_ret_cons]
  exact ⟨targetStore, physical, rfl, stateRelated.1, decoded⟩

/--
Generic recursive semantic rule for a direct `let`: an operation-specific
`LetStepSimulates` witness plugs into the compiler/adapter composition rule and
the already established continuation `CodeWP`.
-/
theorem codeWP_let
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv RuntimeHost}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {sourceValue : Value} {valueCode : List Fir.Wasm.Instruction}
    {targetValue targetRest : Wasm.Program}
    {targetStore nextStore : Wasm.Store RuntimeHost}
    {targetLocals nextLocals : Wasm.Locals} {resultIndex : Nat}
    {tail : List Wasm.Value} {Q : Wasm.Assertion RuntimeHost}
    (valueCompiled : Fir.Wasm.compileLetValue context decl = .ok valueCode)
    (valueAdapted :
      instructions sourceModule sourceFunction labels valueCode = .ok targetValue)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (step :
      LetStepSimulates context sourceFunction module hostEnv decl targetValue
        sourceRuntime nextRuntime sourceEnv sourceValue targetStore nextStore
        targetLocals nextLocals resultIndex)
    (continued :
      CodeWP context sourceModule sourceFunction labels module hostEnv
        nextRuntime (bind sourceEnv decl.fvarId sourceValue) continuation targetRest
        nextStore nextLocals tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv (.let decl continuation)
      (targetValue ++ .localSet resultIndex :: targetRest)
      targetStore targetLocals tail Q := by
  rcases step with ⟨sourceStep, initialRelated, nextRelated, stepWP⟩
  rcases continued with ⟨continuationAdapted, continuedRelated, continuedWP⟩
  refine ⟨codeAdapted_let valueCompiled valueAdapted resultFound
      continuationAdapted, initialRelated, ?_⟩
  exact stepWP targetRest Q tail continuedWP

/-- Recursive `CodeWP` rule for an external-call `let`.  The target
composition is identical to an internal value binding, while the source
component is the explicit three-step external protocol carried by
`ExternalLetStepSimulates`. -/
theorem codeWP_externalLet
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv RuntimeHost} {externals : ExternalImpl}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {sourceValue : Value} {valueCode : List Fir.Wasm.Instruction}
    {targetValue targetRest : Wasm.Program}
    {targetStore nextStore : Wasm.Store RuntimeHost}
    {targetLocals nextLocals : Wasm.Locals} {resultIndex : Nat}
    {tail : List Wasm.Value} {Q : Wasm.Assertion RuntimeHost}
    (valueCompiled : Fir.Wasm.compileLetValue context decl = .ok valueCode)
    (valueAdapted :
      instructions sourceModule sourceFunction labels valueCode = .ok targetValue)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (step :
      ExternalLetStepSimulates context sourceFunction module hostEnv externals
        decl continuation targetValue sourceRuntime nextRuntime sourceEnv
        sourceValue targetStore nextStore targetLocals nextLocals resultIndex)
    (continued :
      CodeWP context sourceModule sourceFunction labels module hostEnv
        nextRuntime (bind sourceEnv decl.fvarId sourceValue) continuation targetRest
        nextStore nextLocals tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv (.let decl continuation)
      (targetValue ++ .localSet resultIndex :: targetRest)
      targetStore targetLocals tail Q := by
  rcases step with ⟨_, initialRelated, _, stepWP⟩
  rcases continued with ⟨continuationAdapted, _, continuedWP⟩
  refine ⟨codeAdapted_let valueCompiled valueAdapted resultFound
      continuationAdapted, initialRelated, ?_⟩
  exact stepWP targetRest Q tail continuedWP

/-- Recursive `CodeWP` rule for either lazy cache path. The compiler and
adapter witnesses fix the generated globals/conditional prefix, while the
path-specific simulation supplies its semantic WP transformer. -/
theorem codeWP_lazyLet
    {path : LazyCachePath} {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv RuntimeHost} {externals : ExternalImpl}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {sourceValue : Value} {valueCode : List Fir.Wasm.Instruction}
    {targetValue targetRest : Wasm.Program}
    {targetStore nextStore : Wasm.Store RuntimeHost}
    {targetLocals nextLocals : Wasm.Locals} {resultIndex : Nat}
    {tail : List Wasm.Value} {Q : Wasm.Assertion RuntimeHost}
    (valueCompiled : Fir.Wasm.compileLetValue context decl = .ok valueCode)
    (valueAdapted :
      instructions sourceModule sourceFunction labels valueCode = .ok targetValue)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (step : LazyLetStepSimulates path context sourceFunction module hostEnv
      externals decl continuation targetValue sourceRuntime nextRuntime sourceEnv
      sourceValue targetStore nextStore targetLocals nextLocals resultIndex)
    (continued :
      CodeWP context sourceModule sourceFunction labels module hostEnv
        nextRuntime (bind sourceEnv decl.fvarId sourceValue) continuation targetRest
        nextStore nextLocals tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv (.let decl continuation)
      (targetValue ++ .localSet resultIndex :: targetRest)
      targetStore targetLocals tail Q := by
  rcases step with ⟨_, initialRelated, _, stepWP⟩
  rcases continued with ⟨continuationAdapted, _, continuedWP⟩
  refine ⟨codeAdapted_let valueCompiled valueAdapted resultFound
      continuationAdapted, initialRelated, ?_⟩
  exact stepWP targetRest Q tail continuedWP

/-- Recursive `CodeWP` rule for a terminating interprocedural call prefix.
This covers both ordinary declaration calls (including recursion) and the
non-circular closure trampoline. -/
theorem codeWP_callLet
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv RuntimeHost} {externals : ExternalImpl}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {sourceValue : Value} {valueCode : List Fir.Wasm.Instruction}
    {targetValue targetRest : Wasm.Program}
    {targetStore nextStore : Wasm.Store RuntimeHost}
    {targetLocals nextLocals : Wasm.Locals} {resultIndex : Nat}
    {tail : List Wasm.Value} {Q : Wasm.Assertion RuntimeHost}
    (valueCompiled : Fir.Wasm.compileLetValue context decl = .ok valueCode)
    (valueAdapted :
      instructions sourceModule sourceFunction labels valueCode = .ok targetValue)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (step : CallLetStepSimulates context sourceFunction module hostEnv externals
      decl continuation targetValue sourceRuntime nextRuntime sourceEnv
      sourceValue targetStore nextStore targetLocals nextLocals resultIndex)
    (continued :
      CodeWP context sourceModule sourceFunction labels module hostEnv
        nextRuntime (bind sourceEnv decl.fvarId sourceValue) continuation targetRest
        nextStore nextLocals tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv (.let decl continuation)
      (targetValue ++ .localSet resultIndex :: targetRest)
      targetStore targetLocals tail Q := by
  rcases step with ⟨_, initialRelated, _, stepWP⟩
  rcases continued with ⟨continuationAdapted, _, continuedWP⟩
  refine ⟨codeAdapted_let valueCompiled valueAdapted resultFound
      continuationAdapted, initialRelated, ?_⟩
  exact stepWP targetRest Q tail continuedWP

/--
Natural-literal instantiation of `LetStepSimulates`. This is the first complete
semantic `let` prefix: source evaluation allocates the literal, the semantic
host encodes it, the generated local write extends `EnvLocalsRelated`, and the
operation-specific WP rule resumes an arbitrary continuation.
-/
theorem letStepSimulates_naturalLiteral
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv RuntimeHost}
    {spec : Wasm.HostSpec RuntimeHost} {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure} {sourceEnv : Env}
    {initial : Wasm.Store RuntimeHost} {locals updated : Wasm.Locals}
    {resultIndex : Nat} {value : Nat} {after : HandleTable} {handle : Handle}
    (valueEq : decl.value = .lit (.nat value))
    (initialRelated :
      StateRelated sourceFunction initial.host.runtime sourceEnv initial locals)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (kindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some .tobject)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract :
      spec.contracts[id]? = some (hostContract (.naturalLiteral value .tobject)))
    (hParams : imp.params = [])
    (hResults : imp.results = [.i32])
    (encoded :
      initial.host.handles.encode .tobject
          (literal initial.host.runtime (.nat value)).2 = .ok (after, handle))
    (targetSet : locals.set? resultIndex (.i32 handle) = some updated) :
    LetStepSimulates context sourceFunction module hostEnv decl [.call id]
      initial.host.runtime (literal initial.host.runtime (.nat value)).1 sourceEnv
      (literal initial.host.runtime (.nat value)).2 initial
      (successfulHostStore initial (literal initial.host.runtime (.nat value)).1 after)
      locals updated resultIndex := by
  refine ⟨?_, initialRelated, ?_, ?_⟩
  · unfold SourceLetResult
    simp [evalLetValue, valueEq]
    rfl
  · refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · exact handleTableInvariant_of_encode initialRelated.2.2.2.1 (by rfl) encoded
    · exact EnvLocalsRelated.bind_handle_of_encode
        initialRelated.2.2.2.2 initialRelated.2.2.2.1 resultFound kindAt
        (by rfl) encoded targetSet
  · intro rest Q tail continued
    simpa [successfulHostStore] using
      wp_naturalLiteral_let initial value after handle tail
        hImp hSat hi hContract hParams hResults encoded targetSet continued

/--
Recursive semantic rule for a natural-literal `let`. The conclusion contains
the real compiled/adapted prefix and the same `ReturnPost` (or other assertion)
proved by the recursively supplied continuation.
-/
theorem codeWP_naturalLiteral_let
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv RuntimeHost} {spec : Wasm.HostSpec RuntimeHost}
    {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {sourceEnv : Env} {initial : Wasm.Store RuntimeHost}
    {locals updated : Wasm.Locals} {resultIndex : Nat}
    {value : Nat} {after : HandleTable} {handle : Handle}
    {targetRest : Wasm.Program} {tail : List Wasm.Value}
    {Q : Wasm.Assertion RuntimeHost}
    (valueEq : decl.value = .lit (.nat value))
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.call (.runtime (.literal (.nat value) .tobject))])
    (callFound :
      callIndex? sourceModule (.runtime (.literal (.nat value) .tobject)) = some id)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (kindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some .tobject)
    (initialRelated :
      StateRelated sourceFunction initial.host.runtime sourceEnv initial locals)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract :
      spec.contracts[id]? = some (hostContract (.naturalLiteral value .tobject)))
    (hParams : imp.params = [])
    (hResults : imp.results = [.i32])
    (encoded :
      initial.host.handles.encode .tobject
          (literal initial.host.runtime (.nat value)).2 = .ok (after, handle))
    (targetSet : locals.set? resultIndex (.i32 handle) = some updated)
    (continued :
      CodeWP context sourceModule sourceFunction labels module hostEnv
        (literal initial.host.runtime (.nat value)).1
        (bind sourceEnv decl.fvarId (literal initial.host.runtime (.nat value)).2)
        continuation targetRest
        (successfulHostStore initial (literal initial.host.runtime (.nat value)).1 after)
        updated tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      initial.host.runtime sourceEnv (.let decl continuation)
      (.call id :: .localSet resultIndex :: targetRest)
      initial locals tail Q := by
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          [.call (.runtime (.literal (.nat value) .tobject))] = .ok [.call id] := by
    simp [instructions, instruction, callFound]
    rfl
  have step := letStepSimulates_naturalLiteral (context := context)
    valueEq initialRelated resultFound kindAt hImp hSat hi hContract hParams hResults
    encoded targetSet
  simpa using codeWP_let (context := context) valueCompiled valueAdapted resultFound
    step continued

/--
First closed straight-line W4 theorem: a natural literal is evaluated, encoded,
stored in its generated local, loaded again by the compiled return, and decoded
to the exact source value under a fuel-free Talos weakest precondition.
-/
theorem codeWP_naturalLiteral_return
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv RuntimeHost} {spec : Wasm.HostSpec RuntimeHost}
    {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure} {sourceEnv : Env}
    {initial : Wasm.Store RuntimeHost} {locals updated : Wasm.Locals}
    {resultIndex : Nat} {value : Nat} {after : HandleTable} {handle : Handle}
    (valueEq : decl.value = .lit (.nat value))
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.call (.runtime (.literal (.nat value) .tobject))])
    (localCompiled :
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, .tobject))
    (callFound :
      callIndex? sourceModule (.runtime (.literal (.nat value) .tobject)) = some id)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (kindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some .tobject)
    (initialRelated :
      StateRelated sourceFunction initial.host.runtime sourceEnv initial locals)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract :
      spec.contracts[id]? = some (hostContract (.naturalLiteral value .tobject)))
    (hParams : imp.params = [])
    (hResults : imp.results = [.i32])
    (encoded :
      initial.host.handles.encode .tobject
          (literal initial.host.runtime (.nat value)).2 = .ok (after, handle))
    (targetSet : locals.set? resultIndex (.i32 handle) = some updated) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      initial.host.runtime sourceEnv (.let decl (.return decl.fvarId))
      [.call id, .localSet resultIndex, .localGet resultIndex, .ret]
      initial locals []
      (ReturnPost (literal initial.host.runtime (.nat value)).1
        (literal initial.host.runtime (.nat value)).2 .tobject []) := by
  have step := letStepSimulates_naturalLiteral (context := context)
    valueEq initialRelated resultFound kindAt hImp hSat hi hContract hParams hResults
    encoded targetSet
  have continued := codeWP_return
    (context := context) (sourceModule := sourceModule)
    (sourceFunction := sourceFunction) (labels := labels) (module := module)
    (hostEnv := hostEnv) (tail := []) localCompiled resultFound kindAt
    (lookup_bind_self sourceEnv decl.fvarId
      (literal initial.host.runtime (.nat value)).2)
    step.2.2.1
  exact codeWP_naturalLiteral_let valueEq valueCompiled callFound resultFound kindAt
    initialRelated hImp hSat hi hContract hParams hResults encoded targetSet continued

/-- String-literal instance of the reusable direct-`let` simulation boundary. -/
theorem letStepSimulates_stringLiteral
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv RuntimeHost}
    {spec : Wasm.HostSpec RuntimeHost} {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure} {sourceEnv : Env}
    {initial : Wasm.Store RuntimeHost} {locals updated : Wasm.Locals}
    {resultIndex : Nat} {value : String} {after : HandleTable} {handle : Handle}
    (valueEq : decl.value = .lit (.str value))
    (initialRelated :
      StateRelated sourceFunction initial.host.runtime sourceEnv initial locals)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (kindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some .object)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract :
      spec.contracts[id]? = some (hostContract (.stringLiteral value .object)))
    (hParams : imp.params = [])
    (hResults : imp.results = [.i32])
    (encoded :
      initial.host.handles.encode .object
          (literal initial.host.runtime (.str value)).2 = .ok (after, handle))
    (targetSet : locals.set? resultIndex (.i32 handle) = some updated) :
    LetStepSimulates context sourceFunction module hostEnv decl [.call id]
      initial.host.runtime (literal initial.host.runtime (.str value)).1 sourceEnv
      (literal initial.host.runtime (.str value)).2 initial
      (successfulHostStore initial (literal initial.host.runtime (.str value)).1 after)
      locals updated resultIndex := by
  refine ⟨?_, initialRelated, ?_, ?_⟩
  · unfold SourceLetResult
    simp [evalLetValue, valueEq]
    rfl
  · refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · exact handleTableInvariant_of_encode initialRelated.2.2.2.1 (by rfl) encoded
    · exact EnvLocalsRelated.bind_handle_of_encode
        initialRelated.2.2.2.2 initialRelated.2.2.2.1 resultFound kindAt
        (by rfl) encoded targetSet
  · intro rest Q tail continued
    simpa [successfulHostStore] using
      wp_stringLiteral_let initial value after handle tail
        hImp hSat hi hContract hParams hResults encoded targetSet continued

/-- Recursive semantic rule for a string-literal `let`. -/
theorem codeWP_stringLiteral_let
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv RuntimeHost} {spec : Wasm.HostSpec RuntimeHost}
    {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {sourceEnv : Env} {initial : Wasm.Store RuntimeHost}
    {locals updated : Wasm.Locals} {resultIndex : Nat}
    {value : String} {after : HandleTable} {handle : Handle}
    {targetRest : Wasm.Program} {tail : List Wasm.Value}
    {Q : Wasm.Assertion RuntimeHost}
    (valueEq : decl.value = .lit (.str value))
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.call (.runtime (.literal (.str value) .object))])
    (callFound :
      callIndex? sourceModule (.runtime (.literal (.str value) .object)) = some id)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (kindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some .object)
    (initialRelated :
      StateRelated sourceFunction initial.host.runtime sourceEnv initial locals)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract :
      spec.contracts[id]? = some (hostContract (.stringLiteral value .object)))
    (hParams : imp.params = [])
    (hResults : imp.results = [.i32])
    (encoded :
      initial.host.handles.encode .object
          (literal initial.host.runtime (.str value)).2 = .ok (after, handle))
    (targetSet : locals.set? resultIndex (.i32 handle) = some updated)
    (continued :
      CodeWP context sourceModule sourceFunction labels module hostEnv
        (literal initial.host.runtime (.str value)).1
        (bind sourceEnv decl.fvarId (literal initial.host.runtime (.str value)).2)
        continuation targetRest
        (successfulHostStore initial (literal initial.host.runtime (.str value)).1 after)
        updated tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      initial.host.runtime sourceEnv (.let decl continuation)
      (.call id :: .localSet resultIndex :: targetRest)
      initial locals tail Q := by
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          [.call (.runtime (.literal (.str value) .object))] = .ok [.call id] := by
    simp [instructions, instruction, callFound]
    rfl
  have step := letStepSimulates_stringLiteral (context := context)
    valueEq initialRelated resultFound kindAt hImp hSat hi hContract hParams hResults
    encoded targetSet
  simpa using codeWP_let (context := context) valueCompiled valueAdapted resultFound
    step continued

/-- Closed string-literal `let; return` correctness theorem. -/
theorem codeWP_stringLiteral_return
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv RuntimeHost} {spec : Wasm.HostSpec RuntimeHost}
    {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure} {sourceEnv : Env}
    {initial : Wasm.Store RuntimeHost} {locals updated : Wasm.Locals}
    {resultIndex : Nat} {value : String} {after : HandleTable} {handle : Handle}
    (valueEq : decl.value = .lit (.str value))
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.call (.runtime (.literal (.str value) .object))])
    (localCompiled :
      Fir.Wasm.getLocal context decl.fvarId =
        .ok (.localGet decl.fvarId, .object))
    (callFound :
      callIndex? sourceModule (.runtime (.literal (.str value) .object)) = some id)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (kindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some .object)
    (initialRelated :
      StateRelated sourceFunction initial.host.runtime sourceEnv initial locals)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract :
      spec.contracts[id]? = some (hostContract (.stringLiteral value .object)))
    (hParams : imp.params = [])
    (hResults : imp.results = [.i32])
    (encoded :
      initial.host.handles.encode .object
          (literal initial.host.runtime (.str value)).2 = .ok (after, handle))
    (targetSet : locals.set? resultIndex (.i32 handle) = some updated) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      initial.host.runtime sourceEnv (.let decl (.return decl.fvarId))
      [.call id, .localSet resultIndex, .localGet resultIndex, .ret]
      initial locals []
      (ReturnPost (literal initial.host.runtime (.str value)).1
        (literal initial.host.runtime (.str value)).2 .object []) := by
  have step := letStepSimulates_stringLiteral (context := context)
    valueEq initialRelated resultFound kindAt hImp hSat hi hContract hParams hResults
    encoded targetSet
  have continued := codeWP_return
    (context := context) (sourceModule := sourceModule)
    (sourceFunction := sourceFunction) (labels := labels) (module := module)
    (hostEnv := hostEnv) (tail := []) localCompiled resultFound kindAt
    (lookup_bind_self sourceEnv decl.fvarId
      (literal initial.host.runtime (.str value)).2)
    step.2.2.1
  exact codeWP_stringLiteral_let valueEq valueCompiled callFound resultFound kindAt
    initialRelated hImp hSat hi hContract hParams hResults encoded targetSet continued

/-- Constructor-allocation instance of the reusable direct-`let` boundary. -/
theorem letStepSimulates_constructor
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv RuntimeHost}
    {spec : Wasm.HostSpec RuntimeHost} {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {info : Lean.Compiler.LCNF.CtorInfo}
    {args : Array (Lean.Compiler.LCNF.Arg .impure)} {sourceEnv : Env}
    {initial : Wasm.Store RuntimeHost} {locals updated : Wasm.Locals}
    {indices : List Nat} {physicalArgs : List Wasm.Value}
    {semanticArgs : Array Value} {nextRuntime : RuntimeState}
    {sourceValue : Value} {resultIndex : Nat}
    {fieldKinds : Array AbiKind} {resultKind : AbiKind}
    {after : HandleTable} {handle : Handle}
    (valueEq : decl.value = .ctor info args)
    (evaluated : evalArgs sourceEnv args = .ok semanticArgs)
    (allocated :
      allocCtor initial.host.runtime info semanticArgs = .ok (nextRuntime, sourceValue))
    (initialRelated :
      StateRelated sourceFunction initial.host.runtime sourceEnv initial locals)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (kindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some resultKind)
    (hGets :
      List.Forall₂ (fun index physical => locals.get index = some physical)
        indices physicalArgs)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract :
      spec.contracts[id]? =
        some (hostContract (.allocCtor info fieldKinds resultKind)))
    (hParams : imp.params.length = physicalArgs.length)
    (hResults : imp.results.length = 1)
    (decoded :
      decodeArgs initial.host.handles fieldKinds physicalArgs = .ok semanticArgs)
    (usesHandle : resultKind.usesHandle = true)
    (encoded :
      initial.host.handles.encode resultKind sourceValue = .ok (after, handle))
    (targetSet : locals.set? resultIndex (.i32 handle) = some updated) :
    LetStepSimulates context sourceFunction module hostEnv decl
      (indices.map Wasm.Instruction.localGet ++ [.call id])
      initial.host.runtime nextRuntime sourceEnv sourceValue initial
      (successfulHostStore initial nextRuntime after) locals updated resultIndex := by
  refine ⟨?_, initialRelated, ?_, ?_⟩
  · unfold SourceLetResult
    simp [evalLetValue, valueEq, evaluated]
    change ((fun result : RuntimeState × Value =>
      (result.1, LetAction.value result.2)) <$>
        allocCtor initial.host.runtime info semanticArgs) =
      .ok (nextRuntime, .value sourceValue)
    rw [allocated]
    rfl
  · refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · exact handleTableInvariant_of_encode initialRelated.2.2.2.1 usesHandle encoded
    · exact EnvLocalsRelated.bind_handle_of_encode
        initialRelated.2.2.2.2 initialRelated.2.2.2.1 resultFound kindAt
        usesHandle encoded targetSet
  · intro rest Q tail continued
    simpa [successfulHostStore, List.append_assoc] using
      wp_constructor_let info fieldKinds resultKind semanticArgs nextRuntime sourceValue
        after handle tail hGets hImp hSat hi hContract hParams hResults decoded
        allocated usesHandle encoded targetSet continued

/-- Recursive semantic rule for a constructor-allocation `let`. -/
theorem codeWP_constructor_let
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv RuntimeHost} {spec : Wasm.HostSpec RuntimeHost}
    {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {info : Lean.Compiler.LCNF.CtorInfo}
    {args : Array (Lean.Compiler.LCNF.Arg .impure)} {sourceEnv : Env}
    {initial : Wasm.Store RuntimeHost} {locals updated : Wasm.Locals}
    {fvarIds : List Lean.FVarId} {indices : List Nat}
    {physicalArgs : List Wasm.Value} {semanticArgs : Array Value}
    {nextRuntime : RuntimeState} {sourceValue : Value} {resultIndex : Nat}
    {fieldKinds : Array AbiKind} {resultKind : AbiKind}
    {after : HandleTable} {handle : Handle}
    {targetRest : Wasm.Program} {tail : List Wasm.Value}
    {Q : Wasm.Assertion RuntimeHost}
    (valueEq : decl.value = .ctor info args)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok (fvarIds.map Fir.Wasm.Instruction.localGet ++
          [.call (.runtime (.allocCtor info fieldKinds resultKind))]))
    (argumentsFound :
      List.Forall₂
        (fun fvarId index =>
          findFVar? (functionBindings sourceFunction) fvarId = some index)
        fvarIds indices)
    (callFound :
      callIndex? sourceModule (.runtime (.allocCtor info fieldKinds resultKind)) =
        some id)
    (evaluated : evalArgs sourceEnv args = .ok semanticArgs)
    (allocated :
      allocCtor initial.host.runtime info semanticArgs = .ok (nextRuntime, sourceValue))
    (initialRelated :
      StateRelated sourceFunction initial.host.runtime sourceEnv initial locals)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (kindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some resultKind)
    (hGets :
      List.Forall₂ (fun index physical => locals.get index = some physical)
        indices physicalArgs)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract :
      spec.contracts[id]? =
        some (hostContract (.allocCtor info fieldKinds resultKind)))
    (hParams : imp.params.length = physicalArgs.length)
    (hResults : imp.results.length = 1)
    (decoded :
      decodeArgs initial.host.handles fieldKinds physicalArgs = .ok semanticArgs)
    (usesHandle : resultKind.usesHandle = true)
    (encoded :
      initial.host.handles.encode resultKind sourceValue = .ok (after, handle))
    (targetSet : locals.set? resultIndex (.i32 handle) = some updated)
    (continued :
      CodeWP context sourceModule sourceFunction labels module hostEnv
        nextRuntime (bind sourceEnv decl.fvarId sourceValue) continuation targetRest
        (successfulHostStore initial nextRuntime after) updated tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      initial.host.runtime sourceEnv (.let decl continuation)
      (indices.map Wasm.Instruction.localGet ++
        .call id :: .localSet resultIndex :: targetRest)
      initial locals tail Q := by
  have argumentsAdapted := instructions_localGets
    (sourceModule := sourceModule) (sourceFunction := sourceFunction)
    (labels := labels) argumentsFound
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          (fvarIds.map Fir.Wasm.Instruction.localGet ++
            [.call (.runtime (.allocCtor info fieldKinds resultKind))]) =
        .ok (indices.map Wasm.Instruction.localGet ++ [.call id]) := by
    rw [instructions_append, argumentsAdapted]
    simp [instructions, instruction, callFound]
  have step := letStepSimulates_constructor (context := context)
    valueEq evaluated allocated initialRelated resultFound kindAt hGets hImp hSat hi
    hContract hParams hResults decoded usesHandle encoded targetSet
  simpa [List.append_assoc] using
    codeWP_let (context := context) valueCompiled valueAdapted resultFound step continued

/-- Object-projection instance of the reusable direct-`let` boundary. -/
theorem letStepSimulates_objectProjection
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv RuntimeHost}
    {spec : Wasm.HostSpec RuntimeHost} {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure} {sourceEnv : Env}
    {index : Nat} {objectId : Lean.FVarId}
    {initial : Wasm.Store RuntimeHost} {locals updated : Wasm.Locals}
    {objectIndex resultIndex : Nat} {objectHandle : Handle}
    {sourceObject sourceValue : Value} {resultKind : AbiKind}
    {after : HandleTable} {resultHandle : Handle}
    (valueEq : decl.value = .oproj index objectId)
    (objectLookup : lookupValue sourceEnv objectId = .ok sourceObject)
    (projected :
      getObjectField initial.host.runtime sourceObject index = .ok sourceValue)
    (initialRelated :
      StateRelated sourceFunction initial.host.runtime sourceEnv initial locals)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (kindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some resultKind)
    (hObject : locals.get objectIndex = some (.i32 objectHandle))
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract :
      spec.contracts[id]? = some (hostContract (.objectProj index resultKind)))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (decoded :
      decodeArgs initial.host.handles #[.tobject] [.i32 objectHandle] =
        .ok #[sourceObject])
    (usesHandle : resultKind.usesHandle = true)
    (encoded :
      initial.host.handles.encode resultKind sourceValue = .ok (after, resultHandle))
    (targetSet : locals.set? resultIndex (.i32 resultHandle) = some updated) :
    LetStepSimulates context sourceFunction module hostEnv decl
      [.localGet objectIndex, .call id]
      initial.host.runtime initial.host.runtime sourceEnv sourceValue initial
      (successfulHostStore initial initial.host.runtime after)
      locals updated resultIndex := by
  refine ⟨?_, initialRelated, ?_, ?_⟩
  · unfold SourceLetResult
    simp [evalLetValue, valueEq]
    rw [objectLookup]
    change ((fun value : Value =>
      (initial.host.runtime, LetAction.value value)) <$>
        getObjectField initial.host.runtime sourceObject index) =
      .ok (initial.host.runtime, .value sourceValue)
    rw [projected]
    rfl
  · refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · exact handleTableInvariant_of_encode initialRelated.2.2.2.1 usesHandle encoded
    · exact EnvLocalsRelated.bind_handle_of_encode
        initialRelated.2.2.2.2 initialRelated.2.2.2.1 resultFound kindAt
        usesHandle encoded targetSet
  · intro rest Q tail continued
    simpa [successfulHostStore] using
      wp_objectProjection_let index resultKind objectHandle sourceObject sourceValue
        after resultHandle tail hObject hImp hSat hi hContract hParams hResults
        decoded projected usesHandle encoded targetSet continued

/-- Recursive semantic rule for an object-projection `let`. -/
theorem codeWP_objectProjection_let
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv RuntimeHost} {spec : Wasm.HostSpec RuntimeHost}
    {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure} {sourceEnv : Env}
    {index : Nat} {objectId : Lean.FVarId}
    {initial : Wasm.Store RuntimeHost} {locals updated : Wasm.Locals}
    {objectIndex resultIndex : Nat} {objectHandle : Handle}
    {sourceObject sourceValue : Value} {resultKind : AbiKind}
    {after : HandleTable} {resultHandle : Handle}
    {targetRest : Wasm.Program} {tail : List Wasm.Value}
    {Q : Wasm.Assertion RuntimeHost}
    (valueEq : decl.value = .oproj index objectId)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.localGet objectId, .call (.runtime (.objectProj index resultKind))])
    (objectFound :
      findFVar? (functionBindings sourceFunction) objectId = some objectIndex)
    (callFound :
      callIndex? sourceModule (.runtime (.objectProj index resultKind)) = some id)
    (objectLookup : lookupValue sourceEnv objectId = .ok sourceObject)
    (projected :
      getObjectField initial.host.runtime sourceObject index = .ok sourceValue)
    (initialRelated :
      StateRelated sourceFunction initial.host.runtime sourceEnv initial locals)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (kindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some resultKind)
    (hObject : locals.get objectIndex = some (.i32 objectHandle))
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract :
      spec.contracts[id]? = some (hostContract (.objectProj index resultKind)))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (decoded :
      decodeArgs initial.host.handles #[.tobject] [.i32 objectHandle] =
        .ok #[sourceObject])
    (usesHandle : resultKind.usesHandle = true)
    (encoded :
      initial.host.handles.encode resultKind sourceValue = .ok (after, resultHandle))
    (targetSet : locals.set? resultIndex (.i32 resultHandle) = some updated)
    (continued :
      CodeWP context sourceModule sourceFunction labels module hostEnv
        initial.host.runtime (bind sourceEnv decl.fvarId sourceValue)
        continuation targetRest
        (successfulHostStore initial initial.host.runtime after) updated tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      initial.host.runtime sourceEnv (.let decl continuation)
      (.localGet objectIndex :: .call id :: .localSet resultIndex :: targetRest)
      initial locals tail Q := by
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          [.localGet objectId, .call (.runtime (.objectProj index resultKind))] =
        .ok [.localGet objectIndex, .call id] := by
    have objectFound' :
        findFVar? (sourceFunction.params.toList ++ sourceFunction.locals.toList)
          objectId = some objectIndex := by
      simpa [functionBindings] using objectFound
    simp [instructions, instruction, objectFound', callFound]
    rfl
  have step := letStepSimulates_objectProjection (context := context)
    valueEq objectLookup projected initialRelated resultFound kindAt hObject hImp hSat
    hi hContract hParams hResults decoded usesHandle encoded targetSet
  simpa using
    codeWP_let (context := context) valueCompiled valueAdapted resultFound step continued

/-- USize-projection instance of the reusable direct-`let` boundary. -/
theorem letStepSimulates_usizeProjection
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv RuntimeHost}
    {spec : Wasm.HostSpec RuntimeHost} {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure} {sourceEnv : Env}
    {index : Nat} {objectId : Lean.FVarId}
    {initial : Wasm.Store RuntimeHost} {locals updated : Wasm.Locals}
    {objectIndex resultIndex : Nat} {objectHandle : Handle}
    {sourceObject : Value} {value : UInt64}
    (valueEq : decl.value = .uproj index objectId)
    (objectLookup : lookupValue sourceEnv objectId = .ok sourceObject)
    (projected : getUSizeField initial.host.runtime sourceObject index =
      .ok (.usize value))
    (initialRelated :
      StateRelated sourceFunction initial.host.runtime sourceEnv initial locals)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (kindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some .usize)
    (hObject : locals.get objectIndex = some (.i32 objectHandle))
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (hostContract (.usizeProj index)))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (decoded : decodeArgs initial.host.handles #[.tobject] [.i32 objectHandle] =
      .ok #[sourceObject])
    (targetSet : locals.set? resultIndex (.i64 value) = some updated) :
    LetStepSimulates context sourceFunction module hostEnv decl
      [.localGet objectIndex, .call id]
      initial.host.runtime initial.host.runtime sourceEnv (.usize value) initial
      (successfulHostStore initial initial.host.runtime initial.host.handles)
      locals updated resultIndex := by
  refine ⟨?_, initialRelated, ?_, ?_⟩
  · unfold SourceLetResult
    simp [evalLetValue, valueEq]
    rw [objectLookup]
    change ((fun result : Value =>
      (initial.host.runtime, LetAction.value result)) <$>
        getUSizeField initial.host.runtime sourceObject index) =
      .ok (initial.host.runtime, .value (.usize value))
    rw [projected]
    rfl
  · refine ⟨rfl, rfl, rfl, initialRelated.2.2.2.1, ?_⟩
    exact EnvLocalsRelated.bind_direct initialRelated.2.2.2.2
      resultFound kindAt (decodeValue_usize initial.host.handles value) targetSet
  · intro rest Q tail continued
    simpa [successfulHostStore] using
      wp_usizeProjection_let index objectHandle sourceObject value tail hObject
        hImp hSat hi hContract hParams hResults decoded projected targetSet continued

/-- Integer-scalar-projection instance. The encode/decode premises are the
dynamic scalar-field typing invariant exposed by the source runtime. -/
theorem letStepSimulates_scalarProjection
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv RuntimeHost}
    {spec : Wasm.HostSpec RuntimeHost} {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure} {sourceEnv : Env}
    {width offset : Nat} {objectId : Lean.FVarId}
    {initial : Wasm.Store RuntimeHost} {locals updated : Wasm.Locals}
    {objectIndex resultIndex : Nat} {objectHandle : Handle}
    {sourceObject sourceValue : Value} {resultKind : AbiKind}
    {physical : Wasm.Value}
    (valueEq : decl.value = .sproj width offset objectId)
    (objectLookup : lookupValue sourceEnv objectId = .ok sourceObject)
    (projected : getScalarField initial.host.runtime sourceObject width offset =
      .ok sourceValue)
    (initialRelated :
      StateRelated sourceFunction initial.host.runtime sourceEnv initial locals)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (kindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some resultKind)
    (hObject : locals.get objectIndex = some (.i32 objectHandle))
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (hostContract (.scalarProj width offset resultKind)))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (decodedObject :
      decodeArgs initial.host.handles #[.tobject] [.i32 objectHandle] =
        .ok #[sourceObject])
    (encodedResult : encodeValue initial.host.handles resultKind sourceValue =
      .ok (initial.host.handles, physical))
    (decodedResult : DecodesValue initial.host.handles resultKind physical sourceValue)
    (targetSet : locals.set? resultIndex physical = some updated) :
    LetStepSimulates context sourceFunction module hostEnv decl
      [.localGet objectIndex, .call id]
      initial.host.runtime initial.host.runtime sourceEnv sourceValue initial
      (successfulHostStore initial initial.host.runtime initial.host.handles)
      locals updated resultIndex := by
  refine ⟨?_, initialRelated, ?_, ?_⟩
  · unfold SourceLetResult
    simp [evalLetValue, valueEq]
    rw [objectLookup]
    change ((fun result : Value =>
      (initial.host.runtime, LetAction.value result)) <$>
        getScalarField initial.host.runtime sourceObject width offset) =
      .ok (initial.host.runtime, .value sourceValue)
    rw [projected]
    rfl
  · refine ⟨rfl, rfl, rfl, initialRelated.2.2.2.1, ?_⟩
    exact EnvLocalsRelated.bind_direct initialRelated.2.2.2.2
      resultFound kindAt decodedResult targetSet
  · intro rest Q tail continued
    simpa [successfulHostStore] using
      wp_scalarProjection_let width offset resultKind objectHandle sourceObject
        sourceValue physical tail hObject hImp hSat hi hContract hParams hResults
        decodedObject projected encodedResult targetSet continued

/-- Recursive semantic rule for a USize-projection `let`. -/
theorem codeWP_usizeProjection_let
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv RuntimeHost} {spec : Wasm.HostSpec RuntimeHost}
    {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure} {sourceEnv : Env}
    {index : Nat} {objectId : Lean.FVarId}
    {initial : Wasm.Store RuntimeHost} {locals updated : Wasm.Locals}
    {objectIndex resultIndex : Nat} {objectHandle : Handle}
    {sourceObject : Value} {value : UInt64}
    {targetRest : Wasm.Program} {tail : List Wasm.Value}
    {Q : Wasm.Assertion RuntimeHost}
    (valueEq : decl.value = .uproj index objectId)
    (valueCompiled : Fir.Wasm.compileLetValue context decl =
      .ok [.localGet objectId, .call (.runtime (.usizeProj index))])
    (objectFound :
      findFVar? (functionBindings sourceFunction) objectId = some objectIndex)
    (callFound : callIndex? sourceModule (.runtime (.usizeProj index)) = some id)
    (objectLookup : lookupValue sourceEnv objectId = .ok sourceObject)
    (projected : getUSizeField initial.host.runtime sourceObject index =
      .ok (.usize value))
    (initialRelated :
      StateRelated sourceFunction initial.host.runtime sourceEnv initial locals)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (kindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some .usize)
    (hObject : locals.get objectIndex = some (.i32 objectHandle))
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (hostContract (.usizeProj index)))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (decoded : decodeArgs initial.host.handles #[.tobject] [.i32 objectHandle] =
      .ok #[sourceObject])
    (targetSet : locals.set? resultIndex (.i64 value) = some updated)
    (continued :
      CodeWP context sourceModule sourceFunction labels module hostEnv
        initial.host.runtime (bind sourceEnv decl.fvarId (.usize value))
        continuation targetRest
        (successfulHostStore initial initial.host.runtime initial.host.handles)
        updated tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      initial.host.runtime sourceEnv (.let decl continuation)
      (.localGet objectIndex :: .call id :: .localSet resultIndex :: targetRest)
      initial locals tail Q := by
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          [.localGet objectId, .call (.runtime (.usizeProj index))] =
        .ok [.localGet objectIndex, .call id] := by
    have objectFound' :
        findFVar? (sourceFunction.params.toList ++ sourceFunction.locals.toList)
          objectId = some objectIndex := by
      simpa [functionBindings] using objectFound
    simp [instructions, instruction, objectFound', callFound]
    rfl
  have step := letStepSimulates_usizeProjection (context := context)
    valueEq objectLookup projected initialRelated resultFound kindAt hObject hImp
    hSat hi hContract hParams hResults decoded targetSet
  simpa using
    codeWP_let (context := context) valueCompiled valueAdapted resultFound step continued

/-- Recursive semantic rule for an integer scalar-projection `let`. -/
theorem codeWP_scalarProjection_let
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv RuntimeHost} {spec : Wasm.HostSpec RuntimeHost}
    {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure} {sourceEnv : Env}
    {width offset : Nat} {objectId : Lean.FVarId}
    {initial : Wasm.Store RuntimeHost} {locals updated : Wasm.Locals}
    {objectIndex resultIndex : Nat} {objectHandle : Handle}
    {sourceObject sourceValue : Value} {resultKind : AbiKind}
    {physical : Wasm.Value} {targetRest : Wasm.Program}
    {tail : List Wasm.Value} {Q : Wasm.Assertion RuntimeHost}
    (valueEq : decl.value = .sproj width offset objectId)
    (valueCompiled : Fir.Wasm.compileLetValue context decl =
      .ok [.localGet objectId,
        .call (.runtime (.scalarProj width offset resultKind))])
    (objectFound :
      findFVar? (functionBindings sourceFunction) objectId = some objectIndex)
    (callFound : callIndex? sourceModule
      (.runtime (.scalarProj width offset resultKind)) = some id)
    (objectLookup : lookupValue sourceEnv objectId = .ok sourceObject)
    (projected : getScalarField initial.host.runtime sourceObject width offset =
      .ok sourceValue)
    (initialRelated :
      StateRelated sourceFunction initial.host.runtime sourceEnv initial locals)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (kindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some resultKind)
    (hObject : locals.get objectIndex = some (.i32 objectHandle))
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (hostContract (.scalarProj width offset resultKind)))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (decodedObject :
      decodeArgs initial.host.handles #[.tobject] [.i32 objectHandle] =
        .ok #[sourceObject])
    (encodedResult : encodeValue initial.host.handles resultKind sourceValue =
      .ok (initial.host.handles, physical))
    (decodedResult : DecodesValue initial.host.handles resultKind physical sourceValue)
    (targetSet : locals.set? resultIndex physical = some updated)
    (continued :
      CodeWP context sourceModule sourceFunction labels module hostEnv
        initial.host.runtime (bind sourceEnv decl.fvarId sourceValue)
        continuation targetRest
        (successfulHostStore initial initial.host.runtime initial.host.handles)
        updated tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      initial.host.runtime sourceEnv (.let decl continuation)
      (.localGet objectIndex :: .call id :: .localSet resultIndex :: targetRest)
      initial locals tail Q := by
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          [.localGet objectId,
            .call (.runtime (.scalarProj width offset resultKind))] =
        .ok [.localGet objectIndex, .call id] := by
    have objectFound' :
        findFVar? (sourceFunction.params.toList ++ sourceFunction.locals.toList)
          objectId = some objectIndex := by
      simpa [functionBindings] using objectFound
    simp [instructions, instruction, objectFound', callFound]
    rfl
  have step := letStepSimulates_scalarProjection (context := context)
    valueEq objectLookup projected initialRelated resultFound kindAt hObject hImp
    hSat hi hContract hParams hResults decodedObject encodedResult decodedResult targetSet
  simpa using
    codeWP_let (context := context) valueCompiled valueAdapted resultFound step continued

/-- Boxing instance of the reusable direct-`let` boundary. -/
theorem letStepSimulates_box
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv RuntimeHost}
    {spec : Wasm.HostSpec RuntimeHost} {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure} {sourceEnv : Env}
    {type : Lean.Expr} {scalarId : Lean.FVarId}
    {scalarKind resultKind : AbiKind}
    {initial : Wasm.Store RuntimeHost} {locals updated : Wasm.Locals}
    {scalarIndex resultIndex : Nat} {physicalScalar : Wasm.Value}
    {sourceScalar sourceValue : Value} {sourceRuntime : RuntimeState}
    {after : HandleTable} {resultHandle : Handle}
    (valueEq : decl.value = .box type scalarId)
    (scalarLookup : lookupValue sourceEnv scalarId = .ok sourceScalar)
    (boxed : Fir.LeanIR.Impure.box initial.host.runtime type sourceScalar =
      .ok (sourceRuntime, sourceValue))
    (initialRelated :
      StateRelated sourceFunction initial.host.runtime sourceEnv initial locals)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (kindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some resultKind)
    (hScalar : locals.get scalarIndex = some physicalScalar)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (hostContract (.box scalarKind resultKind)))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (typeEq : runtimeScalarType? scalarKind = some type)
    (decoded : decodeArgs initial.host.handles #[scalarKind] [physicalScalar] =
      .ok #[sourceScalar])
    (usesHandle : resultKind.usesHandle = true)
    (encoded : initial.host.handles.encode resultKind sourceValue =
      .ok (after, resultHandle))
    (targetSet : locals.set? resultIndex (.i32 resultHandle) = some updated) :
    LetStepSimulates context sourceFunction module hostEnv decl
      [.localGet scalarIndex, .call id]
      initial.host.runtime sourceRuntime sourceEnv sourceValue initial
      (successfulHostStore initial sourceRuntime after)
      locals updated resultIndex := by
  refine ⟨?_, initialRelated, ?_, ?_⟩
  · unfold SourceLetResult
    simp [evalLetValue, valueEq]
    rw [scalarLookup]
    change ((fun result : RuntimeState × Value =>
      (result.1, LetAction.value result.2)) <$>
        Fir.LeanIR.Impure.box initial.host.runtime type sourceScalar) =
      .ok (sourceRuntime, .value sourceValue)
    rw [boxed]
    rfl
  · refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · exact handleTableInvariant_of_encode initialRelated.2.2.2.1 usesHandle encoded
    · exact EnvLocalsRelated.bind_handle_of_encode
        initialRelated.2.2.2.2 initialRelated.2.2.2.1 resultFound kindAt
        usesHandle encoded targetSet
  · intro rest Q tail continued
    simpa [successfulHostStore] using
      wp_box_let scalarKind resultKind type physicalScalar sourceScalar
        sourceRuntime sourceValue after resultHandle tail hScalar hImp hSat hi
        hContract hParams hResults typeEq decoded boxed usesHandle encoded
        targetSet continued

/-- Unboxing instance of the reusable direct-`let` boundary. -/
theorem letStepSimulates_unbox
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv RuntimeHost}
    {spec : Wasm.HostSpec RuntimeHost} {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure} {sourceEnv : Env}
    {objectId : Lean.FVarId} {scalarKind : AbiKind} {type : Lean.Expr}
    {initial : Wasm.Store RuntimeHost} {locals updated : Wasm.Locals}
    {objectIndex resultIndex : Nat} {objectHandle : Handle}
    {sourceObject sourceValue : Value} {physical : Wasm.Value}
    (valueEq : decl.value = .unbox objectId)
    (resultTypeEq : decl.type = type)
    (objectLookup : lookupValue sourceEnv objectId = .ok sourceObject)
    (unboxed : Fir.LeanIR.Impure.unbox initial.host.runtime type sourceObject =
      .ok sourceValue)
    (initialRelated :
      StateRelated sourceFunction initial.host.runtime sourceEnv initial locals)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (kindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some scalarKind)
    (hObject : locals.get objectIndex = some (.i32 objectHandle))
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (hostContract (.unbox scalarKind)))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (typeEq : runtimeScalarType? scalarKind = some type)
    (decodedObject :
      decodeArgs initial.host.handles #[.tobject] [.i32 objectHandle] =
        .ok #[sourceObject])
    (encodedResult : encodeValue initial.host.handles scalarKind sourceValue =
      .ok (initial.host.handles, physical))
    (decodedResult : DecodesValue initial.host.handles scalarKind physical sourceValue)
    (targetSet : locals.set? resultIndex physical = some updated) :
    LetStepSimulates context sourceFunction module hostEnv decl
      [.localGet objectIndex, .call id]
      initial.host.runtime initial.host.runtime sourceEnv sourceValue initial
      (successfulHostStore initial initial.host.runtime initial.host.handles)
      locals updated resultIndex := by
  refine ⟨?_, initialRelated, ?_, ?_⟩
  · unfold SourceLetResult
    simp [evalLetValue, valueEq]
    rw [objectLookup, resultTypeEq]
    change ((fun result : Value =>
      (initial.host.runtime, LetAction.value result)) <$>
        Fir.LeanIR.Impure.unbox initial.host.runtime type sourceObject) =
      .ok (initial.host.runtime, .value sourceValue)
    rw [unboxed]
    rfl
  · refine ⟨rfl, rfl, rfl, initialRelated.2.2.2.1, ?_⟩
    exact EnvLocalsRelated.bind_direct initialRelated.2.2.2.2
      resultFound kindAt decodedResult targetSet
  · intro rest Q tail continued
    simpa [successfulHostStore] using
      wp_unbox_let scalarKind type objectHandle sourceObject sourceValue physical
        tail hObject hImp hSat hi hContract hParams hResults typeEq decodedObject
        unboxed encodedResult targetSet continued

/-- `isShared` instance with Lean 4.32's direct UInt8 result. -/
theorem letStepSimulates_isShared
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv RuntimeHost}
    {spec : Wasm.HostSpec RuntimeHost} {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure} {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {initial : Wasm.Store RuntimeHost} {locals updated : Wasm.Locals}
    {objectIndex resultIndex : Nat} {objectHandle : Handle}
    {sourceObject : Value} {shared : UInt8}
    (valueEq : decl.value = .isShared objectId)
    (objectLookup : lookupValue sourceEnv objectId = .ok sourceObject)
    (evaluated : Fir.LeanIR.Impure.isShared initial.host.runtime sourceObject =
      .ok (.scalar (.uint8 shared)))
    (initialRelated :
      StateRelated sourceFunction initial.host.runtime sourceEnv initial locals)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (kindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some .uint8)
    (hObject : locals.get objectIndex = some (.i32 objectHandle))
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (hostContract .isShared))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (decodedObject :
      decodeArgs initial.host.handles #[.tobject] [.i32 objectHandle] =
        .ok #[sourceObject])
    (targetSet : locals.set? resultIndex (.i32 (UInt32.ofNat shared.toNat)) =
      some updated) :
    LetStepSimulates context sourceFunction module hostEnv decl
      [.localGet objectIndex, .call id]
      initial.host.runtime initial.host.runtime sourceEnv (.scalar (.uint8 shared)) initial
      (successfulHostStore initial initial.host.runtime initial.host.handles)
      locals updated resultIndex := by
  refine ⟨?_, initialRelated, ?_, ?_⟩
  · unfold SourceLetResult
    simp [evalLetValue, valueEq]
    rw [objectLookup]
    change ((fun result : Value =>
      (initial.host.runtime, LetAction.value result)) <$>
        Fir.LeanIR.Impure.isShared initial.host.runtime sourceObject) =
      .ok (initial.host.runtime, .value (.scalar (.uint8 shared)))
    rw [evaluated]
    rfl
  · refine ⟨rfl, rfl, rfl, initialRelated.2.2.2.1, ?_⟩
    exact EnvLocalsRelated.bind_direct initialRelated.2.2.2.2
      resultFound kindAt (decodeValue_uint8 initial.host.handles shared) targetSet
  · intro rest Q tail continued
    simpa [successfulHostStore] using
      wp_isShared_let objectHandle sourceObject shared tail hObject hImp hSat hi
        hContract hParams hResults decodedObject evaluated targetSet continued

/-- Reset instance of the reusable direct-`let` boundary. -/
theorem letStepSimulates_reset
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv RuntimeHost}
    {spec : Wasm.HostSpec RuntimeHost} {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure} {sourceEnv : Env}
    {objectId : Lean.FVarId} {objectFields : Nat}
    {initial : Wasm.Store RuntimeHost} {locals updated : Wasm.Locals}
    {objectIndex resultIndex : Nat} {objectHandle tokenHandle : Handle}
    {sourceObject sourceToken : Value} {sourceRuntime : RuntimeState}
    {after : HandleTable}
    (valueEq : decl.value = .reset objectFields objectId)
    (objectLookup : lookupValue sourceEnv objectId = .ok sourceObject)
    (resetResult : Fir.LeanIR.Impure.reset initial.host.runtime objectFields
      sourceObject = .ok (sourceRuntime, sourceToken))
    (initialRelated :
      StateRelated sourceFunction initial.host.runtime sourceEnv initial locals)
    (resultFound : findFVar? (functionBindings sourceFunction) decl.fvarId =
      some resultIndex)
    (kindAt : (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
      some .reuseToken)
    (hObject : locals.get objectIndex = some (.i32 objectHandle))
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (hostContract (.reset objectFields)))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (decoded : decodeArgs initial.host.handles #[.tobject] [.i32 objectHandle] =
      .ok #[sourceObject])
    (encoded : initial.host.handles.encode .reuseToken sourceToken =
      .ok (after, tokenHandle))
    (targetSet : locals.set? resultIndex (.i32 tokenHandle) = some updated) :
    LetStepSimulates context sourceFunction module hostEnv decl
      [.localGet objectIndex, .call id]
      initial.host.runtime sourceRuntime sourceEnv sourceToken initial
      (successfulHostStore initial sourceRuntime after) locals updated resultIndex := by
  refine ⟨?_, initialRelated, ?_, ?_⟩
  · unfold SourceLetResult
    simp [evalLetValue, valueEq]
    rw [objectLookup]
    change ((fun result : RuntimeState × Value =>
      (result.1, LetAction.value result.2)) <$>
        Fir.LeanIR.Impure.reset initial.host.runtime objectFields sourceObject) =
      .ok (sourceRuntime, .value sourceToken)
    rw [resetResult]
    rfl
  · refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · exact handleTableInvariant_of_encode initialRelated.2.2.2.1 (by rfl) encoded
    · exact EnvLocalsRelated.bind_handle_of_encode
        initialRelated.2.2.2.2 initialRelated.2.2.2.1 resultFound kindAt
        (by rfl) encoded targetSet
  · intro rest Q tail continued
    simpa [successfulHostStore] using
      wp_reset_let objectFields objectHandle sourceObject sourceRuntime
        sourceToken after tokenHandle tail hObject hImp hSat hi hContract hParams
        hResults decoded resetResult encoded targetSet continued

/-- Reuse instance of the reusable direct-`let` boundary. -/
theorem letStepSimulates_reuse
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv RuntimeHost}
    {spec : Wasm.HostSpec RuntimeHost} {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure} {sourceEnv : Env}
    {tokenId : Lean.FVarId} {info : Lean.Compiler.LCNF.CtorInfo}
    {updateHeader : Bool} {args : Array (Lean.Compiler.LCNF.Arg .impure)}
    {fieldKinds : Array AbiKind} {resultKind : AbiKind}
    {initial : Wasm.Store RuntimeHost} {locals updated : Wasm.Locals}
    {indices : List Nat} {physicalArgs : List Wasm.Value}
    {resultIndex : Nat} {sourceToken sourceValue : Value}
    {sourceFields semanticArgs : Array Value} {sourceRuntime : RuntimeState}
    {after : HandleTable} {resultHandle : Handle}
    (valueEq : decl.value = .reuse tokenId info updateHeader args)
    (tokenLookup : lookupValue sourceEnv tokenId = .ok sourceToken)
    (argumentsEvaluated : evalArgs sourceEnv args = .ok sourceFields)
    (reused : Fir.LeanIR.Impure.reuse initial.host.runtime sourceToken info
      updateHeader sourceFields = .ok (sourceRuntime, sourceValue))
    (initialRelated :
      StateRelated sourceFunction initial.host.runtime sourceEnv initial locals)
    (resultFound : findFVar? (functionBindings sourceFunction) decl.fvarId =
      some resultIndex)
    (kindAt : (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
      some resultKind)
    (hGets : List.Forall₂ (fun index value => locals.get index = some value)
      indices physicalArgs)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some
      (hostContract (.reuse info updateHeader fieldKinds resultKind)))
    (hParams : imp.params.length = physicalArgs.length)
    (hResults : imp.results.length = 1)
    (decoded : decodeArgs initial.host.handles (#[.reuseToken] ++ fieldKinds)
      physicalArgs = .ok semanticArgs)
    (tokenHead : semanticArgs[0]? = some sourceToken)
    (fieldsTail : semanticArgs.extract 1 semanticArgs.size = sourceFields)
    (usesHandle : resultKind.usesHandle = true)
    (encoded : initial.host.handles.encode resultKind sourceValue =
      .ok (after, resultHandle))
    (targetSet : locals.set? resultIndex (.i32 resultHandle) = some updated) :
    LetStepSimulates context sourceFunction module hostEnv decl
      (indices.map Wasm.Instruction.localGet ++ [.call id])
      initial.host.runtime sourceRuntime sourceEnv sourceValue initial
      (successfulHostStore initial sourceRuntime after) locals updated resultIndex := by
  have hostReused : Fir.LeanIR.Impure.reuse initial.host.runtime sourceToken info
      updateHeader (semanticArgs.extract 1 semanticArgs.size) =
        .ok (sourceRuntime, sourceValue) := by
    rw [fieldsTail]
    exact reused
  refine ⟨?_, initialRelated, ?_, ?_⟩
  · unfold SourceLetResult
    simp [evalLetValue, valueEq]
    rw [tokenLookup, argumentsEvaluated]
    change ((fun result : RuntimeState × Value =>
      (result.1, LetAction.value result.2)) <$>
        Fir.LeanIR.Impure.reuse initial.host.runtime sourceToken info
          updateHeader sourceFields) = .ok (sourceRuntime, .value sourceValue)
    rw [reused]
    rfl
  · refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · exact handleTableInvariant_of_encode initialRelated.2.2.2.1 usesHandle encoded
    · exact EnvLocalsRelated.bind_handle_of_encode
        initialRelated.2.2.2.2 initialRelated.2.2.2.1 resultFound kindAt
        usesHandle encoded targetSet
  · intro rest Q tail continued
    simpa [successfulHostStore, List.append_assoc] using
      wp_reuse_let info updateHeader fieldKinds resultKind semanticArgs sourceToken
        sourceRuntime sourceValue after resultHandle tail hGets hImp hSat hi
        hContract hParams hResults decoded tokenHead hostReused usesHandle encoded
        targetSet continued

/-- Generic unary semantic-host instance of the no-result effect boundary. -/
theorem effectStepSimulates_unaryHost
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv RuntimeHost} {spec : Wasm.HostSpec RuntimeHost}
    {id : Nat} {imp : Wasm.ImportDecl} {sourceEnv : Env}
    {code continuation : Lean.Compiler.LCNF.Code .impure}
    {initial : Wasm.Store RuntimeHost} {locals : Wasm.Locals}
    {objectIndex : Nat} {physicalObject : Wasm.Value}
    {operation : HostOperation} {sourceRuntime : RuntimeState}
    {targetRest : Wasm.Program}
    (sourceStep : SourceEffectResult context initial.host.runtime sourceRuntime
      sourceEnv code continuation)
    (adapted : CodeAdapted context sourceModule sourceFunction labels code
      ([.localGet objectIndex, .call id] ++ targetRest))
    (initialRelated :
      StateRelated sourceFunction initial.host.runtime sourceEnv initial locals)
    (hObject : locals.get objectIndex = some physicalObject)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (hostContract operation))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 0)
    (step : hostStep operation initial [physicalObject] =
      .Return [] (successfulHostStore initial sourceRuntime initial.host.handles)) :
    EffectStepSimulates context sourceModule sourceFunction labels module hostEnv
      initial.host.runtime sourceRuntime sourceEnv code continuation
      ([.localGet objectIndex, .call id] ++ targetRest) targetRest initial
      (successfulHostStore initial sourceRuntime initial.host.handles) locals := by
  refine ⟨sourceStep, adapted, initialRelated, ?_, ?_⟩
  · exact ⟨rfl, rfl, rfl, initialRelated.2.2.2.1,
      initialRelated.2.2.2.2⟩
  · intro Q tail continued
    simpa using
      wp_effect_localGets
        (indices := [objectIndex]) (physicalArgs := [physicalObject])
        (operation := operation) (tail := tail) (.cons hObject .nil)
        hImp hSat hi hContract hParams hResults step continued

/-- A compiler-elided source effect advances only the source control state. -/
theorem effectStepSimulates_elided
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv RuntimeHost} {sourceEnv : Env}
    {code continuation : Lean.Compiler.LCNF.Code .impure}
    {initial : Wasm.Store RuntimeHost} {locals : Wasm.Locals}
    {targetRest : Wasm.Program}
    (sourceStep : SourceEffectResult context initial.host.runtime
      initial.host.runtime sourceEnv code continuation)
    (adapted :
      CodeAdapted context sourceModule sourceFunction labels code targetRest)
    (initialRelated :
      StateRelated sourceFunction initial.host.runtime sourceEnv initial locals) :
    EffectStepSimulates context sourceModule sourceFunction labels module hostEnv
      initial.host.runtime initial.host.runtime sourceEnv code continuation
      targetRest targetRest initial initial locals := by
  exact ⟨sourceStep, adapted, initialRelated, initialRelated,
    fun _ _ continued => continued⟩

/-- USize-field mutation instance of the reusable no-result effect boundary. -/
theorem effectStepSimulates_usizeSet
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv RuntimeHost} {spec : Wasm.HostSpec RuntimeHost}
    {id : Nat} {imp : Wasm.ImportDecl} {sourceEnv : Env}
    {objectId fieldId : Lean.FVarId} {index : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {initial : Wasm.Store RuntimeHost} {locals : Wasm.Locals}
    {objectIndex fieldIndex : Nat} {objectHandle : Handle} {fieldValue : UInt64}
    {sourceObject : Value} {sourceRuntime : RuntimeState}
    {targetRest : Wasm.Program}
    (objectLookup : lookupValue sourceEnv objectId = .ok sourceObject)
    (fieldLookup : lookupValue sourceEnv fieldId = .ok (.usize fieldValue))
    (mutated : setUSizeField initial.host.runtime sourceObject index
      (.usize fieldValue) = .ok sourceRuntime)
    (initialRelated :
      StateRelated sourceFunction initial.host.runtime sourceEnv initial locals)
    (objectCompiled : Fir.Wasm.getLocal context objectId =
      .ok (.localGet objectId, .object))
    (fieldCompiled : Fir.Wasm.getLocal context fieldId =
      .ok (.localGet fieldId, .usize))
    (objectFound : findFVar? (functionBindings sourceFunction) objectId =
      some objectIndex)
    (fieldFound : findFVar? (functionBindings sourceFunction) fieldId =
      some fieldIndex)
    (callFound : callIndex? sourceModule (.runtime (.usizeSet index)) = some id)
    (continuationAdapted :
      CodeAdapted context sourceModule sourceFunction labels continuation targetRest)
    (hObject : locals.get objectIndex = some (.i32 objectHandle))
    (hField : locals.get fieldIndex = some (.i64 fieldValue))
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (hostContract (.usizeSet index)))
    (hParams : imp.params.length = 2)
    (hResults : imp.results.length = 0)
    (decoded : decodeArgs initial.host.handles #[.object, .usize]
      [.i32 objectHandle, .i64 fieldValue] =
        .ok #[sourceObject, .usize fieldValue]) :
    EffectStepSimulates context sourceModule sourceFunction labels module hostEnv
      initial.host.runtime sourceRuntime sourceEnv
      (.uset objectId index fieldId continuation) continuation
      ([.localGet objectIndex, .localGet fieldIndex, .call id] ++ targetRest)
      targetRest initial
      (successfulHostStore initial sourceRuntime initial.host.handles) locals := by
  refine ⟨?_, ?_, initialRelated, ?_, ?_⟩
  · intro externals
    simp [executeStep, coreStep, objectLookup, fieldLookup, mutated]
  · exact codeAdapted_uset objectCompiled fieldCompiled objectFound fieldFound
      callFound continuationAdapted
  · exact ⟨rfl, rfl, rfl, initialRelated.2.2.2.1,
      initialRelated.2.2.2.2⟩
  · intro Q tail continued
    simpa [successfulHostStore] using
      wp_effect_localGets
        (indices := [objectIndex, fieldIndex])
        (physicalArgs := [.i32 objectHandle, .i64 fieldValue])
        (operation := HostOperation.usizeSet index) (tail := tail)
        (.cons hObject (.cons hField .nil)) hImp hSat hi hContract hParams
        hResults
        (hostStep_usizeSet_of_decode initial index
          [.i32 objectHandle, .i64 fieldValue] sourceObject (.usize fieldValue)
          sourceRuntime decoded mutated)
        continued

/-- Integer-scalar field mutation instance of the reusable effect boundary. -/
theorem effectStepSimulates_scalarSet
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv RuntimeHost} {spec : Wasm.HostSpec RuntimeHost}
    {id : Nat} {imp : Wasm.ImportDecl} {sourceEnv : Env}
    {objectId fieldId : Lean.FVarId} {width offset : Nat} {type : Lean.Expr}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {initial : Wasm.Store RuntimeHost} {locals : Wasm.Locals}
    {objectIndex fieldIndex : Nat} {objectHandle : Handle}
    {fieldKind : AbiKind} {physicalField : Wasm.Value}
    {sourceObject sourceField : Value} {sourceRuntime : RuntimeState}
    {targetRest : Wasm.Program}
    (objectLookup : lookupValue sourceEnv objectId = .ok sourceObject)
    (fieldLookup : lookupValue sourceEnv fieldId = .ok sourceField)
    (mutated : setScalarField initial.host.runtime sourceObject width offset sourceField =
      .ok sourceRuntime)
    (initialRelated :
      StateRelated sourceFunction initial.host.runtime sourceEnv initial locals)
    (objectCompiled : Fir.Wasm.getLocal context objectId =
      .ok (.localGet objectId, .object))
    (fieldCompiled : Fir.Wasm.getLocal context fieldId =
      .ok (.localGet fieldId, fieldKind))
    (objectFound : findFVar? (functionBindings sourceFunction) objectId =
      some objectIndex)
    (fieldFound : findFVar? (functionBindings sourceFunction) fieldId =
      some fieldIndex)
    (callFound : callIndex? sourceModule
      (.runtime (.scalarSet width offset fieldKind)) = some id)
    (continuationAdapted :
      CodeAdapted context sourceModule sourceFunction labels continuation targetRest)
    (hObject : locals.get objectIndex = some (.i32 objectHandle))
    (hField : locals.get fieldIndex = some physicalField)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (hostContract (.scalarSet width offset fieldKind)))
    (hParams : imp.params.length = 2)
    (hResults : imp.results.length = 0)
    (decoded : decodeArgs initial.host.handles #[.object, fieldKind]
      [.i32 objectHandle, physicalField] = .ok #[sourceObject, sourceField]) :
    EffectStepSimulates context sourceModule sourceFunction labels module hostEnv
      initial.host.runtime sourceRuntime sourceEnv
      (.sset objectId width offset fieldId type continuation) continuation
      ([.localGet objectIndex, .localGet fieldIndex, .call id] ++ targetRest)
      targetRest initial
      (successfulHostStore initial sourceRuntime initial.host.handles) locals := by
  refine ⟨?_, ?_, initialRelated, ?_, ?_⟩
  · intro externals
    simp [executeStep, coreStep, objectLookup, fieldLookup, mutated]
  · exact codeAdapted_sset objectCompiled fieldCompiled objectFound fieldFound
      callFound continuationAdapted
  · exact ⟨rfl, rfl, rfl, initialRelated.2.2.2.1,
      initialRelated.2.2.2.2⟩
  · intro Q tail continued
    simpa [successfulHostStore] using
      wp_effect_localGets
        (indices := [objectIndex, fieldIndex])
        (physicalArgs := [.i32 objectHandle, physicalField])
        (operation := HostOperation.scalarSet width offset fieldKind) (tail := tail)
        (.cons hObject (.cons hField .nil)) hImp hSat hi hContract hParams
        hResults
        (hostStep_scalarSet_of_decode initial width offset fieldKind
          [.i32 objectHandle, physicalField] sourceObject sourceField sourceRuntime
          decoded mutated)
        continued

/-- Constructor-tag mutation instance of the reusable effect boundary. -/
theorem effectStepSimulates_setTag
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv RuntimeHost} {spec : Wasm.HostSpec RuntimeHost}
    {id : Nat} {imp : Wasm.ImportDecl} {sourceEnv : Env}
    {objectId : Lean.FVarId} {tag : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {initial : Wasm.Store RuntimeHost} {locals : Wasm.Locals}
    {objectIndex : Nat} {objectHandle : Handle} {sourceObject : Value}
    {sourceRuntime : RuntimeState} {targetRest : Wasm.Program}
    (objectLookup : lookupValue sourceEnv objectId = .ok sourceObject)
    (mutated : Fir.LeanIR.Impure.setTag initial.host.runtime sourceObject tag =
      .ok sourceRuntime)
    (initialRelated :
      StateRelated sourceFunction initial.host.runtime sourceEnv initial locals)
    (objectCompiled : Fir.Wasm.getLocal context objectId =
      .ok (.localGet objectId, .object))
    (objectFound : findFVar? (functionBindings sourceFunction) objectId =
      some objectIndex)
    (callFound : callIndex? sourceModule (.runtime (.setTag tag)) = some id)
    (continuationAdapted :
      CodeAdapted context sourceModule sourceFunction labels continuation targetRest)
    (hObject : locals.get objectIndex = some (.i32 objectHandle))
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (hostContract (.setTag tag)))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 0)
    (decoded : decodeArgs initial.host.handles #[.object] [.i32 objectHandle] =
      .ok #[sourceObject]) :
    EffectStepSimulates context sourceModule sourceFunction labels module hostEnv
      initial.host.runtime sourceRuntime sourceEnv
      (.setTag objectId tag continuation) continuation
      ([.localGet objectIndex, .call id] ++ targetRest) targetRest initial
      (successfulHostStore initial sourceRuntime initial.host.handles) locals := by
  refine ⟨?_, ?_, initialRelated, ?_, ?_⟩
  · intro externals
    simp [executeStep, coreStep, objectLookup, mutated]
  · exact codeAdapted_setTag objectCompiled objectFound callFound
      continuationAdapted
  · exact ⟨rfl, rfl, rfl, initialRelated.2.2.2.1,
      initialRelated.2.2.2.2⟩
  · intro Q tail continued
    simpa [successfulHostStore] using
      wp_effect_localGets
        (indices := [objectIndex]) (physicalArgs := [.i32 objectHandle])
        (operation := HostOperation.setTag tag) (tail := tail)
        (.cons hObject .nil) hImp hSat hi hContract hParams hResults
        (hostStep_setTag_of_decode initial tag [.i32 objectHandle] sourceObject
          sourceRuntime decoded mutated)
        continued

/-- FVar object-field mutation instance of the reusable effect boundary. -/
theorem effectStepSimulates_objectSet
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv RuntimeHost} {spec : Wasm.HostSpec RuntimeHost}
    {id : Nat} {imp : Wasm.ImportDecl} {sourceEnv : Env}
    {objectId fieldId : Lean.FVarId} {index : Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {initial : Wasm.Store RuntimeHost} {locals : Wasm.Locals}
    {objectIndex fieldIndex : Nat} {objectHandle : Handle}
    {fieldKind : AbiKind} {physicalField : Wasm.Value}
    {sourceObject sourceField : Value} {sourceRuntime : RuntimeState}
    {targetRest : Wasm.Program}
    (objectLookup : lookupValue sourceEnv objectId = .ok sourceObject)
    (fieldLookup : lookupValue sourceEnv fieldId = .ok sourceField)
    (mutated : setObjectField initial.host.runtime sourceObject index sourceField =
      .ok sourceRuntime)
    (initialRelated :
      StateRelated sourceFunction initial.host.runtime sourceEnv initial locals)
    (objectCompiled : Fir.Wasm.getLocal context objectId =
      .ok (.localGet objectId, .object))
    (fieldCompiled : Fir.Wasm.compileArg context (.fvar fieldId) =
      .ok ([.localGet fieldId], fieldKind))
    (objectFound : findFVar? (functionBindings sourceFunction) objectId =
      some objectIndex)
    (fieldFound : findFVar? (functionBindings sourceFunction) fieldId =
      some fieldIndex)
    (callFound : callIndex? sourceModule
      (.runtime (.objectSet index fieldKind)) = some id)
    (continuationAdapted :
      CodeAdapted context sourceModule sourceFunction labels continuation targetRest)
    (hObject : locals.get objectIndex = some (.i32 objectHandle))
    (hField : locals.get fieldIndex = some physicalField)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (hostContract (.objectSet index fieldKind)))
    (hParams : imp.params.length = 2)
    (hResults : imp.results.length = 0)
    (decoded : decodeArgs initial.host.handles #[.object, fieldKind]
      [.i32 objectHandle, physicalField] = .ok #[sourceObject, sourceField]) :
    EffectStepSimulates context sourceModule sourceFunction labels module hostEnv
      initial.host.runtime sourceRuntime sourceEnv
      (.oset objectId index (.fvar fieldId) continuation) continuation
      ([.localGet objectIndex, .localGet fieldIndex, .call id] ++ targetRest)
      targetRest initial
      (successfulHostStore initial sourceRuntime initial.host.handles) locals := by
  refine ⟨?_, ?_, initialRelated, ?_, ?_⟩
  · intro externals
    change evalArg sourceEnv (.fvar fieldId) = .ok sourceField at fieldLookup
    simp [executeStep, coreStep, objectLookup, fieldLookup, mutated]
  · apply codeAdapted_oset (targetField := [.localGet fieldIndex])
      objectCompiled fieldCompiled objectFound
    · apply instructions_localGets (fvarIds := [fieldId])
        (indices := [fieldIndex])
      exact .cons (by simpa [functionBindings] using fieldFound) .nil
    · exact callFound
    · exact continuationAdapted
  · exact ⟨rfl, rfl, rfl, initialRelated.2.2.2.1,
      initialRelated.2.2.2.2⟩
  · intro Q tail continued
    simpa [successfulHostStore] using
      wp_effect_localGets
        (indices := [objectIndex, fieldIndex])
        (physicalArgs := [.i32 objectHandle, physicalField])
        (operation := HostOperation.objectSet index fieldKind) (tail := tail)
        (.cons hObject (.cons hField .nil)) hImp hSat hi hContract hParams
        hResults
        (hostStep_objectSet_of_decode initial index fieldKind
          [.i32 objectHandle, physicalField] sourceObject sourceField sourceRuntime
          decoded mutated)
        continued

/-- Nonpersistent reference-count increment through the unary host boundary. -/
theorem effectStepSimulates_inc
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv RuntimeHost} {spec : Wasm.HostSpec RuntimeHost}
    {id : Nat} {imp : Wasm.ImportDecl} {sourceEnv : Env}
    {objectId : Lean.FVarId} {amount : Nat} {check : Bool}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {initial : Wasm.Store RuntimeHost} {locals : Wasm.Locals}
    {objectIndex : Nat} {objectHandle : Handle} {objectKind : AbiKind}
    {sourceObject : Value} {sourceRuntime : RuntimeState}
    {targetRest : Wasm.Program}
    (objectLookup : lookupValue sourceEnv objectId = .ok sourceObject)
    (updated : incValue initial.host.runtime sourceObject amount check =
      .ok sourceRuntime)
    (initialRelated :
      StateRelated sourceFunction initial.host.runtime sourceEnv initial locals)
    (objectCompiled : Fir.Wasm.getLocal context objectId =
      .ok (.localGet objectId, objectKind))
    (objectFound : findFVar? (functionBindings sourceFunction) objectId =
      some objectIndex)
    (callFound : callIndex? sourceModule (.runtime (.inc amount check)) = some id)
    (continuationAdapted :
      CodeAdapted context sourceModule sourceFunction labels continuation targetRest)
    (hObject : locals.get objectIndex = some (.i32 objectHandle))
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (hostContract (.inc amount check)))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 0)
    (decoded : decodeArgs initial.host.handles #[.tobject] [.i32 objectHandle] =
      .ok #[sourceObject]) :
    EffectStepSimulates context sourceModule sourceFunction labels module hostEnv
      initial.host.runtime sourceRuntime sourceEnv
      (.inc objectId amount check false continuation) continuation
      ([.localGet objectIndex, .call id] ++ targetRest) targetRest initial
      (successfulHostStore initial sourceRuntime initial.host.handles) locals := by
  apply effectStepSimulates_unaryHost
  · intro externals
    simp [executeStep, coreStep, objectLookup, updated]
  · exact codeAdapted_inc objectCompiled objectFound callFound continuationAdapted
  · exact initialRelated
  · exact hObject
  · exact hImp
  · exact hSat
  · exact hi
  · exact hContract
  · exact hParams
  · exact hResults
  · simpa [successfulHostStore] using
      hostStep_inc_of_decode initial amount check [.i32 objectHandle]
        sourceObject sourceRuntime decoded updated

/-- Nonpersistent reference-count decrement through the unary host boundary. -/
theorem effectStepSimulates_dec
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv RuntimeHost} {spec : Wasm.HostSpec RuntimeHost}
    {id : Nat} {imp : Wasm.ImportDecl} {sourceEnv : Env}
    {objectId : Lean.FVarId} {amount : Nat} {check : Bool}
    {objectFields? : Option Nat} {continuation : Lean.Compiler.LCNF.Code .impure}
    {initial : Wasm.Store RuntimeHost} {locals : Wasm.Locals}
    {objectIndex : Nat} {objectHandle : Handle} {objectKind : AbiKind}
    {sourceObject : Value} {sourceRuntime : RuntimeState}
    {targetRest : Wasm.Program}
    (objectLookup : lookupValue sourceEnv objectId = .ok sourceObject)
    (updated : decValue initial.host.runtime sourceObject amount check =
      .ok sourceRuntime)
    (initialRelated :
      StateRelated sourceFunction initial.host.runtime sourceEnv initial locals)
    (objectCompiled : Fir.Wasm.getLocal context objectId =
      .ok (.localGet objectId, objectKind))
    (objectFound : findFVar? (functionBindings sourceFunction) objectId =
      some objectIndex)
    (callFound : callIndex? sourceModule
      (.runtime (.dec amount check objectFields?)) = some id)
    (continuationAdapted :
      CodeAdapted context sourceModule sourceFunction labels continuation targetRest)
    (hObject : locals.get objectIndex = some (.i32 objectHandle))
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (hostContract (.dec amount check objectFields?)))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 0)
    (decoded : decodeArgs initial.host.handles #[.tobject] [.i32 objectHandle] =
      .ok #[sourceObject]) :
    EffectStepSimulates context sourceModule sourceFunction labels module hostEnv
      initial.host.runtime sourceRuntime sourceEnv
      (.dec objectId amount check false objectFields? continuation) continuation
      ([.localGet objectIndex, .call id] ++ targetRest) targetRest initial
      (successfulHostStore initial sourceRuntime initial.host.handles) locals := by
  apply effectStepSimulates_unaryHost
  · intro externals
    simp [executeStep, coreStep, objectLookup, updated]
  · exact codeAdapted_dec objectCompiled objectFound callFound continuationAdapted
  · exact initialRelated
  · exact hObject
  · exact hImp
  · exact hSat
  · exact hi
  · exact hContract
  · exact hParams
  · exact hResults
  · simpa [successfulHostStore] using
      hostStep_dec_of_decode initial amount check objectFields?
        [.i32 objectHandle] sourceObject sourceRuntime decoded updated

/-- Explicit deletion through the unary host boundary. -/
theorem effectStepSimulates_delete
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv RuntimeHost} {spec : Wasm.HostSpec RuntimeHost}
    {id : Nat} {imp : Wasm.ImportDecl} {sourceEnv : Env}
    {objectId : Lean.FVarId} {continuation : Lean.Compiler.LCNF.Code .impure}
    {initial : Wasm.Store RuntimeHost} {locals : Wasm.Locals}
    {objectIndex : Nat} {objectHandle : Handle} {sourceObject : Value}
    {sourceRuntime : RuntimeState} {targetRest : Wasm.Program}
    (objectLookup : lookupValue sourceEnv objectId = .ok sourceObject)
    (updated : deleteValue initial.host.runtime sourceObject = .ok sourceRuntime)
    (initialRelated :
      StateRelated sourceFunction initial.host.runtime sourceEnv initial locals)
    (objectCompiled : Fir.Wasm.getLocal context objectId =
      .ok (.localGet objectId, .object))
    (objectFound : findFVar? (functionBindings sourceFunction) objectId =
      some objectIndex)
    (callFound : callIndex? sourceModule (.runtime .delete) = some id)
    (continuationAdapted :
      CodeAdapted context sourceModule sourceFunction labels continuation targetRest)
    (hObject : locals.get objectIndex = some (.i32 objectHandle))
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (hostContract .delete))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 0)
    (decoded : decodeArgs initial.host.handles #[.object] [.i32 objectHandle] =
      .ok #[sourceObject]) :
    EffectStepSimulates context sourceModule sourceFunction labels module hostEnv
      initial.host.runtime sourceRuntime sourceEnv (.del objectId continuation)
      continuation ([.localGet objectIndex, .call id] ++ targetRest) targetRest
      initial (successfulHostStore initial sourceRuntime initial.host.handles)
      locals := by
  apply effectStepSimulates_unaryHost
  · intro externals
    simp [executeStep, coreStep, objectLookup, updated]
  · exact codeAdapted_delete objectCompiled objectFound callFound
      continuationAdapted
  · exact initialRelated
  · exact hObject
  · exact hImp
  · exact hSat
  · exact hi
  · exact hContract
  · exact hParams
  · exact hResults
  · simpa [successfulHostStore] using
      hostStep_delete_of_decode initial [.i32 objectHandle] sourceObject
        sourceRuntime decoded updated

/-- Persistent increments are source and target control-flow no-ops. -/
theorem effectStepSimulates_inc_persistent
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv RuntimeHost} {sourceEnv : Env}
    {objectId : Lean.FVarId} {amount : Nat} {check : Bool}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {initial : Wasm.Store RuntimeHost} {locals : Wasm.Locals}
    {targetRest : Wasm.Program}
    (initialRelated :
      StateRelated sourceFunction initial.host.runtime sourceEnv initial locals)
    (continuationAdapted :
      CodeAdapted context sourceModule sourceFunction labels continuation targetRest) :
    EffectStepSimulates context sourceModule sourceFunction labels module hostEnv
      initial.host.runtime initial.host.runtime sourceEnv
      (.inc objectId amount check true continuation) continuation targetRest
      targetRest initial initial locals := by
  apply effectStepSimulates_elided
  · intro externals
    simp [executeStep, coreStep]
  · exact codeAdapted_inc_persistent continuationAdapted
  · exact initialRelated

/-- Persistent decrements are source and target control-flow no-ops. -/
theorem effectStepSimulates_dec_persistent
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv RuntimeHost} {sourceEnv : Env}
    {objectId : Lean.FVarId} {amount : Nat} {check : Bool}
    {objectFields? : Option Nat} {continuation : Lean.Compiler.LCNF.Code .impure}
    {initial : Wasm.Store RuntimeHost} {locals : Wasm.Locals}
    {targetRest : Wasm.Program}
    (initialRelated :
      StateRelated sourceFunction initial.host.runtime sourceEnv initial locals)
    (continuationAdapted :
      CodeAdapted context sourceModule sourceFunction labels continuation targetRest) :
    EffectStepSimulates context sourceModule sourceFunction labels module hostEnv
      initial.host.runtime initial.host.runtime sourceEnv
      (.dec objectId amount check true objectFields? continuation) continuation
      targetRest targetRest initial initial locals := by
  apply effectStepSimulates_elided
  · intro externals
    simp [executeStep, coreStep]
  · exact codeAdapted_dec_persistent continuationAdapted
  · exact initialRelated

/-- The empty constructor-test suffix executes its already adapted fallback. -/
theorem caseChainWP_nil
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv RuntimeHost}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {discr : Lean.FVarId} {fallback : List Fir.Wasm.Instruction}
    {target : Wasm.Program} {targetStore : Wasm.Store RuntimeHost}
    {targetLocals : Wasm.Locals} {tail : List Wasm.Value}
    {Q : Wasm.Assertion RuntimeHost}
    (fallbackAdapted :
      instructions sourceModule sourceFunction labels fallback = .ok target)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv targetStore targetLocals)
    (fallbackWP :
      Wasm.wp module target Q targetStore
        { targetLocals with values := tail } hostEnv) :
    CaseChainWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv discr [] fallback target targetStore targetLocals
      tail Q := by
  exact ⟨caseChainAdapted_nil fallbackAdapted, stateRelated, fallbackWP⟩

/-- A source default is omitted from the constructor-test suffix. -/
theorem caseChainWP_default
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv RuntimeHost}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {discr : Lean.FVarId} {code : Lean.Compiler.LCNF.Code .impure}
    {alts : List (Lean.Compiler.LCNF.Alt .impure)}
    {fallback : List Fir.Wasm.Instruction} {target : Wasm.Program}
    {targetStore : Wasm.Store RuntimeHost} {targetLocals : Wasm.Locals}
    {tail : List Wasm.Value} {Q : Wasm.Assertion RuntimeHost}
    (rest :
      CaseChainWP context sourceModule sourceFunction labels module hostEnv
        sourceRuntime sourceEnv discr alts fallback target targetStore targetLocals
        tail Q) :
    CaseChainWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv discr (.default code :: alts) fallback target
      targetStore targetLocals tail Q := by
  exact ⟨caseChainAdapted_default rest.1, rest.2⟩

/--
Semantic constructor-test rule. Structural adaptation is required for both
arms, but the weakest-precondition premise follows only the arm selected by
the source `getTag` result. This is the path-sensitive induction step used by
the hit and miss rules below.
-/
theorem caseChainWP_constructor
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv RuntimeHost} {spec : Wasm.HostSpec RuntimeHost}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {discr : Lean.FVarId} {info : Lean.Compiler.LCNF.CtorInfo}
    {code : Lean.Compiler.LCNF.Code .impure}
    {alts : List (Lean.Compiler.LCNF.Alt .impure)}
    {fallback : List Fir.Wasm.Instruction}
    {thenTarget elseTarget : Wasm.Program}
    {initial : Wasm.Store RuntimeHost} {locals : Wasm.Locals}
    {tail : List Wasm.Value} {Q : Wasm.Assertion RuntimeHost}
    {discrIndex getTagIndex : Nat} {handle : Handle}
    {imp : Wasm.ImportDecl} {sourceObject : Value} {actualTag : Nat}
    (fits : Fir.Wasm.constructorTagFitsI32 info = true)
    (thenAdapted :
      CodeAdapted context sourceModule sourceFunction labels code thenTarget)
    (elseAdapted :
      CaseChainAdapted context sourceModule sourceFunction labels discr alts
        fallback elseTarget)
    (discrFound :
      findFVar? (sourceFunction.params.toList ++ sourceFunction.locals.toList)
        discr = some discrIndex)
    (getTagFound :
      callIndex? sourceModule (.runtime .getTag) = some getTagIndex)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals)
    (hLocal : locals.get discrIndex = some (.i32 handle))
    (hImp : module.imports[getTagIndex]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : getTagIndex < module.imports.length)
    (hContract :
      spec.contracts[getTagIndex]? = some (hostContract .getTag))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (decoded :
      decodeArgs initial.host.handles #[.tobject] [.i32 handle] =
        .ok #[sourceObject])
    (tagged : getTag initial.host.runtime sourceObject = .ok actualTag)
    (actualFits : actualTag < UInt32.size)
    (expectedFits : info.cidx < UInt32.size)
    (selectedWP :
      Wasm.wp module
        (if actualTag = info.cidx then thenTarget else elseTarget)
        (CaseResumePost module hostEnv [] Q tail) initial
        { locals with values := tail } hostEnv) :
    CaseChainWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv discr (.ctorAlt info code :: alts) fallback
      [.localGet discrIndex, .call getTagIndex,
        .const (UInt32.ofNat info.cidx), .eq,
        .iff 0 0 thenTarget elseTarget]
      initial locals tail Q := by
  refine ⟨caseChainAdapted_constructor fits thenAdapted elseAdapted discrFound
    getTagFound, stateRelated, ?_⟩
  apply wp_getTag_case_test (spec := spec) (rest := []) sourceObject actualTag
    info.cidx
  · simpa [Wasm.Locals.get] using hLocal
  · exact hImp
  · exact hSat
  · exact hi
  · exact hContract
  · exact hParams
  · exact hResults
  · exact decoded
  · exact tagged
  · exact actualFits
  · exact expectedFits
  · rw [StateRelated.clearFailures stateRelated]
    exact selectedWP

/--
Path-sensitive constructor hit: only the selected source branch needs a
semantic `CodeWP`; the unselected suffix remains a structural obligation.
-/
theorem caseChainWP_constructor_hit
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv RuntimeHost} {spec : Wasm.HostSpec RuntimeHost}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {discr : Lean.FVarId} {info : Lean.Compiler.LCNF.CtorInfo}
    {code : Lean.Compiler.LCNF.Code .impure}
    {alts : List (Lean.Compiler.LCNF.Alt .impure)}
    {fallback : List Fir.Wasm.Instruction}
    {thenTarget elseTarget : Wasm.Program}
    {initial : Wasm.Store RuntimeHost} {locals : Wasm.Locals}
    {tail : List Wasm.Value} {Q : Wasm.Assertion RuntimeHost}
    {discrIndex getTagIndex : Nat} {handle : Handle}
    {imp : Wasm.ImportDecl} {sourceObject : Value} {actualTag : Nat}
    (fits : Fir.Wasm.constructorTagFitsI32 info = true)
    (thenBranch :
      CodeWP context sourceModule sourceFunction labels module hostEnv
        sourceRuntime sourceEnv code thenTarget initial locals tail
        (CaseResumePost module hostEnv [] Q tail))
    (elseAdapted :
      CaseChainAdapted context sourceModule sourceFunction labels discr alts
        fallback elseTarget)
    (tagEq : actualTag = info.cidx)
    (discrFound :
      findFVar? (sourceFunction.params.toList ++ sourceFunction.locals.toList)
        discr = some discrIndex)
    (getTagFound :
      callIndex? sourceModule (.runtime .getTag) = some getTagIndex)
    (hLocal : locals.get discrIndex = some (.i32 handle))
    (hImp : module.imports[getTagIndex]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : getTagIndex < module.imports.length)
    (hContract :
      spec.contracts[getTagIndex]? = some (hostContract .getTag))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (decoded :
      decodeArgs initial.host.handles #[.tobject] [.i32 handle] =
        .ok #[sourceObject])
    (tagged : getTag initial.host.runtime sourceObject = .ok actualTag)
    (actualFits : actualTag < UInt32.size)
    (expectedFits : info.cidx < UInt32.size) :
    CaseChainWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv discr (.ctorAlt info code :: alts) fallback
      [.localGet discrIndex, .call getTagIndex,
        .const (UInt32.ofNat info.cidx), .eq,
        .iff 0 0 thenTarget elseTarget]
      initial locals tail Q := by
  apply caseChainWP_constructor fits thenBranch.1 elseAdapted discrFound getTagFound
    thenBranch.2.1 hLocal hImp hSat hi hContract hParams hResults decoded tagged
    actualFits expectedFits
  simpa [tagEq] using thenBranch.2.2

/--
Path-sensitive constructor miss: the current source arm only needs structural
adaptation and the semantic proof proceeds recursively through the suffix.
-/
theorem caseChainWP_constructor_miss
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv RuntimeHost} {spec : Wasm.HostSpec RuntimeHost}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {discr : Lean.FVarId} {info : Lean.Compiler.LCNF.CtorInfo}
    {code : Lean.Compiler.LCNF.Code .impure}
    {alts : List (Lean.Compiler.LCNF.Alt .impure)}
    {fallback : List Fir.Wasm.Instruction}
    {thenTarget elseTarget : Wasm.Program}
    {initial : Wasm.Store RuntimeHost} {locals : Wasm.Locals}
    {tail : List Wasm.Value} {Q : Wasm.Assertion RuntimeHost}
    {discrIndex getTagIndex : Nat} {handle : Handle}
    {imp : Wasm.ImportDecl} {sourceObject : Value} {actualTag : Nat}
    (fits : Fir.Wasm.constructorTagFitsI32 info = true)
    (thenAdapted :
      CodeAdapted context sourceModule sourceFunction labels code thenTarget)
    (elseBranch :
      CaseChainWP context sourceModule sourceFunction labels module hostEnv
        sourceRuntime sourceEnv discr alts fallback elseTarget initial locals tail
        (CaseResumePost module hostEnv [] Q tail))
    (tagNe : actualTag ≠ info.cidx)
    (discrFound :
      findFVar? (sourceFunction.params.toList ++ sourceFunction.locals.toList)
        discr = some discrIndex)
    (getTagFound :
      callIndex? sourceModule (.runtime .getTag) = some getTagIndex)
    (hLocal : locals.get discrIndex = some (.i32 handle))
    (hImp : module.imports[getTagIndex]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : getTagIndex < module.imports.length)
    (hContract :
      spec.contracts[getTagIndex]? = some (hostContract .getTag))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (decoded :
      decodeArgs initial.host.handles #[.tobject] [.i32 handle] =
        .ok #[sourceObject])
    (tagged : getTag initial.host.runtime sourceObject = .ok actualTag)
    (actualFits : actualTag < UInt32.size)
    (expectedFits : info.cidx < UInt32.size) :
    CaseChainWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv discr (.ctorAlt info code :: alts) fallback
      [.localGet discrIndex, .call getTagIndex,
        .const (UInt32.ofNat info.cidx), .eq,
        .iff 0 0 thenTarget elseTarget]
      initial locals tail Q := by
  apply caseChainWP_constructor fits thenAdapted elseBranch.1 discrFound getTagFound
    elseBranch.2.1 hLocal hImp hSat hi hContract hParams hResults decoded tagged
    actualFits expectedFits
  simpa [tagNe] using elseBranch.2.2

/-- A semantically established full test chain is a semantic source `.cases`. -/
theorem codeWP_cases
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv RuntimeHost}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {cases : Lean.Compiler.LCNF.Cases .impure}
    {fallback : List Fir.Wasm.Instruction} {target : Wasm.Program}
    {targetStore : Wasm.Store RuntimeHost} {targetLocals : Wasm.Locals}
    {tail : List Wasm.Value} {Q : Wasm.Assertion RuntimeHost}
    (fallbackCompiled :
      Fir.Wasm.compileCaseFallback context cases.alts.toList = .ok fallback)
    (chain :
      CaseChainWP context sourceModule sourceFunction labels module hostEnv
        sourceRuntime sourceEnv cases.discr cases.alts.toList fallback target
        targetStore targetLocals tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv (.cases cases) target targetStore targetLocals tail Q := by
  exact ⟨codeAdapted_cases ⟨fallback, fallbackCompiled, chain.1⟩, chain.2⟩

end FirTalos.Correctness
