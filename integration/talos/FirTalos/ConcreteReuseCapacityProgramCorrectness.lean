import FirTalos.ConcreteReuseCapacityCorrectness
import FirTalos.ConcreteProgramCorrectness

namespace FirTalos.Concrete

open Lean
open Lean.Compiler
open Fir.Wasm
open Fir.LeanIR.Impure
open Fir.Wasm.Concrete
open FirTalos.Correctness

/--
Capacity-preserving result-step boundary.

`ordinaryStep` owns source control, the concrete execution, and the existing
W6 state refinement. The two indexed state relations state the additional
T4S obligation exactly: every fact in `facts` is valid before the step and
every fact selected by the validator in `nextFacts` is valid after binding the
result. Instantiating `ordinaryStep` with `CallLetStepSimulates` is the complete
interprocedural condition; no stronger property of the callee is hidden in
the recursive code certificate.
-/
structure ReuseCapacityResultStep
    (facts nextFacts : ReuseCapacityFacts)
    (sourceFunction : Fir.Wasm.Function)
    (sourceRuntime nextRuntime : RuntimeState)
    (sourceEnv : Env) (result : FVarId) (sourceValue : Value)
    (targetStore nextStore : Wasm.Store Host)
    (targetLocals nextLocals : Wasm.Locals)
    (beforeWitness afterWitness : RefinementWitness)
    (ordinaryStep : Prop) : Prop where
  ordinary : ordinaryStep
  initialRelated :
    ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
      targetStore targetLocals beforeWitness
  nextRelated :
    ReuseCapacityStateRelated nextFacts sourceFunction nextRuntime
      (bind sourceEnv result sourceValue) nextStore nextLocals afterWitness

/-- Direct-result instantiation of `ReuseCapacityResultStep`. -/
abbrev ReuseCapacityLetStepSimulates
    (facts nextFacts : ReuseCapacityFacts)
    (context : Fir.Wasm.Context)
    (sourceFunction : Fir.Wasm.Function) (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host)
    (decl : LCNF.LetDecl .impure) (targetValue : Wasm.Program)
    (sourceRuntime nextRuntime : RuntimeState) (sourceEnv : Env)
    (sourceValue : Value)
    (targetStore nextStore : Wasm.Store Host)
    (targetLocals nextLocals : Wasm.Locals) (resultIndex : Nat)
    (beforeWitness afterWitness : RefinementWitness) : Prop :=
  ReuseCapacityResultStep facts nextFacts sourceFunction sourceRuntime
    nextRuntime sourceEnv decl.fvarId sourceValue targetStore nextStore
    targetLocals nextLocals beforeWitness afterWitness
    (LetStepSimulates context sourceFunction module hostEnv decl targetValue
      sourceRuntime nextRuntime sourceEnv sourceValue targetStore nextStore
      targetLocals nextLocals resultIndex beforeWitness afterWitness)

/-- External-result instantiation. A response contract may extend the witness
or heap, but it must establish the same explicit post-fact relation. -/
abbrev ReuseCapacityExternalLetStepSimulates
    (facts nextFacts : ReuseCapacityFacts)
    (context : Fir.Wasm.Context)
    (sourceFunction : Fir.Wasm.Function) (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host) (sourceExternals : ExternalImpl)
    (decl : LCNF.LetDecl .impure) (continuation : LCNF.Code .impure)
    (targetValue : Wasm.Program)
    (sourceRuntime nextRuntime : RuntimeState) (sourceEnv : Env)
    (sourceValue : Value)
    (targetStore nextStore : Wasm.Store Host)
    (targetLocals nextLocals : Wasm.Locals) (resultIndex : Nat)
    (beforeWitness afterWitness : RefinementWitness) : Prop :=
  ReuseCapacityResultStep facts nextFacts sourceFunction sourceRuntime
    nextRuntime sourceEnv decl.fvarId sourceValue targetStore nextStore
    targetLocals nextLocals beforeWitness afterWitness
    (ExternalLetStepSimulates context sourceFunction module hostEnv
      sourceExternals decl continuation targetValue sourceRuntime nextRuntime
      sourceEnv sourceValue targetStore nextStore targetLocals nextLocals
      resultIndex beforeWitness afterWitness)

/-- Lazy-cache-result instantiation. -/
abbrev ReuseCapacityLazyLetStepSimulates
    (path : LazyCachePath)
    (facts nextFacts : ReuseCapacityFacts)
    (context : Fir.Wasm.Context)
    (sourceFunction : Fir.Wasm.Function) (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host) (sourceExternals : ExternalImpl)
    (decl : LCNF.LetDecl .impure) (continuation : LCNF.Code .impure)
    (targetValue : Wasm.Program)
    (sourceRuntime nextRuntime : RuntimeState) (sourceEnv : Env)
    (sourceValue : Value)
    (targetStore nextStore : Wasm.Store Host)
    (targetLocals nextLocals : Wasm.Locals) (resultIndex : Nat)
    (beforeWitness afterWitness : RefinementWitness) : Prop :=
  ReuseCapacityResultStep facts nextFacts sourceFunction sourceRuntime
    nextRuntime sourceEnv decl.fvarId sourceValue targetStore nextStore
    targetLocals nextLocals beforeWitness afterWitness
    (LazyLetStepSimulates path context sourceFunction module hostEnv
      sourceExternals decl continuation targetValue sourceRuntime nextRuntime
      sourceEnv sourceValue targetStore nextStore targetLocals nextLocals
      resultIndex beforeWitness afterWitness)

/-- Exact interprocedural W6/T4S boundary. In addition to the existing call
simulation, a successful callee must establish the validator-selected fact map
at the caller's bound result state. -/
abbrev ReuseCapacityCallLetStepSimulates
    (facts nextFacts : ReuseCapacityFacts)
    (context : Fir.Wasm.Context)
    (sourceFunction : Fir.Wasm.Function) (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host) (sourceExternals : ExternalImpl)
    (decl : LCNF.LetDecl .impure) (continuation : LCNF.Code .impure)
    (targetValue : Wasm.Program)
    (sourceRuntime nextRuntime : RuntimeState) (sourceEnv : Env)
    (sourceValue : Value)
    (targetStore nextStore : Wasm.Store Host)
    (targetLocals nextLocals : Wasm.Locals) (resultIndex : Nat)
    (beforeWitness afterWitness : RefinementWitness) : Prop :=
  ReuseCapacityResultStep facts nextFacts sourceFunction sourceRuntime
    nextRuntime sourceEnv decl.fvarId sourceValue targetStore nextStore
    targetLocals nextLocals beforeWitness afterWitness
    (CallLetStepSimulates context sourceFunction module hostEnv sourceExternals
      decl continuation targetValue sourceRuntime nextRuntime sourceEnv
      sourceValue targetStore nextStore targetLocals nextLocals resultIndex
      beforeWitness afterWitness)

/-- Any result step that transports witnesses and retained headers can erase
the destination's stale fact. This is the common constructor for direct lets,
calls, externals, and lazy-cache results that do not themselves create tracked
reuse evidence. -/
theorem ReuseCapacityResultStep.ofErase
    {facts : ReuseCapacityFacts}
    {sourceFunction : Fir.Wasm.Function}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env} {result : FVarId} {sourceValue : Value}
    {targetStore nextStore : Wasm.Store Host}
    {targetLocals nextLocals : Wasm.Locals}
    {beforeWitness afterWitness : RefinementWitness}
    {ordinaryStep : Prop} {resultIndex : Nat} {physical : Wasm.Value}
    (ordinary : ordinaryStep)
    (initialRelated :
      ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
        targetStore targetLocals beforeWitness)
    (finalRelated :
      StateRelated sourceFunction nextRuntime
        (bind sourceEnv result sourceValue) nextStore nextLocals afterWitness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) result = some resultIndex)
    (localUpdate :
      LocalUpdate targetLocals nextLocals resultIndex physical)
    (witnessTransport : WitnessTransport beforeWitness afterWitness)
    (capacityTransport :
      HeaderCapacityTransport targetStore.host.runtime.heap
        nextStore.host.runtime.heap beforeWitness) :
    ReuseCapacityResultStep facts (eraseReuseCapacityFact facts result)
      sourceFunction sourceRuntime nextRuntime sourceEnv result sourceValue
      targetStore nextStore targetLocals nextLocals beforeWitness afterWitness
      ordinaryStep :=
  ⟨ordinary, initialRelated,
    initialRelated.eraseResult finalRelated resultFound localUpdate
      witnessTransport capacityTransport⟩

/-- Tracked-result counterpart of `ofErase`. The caller supplies exactly the
new evidence selected by the validator and its concrete value interpretation.
-/
theorem ReuseCapacityResultStep.ofBind
    {facts : ReuseCapacityFacts}
    {sourceFunction : Fir.Wasm.Function}
    {sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env} {result : FVarId} {sourceValue : Value}
    {targetStore nextStore : Wasm.Store Host}
    {targetLocals nextLocals : Wasm.Locals}
    {beforeWitness afterWitness : RefinementWitness}
    {ordinaryStep : Prop} {resultIndex : Nat} {kind : AbiKind}
    {lane : LaneValue} {evidence : ReuseCapacityEvidence}
    (ordinary : ordinaryStep)
    (initialRelated :
      ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
        targetStore targetLocals beforeWitness)
    (finalRelated :
      StateRelated sourceFunction nextRuntime
        (bind sourceEnv result sourceValue) nextStore nextLocals afterWitness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) result = some resultIndex)
    (kindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some kind)
    (localUpdate :
      LocalUpdate targetLocals nextLocals resultIndex (physicalOfLane lane))
    (witnessTransport : WitnessTransport beforeWitness afterWitness)
    (capacityTransport :
      HeaderCapacityTransport targetStore.host.runtime.heap
        nextStore.host.runtime.heap beforeWitness)
    (valueRelated :
      ReuseCapacityValueRel nextStore.host.runtime.heap afterWitness evidence
        kind lane sourceValue) :
    ReuseCapacityResultStep facts
      (insertReuseCapacityFact facts result evidence) sourceFunction
      sourceRuntime nextRuntime sourceEnv result sourceValue targetStore
      nextStore targetLocals nextLocals beforeWitness afterWitness
      ordinaryStep :=
  ⟨ordinary, initialRelated,
    initialRelated.bindResult finalRelated resultFound kindAt localUpdate
      witnessTransport capacityTransport valueRelated⟩

/-- Construct the interprocedural call boundary for the validator's ordinary
result transfer. These three transport premises are exactly what the existing
`CallLetStepSimulates` contract does not expose: the checked destination write,
witness growth, and preservation of retained allocation headers. -/
theorem ReuseCapacityCallLetStepSimulates.ofErase
    {facts : ReuseCapacityFacts}
    {context : Fir.Wasm.Context}
    {sourceFunction : Fir.Wasm.Function} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {sourceExternals : ExternalImpl}
    {decl : LCNF.LetDecl .impure} {continuation : LCNF.Code .impure}
    {targetValue : Wasm.Program}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {sourceValue : Value}
    {targetStore nextStore : Wasm.Store Host}
    {targetLocals nextLocals : Wasm.Locals} {resultIndex : Nat}
    {beforeWitness afterWitness : RefinementWitness}
    {physical : Wasm.Value}
    (initialRelated :
      ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
        targetStore targetLocals beforeWitness)
    (step :
      CallLetStepSimulates context sourceFunction module hostEnv
        sourceExternals decl continuation targetValue sourceRuntime nextRuntime
        sourceEnv sourceValue targetStore nextStore targetLocals nextLocals
        resultIndex beforeWitness afterWitness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex)
    (localUpdate :
      LocalUpdate targetLocals nextLocals resultIndex physical)
    (witnessTransport : WitnessTransport beforeWitness afterWitness)
    (capacityTransport :
      HeaderCapacityTransport targetStore.host.runtime.heap
        nextStore.host.runtime.heap beforeWitness) :
    ReuseCapacityCallLetStepSimulates facts
      (eraseReuseCapacityFact facts decl.fvarId) context sourceFunction module
      hostEnv sourceExternals decl continuation targetValue sourceRuntime
      nextRuntime sourceEnv sourceValue targetStore nextStore targetLocals
      nextLocals resultIndex beforeWitness afterWitness :=
  ReuseCapacityResultStep.ofErase step initialRelated step.2.2.1 resultFound
    localUpdate witnessTransport capacityTransport

/--
Syntax-directed W6 capacity certificate.

This is the capacity-strengthened analogue of `ConcreteCodeSimulation`.
Every node records the validator fact state and its dynamic interpretation;
result-producing nodes additionally name the authoritative static fact
transfer. `resultFacts` exposes the fact state at the selected return leaf.
Erasing these extra fields recovers the existing executable simulation.
-/
inductive ReuseCapacityCodeSimulation
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (labels : List FVarId)
    (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host)
    (sourceExternals : ExternalImpl) :
    ReuseCapacityFacts →
      RuntimeState → Env → LCNF.Code .impure → Wasm.Program →
      Wasm.Store Host → Wasm.Locals → RefinementWitness →
      ReuseCapacityFacts →
      RuntimeState → Value → AbiKind → Wasm.Store Host →
      RefinementWitness → Wasm.Value → Prop where
  | ret
      (safe :
        reuseCapacitySafeCode facts (.return result) = true)
      (localCompiled :
        Fir.Wasm.getLocal context result = .ok (.localGet result, kind))
      (resultFound :
        findFVar? (functionBindings sourceFunction) result = some resultIndex)
      (kindAt :
        (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
          some kind)
      (sourceLookup : lookup sourceEnv result = some sourceValue)
      (stateRelated :
        ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
          targetStore targetLocals witness)
      (targetLookup : targetLocals.get resultIndex = some physical) :
      ReuseCapacityCodeSimulation context sourceModule sourceFunction labels
        module hostEnv sourceExternals facts sourceRuntime sourceEnv
        (.return result) [.localGet resultIndex, .ret] targetStore targetLocals
        witness facts sourceRuntime sourceValue kind targetStore witness physical
  | letValue
      (safe :
        reuseCapacitySafeCode facts (.let decl continuation) = true)
      (transfer :
        reuseCapacityLetFacts? facts decl = some nextFacts)
      (valueCompiled :
        Fir.Wasm.compileLetValue context decl = .ok valueCode)
      (valueAdapted :
        instructions sourceModule sourceFunction labels valueCode =
          .ok targetValue)
      (resultFound :
        findFVar? (functionBindings sourceFunction) decl.fvarId =
          some resultIndex)
      (step :
        ReuseCapacityLetStepSimulates facts nextFacts context sourceFunction
          module hostEnv decl targetValue sourceRuntime nextRuntime sourceEnv
          sourceValue targetStore nextStore targetLocals nextLocals resultIndex
          witness nextWitness)
      (continued :
        ReuseCapacityCodeSimulation context sourceModule sourceFunction labels
          module hostEnv sourceExternals nextFacts nextRuntime
          (bind sourceEnv decl.fvarId sourceValue) continuation targetRest
          nextStore nextLocals nextWitness resultFacts resultRuntime resultValue
          resultKind resultStore resultWitness physical) :
      ReuseCapacityCodeSimulation context sourceModule sourceFunction labels
        module hostEnv sourceExternals facts sourceRuntime sourceEnv
        (.let decl continuation)
        (targetValue ++ .localSet resultIndex :: targetRest)
        targetStore targetLocals witness resultFacts resultRuntime resultValue
        resultKind resultStore resultWitness physical
  | callLet
      (safe :
        reuseCapacitySafeCode facts (.let decl continuation) = true)
      (transfer :
        reuseCapacityLetFacts? facts decl = some nextFacts)
      (valueCompiled :
        Fir.Wasm.compileLetValue context decl = .ok valueCode)
      (valueAdapted :
        instructions sourceModule sourceFunction labels valueCode =
          .ok targetValue)
      (resultFound :
        findFVar? (functionBindings sourceFunction) decl.fvarId =
          some resultIndex)
      (step :
        ReuseCapacityCallLetStepSimulates facts nextFacts context sourceFunction
          module hostEnv sourceExternals decl continuation targetValue
          sourceRuntime nextRuntime sourceEnv sourceValue targetStore nextStore
          targetLocals nextLocals resultIndex witness nextWitness)
      (continued :
        ReuseCapacityCodeSimulation context sourceModule sourceFunction labels
          module hostEnv sourceExternals nextFacts nextRuntime
          (bind sourceEnv decl.fvarId sourceValue) continuation targetRest
          nextStore nextLocals nextWitness resultFacts resultRuntime resultValue
          resultKind resultStore resultWitness physical) :
      ReuseCapacityCodeSimulation context sourceModule sourceFunction labels
        module hostEnv sourceExternals facts sourceRuntime sourceEnv
        (.let decl continuation)
        (targetValue ++ .localSet resultIndex :: targetRest)
        targetStore targetLocals witness resultFacts resultRuntime resultValue
        resultKind resultStore resultWitness physical
  | externalLet
      (safe :
        reuseCapacitySafeCode facts (.let decl continuation) = true)
      (transfer :
        reuseCapacityLetFacts? facts decl = some nextFacts)
      (valueCompiled :
        Fir.Wasm.compileLetValue context decl = .ok valueCode)
      (valueAdapted :
        instructions sourceModule sourceFunction labels valueCode =
          .ok targetValue)
      (resultFound :
        findFVar? (functionBindings sourceFunction) decl.fvarId =
          some resultIndex)
      (step :
        ReuseCapacityExternalLetStepSimulates facts nextFacts context
          sourceFunction module hostEnv sourceExternals decl continuation
          targetValue sourceRuntime nextRuntime sourceEnv sourceValue
          targetStore nextStore targetLocals nextLocals resultIndex witness
          nextWitness)
      (continued :
        ReuseCapacityCodeSimulation context sourceModule sourceFunction labels
          module hostEnv sourceExternals nextFacts nextRuntime
          (bind sourceEnv decl.fvarId sourceValue) continuation targetRest
          nextStore nextLocals nextWitness resultFacts resultRuntime resultValue
          resultKind resultStore resultWitness physical) :
      ReuseCapacityCodeSimulation context sourceModule sourceFunction labels
        module hostEnv sourceExternals facts sourceRuntime sourceEnv
        (.let decl continuation)
        (targetValue ++ .localSet resultIndex :: targetRest)
        targetStore targetLocals witness resultFacts resultRuntime resultValue
        resultKind resultStore resultWitness physical
  | lazyLet
      (path : LazyCachePath)
      (safe :
        reuseCapacitySafeCode facts (.let decl continuation) = true)
      (transfer :
        reuseCapacityLetFacts? facts decl = some nextFacts)
      (valueCompiled :
        Fir.Wasm.compileLetValue context decl = .ok valueCode)
      (valueAdapted :
        instructions sourceModule sourceFunction labels valueCode =
          .ok targetValue)
      (resultFound :
        findFVar? (functionBindings sourceFunction) decl.fvarId =
          some resultIndex)
      (step :
        ReuseCapacityLazyLetStepSimulates path facts nextFacts context
          sourceFunction module hostEnv sourceExternals decl continuation
          targetValue sourceRuntime nextRuntime sourceEnv sourceValue
          targetStore nextStore targetLocals nextLocals resultIndex witness
          nextWitness)
      (continued :
        ReuseCapacityCodeSimulation context sourceModule sourceFunction labels
          module hostEnv sourceExternals nextFacts nextRuntime
          (bind sourceEnv decl.fvarId sourceValue) continuation targetRest
          nextStore nextLocals nextWitness resultFacts resultRuntime resultValue
          resultKind resultStore resultWitness physical) :
      ReuseCapacityCodeSimulation context sourceModule sourceFunction labels
        module hostEnv sourceExternals facts sourceRuntime sourceEnv
        (.let decl continuation)
        (targetValue ++ .localSet resultIndex :: targetRest)
        targetStore targetLocals witness resultFacts resultRuntime resultValue
        resultKind resultStore resultWitness physical
  | caseOf
      (safe :
        reuseCapacitySafeCode facts (.cases cases) = true)
      (target selectedTarget : Wasm.Program)
      (stateRelated :
        ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
          targetStore targetLocals witness)
      (step :
        ConcreteCasesStepSimulates context sourceModule sourceFunction labels
          module hostEnv sourceRuntime sourceEnv cases selected target
          selectedTarget targetStore targetLocals witness)
      (continued :
        ReuseCapacityCodeSimulation context sourceModule sourceFunction labels
          module hostEnv sourceExternals facts sourceRuntime sourceEnv selected
          selectedTarget targetStore targetLocals witness resultFacts
          resultRuntime resultValue resultKind resultStore resultWitness
          physical) :
      ReuseCapacityCodeSimulation context sourceModule sourceFunction labels
        module hostEnv sourceExternals facts sourceRuntime sourceEnv
        (.cases cases) target targetStore targetLocals witness resultFacts
        resultRuntime resultValue resultKind resultStore resultWitness physical
  | effect
      (safe : reuseCapacitySafeCode facts code = true)
      (target targetRest : Wasm.Program)
      (stateRelated :
        ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
          targetStore targetLocals witness)
      (step :
        EffectStepSimulates context sourceModule sourceFunction labels module
          hostEnv sourceRuntime nextRuntime sourceEnv code continuation target
          targetRest targetStore nextStore targetLocals witness nextWitness)
      (continued :
        ReuseCapacityCodeSimulation context sourceModule sourceFunction labels
          module hostEnv sourceExternals facts nextRuntime sourceEnv continuation
          targetRest nextStore targetLocals nextWitness resultFacts resultRuntime
          resultValue resultKind resultStore resultWitness physical) :
      ReuseCapacityCodeSimulation context sourceModule sourceFunction labels
        module hostEnv sourceExternals facts sourceRuntime sourceEnv code target
        targetStore targetLocals witness resultFacts resultRuntime resultValue
        resultKind resultStore resultWitness physical

/-- The certificate exposes the strengthened relation at its current node. -/
theorem ReuseCapacityCodeSimulation.initialRelated
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {sourceExternals : ExternalImpl}
    {facts resultFacts : ReuseCapacityFacts}
    {sourceRuntime resultRuntime : RuntimeState} {sourceEnv : Env}
    {sourceCode : LCNF.Code .impure} {target : Wasm.Program}
    {targetStore resultStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {witness resultWitness : RefinementWitness}
    {resultValue : Value} {resultKind : AbiKind} {physical : Wasm.Value}
    (simulation :
      ReuseCapacityCodeSimulation context sourceModule sourceFunction labels
        module hostEnv sourceExternals facts sourceRuntime sourceEnv sourceCode
        target targetStore targetLocals witness resultFacts resultRuntime
        resultValue resultKind resultStore resultWitness physical) :
    ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
      targetStore targetLocals witness := by
  cases simulation with
  | ret _ _ _ _ _ stateRelated _ => exact stateRelated
  | letValue _ _ _ _ _ step _ => exact step.initialRelated
  | callLet _ _ _ _ _ step _ => exact step.initialRelated
  | externalLet _ _ _ _ _ step _ => exact step.initialRelated
  | lazyLet _ _ _ _ _ _ step _ => exact step.initialRelated
  | caseOf _ _ _ stateRelated _ _ => exact stateRelated
  | effect _ _ _ stateRelated _ _ => exact stateRelated

/-- Canonical return node. Return syntax is capacity-safe by definition and
leaves the fact map and concrete state unchanged. -/
theorem ReuseCapacityCodeSimulation.returnNode
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {sourceExternals : ExternalImpl}
    {facts : ReuseCapacityFacts}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {result : FVarId} {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals} {witness : RefinementWitness}
    {kind : AbiKind} {sourceValue : Value} {resultIndex : Nat}
    {physical : Wasm.Value}
    (localCompiled :
      Fir.Wasm.getLocal context result = .ok (.localGet result, kind))
    (resultFound :
      findFVar? (functionBindings sourceFunction) result = some resultIndex)
    (kindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some kind)
    (sourceLookup : lookup sourceEnv result = some sourceValue)
    (stateRelated :
      ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
        targetStore targetLocals witness)
    (targetLookup : targetLocals.get resultIndex = some physical) :
    ReuseCapacityCodeSimulation context sourceModule sourceFunction labels
      module hostEnv sourceExternals facts sourceRuntime sourceEnv
      (.return result) [.localGet resultIndex, .ret] targetStore targetLocals
      witness facts sourceRuntime sourceValue kind targetStore witness physical :=
  .ret (by simp [reuseCapacitySafeCode]) localCompiled resultFound kindAt
    sourceLookup stateRelated targetLookup

/-- A selected case branch already starts in the enclosing case state, so its
certificate supplies the strengthened initial relation required by the case
node. -/
theorem ReuseCapacityCodeSimulation.caseOfContinuation
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {sourceExternals : ExternalImpl}
    {facts resultFacts : ReuseCapacityFacts}
    {sourceRuntime resultRuntime : RuntimeState} {sourceEnv : Env}
    {cases : LCNF.Cases .impure} {selected : LCNF.Code .impure}
    {target selectedTarget : Wasm.Program}
    {targetStore resultStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {witness resultWitness : RefinementWitness}
    {resultValue : Value} {resultKind : AbiKind} {physical : Wasm.Value}
    (safe : reuseCapacitySafeCode facts (.cases cases) = true)
    (step :
      ConcreteCasesStepSimulates context sourceModule sourceFunction labels
        module hostEnv sourceRuntime sourceEnv cases selected target
        selectedTarget targetStore targetLocals witness)
    (continued :
      ReuseCapacityCodeSimulation context sourceModule sourceFunction labels
        module hostEnv sourceExternals facts sourceRuntime sourceEnv selected
        selectedTarget targetStore targetLocals witness resultFacts
        resultRuntime resultValue resultKind resultStore resultWitness
        physical) :
    ReuseCapacityCodeSimulation context sourceModule sourceFunction labels
      module hostEnv sourceExternals facts sourceRuntime sourceEnv
      (.cases cases) target targetStore targetLocals witness resultFacts
      resultRuntime resultValue resultKind resultStore resultWitness physical :=
  .caseOf safe target selectedTarget continued.initialRelated step continued

/-- Generic no-result node builder. The operation theorem supplies the
ordinary effect simulation plus witness/header transport; the continuation
builder receives the strengthened post-state derived from those facts. -/
theorem ReuseCapacityCodeSimulation.effectOfTransport
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {sourceExternals : ExternalImpl}
    {facts resultFacts : ReuseCapacityFacts}
    {sourceRuntime nextRuntime resultRuntime : RuntimeState}
    {sourceEnv : Env}
    {code continuation : LCNF.Code .impure}
    {target targetRest : Wasm.Program}
    {targetStore nextStore resultStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {witness nextWitness resultWitness : RefinementWitness}
    {resultValue : Value} {resultKind : AbiKind} {physical : Wasm.Value}
    (safe : reuseCapacitySafeCode facts code = true)
    (related :
      ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
        targetStore targetLocals witness)
    (step :
      EffectStepSimulates context sourceModule sourceFunction labels module
        hostEnv sourceRuntime nextRuntime sourceEnv code continuation target
        targetRest targetStore nextStore targetLocals witness nextWitness)
    (witnessTransport : WitnessTransport witness nextWitness)
    (capacityTransport :
      HeaderCapacityTransport targetStore.host.runtime.heap
        nextStore.host.runtime.heap witness)
    (continued :
      ReuseCapacityStateRelated facts sourceFunction nextRuntime sourceEnv
          nextStore targetLocals nextWitness →
        ReuseCapacityCodeSimulation context sourceModule sourceFunction labels
          module hostEnv sourceExternals facts nextRuntime sourceEnv
          continuation targetRest nextStore targetLocals nextWitness resultFacts
          resultRuntime resultValue resultKind resultStore resultWitness
          physical) :
    ReuseCapacityCodeSimulation context sourceModule sourceFunction labels
      module hostEnv sourceExternals facts sourceRuntime sourceEnv code target
      targetStore targetLocals witness resultFacts resultRuntime resultValue
      resultKind resultStore resultWitness physical :=
  .effect safe target targetRest related step
    (continued
      (related.ofEffectStep step witnessTransport capacityTransport))

/-- Forgetting validation and capacity fields recovers W6's executable code
simulation without changing any source or target endpoint. -/
theorem ReuseCapacityCodeSimulation.erase
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {sourceExternals : ExternalImpl}
    {facts resultFacts : ReuseCapacityFacts}
    {sourceRuntime resultRuntime : RuntimeState} {sourceEnv : Env}
    {sourceCode : LCNF.Code .impure} {target : Wasm.Program}
    {targetStore resultStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {witness resultWitness : RefinementWitness}
    {resultValue : Value} {resultKind : AbiKind} {physical : Wasm.Value}
    (simulation :
      ReuseCapacityCodeSimulation context sourceModule sourceFunction labels
        module hostEnv sourceExternals facts sourceRuntime sourceEnv sourceCode
        target targetStore targetLocals witness resultFacts resultRuntime
        resultValue resultKind resultStore resultWitness physical) :
    ConcreteCodeSimulation context sourceModule sourceFunction labels module
      hostEnv sourceExternals sourceRuntime sourceEnv sourceCode target
      targetStore targetLocals witness resultRuntime resultValue resultKind
      resultStore resultWitness physical := by
  induction simulation with
  | ret _ localCompiled resultFound kindAt sourceLookup stateRelated
      targetLookup =>
      exact .ret localCompiled resultFound kindAt sourceLookup
        stateRelated.stateRelated targetLookup
  | letValue _ _ valueCompiled valueAdapted resultFound step _ continued =>
      exact .letValue valueCompiled valueAdapted resultFound step.ordinary
        continued
  | callLet _ _ valueCompiled valueAdapted resultFound step _ continued =>
      exact .callLet valueCompiled valueAdapted resultFound step.ordinary
        continued
  | externalLet _ _ valueCompiled valueAdapted resultFound step _ continued =>
      exact .externalLet valueCompiled valueAdapted resultFound step.ordinary
        continued
  | lazyLet path _ _ valueCompiled valueAdapted resultFound step _
      continued =>
      exact .lazyLet path valueCompiled valueAdapted resultFound step.ordinary
        continued
  | caseOf _ target selectedTarget _ step _ continued =>
      exact .caseOf target selectedTarget step continued
  | effect _ target targetRest _ step _ continued =>
      exact .effect target targetRest step continued

/-- The selected return leaf still carries the dynamic meaning of its final
validator fact state. -/
theorem ReuseCapacityCodeSimulation.finalRelated
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {sourceExternals : ExternalImpl}
    {facts resultFacts : ReuseCapacityFacts}
    {sourceRuntime resultRuntime : RuntimeState} {sourceEnv : Env}
    {sourceCode : LCNF.Code .impure} {target : Wasm.Program}
    {targetStore resultStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {witness resultWitness : RefinementWitness}
    {resultValue : Value} {resultKind : AbiKind} {physical : Wasm.Value}
    (simulation :
      ReuseCapacityCodeSimulation context sourceModule sourceFunction labels
        module hostEnv sourceExternals facts sourceRuntime sourceEnv sourceCode
        target targetStore targetLocals witness resultFacts resultRuntime
        resultValue resultKind resultStore resultWitness physical) :
    ∃ resultEnv resultLocals,
      ReuseCapacityStateRelated resultFacts sourceFunction resultRuntime
        resultEnv resultStore resultLocals resultWitness := by
  induction simulation with
  | ret _ _ _ _ _ stateRelated _ =>
      exact ⟨_, _, stateRelated⟩
  | letValue _ _ _ _ _ _ _ continued => exact continued
  | callLet _ _ _ _ _ _ _ continued => exact continued
  | externalLet _ _ _ _ _ _ _ continued => exact continued
  | lazyLet _ _ _ _ _ _ _ _ continued => exact continued
  | caseOf _ _ _ _ _ _ continued => exact continued
  | effect _ _ _ _ _ _ continued => exact continued

/-- Capacity certification is a conservative strengthening of the existing
code-to-Wasm weakest-precondition theorem. -/
theorem ReuseCapacityCodeSimulation.toCodeWP
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {sourceExternals : ExternalImpl}
    {facts resultFacts : ReuseCapacityFacts}
    {sourceRuntime resultRuntime : RuntimeState} {sourceEnv : Env}
    {sourceCode : LCNF.Code .impure} {target : Wasm.Program}
    {targetStore resultStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {witness resultWitness : RefinementWitness}
    {resultValue : Value} {resultKind : AbiKind} {physical : Wasm.Value}
    {targetFunction : Wasm.Function}
    {parameters callerTail : List Wasm.Value}
    (simulation :
      ReuseCapacityCodeSimulation context sourceModule sourceFunction labels
        module hostEnv sourceExternals facts sourceRuntime sourceEnv sourceCode
        target targetStore targetLocals witness resultFacts resultRuntime
        resultValue resultKind resultStore resultWitness physical)
    (parameterCount : parameters.length = targetFunction.numParams)
    (resultCount : targetFunction.results.length = 1) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv sourceCode target targetStore targetLocals witness
      []
      (ConcreteFunctionBodyPost targetFunction (parameters ++ callerTail)
        (ExactReturnPost resultStore physical callerTail)) :=
  simulation.erase.toCodeWP parameterCount resultCount

end FirTalos.Concrete
