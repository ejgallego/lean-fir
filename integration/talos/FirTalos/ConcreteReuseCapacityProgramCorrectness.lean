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
      (stateRelated :
        ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
          targetStore targetLocals witness)
      (step :
        LetStepSimulates context sourceFunction module hostEnv decl targetValue
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
      (stateRelated :
        ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
          targetStore targetLocals witness)
      (step :
        CallLetStepSimulates context sourceFunction module hostEnv
          sourceExternals decl continuation targetValue sourceRuntime
          nextRuntime sourceEnv sourceValue targetStore nextStore targetLocals
          nextLocals resultIndex witness nextWitness)
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
      (stateRelated :
        ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
          targetStore targetLocals witness)
      (step :
        ExternalLetStepSimulates context sourceFunction module hostEnv
          sourceExternals decl continuation targetValue sourceRuntime
          nextRuntime sourceEnv sourceValue targetStore nextStore targetLocals
          nextLocals resultIndex witness nextWitness)
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
      (stateRelated :
        ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
          targetStore targetLocals witness)
      (step :
        LazyLetStepSimulates path context sourceFunction module hostEnv
          sourceExternals decl continuation targetValue sourceRuntime
          nextRuntime sourceEnv sourceValue targetStore nextStore targetLocals
          nextLocals resultIndex witness nextWitness)
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
  cases simulation <;> assumption

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
  | letValue _ _ valueCompiled valueAdapted resultFound _ step _ continued =>
      exact .letValue valueCompiled valueAdapted resultFound step continued
  | callLet _ _ valueCompiled valueAdapted resultFound _ step _ continued =>
      exact .callLet valueCompiled valueAdapted resultFound step continued
  | externalLet _ _ valueCompiled valueAdapted resultFound _ step _ continued =>
      exact .externalLet valueCompiled valueAdapted resultFound step continued
  | lazyLet path _ _ valueCompiled valueAdapted resultFound _ step _
      continued =>
      exact .lazyLet path valueCompiled valueAdapted resultFound step continued
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
  | letValue _ _ _ _ _ _ _ _ continued => exact continued
  | callLet _ _ _ _ _ _ _ _ continued => exact continued
  | externalLet _ _ _ _ _ _ _ _ continued => exact continued
  | lazyLet _ _ _ _ _ _ _ _ _ continued => exact continued
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
