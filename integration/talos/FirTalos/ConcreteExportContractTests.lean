import FirTalos.ConcreteRootedTerminal
import FirTalos.ConcreteFaultCorrectness
import FirTalos.ConcreteObservationSensitivity
import FirTalos.TrustAuditCore

/-!
# Public export contract regressions

The client statements below are independent expectations, not inferred types
or generated fingerprints. They retain the current admission/resource/runtime
premises, and the fault endpoint's explicit simulation certificate. They do
not claim those premises are discharged. Observable projections below also
protect the meaning of the predicates used in the public conclusions.
-/

namespace FirTalos.Concrete.ExportContractTests

open Lean Lean.Compiler Fir.Wasm Fir.Wasm.Concrete Fir.LeanIR.Impure FirTalos.Correctness

section RootedReturn

variable
    {program : Fir.LeanIR.ImpureProgram} {context : Fir.Wasm.Context}
    {code : Lean.Compiler.LCNF.Code .impure} {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function} {targetModule : AdaptedModule}
    {hosts : ResolvedHosts} {exportName : String}
    (spec : ConcreteSupportedExport program context code sourceModule
      sourceFunction targetModule hosts exportName)
    {externals : ExternalImpl}
    (admission : ConcreteStructuredCompilerCurrentStepAdmission program
      sourceModule targetModule hosts externals)
    (addressSpaceSafety : ConcreteStructuredCurrentStepAddressSpaceSafety program
      sourceModule targetModule hosts externals)
    (contextCaches : context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program)
    {facts : ReuseCapacityFacts} {remainingBytes : Nat}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {initial : Wasm.Store Host} {initialWitness : RefinementWitness}
    {parameters : List Wasm.Value} {observation : Observation} {value : Value}
    (parameterCount : parameters.length = spec.targetFunction.numParams)
    (runtimeInvariant : ConcreteReuseCapacityCacheAbiFrame context sourceModule
      sourceFunction externals facts remainingBytes sourceRuntime sourceEnv
      initial (spec.targetFunction.toLocals parameters.reverse) initialWitness)

include admission addressSpaceSafety contextCaches parameterCount runtimeInvariant

private theorem rootedEvaluation
    (evaluation : ExecEvaluates externals
      (sourceCodeState context sourceRuntime sourceEnv code) observation)
    (success : observation.outcome = .returned value) :
    ∃ resultRuntime,
      observation = ReturnedObservation resultRuntime value ∧
      ConcreteExportTerminatesWith hosts.env targetModule.wasmModule exportName
        initial parameters
        (RefinedReturnPost resultRuntime value spec.sourceResultKind []) :=
  spec.terminatesWith_of_rootedExecEvaluates admission addressSpaceSafety
    contextCaches parameterCount runtimeInvariant evaluation success

private theorem rootedRun
    {fuel : Nat}
    (execution : Fir.LeanIR.Impure.run fuel externals
      (sourceCodeState context sourceRuntime sourceEnv code) = .done observation)
    (success : observation.outcome = .returned value) :
    ∃ resultRuntime,
      observation = ReturnedObservation resultRuntime value ∧
      ConcreteExportTerminatesWith hosts.env targetModule.wasmModule exportName
        initial parameters
        (RefinedReturnPost resultRuntime value spec.sourceResultKind []) :=
  spec.terminatesWith_of_rootedRun admission addressSpaceSafety
    contextCaches parameterCount runtimeInvariant execution success

/- Deliberate weakenings of the successful-return endpoint. They keep its
real proof dependencies, but forget either the selected ABI or the connection
to the source observation. The signature check must reject both. -/
private theorem existentialAbiRun
    {fuel : Nat}
    (execution : Fir.LeanIR.Impure.run fuel externals
      (sourceCodeState context sourceRuntime sourceEnv code) = .done observation)
    (success : observation.outcome = .returned value) :
    ∃ resultRuntime kind,
      observation = ReturnedObservation resultRuntime value ∧
      ConcreteExportTerminatesWith hosts.env targetModule.wasmModule exportName
        initial parameters
        (RefinedReturnPost resultRuntime value kind []) := by
  obtain ⟨runtime, observed, returned⟩ :=
    spec.terminatesWith_of_rootedRun admission addressSpaceSafety
      contextCaches parameterCount runtimeInvariant execution success
  exact ⟨runtime, spec.sourceResultKind, observed, returned⟩

private theorem unrelatedObservationRun
    {fuel : Nat}
    (execution : Fir.LeanIR.Impure.run fuel externals
      (sourceCodeState context sourceRuntime sourceEnv code) = .done observation)
    (success : observation.outcome = .returned value) :
    ∃ resultRuntime,
      ConcreteExportTerminatesWith hosts.env targetModule.wasmModule exportName
        initial parameters
        (RefinedReturnPost resultRuntime value spec.sourceResultKind []) := by
  obtain ⟨runtime, _, returned⟩ :=
    spec.terminatesWith_of_rootedRun admission addressSpaceSafety
      contextCaches parameterCount runtimeInvariant execution success
  exact ⟨runtime, returned⟩

end RootedReturn

private theorem faultSimulation
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec :
      ConcreteSupportedExport program context sourceCode sourceModule
        sourceFunction target hosts exportName)
    {sourceExternals : ExternalImpl}
    {sourceRuntime faultRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {initialWitness : RefinementWitness}
    {parameters callerTail : List Wasm.Value}
    {fault : RuntimeFault}
    (simulation :
      ConcreteFaultSimulation context sourceModule sourceFunction
        target.wasmModule hosts.env sourceExternals [] sourceRuntime sourceEnv
        sourceCode spec.targetFunction.body initial
        (spec.targetFunction.toLocals parameters.reverse) initialWitness
        faultRuntime fault)
    (parameterCount :
      parameters.length = spec.targetFunction.numParams) :
    ExecEvaluates sourceExternals
        (sourceCodeState context sourceRuntime sourceEnv sourceCode)
        (FaultObservation faultRuntime fault) ∧
      ConcreteExportTrapsWith hosts.env target.wasmModule exportName initial
        (parameters ++ callerTail) (RefinedFaultPost faultRuntime fault) :=
  spec.faultCorrectOfSimulation simulation parameterCount

private theorem finitePrefix
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {exportName : String}
    (spec : ConcreteSupportedExport program context sourceCode sourceModule
      sourceFunction targetModule hosts exportName)
    {externals : Fir.LeanIR.Impure.ExternalImpl}
    (admission : ConcreteStructuredCompilerCurrentStepAdmission program
      sourceModule targetModule hosts externals)
    (addressSpaceSafety : ConcreteStructuredCurrentStepAddressSpaceSafety program
      sourceModule targetModule hosts externals)
    (contextCaches :
      context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program)
    {facts : Fir.Wasm.ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceRuntime : Fir.LeanIR.Impure.RuntimeState}
    {sourceEnv : Fir.LeanIR.Impure.Env}
    {initial : Wasm.Store Host}
    {initialWitness : Fir.Wasm.Concrete.RefinementWitness}
    {parameters : List Wasm.Value}
    (invariant : ConcreteReuseCapacityCacheAbiFrame context sourceModule
      sourceFunction externals facts remainingBytes sourceRuntime sourceEnv
      initial (spec.targetFunction.toLocals parameters.reverse)
      initialWitness) :
    ConcreteFiniteTraceCorrect externals
      (concreteStructuredWasmMachine targetModule.wasmModule hosts.env)
      (sourceCodeState context sourceRuntime sourceEnv sourceCode)
      (concreteStructuredFunctionEntry spec.targetFunction initial
        parameters) :=
  spec.finiteTraceCorrect_of_currentStepAdmission admission addressSpaceSafety contextCaches invariant

/- Public wrappers select the requested export and execute the actual Talos
interpreter at every sufficiently large fuel. A mere postcondition witness,
arbitrary function index, or fuel-exhausted result cannot satisfy these clients. -/
example {env : Wasm.HostEnv Host} {module : Wasm.Module} {name : String}
    {initial : Wasm.Store Host} {args : List Wasm.Value}
    {post : Wasm.Store Host → List Wasm.Value → Prop}
    (correct : ConcreteExportTerminatesWith env module name initial args post) :
    ∃ index, module.findExport name = some index ∧
      ∃ bound, ∀ fuel ≥ bound, ∃ values final,
        Wasm.run fuel module index initial args env = .Success values final ∧
        post final values := correct

example {env : Wasm.HostEnv Host} {module : Wasm.Module} {name : String}
    {initial : Wasm.Store Host} {args : List Wasm.Value}
    {post : Wasm.Store Host → String → Prop}
    (correct : ConcreteExportTrapsWith env module name initial args post) :
    ∃ index, module.findExport name = some index ∧
      ∃ bound, ∀ fuel ≥ bound, ∃ final message,
        Wasm.run fuel module index initial args env = .Trap final message ∧
        post final message := correct

/- Pin the returned value's selected ABI, caller tail, clear failure channel,
heap/globals, world and ordered trace under one common refinement witness. -/
example {runtime : RuntimeState} {value : Value} {kind : AbiKind}
    {tail values : List Wasm.Value} {final : Wasm.Store Host}
    (post : RefinedReturnPost runtime value kind tail final values) :
    ∃ witness physical,
      LiveHeapRel final.host.runtime.heap witness runtime ∧
      ConcreteGlobalsRel witness final.host.runtime.globals runtime.globals ∧
      final.host.runtime.world = runtime.world ∧
      ConcreteTraceRel witness final.host.runtime.trace runtime.trace ∧
      final.host.failure? = none ∧
      PhysicalValueRel witness kind physical value ∧ values = physical :: tail := by
  obtain ⟨witness, physical, runtimeRel, clear, valueRel, valuesEq⟩ := post
  exact ⟨witness, physical, runtimeRel.heap, runtimeRel.globals, runtimeRel.world,
    runtimeRel.trace, clear, valueRel, valuesEq⟩

example {runtime : RuntimeState} {value wrong : UInt64} {final : Wasm.Store Host}
    (different : value ≠ wrong) :
    ¬ RefinedReturnPost runtime (.scalar (.uint64 value)) .uint64 [] final [.i64 wrong] := by
  intro post
  have equal := post.uint64_values
  simp only [List.cons.injEq, Wasm.Value.i64.injEq, and_true] at equal
  exact different equal.symm

example {runtime : RuntimeState} {value : UInt64} {final : Wasm.Store Host}
    {values : List Wasm.Value} :
    ¬ RefinedReturnPost runtime (.scalar (.uint64 value)) .uint32 [] final values := by
  rintro ⟨_, _, _, _, related, _⟩
  cases related with
  | word32 related => cases related
  | word64 related => cases related
  | float32Bits related => cases related
  | float64Bits related => cases related

/- Faults retain the source payload and runtime observations. ABI failures and
target-only memory/global failures are outside the source-fault postcondition. -/
example {runtime : RuntimeState} {fault : RuntimeFault}
    {final : Wasm.Store Host} {message : String}
    (post : RefinedFaultPost runtime fault final message) :
    ∃ witness failure,
      LiveHeapRel final.host.runtime.heap witness runtime ∧
      ConcreteGlobalsRel witness final.host.runtime.globals runtime.globals ∧
      final.host.runtime.world = runtime.world ∧
      ConcreteTraceRel witness final.host.runtime.trace runtime.trace ∧
      final.host.failure? = some (.runtime failure.toTrap) ∧
      ConcreteErrorSourceRel witness failure fault := by
  obtain ⟨witness, failure, runtimeRel, recorded, related⟩ := post
  exact ⟨witness, failure, runtimeRel.heap, runtimeRel.globals, runtimeRel.world,
    runtimeRel.trace, recorded, related⟩

example {runtime : RuntimeState} {fault : RuntimeFault}
    {final : Wasm.Store Host} {message : String} {index : Nat} {kind : Fir.Wasm.ValueType}
    (abiFailure : final.host.failure? = some (.laneMismatch index kind)) :
    ¬ RefinedFaultPost runtime fault final message := by
  rintro ⟨_, _, _, recorded, _⟩
  cases recorded.symm.trans abiFailure

example {runtime : RuntimeState} {fault : RuntimeFault}
    {final : Wasm.Store Host} {message : String} {failure : ConcreteTargetFailure}
    (targetFailure : final.host.failure? = some (.runtime (.target failure))) :
    ¬ RefinedFaultPost runtime fault final message := by
  rintro ⟨_, _, _, recorded, related⟩
  obtain ⟨_, sourceTrap, _⟩ := related.toTrap
  rw [sourceTrap] at recorded
  cases recorded.symm.trans targetFailure

example {runtime : RuntimeState} {expected actual message : String}
    {final : Wasm.Store Host}
    (post : RefinedFaultPost runtime (.malformed expected) final message)
    (recorded : final.host.failure? = some (.runtime (.source (.runtime (.malformed actual))))) :
    expected = actual := by
  obtain ⟨_, _, _, failureEq, related⟩ := post
  cases related with
  | source => simpa [ConcreteError.toTrap] using failureEq.symm.trans recorded
  | sourceAddress related => cases related

/- Prefix agreement preserves the world token, event count and the event at
EACH position, including its arguments and result under the same witness. -/
example {externals : ExternalImpl} {target : ConcreteResumableMachine}
    {sourceInitial sourceAfter : MachineState} {targetInitial : target.State}
    {count : Nat}
    (correct : ConcreteFiniteTraceCorrect externals target sourceInitial targetInitial)
    (steps : ExecSteps externals count sourceInitial sourceAfter) :
    ∃ targetCount targetAfter witness,
      FinitePath target.step targetCount targetInitial targetAfter ∧
      (target.store targetAfter).host.runtime.world = sourceAfter.runtime.world ∧
      ConcreteTraceRel witness (target.store targetAfter).host.runtime.trace
        sourceAfter.runtime.trace := by
  obtain ⟨simulation, initial⟩ := correct
  obtain ⟨targetCount, targetAfter, path, _, witness, world, trace⟩ :=
    simulation.execSteps initial steps
  exact ⟨targetCount, targetAfter, witness, path, world, trace⟩

example {source : SourcePrefixObservation} {target : ConcretePrefixObservation}
    (related : ConcretePrefixObservationRel source target) :
    target.world = source.world ∧ target.trace.size = source.trace.size ∧
      ∃ witness : RefinementWitness, ∀ (index : Nat)
        (concrete : ConcreteExternalEvent) (semantic : ExternalEvent),
        target.trace[index]? = some concrete → source.trace[index]? = some semantic →
        concrete.name = semantic.name ∧
        concrete.paramKinds.size = semantic.args.size ∧
        concrete.args.size = semantic.args.size ∧
        (∀ (i : Nat) (kind : AbiKind) (lane : LaneValue) (value : Value),
          concrete.paramKinds[i]? = some kind →
          concrete.args[i]? = some lane → semantic.args[i]? = some value →
          ValueRel witness kind lane value) ∧
        ValueRel witness concrete.resultKind concrete.result semantic.result := by
  obtain ⟨witness, world, trace⟩ := related
  refine ⟨world, trace.size, witness, ?_⟩
  intro index concrete semantic concreteAt semanticAt
  have event := trace.events index concrete semantic concreteAt semanticAt
  exact ⟨event.name, event.paramKindsSize, event.argsSize, event.arguments, event.result⟩

example {source : SourcePrefixObservation} {target : ConcretePrefixObservation}
    (different : target.world ≠ source.world) :
    ¬ ConcretePrefixObservationRel source target := by
  rintro ⟨_, world, _⟩
  exact different world

example {source : SourcePrefixObservation} {target : ConcretePrefixObservation}
    (different : target.trace.size ≠ source.trace.size) :
    ¬ ConcretePrefixObservationRel source target := by
  rintro ⟨_, _, trace⟩
  exact different trace.size

example {source : SourcePrefixObservation} {target : ConcretePrefixObservation}
    {index : Nat} {concrete : ConcreteExternalEvent} {semantic : ExternalEvent}
    (concreteAt : target.trace[index]? = some concrete)
    (semanticAt : source.trace[index]? = some semantic)
    (different : concrete.name ≠ semantic.name) :
    ¬ ConcretePrefixObservationRel source target := by
  rintro ⟨_, _, trace⟩
  exact different (trace.events index concrete semantic concreteAt semanticAt).name

/- Check the independent client signature, then create kernel-checked mutants
that erase the conclusion or add an impossible premise. Each keeps the same
transitive axioms: a discarded endpoint proof is retained in a let, so the
axiom audit alone accepts it. Temporary declarations remain inside the scope. -/
open Lean Meta Elab Command in
private def checkContract (endpoint expected : Name) : CommandElabM Unit := do
  let some (.thmInfo actual) := (← getEnv).find? endpoint |
    throwError "contract requires theorem {endpoint}"
  let expectedInfo ← getConstInfo expected
  unless ← liftTermElabM <| isDefEq actual.type expectedInfo.type do
    throwError "public export contract changed: {endpoint}"

open Lean Meta Elab Command in
private def checkWeakeningRejected (endpoint expected : Name)
    (extraPremise : Bool := false) : CommandElabM Unit :=
  withoutModifyingEnv do
    let info ← getConstInfo endpoint
    let mutant := `FirTalos.Concrete.ExportContractTests.temporaryWeakened
    let (type, value) ← liftTermElabM <| forallTelescope info.type fun args conclusion => do
      let original := mkAppN (mkConst endpoint (info.levelParams.map Level.param)) args
      let (result, proof) := if extraPremise then
        (mkForall `unearned .default (mkConst ``False) conclusion,
         mkLambda `unearned .default (mkConst ``False) original)
      else
        (mkConst ``True, mkLet `retainedEndpoint conclusion original (mkConst ``True.intro))
      return (← mkForallFVars args result, ← mkLambdaFVars args proof)
    liftCoreM <| addDecl (.thmDecl {
      name := mutant, levelParams := info.levelParams, type, value })
    let originalAxioms := (← collectAxioms endpoint).map (·.toString)
    FirTalos.TrustAudit.check mutant originalAxioms
    let accepted ← try
      checkContract mutant expected
      pure true
    catch _ => pure false
    if accepted then throwError "weakened export contract escaped: {endpoint}"

/- Re-run these guards from the forced audit even when the test module is cached. -/
open Lean Elab Command in
def audit : CommandElabM Unit := do
  for (endpoint, expected) in #[
    (``ConcreteSupportedExport.terminatesWith_of_rootedExecEvaluates, ``rootedEvaluation),
    (``ConcreteSupportedExport.terminatesWith_of_rootedRun, ``rootedRun),
    (``ConcreteSupportedExport.faultCorrectOfSimulation, ``faultSimulation),
    (``ConcreteSupportedExport.finiteTraceCorrect_of_currentStepAdmission, ``finitePrefix)] do
    checkContract endpoint expected
    checkWeakeningRejected endpoint expected
    checkWeakeningRejected endpoint expected true
    logInfo m!"export contract: {endpoint}: client signature and same-axiom weakening rejection pass"

  let expectedAxioms := (← collectAxioms
    ``ConcreteSupportedExport.terminatesWith_of_rootedRun).map (·.toString)
  for mutant in #[``existentialAbiRun, ``unrelatedObservationRun] do
    FirTalos.TrustAudit.check mutant expectedAxioms
    let accepted ← try
      checkContract mutant ``rootedRun
      pure true
    catch _ => pure false
    if accepted then throwError "weakened return contract escaped: {mutant}"
  logInfo "export contract: existential ABI and unrelated observation rejected with unchanged axioms"

run_cmd audit

end FirTalos.Concrete.ExportContractTests
