import FirTalos.ConcreteTraceSimulation
import FirTalos.ConcreteCompilerCorrectness
import FirTalos.ConcreteReuseCapacityCacheCorrectness
import FirTalos.Correctness.StructuredWasmAdequacy

/-!
# Compiler relation for the concrete structured Wasm target

This module begins the W6.7e construction of the compiler-derived ranked weak
simulation.  `ConcreteStructuredCodeFocus` is the local code-state component
of the eventual relation: it records the real two-stage compiler output, the
concrete runtime/local refinement, and the corresponding source and target
control states.  Source and target continuation stacks are deliberately left
outside this component so the same local proof can be lifted through the
frame relation constructed by later slices.

The first transition family is the compiler's genuinely silent case.
Persistent reference-count increments and decrements change only source
control and are erased by lowering.  Their target match is therefore the
reflexive structured path, and the structural source-control rank decreases.
-/

namespace FirTalos.Concrete

open Fir.Wasm
open Fir.Wasm.Concrete
open Fir.LeanIR.Impure
open FirTalos.Correctness

/-- Local compiler relation at a source code node and a running structured
target node.  It fixes the source program, runtime and environment and the
target store, locals and residual program, while leaving both continuation
stacks available to the later frame relation. -/
structure ConcreteStructuredCodeFocus
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (labels : List Lean.FVarId)
    (sourceRuntime : RuntimeState)
    (sourceEnv : Env)
    (sourceCode : Lean.Compiler.LCNF.Code .impure)
    (targetStore : Wasm.Store Host)
    (targetLocals : Wasm.Locals)
    (targetCode : Wasm.Program)
    (witness : RefinementWitness)
    (source : MachineState)
    (target : StructuredWasmState Host) : Prop where
  sourceProgramEq : source.program = context.program
  sourceControlEq : source.control = .code sourceCode
  sourceEnvEq : source.env = sourceEnv
  sourceRuntimeEq : source.runtime = sourceRuntime
  targetStoreEq : target.store = targetStore
  targetControlEq : target.control = .running targetLocals targetCode
  adapted :
    CodeAdapted context sourceModule sourceFunction labels sourceCode targetCode
  stateRelated :
    StateRelated sourceFunction sourceRuntime sourceEnv targetStore targetLocals
      witness
  frameAligned :
    ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv targetStore
      targetLocals witness

/-- The local compiler relation already implies exact world/trace observation
agreement.  Frame correspondence is irrelevant to observations and can be
conjoined later without reproving this fact. -/
theorem ConcreteStructuredCodeFocus.observes
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {witness : RefinementWitness}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels sourceRuntime sourceEnv sourceCode targetStore targetLocals
      targetCode witness source target) :
    ConcretePrefixObservationRel
      (sourcePrefixObservation source)
      (concretePrefixObservation target.store) := by
  refine ⟨witness, ?_, ?_⟩
  · change target.store.host.runtime.world = source.runtime.world
    rw [related.targetStoreEq, related.sourceRuntimeEq]
    exact related.stateRelated.1.world
  · change ConcreteTraceRel witness target.store.host.runtime.trace
      source.runtime.trace
    rw [related.targetStoreEq, related.sourceRuntimeEq]
    exact related.stateRelated.1.trace

/-- A total-correctness weakest-precondition proof with an exact successful
fallthrough postcondition already contains a finite Talos execution witness.
This is the executable-semantics boundary used below: operation refinements
produce the witness themselves, rather than asking the compiler-correctness
theorem's caller to supply an execution certificate. -/
theorem structuredWasmExecutes_fallthrough_of_wp
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {targetStore nextStore : Wasm.Store Host}
    {targetLocals nextLocals : Wasm.Locals}
    {target : Wasm.Program} {tail : List Wasm.Value}
    (executed :
      Wasm.wp module target
        (fun continuation =>
          continuation =
            .Fallthrough nextStore { nextLocals with values := tail })
        targetStore { targetLocals with values := tail } hostEnv) :
    StructuredWasmExecutes module hostEnv targetStore
      { targetLocals with values := tail } target
      (.fallthrough nextStore { nextLocals with values := tail }) := by
  unfold Wasm.wp at executed
  obtain ⟨fuel, stable⟩ := executed
  exact ⟨fuel, by
    simpa [StructuredWasmOutcome.toContinuation] using
      stable fuel (Nat.le_refl fuel)⟩

/-- Reify the target prefix guaranteed by an ordinary concrete `let` law as
an exact successful Talos execution.  The continuation-transformer law is
specialized to the empty continuation; no independent target-execution
premise is introduced. -/
theorem LetStepSimulates.structuredExecutes
    {context : Fir.Wasm.Context}
    {sourceFunction : Fir.Wasm.Function} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {targetValue : Wasm.Program}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {sourceValue : Value}
    {targetStore nextStore : Wasm.Store Host}
    {targetLocals nextLocals : Wasm.Locals} {resultIndex : Nat}
    {witness nextWitness : RefinementWitness} {tail : List Wasm.Value}
    (step : LetStepSimulates context sourceFunction module hostEnv decl
      targetValue sourceRuntime nextRuntime sourceEnv sourceValue targetStore
      nextStore targetLocals nextLocals resultIndex witness nextWitness) :
    StructuredWasmExecutes module hostEnv targetStore
      { targetLocals with values := tail }
      (targetValue ++ [.localSet resultIndex])
      (.fallthrough nextStore { nextLocals with values := tail }) := by
  apply structuredWasmExecutes_fallthrough_of_wp
  let Q : Wasm.Assertion Host := fun continuation =>
    continuation =
      .Fallthrough nextStore { nextLocals with values := tail }
  have finalWP :
      Wasm.wp module [] Q nextStore
        { nextLocals with values := tail } hostEnv :=
    (Wasm.wp_nil).2 rfl
  simpa [Q] using step.2.2.2 [] Q tail finalWP

/-- A straight-line ordinary `let` prefix therefore advances the structured
machine beneath an arbitrary residual program and saved frame stack. -/
theorem LetStepSimulates.structuredFinitePath
    {context : Fir.Wasm.Context}
    {sourceFunction : Fir.Wasm.Function} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {targetValue targetRest : Wasm.Program}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {sourceValue : Value}
    {targetStore nextStore : Wasm.Store Host}
    {targetLocals nextLocals : Wasm.Locals} {resultIndex : Nat}
    {witness nextWitness : RefinementWitness} {tail : List Wasm.Value}
    {frames : List StructuredWasmFrame}
    (flat : StructuredWasmFlatProgram module
      (targetValue ++ [.localSet resultIndex]))
    (step : LetStepSimulates context sourceFunction module hostEnv decl
      targetValue sourceRuntime nextRuntime sourceEnv sourceValue targetStore
      nextStore targetLocals nextLocals resultIndex witness nextWitness) :
    FinitePath (StructuredWasmStep module hostEnv)
      (targetValue ++ [Wasm.Instruction.localSet resultIndex]).length
      ⟨targetStore,
        .running { targetLocals with values := tail }
          (targetValue ++ .localSet resultIndex :: targetRest),
        frames⟩
      ⟨nextStore,
        .running { nextLocals with values := tail } targetRest,
        frames⟩ := by
  simpa [List.append_assoc] using
    flat.finitePathWithSuffix (suffix := targetRest) (frames := frames)
      step.structuredExecutes

/-- The concrete target for any admitted immediate literal followed by its
destination write is a straight-line structured fragment. -/
theorem ImmediateLiteralKind.structuredFlatProgram
    {literal : Lean.Compiler.LCNF.LitValue} {kind : AbiKind}
    (shape : ImmediateLiteralKind literal kind)
    (module : Wasm.Module) (resultIndex : Nat) :
    StructuredWasmFlatProgram module
      ([shape.targetInstruction] ++ [.localSet resultIndex]) := by
  cases shape <;>
    exact .cons (.atomic (by trivial))
      (.cons (.atomic (by trivial)) .nil)

/-- Successful production compilation and adaptation determine the immediate
literal's flat target prefix; no target syntax is admitted independently. -/
theorem ImmediateLiteralSupported.structuredFlatProgram
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {valueCode : List Fir.Wasm.Instruction} {targetValue : Wasm.Program}
    {resultIndex : Nat}
    (supported : ImmediateLiteralSupported context decl)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl = .ok valueCode)
    (valueAdapted :
      instructions sourceModule sourceFunction labels valueCode =
        .ok targetValue) :
    StructuredWasmFlatProgram module
      (targetValue ++ [.localSet resultIndex]) := by
  cases supported with
  | intro literal resultKind valueEq valueKind _ shape =>
      have expectedCompiled :=
        shape.compileLetValue_eq (context := context) valueEq valueKind
      rw [expectedCompiled] at valueCompiled
      injection valueCompiled with valueCodeEq
      subst valueCode
      have expectedAdapted :=
        shape.instructions_eq (sourceModule := sourceModule)
          (sourceFunction := sourceFunction) (labels := labels)
      rw [expectedAdapted] at valueAdapted
      injection valueAdapted with targetValueEq
      subst targetValue
      exact shape.structuredFlatProgram module resultIndex

/-- A local read followed by the generated destination write is the other
cost-zero straight-line prefix used by the first recursive spine. -/
theorem structuredWasmFlatProgram_localGet_localSet
    (module : Wasm.Module) (sourceIndex resultIndex : Nat) :
    StructuredWasmFlatProgram module
      ([.localGet sourceIndex] ++ [.localSet resultIndex]) := by
  exact .cons (.atomic (by trivial))
    (.cons (.atomic (by trivial)) .nil)

/-- A compiler-generated call that resolves to a target import, followed by
the generated destination write, is a two-step flat target fragment. -/
theorem structuredWasmFlatProgram_importCall_localSet
    {module : Wasm.Module} {functionIndex resultIndex : Nat}
    {imp : Wasm.ImportDecl}
    (imported : module.imports[functionIndex]? = some imp) :
    StructuredWasmFlatProgram module
      ([.call functionIndex] ++ [.localSet resultIndex]) := by
  exact .cons (.importedCall imported)
    (.cons (.atomic (by trivial)) .nil)

/-- Flat target fragments are closed under program concatenation. -/
theorem StructuredWasmFlatProgram.append
    {module : Wasm.Module} {left right : Wasm.Program}
    (leftFlat : StructuredWasmFlatProgram module left)
    (rightFlat : StructuredWasmFlatProgram module right) :
    StructuredWasmFlatProgram module (left ++ right) := by
  induction leftFlat with
  | nil => simpa using rightFlat
  | cons head tail ih => exact .cons head ih

/-- The production argument compiler emits only local reads and erased-zero
constants.  Successful adaptation therefore maps its entire output to a flat
target fragment, independently of runtime state or argument values. -/
theorem ConstructorArgsCompiled.structuredFlatProgram
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {args : List (Lean.Compiler.LCNF.Arg .impure)}
    {argumentCode : List Fir.Wasm.Instruction}
    {fieldKinds : List AbiKind} {targetArguments : Wasm.Program}
    (compiled : ConstructorArgsCompiled context args argumentCode fieldKinds)
    (adapted :
      instructions sourceModule sourceFunction labels argumentCode =
        .ok targetArguments) :
    StructuredWasmFlatProgram module targetArguments := by
  induction compiled generalizing targetArguments with
  | nil =>
      have targetEq : targetArguments = [] := by
        have adaptedEq :
            (Except.ok [] : Except AdapterError Wasm.Program) =
              .ok targetArguments := by
          simpa [instructions, pure, Except.pure] using adapted
        exact (Except.ok.inj adaptedEq).symm
      subst targetArguments
      exact .nil
  | erased rest ih =>
      obtain ⟨targetHead, targetRest, headAdapted, restAdapted, targetEq⟩ :=
        instructions_cons_eq_ok adapted
      have targetHeadEq : targetHead = .const 0 := by
        have adaptedEq :
            (Except.ok (.const 0) : Except AdapterError Wasm.Instruction) =
              .ok targetHead := by
          simpa [instruction, pure, Except.pure] using headAdapted
        exact (Except.ok.inj adaptedEq).symm
      subst targetHead
      subst targetArguments
      exact .cons (.atomic (by trivial)) (ih restAdapted)
  | @fvar fvarId kind args argumentCode fieldKinds kindFound rest ih =>
      obtain ⟨targetHead, targetRest, headAdapted, restAdapted, targetEq⟩ :=
        instructions_cons_eq_ok adapted
      cases sourceFound :
          findFVar?
            (sourceFunction.params.toList ++ sourceFunction.locals.toList)
            fvarId with
      | none =>
          simp [instruction, sourceFound] at headAdapted
      | some sourceIndex =>
          have targetHeadEq : targetHead = .localGet sourceIndex := by
            have adaptedEq :
                (Except.ok (.localGet sourceIndex) :
                    Except AdapterError Wasm.Instruction) =
                  .ok targetHead := by
              simpa [instruction, sourceFound, pure, Except.pure] using
                headAdapted
            exact (Except.ok.inj adaptedEq).symm
          subst targetHead
          subst targetArguments
          exact .cons (.atomic (by trivial)) (ih restAdapted)

/-- A successfully compiled argument row followed by any runtime call is flat
after production adaptation whenever the selected call is covered by the
module-wide runtime-call alignment theorem. -/
theorem
    ConcreteSupportedFunction.structuredFlatProgram_compileArgs_runtimeCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule} {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context sourceCode sourceModule
        sourceFunction target hosts)
    {labels : List Lean.FVarId}
    {args : Array (Lean.Compiler.LCNF.Arg .impure)}
    {argumentCode : List Fir.Wasm.Instruction}
    {fieldKinds : Array AbiKind} {operation : RuntimeOp}
    {targetValue : Wasm.Program} {resultIndex : Nat}
    (argumentsCompiled :
      Fir.Wasm.compileArgs context args = .ok (argumentCode, fieldKinds))
    (valueAdapted :
      instructions sourceModule sourceFunction labels
          (argumentCode ++ [.call (.runtime operation)]) =
        .ok targetValue) :
    StructuredWasmFlatProgram target.wasmModule
      (targetValue ++ [.localSet resultIndex]) := by
  obtain ⟨targetArguments, callIndex, argumentsAdapted, callFound,
      targetEq⟩ :=
    instructions_append_call_eq valueAdapted
  obtain ⟨imp, imported, _⟩ := spec.runtimeCallsAligned callFound
  have argumentsFlat :
      StructuredWasmFlatProgram target.wasmModule targetArguments :=
    (ConstructorArgsCompiled.ofCompileArgs argumentsCompiled).structuredFlatProgram
      argumentsAdapted
  subst targetValue
  simpa [List.append_assoc] using
    StructuredWasmFlatProgram.append argumentsFlat
      (structuredWasmFlatProgram_importCall_localSet
        (resultIndex := resultIndex) imported)

/-- A production argument row followed by a compiler-selected external
declaration call is flat after adaptation.  Import status is derived from the
whole-pipeline external-call alignment, not assumed from target syntax. -/
theorem
    ConcreteSupportedFunction.structuredFlatProgram_compileArgs_externalCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule} {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context sourceCode sourceModule
        sourceFunction target hosts)
    {labels : List Lean.FVarId}
    {name : Lean.Name} {declaration : Lean.Compiler.LCNF.Decl .impure}
    {args : Array (Lean.Compiler.LCNF.Arg .impure)}
    {argumentCode : List Fir.Wasm.Instruction}
    {argumentKinds : Array AbiKind}
    {targetValue : Wasm.Program} {resultIndex : Nat}
    (argumentsCompiled :
      Fir.Wasm.compileArgs context args =
        .ok (argumentCode, argumentKinds))
    (declarationFound : program.findDecl? name = some declaration)
    (declarationExternal : ∃ metadata, declaration.value = .extern metadata)
    (valueAdapted :
      instructions sourceModule sourceFunction labels
          (argumentCode ++ [.call (.declaration name)]) =
        .ok targetValue) :
    StructuredWasmFlatProgram target.wasmModule
      (targetValue ++ [.localSet resultIndex]) := by
  obtain ⟨targetArguments, callIndex, argumentsAdapted, callFound,
      targetEq⟩ :=
    instructions_append_declaration_call_eq valueAdapted
  obtain ⟨_operation, _resultKind, imp, _operationName, _operationMatches,
      _resultSignature, imported, _inBounds, _contracted, _parameterCount,
      _resultCount⟩ :=
    spec.externalCall declarationFound declarationExternal callFound
  have argumentsFlat :
      StructuredWasmFlatProgram target.wasmModule targetArguments :=
    (ConstructorArgsCompiled.ofCompileArgs argumentsCompiled).structuredFlatProgram
      argumentsAdapted
  subst targetValue
  simpa [List.append_assoc] using
    StructuredWasmFlatProgram.append argumentsFlat
      (structuredWasmFlatProgram_importCall_localSet
        (resultIndex := resultIndex) imported)

/-- Every admitted pure external result has a compiler-derived straight-line
target prefix: compiled arguments, one resolved import call, and the generated
destination write. -/
theorem PureExternalSupported.structuredFlatProgram
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule} {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context sourceCode sourceModule
        sourceFunction target hosts)
    {labels : List Lean.FVarId}
    {externals : ExternalImpl}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {sourceValue : Value} {stepCost : Nat}
    {valueCode : List Fir.Wasm.Instruction}
    {targetValue : Wasm.Program} {resultIndex : Nat}
    (supported : PureExternalSupported context externals sourceRuntime sourceEnv
      decl continuation nextRuntime sourceValue stepCost)
    (valueCompiled : Fir.Wasm.compileLetValue context decl = .ok valueCode)
    (valueAdapted :
      instructions sourceModule sourceFunction labels valueCode =
        .ok targetValue) :
    StructuredWasmFlatProgram target.wasmModule
      (targetValue ++ [.localSet resultIndex]) := by
  rcases supported with integer | natural | scalar
  · rcases integer with
      ⟨name, args, argumentCode, argumentKinds, _semanticArgs, declaration,
        _value, valueEq, _operation, nonempty, targetFound, targetExternal,
        valueKind, argumentsCompiled, _argumentsEvaluated, _signature,
        _resultCompiled, _semanticCalled, _nextRuntimeEq, _sourceValueEq,
        _stepCostEq⟩
    have expectedCompiled :
        Fir.Wasm.compileLetValue context decl =
          .ok (argumentCode ++ [.call (.declaration name)]) := by
      simp [Fir.Wasm.compileLetValue, valueEq, valueKind, argumentsCompiled,
        targetFound, nonempty, Bind.bind, Except.bind, pure, Except.pure]
    rw [expectedCompiled] at valueCompiled
    have valueCodeEq := Except.ok.inj valueCompiled
    subst valueCode
    have declarationFound : program.findDecl? name = some declaration := by
      rw [← spec.contextProgram]
      exact targetFound
    exact spec.structuredFlatProgram_compileArgs_externalCall
      argumentsCompiled declarationFound targetExternal valueAdapted
  · rcases natural with
      ⟨name, args, argumentCode, argumentKinds, _semanticArgs, declaration,
        _value, valueEq, _operation, nonempty, targetFound, targetExternal,
        valueKind, argumentsCompiled, _argumentsEvaluated, _signature,
        _resultCompiled, _semanticCalled, _nextRuntimeEq, _sourceValueEq,
        _stepCostEq⟩
    have expectedCompiled :
        Fir.Wasm.compileLetValue context decl =
          .ok (argumentCode ++ [.call (.declaration name)]) := by
      simp [Fir.Wasm.compileLetValue, valueEq, valueKind, argumentsCompiled,
        targetFound, nonempty, Bind.bind, Except.bind, pure, Except.pure]
    rw [expectedCompiled] at valueCompiled
    have valueCodeEq := Except.ok.inj valueCompiled
    subst valueCode
    have declarationFound : program.findDecl? name = some declaration := by
      rw [← spec.contextProgram]
      exact targetFound
    exact spec.structuredFlatProgram_compileArgs_externalCall
      argumentsCompiled declarationFound targetExternal valueAdapted
  · rcases scalar with
      ⟨name, args, argumentCode, argumentKinds, _semanticArgs, declaration,
        _value, valueEq, _operation, nonempty, targetFound, targetExternal,
        valueKind, argumentsCompiled, _argumentsEvaluated, _signature,
        _resultCompiled, _semanticCalled, _nextRuntimeEq, _sourceValueEq,
        _stepCostEq⟩
    have expectedCompiled :
        Fir.Wasm.compileLetValue context decl =
          .ok (argumentCode ++ [.call (.declaration name)]) := by
      simp [Fir.Wasm.compileLetValue, valueEq, valueKind, argumentsCompiled,
        targetFound, nonempty, Bind.bind, Except.bind, pure, Except.pure]
    rw [expectedCompiled] at valueCompiled
    have valueCodeEq := Except.ok.inj valueCompiled
    subst valueCode
    have declarationFound : program.findDecl? name = some declaration := by
      rw [← spec.contextProgram]
      exact targetFound
    exact spec.structuredFlatProgram_compileArgs_externalCall
      argumentsCompiled declarationFound targetExternal valueAdapted

/-- Successful adaptation of one symbolic local read determines one atomic
target local read, regardless of the source local's numeric target index. -/
theorem structuredWasmFlatProgram_localGet_of_instructions
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {fvarId : Lean.FVarId} {targetArguments : Wasm.Program}
    (adapted :
      instructions sourceModule sourceFunction labels [.localGet fvarId] =
        .ok targetArguments) :
    StructuredWasmFlatProgram module targetArguments := by
  obtain ⟨targetHead, targetRest, headAdapted, restAdapted, targetEq⟩ :=
    instructions_cons_eq_ok adapted
  have restEq : targetRest = [] := by
    have adaptedEq :
        (Except.ok [] : Except AdapterError Wasm.Program) =
          .ok targetRest := by
      simpa [instructions, pure, Except.pure] using restAdapted
    exact (Except.ok.inj adaptedEq).symm
  cases sourceFound :
      findFVar?
        (sourceFunction.params.toList ++ sourceFunction.locals.toList)
        fvarId with
  | none => simp [instruction, sourceFound] at headAdapted
  | some sourceIndex =>
      have headEq : targetHead = .localGet sourceIndex := by
        have adaptedEq :
            (Except.ok (.localGet sourceIndex) :
                Except AdapterError Wasm.Instruction) =
              .ok targetHead := by
          simpa [instruction, sourceFound, pure, Except.pure] using
            headAdapted
        exact (Except.ok.inj adaptedEq).symm
      subst targetHead
      subst targetRest
      subst targetArguments
      exact .cons (.atomic (by trivial)) .nil

/-- Every direct operation whose compiler shape is one local read followed by
one runtime call has a flat adapted prefix. -/
theorem
    ConcreteSupportedFunction.structuredFlatProgram_localGet_runtimeCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule} {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context sourceCode sourceModule
        sourceFunction target hosts)
    {labels : List Lean.FVarId} {fvarId : Lean.FVarId}
    {operation : RuntimeOp} {targetValue : Wasm.Program} {resultIndex : Nat}
    (valueAdapted :
      instructions sourceModule sourceFunction labels
          [.localGet fvarId, .call (.runtime operation)] =
        .ok targetValue) :
    StructuredWasmFlatProgram target.wasmModule
      (targetValue ++ [.localSet resultIndex]) := by
  obtain ⟨targetArguments, callIndex, argumentsAdapted, callFound,
      targetEq⟩ :=
    instructions_append_call_eq
      (argumentCode := [.localGet fvarId]) valueAdapted
  obtain ⟨imp, imported, _⟩ := spec.runtimeCallsAligned callFound
  have argumentsFlat :
      StructuredWasmFlatProgram target.wasmModule targetArguments :=
    structuredWasmFlatProgram_localGet_of_instructions argumentsAdapted
  subst targetValue
  simpa [List.append_assoc] using
    StructuredWasmFlatProgram.append argumentsFlat
      (structuredWasmFlatProgram_importCall_localSet
        (resultIndex := resultIndex) imported)

/-- Recover the one-local/one-runtime-call target shape from the actual
`compileLetValue` result before applying the generic adapter theorem. -/
theorem
    ConcreteSupportedFunction.structuredFlatProgram_localRuntimeCall_of_compiler
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule} {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context sourceCode sourceModule
        sourceFunction target hosts)
    {labels : List Lean.FVarId}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {fvarId : Lean.FVarId} {operation : RuntimeOp}
    {valueCode : List Fir.Wasm.Instruction}
    {targetValue : Wasm.Program} {resultIndex : Nat}
    (expectedCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.localGet fvarId, .call (.runtime operation)])
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl = .ok valueCode)
    (valueAdapted :
      instructions sourceModule sourceFunction labels valueCode =
        .ok targetValue) :
    StructuredWasmFlatProgram target.wasmModule
      (targetValue ++ [.localSet resultIndex]) := by
  rw [expectedCompiled] at valueCompiled
  injection valueCompiled with valueCodeEq
  subst valueCode
  exact spec.structuredFlatProgram_localGet_runtimeCall valueAdapted

/-- Admitted `USize` projections satisfy the production flatness law. -/
theorem USizeProjectionSupported.structuredFlatProgram
    {program : Fir.LeanIR.ImpureProgram} {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule} {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context sourceCode sourceModule
        sourceFunction target hosts)
    {labels : List Lean.FVarId}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {valueCode : List Fir.Wasm.Instruction}
    {targetValue : Wasm.Program} {resultIndex : Nat}
    (supported : USizeProjectionSupported context decl)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl = .ok valueCode)
    (valueAdapted :
      instructions sourceModule sourceFunction labels valueCode =
        .ok targetValue) :
    StructuredWasmFlatProgram target.wasmModule
      (targetValue ++ [.localSet resultIndex]) := by
  cases supported with
  | intro index objectId objectKind valueEq resultKind objectCompiled
      objectRefines resultCompiled =>
      exact spec.structuredFlatProgram_localRuntimeCall_of_compiler
        (compileLetValue_usizeProjection valueEq resultKind objectCompiled)
        valueCompiled valueAdapted

/-- Admitted object projections satisfy the same production flatness law. -/
theorem ObjectProjectionSupported.structuredFlatProgram
    {program : Fir.LeanIR.ImpureProgram} {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule} {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context sourceCode sourceModule
        sourceFunction target hosts)
    {labels : List Lean.FVarId}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {valueCode : List Fir.Wasm.Instruction}
    {targetValue : Wasm.Program} {resultIndex : Nat}
    (supported : ObjectProjectionSupported context decl)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl = .ok valueCode)
    (valueAdapted :
      instructions sourceModule sourceFunction labels valueCode =
        .ok targetValue) :
    StructuredWasmFlatProgram target.wasmModule
      (targetValue ++ [.localSet resultIndex]) := by
  cases supported with
  | intro index objectId objectKind resultKind valueEq valueKind objectCompiled
      objectRefines resultCompiled fieldKindAligned =>
      exact spec.structuredFlatProgram_localRuntimeCall_of_compiler
        (compileLetValue_objectProjection valueEq valueKind objectCompiled)
        valueCompiled valueAdapted

/-- Admitted packed-scalar projections satisfy production flatness. -/
theorem ScalarProjectionSupported.structuredFlatProgram
    {program : Fir.LeanIR.ImpureProgram} {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule} {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context sourceCode sourceModule
        sourceFunction target hosts)
    {labels : List Lean.FVarId}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {valueCode : List Fir.Wasm.Instruction}
    {targetValue : Wasm.Program} {resultIndex : Nat}
    (supported : ScalarProjectionSupported context decl)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl = .ok valueCode)
    (valueAdapted :
      instructions sourceModule sourceFunction labels valueCode =
        .ok targetValue) :
    StructuredWasmFlatProgram target.wasmModule
      (targetValue ++ [.localSet resultIndex]) := by
  cases supported with
  | intro width offset objectId objectKind resultKind valueEq valueKind
      objectCompiled objectRefines resultCompiled valueKindAligned =>
      exact spec.structuredFlatProgram_localRuntimeCall_of_compiler
        (compileLetValue_scalarProjection valueEq valueKind objectCompiled)
        valueCompiled valueAdapted

/-- Admitted scalar boxing satisfies production flatness independently of
the concrete tagged-or-heap representation selected at runtime. -/
theorem BoxSupported.structuredFlatProgram
    {program : Fir.LeanIR.ImpureProgram} {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule} {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context sourceCode sourceModule
        sourceFunction target hosts)
    {labels : List Lean.FVarId}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {valueCode : List Fir.Wasm.Instruction}
    {targetValue : Wasm.Program} {resultIndex : Nat}
    (supported : BoxSupported context decl)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl = .ok valueCode)
    (valueAdapted :
      instructions sourceModule sourceFunction labels valueCode =
        .ok targetValue) :
    StructuredWasmFlatProgram target.wasmModule
      (targetValue ++ [.localSet resultIndex]) := by
  cases supported with
  | intro scalarId kind resultKind valueEq valueKind resultKindEq
      scalarCompiled annotationKind resultCompiled =>
      exact spec.structuredFlatProgram_localRuntimeCall_of_compiler
        (compileLetValue_box valueEq valueKind scalarCompiled annotationKind)
        valueCompiled valueAdapted

/-- Admitted typed unboxing satisfies production flatness. -/
theorem UnboxSupported.structuredFlatProgram
    {program : Fir.LeanIR.ImpureProgram} {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule} {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context sourceCode sourceModule
        sourceFunction target hosts)
    {labels : List Lean.FVarId}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {valueCode : List Fir.Wasm.Instruction}
    {targetValue : Wasm.Program} {resultIndex : Nat}
    (supported : UnboxSupported context decl)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl = .ok valueCode)
    (valueAdapted :
      instructions sourceModule sourceFunction labels valueCode =
        .ok targetValue) :
    StructuredWasmFlatProgram target.wasmModule
      (targetValue ++ [.localSet resultIndex]) := by
  cases supported with
  | intro objectId objectKind kind valueEq resultTypeEq valueKind
      objectCompiled objectRefines resultCompiled kindCompatible =>
      exact spec.structuredFlatProgram_localRuntimeCall_of_compiler
        (compileLetValue_unbox valueEq valueKind objectCompiled)
        valueCompiled valueAdapted

/-- Admitted sharing observations satisfy production flatness. -/
theorem IsSharedSupported.structuredFlatProgram
    {program : Fir.LeanIR.ImpureProgram} {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule} {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context sourceCode sourceModule
        sourceFunction target hosts)
    {labels : List Lean.FVarId}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {valueCode : List Fir.Wasm.Instruction}
    {targetValue : Wasm.Program} {resultIndex : Nat}
    (supported : IsSharedSupported context decl)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl = .ok valueCode)
    (valueAdapted :
      instructions sourceModule sourceFunction labels valueCode =
        .ok targetValue) :
    StructuredWasmFlatProgram target.wasmModule
      (targetValue ++ [.localSet resultIndex]) := by
  cases supported with
  | intro objectId objectKind valueEq valueKind objectCompiled objectRefines
      resultCompiled =>
      exact spec.structuredFlatProgram_localRuntimeCall_of_compiler
        (compileLetValue_isShared valueEq valueKind objectCompiled)
        valueCompiled valueAdapted

/-- Ownership reset has the same one-local/one-runtime-call compiler shape. -/
theorem ResetSupported.structuredFlatProgram
    {program : Fir.LeanIR.ImpureProgram} {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule} {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context sourceCode sourceModule
        sourceFunction target hosts)
    {labels : List Lean.FVarId}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {valueCode : List Fir.Wasm.Instruction}
    {targetValue : Wasm.Program} {resultIndex : Nat}
    (supported : ResetSupported context decl)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl = .ok valueCode)
    (valueAdapted :
      instructions sourceModule sourceFunction labels valueCode =
        .ok targetValue) :
    StructuredWasmFlatProgram target.wasmModule
      (targetValue ++ [.localSet resultIndex]) := by
  cases supported with
  | intro count objectId objectKind valueEq valueKind objectCompiled
      objectRefines resultCompiled =>
      exact spec.structuredFlatProgram_localRuntimeCall_of_compiler
        (compileLetValue_reset valueEq valueKind objectCompiled)
        valueCompiled valueAdapted

/-- Admitted nonempty constructors use the compiler-characterized argument
prefix followed by one aligned allocation import. -/
theorem NonemptyConstructorSupported.structuredFlatProgram
    {program : Fir.LeanIR.ImpureProgram} {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule} {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context sourceCode sourceModule
        sourceFunction target hosts)
    {labels : List Lean.FVarId}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {valueCode : List Fir.Wasm.Instruction}
    {targetValue : Wasm.Program} {resultIndex : Nat}
    (supported : NonemptyConstructorSupported context decl)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl = .ok valueCode)
    (valueAdapted :
      instructions sourceModule sourceFunction labels valueCode =
        .ok targetValue) :
    StructuredWasmFlatProgram target.wasmModule
      (targetValue ++ [.localSet resultIndex]) := by
  cases supported with
  | intro info args argumentCode fieldKinds resultKind valueEq tagFits
      valueKind argumentsCompiled resultCompiled operationWellFormed nonempty
      objectFieldsFit usizeFieldsFit scalarBytesFit =>
      have expectedCompiled :
          Fir.Wasm.compileLetValue context decl =
            .ok (argumentCode ++
              [.call (.runtime (.allocCtor info fieldKinds resultKind))]) :=
        compileLetValue_constructor valueEq tagFits valueKind
          argumentsCompiled
      rw [expectedCompiled] at valueCompiled
      injection valueCompiled with valueCodeEq
      subst valueCode
      exact spec.structuredFlatProgram_compileArgs_runtimeCall
        argumentsCompiled valueAdapted

/-- A leading symbolic local read may be prepended to a compiled argument row
and runtime call without leaving the flat target fragment.  This is the exact
production shape used by reuse. -/
theorem
    ConcreteSupportedFunction.structuredFlatProgram_localGet_compileArgs_runtimeCall
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule} {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context sourceCode sourceModule
        sourceFunction target hosts)
    {labels : List Lean.FVarId} {fvarId : Lean.FVarId}
    {args : Array (Lean.Compiler.LCNF.Arg .impure)}
    {argumentCode : List Fir.Wasm.Instruction}
    {fieldKinds : Array AbiKind} {operation : RuntimeOp}
    {targetValue : Wasm.Program} {resultIndex : Nat}
    (argumentsCompiled :
      Fir.Wasm.compileArgs context args = .ok (argumentCode, fieldKinds))
    (valueAdapted :
      instructions sourceModule sourceFunction labels
          (.localGet fvarId ::
            argumentCode ++ [.call (.runtime operation)]) =
        .ok targetValue) :
    StructuredWasmFlatProgram target.wasmModule
      (targetValue ++ [.localSet resultIndex]) := by
  have appendedAdapted :
      instructions sourceModule sourceFunction labels
          ([.localGet fvarId] ++
            (argumentCode ++ [.call (.runtime operation)])) =
        .ok targetValue := by
    simpa using valueAdapted
  obtain ⟨targetLocal, targetRest, localAdapted, restAdapted, targetEq⟩ :=
    instructions_append_eq_ok appendedAdapted
  have localFlat :
      StructuredWasmFlatProgram target.wasmModule targetLocal :=
    structuredWasmFlatProgram_localGet_of_instructions localAdapted
  have restFlat :
      StructuredWasmFlatProgram target.wasmModule
        (targetRest ++ [.localSet resultIndex]) :=
    spec.structuredFlatProgram_compileArgs_runtimeCall argumentsCompiled
      restAdapted
  subst targetValue
  simpa [List.append_assoc] using
    StructuredWasmFlatProgram.append localFlat restFlat

/-- Capacity-admitted reuse satisfies production flatness for arbitrary mixed
local/erased constructor arguments. -/
theorem ReuseSupported.structuredFlatProgram
    {program : Fir.LeanIR.ImpureProgram} {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule} {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context sourceCode sourceModule
        sourceFunction target hosts)
    {facts : ReuseCapacityFacts} {labels : List Lean.FVarId}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {valueCode : List Fir.Wasm.Instruction}
    {targetValue : Wasm.Program} {resultIndex : Nat}
    (supported : ReuseSupported context facts decl)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl = .ok valueCode)
    (valueAdapted :
      instructions sourceModule sourceFunction labels valueCode =
        .ok targetValue) :
    StructuredWasmFlatProgram target.wasmModule
      (targetValue ++ [.localSet resultIndex]) := by
  cases supported with
  | intro tokenId info updateHeader args argumentCode fieldKinds resultKind
      evidence valueEq tagFits valueKind tokenCompiled argumentsCompiled
      resultCompiled operationWellFormed capacityFitting resultCompatible
      objectFieldsFit usizeFieldsFit scalarBytesFit =>
      have expectedCompiled :
          Fir.Wasm.compileLetValue context decl =
            .ok (.localGet tokenId :: argumentCode ++
              [.call
                (.runtime
                  (.reuse info updateHeader fieldKinds resultKind))]) :=
        compileLetValue_reuse valueEq valueKind tokenCompiled
          argumentsCompiled
      rw [expectedCompiled] at valueCompiled
      injection valueCompiled with valueCodeEq
      subst valueCode
      exact spec.structuredFlatProgram_localGet_compileArgs_runtimeCall
        argumentsCompiled valueAdapted

/-- Production compilation of an admitted natural literal emits exactly one
runtime import call followed by the destination write.  Runtime-call
alignment supplies the target-import fact, so flatness is derived from the
compiler and adapter rather than stated as a separate certificate. -/
theorem NaturalLiteralSupported.structuredFlatProgram
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {valueCode : List Fir.Wasm.Instruction} {targetValue : Wasm.Program}
    {resultIndex : Nat}
    (spec :
      ConcreteSupportedFunction program context sourceCode sourceModule
        sourceFunction target hosts)
    (supported : NaturalLiteralSupported context decl)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl = .ok valueCode)
    (valueAdapted :
      instructions sourceModule sourceFunction labels valueCode =
        .ok targetValue) :
    StructuredWasmFlatProgram target.wasmModule
      (targetValue ++ [.localSet resultIndex]) := by
  cases supported with
  | intro value valueEq valueKind _ =>
      have expectedCompiled :
          Fir.Wasm.compileLetValue context decl =
            .ok [.call (.runtime (.literal (.nat value) .tobject))] :=
        compileLetValue_naturalLiteral valueEq valueKind
      rw [expectedCompiled] at valueCompiled
      injection valueCompiled with valueCodeEq
      subst valueCode
      cases callFound :
          callIndex? sourceModule
            (.runtime (.literal (.nat value) .tobject)) with
      | none =>
          simp [instructions, instruction, callFound] at valueAdapted
          change
            Except.error AdapterError.unknownCallTarget =
              Except.ok targetValue at valueAdapted
          cases valueAdapted
      | some callIndex =>
          have expectedAdapted :
              instructions sourceModule sourceFunction labels
                  [.call (.runtime (.literal (.nat value) .tobject))] =
                .ok [.call callIndex] := by
            simp [instructions, instruction, callFound]
            rfl
          rw [expectedAdapted] at valueAdapted
          injection valueAdapted with targetValueEq
          subst targetValue
          obtain ⟨imp, imported, _⟩ := spec.naturalLiteralCall callFound
          exact structuredWasmFlatProgram_importCall_localSet imported

/-- The corresponding UTF-8 String literal prefix is likewise recovered from
the production compiler and adapter and ends in a resolved target import. -/
theorem StringLiteralSupported.structuredFlatProgram
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {target : AdaptedModule}
    {hosts : ResolvedHosts}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {valueCode : List Fir.Wasm.Instruction} {targetValue : Wasm.Program}
    {resultIndex : Nat}
    (spec :
      ConcreteSupportedFunction program context sourceCode sourceModule
        sourceFunction target hosts)
    (supported : StringLiteralSupported context decl)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl = .ok valueCode)
    (valueAdapted :
      instructions sourceModule sourceFunction labels valueCode =
        .ok targetValue) :
    StructuredWasmFlatProgram target.wasmModule
      (targetValue ++ [.localSet resultIndex]) := by
  cases supported with
  | intro value valueEq valueKind _ =>
      have expectedCompiled :
          Fir.Wasm.compileLetValue context decl =
            .ok [.call (.runtime (.literal (.str value) .object))] :=
        compileLetValue_stringLiteral valueEq valueKind
      rw [expectedCompiled] at valueCompiled
      injection valueCompiled with valueCodeEq
      subst valueCode
      cases callFound :
          callIndex? sourceModule
            (.runtime (.literal (.str value) .object)) with
      | none =>
          simp [instructions, instruction, callFound] at valueAdapted
          change
            Except.error AdapterError.unknownCallTarget =
              Except.ok targetValue at valueAdapted
          cases valueAdapted
      | some callIndex =>
          have expectedAdapted :
              instructions sourceModule sourceFunction labels
                  [.call (.runtime (.literal (.str value) .object))] =
                .ok [.call callIndex] := by
            simp [instructions, instruction, callFound]
            rfl
          rw [expectedAdapted] at valueAdapted
          injection valueAdapted with targetValueEq
          subst targetValue
          obtain ⟨imp, imported, _⟩ := spec.stringLiteralCall callFound
          exact structuredWasmFlatProgram_importCall_localSet imported

/-- Local-alias admission plus the executable compiler and adapter uniquely
recover that two-instruction target prefix. -/
theorem LocalAliasSupported.structuredFlatProgram
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {valueCode : List Fir.Wasm.Instruction} {targetValue : Wasm.Program}
    {resultIndex : Nat}
    (supported : LocalAliasSupported context decl)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl = .ok valueCode)
    (valueAdapted :
      instructions sourceModule sourceFunction labels valueCode =
        .ok targetValue) :
    StructuredWasmFlatProgram module
      (targetValue ++ [.localSet resultIndex]) := by
  cases supported with
  | intro sourceId kind valueEq resultKind sourceCompiled _ =>
      have emptyCompiled :
          Fir.Wasm.compileArgs context #[] = .ok ([], #[]) := by
        rfl
      have expectedCompiled :
          Fir.Wasm.compileLetValue context decl =
            .ok [.localGet sourceId] := by
        simp [Fir.Wasm.compileLetValue, valueEq, resultKind, sourceCompiled,
          emptyCompiled]
        rfl
      rw [expectedCompiled] at valueCompiled
      injection valueCompiled with valueCodeEq
      subst valueCode
      cases sourceFound :
          findFVar?
            (sourceFunction.params.toList ++ sourceFunction.locals.toList)
            sourceId with
      | none =>
          simp [instructions, instruction, sourceFound, Bind.bind,
            Except.bind] at valueAdapted
      | some sourceIndex =>
          have expectedAdapted :
              instructions sourceModule sourceFunction labels
                  [.localGet sourceId] =
                .ok [.localGet sourceIndex] := by
            simp [instructions, instruction, sourceFound]
            rfl
          rw [expectedAdapted] at valueAdapted
          injection valueAdapted with targetValueEq
          subst targetValue
          exact structuredWasmFlatProgram_localGet_localSet module sourceIndex
            resultIndex

/-- Uniform compiler-shape law for a facts-indexed family of direct values.
It quantifies over the real lowering and adapter results and concludes only
that their generated call/write prefix is structurally flat.  This is a
compiler theorem interface, not a per-program target certificate. -/
def ReuseCapacityDirectTargetFlat
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (labels : List Lean.FVarId)
    (module : Wasm.Module)
    (Supported :
      ReuseCapacityFacts → Lean.Compiler.LCNF.LetDecl .impure → Prop) : Prop :=
  ∀ {facts : ReuseCapacityFacts}
      {decl : Lean.Compiler.LCNF.LetDecl .impure}
      {valueCode : List Fir.Wasm.Instruction}
      {targetValue : Wasm.Program}
      {resultIndex : Nat},
    Supported facts decl →
      Fir.Wasm.compileLetValue context decl = .ok valueCode →
      instructions sourceModule sourceFunction labels valueCode =
          .ok targetValue →
      StructuredWasmFlatProgram module
        (targetValue ++ [.localSet resultIndex])

/-- Flat compiler-shape laws compose across source-admission disjunction. -/
theorem ReuseCapacityDirectTargetFlat.or
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {Left Right :
      ReuseCapacityFacts → Lean.Compiler.LCNF.LetDecl .impure → Prop}
    (left : ReuseCapacityDirectTargetFlat context sourceModule sourceFunction
      labels module Left)
    (right : ReuseCapacityDirectTargetFlat context sourceModule sourceFunction
      labels module Right) :
    ReuseCapacityDirectTargetFlat context sourceModule sourceFunction labels
      module (fun facts decl => Left facts decl ∨ Right facts decl) := by
  intro facts decl valueCode targetValue resultIndex supported valueCompiled
    valueAdapted
  cases supported with
  | inl supported => exact left supported valueCompiled valueAdapted
  | inr supported => exact right supported valueCompiled valueAdapted

/-- Immediate literals satisfy the uniform facts-indexed compiler-shape law. -/
theorem reuseCapacityDirectTargetFlat_immediateLiteral
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module} :
    ReuseCapacityDirectTargetFlat context sourceModule sourceFunction labels
      module (fun _ decl => ImmediateLiteralSupported context decl) := by
  intro facts decl valueCode targetValue resultIndex supported valueCompiled
    valueAdapted
  exact supported.structuredFlatProgram valueCompiled valueAdapted

/-- Local aliases satisfy the same uniform facts-indexed shape law. -/
theorem reuseCapacityDirectTargetFlat_localAlias
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module} :
    ReuseCapacityDirectTargetFlat context sourceModule sourceFunction labels
      module (fun _ decl => LocalAliasSupported context decl) := by
  intro facts decl valueCode targetValue resultIndex supported valueCompiled
    valueAdapted
  exact supported.structuredFlatProgram valueCompiled valueAdapted

/-- Runtime-call alignment discharges the natural-literal shape law. -/
theorem ConcreteSupportedFunction.reuseCapacityDirectTargetFlat_naturalLiteral
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule} {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context sourceCode sourceModule
        sourceFunction target hosts)
    {labels : List Lean.FVarId} :
    ReuseCapacityDirectTargetFlat context sourceModule sourceFunction labels
      target.wasmModule
      (fun _ decl => NaturalLiteralSupported context decl) := by
  intro facts decl valueCode targetValue resultIndex supported valueCompiled
    valueAdapted
  exact supported.structuredFlatProgram spec valueCompiled valueAdapted

/-- Runtime-call alignment also discharges the String-literal shape law. -/
theorem ConcreteSupportedFunction.reuseCapacityDirectTargetFlat_stringLiteral
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule} {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context sourceCode sourceModule
        sourceFunction target hosts)
    {labels : List Lean.FVarId} :
    ReuseCapacityDirectTargetFlat context sourceModule sourceFunction labels
      target.wasmModule
      (fun _ decl => StringLiteralSupported context decl) := by
  intro facts decl valueCode targetValue resultIndex supported valueCompiled
    valueAdapted
  exact supported.structuredFlatProgram spec valueCompiled valueAdapted

theorem ConcreteSupportedFunction.reuseCapacityDirectTargetFlat_reuse
    {program : Fir.LeanIR.ImpureProgram} {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule} {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context sourceCode sourceModule
        sourceFunction target hosts)
    {labels : List Lean.FVarId} :
    ReuseCapacityDirectTargetFlat context sourceModule sourceFunction labels
      target.wasmModule (ReuseSupported context) := by
  intro facts decl valueCode targetValue resultIndex supported valueCompiled
    valueAdapted
  exact supported.structuredFlatProgram spec valueCompiled valueAdapted

theorem ConcreteSupportedFunction.reuseCapacityDirectTargetFlat_usizeProjection
    {program : Fir.LeanIR.ImpureProgram} {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule} {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context sourceCode sourceModule
        sourceFunction target hosts)
    {labels : List Lean.FVarId} :
    ReuseCapacityDirectTargetFlat context sourceModule sourceFunction labels
      target.wasmModule
      (fun _ decl => USizeProjectionSupported context decl) := by
  intro facts decl valueCode targetValue resultIndex supported valueCompiled
    valueAdapted
  exact supported.structuredFlatProgram spec valueCompiled valueAdapted

theorem ConcreteSupportedFunction.reuseCapacityDirectTargetFlat_objectProjection
    {program : Fir.LeanIR.ImpureProgram} {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule} {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context sourceCode sourceModule
        sourceFunction target hosts)
    {labels : List Lean.FVarId} :
    ReuseCapacityDirectTargetFlat context sourceModule sourceFunction labels
      target.wasmModule
      (fun _ decl => ObjectProjectionSupported context decl) := by
  intro facts decl valueCode targetValue resultIndex supported valueCompiled
    valueAdapted
  exact supported.structuredFlatProgram spec valueCompiled valueAdapted

theorem ConcreteSupportedFunction.reuseCapacityDirectTargetFlat_scalarProjection
    {program : Fir.LeanIR.ImpureProgram} {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule} {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context sourceCode sourceModule
        sourceFunction target hosts)
    {labels : List Lean.FVarId} :
    ReuseCapacityDirectTargetFlat context sourceModule sourceFunction labels
      target.wasmModule
      (fun _ decl => ScalarProjectionSupported context decl) := by
  intro facts decl valueCode targetValue resultIndex supported valueCompiled
    valueAdapted
  exact supported.structuredFlatProgram spec valueCompiled valueAdapted

theorem ConcreteSupportedFunction.reuseCapacityDirectTargetFlat_unbox
    {program : Fir.LeanIR.ImpureProgram} {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule} {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context sourceCode sourceModule
        sourceFunction target hosts)
    {labels : List Lean.FVarId} :
    ReuseCapacityDirectTargetFlat context sourceModule sourceFunction labels
      target.wasmModule (fun _ decl => UnboxSupported context decl) := by
  intro facts decl valueCode targetValue resultIndex supported valueCompiled
    valueAdapted
  exact supported.structuredFlatProgram spec valueCompiled valueAdapted

theorem ConcreteSupportedFunction.reuseCapacityDirectTargetFlat_isShared
    {program : Fir.LeanIR.ImpureProgram} {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule} {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context sourceCode sourceModule
        sourceFunction target hosts)
    {labels : List Lean.FVarId} :
    ReuseCapacityDirectTargetFlat context sourceModule sourceFunction labels
      target.wasmModule (fun _ decl => IsSharedSupported context decl) := by
  intro facts decl valueCode targetValue resultIndex supported valueCompiled
    valueAdapted
  exact supported.structuredFlatProgram spec valueCompiled valueAdapted

theorem ConcreteSupportedFunction.reuseCapacityDirectTargetFlat_constructor
    {program : Fir.LeanIR.ImpureProgram} {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule} {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context sourceCode sourceModule
        sourceFunction target hosts)
    {labels : List Lean.FVarId} :
    ReuseCapacityDirectTargetFlat context sourceModule sourceFunction labels
      target.wasmModule
      (fun _ decl => NonemptyConstructorSupported context decl) := by
  intro facts decl valueCode targetValue resultIndex supported valueCompiled
    valueAdapted
  exact supported.structuredFlatProgram spec valueCompiled valueAdapted

theorem ConcreteSupportedFunction.reuseCapacityDirectTargetFlat_box
    {program : Fir.LeanIR.ImpureProgram} {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule} {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context sourceCode sourceModule
        sourceFunction target hosts)
    {labels : List Lean.FVarId} :
    ReuseCapacityDirectTargetFlat context sourceModule sourceFunction labels
      target.wasmModule (fun _ decl => BoxSupported context decl) := by
  intro facts decl valueCode targetValue resultIndex supported valueCompiled
    valueAdapted
  exact supported.structuredFlatProgram spec valueCompiled valueAdapted

/-- The complete facts-indexed direct fragment used by the existing resource
theorem has one uniform compiler-derived flatness law. -/
theorem
    ConcreteSupportedFunction.reuseCapacityDirectTargetFlat_reuseBudgetedDirect
    {program : Fir.LeanIR.ImpureProgram} {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule} {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context sourceCode sourceModule
        sourceFunction target hosts)
    {labels : List Lean.FVarId} :
    ReuseCapacityDirectTargetFlat context sourceModule sourceFunction labels
      target.wasmModule (ReuseBudgetedDirectSupported context) := by
  unfold ReuseBudgetedDirectSupported ReuseConstructorBoxSupported
    ReuseReadOnlyConstructorSupported ReuseReadOnlySupported
    ReuseAliasSupported
  intro facts decl valueCode targetValue resultIndex supported valueCompiled
    valueAdapted
  cases supported with
  | inl constructorBox =>
      cases constructorBox with
      | inl readOnlyConstructor =>
          cases readOnlyConstructor with
          | inl readOnly =>
              cases readOnly with
              | inl reuseOrReader =>
                  cases reuseOrReader with
                  | inl reuseAlias =>
                      cases reuseAlias with
                      | inl reuse =>
                          exact reuse.structuredFlatProgram spec valueCompiled
                            valueAdapted
                      | inr localAlias =>
                          exact localAlias.structuredFlatProgram valueCompiled
                            valueAdapted
                  | inr reader =>
                      cases reader with
                      | inl immediate =>
                          exact immediate.structuredFlatProgram valueCompiled
                            valueAdapted
                      | inr projection =>
                          cases projection with
                          | inl usize =>
                              exact usize.structuredFlatProgram spec
                                valueCompiled valueAdapted
                          | inr objectOrScalar =>
                              cases objectOrScalar with
                              | inl object =>
                                  exact object.structuredFlatProgram spec
                                    valueCompiled valueAdapted
                              | inr scalar =>
                                  exact scalar.structuredFlatProgram spec
                                    valueCompiled valueAdapted
              | inr unboxOrShared =>
                  cases unboxOrShared with
                  | inl unbox =>
                      exact unbox.structuredFlatProgram spec valueCompiled
                        valueAdapted
                  | inr shared =>
                      exact shared.structuredFlatProgram spec valueCompiled
                        valueAdapted
          | inr constructor =>
              exact constructor.structuredFlatProgram spec valueCompiled
                valueAdapted
      | inr box =>
          exact box.structuredFlatProgram spec valueCompiled valueAdapted
  | inr literal =>
      cases literal with
      | inl natural =>
          exact natural.structuredFlatProgram spec valueCompiled valueAdapted
      | inr string =>
          exact string.structuredFlatProgram spec valueCompiled valueAdapted

/-- Interprocedural concrete `let` laws expose the same exact executable
prefix.  Internal-call execution is therefore obtained from the proved
runtime law and will be structurally reified by the shared target theorem. -/
theorem CallLetStepSimulates.structuredExecutes
    {context : Fir.Wasm.Context}
    {sourceFunction : Fir.Wasm.Function} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {externals : ExternalImpl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetValue : Wasm.Program}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {sourceValue : Value}
    {targetStore nextStore : Wasm.Store Host}
    {targetLocals nextLocals : Wasm.Locals} {resultIndex : Nat}
    {witness nextWitness : RefinementWitness} {tail : List Wasm.Value}
    (step : CallLetStepSimulates context sourceFunction module hostEnv
      externals decl continuation targetValue sourceRuntime nextRuntime
      sourceEnv sourceValue targetStore nextStore targetLocals nextLocals
      resultIndex witness nextWitness) :
    StructuredWasmExecutes module hostEnv targetStore
      { targetLocals with values := tail }
      (targetValue ++ [.localSet resultIndex])
      (.fallthrough nextStore { nextLocals with values := tail }) := by
  apply structuredWasmExecutes_fallthrough_of_wp
  let Q : Wasm.Assertion Host := fun continuation =>
    continuation =
      .Fallthrough nextStore { nextLocals with values := tail }
  have finalWP :
      Wasm.wp module [] Q nextStore
        { nextLocals with values := tail } hostEnv :=
    (Wasm.wp_nil).2 rfl
  simpa [Q] using step.2.2.2 [] Q tail finalWP

/-- External-call refinements expose their generated prefix at the identical
executable boundary. -/
theorem ExternalLetStepSimulates.structuredExecutes
    {context : Fir.Wasm.Context}
    {sourceFunction : Fir.Wasm.Function} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {externals : ExternalImpl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetValue : Wasm.Program}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {sourceValue : Value}
    {targetStore nextStore : Wasm.Store Host}
    {targetLocals nextLocals : Wasm.Locals} {resultIndex : Nat}
    {witness nextWitness : RefinementWitness} {tail : List Wasm.Value}
    (step : ExternalLetStepSimulates context sourceFunction module hostEnv
      externals decl continuation targetValue sourceRuntime nextRuntime
      sourceEnv sourceValue targetStore nextStore targetLocals nextLocals
      resultIndex witness nextWitness) :
    StructuredWasmExecutes module hostEnv targetStore
      { targetLocals with values := tail }
      (targetValue ++ [.localSet resultIndex])
      (.fallthrough nextStore { nextLocals with values := tail }) := by
  apply structuredWasmExecutes_fallthrough_of_wp
  let Q : Wasm.Assertion Host := fun continuation =>
    continuation =
      .Fallthrough nextStore { nextLocals with values := tail }
  have finalWP :
      Wasm.wp module [] Q nextStore
        { nextLocals with values := tail } hostEnv :=
    (Wasm.wp_nil).2 rfl
  simpa [Q] using step.2.2.2 [] Q tail finalWP

/-- A straight-line external-call prefix advances beneath the same arbitrary
residual program and saved frame stack. -/
theorem ExternalLetStepSimulates.structuredFinitePath
    {context : Fir.Wasm.Context}
    {sourceFunction : Fir.Wasm.Function} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {externals : ExternalImpl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetValue targetRest : Wasm.Program}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {sourceValue : Value}
    {targetStore nextStore : Wasm.Store Host}
    {targetLocals nextLocals : Wasm.Locals} {resultIndex : Nat}
    {witness nextWitness : RefinementWitness} {tail : List Wasm.Value}
    {frames : List StructuredWasmFrame}
    (flat : StructuredWasmFlatProgram module
      (targetValue ++ [.localSet resultIndex]))
    (step : ExternalLetStepSimulates context sourceFunction module hostEnv
      externals decl continuation targetValue sourceRuntime nextRuntime
      sourceEnv sourceValue targetStore nextStore targetLocals nextLocals
      resultIndex witness nextWitness) :
    FinitePath (StructuredWasmStep module hostEnv)
      (targetValue ++ [Wasm.Instruction.localSet resultIndex]).length
      ⟨targetStore,
        .running { targetLocals with values := tail }
          (targetValue ++ .localSet resultIndex :: targetRest),
        frames⟩
      ⟨nextStore,
        .running { nextLocals with values := tail } targetRest,
        frames⟩ := by
  simpa [List.append_assoc] using
    flat.finitePathWithSuffix (suffix := targetRest) (frames := frames)
      step.structuredExecutes

/-- Both lazy-cache paths obtain their concrete execution from the proved
cache law, so hits and misses share the same structural reification boundary. -/
theorem LazyLetStepSimulates.structuredExecutes
    {path : LazyCachePath} {context : Fir.Wasm.Context}
    {sourceFunction : Fir.Wasm.Function} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {externals : ExternalImpl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetValue : Wasm.Program}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {sourceValue : Value}
    {targetStore nextStore : Wasm.Store Host}
    {targetLocals nextLocals : Wasm.Locals} {resultIndex : Nat}
    {witness nextWitness : RefinementWitness} {tail : List Wasm.Value}
    (step : LazyLetStepSimulates path context sourceFunction module hostEnv
      externals decl continuation targetValue sourceRuntime nextRuntime
      sourceEnv sourceValue targetStore nextStore targetLocals nextLocals
      resultIndex witness nextWitness) :
    StructuredWasmExecutes module hostEnv targetStore
      { targetLocals with values := tail }
      (targetValue ++ [.localSet resultIndex])
      (.fallthrough nextStore { nextLocals with values := tail }) := by
  apply structuredWasmExecutes_fallthrough_of_wp
  let Q : Wasm.Assertion Host := fun continuation =>
    continuation =
      .Fallthrough nextStore { nextLocals with values := tail }
  have finalWP :
      Wasm.wp module [] Q nextStore
        { nextLocals with values := tail } hostEnv :=
    (Wasm.wp_nil).2 rfl
  simpa [Q] using step.2.2.2 [] Q tail finalWP

/-- The concrete state relation is insensitive to the operand-stack suffix;
all environment bindings live in parameter or local slots. -/
theorem StateRelated.withValues
    {sourceFunction : Fir.Wasm.Function}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {targetStore : Wasm.Store Host} {targetLocals : Wasm.Locals}
    {witness : RefinementWitness}
    (related : StateRelated sourceFunction sourceRuntime sourceEnv targetStore
      targetLocals witness)
    (values : List Wasm.Value) :
    StateRelated sourceFunction sourceRuntime sourceEnv targetStore
      { targetLocals with values := values } witness := by
  refine ⟨related.1, related.2.1, ?_⟩
  intro fvar value sourceLookup
  obtain ⟨index, kind, physical, found, kindAt, targetLookup,
      valueRelated⟩ := related.2.2 sourceLookup
  exact ⟨index, kind, physical, found, kindAt, by simpa using targetLookup,
    valueRelated⟩

/-- Static reuse-capacity facts are interpreted through parameter/local slots
only, so changing the operand stack preserves their dynamic meaning. -/
theorem ReuseCapacityFactsRel.withValues
    {facts : ReuseCapacityFacts}
    {bindings : List (Lean.FVarId × AbiKind)} {sourceEnv : Env}
    {targetLocals : Wasm.Locals} {heap : MemoryState}
    {witness : RefinementWitness}
    (related :
      ReuseCapacityFactsRel facts bindings sourceEnv targetLocals heap witness)
    (values : List Wasm.Value) :
    ReuseCapacityFactsRel facts bindings sourceEnv
      { targetLocals with values } heap witness := by
  intro fvarId evidence found
  obtain ⟨index, kind, lane, semantic, sourceLookup, localFound, kindAt,
      targetLookup, valueRelated⟩ := related fvarId evidence found
  exact ⟨index, kind, lane, semantic, sourceLookup, localFound, kindAt,
    by simpa using targetLookup, valueRelated⟩

/-- The combined state-plus-capacity relation is operand-stack insensitive. -/
theorem ReuseCapacityStateRelated.withValues
    {facts : ReuseCapacityFacts} {sourceFunction : Fir.Wasm.Function}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {targetStore : Wasm.Store Host} {targetLocals : Wasm.Locals}
    {witness : RefinementWitness}
    (related :
      ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
        targetStore targetLocals witness)
    (values : List Wasm.Value) :
    ReuseCapacityStateRelated facts sourceFunction sourceRuntime sourceEnv
      targetStore { targetLocals with values } witness := by
  exact ⟨related.1.withValues values, related.2.withValues values⟩

/-- Local-frame shape is likewise independent of the operand stack. -/
theorem ConcreteLocalFrameAligned.withValues
    {sourceFunction : Fir.Wasm.Function}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {targetStore : Wasm.Store Host} {targetLocals : Wasm.Locals}
    {witness : RefinementWitness}
    (aligned : ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv
      targetStore targetLocals witness)
    (values : List Wasm.Value) :
    ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv targetStore
      { targetLocals with values := values } witness := by
  exact aligned

/-- The authoritative resource frame is also operand-stack insensitive. -/
theorem ConcreteReuseCapacityFrame.withValues
    {sourceFunction : Fir.Wasm.Function} {facts : ReuseCapacityFacts}
    {remainingBytes : Nat} {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {targetStore : Wasm.Store Host} {targetLocals : Wasm.Locals}
    {witness : RefinementWitness}
    (frame :
      ConcreteReuseCapacityFrame sourceFunction facts remainingBytes
        sourceRuntime sourceEnv targetStore targetLocals witness)
    (values : List Wasm.Value) :
    ConcreteReuseCapacityFrame sourceFunction facts remainingBytes
      sourceRuntime sourceEnv targetStore { targetLocals with values }
      witness := by
  rcases frame with ⟨related, ordinary, aligned, budget⟩
  exact ⟨related.withValues values, ordinary, aligned.withValues values,
    budget⟩

/-- The hereditary cache frame also depends only on parameter/local slots;
the operand stack may change while a structured call is staged or resumed. -/
theorem ConcreteReuseCapacityCacheFrame.withValues
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function} {externals : ExternalImpl}
    {facts : ReuseCapacityFacts} {remainingBytes : Nat}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {targetStore : Wasm.Store Host} {targetLocals : Wasm.Locals}
    {witness : RefinementWitness}
    (frame :
      ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals
        facts remainingBytes sourceRuntime sourceEnv targetStore targetLocals
        witness)
    (values : List Wasm.Value) :
    ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals facts
      remainingBytes sourceRuntime sourceEnv targetStore
      { targetLocals with values } witness := by
  rcases frame with
    ⟨⟨⟨⟨related, ordinary, aligned, budget⟩, integer, natural, scalar⟩,
      descriptors⟩, cache, closureTables⟩
  exact
    ⟨⟨⟨⟨related.withValues values, ordinary, aligned.withValues values,
      budget⟩, integer, natural, scalar⟩, descriptors⟩, cache, closureTables⟩

/-- Entry-relative transports are independent of the current operand stack. -/
theorem ReuseCapacityEntryRelativeFrame.withValues
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function} {externals : ExternalImpl}
    {entryRuntime currentRuntime : RuntimeState}
    {entryStore currentStore : Wasm.Store Host}
    {entryWitness currentWitness : RefinementWitness}
    {facts : ReuseCapacityFacts} {remainingBytes : Nat}
    {currentEnv : Env} {currentLocals : Wasm.Locals}
    (frame :
      ReuseCapacityEntryRelativeFrame
        (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals)
        entryRuntime entryStore entryWitness facts remainingBytes currentRuntime
        currentEnv currentStore currentLocals currentWitness)
    (values : List Wasm.Value) :
    ReuseCapacityEntryRelativeFrame
      (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals)
      entryRuntime entryStore entryWitness facts remainingBytes currentRuntime
      currentEnv currentStore { currentLocals with values } currentWitness :=
  ⟨frame.1.withValues values, frame.2⟩

/-- One direct source `let` whose generated prefix is straight-line advances
both machines to the recursively compiled continuation.  The target path is
derived from the runtime law's exact WP execution plus compiler-side flatness;
the caller supplies neither an execution trace nor a translation certificate.
The operand-stack suffix and both continuation stacks are preserved exactly. -/
theorem ConcreteStructuredCodeFocus.advance_flatLet
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {externals : ExternalImpl}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {sourceValue : Value}
    {targetStore nextStore : Wasm.Store Host}
    {targetLocals nextLocals : Wasm.Locals}
    {targetCode targetValue targetRest : Wasm.Program}
    {resultIndex : Nat} {witness nextWitness : RefinementWitness}
    {source : MachineState} {target : StructuredWasmState Host}
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels sourceRuntime sourceEnv (.let decl continuation) targetStore
      targetLocals targetCode witness source target)
    (targetCodeEq :
      targetCode = targetValue ++ .localSet resultIndex :: targetRest)
    (continuationAdapted :
      CodeAdapted context sourceModule sourceFunction labels continuation
        targetRest)
    (flat : StructuredWasmFlatProgram module
      (targetValue ++ [.localSet resultIndex]))
    (step : LetStepSimulates context sourceFunction module hostEnv decl
      targetValue sourceRuntime nextRuntime sourceEnv sourceValue targetStore
      nextStore targetLocals nextLocals resultIndex witness nextWitness)
    (nextAligned :
      ConcreteLocalFrameAligned sourceFunction nextRuntime
        (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals
        nextWitness) :
    ∃ sourceAfter targetAfter,
      executeStep externals source = .next sourceAfter ∧
      FinitePath (StructuredWasmStep module hostEnv)
        (targetValue ++ [Wasm.Instruction.localSet resultIndex]).length
        target targetAfter ∧
      ConcreteStructuredCodeFocus context sourceModule sourceFunction labels
        nextRuntime (bind sourceEnv decl.fvarId sourceValue) continuation
        nextStore { nextLocals with values := targetLocals.values } targetRest
        nextWitness sourceAfter targetAfter ∧
      sourceAfter.joins = source.joins ∧
      sourceAfter.frames = source.frames ∧
      targetAfter.frames = target.frames := by
  let resumedLocals : Wasm.Locals :=
    { nextLocals with values := targetLocals.values }
  let sourceAfter : MachineState :=
    { source with
      control := .code continuation
      env := bind sourceEnv decl.fvarId sourceValue
      runtime := nextRuntime }
  let targetAfter : StructuredWasmState Host :=
    { target with
      store := nextStore
      control := .running resumedLocals targetRest }
  refine ⟨sourceAfter, targetAfter, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases source with
      ⟨program, control, env, joins, frames, runtime⟩
    have programEq := related.sourceProgramEq
    change program = context.program at programEq
    subst program
    have controlEq := related.sourceControlEq
    change control = .code (.let decl continuation) at controlEq
    subst control
    have envEq := related.sourceEnvEq
    change env = sourceEnv at envEq
    subst env
    have runtimeEq := related.sourceRuntimeEq
    change runtime = sourceRuntime at runtimeEq
    subst runtime
    have evaluated :
        evalLetValue {
          program := context.program
          control := .code (.let decl continuation)
          env := sourceEnv
          joins := joins
          frames := frames
          runtime := sourceRuntime } decl =
          .ok (nextRuntime, .value sourceValue) := by
      have sourceStep := step.1
      unfold SourceLetResult at sourceStep
      cases decl.value <;> exact sourceStep
    simp [sourceAfter, executeStep, coreStep, evaluated]
  · rcases target with ⟨store, control, frames⟩
    have storeEq := related.targetStoreEq
    change store = targetStore at storeEq
    subst store
    have controlEq := related.targetControlEq
    rw [targetCodeEq] at controlEq
    change control =
      .running targetLocals
        (targetValue ++ .localSet resultIndex :: targetRest) at controlEq
    subst control
    simpa [resumedLocals, targetAfter] using
      step.structuredFinitePath (targetRest := targetRest)
        (tail := targetLocals.values) (frames := frames) flat
  · exact {
      sourceProgramEq := by simp [sourceAfter, related.sourceProgramEq]
      sourceControlEq := by simp [sourceAfter]
      sourceEnvEq := by simp [sourceAfter]
      sourceRuntimeEq := by simp [sourceAfter]
      targetStoreEq := by simp [targetAfter]
      targetControlEq := by simp [targetAfter, resumedLocals]
      adapted := continuationAdapted
      stateRelated := by
        simpa [resumedLocals] using
          (step.2.2.1.withValues targetLocals.values)
      frameAligned := by
        simpa [resumedLocals] using
          (nextAligned.withValues targetLocals.values) }
  · simp [sourceAfter]
  · simp [sourceAfter]
  · simp [targetAfter]

/-- Interpreter `ExecSteps` are the source transition system's exact finite
paths. -/
theorem ExecSteps.toFinitePath
    {externals : ExternalImpl} {count : Nat}
    {first last : MachineState}
    (steps : ExecSteps externals count first last) :
    FinitePath
      (fun before after => executeStep externals before = .next after)
      count first last := by
  induction steps with
  | refl state => exact .refl state
  | step head _tail ih =>
      simpa [Nat.succ_eq_add_one] using
        FinitePath.cons
          (step :=
            fun before after =>
              executeStep externals before = .next after)
          head ih

/-- One supported external-result `let` advances through the interpreter's
three-step request protocol and the exact flat imported-call target prefix.

The current recursive fragment has no join constructors, so its local source
focus carries the empty join environment.  Saved bind/call frames may still be
arbitrarily deep; the executable external prefix is lifted beneath that exact
frame suffix. -/
theorem ConcreteStructuredCodeFocus.advance_flatExternalLet
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {externals : ExternalImpl}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {sourceValue : Value}
    {targetStore nextStore : Wasm.Store Host}
    {targetLocals nextLocals : Wasm.Locals}
    {targetCode targetValue targetRest : Wasm.Program}
    {resultIndex : Nat} {witness nextWitness : RefinementWitness}
    {source : MachineState} {target : StructuredWasmState Host}
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels sourceRuntime sourceEnv (.let decl continuation) targetStore
      targetLocals targetCode witness source target)
    (sourceJoins : source.joins = [])
    (targetCodeEq :
      targetCode = targetValue ++ .localSet resultIndex :: targetRest)
    (continuationAdapted :
      CodeAdapted context sourceModule sourceFunction labels continuation
        targetRest)
    (flat : StructuredWasmFlatProgram module
      (targetValue ++ [.localSet resultIndex]))
    (step : ExternalLetStepSimulates context sourceFunction module hostEnv
      externals decl continuation targetValue sourceRuntime nextRuntime
      sourceEnv sourceValue targetStore nextStore targetLocals nextLocals
      resultIndex witness nextWitness)
    (nextAligned :
      ConcreteLocalFrameAligned sourceFunction nextRuntime
        (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals
        nextWitness) :
    ∃ sourceAfter targetAfter,
      FinitePath
          (fun before after => executeStep externals before = .next after)
          3 source sourceAfter ∧
      FinitePath (StructuredWasmStep module hostEnv)
        (targetValue ++ [Wasm.Instruction.localSet resultIndex]).length
        target targetAfter ∧
      ConcreteStructuredCodeFocus context sourceModule sourceFunction labels
        nextRuntime (bind sourceEnv decl.fvarId sourceValue) continuation
        nextStore { nextLocals with values := targetLocals.values } targetRest
        nextWitness sourceAfter targetAfter ∧
      sourceAfter.joins = [] ∧
      sourceAfter.frames = source.frames ∧
      targetAfter.frames = target.frames := by
  let resumedLocals : Wasm.Locals :=
    { nextLocals with values := targetLocals.values }
  let sourceAfter : MachineState :=
    { source with
      control := .code continuation
      env := bind sourceEnv decl.fvarId sourceValue
      runtime := nextRuntime }
  let targetAfter : StructuredWasmState Host :=
    { target with
      store := nextStore
      control := .running resumedLocals targetRest }
  refine ⟨sourceAfter, targetAfter, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply ExecSteps.toFinitePath
    rcases source with
      ⟨program, control, env, joins, frames, runtime⟩
    have programEq := related.sourceProgramEq
    change program = context.program at programEq
    subst program
    have controlEq := related.sourceControlEq
    change control = .code (.let decl continuation) at controlEq
    subst control
    have envEq := related.sourceEnvEq
    change env = sourceEnv at envEq
    subst env
    have runtimeEq := related.sourceRuntimeEq
    change runtime = sourceRuntime at runtimeEq
    subst runtime
    change joins = [] at sourceJoins
    subst joins
    have lifted :=
      FirTalos.Correctness.ExecSteps.withFrameSuffix
        (suffix := frames) step.1
    simpa [SourceExternalLetResult, withFrameSuffix, sourceAfter] using lifted
  · rcases target with ⟨store, control, frames⟩
    have storeEq := related.targetStoreEq
    change store = targetStore at storeEq
    subst store
    have controlEq := related.targetControlEq
    rw [targetCodeEq] at controlEq
    change control =
      .running targetLocals
        (targetValue ++ .localSet resultIndex :: targetRest) at controlEq
    subst control
    simpa [resumedLocals, targetAfter] using
      step.structuredFinitePath (targetRest := targetRest)
        (tail := targetLocals.values) (frames := frames) flat
  · exact {
      sourceProgramEq := by simp [sourceAfter, related.sourceProgramEq]
      sourceControlEq := by simp [sourceAfter]
      sourceEnvEq := by simp [sourceAfter]
      sourceRuntimeEq := by simp [sourceAfter]
      targetStoreEq := by simp [targetAfter]
      targetControlEq := by simp [targetAfter, resumedLocals]
      adapted := continuationAdapted
      stateRelated := by
        simpa [resumedLocals] using
          (step.2.2.1.withValues targetLocals.values)
      frameAligned := by
        simpa [resumedLocals] using
          (nextAligned.withValues targetLocals.values) }
  · simp [sourceAfter, sourceJoins]
  · simp [sourceAfter]
  · simp [targetAfter]

/-- Local compiler relation after a source return has yielded its semantic
value and the generated target has entered explicit return mode.  The
pre-return locals remain available for the later call-frame relation; the
physical result at the head of the returning stack is related at the exact
ABI kind selected by the compiler. -/
structure ConcreteStructuredYieldFocus
    (context : Fir.Wasm.Context)
    (sourceFunction : Fir.Wasm.Function)
    (sourceRuntime : RuntimeState)
    (sourceEnv : Env)
    (sourceValue : Value)
    (targetStore : Wasm.Store Host)
    (targetLocals : Wasm.Locals)
    (witness : RefinementWitness)
    (kind : AbiKind)
    (physical : Wasm.Value)
    (source : MachineState)
    (target : StructuredWasmState Host) : Prop where
  sourceProgramEq : source.program = context.program
  sourceControlEq : source.control = .yielded sourceValue
  sourceEnvEq : source.env = sourceEnv
  sourceRuntimeEq : source.runtime = sourceRuntime
  targetStoreEq : target.store = targetStore
  targetControlEq :
    target.control = .returning (physical :: targetLocals.values)
  stateRelated :
    StateRelated sourceFunction sourceRuntime sourceEnv targetStore targetLocals
      witness
  frameAligned :
    ConcreteLocalFrameAligned sourceFunction sourceRuntime sourceEnv targetStore
      targetLocals witness
  valueRelated : PhysicalValueRel witness kind physical sourceValue

theorem ConcreteStructuredYieldFocus.observes
    {context : Fir.Wasm.Context}
    {sourceFunction : Fir.Wasm.Function}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {sourceValue : Value}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {witness : RefinementWitness}
    {kind : AbiKind}
    {physical : Wasm.Value}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredYieldFocus context sourceFunction
      sourceRuntime sourceEnv sourceValue targetStore targetLocals witness kind
      physical source target) :
    ConcretePrefixObservationRel
      (sourcePrefixObservation source)
      (concretePrefixObservation target.store) := by
  refine ⟨witness, ?_, ?_⟩
  · change target.store.host.runtime.world = source.runtime.world
    rw [related.targetStoreEq, related.sourceRuntimeEq]
    exact related.stateRelated.1.world
  · change ConcreteTraceRel witness target.store.host.runtime.trace
      source.runtime.trace
    rw [related.targetStoreEq, related.sourceRuntimeEq]
    exact related.stateRelated.1.trace

/-- A source return is matched by the generated positive target path:
`local.get resultIndex` followed by the structured machine's explicit `ret`
transition.  Successful two-stage adaptation determines the index and ABI
kind, while `StateRelated.resolve` supplies the physical result and its
refinement proof. -/
theorem ConcreteStructuredCodeFocus.advance_return
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {externals : ExternalImpl}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {result : Lean.FVarId}
    {sourceValue : Value}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {witness : RefinementWitness}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (sourceLookup : lookup sourceEnv result = some sourceValue)
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels sourceRuntime sourceEnv (.return result) targetStore targetLocals
      targetCode witness source target) :
    ∃ kind physical sourceAfter targetAfter,
      Fir.Wasm.getLocal context result = .ok (.localGet result, kind) ∧
      executeStep externals source = .next sourceAfter ∧
      FinitePath (StructuredWasmStep module hostEnv) 2 target targetAfter ∧
      ConcreteStructuredYieldFocus context sourceFunction sourceRuntime
        sourceEnv sourceValue targetStore targetLocals witness kind physical
        sourceAfter targetAfter ∧
      sourceAfter.joins = source.joins ∧
      sourceAfter.frames = source.frames ∧
      targetAfter.frames = target.frames := by
  obtain ⟨kind, resultIndex, localCompiled, resultFound, kindAt,
      targetCodeEq⟩ :=
    CodeAdapted.return_eq localsAligned related.adapted
  obtain ⟨physical, targetLookup, valueRelated⟩ :=
    related.stateRelated.resolve sourceLookup resultFound kindAt
  subst targetCode
  let sourceAfter : MachineState :=
    { source with control := .yielded sourceValue }
  let targetAfterGet : StructuredWasmState Host :=
    { target with
      control := .running
        { targetLocals with
          values := physical :: targetLocals.values }
        [.ret] }
  let targetAfter : StructuredWasmState Host :=
    { target with
      control := .returning (physical :: targetLocals.values) }
  refine ⟨kind, physical, sourceAfter, targetAfter, localCompiled, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · rcases source with
      ⟨program, control, env, joins, frames, runtime⟩
    have controlEq := related.sourceControlEq
    change control = .code (.return result) at controlEq
    subst control
    have envEq := related.sourceEnvEq
    change env = sourceEnv at envEq
    subst env
    simp [sourceAfter, executeStep, coreStep, lookupValue, sourceLookup]
  · have getStep :
        StructuredWasmStep module hostEnv target targetAfterGet := by
      rcases target with ⟨store, control, frames⟩
      have storeEq := related.targetStoreEq
      change store = targetStore at storeEq
      subst store
      have controlEq := related.targetControlEq
      change control =
        .running targetLocals [.localGet resultIndex, .ret] at controlEq
      subst control
      apply StructuredWasmStep.atomic (fuel := 1)
      · trivial
      · simp only [Wasm.execOne.eq_def, targetLookup]
    have returnStep :
        StructuredWasmStep module hostEnv targetAfterGet targetAfter := by
      rcases target with ⟨store, control, frames⟩
      have storeEq := related.targetStoreEq
      change store = targetStore at storeEq
      subst store
      exact StructuredWasmStep.beginReturn
    exact .cons getStep (.cons returnStep (.refl targetAfter))
  · exact {
      sourceProgramEq := by simp [sourceAfter, related.sourceProgramEq]
      sourceControlEq := by simp [sourceAfter]
      sourceEnvEq := by simp [sourceAfter, related.sourceEnvEq]
      sourceRuntimeEq := by simp [sourceAfter, related.sourceRuntimeEq]
      targetStoreEq := by simp [targetAfter, related.targetStoreEq]
      targetControlEq := by simp [targetAfter]
      stateRelated := related.stateRelated
      frameAligned := related.frameAligned
      valueRelated }
  · simp [sourceAfter]
  · simp [sourceAfter]
  · simp [targetAfter]

/-- Simulation-facing return rule.  The generic advance theorem supplies a
successful source step, so this wrapper recovers the returned binding from
that step and invokes `advance_return`; clients do not provide an extra
source-execution certificate or lookup premise. -/
theorem ConcreteStructuredCodeFocus.advance_return_of_step
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {externals : ExternalImpl}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {result : Lean.FVarId}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {witness : RefinementWitness}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels sourceRuntime sourceEnv (.return result) targetStore targetLocals
      targetCode witness source target)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ sourceValue kind physical targetAfter,
      FinitePath (StructuredWasmStep module hostEnv) 2 target targetAfter ∧
      ConcreteStructuredYieldFocus context sourceFunction sourceRuntime
        sourceEnv sourceValue targetStore targetLocals witness kind physical
        sourceAfter targetAfter := by
  cases sourceLookup : lookup sourceEnv result with
  | none =>
      rcases source with
        ⟨program, control, env, joins, frames, runtime⟩
      have controlEq := related.sourceControlEq
      change control = .code (.return result) at controlEq
      subst control
      have envEq := related.sourceEnvEq
      change env = sourceEnv at envEq
      subst env
      simp [executeStep, coreStep, lookupValue, sourceLookup, fail] at sourceStep
  | some sourceValue =>
      obtain ⟨kind, physical, computedAfter, targetAfter, _localCompiled,
          computedStep, path, focus, _sourceFramesEq, _targetFramesEq⟩ :=
        related.advance_return localsAligned sourceLookup
      have afterEq : sourceAfter = computedAfter := by
        rw [sourceStep] at computedStep
        injection computedStep
      subst computedAfter
      exact ⟨sourceValue, kind, physical, targetAfter, path, focus⟩

/-- Partial correctness for an arbitrary finite direct-value spine in the
structured target machine.

The source evaluation supplies only source steps, admission, fact transfer,
and its allocation-cost index.  At every `let`, the uniform runtime theorem
constructs the exact concrete successor and the uniform compiler-shape law
proves that the production target prefix is flat; `advance_flatLet` then
reifies that exact execution as structured steps.  The return rule closes the
path at a related yielded source value and explicit target return state.

Both path lengths remain explicit.  This theorem therefore exposes the local
progress information needed by the later weak-simulation theorem while making
no termination claim for programs outside the supplied finite source
evaluation. -/
theorem
    ConcreteStructuredCodeFocus.reachesYield_of_reuseCapacityCodeEvaluates
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {externals : ExternalImpl}
    {DirectSupported :
      ReuseCapacityFacts → Lean.Compiler.LCNF.LetDecl .impure → Prop}
    {letCost : Lean.Compiler.LCNF.LetDecl .impure → Nat}
    {Invariant :
      ReuseCapacityFacts → Nat → RuntimeState → Env →
        Wasm.Store Host → Wasm.Locals → RefinementWitness → Prop}
    {facts resultFacts : ReuseCapacityFacts}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv resultEnv : Env}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {resultValue : Value} {requiredBytes : Nat}
    {targetStore : Wasm.Store Host} {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program} {witness : RefinementWitness}
    {source : MachineState} {target : StructuredWasmState Host}
    (evaluation :
      ReuseCapacityCodeEvaluates context DirectSupported letCost facts
        sourceRuntime sourceEnv sourceCode resultFacts resultRuntime resultEnv
        resultValue requiredBytes)
    (related :
      ConcreteStructuredCodeFocus context sourceModule sourceFunction labels
        sourceRuntime sourceEnv sourceCode targetStore targetLocals targetCode
        witness source target)
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (invariant :
      Invariant facts requiredBytes sourceRuntime sourceEnv targetStore
        targetLocals witness)
    (runtimeRefines :
      ReuseCapacityDirectLetRuntimeRefinesWithCost context sourceModule
        sourceFunction labels module hostEnv DirectSupported letCost Invariant)
    (targetFlat :
      ReuseCapacityDirectTargetFlat context sourceModule sourceFunction labels
        module DirectSupported)
    (invariantFrameAligned :
      ∀ {frameFacts frameBytes frameRuntime frameEnv frameStore frameLocals
          frameWitness},
        Invariant frameFacts frameBytes frameRuntime frameEnv frameStore
            frameLocals frameWitness →
          ConcreteLocalFrameAligned sourceFunction frameRuntime frameEnv
            frameStore frameLocals frameWitness)
    (invariantWithValues :
      ∀ {frameFacts frameBytes frameRuntime frameEnv frameStore frameLocals
          frameWitness},
        Invariant frameFacts frameBytes frameRuntime frameEnv frameStore
            frameLocals frameWitness →
          ∀ values,
            Invariant frameFacts frameBytes frameRuntime frameEnv frameStore
              { frameLocals with values } frameWitness) :
    ∃ sourceAfter targetAfter resultStore resultLocals resultWitness kind
        physical sourceCount targetCount,
      FinitePath
          (fun before after => executeStep externals before = .next after)
          sourceCount source sourceAfter ∧
        FinitePath (StructuredWasmStep module hostEnv) targetCount target
          targetAfter ∧
          ConcreteStructuredYieldFocus context sourceFunction resultRuntime
            resultEnv resultValue resultStore resultLocals resultWitness kind
            physical sourceAfter targetAfter ∧
        sourceAfter.frames = source.frames ∧
        targetAfter.frames = target.frames := by
  induction evaluation generalizing targetStore targetLocals targetCode witness
      source target with
  | ret sourceLookup =>
      obtain ⟨kind, physical, sourceAfter, targetAfter, _localCompiled,
          sourceStep, targetPath, focus, _sourceJoinsEq, sourceFramesEq,
          targetFramesEq⟩ :=
        related.advance_return localsAligned sourceLookup
      exact ⟨sourceAfter, targetAfter, targetStore, targetLocals, witness,
        kind, physical, 1, 2, .single sourceStep, targetPath, focus,
        sourceFramesEq, targetFramesEq⟩
  | @letValue facts decl letSourceRuntime letSourceEnv letNextRuntime
      letSourceValue nextFacts continuation resultFacts resultRuntime resultEnv
      resultValue continuationCost supported sourceStep transfer continued ih =>
      obtain ⟨valueCode, restCode, targetValue, targetRest, resultIndex,
          valueCompiled, restCompiled, valueAdapted, restAdapted, resultFound,
          targetCodeEq⟩ :=
        CodeAdapted.let_eq related.adapted
      have continuationAdapted :
          CodeAdapted context sourceModule sourceFunction labels continuation
            targetRest :=
        ⟨restCode, restCompiled, restAdapted⟩
      have stepFits :
          letCost decl ≤ letCost decl + continuationCost :=
        Nat.le_add_right _ _
      obtain ⟨nextStore, nextLocals, nextWitness, producedFacts, step,
          _externalsPreserved, _hostDescriptorsPreserved,
          _witnessDescriptorsPreserved, _transports, producedTransfer,
          nextInvariant⟩ :=
        runtimeRefines supported stepFits invariant sourceStep
          valueCompiled valueAdapted resultFound
      rw [transfer] at producedTransfer
      have factsEq := Option.some.inj producedTransfer
      subst producedFacts
      have continuationInvariant :
          Invariant nextFacts continuationCost letNextRuntime
            (bind letSourceEnv decl.fvarId letSourceValue) nextStore nextLocals
            nextWitness := by
        simpa using nextInvariant
      have flat :
          StructuredWasmFlatProgram module
            (targetValue ++ [.localSet resultIndex]) :=
        targetFlat supported valueCompiled valueAdapted
      obtain ⟨sourceMiddle, targetMiddle, firstSourceStep, targetPrefix,
          nextFocus, _firstSourceJoinsEq, firstSourceFramesEq,
          firstTargetFramesEq⟩ :=
        related.advance_flatLet targetCodeEq continuationAdapted flat step
          (invariantFrameAligned continuationInvariant)
      obtain ⟨sourceAfter, targetAfter, resultStore, resultLocals,
          resultWitness, kind, physical, sourceCount, targetCount, sourceTail,
          targetTail, yieldFocus, tailSourceFramesEq, tailTargetFramesEq⟩ :=
        ih nextFocus
          (invariantWithValues continuationInvariant targetLocals.values)
      exact ⟨sourceAfter, targetAfter, resultStore, resultLocals,
        resultWitness, kind, physical, 1 + sourceCount,
        (targetValue ++ [Wasm.Instruction.localSet resultIndex]).length +
          targetCount,
        (FinitePath.single
          (step := fun before after =>
            executeStep externals before = .next after)
          firstSourceStep).trans sourceTail,
        targetPrefix.trans targetTail, yieldFocus,
        tailSourceFramesEq.trans firstSourceFramesEq,
        tailTargetFramesEq.trans firstTargetFramesEq⟩

/-- Concrete endpoint for the complete current facts-indexed direct fragment.
It combines the production runtime theorem and compiler-derived shape theorem
with the generic structured spine, leaving only the source evaluation and the
ordinary initial resource relation as dynamic premises. -/
theorem ConcreteSupportedFunction.reachesYield_reuseBudgetedDirect
    {program : Fir.LeanIR.ImpureProgram} {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule} {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context sourceCode sourceModule
        sourceFunction targetModule hosts)
    {labels : List Lean.FVarId} {externals : ExternalImpl}
    {facts resultFacts : ReuseCapacityFacts}
    {sourceRuntime resultRuntime : RuntimeState}
    {sourceEnv resultEnv : Env}
    {code : Lean.Compiler.LCNF.Code .impure}
    {resultValue : Value} {requiredBytes : Nat}
    {targetStore : Wasm.Store Host} {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program} {witness : RefinementWitness}
    {source : MachineState} {target : StructuredWasmState Host}
    (evaluation :
      ReuseCapacityCodeEvaluates context (ReuseBudgetedDirectSupported context)
        directLetAllocationCost facts sourceRuntime sourceEnv code resultFacts
        resultRuntime resultEnv resultValue requiredBytes)
    (related :
      ConcreteStructuredCodeFocus context sourceModule sourceFunction labels
        sourceRuntime sourceEnv code targetStore targetLocals targetCode witness
        source target)
    (invariant :
      ConcreteReuseCapacityFrame sourceFunction facts requiredBytes
        sourceRuntime sourceEnv targetStore targetLocals witness) :
    ∃ sourceAfter targetAfter resultStore resultLocals resultWitness kind
        physical sourceCount targetCount,
      FinitePath
          (fun before after => executeStep externals before = .next after)
          sourceCount source sourceAfter ∧
        FinitePath
            (StructuredWasmStep targetModule.wasmModule hosts.env)
            targetCount target targetAfter ∧
          ConcreteStructuredYieldFocus context sourceFunction resultRuntime
            resultEnv resultValue resultStore resultLocals resultWitness kind
            physical sourceAfter targetAfter ∧
        sourceAfter.frames = source.frames ∧
        targetAfter.frames = target.frames := by
  exact
    ConcreteStructuredCodeFocus.reachesYield_of_reuseCapacityCodeEvaluates
      evaluation related spec.localsAligned invariant
      spec.reuseCapacityDirectLetRuntimeRefinesWithCost_reuseBudgetedDirect
      spec.reuseCapacityDirectTargetFlat_reuseBudgetedDirect
      (by
        intro frameFacts frameBytes frameRuntime frameEnv frameStore frameLocals
          frameWitness frame
        exact frame.2.2.1)
      (by
        intro frameFacts frameBytes frameRuntime frameEnv frameStore frameLocals
          frameWitness frame values
        exact frame.withValues values)

/-- Changing only the operand stack commutes with a successful checked local
write.  The structured call-frame proof uses this to expose the returned value
as a stack head, execute `local.set`, and restore the caller's saved operand
tail. -/
theorem locals_set?_with_values
    {locals updated : Wasm.Locals}
    {index : Nat}
    {value : Wasm.Value}
    (values : List Wasm.Value)
    (set : locals.set? index value = some updated) :
    ({ locals with values }.set? index value) =
      some { updated with values } := by
  unfold Wasm.Locals.set? at set
  split at set
  · rename_i inParams
    cases set
    simp [Wasm.Locals.set?, inParams]
  · rename_i notInParams
    split at set
    · rename_i inLocals
      cases set
      simp [Wasm.Locals.set?, notInParams, inLocals]
    · contradiction

/-- The compiler-characterized argument prefix has an exact structured-machine
execution: every generated local read or erased zero takes one atomic target
step, the source-order physical arguments are left in Wasm stack order, and
the caller operand tail, store, and continuation frames are preserved. -/
theorem ConstructorArgsReady.finitePath
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {argumentCode : Wasm.Program} {physicalArgs : List Wasm.Value}
    {store : Wasm.Store Host} {locals : Wasm.Locals}
    {rest : Wasm.Program} {frames : List StructuredWasmFrame}
    (tail : List Wasm.Value)
    (ready : ConstructorArgsReady locals argumentCode physicalArgs) :
    FinitePath (StructuredWasmStep module hostEnv) argumentCode.length
      ⟨store, .running { locals with values := tail }
        (argumentCode ++ rest), frames⟩
      ⟨store, .running
        { locals with values := physicalArgs.reverse ++ tail } rest, frames⟩ := by
  induction ready generalizing tail with
  | nil =>
      exact .refl _
  | @localGet index physical targetArgs remainingPhysical found ready ih =>
      have foundWithStack :
          ({ locals with values := tail } : Wasm.Locals).get index =
            some physical := by
        simpa [Wasm.Locals.get] using found
      have head :
          StructuredWasmStep module hostEnv
            ⟨store, .running { locals with values := tail }
              (.localGet index :: targetArgs ++ rest), frames⟩
            ⟨store, .running { locals with values := physical :: tail }
              (targetArgs ++ rest), frames⟩ := by
        apply StructuredWasmStep.atomic (fuel := 1)
        · trivial
        · simp only [Wasm.execOne.eq_def, foundWithStack]
      simpa [List.reverse_cons, List.append_assoc] using
        FinitePath.cons head (ih (tail := physical :: tail))
  | @erased targetArgs remainingPhysical ready ih =>
      have head :
          StructuredWasmStep module hostEnv
            ⟨store, .running { locals with values := tail }
              (.const 0 :: targetArgs ++ rest), frames⟩
            ⟨store, .running { locals with values := .i32 0 :: tail }
              (targetArgs ++ rest), frames⟩ := by
        apply StructuredWasmStep.atomic (fuel := 1)
        · trivial
        · simp only [Wasm.execOne.eq_def]
      simpa [List.reverse_cons, List.append_assoc] using
        FinitePath.cons head (ih (tail := .i32 0 :: tail))

/-- Intermediate relation after the source has staged an internal named call
and the generated target has evaluated its argument prefix.  Both machines
are poised to enter the callee.  The relation retains the caller continuation
and local refinement that the call frame must protect, while the generated
callee row and related physical arguments determine the entry state without a
translation certificate or assumed target execution. -/
structure ConcreteStructuredDirectCallReadyFocus
    (callerContext calleeContext : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (callerFunction calleeFunction : Fir.Wasm.Function)
    (targetModule : AdaptedModule)
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {callerEnv : Env}
    (site : DirectInternalCallSite callerContext decl callerEnv)
    (row : ConcreteGeneratedInternalDeclaration callerContext.program
      site.sourceDeclaration calleeContext site.calleeCode sourceModule
      calleeFunction targetModule)
    (labels : List Lean.FVarId)
    (sourceRuntime : RuntimeState)
    (continuation : Lean.Compiler.LCNF.Code .impure)
    (callerJoins : JoinEnv)
    (sourceFrames : List Frame)
    (targetStore : Wasm.Store Host)
    (callerLocals : Wasm.Locals)
    (callerRemainder : List Wasm.Value)
    (targetRest : Wasm.Program)
    (targetFrames : List StructuredWasmFrame)
    (witness : RefinementWitness)
    (physicalArgs : List Wasm.Value)
    (resultIndex : Nat)
    (source : MachineState)
    (target : StructuredWasmState Host) : Prop where
  sourceProgramEq : source.program = callerContext.program
  sourceControlEq :
    source.control = .invokeName site.declaration site.semanticArgs
  sourceEnvEq : source.env = callerEnv
  sourceRuntimeEq : source.runtime = sourceRuntime
  sourceJoinsEq : source.joins = callerJoins
  sourceFramesEq :
    source.frames =
      .bind decl.fvarId continuation callerEnv callerJoins :: sourceFrames
  targetStoreEq : target.store = targetStore
  targetControlEq :
    target.control = .running
      { callerLocals with
        values := physicalArgs.reverse ++ callerRemainder }
      (.call row.targetFunctionIndex ::
        .localSet resultIndex :: targetRest)
  targetFramesEq : target.frames = targetFrames
  continuationAdapted :
    CodeAdapted callerContext sourceModule callerFunction labels continuation
      targetRest
  callerStateRelated :
    StateRelated callerFunction sourceRuntime callerEnv targetStore callerLocals
      witness
  callerFrameAligned :
    ConcreteLocalFrameAligned callerFunction sourceRuntime callerEnv targetStore
      callerLocals witness
  resultFound :
    findFVar? (functionBindings callerFunction) decl.fvarId = some resultIndex
  resultKindAt :
    (functionBindings callerFunction)[resultIndex]?.map Prod.snd =
      some site.resultKind
  argumentsRelated :
    ConstructorArgumentsRelated witness site.argumentKinds.toList physicalArgs
      site.semanticArgs.toList

theorem ConcreteStructuredDirectCallReadyFocus.observes
    {callerContext calleeContext : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction calleeFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {callerEnv : Env}
    {site : DirectInternalCallSite callerContext decl callerEnv}
    {row : ConcreteGeneratedInternalDeclaration callerContext.program
      site.sourceDeclaration calleeContext site.calleeCode sourceModule
      calleeFunction targetModule}
    {labels : List Lean.FVarId}
    {sourceRuntime : RuntimeState}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {callerJoins : JoinEnv}
    {sourceFrames : List Frame}
    {targetStore : Wasm.Store Host}
    {callerLocals : Wasm.Locals}
    {callerRemainder : List Wasm.Value}
    {targetRest : Wasm.Program}
    {targetFrames : List StructuredWasmFrame}
    {witness : RefinementWitness}
    {physicalArgs : List Wasm.Value}
    {resultIndex : Nat}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredDirectCallReadyFocus callerContext
      calleeContext sourceModule callerFunction calleeFunction targetModule
      site row labels sourceRuntime continuation callerJoins sourceFrames
      targetStore callerLocals callerRemainder targetRest targetFrames witness
      physicalArgs resultIndex source target) :
    ConcretePrefixObservationRel
      (sourcePrefixObservation source)
      (concretePrefixObservation target.store) := by
  refine ⟨witness, ?_, ?_⟩
  · change target.store.host.runtime.world = source.runtime.world
    rw [related.targetStoreEq, related.sourceRuntimeEq]
    exact related.callerStateRelated.1.world
  · change ConcreteTraceRel witness target.store.host.runtime.trace
      source.runtime.trace
    rw [related.targetStoreEq, related.sourceRuntimeEq]
    exact related.callerStateRelated.1.trace

/-- The first direct-call simulation step is entirely compiler-derived.  The
source stages the named invocation under its bind frame while the target
executes the exact local-read/erased-zero argument prefix recovered from
two-stage adaptation.  Both sides finish poised at their respective call
entry transitions, with the caller continuation relation protected by
`ConcreteStructuredDirectCallReadyFocus`. -/
theorem ConcreteStructuredCodeFocus.advance_directCall_stage
    {callerContext calleeContext : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction calleeFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hostEnv : Wasm.HostEnv Host}
    {externals : ExternalImpl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {callerEnv : Env}
    (site : DirectInternalCallSite callerContext decl callerEnv)
    (row : ConcreteGeneratedInternalDeclaration callerContext.program
      site.sourceDeclaration calleeContext site.calleeCode sourceModule
      calleeFunction targetModule)
    {labels : List Lean.FVarId}
    {sourceRuntime : RuntimeState}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {witness : RefinementWitness}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (localsAligned : LocalLayoutAligned callerContext callerFunction)
    (related : ConcreteStructuredCodeFocus callerContext sourceModule
      callerFunction labels sourceRuntime callerEnv (.let decl continuation)
      targetStore targetLocals targetCode witness source target) :
    ∃ physicalArgs resultIndex,
      ∃ targetArguments targetRest : Wasm.Program,
      ∃ sourceAfter targetAfter,
      executeStep externals source = .next sourceAfter ∧
      FinitePath (StructuredWasmStep targetModule.wasmModule hostEnv)
        targetArguments.length target targetAfter ∧
      ConcreteStructuredDirectCallReadyFocus callerContext calleeContext
        sourceModule callerFunction calleeFunction targetModule site row labels
        sourceRuntime continuation source.joins source.frames targetStore
        targetLocals targetLocals.values targetRest target.frames witness
        physicalArgs resultIndex sourceAfter targetAfter := by
  obtain ⟨valueCode, restCode, targetValue, targetRest, resultIndex,
      valueCompiled, restCompiled, valueAdapted, restAdapted, resultFound,
      targetCodeEq⟩ :=
    CodeAdapted.let_eq related.adapted
  have expectedCompiled :
      Fir.Wasm.compileLetValue callerContext decl =
        .ok (site.argumentCode ++
          [.call (.declaration site.declaration)]) := by
    simp [Fir.Wasm.compileLetValue, Fir.Wasm.letValueKind, site.valueEq,
      site.kindEq, site.argumentsCompiled, site.declarationFound,
      site.nonCached, Bind.bind, Except.bind, pure, Except.pure]
  have valueCodeEq :
      valueCode =
        site.argumentCode ++ [.call (.declaration site.declaration)] := by
    rw [expectedCompiled] at valueCompiled
    exact (Except.ok.inj valueCompiled).symm
  subst valueCode
  obtain ⟨targetArguments, functionIndex, argumentsAdapted, callFound,
      targetValueEq⟩ :=
    instructions_append_declaration_call_eq valueAdapted
  subst targetValue
  have declarationNameEq :
      site.sourceDeclaration.name = site.declaration := by
    have selected :=
      (Array.find?_eq_some_iff_getElem.mp site.declarationFound).1
    simpa [Fir.LeanIR.Program.findDecl?] using selected
  have exactCallIndex :
      callIndex? sourceModule (.declaration site.declaration) =
        some row.targetFunctionIndex := by
    simpa [declarationNameEq] using row.callIndexEq
  rw [exactCallIndex] at callFound
  have functionIndexEq : row.targetFunctionIndex = functionIndex :=
    Option.some.inj callFound
  subst functionIndex
  obtain ⟨physicalArgs, argumentsReady, _physicalLength,
      argumentsRelated⟩ :=
    constructorArgsReady_of_compileArgs localsAligned site.argumentsCompiled
      argumentsAdapted site.argumentsEvaluated related.stateRelated
  obtain ⟨alignedResultIndex, alignedResultFound, resultKindAt⟩ :=
    localsAligned site.resultCompiled
  rw [resultFound] at alignedResultFound
  have resultIndexEq : alignedResultIndex = resultIndex :=
    (Option.some.inj alignedResultFound).symm
  subst alignedResultIndex
  have continuationAdapted :
      CodeAdapted callerContext sourceModule callerFunction labels continuation
        targetRest :=
    ⟨restCode, restCompiled, restAdapted⟩
  subst targetCode
  let sourceAfter : MachineState :=
    { source with
      control := .invokeName site.declaration site.semanticArgs
      frames :=
        .bind decl.fvarId continuation source.env source.joins :: source.frames }
  let targetAfter : StructuredWasmState Host :=
    { target with
      control := .running
        { targetLocals with
          values := physicalArgs.reverse ++ targetLocals.values }
        (.call row.targetFunctionIndex ::
          .localSet resultIndex :: targetRest) }
  refine ⟨physicalArgs, resultIndex, targetArguments, targetRest, sourceAfter,
    targetAfter, ?_, ?_, ?_⟩
  · rcases source with
      ⟨program, control, env, joins, frames, runtime⟩
    have controlEq := related.sourceControlEq
    change control = .code (.let decl continuation) at controlEq
    subst control
    have envEq := related.sourceEnvEq
    change env = callerEnv at envEq
    subst env
    have runtimeEq := related.sourceRuntimeEq
    change runtime = sourceRuntime at runtimeEq
    subst runtime
    simp [sourceAfter, executeStep, coreStep, evalLetValue, site.valueEq,
      site.argumentsEvaluated, pushBindFrame]
  · rcases target with ⟨store, control, frames⟩
    have storeEq := related.targetStoreEq
    change store = targetStore at storeEq
    subst store
    have controlEq := related.targetControlEq
    change control = .running targetLocals
      ((targetArguments ++ [.call row.targetFunctionIndex]) ++
        .localSet resultIndex :: targetRest) at controlEq
    subst control
    simpa [targetAfter, List.append_assoc] using
      (argumentsReady.finitePath
        (module := targetModule.wasmModule) (hostEnv := hostEnv)
        (store := targetStore)
        (rest := .call row.targetFunctionIndex ::
          .localSet resultIndex :: targetRest)
        (frames := frames) targetLocals.values)
  · exact {
      sourceProgramEq := by simp [sourceAfter, related.sourceProgramEq]
      sourceControlEq := by simp [sourceAfter]
      sourceEnvEq := by simp [sourceAfter, related.sourceEnvEq]
      sourceRuntimeEq := by simp [sourceAfter, related.sourceRuntimeEq]
      sourceJoinsEq := by simp [sourceAfter]
      sourceFramesEq := by simp [sourceAfter, related.sourceEnvEq]
      targetStoreEq := by simp [targetAfter, related.targetStoreEq]
      targetControlEq := by simp [targetAfter]
      targetFramesEq := by simp [targetAfter]
      continuationAdapted
      callerStateRelated := related.stateRelated
      callerFrameAligned := related.frameAligned
      resultFound
      resultKindAt
      argumentsRelated }

/-- Production argument compilation preserves the source/ABI row length. -/
theorem ConstructorArgsCompiled.argumentLength
    {context : Fir.Wasm.Context}
    {args : List (Lean.Compiler.LCNF.Arg .impure)}
    {argumentCode : List Fir.Wasm.Instruction}
    {kinds : List AbiKind}
    (compiled : ConstructorArgsCompiled context args argumentCode kinds) :
    args.length = kinds.length := by
  induction compiled with
  | nil => rfl
  | erased _ ih => simp [ih]
  | fvar _ _ ih => simp [ih]

/-- The generated callee locals selected by the direct-call argument relation
have exactly the source symbolic parameter/local shape.  This is the local
frame component needed when the structured machine enters the callee. -/
theorem ConcreteGeneratedInternalDeclaration.entryFrameAligned
    {callerContext calleeContext : Fir.Wasm.Context}
    {callerDecl : Lean.Compiler.LCNF.LetDecl .impure}
    {callerEnv : Env}
    {sourceModule : Fir.Wasm.Module}
    {calleeFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    (site : DirectInternalCallSite callerContext callerDecl callerEnv)
    (row : ConcreteGeneratedInternalDeclaration callerContext.program
      site.sourceDeclaration calleeContext site.calleeCode sourceModule
      calleeFunction targetModule)
    {sourceRuntime : RuntimeState}
    {targetStore : Wasm.Store Host}
    {witness : RefinementWitness}
    {physicalArgs : List Wasm.Value}
    (argumentsRelated :
      ConstructorArgumentsRelated witness site.argumentKinds.toList
        physicalArgs site.semanticArgs.toList) :
    ConcreteLocalFrameAligned calleeFunction sourceRuntime site.calleeEnv
      targetStore (row.targetFunction.toLocals physicalArgs) witness := by
  have classifiedSize := row.parameterKindsSize site.parametersKnown
  have parameterBindings := row.sourceParameterBindings site.parametersKnown
  have sourceParameterSize :
      calleeFunction.params.size = site.parameterKinds.size := by
    have lengths := congrArg List.length parameterBindings
    simp only [Array.length_toList, List.length_map, List.length_zip] at lengths
    rw [← classifiedSize] at lengths
    simpa using lengths
  have parameterRelated :=
    argumentsRelated.ofKindsRefine site.argumentsRefine
  have physicalSize : physicalArgs.length = site.parameterKinds.size := by
    simpa using parameterRelated.physicalLength
  have parameterFrameSize :
      (row.targetFunction.toLocals physicalArgs).params.length =
        calleeFunction.params.size := by
    simpa [Wasm.Function.toLocals] using
      physicalSize.trans sourceParameterSize.symm
  have signature :=
    FirTalos.Correctness.function_preserves_signature row.functionAdapted
  have localFrameSize :
      (row.targetFunction.toLocals physicalArgs).locals.length =
        calleeFunction.locals.size := by
    simp [Wasm.Function.toLocals, signature.2.1]
  exact ⟨parameterFrameSize, localFrameSize⟩

/-- Relation immediately after both machines enter a generated direct callee.
The local code focus is now indexed by the callee's real symbolic and adapted
function rows.  The separate caller fields record exactly the bind/call frame
that must be transported across callee effects before the accepted return
unwinding theorem can be applied. -/
structure ConcreteStructuredDirectCallEntryFocus
    (callerContext calleeContext : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (callerFunction calleeFunction : Fir.Wasm.Function)
    (targetModule : AdaptedModule)
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {callerEnv : Env}
    (site : DirectInternalCallSite callerContext decl callerEnv)
    (row : ConcreteGeneratedInternalDeclaration callerContext.program
      site.sourceDeclaration calleeContext site.calleeCode sourceModule
      calleeFunction targetModule)
    (labels : List Lean.FVarId)
    (sourceRuntime : RuntimeState)
    (continuation : Lean.Compiler.LCNF.Code .impure)
    (callerJoins : JoinEnv)
    (sourceFrames : List Frame)
    (targetStore : Wasm.Store Host)
    (callerLocals : Wasm.Locals)
    (callerRemainder : List Wasm.Value)
    (targetRest : Wasm.Program)
    (targetFrames : List StructuredWasmFrame)
    (witness : RefinementWitness)
    (physicalArgs : List Wasm.Value)
    (resultIndex : Nat)
    (source : MachineState)
    (target : StructuredWasmState Host) : Prop where
  calleeFocus :
    ConcreteStructuredCodeFocus calleeContext sourceModule calleeFunction []
      sourceRuntime site.calleeEnv site.calleeCode targetStore
      (row.targetFunction.toLocals physicalArgs) row.targetFunction.body witness
      source target
  sourceJoinsEq : source.joins = []
  sourceFramesEq :
    source.frames =
      .bind decl.fvarId continuation callerEnv callerJoins :: sourceFrames
  targetFramesEq :
    target.frames =
      .call 1 callerRemainder callerLocals
          (.localSet resultIndex :: targetRest) :: targetFrames
  continuationAdapted :
    CodeAdapted callerContext sourceModule callerFunction labels continuation
      targetRest
  callerStateRelated :
    StateRelated callerFunction sourceRuntime callerEnv targetStore callerLocals
      witness
  callerFrameAligned :
    ConcreteLocalFrameAligned callerFunction sourceRuntime callerEnv targetStore
      callerLocals witness
  resultFound :
    findFVar? (functionBindings callerFunction) decl.fvarId = some resultIndex
  resultKindAt :
    (functionBindings callerFunction)[resultIndex]?.map Prod.snd =
      some site.resultKind
  argumentsRelated :
    ConstructorArgumentsRelated witness site.argumentKinds.toList physicalArgs
      site.semanticArgs.toList

theorem ConcreteStructuredDirectCallEntryFocus.observes
    {callerContext calleeContext : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction calleeFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {callerEnv : Env}
    {site : DirectInternalCallSite callerContext decl callerEnv}
    {row : ConcreteGeneratedInternalDeclaration callerContext.program
      site.sourceDeclaration calleeContext site.calleeCode sourceModule
      calleeFunction targetModule}
    {labels : List Lean.FVarId}
    {sourceRuntime : RuntimeState}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {callerJoins : JoinEnv}
    {sourceFrames : List Frame}
    {targetStore : Wasm.Store Host}
    {callerLocals : Wasm.Locals}
    {callerRemainder : List Wasm.Value}
    {targetRest : Wasm.Program}
    {targetFrames : List StructuredWasmFrame}
    {witness : RefinementWitness}
    {physicalArgs : List Wasm.Value}
    {resultIndex : Nat}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredDirectCallEntryFocus callerContext
      calleeContext sourceModule callerFunction calleeFunction targetModule
      site row labels sourceRuntime continuation callerJoins sourceFrames
      targetStore callerLocals callerRemainder targetRest targetFrames witness
      physicalArgs resultIndex source target) :
    ConcretePrefixObservationRel
      (sourcePrefixObservation source)
      (concretePrefixObservation target.store) :=
  related.calleeFocus.observes

/-- The poised source and target call states enter the same generated callee.
The source dispatcher takes one step; the structured target takes its real
`enterCall` step.  The conclusion contains the callee code focus plus the
exact saved caller frames.  In particular, the target call frame retains the
post-argument operand stack prescribed by Wasm, while its semantic/local
invariant is transported without changing the store or witness. -/
theorem ConcreteStructuredDirectCallReadyFocus.advance_enter
    {callerContext calleeContext : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction calleeFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hostEnv : Wasm.HostEnv Host}
    {externals : ExternalImpl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {callerEnv : Env}
    {site : DirectInternalCallSite callerContext decl callerEnv}
    {row : ConcreteGeneratedInternalDeclaration callerContext.program
      site.sourceDeclaration calleeContext site.calleeCode sourceModule
      calleeFunction targetModule}
    {labels : List Lean.FVarId}
    {sourceRuntime : RuntimeState}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {callerJoins : JoinEnv}
    {sourceFrames : List Frame}
    {targetStore : Wasm.Store Host}
    {callerLocals : Wasm.Locals}
    {callerRemainder : List Wasm.Value}
    {targetRest : Wasm.Program}
    {targetFrames : List StructuredWasmFrame}
    {witness : RefinementWitness}
    {physicalArgs : List Wasm.Value}
    {resultIndex : Nat}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredDirectCallReadyFocus callerContext
      calleeContext sourceModule callerFunction calleeFunction targetModule
      site row labels sourceRuntime continuation callerJoins sourceFrames
      targetStore callerLocals callerRemainder targetRest targetFrames witness
      physicalArgs resultIndex source target) :
    ∃ sourceAfter targetAfter storedCallerLocals,
      storedCallerLocals =
          { callerLocals with
            values := physicalArgs.reverse ++ callerRemainder } ∧
      executeStep externals source = .next sourceAfter ∧
      FinitePath (StructuredWasmStep targetModule.wasmModule hostEnv) 1 target
        targetAfter ∧
      ConcreteStructuredDirectCallEntryFocus callerContext calleeContext
        sourceModule callerFunction calleeFunction targetModule site row labels
        sourceRuntime continuation callerJoins sourceFrames targetStore
        storedCallerLocals callerRemainder targetRest targetFrames witness
        physicalArgs resultIndex sourceAfter targetAfter := by
  have argumentCompilation :=
    ConstructorArgsCompiled.ofCompileArgs site.argumentsCompiled
  have argumentSize : site.semanticArgs.size = site.args.size := by
    have semanticLength := related.argumentsRelated.semanticLength
    have compiledLength := argumentCompilation.argumentLength
    simpa using semanticLength.trans compiledLength.symm
  have parameterSize :
      site.semanticArgs.size = site.sourceDeclaration.params.size := by
    by_contra different
    have sizeTest :
        (site.sourceDeclaration.params.size == site.semanticArgs.size) =
          false :=
      beq_eq_false_iff_ne.mpr (Ne.symm different)
    have bound := site.parametersBound
    unfold bindParams at bound
    simp [sizeTest] at bound
  have callArgs :
      site.semanticArgs.extract 0 site.sourceDeclaration.params.size =
        site.semanticArgs := by
    simp [← parameterSize]
  have argumentsNonempty : site.semanticArgs.isEmpty = false := by
    simpa [Array.isEmpty, ← argumentSize, ← parameterSize] using site.nonCached
  have parameterCount :
      physicalArgs.reverse.length = row.targetFunction.numParams :=
    row.targetParameterCount site related.argumentsRelated
  have takeParameters :
      (physicalArgs.reverse ++ callerRemainder).take
          row.targetFunction.numParams =
        physicalArgs.reverse := by
    rw [← parameterCount]
    simp
  have dropParameters :
      (physicalArgs.reverse ++ callerRemainder).drop
          row.targetFunction.numParams =
        callerRemainder := by
    rw [← parameterCount]
    simp
  have calleeLocalsRelated :
      EnvLocalsRelated witness (functionBindings calleeFunction)
        site.calleeEnv (row.targetFunction.toLocals physicalArgs) :=
    row.entryEnvLocalsRelatedOfArguments site related.argumentsRelated
  have calleeStateRelated :
      StateRelated calleeFunction sourceRuntime site.calleeEnv targetStore
        (row.targetFunction.toLocals physicalArgs) witness :=
    ⟨related.callerStateRelated.1,
      related.callerStateRelated.2.1, calleeLocalsRelated⟩
  have calleeFrameAligned :
      ConcreteLocalFrameAligned calleeFunction sourceRuntime site.calleeEnv
        targetStore (row.targetFunction.toLocals physicalArgs) witness :=
    row.entryFrameAligned site related.argumentsRelated
  let storedCallerLocals : Wasm.Locals :=
    { callerLocals with
      values := physicalArgs.reverse ++ callerRemainder }
  have storedCallerStateRelated :
      StateRelated callerFunction sourceRuntime callerEnv targetStore
        storedCallerLocals witness := by
    simpa [storedCallerLocals, StateRelated, EnvLocalsRelated,
      Wasm.Locals.get] using related.callerStateRelated
  have storedCallerFrameAligned :
      ConcreteLocalFrameAligned callerFunction sourceRuntime callerEnv
        targetStore storedCallerLocals witness := by
    simpa [storedCallerLocals, ConcreteLocalFrameAligned] using
      related.callerFrameAligned
  let sourceAfter : MachineState :=
    { source with
      control := .code site.calleeCode
      env := site.calleeEnv
      joins := [] }
  let targetAfter : StructuredWasmState Host :=
    { target with
      control := .running (row.targetFunction.toLocals physicalArgs)
        row.targetFunction.body
      frames :=
        .call 1 callerRemainder storedCallerLocals
            (.localSet resultIndex :: targetRest) :: targetFrames }
  refine ⟨sourceAfter, targetAfter, storedCallerLocals, rfl, ?_, ?_, ?_⟩
  · rcases source with
      ⟨program, control, env, joins, frames, runtime⟩
    have programEq := related.sourceProgramEq
    change program = callerContext.program at programEq
    subst program
    have controlEq := related.sourceControlEq
    change control = .invokeName site.declaration site.semanticArgs at controlEq
    subst control
    have envEq := related.sourceEnvEq
    change env = callerEnv at envEq
    subst env
    have runtimeEq := related.sourceRuntimeEq
    change runtime = sourceRuntime at runtimeEq
    subst runtime
    have joinsEq := related.sourceJoinsEq
    change joins = callerJoins at joinsEq
    subst joins
    have framesEq := related.sourceFramesEq
    change frames = _ at framesEq
    subst frames
    simp [sourceAfter, executeStep, coreStep, invokeDecl,
      site.declarationFound, argumentsNonempty, parameterSize, callArgs,
      site.parametersBound, site.bodyEq]
  · have entered :
        StructuredWasmStep targetModule.wasmModule hostEnv target
          targetAfter := by
      rcases target with ⟨store, control, frames⟩
      have storeEq := related.targetStoreEq
      change store = targetStore at storeEq
      subst store
      have controlEq := related.targetControlEq
      change control = .running storedCallerLocals
        (.call row.targetFunctionIndex ::
          .localSet resultIndex :: targetRest) at controlEq
      subst control
      have framesEq := related.targetFramesEq
      change frames = targetFrames at framesEq
      subst frames
      simpa only [targetAfter, storedCallerLocals, takeParameters,
        dropParameters, row.singleResult, List.reverse_reverse] using
        (StructuredWasmStep.enterCall
          (module := targetModule.wasmModule) (env := hostEnv)
          (id := row.targetFunctionIndex) (function := row.targetFunction)
          (store := targetStore) (locals := storedCallerLocals)
          (rest := .localSet resultIndex :: targetRest)
          (frames := targetFrames) row.notImport row.targetFunctionFound)
    exact .single entered
  · refine {
      calleeFocus := ?_
      sourceJoinsEq := by simp [sourceAfter]
      sourceFramesEq := by simp [sourceAfter, related.sourceFramesEq]
      targetFramesEq := by simp [targetAfter]
      continuationAdapted := related.continuationAdapted
      callerStateRelated := storedCallerStateRelated
      callerFrameAligned := storedCallerFrameAligned
      resultFound := related.resultFound
      resultKindAt := related.resultKindAt
      argumentsRelated := related.argumentsRelated }
    exact {
      sourceProgramEq := by
        calc
          sourceAfter.program = callerContext.program := by
            simp [sourceAfter, related.sourceProgramEq]
          _ = calleeContext.program := row.contextProgram.symm
      sourceControlEq := by simp [sourceAfter]
      sourceEnvEq := by simp [sourceAfter]
      sourceRuntimeEq := by simp [sourceAfter, related.sourceRuntimeEq]
      targetStoreEq := by simp [targetAfter, related.targetStoreEq]
      targetControlEq := by simp [targetAfter]
      adapted := row.bodyAdapted
      stateRelated := calleeStateRelated
      frameAligned := calleeFrameAligned }

/-- Entry-to-current runtime transports preserve a suspended caller's local
relation.  The current callee relation supplies the evolved runtime and clear
failure channel; the accumulated witness transport reinterprets every saved
caller local at the current witness without changing either the source
environment or the physical local frame. -/
theorem ReuseCapacityCodeEntryTransports.savedStateRelated
    {entryRuntime currentRuntime : RuntimeState}
    {entryStore currentStore : Wasm.Store Host}
    {entryWitness currentWitness : RefinementWitness}
    {entryFunction currentFunction : Fir.Wasm.Function}
    {entryEnv currentEnv : Env}
    {entryLocals currentLocals : Wasm.Locals}
    (transports :
      ReuseCapacityCodeEntryTransports entryRuntime currentRuntime entryStore
        currentStore entryWitness currentWitness)
    (entryRelated :
      StateRelated entryFunction entryRuntime entryEnv entryStore entryLocals
        entryWitness)
    (currentRelated :
      StateRelated currentFunction currentRuntime currentEnv currentStore
        currentLocals currentWitness) :
    StateRelated entryFunction currentRuntime entryEnv currentStore entryLocals
      currentWitness := by
  exact ⟨currentRelated.1, currentRelated.2.1,
    EnvLocalsRelated.witnessTransport transports.witness entryRelated.2.2⟩

/-- Strengthen a structured direct-call entry with the canonical hereditary
cache frame used by the existing W6 operation-family induction.  The callee
starts with empty reuse facts and reflexive entry transports; its runtime,
budget, handler, cache, ownership, and immutable-table invariants come from
the caller frame through the generated declaration row. -/
theorem
    ConcreteStructuredDirectCallEntryFocus.calleeEntryRelativeCacheFrame
    {callerContext calleeContext : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction calleeFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {externals : ExternalImpl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {callerEnv : Env}
    {site : DirectInternalCallSite callerContext decl callerEnv}
    {row : ConcreteGeneratedInternalDeclaration callerContext.program
      site.sourceDeclaration calleeContext site.calleeCode sourceModule
      calleeFunction targetModule}
    {labels : List Lean.FVarId}
    {entryRuntime : RuntimeState}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {callerJoins : JoinEnv}
    {sourceFrames : List Frame}
    {entryStore : Wasm.Store Host}
    {callerLocals : Wasm.Locals}
    {callerRemainder : List Wasm.Value}
    {targetRest : Wasm.Program}
    {targetFrames : List StructuredWasmFrame}
    {entryWitness : RefinementWitness}
    {physicalArgs : List Wasm.Value}
    {resultIndex : Nat}
    {entrySource : MachineState}
    {entryTarget : StructuredWasmState Host}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    (entry : ConcreteStructuredDirectCallEntryFocus callerContext
      calleeContext sourceModule callerFunction calleeFunction targetModule
      site row labels entryRuntime continuation callerJoins sourceFrames
      entryStore callerLocals callerRemainder targetRest targetFrames
      entryWitness physicalArgs resultIndex entrySource entryTarget)
    (callerFrame :
      ConcreteReuseCapacityCacheFrame sourceModule callerFunction externals
        facts remainingBytes entryRuntime callerEnv entryStore callerLocals
        entryWitness) :
    ReuseCapacityEntryRelativeFrame
      (ConcreteReuseCapacityCacheFrame sourceModule calleeFunction externals)
      entryRuntime entryStore entryWitness [] remainingBytes entryRuntime
      site.calleeEnv entryStore (row.targetFunction.toLocals physicalArgs)
      entryWitness := by
  exact
    ⟨callerFrame.generatedDirectCalleeEntry site row entry.argumentsRelated,
      ReuseCapacityCodeEntryTransports.refl entryRuntime entryStore
        entryWitness⟩

/-- One saved source bind frame corresponds to the generated call frame whose
caller residual program stores the single returned value and continues with
the adapted source continuation.  Target-only label/loop frames may surround
this constructor later; they are not falsely identified with source frames. -/
structure ConcreteStructuredBindFrameFocus
    (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (labels : List Lean.FVarId)
    (sourceRuntime : RuntimeState)
    (callerEnv : Env)
    (sourceValue : Value)
    (result : Lean.FVarId)
    (continuation : Lean.Compiler.LCNF.Code .impure)
    (callerJoins : JoinEnv)
    (sourceFrames : List Frame)
    (targetStore : Wasm.Store Host)
    (callerLocals : Wasm.Locals)
    (callerRemainder : List Wasm.Value)
    (targetRest : Wasm.Program)
    (targetFrames : List StructuredWasmFrame)
    (returnedTail : List Wasm.Value)
    (witness : RefinementWitness)
    (kind : AbiKind)
    (physical : Wasm.Value)
    (resultIndex : Nat)
    (source : MachineState)
    (target : StructuredWasmState Host) : Prop where
  sourceProgramEq : source.program = context.program
  sourceControlEq : source.control = .yielded sourceValue
  sourceRuntimeEq : source.runtime = sourceRuntime
  sourceFramesEq :
    source.frames = .bind result continuation callerEnv callerJoins ::
      sourceFrames
  targetStoreEq : target.store = targetStore
  targetControlEq :
    target.control = .returning (physical :: returnedTail)
  targetFramesEq :
    target.frames =
      .call 1 callerRemainder callerLocals
          (.localSet resultIndex :: targetRest) :: targetFrames
  continuationAdapted :
    CodeAdapted context sourceModule sourceFunction labels continuation
      targetRest
  stateRelated :
    StateRelated sourceFunction sourceRuntime callerEnv targetStore callerLocals
      witness
  frameAligned :
    ConcreteLocalFrameAligned sourceFunction sourceRuntime callerEnv targetStore
      callerLocals witness
  resultFound :
    findFVar? (functionBindings sourceFunction) result = some resultIndex
  kindAt :
    (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some kind
  valueRelated : PhysicalValueRel witness kind physical sourceValue

theorem ConcreteStructuredBindFrameFocus.observes
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {sourceRuntime : RuntimeState}
    {callerEnv : Env}
    {sourceValue : Value}
    {result : Lean.FVarId}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {callerJoins : JoinEnv}
    {sourceFrames : List Frame}
    {targetStore : Wasm.Store Host}
    {callerLocals : Wasm.Locals}
    {callerRemainder returnedTail : List Wasm.Value}
    {targetRest : Wasm.Program}
    {targetFrames : List StructuredWasmFrame}
    {witness : RefinementWitness}
    {kind : AbiKind}
    {physical : Wasm.Value}
    {resultIndex : Nat}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredBindFrameFocus context sourceModule
      sourceFunction labels sourceRuntime callerEnv sourceValue result
      continuation callerJoins sourceFrames targetStore callerLocals
      callerRemainder targetRest targetFrames returnedTail witness kind physical
      resultIndex source target) :
    ConcretePrefixObservationRel
      (sourcePrefixObservation source)
      (concretePrefixObservation target.store) := by
  refine ⟨witness, ?_, ?_⟩
  · change target.store.host.runtime.world = source.runtime.world
    rw [related.targetStoreEq, related.sourceRuntimeEq]
    exact related.stateRelated.1.world
  · change ConcreteTraceRel witness target.store.host.runtime.trace
      source.runtime.trace
    rw [related.targetStoreEq, related.sourceRuntimeEq]
    exact related.stateRelated.1.trace

/-- Close the hereditary direct-call scope at a related callee yield.

The callee's current state relation and the accumulated entry transports
reconstruct the saved caller relation at the evolved store and witness.  The
explicit frame equalities state that nested administrative work has unwound
back to this call boundary.  The result is exactly the previously accepted
bind-frame focus, ready for `ConcreteStructuredBindFrameFocus.advance`; no
pre-call store equality or target-execution certificate is assumed. -/
theorem ConcreteStructuredDirectCallEntryFocus.bindFrame_of_yield
    {callerContext calleeContext : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction calleeFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {callerEnv : Env}
    {site : DirectInternalCallSite callerContext decl callerEnv}
    {row : ConcreteGeneratedInternalDeclaration callerContext.program
      site.sourceDeclaration calleeContext site.calleeCode sourceModule
      calleeFunction targetModule}
    {labels : List Lean.FVarId}
    {entryRuntime currentRuntime : RuntimeState}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {callerJoins : JoinEnv}
    {sourceFrames : List Frame}
    {entryStore currentStore : Wasm.Store Host}
    {callerLocals calleeLocals : Wasm.Locals}
    {callerRemainder : List Wasm.Value}
    {targetRest : Wasm.Program}
    {targetFrames : List StructuredWasmFrame}
    {entryWitness currentWitness : RefinementWitness}
    {physicalArgs : List Wasm.Value}
    {resultIndex : Nat}
    {entrySource : MachineState}
    {entryTarget : StructuredWasmState Host}
    {currentEnv : Env}
    {sourceValue : Value}
    {actualKind : AbiKind}
    {physical : Wasm.Value}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (entry : ConcreteStructuredDirectCallEntryFocus callerContext
      calleeContext sourceModule callerFunction calleeFunction targetModule
      site row labels entryRuntime continuation callerJoins sourceFrames
      entryStore callerLocals callerRemainder targetRest targetFrames
      entryWitness physicalArgs resultIndex entrySource entryTarget)
    (yielded : ConcreteStructuredYieldFocus calleeContext calleeFunction
      currentRuntime currentEnv sourceValue currentStore calleeLocals
      currentWitness actualKind physical source target)
    (transports :
      ReuseCapacityCodeEntryTransports entryRuntime currentRuntime entryStore
        currentStore entryWitness currentWitness)
    (sourceFramesEq :
      source.frames =
        .bind decl.fvarId continuation callerEnv callerJoins :: sourceFrames)
    (targetFramesEq :
      target.frames =
        .call 1 callerRemainder callerLocals
            (.localSet resultIndex :: targetRest) :: targetFrames)
    (resultRefines : actualKind.refines site.resultKind = true) :
    ConcreteStructuredBindFrameFocus callerContext sourceModule callerFunction
      labels currentRuntime callerEnv sourceValue decl.fvarId continuation
      callerJoins sourceFrames currentStore callerLocals callerRemainder
      targetRest targetFrames calleeLocals.values currentWitness site.resultKind
      physical resultIndex source target := by
  have callerStateRelated :
      StateRelated callerFunction currentRuntime callerEnv currentStore
        callerLocals currentWitness :=
    transports.savedStateRelated entry.callerStateRelated yielded.stateRelated
  have callerFrameAligned :
      ConcreteLocalFrameAligned callerFunction currentRuntime callerEnv
        currentStore callerLocals currentWitness := by
    simpa [ConcreteLocalFrameAligned] using entry.callerFrameAligned
  exact {
    sourceProgramEq := yielded.sourceProgramEq.trans row.contextProgram
    sourceControlEq := yielded.sourceControlEq
    sourceRuntimeEq := yielded.sourceRuntimeEq
    sourceFramesEq
    targetStoreEq := yielded.targetStoreEq
    targetControlEq := yielded.targetControlEq
    targetFramesEq
    continuationAdapted := entry.continuationAdapted
    stateRelated := callerStateRelated
    frameAligned := callerFrameAligned
    resultFound := entry.resultFound
    kindAt := entry.resultKindAt
    valueRelated := yielded.valueRelated.ofRefines resultRefines }

/-- Entry-relative cache-frame specialization of `bindFrame_of_yield`.

This is the direct composition point with the established hereditary runtime
proof: its final frame already contains the accumulated entry transports, so
clients need not unpack or restate witness/capacity/ownership transport when
closing a structured call. -/
theorem
    ConcreteStructuredDirectCallEntryFocus.bindFrame_of_yield_cacheFrame
    {callerContext calleeContext : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {callerFunction calleeFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {externals : ExternalImpl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {callerEnv : Env}
    {site : DirectInternalCallSite callerContext decl callerEnv}
    {row : ConcreteGeneratedInternalDeclaration callerContext.program
      site.sourceDeclaration calleeContext site.calleeCode sourceModule
      calleeFunction targetModule}
    {labels : List Lean.FVarId}
    {entryRuntime currentRuntime : RuntimeState}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {callerJoins : JoinEnv}
    {sourceFrames : List Frame}
    {entryStore currentStore : Wasm.Store Host}
    {callerLocals calleeLocals : Wasm.Locals}
    {callerRemainder : List Wasm.Value}
    {targetRest : Wasm.Program}
    {targetFrames : List StructuredWasmFrame}
    {entryWitness currentWitness : RefinementWitness}
    {physicalArgs : List Wasm.Value}
    {resultIndex : Nat}
    {entrySource : MachineState}
    {entryTarget : StructuredWasmState Host}
    {currentEnv : Env}
    {sourceValue : Value}
    {actualKind : AbiKind}
    {physical : Wasm.Value}
    {source : MachineState}
    {target : StructuredWasmState Host}
    {resultFacts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    (entry : ConcreteStructuredDirectCallEntryFocus callerContext
      calleeContext sourceModule callerFunction calleeFunction targetModule
      site row labels entryRuntime continuation callerJoins sourceFrames
      entryStore callerLocals callerRemainder targetRest targetFrames
      entryWitness physicalArgs resultIndex entrySource entryTarget)
    (yielded : ConcreteStructuredYieldFocus calleeContext calleeFunction
      currentRuntime currentEnv sourceValue currentStore calleeLocals
      currentWitness actualKind physical source target)
    (invariant :
      ReuseCapacityEntryRelativeFrame
        (ConcreteReuseCapacityCacheFrame sourceModule calleeFunction externals)
        entryRuntime entryStore entryWitness resultFacts remainingBytes
        currentRuntime currentEnv currentStore calleeLocals currentWitness)
    (sourceFramesEq :
      source.frames =
        .bind decl.fvarId continuation callerEnv callerJoins :: sourceFrames)
    (targetFramesEq :
      target.frames =
        .call 1 callerRemainder callerLocals
            (.localSet resultIndex :: targetRest) :: targetFrames)
    (resultRefines : actualKind.refines site.resultKind = true) :
    ConcreteStructuredBindFrameFocus callerContext sourceModule callerFunction
      labels currentRuntime callerEnv sourceValue decl.fvarId continuation
      callerJoins sourceFrames currentStore callerLocals callerRemainder
      targetRest targetFrames calleeLocals.values currentWitness site.resultKind
      physical resultIndex source target :=
  entry.bindFrame_of_yield yielded invariant.2 sourceFramesEq targetFramesEq
    resultRefines

/-- Resuming a related bind/call frame takes one source administrative step
and exactly two structured target steps: unwind the call frame, then store the
returned physical value.  The resulting source code and target residual code
re-enter `ConcreteStructuredCodeFocus` with the semantic result bound in the
caller environment. -/
theorem ConcreteStructuredBindFrameFocus.advance
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {externals : ExternalImpl}
    {sourceRuntime : RuntimeState}
    {callerEnv : Env}
    {sourceValue : Value}
    {result : Lean.FVarId}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {callerJoins : JoinEnv}
    {sourceFrames : List Frame}
    {targetStore : Wasm.Store Host}
    {callerLocals : Wasm.Locals}
    {callerRemainder returnedTail : List Wasm.Value}
    {targetRest : Wasm.Program}
    {targetFrames : List StructuredWasmFrame}
    {witness : RefinementWitness}
    {kind : AbiKind}
    {physical : Wasm.Value}
    {resultIndex : Nat}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredBindFrameFocus context sourceModule
      sourceFunction labels sourceRuntime callerEnv sourceValue result
      continuation callerJoins sourceFrames targetStore callerLocals
      callerRemainder targetRest targetFrames returnedTail witness kind physical
      resultIndex source target) :
    ∃ sourceAfter targetAfter updated resumedLocals,
      executeStep externals source = .next sourceAfter ∧
      FinitePath (StructuredWasmStep module hostEnv) 2 target targetAfter ∧
      callerLocals.set? resultIndex physical = some updated ∧
      resumedLocals = { updated with values := callerRemainder } ∧
      ConcreteStructuredCodeFocus context sourceModule sourceFunction labels
          sourceRuntime (bind callerEnv result sourceValue) continuation
          targetStore resumedLocals targetRest witness sourceAfter targetAfter ∧
        sourceAfter.joins = callerJoins ∧
        sourceAfter.frames = sourceFrames ∧
        targetAfter.frames = targetFrames := by
  obtain ⟨updated, targetSet, updatedAligned⟩ :=
    related.frameAligned.set?
      (nextRuntime := sourceRuntime)
      (nextEnv := bind callerEnv result sourceValue)
      (nextStore := targetStore)
      (nextWitness := witness)
      related.resultFound
  let resumedLocals : Wasm.Locals :=
    { updated with values := callerRemainder }
  have updatedRelated :
      StateRelated sourceFunction sourceRuntime
        (bind callerEnv result sourceValue) targetStore resumedLocals witness := by
    have bound := related.stateRelated.bindPhysical related.resultFound
      related.kindAt related.valueRelated targetSet
    rw [related.stateRelated.clearFailure] at bound
    simpa [resumedLocals, StateRelated, EnvLocalsRelated, Wasm.Locals.get]
      using bound
  have resumedAligned :
      ConcreteLocalFrameAligned sourceFunction sourceRuntime
        (bind callerEnv result sourceValue) targetStore resumedLocals witness := by
    simpa [resumedLocals, ConcreteLocalFrameAligned] using updatedAligned
  let sourceAfter : MachineState :=
    { source with
      control := .code continuation
      env := bind callerEnv result sourceValue
      joins := callerJoins
      frames := sourceFrames }
  let targetAfterCall : StructuredWasmState Host :=
    { target with
      control := .running
        { callerLocals with
          values := physical :: callerRemainder }
        (.localSet resultIndex :: targetRest)
      frames := targetFrames }
  let targetAfter : StructuredWasmState Host :=
    { target with
      control := .running resumedLocals targetRest
      frames := targetFrames }
  refine ⟨sourceAfter, targetAfter, updated, resumedLocals, ?_, ?_, targetSet,
    rfl, ?_, ?_, ?_, ?_⟩
  · rcases source with
      ⟨program, control, env, joins, frames, runtime⟩
    have controlEq := related.sourceControlEq
    change control = .yielded sourceValue at controlEq
    subst control
    have framesEq := related.sourceFramesEq
    change frames = _ at framesEq
    subst frames
    simp [sourceAfter, executeStep, coreStep]
  · have unwindStep :
        StructuredWasmStep module hostEnv target targetAfterCall := by
      rcases target with ⟨store, control, frames⟩
      have storeEq := related.targetStoreEq
      change store = targetStore at storeEq
      subst store
      have controlEq := related.targetControlEq
      change control = .returning (physical :: returnedTail) at controlEq
      subst control
      have framesEq := related.targetFramesEq
      change frames = _ at framesEq
      subst frames
      exact StructuredWasmStep.returnCall
    have stackSet :
        ({ callerLocals with
            values := physical :: callerRemainder }.set? resultIndex physical) =
          some { updated with values := physical :: callerRemainder } :=
      locals_set?_with_values (physical :: callerRemainder) targetSet
    have storeStep :
        StructuredWasmStep module hostEnv targetAfterCall targetAfter := by
      rcases target with ⟨store, control, frames⟩
      have storeEq := related.targetStoreEq
      change store = targetStore at storeEq
      subst store
      apply StructuredWasmStep.atomic (fuel := 1)
      · trivial
      · simp only [Wasm.execOne.eq_def, stackSet]
        rfl
    exact .cons unwindStep (.cons storeStep (.refl targetAfter))
  · exact {
      sourceProgramEq := by simp [sourceAfter, related.sourceProgramEq]
      sourceControlEq := by simp [sourceAfter]
      sourceEnvEq := by simp [sourceAfter]
      sourceRuntimeEq := by simp [sourceAfter, related.sourceRuntimeEq]
      targetStoreEq := by simp [targetAfter, related.targetStoreEq]
      targetControlEq := by simp [targetAfter]
      adapted := related.continuationAdapted
      stateRelated := updatedRelated
      frameAligned := resumedAligned }
  · simp [sourceAfter]
  · simp [sourceAfter]
  · simp [targetAfter]

/-- Re-index a recursively evolved callee frame back to its suspended caller.

The callee's entry-relative transport package carries every representation,
capacity, ownership, handler, cache, and immutable-table fact that may change
inside the call.  The checked caller-local update supplies the only
function-local operation needed at return.  This lemma therefore restores the
complete caller cache frame without packaging the callee as a target
execution certificate. -/
theorem ReuseCapacityEntryRelativeFrame.restoreDirectCaller
    {sourceModule : Fir.Wasm.Module}
    {callerFunction calleeFunction : Fir.Wasm.Function}
    {externals : ExternalImpl}
    {entryRuntime sourceRuntime nextRuntime : RuntimeState}
    {entryStore initial afterCall : Wasm.Store Host}
    {entryWitness initialWitness resultWitness : RefinementWitness}
    {facts calleeResultFacts : ReuseCapacityFacts}
    {callerBytes resultBytes : Nat}
    {sourceEnv calleeEnv : Env}
    {callerLocals calleeLocals resumedLocals : Wasm.Locals}
    {result : Lean.FVarId} {resultIndex : Nat}
    {sourceValue : Value} {physical : Wasm.Value}
    (caller :
      ReuseCapacityEntryRelativeFrame
        (ConcreteReuseCapacityCacheFrame sourceModule callerFunction externals)
        entryRuntime entryStore entryWitness facts callerBytes sourceRuntime
        sourceEnv initial callerLocals initialWitness)
    (callee :
      ReuseCapacityEntryRelativeFrame
        (ConcreteReuseCapacityCacheFrame sourceModule calleeFunction externals)
        sourceRuntime initial initialWitness calleeResultFacts resultBytes
        nextRuntime calleeEnv afterCall calleeLocals resultWitness)
    (finalRelated :
      StateRelated callerFunction nextRuntime
        (bind sourceEnv result sourceValue) afterCall resumedLocals
        resultWitness)
    (finalAligned :
      ConcreteLocalFrameAligned callerFunction nextRuntime
        (bind sourceEnv result sourceValue) afterCall resumedLocals
        resultWitness)
    (resultFound :
      findFVar? (functionBindings callerFunction) result = some resultIndex)
    (localUpdate :
      FirTalos.Correctness.LocalUpdate callerLocals resumedLocals resultIndex
        physical) :
    ReuseCapacityEntryRelativeFrame
      (ConcreteReuseCapacityCacheFrame sourceModule callerFunction externals)
      entryRuntime entryStore entryWitness (eraseReuseCapacityFact facts result)
      resultBytes nextRuntime (bind sourceEnv result sourceValue) afterCall
      resumedLocals resultWitness := by
  rcases caller.1 with
    ⟨⟨⟨⟨callerRelated, callerOrdinary, _callerAligned, _callerBudget⟩,
      _callerInteger, _callerNatural, _callerScalar⟩, _callerDescriptors⟩,
      _callerCache, _callerClosureTables⟩
  rcases callee.1 with
    ⟨⟨⟨⟨_calleeRelated, _calleeOrdinary, _calleeAligned, resultBudget⟩,
      resultInteger, resultNatural, resultScalar⟩, resultDescriptors⟩,
      resultCache, resultClosureTables⟩
  have resultRelated :
      ReuseCapacityStateRelated (eraseReuseCapacityFact facts result)
        callerFunction nextRuntime (bind sourceEnv result sourceValue)
        afterCall resumedLocals resultWitness :=
    callerRelated.eraseResult finalRelated resultFound localUpdate
      callee.2.witness callee.2.capacity
  have resultOrdinary :
      ReuseTokenOrdinaryRel (eraseReuseCapacityFact facts result) nextRuntime
        (bind sourceEnv result sourceValue) :=
    callerOrdinary.eraseBind callee.2.ordinary
  have resultTransports :
      ReuseCapacityCodeEntryTransports entryRuntime nextRuntime entryStore
        afterCall entryWitness resultWitness :=
    caller.2.step callee.2.witness callee.2.closureAllocationsPersistent
      callee.2.capacity callee.2.ordinary callee.2.externals
      callee.2.toClosureTablesTransport
  have resultBase :
      ConcreteReuseCapacityFrame callerFunction
        (eraseReuseCapacityFact facts result) resultBytes nextRuntime
        (bind sourceEnv result sourceValue) afterCall resumedLocals
        resultWitness :=
    ⟨resultRelated, resultOrdinary, finalAligned, resultBudget⟩
  have resultPure :
      ConcreteReuseCapacityPureExternalFrame callerFunction externals
        (eraseReuseCapacityFact facts result) resultBytes nextRuntime
        (bind sourceEnv result sourceValue) afterCall resumedLocals
        resultWitness :=
    ⟨resultBase, resultInteger, resultNatural, resultScalar⟩
  have resultOwnership :
      ConcreteReuseCapacityPureExternalOwnershipFrame callerFunction externals
        (eraseReuseCapacityFact facts result) resultBytes nextRuntime
        (bind sourceEnv result sourceValue) afterCall resumedLocals
        resultWitness :=
    ⟨resultPure, resultDescriptors⟩
  have resultFrame :
      ConcreteReuseCapacityCacheFrame sourceModule callerFunction externals
        (eraseReuseCapacityFact facts result) resultBytes nextRuntime
        (bind sourceEnv result sourceValue) afterCall resumedLocals
        resultWitness :=
    ⟨resultOwnership, resultCache, resultClosureTables⟩
  exact ⟨resultFrame, resultTransports⟩

/-- Empty case-selection family for the first recursive structured fragment. -/
def NoStructuredCasesSupported
    (_context : Fir.Wasm.Context) (_runtime : RuntimeState) (_env : Env)
    (_cases : Lean.Compiler.LCNF.Cases .impure)
    (_selected : Lean.Compiler.LCNF.Code .impure) : Prop :=
  False

/-- Source-only recursive admission for direct values and statically named
internal calls.  This is a specialization of the existing hereditary source
relation, not a second evaluator: external, lazy, case, and effect constructors
are disabled until their structured target rules are connected. -/
abbrev ReuseCapacityStructuredDirectCallCodeEvaluates
    (externals : ExternalImpl) :=
  ReuseCapacityDirectHereditaryCodeEvaluates externals
    (fun context => ReuseBudgetedDirectSupported context)
    (fun _context => NoReuseCapacityExternalsSupported)
    (fun _context => NoReuseCapacityLazySupported)
    NoStructuredCasesSupported
    (fun _context => NoEffectsSupported)
    directLetAllocationCost

/-- Recursive admission after connecting the complete pure external-result
family to the structured target.  Lazy/cache, case, and effect constructors
remain disabled at this layer. -/
abbrev ReuseCapacityStructuredPureExternalCallCodeEvaluates
    (externals : ExternalImpl) :=
  ReuseCapacityDirectHereditaryCodeEvaluates externals
    (fun context => ReuseBudgetedDirectSupported context)
    (fun context => PureExternalSupported context externals)
    (fun _context => NoReuseCapacityLazySupported)
    NoStructuredCasesSupported
    (fun _context => NoEffectsSupported)
    directLetAllocationCost

/-- Recover the ordinary ABI classifier from the direct-call classifier. -/
theorem abiKind?_of_directAbiKind?_eq_some
    {type : Lean.Expr} {kind : AbiKind}
    (classified : Fir.Wasm.directAbiKind? type = some kind) :
    Fir.Wasm.abiKind? type = .ok (some kind) := by
  unfold Fir.Wasm.directAbiKind? at classified
  cases result : Fir.Wasm.abiKind? type with
  | error error => simp [result] at classified
  | ok optional =>
      cases optional with
      | none => simp [result] at classified
      | some actual =>
          simp only [result, Option.some.injEq] at classified
          subst actual
          rfl

/-- ABI representation refinement composes across generated declaration and
caller result rows. -/
theorem AbiKind.refines_trans
    {actual middle expected : AbiKind}
    (left : actual.refines middle = true)
    (right : middle.refines expected = true) :
    actual.refines expected = true := by
  cases actual <;> cases middle <;> cases expected <;>
    simp_all [AbiKind.refines]

/-- Simulation-facing bind-frame rule.  Determinism identifies the successor
constructed by `advance` with the successor supplied by the generic source
transition premise. -/
theorem ConcreteStructuredBindFrameFocus.advance_of_step
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {externals : ExternalImpl}
    {sourceRuntime : RuntimeState}
    {callerEnv : Env}
    {sourceValue : Value}
    {result : Lean.FVarId}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {callerJoins : JoinEnv}
    {sourceFrames : List Frame}
    {targetStore : Wasm.Store Host}
    {callerLocals : Wasm.Locals}
    {callerRemainder returnedTail : List Wasm.Value}
    {targetRest : Wasm.Program}
    {targetFrames : List StructuredWasmFrame}
    {witness : RefinementWitness}
    {kind : AbiKind}
    {physical : Wasm.Value}
    {resultIndex : Nat}
    {source sourceAfter : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredBindFrameFocus context sourceModule
      sourceFunction labels sourceRuntime callerEnv sourceValue result
      continuation callerJoins sourceFrames targetStore callerLocals
      callerRemainder targetRest targetFrames returnedTail witness kind physical
      resultIndex source target)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ targetAfter resumedLocals,
      FinitePath (StructuredWasmStep module hostEnv) 2 target targetAfter ∧
      ConcreteStructuredCodeFocus context sourceModule sourceFunction labels
        sourceRuntime (bind callerEnv result sourceValue) continuation
        targetStore resumedLocals targetRest witness sourceAfter targetAfter := by
  obtain ⟨computedAfter, targetAfter, _updated, resumedLocals, computedStep,
      path, _targetSet, _resumedEq, focus, _sourceJoinsEq, _sourceFramesEq,
      _targetFramesEq⟩ :=
    related.advance (module := module) (hostEnv := hostEnv)
      (externals := externals)
  have afterEq : sourceAfter = computedAfter := by
    rw [sourceStep] at computedStep
    injection computedStep
  subst computedAfter
  exact ⟨targetAfter, resumedLocals, path, focus⟩

/-- Recursive structured partial correctness for direct values, supported pure
external results, and statically named calls.

External results traverse the interpreter's exact three-step request protocol
and the compiler-derived imported-call prefix. A named call is staged by the
production compiler, entered by the structured machine, discharged recursively
in the exact generated declaration row, and returned through the saved
bind/call frames. Both machine paths, the entry-relative concrete resource
frame, the result ABI refinement, and exact restoration of the enclosing frame
stacks are retained. No target trace, callee execution package, or translation
certificate is a premise. -/
theorem
    ConcreteStructuredCodeFocus.reachesYield_reuseBudgetedDirectPureExternalCalls_generated
    {program : Fir.LeanIR.ImpureProgram}
    {rootContext : Fir.Wasm.Context}
    {rootCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {rootFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule} {hosts : ResolvedHosts}
    {exportName : String}
    (rootSpec :
      ConcreteSupportedExport program rootContext rootCode sourceModule
        rootFunction targetModule hosts exportName)
    {context : Fir.Wasm.Context}
    {functionCode code : Lean.Compiler.LCNF.Code .impure}
    {sourceFunction : Fir.Wasm.Function}
    (functionSpec :
      ConcreteSupportedFunction program context functionCode sourceModule
        sourceFunction targetModule hosts)
    (contextCaches :
      context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program)
    {externals : ExternalImpl}
    {expectedResult : AbiKind}
    {facts resultFacts : ReuseCapacityFacts}
    {sourceRuntime resultRuntime entryRuntime : RuntimeState}
    {sourceEnv resultEnv : Env}
    {resultValue : Value} {requiredBytes slack : Nat}
    {targetStore entryStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {witness entryWitness : RefinementWitness}
    {targetCode : Wasm.Program}
    {source : MachineState} {target : StructuredWasmState Host}
    (evaluation :
      ReuseCapacityStructuredPureExternalCallCodeEvaluates externals context
        expectedResult facts sourceRuntime sourceEnv code resultFacts
        resultRuntime resultEnv resultValue requiredBytes)
    (related :
      ConcreteStructuredCodeFocus context sourceModule sourceFunction []
        sourceRuntime sourceEnv code targetStore targetLocals targetCode witness
        source target)
    (sourceJoins : source.joins = [])
    (invariant :
      ReuseCapacityEntryRelativeFrame
        (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals)
        entryRuntime entryStore entryWitness facts (requiredBytes + slack)
        sourceRuntime sourceEnv targetStore targetLocals witness) :
    ∃ sourceAfter targetAfter resultStore resultLocals resultWitness kind
        physical sourceCount targetCount,
      FinitePath
          (fun before after => executeStep externals before = .next after)
          sourceCount source sourceAfter ∧
        FinitePath
            (StructuredWasmStep targetModule.wasmModule hosts.env)
            targetCount target targetAfter ∧
          ConcreteStructuredYieldFocus context sourceFunction resultRuntime
              resultEnv resultValue resultStore resultLocals resultWitness kind
              physical sourceAfter targetAfter ∧
            ReuseCapacityEntryRelativeFrame
                (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
                  externals)
                entryRuntime entryStore entryWitness resultFacts slack
                resultRuntime resultEnv resultStore resultLocals resultWitness ∧
              kind.refines expectedResult = true ∧
                sourceAfter.joins = [] ∧
                sourceAfter.frames = source.frames ∧
                targetAfter.frames = target.frames := by
  induction evaluation generalizing functionCode sourceFunction
      targetStore targetLocals targetCode witness source target entryRuntime
      entryStore entryWitness slack with
  | ret sourceLookup resultCompiled resultRefines =>
      obtain ⟨kind, physical, sourceAfter, targetAfter, targetResultCompiled,
          sourceStep, targetPath, yielded, sourceAfterJoins, sourceFramesEq,
          targetFramesEq⟩ :=
        related.advance_return functionSpec.localsAligned sourceLookup
      rw [resultCompiled] at targetResultCompiled
      have resultPairEq := Except.ok.inj targetResultCompiled
      cases resultPairEq
      exact ⟨sourceAfter, targetAfter, targetStore, targetLocals, witness,
        _, physical, 1, 2, .single sourceStep, targetPath,
        yielded, by simpa using invariant, resultRefines,
        sourceAfterJoins.trans sourceJoins, sourceFramesEq, targetFramesEq⟩
  | @letValue context facts decl sourceRuntime sourceEnv nextRuntime sourceValue
      nextFacts expectedResult continuation resultFacts resultRuntime resultEnv
      resultValue continuationCost supported sourceStep transfer continued ih =>
      obtain ⟨valueCode, restCode, targetValue, targetRest, resultIndex,
          valueCompiled, restCompiled, valueAdapted, restAdapted, resultFound,
          targetCodeEq⟩ :=
        CodeAdapted.let_eq related.adapted
      have continuationAdapted :
          CodeAdapted context sourceModule sourceFunction [] continuation
            targetRest :=
        ⟨restCode, restCompiled, restAdapted⟩
      have stepFits :
          directLetAllocationCost decl ≤
            (directLetAllocationCost decl + continuationCost) + slack := by
        omega
      obtain ⟨nextStore, nextLocals, nextWitness, producedFacts, step,
          _externalsPreserved, _hostDescriptorsPreserved,
          _witnessDescriptorsPreserved, _transports, producedTransfer,
          nextInvariant⟩ :=
        (functionSpec.reuseCapacityDirectLetRuntimeRefinesWithCost_reuseBudgetedDirect_pureExternalOwnership_entryRelativeCache
          externals) supported stepFits invariant sourceStep valueCompiled
            valueAdapted resultFound
      rw [transfer] at producedTransfer
      have factsEq := Option.some.inj producedTransfer
      subst producedFacts
      have continuationInvariant :
          ReuseCapacityEntryRelativeFrame
            (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
              externals)
            entryRuntime entryStore entryWitness nextFacts
            (continuationCost + slack) nextRuntime
            (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals
            nextWitness := by
        have budgetEq :
            (directLetAllocationCost decl + continuationCost) + slack -
                directLetAllocationCost decl =
              continuationCost + slack := by
          omega
        simpa only [budgetEq] using nextInvariant
      have flat :
          StructuredWasmFlatProgram targetModule.wasmModule
            (targetValue ++ [.localSet resultIndex]) :=
        functionSpec.reuseCapacityDirectTargetFlat_reuseBudgetedDirect
          supported valueCompiled valueAdapted
      obtain ⟨sourceMiddle, targetMiddle, firstSourceStep, targetPrefix,
          nextFocus, firstSourceJoinsEq, firstSourceFramesEq,
          firstTargetFramesEq⟩ :=
        related.advance_flatLet targetCodeEq continuationAdapted flat step
          continuationInvariant.1.1.1.1.2.2.1
      obtain ⟨sourceAfter, targetAfter, resultStore, resultLocals,
          resultWitness, kind, physical, sourceCount, targetCount, sourceTail,
          targetTail, yielded, resultInvariant, resultRefines,
          resultJoins, tailSourceFramesEq, tailTargetFramesEq⟩ :=
        ih functionSpec contextCaches nextFocus
          (firstSourceJoinsEq.trans sourceJoins)
          (continuationInvariant.withValues targetLocals.values)
      exact ⟨sourceAfter, targetAfter, resultStore, resultLocals,
        resultWitness, kind, physical, 1 + sourceCount,
        (targetValue ++ [Wasm.Instruction.localSet resultIndex]).length +
          targetCount,
        (FinitePath.single
          (step := fun before after =>
            executeStep externals before = .next after)
          firstSourceStep).trans sourceTail,
        targetPrefix.trans targetTail, yielded, resultInvariant, resultRefines,
        resultJoins, tailSourceFramesEq.trans firstSourceFramesEq,
        tailTargetFramesEq.trans firstTargetFramesEq⟩
  | @directCallLet context decl sourceEnv sourceRuntime calleeResultFacts
      nextRuntime calleeResultEnv sourceValue stepCost facts nextFacts
      expectedResult continuation resultFacts resultRuntime resultEnv resultValue
      continuationCost calleeFunction site loweredRow callee transfer continued
      calleeIH continuedIH =>
      have programEq : context.program = program := functionSpec.contextProgram
      subst program
      have resultClassified :
          Fir.Wasm.abiKind? site.sourceDeclaration.type =
            .ok (some site.calleeResultKind) :=
        abiKind?_of_directAbiKind?_eq_some site.calleeResult
      obtain ⟨generatedRow⟩ :=
        ConcreteGeneratedInternalDeclaration.exists_ofSupportedPipelineAtLowered
          rfl contextCaches rootSpec.programNamesUnique rootSpec.lowered
          rootSpec.adapted site.declarationFound loweredRow resultClassified
      obtain ⟨physicalArgs, resultIndex, targetArguments, targetRest,
          sourceStaged, targetReady, stageSourceStep, targetArgumentsPath,
          ready⟩ :=
        related.advance_directCall_stage site generatedRow
          functionSpec.localsAligned
      obtain ⟨sourceEntry, targetEntry, storedCallerLocals, storedCallerEq,
          enterSourceStep, enterTargetPath, entry⟩ :=
        ready.advance_enter
      have storedCallerFrame :
          ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals
            facts ((stepCost + continuationCost) + slack) sourceRuntime
            sourceEnv targetStore storedCallerLocals witness := by
        rw [storedCallerEq]
        exact invariant.1.withValues _
      have calleeEntryInvariant :=
        entry.calleeEntryRelativeCacheFrame storedCallerFrame
      have calleeInvariantWithSlack :
          ReuseCapacityEntryRelativeFrame
            (ConcreteReuseCapacityCacheFrame sourceModule calleeFunction
              externals)
            sourceRuntime targetStore witness []
            (stepCost + (continuationCost + slack)) sourceRuntime
            site.calleeEnv targetStore
            (generatedRow.targetFunction.toLocals physicalArgs) witness := by
        simpa only [Nat.add_assoc] using calleeEntryInvariant
      obtain ⟨sourceYield, targetYield, afterCall, calleeLocals, resultWitness,
          actualKind, physical, calleeSourceCount, calleeTargetCount,
          calleeSourcePath, calleeTargetPath, calleeYielded, calleeInvariant,
          calleeResultRefines, _calleeResultJoins, calleeSourceFramesEq,
          calleeTargetFramesEq⟩ :=
        calleeIH (generatedRow.toSupportedFunction rootSpec)
          generatedRow.contextCaches entry.calleeFocus entry.sourceJoinsEq
          calleeInvariantWithSlack
      have sourceCallFramesEq :
          sourceYield.frames =
            .bind decl.fvarId continuation sourceEnv source.joins ::
              source.frames :=
        calleeSourceFramesEq.trans entry.sourceFramesEq
      have targetCallFramesEq :
          targetYield.frames =
            .call 1 targetLocals.values storedCallerLocals
                (.localSet resultIndex :: targetRest) :: target.frames :=
        calleeTargetFramesEq.trans entry.targetFramesEq
      have bindFocus :=
        entry.bindFrame_of_yield_cacheFrame calleeYielded calleeInvariant
          sourceCallFramesEq targetCallFramesEq
          (AbiKind.refines_trans calleeResultRefines
            site.calleeResultRefines)
      obtain ⟨sourceResumed, targetResumed, updated, resumedLocals,
          bindSourceStep, bindTargetPath, targetSet, resumedEq, resumedFocus,
          resumedSourceJoinsEq, resumedSourceFramesEq,
          resumedTargetFramesEq⟩ :=
        bindFocus.advance
      have storedInvariant :
          ReuseCapacityEntryRelativeFrame
            (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
              externals)
            entryRuntime entryStore entryWitness facts
            ((stepCost + continuationCost) + slack) sourceRuntime sourceEnv
            targetStore storedCallerLocals witness := by
        rw [storedCallerEq]
        exact invariant.withValues _
      have resumedUpdate :
          FirTalos.Correctness.LocalUpdate storedCallerLocals resumedLocals
            resultIndex physical := by
        rw [resumedEq]
        have base := FirTalos.Correctness.localUpdate_of_set? targetSet
        refine ⟨?_, ?_⟩
        · simpa [Wasm.Locals.get] using base.1
        · intro other different
          simpa [Wasm.Locals.get] using base.2 different
      have expectedTransfer :
          reuseCapacityLetFacts? facts decl =
            some (eraseReuseCapacityFact facts decl.fvarId) := by
        simp [reuseCapacityLetFacts?, site.valueEq]
      rw [expectedTransfer] at transfer
      have nextFactsEq : nextFacts = eraseReuseCapacityFact facts decl.fvarId :=
        Option.some.inj transfer.symm
      have callerAfterCall :=
        storedInvariant.restoreDirectCaller calleeInvariant
          resumedFocus.stateRelated resumedFocus.frameAligned entry.resultFound
          resumedUpdate
      have continuationInvariant :
          ReuseCapacityEntryRelativeFrame
            (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
              externals)
            entryRuntime entryStore entryWitness nextFacts
            (continuationCost + slack) nextRuntime
            (bind sourceEnv decl.fvarId sourceValue) afterCall resumedLocals
            resultWitness := by
        simpa only [nextFactsEq] using callerAfterCall
      obtain ⟨sourceAfter, targetAfter, resultStore, resultLocals,
          finalWitness, kind, resultPhysical, continuationSourceCount,
          continuationTargetCount, continuationSourcePath,
          continuationTargetPath, yielded, resultInvariant, resultRefines,
          resultJoins, continuationSourceFramesEq,
          continuationTargetFramesEq⟩ :=
        continuedIH functionSpec contextCaches resumedFocus
          (resumedSourceJoinsEq.trans sourceJoins)
          continuationInvariant
      exact ⟨sourceAfter, targetAfter, resultStore, resultLocals, finalWitness,
        kind, resultPhysical,
        1 + 1 + calleeSourceCount + 1 + continuationSourceCount,
        targetArguments.length + 1 + calleeTargetCount + 2 +
          continuationTargetCount,
        (((FinitePath.single
          (step := fun before after =>
            executeStep externals before = .next after)
          stageSourceStep).trans (.single enterSourceStep)).trans
            calleeSourcePath).trans (.single bindSourceStep) |>.trans
              continuationSourcePath,
        (((targetArgumentsPath.trans enterTargetPath).trans calleeTargetPath).trans
          bindTargetPath).trans continuationTargetPath,
        yielded, resultInvariant, resultRefines, resultJoins,
        continuationSourceFramesEq.trans resumedSourceFramesEq,
        continuationTargetFramesEq.trans resumedTargetFramesEq⟩
  | @externalLet context sourceRuntime sourceEnv decl continuation nextRuntime
      sourceValue stepCost facts nextFacts expectedResult resultFacts
      resultRuntime resultEnv resultValue continuationCost supported sourceStep
      transfer continued ih =>
      obtain ⟨valueCode, restCode, targetValue, targetRest, resultIndex,
          valueCompiled, restCompiled, valueAdapted, restAdapted, resultFound,
          targetCodeEq⟩ :=
        CodeAdapted.let_eq related.adapted
      have continuationAdapted :
          CodeAdapted context sourceModule sourceFunction [] continuation
            targetRest :=
        ⟨restCode, restCompiled, restAdapted⟩
      have stepFits :
          stepCost ≤ (stepCost + continuationCost) + slack := by
        omega
      obtain ⟨nextStore, nextLocals, nextWitness, producedFacts, step,
          _externalsPreserved, _hostDescriptorsPreserved,
          _witnessDescriptorsPreserved, producedTransfer, nextInvariant⟩ :=
        (functionSpec.reuseCapacityExternalLetRuntimeRefinesWithCost_pureExternal_entryRelativeCache
          externals) supported stepFits invariant sourceStep valueCompiled
            valueAdapted resultFound
      rw [transfer] at producedTransfer
      have factsEq := Option.some.inj producedTransfer
      subst producedFacts
      have continuationInvariant :
          ReuseCapacityEntryRelativeFrame
            (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
              externals)
            entryRuntime entryStore entryWitness nextFacts
            (continuationCost + slack) nextRuntime
            (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals
            nextWitness := by
        have budgetEq :
            (stepCost + continuationCost) + slack - stepCost =
              continuationCost + slack := by
          omega
        simpa only [budgetEq] using nextInvariant
      have flat :
          StructuredWasmFlatProgram targetModule.wasmModule
            (targetValue ++ [.localSet resultIndex]) :=
        supported.structuredFlatProgram functionSpec valueCompiled valueAdapted
      obtain ⟨sourceMiddle, targetMiddle, sourcePrefix, targetPrefix,
          nextFocus, nextSourceJoins, firstSourceFramesEq,
          firstTargetFramesEq⟩ :=
        related.advance_flatExternalLet sourceJoins targetCodeEq
          continuationAdapted flat step
          continuationInvariant.1.1.1.1.2.2.1
      obtain ⟨sourceAfter, targetAfter, resultStore, resultLocals,
          resultWitness, kind, physical, sourceCount, targetCount, sourceTail,
          targetTail, yielded, resultInvariant, resultRefines, resultJoins,
          tailSourceFramesEq, tailTargetFramesEq⟩ :=
        ih functionSpec contextCaches nextFocus nextSourceJoins
          (continuationInvariant.withValues targetLocals.values)
      exact ⟨sourceAfter, targetAfter, resultStore, resultLocals,
        resultWitness, kind, physical, 3 + sourceCount,
        (targetValue ++ [Wasm.Instruction.localSet resultIndex]).length +
          targetCount,
        sourcePrefix.trans sourceTail, targetPrefix.trans targetTail, yielded,
        resultInvariant, resultRefines, resultJoins,
        tailSourceFramesEq.trans firstSourceFramesEq,
        tailTargetFramesEq.trans firstTargetFramesEq⟩
  | lazyLet _path supported _sourceStep _transfer _continued _ih =>
      exact False.elim supported
  | caseOf supported _sourceStep _continued _ih =>
      exact False.elim supported
  | effect supported _sourceStep _continued _ih =>
      exact False.elim supported

/-- Structural rank used when lowering erases a source control step.  Later
frame slices add their own continuation component; the local erased-step laws
need only this strictly decreasing code-control component. -/
def compilerCodeSilenceDepth : Lean.Compiler.LCNF.Code .impure → Nat
  | .inc _ _ _ true continuation =>
      compilerCodeSilenceDepth continuation + 1
  | .dec _ _ _ true _ continuation =>
      compilerCodeSilenceDepth continuation + 1
  | _ => 0

def compilerCodeSilenceRank (state : MachineState) : Nat :=
  match state.control with
  | .code code => compilerCodeSilenceDepth code
  | _ => 0

/-- A persistent increment is one source step, no target steps, and a strict
drop in the local silence rank. -/
theorem ConcreteStructuredCodeFocus.advance_incPersistent
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {externals : ExternalImpl}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {amount : Nat}
    {check : Bool}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {witness : RefinementWitness}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels sourceRuntime sourceEnv
      (.inc objectId amount check true continuation) targetStore targetLocals
      targetCode witness source target) :
    ∃ sourceAfter,
      executeStep externals source = .next sourceAfter ∧
      FinitePath (StructuredWasmStep module hostEnv) 0 target target ∧
      ConcreteStructuredCodeFocus context sourceModule sourceFunction labels
        sourceRuntime sourceEnv continuation targetStore targetLocals targetCode
        witness sourceAfter target ∧
      compilerCodeSilenceRank sourceAfter < compilerCodeSilenceRank source := by
  let sourceAfter : MachineState :=
    { source with control := .code continuation }
  refine ⟨sourceAfter, ?_, .refl target, ?_, ?_⟩
  · rcases source with
      ⟨program, control, env, joins, frames, runtime⟩
    have controlEq := related.sourceControlEq
    change control = _ at controlEq
    subst control
    rfl
  · exact {
      sourceProgramEq := by simp [sourceAfter, related.sourceProgramEq]
      sourceControlEq := by simp [sourceAfter]
      sourceEnvEq := by simp [sourceAfter, related.sourceEnvEq]
      sourceRuntimeEq := by simp [sourceAfter, related.sourceRuntimeEq]
      targetStoreEq := related.targetStoreEq
      targetControlEq := related.targetControlEq
      adapted := CodeAdapted.incPersistent_eq related.adapted
      stateRelated := related.stateRelated
      frameAligned := related.frameAligned }
  · simp [compilerCodeSilenceRank, compilerCodeSilenceDepth, sourceAfter,
      related.sourceControlEq]

/-- A persistent decrement has the same ranked zero-step target match as a
persistent increment. -/
theorem ConcreteStructuredCodeFocus.advance_decPersistent
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {externals : ExternalImpl}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {objectId : Lean.FVarId}
    {amount : Nat}
    {check : Bool}
    {objectFields? : Option Nat}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {witness : RefinementWitness}
    {source : MachineState}
    {target : StructuredWasmState Host}
    (related : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels sourceRuntime sourceEnv
      (.dec objectId amount check true objectFields? continuation) targetStore
      targetLocals targetCode witness source target) :
    ∃ sourceAfter,
      executeStep externals source = .next sourceAfter ∧
      FinitePath (StructuredWasmStep module hostEnv) 0 target target ∧
      ConcreteStructuredCodeFocus context sourceModule sourceFunction labels
        sourceRuntime sourceEnv continuation targetStore targetLocals targetCode
        witness sourceAfter target ∧
      compilerCodeSilenceRank sourceAfter < compilerCodeSilenceRank source := by
  let sourceAfter : MachineState :=
    { source with control := .code continuation }
  refine ⟨sourceAfter, ?_, .refl target, ?_, ?_⟩
  · rcases source with
      ⟨program, control, env, joins, frames, runtime⟩
    have controlEq := related.sourceControlEq
    change control = _ at controlEq
    subst control
    rfl
  · exact {
      sourceProgramEq := by simp [sourceAfter, related.sourceProgramEq]
      sourceControlEq := by simp [sourceAfter]
      sourceEnvEq := by simp [sourceAfter, related.sourceEnvEq]
      sourceRuntimeEq := by simp [sourceAfter, related.sourceRuntimeEq]
      targetStoreEq := related.targetStoreEq
      targetControlEq := related.targetControlEq
      adapted := CodeAdapted.decPersistent_eq related.adapted
      stateRelated := related.stateRelated
      frameAligned := related.frameAligned }
  · simp [compilerCodeSilenceRank, compilerCodeSilenceDepth, sourceAfter,
      related.sourceControlEq]

end FirTalos.Concrete
