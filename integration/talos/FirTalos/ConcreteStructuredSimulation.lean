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

/-- A proved unary no-result host operation reifies as the exact generated
two-instruction structured prefix.  The host contract supplies execution;
flatness only decomposes that execution into the local-read and imported-call
machine steps beneath an arbitrary continuation and frame stack. -/
theorem structuredWasmUnaryHostEffectPrefixFinitePath
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {step : Wasm.Store Host → List Wasm.Value → Wasm.HostResult Host}
    {initial final : Wasm.Store Host} {locals : Wasm.Locals}
    {objectIndex : Nat} {physicalObject : Wasm.Value}
    {targetRest : Wasm.Program} {tail : List Wasm.Value}
    {frames : List StructuredWasmFrame}
    (objectFound : locals.get objectIndex = some physicalObject)
    (imported : module.imports[id]? = some imp)
    (satisfies : env.Satisfies module spec)
    (inBounds : id < module.imports.length)
    (contracted : spec.contracts[id]? = some
      (fun initial args result => result = step initial args))
    (parameterCount : imp.params.length = 1)
    (resultCount : imp.results.length = 0)
    (operation : step initial [physicalObject] = .Return [] final) :
    FinitePath (StructuredWasmStep module env) 2
      ⟨initial,
        .running { locals with values := tail }
          ([.localGet objectIndex, .call id] ++ targetRest),
        frames⟩
      ⟨final, .running { locals with values := tail } targetRest, frames⟩ := by
  have flat :
      StructuredWasmFlatProgram module [.localGet objectIndex, .call id] :=
    .cons (.atomic (by trivial)) (.cons (.importedCall imported) .nil)
  have executed :
      StructuredWasmExecutes module env initial
        { locals with values := tail } [.localGet objectIndex, .call id]
        (.fallthrough final { locals with values := tail }) := by
    apply structuredWasmExecutes_fallthrough_of_wp
    let Q : Wasm.Assertion Host := fun continuation =>
      continuation = .Fallthrough final { locals with values := tail }
    have finalWP :
        Wasm.wp module [] Q final { locals with values := tail } env :=
      (Wasm.wp_nil).2 rfl
    simpa [Q] using
      wp_effect_localGets
        (indices := [objectIndex]) (physicalArgs := [physicalObject])
        (rest := []) (tail := tail) (.cons objectFound .nil) imported satisfies
        inBounds contracted parameterCount resultCount operation finalWP
  simpa using
    flat.finitePathWithSuffix (suffix := targetRest) (frames := frames)
      executed

/-- A proved binary no-result host operation reifies as the exact generated
three-instruction structured prefix beneath arbitrary residual code and saved
frames. -/
theorem structuredWasmBinaryHostEffectPrefixFinitePath
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {step : Wasm.Store Host → List Wasm.Value → Wasm.HostResult Host}
    {initial final : Wasm.Store Host} {locals : Wasm.Locals}
    {firstIndex secondIndex : Nat}
    {physicalFirst physicalSecond : Wasm.Value}
    {targetRest : Wasm.Program} {tail : List Wasm.Value}
    {frames : List StructuredWasmFrame}
    (firstFound : locals.get firstIndex = some physicalFirst)
    (secondFound : locals.get secondIndex = some physicalSecond)
    (imported : module.imports[id]? = some imp)
    (satisfies : env.Satisfies module spec)
    (inBounds : id < module.imports.length)
    (contracted : spec.contracts[id]? = some
      (fun initial args result => result = step initial args))
    (parameterCount : imp.params.length = 2)
    (resultCount : imp.results.length = 0)
    (operation : step initial [physicalFirst, physicalSecond] =
      .Return [] final) :
    FinitePath (StructuredWasmStep module env) 3
      ⟨initial,
        .running { locals with values := tail }
          ([.localGet firstIndex, .localGet secondIndex, .call id] ++
            targetRest),
        frames⟩
      ⟨final, .running { locals with values := tail } targetRest, frames⟩ := by
  have flat :
      StructuredWasmFlatProgram module
        [.localGet firstIndex, .localGet secondIndex, .call id] :=
    .cons (.atomic (by trivial))
      (.cons (.atomic (by trivial)) (.cons (.importedCall imported) .nil))
  have executed :
      StructuredWasmExecutes module env initial
        { locals with values := tail }
        [.localGet firstIndex, .localGet secondIndex, .call id]
        (.fallthrough final { locals with values := tail }) := by
    apply structuredWasmExecutes_fallthrough_of_wp
    let Q : Wasm.Assertion Host := fun continuation =>
      continuation = .Fallthrough final { locals with values := tail }
    have finalWP :
        Wasm.wp module [] Q final { locals with values := tail } env :=
      (Wasm.wp_nil).2 rfl
    simpa [Q] using
      wp_effect_localGets
        (indices := [firstIndex, secondIndex])
        (physicalArgs := [physicalFirst, physicalSecond])
        (rest := []) (tail := tail)
        (.cons firstFound (.cons secondFound .nil)) imported satisfies
        inBounds contracted parameterCount resultCount operation finalWP
  simpa using
    flat.finitePathWithSuffix (suffix := targetRest) (frames := frames)
      executed

/-- A proved local/constant binary host operation reifies as the exact
three-instruction structured prefix used for erased object-field writes. -/
theorem structuredWasmLocalI32ConstHostEffectPrefixFinitePath
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {step : Wasm.Store Host → List Wasm.Value → Wasm.HostResult Host}
    {initial final : Wasm.Store Host} {locals : Wasm.Locals}
    {firstIndex : Nat} {physicalFirst : Wasm.Value} {constant : UInt32}
    {targetRest : Wasm.Program} {tail : List Wasm.Value}
    {frames : List StructuredWasmFrame}
    (firstFound : locals.get firstIndex = some physicalFirst)
    (imported : module.imports[id]? = some imp)
    (satisfies : env.Satisfies module spec)
    (inBounds : id < module.imports.length)
    (contracted : spec.contracts[id]? = some
      (fun initial args result => result = step initial args))
    (parameterCount : imp.params.length = 2)
    (resultCount : imp.results.length = 0)
    (operation : step initial [physicalFirst, .i32 constant] =
      .Return [] final) :
    FinitePath (StructuredWasmStep module env) 3
      ⟨initial,
        .running { locals with values := tail }
          ([.localGet firstIndex, .const constant, .call id] ++ targetRest),
        frames⟩
      ⟨final, .running { locals with values := tail } targetRest, frames⟩ := by
  have flat :
      StructuredWasmFlatProgram module
        [.localGet firstIndex, .const constant, .call id] :=
    .cons (.atomic (by trivial))
      (.cons (.atomic (by trivial)) (.cons (.importedCall imported) .nil))
  have executed :
      StructuredWasmExecutes module env initial
        { locals with values := tail }
        [.localGet firstIndex, .const constant, .call id]
        (.fallthrough final { locals with values := tail }) := by
    apply structuredWasmExecutes_fallthrough_of_wp
    let Q : Wasm.Assertion Host := fun continuation =>
      continuation = .Fallthrough final { locals with values := tail }
    have finalWP :
        Wasm.wp module [] Q final { locals with values := tail } env :=
      (Wasm.wp_nil).2 rfl
    simp only [Wasm.wp_localGet_cons]
    have firstFoundNext :
        ({ locals with values := tail } : Wasm.Locals).get firstIndex =
          some physicalFirst := by
      simpa [Wasm.Locals.get] using firstFound
    rw [firstFoundNext]
    simp only
    rw [Wasm.wp_const_cons]
    apply wp_exact_host_call_of_return
      (physicalArgs := [physicalFirst, .i32 constant]) (results := [])
      imported satisfies inBounds contracted
    · simp [parameterCount]
    · exact operation
    · convert finalWP using 1
      all_goals simp [parameterCount, resultCount]
  simpa using
    flat.finitePathWithSuffix (suffix := targetRest) (frames := frames)
      executed

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

/-- Rebuild the complete entry-relative cache frame after a same-witness heap
effect.  This is the common algebra behind reference-count and field-mutation
steps: the operation law supplies the executable effect, capacity and source
ownership transports, while this theorem preserves pure external handlers,
cache globals, immutable closure tables, and the cumulative entry relation. -/
theorem ReuseCapacityEntryRelativeFrame.ofReplaceHeapEffectStep
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {externals : ExternalImpl} {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {entryRuntime sourceRuntime nextRuntime : RuntimeState}
    {sourceEnv : Env}
    {entryStore targetStore : Wasm.Store Host} {heap : MemoryState}
    {targetLocals : Wasm.Locals}
    {entryWitness witness : RefinementWitness}
    {code continuation : Lean.Compiler.LCNF.Code .impure}
    {target targetRest : Wasm.Program}
    (invariant :
      ReuseCapacityEntryRelativeFrame
        (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals)
        entryRuntime entryStore entryWitness facts remainingBytes sourceRuntime
        sourceEnv targetStore targetLocals witness)
    (step :
      EffectStepSimulates context sourceModule sourceFunction labels module
        hostEnv sourceRuntime nextRuntime sourceEnv code continuation target
        targetRest targetStore (replaceHeap targetStore heap) targetLocals
        witness witness)
    (capacity :
      HeaderCapacityTransport targetStore.host.runtime.heap heap witness)
    (ordinary : OrdinaryPersistenceTransport sourceRuntime nextRuntime)
    (sourceGlobals : nextRuntime.globals = sourceRuntime.globals)
    (cursor : heap.heapCursor = targetStore.host.runtime.heap.heapCursor) :
    ReuseCapacityEntryRelativeFrame
      (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals)
      entryRuntime entryStore entryWitness facts remainingBytes nextRuntime
      sourceEnv (replaceHeap targetStore heap) targetLocals witness := by
  have currentBase := invariant.1.1.1.1
  have integerImplementation :
      targetStore.host.externals.IntegerResultRefines externals :=
    invariant.1.1.1.2.1
  have naturalImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        targetStore.host.externals externals :=
    invariant.1.1.1.2.2.1
  have scalarImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        targetStore.host.externals externals :=
    invariant.1.1.1.2.2.2
  have currentOwnership :
      ConcreteReuseCapacityOwnershipFrame sourceFunction facts remainingBytes
        sourceRuntime sourceEnv targetStore targetLocals witness :=
    ⟨currentBase, invariant.1.1.2⟩
  have nextOwnership :
      ConcreteReuseCapacityOwnershipFrame sourceFunction facts remainingBytes
        nextRuntime sourceEnv (replaceHeap targetStore heap) targetLocals
        witness :=
    currentOwnership.ofReplaceHeapEffectStep step capacity ordinary cursor
  have externalsEq :
      (replaceHeap targetStore heap).host.externals =
        targetStore.host.externals := by
    simp [replaceHeap, clearFailure]
  have nextIntegerImplementation :
      (replaceHeap targetStore heap).host.externals.IntegerResultRefines
        externals := by
    rw [externalsEq]
    exact @integerImplementation
  have nextNaturalImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
        (replaceHeap targetStore heap).host.externals externals := by
    rw [externalsEq]
    exact @naturalImplementation
  have nextScalarImplementation :
      FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
        (replaceHeap targetStore heap).host.externals externals := by
    rw [externalsEq]
    exact @scalarImplementation
  let transports :
      EffectStepTransports sourceRuntime nextRuntime targetStore
        (replaceHeap targetStore heap) witness witness :=
    EffectStepTransports.replaceHeap capacity ordinary sourceGlobals
  have nextCache :
      LazyCacheGlobalsRel witness sourceModule nextRuntime
        (replaceHeap targetStore heap) :=
    invariant.1.2.1.transport transports.witnessTransport
      transports.sourceGlobals transports.wasmGlobals
      transports.hostStaticLayout
  have nextClosureTables :
      ClosureTablesAgree (replaceHeap targetStore heap) witness :=
    transports.toClosureTablesTransport.agree invariant.1.2.2
  have nextEntry :
      ReuseCapacityCodeEntryTransports entryRuntime nextRuntime entryStore
        (replaceHeap targetStore heap) entryWitness witness :=
    invariant.2.step transports.witnessTransport
      transports.closureAllocationsPersistent transports.capacity
      transports.ordinary externalsEq transports.toClosureTablesTransport
  exact
    ⟨⟨⟨⟨nextOwnership.1, nextIntegerImplementation,
            nextNaturalImplementation, nextScalarImplementation⟩,
          nextOwnership.2⟩,
        nextCache, nextClosureTables⟩,
      nextEntry⟩

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

/-- A populated generated lazy-cache slot takes the exact five target steps
of the cache-hit path: load the published flag, enter and leave the empty
`then` arm, load the published value, and write the destination local.  The
miss body is retained syntactically but is not executed. -/
theorem structuredWasmLazyHitFinitePath
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {store : Wasm.Store Host} {locals nextLocals : Wasm.Locals}
    {flagIndex valueIndex resultIndex : Nat} {physical : Wasm.Value}
    {missBody rest : Wasm.Program} {frames : List StructuredWasmFrame}
    (tail : List Wasm.Value)
    (flagPublished :
      store.globals.globals[flagIndex]? = some (.i32 1))
    (valuePublished :
      store.globals.globals[valueIndex]? = some physical)
    (targetSet : locals.set? resultIndex physical = some nextLocals) :
    FinitePath (StructuredWasmStep module hostEnv) 5
      ⟨store, .running { locals with values := tail }
        ([.globalGet flagIndex, .iff 0 0 [] missBody,
            .globalGet valueIndex, .localSet resultIndex] ++ rest), frames⟩
      ⟨store, .running { nextLocals with values := tail } rest, frames⟩ := by
  let afterFlag : StructuredWasmState Host :=
    ⟨store,
      .running { locals with values := .i32 1 :: tail }
        ([.iff 0 0 [] missBody, .globalGet valueIndex,
          .localSet resultIndex] ++ rest),
      frames⟩
  let inThen : StructuredWasmState Host :=
    ⟨store, .running { locals with values := tail } [],
      .label 0 tail
          ([.globalGet valueIndex, .localSet resultIndex] ++ rest) :: frames⟩
  let afterThen : StructuredWasmState Host :=
    ⟨store, .running { locals with values := tail }
        ([.globalGet valueIndex, .localSet resultIndex] ++ rest), frames⟩
  let afterValue : StructuredWasmState Host :=
    ⟨store, .running { locals with values := physical :: tail }
        (.localSet resultIndex :: rest), frames⟩
  have loadFlag :
      StructuredWasmStep module hostEnv
        ⟨store, .running { locals with values := tail }
          ([.globalGet flagIndex, .iff 0 0 [] missBody,
              .globalGet valueIndex, .localSet resultIndex] ++ rest), frames⟩
        afterFlag := by
    apply StructuredWasmStep.atomic (fuel := 1)
    · trivial
    · simp only [Wasm.execOne.eq_def, flagPublished]
  have enterThen :
      StructuredWasmStep module hostEnv afterFlag inThen := by
    exact StructuredWasmStep.enterIffThen (by decide)
  have leaveThen :
      StructuredWasmStep module hostEnv inThen afterThen := by
    exact StructuredWasmStep.leaveLabel
  have loadValue :
      StructuredWasmStep module hostEnv afterThen afterValue := by
    apply StructuredWasmStep.atomic (fuel := 1)
    · trivial
    · simp only [Wasm.execOne.eq_def, valuePublished]
  have stackSet :
      ({ locals with values := physical :: tail }.set? resultIndex physical) =
        some { nextLocals with values := physical :: tail } :=
    locals_set?_with_values (physical :: tail) targetSet
  have setResult :
      StructuredWasmStep module hostEnv afterValue
        ⟨store, .running { nextLocals with values := tail } rest, frames⟩ := by
    apply StructuredWasmStep.atomic (fuel := 1)
    · trivial
    · simp only [Wasm.execOne.eq_def, stackSet]
  exact
    .cons loadFlag
      (.cons enterThen
        (.cons leaveThen (.cons loadValue (.cons setResult (.refl _)))))

/-- The generated cache-miss prefix loads an empty flag, enters the emitted
`else` body, and enters the selected internal initializer. -/
theorem structuredWasmLazyMissPrefixFinitePath
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {store : Wasm.Store Host} {locals : Wasm.Locals}
    {flagIndex valueIndex resultIndex declarationId cacheSetId : Nat}
    {function : Wasm.Function} {rest : Wasm.Program}
    {frames : List StructuredWasmFrame}
    (tail : List Wasm.Value)
    (flagEmpty : store.globals.globals[flagIndex]? = some (.i32 0))
    (notImport : module.imports[declarationId]? = none)
    (functionFound :
      module.funcs[declarationId - module.imports.length]? = some function)
    (parameterCount : function.numParams = 0)
    (resultCount : function.results.length = 1) :
    FinitePath (StructuredWasmStep module hostEnv) 3
      ⟨store, .running { locals with values := tail }
        ([.globalGet flagIndex,
          .iff 0 0 [] [
            .call declarationId,
            .call cacheSetId,
            .globalSet valueIndex,
            .const 1,
            .globalSet flagIndex],
          .globalGet valueIndex,
          .localSet resultIndex] ++ rest), frames⟩
      ⟨store, .running (function.toLocals []) function.body,
        .call 1 tail { locals with values := tail } [
            .call cacheSetId,
            .globalSet valueIndex,
            .const 1,
            .globalSet flagIndex] ::
          .label 0 tail
            ([.globalGet valueIndex, .localSet resultIndex] ++ rest) ::
            frames⟩ := by
  let afterFlag : StructuredWasmState Host :=
    ⟨store, .running { locals with values := .i32 0 :: tail }
      ([.iff 0 0 [] [
          .call declarationId,
          .call cacheSetId,
          .globalSet valueIndex,
          .const 1,
          .globalSet flagIndex],
        .globalGet valueIndex,
        .localSet resultIndex] ++ rest), frames⟩
  let inElse : StructuredWasmState Host :=
    ⟨store, .running { locals with values := tail } [
        .call declarationId,
        .call cacheSetId,
        .globalSet valueIndex,
        .const 1,
        .globalSet flagIndex],
      .label 0 tail
        ([.globalGet valueIndex, .localSet resultIndex] ++ rest) :: frames⟩
  have loadFlag :
      StructuredWasmStep module hostEnv
        ⟨store, .running { locals with values := tail }
          ([.globalGet flagIndex,
            .iff 0 0 [] [
              .call declarationId,
              .call cacheSetId,
              .globalSet valueIndex,
              .const 1,
              .globalSet flagIndex],
            .globalGet valueIndex,
            .localSet resultIndex] ++ rest), frames⟩
        afterFlag := by
    apply StructuredWasmStep.atomic (fuel := 1)
    · trivial
    · simp only [Wasm.execOne.eq_def, flagEmpty]
  have enterElse : StructuredWasmStep module hostEnv afterFlag inElse := by
    exact StructuredWasmStep.enterIffElse
  have enterCall :
      StructuredWasmStep module hostEnv inElse
        ⟨store, .running (function.toLocals []) function.body,
          .call 1 tail { locals with values := tail } [
              .call cacheSetId,
              .globalSet valueIndex,
              .const 1,
              .globalSet flagIndex] ::
            .label 0 tail
              ([.globalGet valueIndex, .localSet resultIndex] ++ rest) ::
              frames⟩ := by
    simpa [inElse, parameterCount, resultCount] using
      (StructuredWasmStep.enterCall (env := hostEnv)
        (module := module) (store := store)
        (locals := { locals with values := tail })
        (rest := [
          .call cacheSetId,
          .globalSet valueIndex,
          .const 1,
          .globalSet flagIndex])
        (frames :=
          .label 0 tail
            (.globalGet valueIndex :: .localSet resultIndex :: rest) :: frames)
        notImport functionFound)
  exact .cons loadFlag (.cons enterElse (.cons enterCall (.refl _)))

/-- After a generated initializer returns, the structured machine performs
the value-preserving concrete cache update, publishes the physical value and
the populated flag, exits the conditional, reloads the value, and writes the
caller's destination local. -/
theorem structuredWasmLazyMissSuffixFinitePath
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host}
    {cacheSetId : Nat} {imp : Wasm.ImportDecl}
    {declaration : Lean.Name} {kind : AbiKind}
    {afterCall afterCache valueStore : Wasm.Store Host}
    {callerLocals calleeLocals nextLocals : Wasm.Locals}
    {physical oldValue oldFlag : Wasm.Value}
    {flagIndex valueIndex resultIndex : Nat}
    {rest : Wasm.Program} {frames : List StructuredWasmFrame}
    (tail : List Wasm.Value)
    (importFound : module.imports[cacheSetId]? = some imp)
    (hostSatisfies : hostEnv.Satisfies module spec)
    (importInBounds : cacheSetId < module.imports.length)
    (contractFound :
      spec.contracts[cacheSetId]? =
        some (cacheSetContract declaration kind))
    (parameterCount : imp.params.length = 1)
    (resultCount : imp.results.length = 1)
    (operation :
      cacheSetStep declaration kind afterCall [physical] =
        .Return [physical] afterCache)
    (valueGlobal :
      afterCache.globals.globals[valueIndex]? = some oldValue)
    (valueStoreEq :
      valueStore = writeWasmGlobal afterCache valueIndex physical)
    (flagGlobal :
      valueStore.globals.globals[flagIndex]? = some oldFlag)
    (distinct : valueIndex ≠ flagIndex)
    (targetSet : callerLocals.set? resultIndex physical = some nextLocals) :
    FinitePath (StructuredWasmStep module hostEnv) 8
      ⟨afterCall, .returning (physical :: calleeLocals.values),
        .call 1 tail { callerLocals with values := tail } [
            .call cacheSetId,
            .globalSet valueIndex,
            .const 1,
            .globalSet flagIndex] ::
          .label 0 tail
            ([.globalGet valueIndex, .localSet resultIndex] ++ rest) ::
            frames⟩
      ⟨writeWasmGlobal valueStore flagIndex (.i32 1),
        .running { nextLocals with values := tail } rest, frames⟩ := by
  let afterReturn : StructuredWasmState Host :=
    ⟨afterCall,
      .running { callerLocals with values := physical :: tail } [
        .call cacheSetId,
        .globalSet valueIndex,
        .const 1,
        .globalSet flagIndex],
      .label 0 tail
        ([.globalGet valueIndex, .localSet resultIndex] ++ rest) :: frames⟩
  let afterHost : StructuredWasmState Host :=
    ⟨afterCache,
      .running { callerLocals with values := physical :: tail } [
        .globalSet valueIndex,
        .const 1,
        .globalSet flagIndex],
      .label 0 tail
        ([.globalGet valueIndex, .localSet resultIndex] ++ rest) :: frames⟩
  let afterValue : StructuredWasmState Host :=
    ⟨valueStore,
      .running { callerLocals with values := tail }
        [.const 1, .globalSet flagIndex],
      .label 0 tail
        ([.globalGet valueIndex, .localSet resultIndex] ++ rest) :: frames⟩
  let afterConst : StructuredWasmState Host :=
    ⟨valueStore,
      .running { callerLocals with values := .i32 1 :: tail }
        [.globalSet flagIndex],
      .label 0 tail
        ([.globalGet valueIndex, .localSet resultIndex] ++ rest) :: frames⟩
  let published := writeWasmGlobal valueStore flagIndex (.i32 1)
  let afterFlag : StructuredWasmState Host :=
    ⟨published, .running { callerLocals with values := tail } [],
      .label 0 tail
        ([.globalGet valueIndex, .localSet resultIndex] ++ rest) :: frames⟩
  let afterLabel : StructuredWasmState Host :=
    ⟨published,
      .running { callerLocals with values := tail }
        ([.globalGet valueIndex, .localSet resultIndex] ++ rest), frames⟩
  let afterReload : StructuredWasmState Host :=
    ⟨published,
      .running { callerLocals with values := physical :: tail }
        (.localSet resultIndex :: rest), frames⟩
  have returnToCaller :
      StructuredWasmStep module hostEnv
        ⟨afterCall, .returning (physical :: calleeLocals.values),
          .call 1 tail { callerLocals with values := tail } [
              .call cacheSetId,
              .globalSet valueIndex,
              .const 1,
              .globalSet flagIndex] ::
            .label 0 tail
              ([.globalGet valueIndex, .localSet resultIndex] ++ rest) ::
              frames⟩
        afterReturn := by
    simpa [afterReturn] using
      (StructuredWasmStep.returnCall (module := module) (env := hostEnv)
        (values := physical :: calleeLocals.values) (resultArity := 1)
        (callerRemainder := tail)
        (callerLocals := { callerLocals with values := tail })
        (rest := [.call cacheSetId, .globalSet valueIndex, .const 1,
          .globalSet flagIndex])
        (frames := .label 0 tail
          (.globalGet valueIndex :: .localSet resultIndex :: rest) :: frames))
  obtain ⟨hostFunction, hostFound, hostContract⟩ :=
    hostSatisfies.lookup_contract importInBounds contractFound
  have invoked :
      hostFunction.invoke afterCall [physical] =
        .Return [physical] afterCache := by
    have contract := hostContract afterCall [physical]
    change hostFunction.invoke afterCall [physical] =
      cacheSetStep declaration kind afterCall [physical] at contract
    rw [operation] at contract
    exact contract
  have callHost :
      StructuredWasmStep module hostEnv afterReturn afterHost := by
    apply StructuredWasmStep.importedCall (fuel := 1) importFound
    simp only [Wasm.execOne.eq_def, Wasm.run,
      importFound, hostFound, parameterCount, resultCount, invoked,
      List.take, List.drop, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append]
  have storeValue :
      StructuredWasmStep module hostEnv afterHost afterValue := by
    apply StructuredWasmStep.atomic (fuel := 1)
    · trivial
    · subst valueStore
      simp only [Wasm.execOne.eq_def, valueGlobal, writeWasmGlobal]
  have pushFlag :
      StructuredWasmStep module hostEnv afterValue afterConst := by
    apply StructuredWasmStep.atomic (fuel := 1)
    · trivial
    · simp only [Wasm.execOne.eq_def]
  have storeFlag :
      StructuredWasmStep module hostEnv afterConst afterFlag := by
    apply StructuredWasmStep.atomic (fuel := 1)
    · trivial
    · simp only [published, Wasm.execOne.eq_def, flagGlobal, writeWasmGlobal]
  have leaveConditional :
      StructuredWasmStep module hostEnv afterFlag afterLabel := by
    simpa [afterFlag, afterLabel, published] using
      (StructuredWasmStep.leaveLabel (module := module) (env := hostEnv)
        (resultArity := 0) (belowStack := tail)
        (rest := .globalGet valueIndex :: .localSet resultIndex :: rest)
        (store := published) (locals := { callerLocals with values := tail })
        (frames := frames))
  have valueAtValueStore :
      valueStore.globals.globals[valueIndex]? = some physical := by
    rw [valueStoreEq]
    exact writeWasmGlobal_get_self valueGlobal
  have valuePublished :
      published.globals.globals[valueIndex]? = some physical := by
    simp only [published]
    rw [writeWasmGlobal_get_ne distinct.symm]
    exact valueAtValueStore
  have reloadValue :
      StructuredWasmStep module hostEnv afterLabel afterReload := by
    apply StructuredWasmStep.atomic (fuel := 1)
    · trivial
    · simp only [Wasm.execOne.eq_def, valuePublished]
  have stackSet :
      ({ callerLocals with values := physical :: tail }.set? resultIndex
          physical) = some { nextLocals with values := physical :: tail } :=
    locals_set?_with_values (physical :: tail) targetSet
  have setResult :
      StructuredWasmStep module hostEnv afterReload
        ⟨published, .running { nextLocals with values := tail } rest,
          frames⟩ := by
    apply StructuredWasmStep.atomic (fuel := 1)
    · trivial
    · simp only [Wasm.execOne.eq_def, stackSet]
  exact .cons returnToCaller
    (.cons callHost
      (.cons storeValue
        (.cons pushFlag
          (.cons storeFlag
            (.cons leaveConditional
              (.cons reloadValue (.cons setResult (.refl _))))))))

/-- A successful object-case test emitted by the compiler takes five
structured steps before entering its selected arm: local read, concrete tag
import, expected-tag constant, equality, and conditional entry. -/
theorem structuredWasmObjectCaseHitPrefixFinitePath
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {store : Wasm.Store Host}
    {locals : Wasm.Locals} {frames : List StructuredWasmFrame}
    {thenTarget elseTarget : Wasm.Program} {discrIndex getTagIndex : Nat}
    {imp : Wasm.ImportDecl} {word : Word32} {actualTag expectedTag : Nat}
    (tagEq : actualTag = expectedTag)
    (localFound :
      locals.get discrIndex =
        some (.i32 (UInt32.ofNat word.value)))
    (importFound : module.imports[getTagIndex]? = some imp)
    (hostSatisfies : hostEnv.Satisfies module spec)
    (importInBounds : getTagIndex < module.imports.length)
    (contractFound : spec.contracts[getTagIndex]? = some getTagContract)
    (parameterCount : imp.params.length = 1)
    (resultCount : imp.results.length = 1)
    (operation :
      getTagStep store [.i32 (UInt32.ofNat word.value)] =
        .Return [.i32 (UInt32.ofNat actualTag)] store) :
    FinitePath (StructuredWasmStep module hostEnv) 5
      ⟨store, .running locals [
          .localGet discrIndex,
          .call getTagIndex,
          .const (UInt32.ofNat expectedTag),
          .eq,
          .iff 0 0 thenTarget elseTarget], frames⟩
      ⟨store, .running { locals with values := locals.values } thenTarget,
        .label 0 (locals.values.drop 0) [] :: frames⟩ := by
  let afterLocal : StructuredWasmState Host :=
    ⟨store,
      .running { locals with
        values := .i32 (UInt32.ofNat word.value) :: locals.values } [
          .call getTagIndex,
          .const (UInt32.ofNat expectedTag),
          .eq,
          .iff 0 0 thenTarget elseTarget],
      frames⟩
  let afterHost : StructuredWasmState Host :=
    ⟨store,
      .running { locals with
        values := .i32 (UInt32.ofNat actualTag) :: locals.values } [
          .const (UInt32.ofNat expectedTag),
          .eq,
          .iff 0 0 thenTarget elseTarget],
      frames⟩
  let afterConst : StructuredWasmState Host :=
    ⟨store,
      .running { locals with values :=
        (.i32 (UInt32.ofNat expectedTag) ::
          .i32 (UInt32.ofNat actualTag) :: locals.values) } [
          .eq,
          .iff 0 0 thenTarget elseTarget],
      frames⟩
  let afterEq : StructuredWasmState Host :=
    ⟨store,
      .running { locals with values := .i32 1 :: locals.values }
        [.iff 0 0 thenTarget elseTarget],
      frames⟩
  have loadLocal :
      StructuredWasmStep module hostEnv
        ⟨store, .running locals [
            .localGet discrIndex,
            .call getTagIndex,
            .const (UInt32.ofNat expectedTag),
            .eq,
            .iff 0 0 thenTarget elseTarget], frames⟩
        afterLocal := by
    apply StructuredWasmStep.atomic (fuel := 1)
    · trivial
    · simp only [Wasm.execOne.eq_def, localFound]
  obtain ⟨hostFunction, hostFound, hostContract⟩ :=
    hostSatisfies.lookup_contract importInBounds contractFound
  have invoked :
      hostFunction.invoke store [.i32 (UInt32.ofNat word.value)] =
        .Return [.i32 (UInt32.ofNat actualTag)] store := by
    have contract :=
      hostContract store [.i32 (UInt32.ofNat word.value)]
    change hostFunction.invoke store [.i32 (UInt32.ofNat word.value)] =
      getTagStep store [.i32 (UInt32.ofNat word.value)] at contract
    rw [operation] at contract
    exact contract
  have callHost :
      StructuredWasmStep module hostEnv afterLocal afterHost := by
    apply StructuredWasmStep.importedCall (fuel := 1) importFound
    simp only [Wasm.execOne.eq_def, Wasm.run,
      importFound, hostFound, parameterCount, resultCount, invoked,
      List.take, List.drop, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append]
  have pushExpected :
      StructuredWasmStep module hostEnv afterHost afterConst := by
    apply StructuredWasmStep.atomic (fuel := 1)
    · trivial
    · simp only [Wasm.execOne.eq_def]
  have compare : StructuredWasmStep module hostEnv afterConst afterEq := by
    apply StructuredWasmStep.atomic (fuel := 1)
    · trivial
    · simp [Wasm.execOne.eq_def, tagEq]
  have enterSelected :
      StructuredWasmStep module hostEnv afterEq
        ⟨store,
          .running { locals with values := locals.values } thenTarget,
          .label 0 (locals.values.drop 0) [] :: frames⟩ := by
    simpa only [afterEq] using
      (StructuredWasmStep.enterIffThen (module := module) (env := hostEnv)
        (store := store) (locals := locals) (thenBody := thenTarget)
        (elseBody := elseTarget) (rest := []) (frames := frames)
        (condition := 1) (by decide))
  exact .cons loadLocal
    (.cons callHost
      (.cons pushExpected
        (.cons compare (.cons enterSelected (.refl _)))))

/-- A failed object-case test takes the same five generated steps and enters
the recursively compiled remainder of the ordered case chain. -/
theorem structuredWasmObjectCaseMissPrefixFinitePath
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {store : Wasm.Store Host}
    {locals : Wasm.Locals} {frames : List StructuredWasmFrame}
    {thenTarget elseTarget : Wasm.Program} {discrIndex getTagIndex : Nat}
    {imp : Wasm.ImportDecl} {word : Word32} {actualTag expectedTag : Nat}
    (tagNe : actualTag ≠ expectedTag)
    (actualFits : actualTag < UInt32.size)
    (expectedFits : expectedTag < UInt32.size)
    (localFound :
      locals.get discrIndex =
        some (.i32 (UInt32.ofNat word.value)))
    (importFound : module.imports[getTagIndex]? = some imp)
    (hostSatisfies : hostEnv.Satisfies module spec)
    (importInBounds : getTagIndex < module.imports.length)
    (contractFound : spec.contracts[getTagIndex]? = some getTagContract)
    (parameterCount : imp.params.length = 1)
    (resultCount : imp.results.length = 1)
    (operation :
      getTagStep store [.i32 (UInt32.ofNat word.value)] =
        .Return [.i32 (UInt32.ofNat actualTag)] store) :
    FinitePath (StructuredWasmStep module hostEnv) 5
      ⟨store, .running locals [
          .localGet discrIndex,
          .call getTagIndex,
          .const (UInt32.ofNat expectedTag),
          .eq,
          .iff 0 0 thenTarget elseTarget], frames⟩
      ⟨store, .running { locals with values := locals.values } elseTarget,
        .label 0 (locals.values.drop 0) [] :: frames⟩ := by
  let afterLocal : StructuredWasmState Host :=
    ⟨store,
      .running { locals with
        values := .i32 (UInt32.ofNat word.value) :: locals.values } [
          .call getTagIndex,
          .const (UInt32.ofNat expectedTag),
          .eq,
          .iff 0 0 thenTarget elseTarget],
      frames⟩
  let afterHost : StructuredWasmState Host :=
    ⟨store,
      .running { locals with
        values := .i32 (UInt32.ofNat actualTag) :: locals.values } [
          .const (UInt32.ofNat expectedTag),
          .eq,
          .iff 0 0 thenTarget elseTarget],
      frames⟩
  let afterConst : StructuredWasmState Host :=
    ⟨store,
      .running { locals with values :=
        (.i32 (UInt32.ofNat expectedTag) ::
          .i32 (UInt32.ofNat actualTag) :: locals.values) } [
          .eq,
          .iff 0 0 thenTarget elseTarget],
      frames⟩
  let afterEq : StructuredWasmState Host :=
    ⟨store,
      .running { locals with values := .i32 0 :: locals.values }
        [.iff 0 0 thenTarget elseTarget],
      frames⟩
  have loadLocal :
      StructuredWasmStep module hostEnv
        ⟨store, .running locals [
            .localGet discrIndex,
            .call getTagIndex,
            .const (UInt32.ofNat expectedTag),
            .eq,
            .iff 0 0 thenTarget elseTarget], frames⟩
        afterLocal := by
    apply StructuredWasmStep.atomic (fuel := 1)
    · trivial
    · simp only [Wasm.execOne.eq_def, localFound]
  obtain ⟨hostFunction, hostFound, hostContract⟩ :=
    hostSatisfies.lookup_contract importInBounds contractFound
  have invoked :
      hostFunction.invoke store [.i32 (UInt32.ofNat word.value)] =
        .Return [.i32 (UInt32.ofNat actualTag)] store := by
    have contract :=
      hostContract store [.i32 (UInt32.ofNat word.value)]
    change hostFunction.invoke store [.i32 (UInt32.ofNat word.value)] =
      getTagStep store [.i32 (UInt32.ofNat word.value)] at contract
    rw [operation] at contract
    exact contract
  have callHost :
      StructuredWasmStep module hostEnv afterLocal afterHost := by
    apply StructuredWasmStep.importedCall (fuel := 1) importFound
    simp only [Wasm.execOne.eq_def, Wasm.run,
      importFound, hostFound, parameterCount, resultCount, invoked,
      List.take, List.drop, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append]
  have pushExpected :
      StructuredWasmStep module hostEnv afterHost afterConst := by
    apply StructuredWasmStep.atomic (fuel := 1)
    · trivial
    · simp only [Wasm.execOne.eq_def]
  have physicalDifferent :
      UInt32.ofNat actualTag ≠ UInt32.ofNat expectedTag := by
    intro physicalEqual
    exact tagNe <|
      (constructorTag_i32_eq_iff actualFits expectedFits).mp physicalEqual
  have compare : StructuredWasmStep module hostEnv afterConst afterEq := by
    apply StructuredWasmStep.atomic (fuel := 1)
    · trivial
    · simp [Wasm.execOne.eq_def, physicalDifferent]
  have enterRemainder :
      StructuredWasmStep module hostEnv afterEq
        ⟨store,
          .running { locals with values := locals.values } elseTarget,
          .label 0 (locals.values.drop 0) [] :: frames⟩ := by
    simpa only [afterEq] using
      (StructuredWasmStep.enterIffElse (module := module) (env := hostEnv)
        (store := store) (locals := locals) (thenBody := thenTarget)
        (elseBody := elseTarget) (rest := []) (frames := frames))
  exact .cons loadLocal
    (.cons callHost
      (.cons pushExpected
        (.cons compare (.cons enterRemainder (.refl _)))))

/-- A related scalar `UInt8` discriminator occupies its direct i32 lane with
exactly the semantic tag selected by FIR. -/
theorem scalarUInt8Local_eq_of_related
    {sourceFunction : Fir.Wasm.Function}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {targetStore : Wasm.Store Host} {targetLocals : Wasm.Locals}
    {witness : RefinementWitness} {discr : Lean.FVarId}
    {discrIndex : Nat} {sourceValue : Value} {actualTag : Nat}
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv targetStore
        targetLocals witness)
    (sourceLookup : lookup sourceEnv discr = some sourceValue)
    (discrFound :
      findFVar? (functionBindings sourceFunction) discr = some discrIndex)
    (discrKind :
      (functionBindings sourceFunction)[discrIndex]?.map Prod.snd =
        some .uint8)
    (tagged : getTag sourceRuntime sourceValue = .ok actualTag) :
    targetLocals.get discrIndex =
        some (.i32 (UInt32.ofNat actualTag)) ∧
      actualTag < UInt8.size := by
  obtain ⟨index, kind, physical, found, kindAt, localValue,
      physicalRelated⟩ := stateRelated.2.2 sourceLookup
  rw [discrFound] at found
  have indexEq := Option.some.inj found
  subst index
  rw [discrKind] at kindAt
  have kindEq := Option.some.inj kindAt
  subst kind
  cases physicalRelated with
  | word32 valueRelated =>
      cases valueRelated with
      | @uint8 word value encoded =>
          have fits64 : value.toNat < UInt64.size := by
            have sizeLe : UInt8.size ≤ UInt64.size := by native_decide
            exact lt_of_lt_of_le (UInt8.toNat_lt_size value) sizeLe
          have valueToNat :
              (UInt64.ofNat value.toNat).toNat = value.toNat :=
            UInt64.toNat_ofNat_of_lt' fits64
          have tagEq : actualTag = value.toNat := by
            simpa [getTag, ScalarValue.toUInt64, ScalarValue.rawBits,
              valueToNat] using tagged.symm
          subst actualTag
          exact ⟨by simpa [Wasm.Locals.get, encoded] using localValue,
            UInt8.toNat_lt_size value⟩
  | word64 valueRelated => cases valueRelated
  | float32Bits valueRelated => cases valueRelated
  | float64Bits valueRelated => cases valueRelated

/-- A successful scalar `UInt8` constructor test takes four structured steps:
local read, expected-tag constant, equality, and conditional entry. -/
theorem structuredWasmScalarUInt8CaseHitPrefixFinitePath
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {store : Wasm.Store Host} {locals : Wasm.Locals}
    {frames : List StructuredWasmFrame}
    {thenTarget elseTarget : Wasm.Program} {discrIndex : Nat}
    {actualTag expectedTag : Nat}
    (tagEq : actualTag = expectedTag)
    (localFound :
      locals.get discrIndex = some (.i32 (UInt32.ofNat actualTag))) :
    FinitePath (StructuredWasmStep module hostEnv) 4
      ⟨store, .running locals [
          .localGet discrIndex,
          .const (UInt32.ofNat expectedTag),
          .eq,
          .iff 0 0 thenTarget elseTarget], frames⟩
      ⟨store, .running { locals with values := locals.values } thenTarget,
        .label 0 (locals.values.drop 0) [] :: frames⟩ := by
  let afterLocal : StructuredWasmState Host :=
    ⟨store,
      .running { locals with
        values := .i32 (UInt32.ofNat actualTag) :: locals.values } [
          .const (UInt32.ofNat expectedTag),
          .eq,
          .iff 0 0 thenTarget elseTarget],
      frames⟩
  let afterConst : StructuredWasmState Host :=
    ⟨store,
      .running { locals with values :=
        (.i32 (UInt32.ofNat expectedTag) ::
          .i32 (UInt32.ofNat actualTag) :: locals.values) } [
          .eq,
          .iff 0 0 thenTarget elseTarget],
      frames⟩
  let afterEq : StructuredWasmState Host :=
    ⟨store,
      .running { locals with values := .i32 1 :: locals.values }
        [.iff 0 0 thenTarget elseTarget],
      frames⟩
  have loadLocal :
      StructuredWasmStep module hostEnv
        ⟨store, .running locals [
            .localGet discrIndex,
            .const (UInt32.ofNat expectedTag),
            .eq,
            .iff 0 0 thenTarget elseTarget], frames⟩
        afterLocal := by
    apply StructuredWasmStep.atomic (fuel := 1)
    · trivial
    · simp only [Wasm.execOne.eq_def, localFound]
  have pushExpected :
      StructuredWasmStep module hostEnv afterLocal afterConst := by
    apply StructuredWasmStep.atomic (fuel := 1)
    · trivial
    · simp only [Wasm.execOne.eq_def]
  have compare : StructuredWasmStep module hostEnv afterConst afterEq := by
    apply StructuredWasmStep.atomic (fuel := 1)
    · trivial
    · simp [Wasm.execOne.eq_def, tagEq]
  have enterSelected :
      StructuredWasmStep module hostEnv afterEq
        ⟨store,
          .running { locals with values := locals.values } thenTarget,
          .label 0 (locals.values.drop 0) [] :: frames⟩ := by
    simpa only [afterEq] using
      (StructuredWasmStep.enterIffThen (module := module) (env := hostEnv)
        (store := store) (locals := locals) (thenBody := thenTarget)
        (elseBody := elseTarget) (rest := []) (frames := frames)
        (condition := 1) (by decide))
  exact .cons loadLocal
    (.cons pushExpected
      (.cons compare (.cons enterSelected (.refl _))))

/-- A failed scalar `UInt8` constructor test takes four steps and enters the
recursively compiled remainder of the case chain. -/
theorem structuredWasmScalarUInt8CaseMissPrefixFinitePath
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {store : Wasm.Store Host} {locals : Wasm.Locals}
    {frames : List StructuredWasmFrame}
    {thenTarget elseTarget : Wasm.Program} {discrIndex : Nat}
    {actualTag expectedTag : Nat}
    (tagNe : actualTag ≠ expectedTag)
    (actualFits : actualTag < UInt8.size)
    (expectedFits : expectedTag < UInt8.size)
    (localFound :
      locals.get discrIndex = some (.i32 (UInt32.ofNat actualTag))) :
    FinitePath (StructuredWasmStep module hostEnv) 4
      ⟨store, .running locals [
          .localGet discrIndex,
          .const (UInt32.ofNat expectedTag),
          .eq,
          .iff 0 0 thenTarget elseTarget], frames⟩
      ⟨store, .running { locals with values := locals.values } elseTarget,
        .label 0 (locals.values.drop 0) [] :: frames⟩ := by
  let afterLocal : StructuredWasmState Host :=
    ⟨store,
      .running { locals with
        values := .i32 (UInt32.ofNat actualTag) :: locals.values } [
          .const (UInt32.ofNat expectedTag),
          .eq,
          .iff 0 0 thenTarget elseTarget],
      frames⟩
  let afterConst : StructuredWasmState Host :=
    ⟨store,
      .running { locals with values :=
        (.i32 (UInt32.ofNat expectedTag) ::
          .i32 (UInt32.ofNat actualTag) :: locals.values) } [
          .eq,
          .iff 0 0 thenTarget elseTarget],
      frames⟩
  let afterEq : StructuredWasmState Host :=
    ⟨store,
      .running { locals with values := .i32 0 :: locals.values }
        [.iff 0 0 thenTarget elseTarget],
      frames⟩
  have loadLocal :
      StructuredWasmStep module hostEnv
        ⟨store, .running locals [
            .localGet discrIndex,
            .const (UInt32.ofNat expectedTag),
            .eq,
            .iff 0 0 thenTarget elseTarget], frames⟩
        afterLocal := by
    apply StructuredWasmStep.atomic (fuel := 1)
    · trivial
    · simp only [Wasm.execOne.eq_def, localFound]
  have pushExpected :
      StructuredWasmStep module hostEnv afterLocal afterConst := by
    apply StructuredWasmStep.atomic (fuel := 1)
    · trivial
    · simp only [Wasm.execOne.eq_def]
  have physicalDifferent :
      UInt32.ofNat actualTag ≠ UInt32.ofNat expectedTag := by
    intro physicalEqual
    exact tagNe <|
      (constructorTag_uint8_eq_iff actualFits expectedFits).mp physicalEqual
  have compare : StructuredWasmStep module hostEnv afterConst afterEq := by
    apply StructuredWasmStep.atomic (fuel := 1)
    · trivial
    · simp [Wasm.execOne.eq_def, physicalDifferent]
  have enterRemainder :
      StructuredWasmStep module hostEnv afterEq
        ⟨store,
          .running { locals with values := locals.values } elseTarget,
          .label 0 (locals.values.drop 0) [] :: frames⟩ := by
    simpa only [afterEq] using
      (StructuredWasmStep.enterIffElse (module := module) (env := hostEnv)
        (store := store) (locals := locals) (thenBody := thenTarget)
        (elseBody := elseTarget) (rest := []) (frames := frames))
  exact .cons loadLocal
    (.cons pushExpected
      (.cons compare (.cons enterRemainder (.refl _))))

/-- Returning through `count` nested generated case conditionals pops exactly
`count` empty-result label frames and preserves the enclosing frame stack. -/
theorem structuredWasmReturnReplicatedCaseLabelsFinitePath
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {store : Wasm.Store Host} {values belowStack : List Wasm.Value}
    {frames : List StructuredWasmFrame} (count : Nat) :
    FinitePath (StructuredWasmStep module hostEnv) count
      ⟨store, .returning values,
        List.replicate count (.label 0 belowStack []) ++ frames⟩
      ⟨store, .returning values, frames⟩ := by
  induction count with
  | zero => exact .refl _
  | succ count ih =>
      rw [List.replicate_succ]
      exact .cons
        (StructuredWasmStep.returnLabel
          (module := module) (env := hostEnv) (values := values)
          (resultArity := 0) (belowStack := belowStack) (rest := [])
          (store := store)
          (frames := List.replicate count
            (StructuredWasmFrame.label 0 belowStack []) ++ frames))
        ih

/-- Appending one more copy to a replicated prefix is insensitive to whether
that copy is exposed at the front or at the end of the identical prefix. -/
theorem List.replicate_succ_append
    {α : Type} (value : α) (count : Nat) (tail : List α) :
    List.replicate (count + 1) value ++ tail =
      List.replicate count value ++ value :: tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa only [Nat.succ_eq_add_one, List.replicate_succ,
        List.cons_append, List.cons.injEq, true_and] using ih

/-- Exact structured path through an arbitrary normalized object-constructor
case chain. Production compiler inversion supplies every generated branch and
test. Source selection determines how many five-step tests execute; the
result retains one empty-result label for each of those tests. -/
theorem ConcreteSupportedFunction.objectConstructorCaseChainFinitePath
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context sourceCode sourceModule
        sourceFunction target hosts)
    {labels : List Lean.FVarId}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {discr : Lean.FVarId} {alts : List (Lean.Compiler.LCNF.Alt .impure)}
    {fallback : List Fir.Wasm.Instruction} {chainTarget : Wasm.Program}
    {selected : Lean.Compiler.LCNF.Code .impure}
    {targetStore : Wasm.Store Host} {targetLocals : Wasm.Locals}
    {witness : RefinementWitness} {sourceObject : Value} {actualTag : Nat}
    {frames : List StructuredWasmFrame}
    (supported : ObjectConstructorCaseAltsSupported alts)
    (modeEq : Fir.Wasm.caseDiscriminatorMode context discr = .objectTag)
    (discrCompiled :
      Fir.Wasm.getLocal context discr = .ok (.localGet discr, .tobject))
    (selection : chooseAlt actualTag alts = some selected)
    (sourceLookup : lookup sourceEnv discr = some sourceObject)
    (tagged : getTag sourceRuntime sourceObject = .ok actualTag)
    (actualFits : actualTag < UInt32.size)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv targetStore
        targetLocals witness)
    (fallbackCompiled :
      Fir.Wasm.compileCaseFallback context alts = .ok fallback)
    (chainAdapted :
      CaseChainAdapted context sourceModule sourceFunction labels discr alts
        fallback chainTarget) :
    ∃ selectedTarget testCount,
      CodeAdapted context sourceModule sourceFunction labels selected
          selectedTarget ∧
        FinitePath (StructuredWasmStep target.wasmModule hosts.env)
          (5 * testCount)
          ⟨targetStore, .running targetLocals chainTarget, frames⟩
          ⟨targetStore,
            .running { targetLocals with values := targetLocals.values }
              selectedTarget,
            List.replicate testCount
                (.label 0 (targetLocals.values.drop 0) []) ++ frames⟩ := by
  induction supported generalizing chainTarget selected frames with
  | nil =>
      simp [chooseAlt, findCtorAlt, findDefaultAlt] at selection
  | default code =>
      have selectedEq : selected = code := by
        simpa [chooseAlt, findCtorAlt, findDefaultAlt] using selection.symm
      subst selected
      have branchCompiled :
          Fir.Wasm.compileCode context code = .ok fallback := by
        simpa [Fir.Wasm.compileCaseFallback,
          Fir.Wasm.compileCaseFallbackWithM, Fir.Wasm.isDefaultAlt]
          using fallbackCompiled
      have branchAdapted :
          CodeAdapted context sourceModule sourceFunction labels code
            chainTarget :=
        ⟨fallback, branchCompiled,
          CaseChainAdapted.nil_eq
            (CaseChainAdapted.default_eq chainAdapted)⟩
      exact ⟨chainTarget, 0, branchAdapted, .refl _⟩
  | @ctor info alts code fits rest ih =>
      have fallbackCompiledRest :
          Fir.Wasm.compileCaseFallback context alts = .ok fallback := by
        simpa [Fir.Wasm.compileCaseFallback,
          Fir.Wasm.compileCaseFallbackWithM, Fir.Wasm.isDefaultAlt]
          using fallbackCompiled
      obtain ⟨thenTarget, elseTarget, discrIndex, getTagIndex, thenAdapted,
          elseAdapted, discrFound, getTagFound, targetEq⟩ :=
        CaseChainAdapted.objectConstructor_eq modeEq fits chainAdapted
      obtain ⟨alignedIndex, alignedFound, discrKind⟩ :=
        spec.localsAligned discrCompiled
      rw [discrFound] at alignedFound
      have alignedEq : alignedIndex = discrIndex :=
        Option.some.inj alignedFound.symm
      subst alignedIndex
      obtain ⟨discrPhysical, targetLookup, physicalRelated⟩ :=
        stateRelated.resolve sourceLookup discrFound discrKind
      obtain ⟨word, physicalEq, objectRelated⟩ :
          ∃ word : Word32,
            discrPhysical = .i32 (UInt32.ofNat word.value) ∧
              ValueRel witness .tobject (.word32 word) sourceObject := by
        cases physicalRelated with
        | word32 valueRelated => exact ⟨_, rfl, valueRelated⟩
        | word64 valueRelated => cases valueRelated
        | float32Bits valueRelated => cases valueRelated
        | float64Bits valueRelated => cases valueRelated
      subst discrPhysical
      obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
        spec.runtimeCallsAligned getTagFound
      have getTagContracted :
          hosts.spec.contracts[getTagIndex]? = some getTagContract := by
        change hosts.spec.contracts[getTagIndex]? =
          some (fun initial args result => result = getTagStep initial args)
        simpa only [resolvedContract?, hostFn?, Option.map_some, getTagFn]
          using contracted
      have parameterCount : imp.params.length = 1 := by
        change imp.params.length = 1 at params
        exact params
      have resultCount : imp.results.length = 1 := by
        change imp.results.length = 1 at results
        exact results
      have expectedFits : info.cidx < UInt32.size := by
        simpa [Fir.Wasm.constructorTagFitsI32] using fits
      have tagOperation :
          getTagStep targetStore [.i32 (UInt32.ofNat word.value)] =
            .Return [.i32 (UInt32.ofNat actualTag)] targetStore := by
        have operation :=
          getTagStep_of_refines stateRelated.1 objectRelated tagged actualFits
        rw [stateRelated.clearFailure] at operation
        exact operation
      by_cases hit : actualTag = info.cidx
      · have selectedEq : selected = code := by
          have branchEq : code = selected := by
            simpa [chooseAlt, findCtorAlt, findDefaultAlt, hit]
              using selection
          exact branchEq.symm
        subst selected
        refine ⟨thenTarget, 1, thenAdapted, ?_⟩
        rw [targetEq]
        simpa using
          structuredWasmObjectCaseHitPrefixFinitePath
            (module := target.wasmModule) (hostEnv := hosts.env)
            (spec := hosts.spec) (store := targetStore)
            (locals := targetLocals) (frames := frames)
            (thenTarget := thenTarget) (elseTarget := elseTarget)
            (discrIndex := discrIndex) (getTagIndex := getTagIndex)
            (imp := imp) (word := word) (actualTag := actualTag)
            (expectedTag := info.cidx) hit targetLookup imported
            spec.hostsSatisfy inBounds getTagContracted parameterCount
            resultCount tagOperation
      · have reverseMiss : info.cidx ≠ actualTag :=
          fun equal => hit equal.symm
        have selectionRest : chooseAlt actualTag alts = some selected := by
          simpa [chooseAlt, findCtorAlt, findDefaultAlt, hit, reverseMiss]
            using selection
        let caseLabel : StructuredWasmFrame :=
          .label 0 (targetLocals.values.drop 0) []
        obtain ⟨selectedTarget, testCount, selectedAdapted, tailPath⟩ :=
          ih selectionRest fallbackCompiledRest elseAdapted
            (frames := caseLabel :: frames)
        have headPath :
            FinitePath (StructuredWasmStep target.wasmModule hosts.env) 5
              ⟨targetStore, .running targetLocals chainTarget, frames⟩
              ⟨targetStore,
                .running { targetLocals with values := targetLocals.values }
                  elseTarget,
                caseLabel :: frames⟩ := by
          rw [targetEq]
          simpa [caseLabel] using
            structuredWasmObjectCaseMissPrefixFinitePath
              (module := target.wasmModule) (hostEnv := hosts.env)
              (spec := hosts.spec) (store := targetStore)
              (locals := targetLocals) (frames := frames)
              (thenTarget := thenTarget) (elseTarget := elseTarget)
              (discrIndex := discrIndex) (getTagIndex := getTagIndex)
              (imp := imp) (word := word) (actualTag := actualTag)
              (expectedTag := info.cidx) hit actualFits expectedFits
              targetLookup imported spec.hostsSatisfy inBounds
              getTagContracted parameterCount resultCount tagOperation
        refine ⟨selectedTarget, testCount + 1, selectedAdapted, ?_⟩
        simpa [caseLabel, Nat.mul_add, Nat.add_comm,
          List.replicate_succ_append] using headPath.trans tailPath

/-- Exact structured path through an arbitrary normalized scalar `UInt8` case
chain. Each compiler-generated direct comparison costs four steps and retains
one empty-result label; no concrete host operation is involved. -/
theorem ConcreteSupportedFunction.scalarUInt8CaseChainFinitePath
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {target : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context sourceCode sourceModule
        sourceFunction target hosts)
    {labels : List Lean.FVarId}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {discr : Lean.FVarId} {alts : List (Lean.Compiler.LCNF.Alt .impure)}
    {fallback : List Fir.Wasm.Instruction} {chainTarget : Wasm.Program}
    {selected : Lean.Compiler.LCNF.Code .impure}
    {targetStore : Wasm.Store Host} {targetLocals : Wasm.Locals}
    {witness : RefinementWitness} {sourceValue : Value} {actualTag : Nat}
    {frames : List StructuredWasmFrame}
    (supported : ScalarUInt8CaseAltsSupported alts)
    (modeEq : Fir.Wasm.caseDiscriminatorMode context discr = .scalarUInt8)
    (discrCompiled :
      Fir.Wasm.getLocal context discr = .ok (.localGet discr, .uint8))
    (selection : chooseAlt actualTag alts = some selected)
    (sourceLookup : lookup sourceEnv discr = some sourceValue)
    (tagged : getTag sourceRuntime sourceValue = .ok actualTag)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv targetStore
        targetLocals witness)
    (fallbackCompiled :
      Fir.Wasm.compileCaseFallback context alts = .ok fallback)
    (chainAdapted :
      CaseChainAdapted context sourceModule sourceFunction labels discr alts
        fallback chainTarget) :
    ∃ selectedTarget testCount,
      CodeAdapted context sourceModule sourceFunction labels selected
          selectedTarget ∧
        FinitePath (StructuredWasmStep target.wasmModule hosts.env)
          (4 * testCount)
          ⟨targetStore, .running targetLocals chainTarget, frames⟩
          ⟨targetStore,
            .running { targetLocals with values := targetLocals.values }
              selectedTarget,
            List.replicate testCount
                (.label 0 (targetLocals.values.drop 0) []) ++ frames⟩ := by
  induction supported generalizing chainTarget selected frames with
  | nil =>
      simp [chooseAlt, findCtorAlt, findDefaultAlt] at selection
  | default code =>
      have selectedEq : selected = code := by
        simpa [chooseAlt, findCtorAlt, findDefaultAlt] using selection.symm
      subst selected
      have branchCompiled :
          Fir.Wasm.compileCode context code = .ok fallback := by
        simpa [Fir.Wasm.compileCaseFallback,
          Fir.Wasm.compileCaseFallbackWithM, Fir.Wasm.isDefaultAlt]
          using fallbackCompiled
      have branchAdapted :
          CodeAdapted context sourceModule sourceFunction labels code
            chainTarget :=
        ⟨fallback, branchCompiled,
          CaseChainAdapted.nil_eq
            (CaseChainAdapted.default_eq chainAdapted)⟩
      exact ⟨chainTarget, 0, branchAdapted, .refl _⟩
  | @ctor info alts code fits rest ih =>
      have fallbackCompiledRest :
          Fir.Wasm.compileCaseFallback context alts = .ok fallback := by
        simpa [Fir.Wasm.compileCaseFallback,
          Fir.Wasm.compileCaseFallbackWithM, Fir.Wasm.isDefaultAlt]
          using fallbackCompiled
      obtain ⟨thenTarget, elseTarget, discrIndex, thenAdapted, elseAdapted,
          discrFound, targetEq⟩ :=
        CaseChainAdapted.scalarUInt8Constructor_eq modeEq fits chainAdapted
      obtain ⟨alignedIndex, alignedFound, discrKind⟩ :=
        spec.localsAligned discrCompiled
      rw [discrFound] at alignedFound
      have alignedEq : alignedIndex = discrIndex :=
        Option.some.inj alignedFound.symm
      subst alignedIndex
      obtain ⟨localFound, actualFits⟩ :=
        scalarUInt8Local_eq_of_related stateRelated sourceLookup discrFound
          discrKind tagged
      have expectedFits : info.cidx < UInt8.size := by
        simpa [Fir.Wasm.constructorTagFitsUInt8] using fits
      by_cases hit : actualTag = info.cidx
      · have selectedEq : selected = code := by
          have branchEq : code = selected := by
            simpa [chooseAlt, findCtorAlt, findDefaultAlt, hit]
              using selection
          exact branchEq.symm
        subst selected
        refine ⟨thenTarget, 1, thenAdapted, ?_⟩
        rw [targetEq]
        simpa using
          structuredWasmScalarUInt8CaseHitPrefixFinitePath
            (module := target.wasmModule) (hostEnv := hosts.env)
            (store := targetStore) (locals := targetLocals) (frames := frames)
            (thenTarget := thenTarget) (elseTarget := elseTarget)
            (discrIndex := discrIndex) (actualTag := actualTag)
            (expectedTag := info.cidx) hit localFound
      · have reverseMiss : info.cidx ≠ actualTag :=
          fun equal => hit equal.symm
        have selectionRest : chooseAlt actualTag alts = some selected := by
          simpa [chooseAlt, findCtorAlt, findDefaultAlt, hit, reverseMiss]
            using selection
        let caseLabel : StructuredWasmFrame :=
          .label 0 (targetLocals.values.drop 0) []
        obtain ⟨selectedTarget, testCount, selectedAdapted, tailPath⟩ :=
          ih selectionRest fallbackCompiledRest elseAdapted
            (frames := caseLabel :: frames)
        have headPath :
            FinitePath (StructuredWasmStep target.wasmModule hosts.env) 4
              ⟨targetStore, .running targetLocals chainTarget, frames⟩
              ⟨targetStore,
                .running { targetLocals with values := targetLocals.values }
                  elseTarget,
                caseLabel :: frames⟩ := by
          rw [targetEq]
          simpa [caseLabel] using
            structuredWasmScalarUInt8CaseMissPrefixFinitePath
              (module := target.wasmModule) (hostEnv := hosts.env)
              (store := targetStore) (locals := targetLocals)
              (frames := frames) (thenTarget := thenTarget)
              (elseTarget := elseTarget) (discrIndex := discrIndex)
              (actualTag := actualTag) (expectedTag := info.cidx) hit
              actualFits expectedFits localFound
        refine ⟨selectedTarget, testCount + 1, selectedAdapted, ?_⟩
        simpa [caseLabel, Nat.mul_add, Nat.add_comm,
          List.replicate_succ_append] using headPath.trans tailPath

/-- Compiler-derived structured simulation of one generated lazy-cache hit.

The source admission contains only the nullary declaration facts.  Compiler
inversion recovers the cache indices and exact conditional body; the generated
cache relation recovers the populated physical slot.  Consequently neither
the five-step target path nor any numeric index is supplied by the caller. -/
theorem ConcreteStructuredCodeFocus.advance_lazyHit_of_compiler
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {targetModule : AdaptedModule} {hosts : ResolvedHosts}
    (spec :
      ConcreteSupportedFunction program context functionCode sourceModule
        sourceFunction targetModule hosts)
    {externals : ExternalImpl}
    {facts : ReuseCapacityFacts}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {sourceValue : Value}
    {declaration : Lean.Name}
    {sourceDeclaration : Lean.Compiler.LCNF.Decl .impure}
    {resultKind : AbiKind}
    {valueCode : List Fir.Wasm.Instruction}
    {targetCode targetValue targetRest : Wasm.Program}
    {resultIndex remainingBytes : Nat}
    {targetStore : Wasm.Store Host} {targetLocals : Wasm.Locals}
    {witness : RefinementWitness}
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
    (supported :
      LazyCacheCallSupported context decl declaration sourceDeclaration
        resultKind)
    (generated : LazyCacheGeneratedEnvironment context sourceModule)
    (sourceStep :
      SourceLazyLetResult .hit context externals sourceRuntime sourceEnv decl
        continuation nextRuntime sourceValue)
    (invariant :
      ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals
        facts remainingBytes sourceRuntime sourceEnv targetStore targetLocals
        witness)
    (valueCompiled : Fir.Wasm.compileLetValue context decl = .ok valueCode)
    (valueAdapted :
      instructions sourceModule sourceFunction labels valueCode =
        .ok targetValue)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId =
        some resultIndex) :
    ∃ sourceAfter targetAfter nextLocals physical,
      BudgetedCapacityPreservingLazyStep .hit facts context sourceFunction
          targetModule.wasmModule hosts.env externals decl continuation
          targetValue sourceRuntime nextRuntime sourceEnv sourceValue
          targetStore targetStore targetLocals nextLocals resultIndex witness
          witness physical 0 ∧
        reuseCapacityLetFacts? facts decl =
            some (eraseReuseCapacityFact facts decl.fvarId) ∧
          LazyCacheGlobalsRel witness sourceModule nextRuntime targetStore ∧
            FinitePath
                (fun before after =>
                  executeStep externals before = .next after)
                3 source sourceAfter ∧
              FinitePath
                  (StructuredWasmStep targetModule.wasmModule hosts.env)
                  5 target targetAfter ∧
                ConcreteStructuredCodeFocus context sourceModule sourceFunction
                    labels nextRuntime
                    (bind sourceEnv decl.fvarId sourceValue) continuation
                    targetStore { nextLocals with values := targetLocals.values }
                    targetRest witness sourceAfter targetAfter ∧
                  sourceAfter.joins = [] ∧
                    sourceAfter.frames = source.frames ∧
                      targetAfter.frames = target.frames := by
  rcases supported with
    ⟨valueEq, kindEq, targetEq, targetResultEq, _resultRefines, paramsEq,
      resultCompiled⟩
  obtain ⟨runtimeEq, semanticFound⟩ :=
    SourceLazyLetResult.hit_cacheFacts_of_valueEq valueEq targetEq paramsEq
      sourceStep
  subst nextRuntime
  obtain ⟨targetResultKind, cacheIndex, _declarationId, _cacheSetId,
      recoveredTargetResultEq, cacheEq, _declarationCall, _cacheSetCall,
      _valueCodeEq, targetValueEq⟩ :=
    compileCachedLetValue_adapted_inv context sourceModule sourceFunction labels
      decl declaration sourceDeclaration _ valueCode targetValue valueEq kindEq
      targetEq paramsEq valueCompiled valueAdapted
  have targetKindEq : targetResultKind = resultKind :=
    Option.some.inj (recoveredTargetResultEq.symm.trans targetResultEq)
  subst targetResultKind
  obtain ⟨alignedResultIndex, alignedResultFound, resultKindAt⟩ :=
    spec.localsAligned resultCompiled
  rw [resultFound] at alignedResultFound
  injection alignedResultFound with resultIndexEq
  subst alignedResultIndex
  rcases invariant with
    ⟨⟨⟨⟨initialRelated, _ordinary, frameAligned, _budget⟩,
      _integer, _natural, _scalar⟩, _descriptors⟩, cacheTable,
      _closureTables⟩
  obtain ⟨initializerFound, signature⟩ :=
    generated.select kindEq targetEq targetResultEq paramsEq cacheEq
  obtain ⟨physical, slot⟩ :=
    cacheTable.populatedSlot initializerFound signature semanticFound
  obtain ⟨nextLocals, targetSet, nextAligned⟩ :=
    frameAligned.set? (nextRuntime := sourceRuntime)
      (nextEnv := bind sourceEnv decl.fvarId sourceValue)
      (nextStore := targetStore) (nextWitness := witness)
      (physical := physical) resultFound
  have hit :
      BudgetedCapacityPreservingLazyStep .hit facts context sourceFunction
        targetModule.wasmModule hosts.env externals decl continuation
        [.globalGet (2 * cacheIndex),
          .iff 0 0 [] [
            .call _declarationId,
            .call _cacheSetId,
            .globalSet (2 * cacheIndex + 1),
            .const 1,
            .globalSet (2 * cacheIndex)],
          .globalGet (2 * cacheIndex + 1)]
        sourceRuntime sourceRuntime sourceEnv sourceValue targetStore targetStore
        targetLocals nextLocals resultIndex witness witness physical 0 :=
    BudgetedCapacityPreservingLazyStep.hit sourceStep
      initialRelated.stateRelated slot.flagPublished slot.valuePublished
      targetSet resultFound resultKindAt slot.valueRelated
  let sourceAfter : MachineState :=
    { source with
      control := .code continuation
      env := bind sourceEnv decl.fvarId sourceValue }
  let targetAfter : StructuredWasmState Host :=
    { target with
      control := .running
        { nextLocals with values := targetLocals.values } targetRest }
  have sourcePath :
      FinitePath
        (fun before after => executeStep externals before = .next after)
        3 source sourceAfter := by
    rcases source with ⟨sourceProgram, sourceControl, sourceStateEnv,
      sourceStateJoins, sourceFrames, sourceStateRuntime⟩
    have programEq := related.sourceProgramEq
    change sourceProgram = context.program at programEq
    subst sourceProgram
    have controlEq := related.sourceControlEq
    change sourceControl = .code (.let decl continuation) at controlEq
    subst sourceControl
    have envEq := related.sourceEnvEq
    change sourceStateEnv = sourceEnv at envEq
    subst sourceStateEnv
    have runtimeStateEq := related.sourceRuntimeEq
    change sourceStateRuntime = sourceRuntime at runtimeStateEq
    subst sourceStateRuntime
    change sourceStateJoins = [] at sourceJoins
    subst sourceStateJoins
    have lifted :=
      FirTalos.Correctness.ExecSteps.withFrameSuffix
        (suffix := sourceFrames) sourceStep
    exact ExecSteps.toFinitePath (by
      simpa [SourceLazyLetResult, withFrameSuffix, sourceAfter] using lifted)
  have targetPath :
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 5
        target targetAfter := by
    rcases target with ⟨targetStateStore, targetControl, targetFrames⟩
    have storeEq := related.targetStoreEq
    change targetStateStore = targetStore at storeEq
    subst targetStateStore
    have controlEq := related.targetControlEq
    rw [targetCodeEq, targetValueEq] at controlEq
    change targetControl =
      .running targetLocals
        ([.globalGet (2 * cacheIndex),
          .iff 0 0 [] [
            .call _declarationId,
            .call _cacheSetId,
            .globalSet (2 * cacheIndex + 1),
            .const 1,
            .globalSet (2 * cacheIndex)],
          .globalGet (2 * cacheIndex + 1),
          .localSet resultIndex] ++ targetRest) at controlEq
    subst targetControl
    simpa [targetAfter] using
      structuredWasmLazyHitFinitePath
        (module := targetModule.wasmModule) (hostEnv := hosts.env)
        (rest := targetRest) (frames := targetFrames)
        targetLocals.values slot.flagPublished slot.valuePublished targetSet
  have focus :
      ConcreteStructuredCodeFocus context sourceModule sourceFunction labels
        sourceRuntime (bind sourceEnv decl.fvarId sourceValue) continuation
        targetStore { nextLocals with values := targetLocals.values } targetRest
        witness sourceAfter targetAfter := {
    sourceProgramEq := by simp [sourceAfter, related.sourceProgramEq]
    sourceControlEq := by simp [sourceAfter]
    sourceEnvEq := by simp [sourceAfter]
    sourceRuntimeEq := by simp [sourceAfter, related.sourceRuntimeEq]
    targetStoreEq := by simp [targetAfter, related.targetStoreEq]
    targetControlEq := by simp [targetAfter]
    adapted := continuationAdapted
    stateRelated := by
      simpa using hit.simulates.2.2.1.withValues targetLocals.values
    frameAligned := by
      simpa using nextAligned.withValues targetLocals.values }
  refine ⟨sourceAfter, targetAfter, nextLocals, physical, ?_, ?_, cacheTable,
    sourcePath, targetPath, focus, ?_, ?_, ?_⟩
  · simpa [targetValueEq] using hit
  · simp [reuseCapacityLetFacts?, valueEq]
  · simp [sourceAfter, sourceJoins]
  · simp [sourceAfter]
  · simp [targetAfter]

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

/-- Source-only recursive admission for the structured fragment proved here.

Lazy initializers are recursive arguments of this relation, just like named
calls.  This is important for compiler correctness: the structured target
proof receives an induction hypothesis for the generated initializer rather
than an opaque runtime certificate.  The cache constructors cover hits and
non-heap misses; a miss recursively evaluates the initializer and then
publishes its result through the concrete host cache and generated Wasm
globals.  Default-only cases are included as compiler-erased control steps,
and arbitrary normalized object-constructor cases execute the
compiler-generated `getTag` chain recursively.  Arbitrary normalized scalar
`UInt8` cases execute the generated direct-comparison chain recursively as
well.  Persistent ownership effects are source-visible recursive steps whose
compiler erasure is matched by a zero-step target path. Successful ordinary
increments execute the exact generated unary-host prefix and recurse through
the updated heap relation. Heap-valued miss publication and the remaining
ownership effects remain separate later widenings. -/
inductive ReuseCapacityStructuredPureExternalLazyCodeEvaluates
    (externals : ExternalImpl) :
    Fir.Wasm.Context → AbiKind → ReuseCapacityFacts → RuntimeState →
      Env → Lean.Compiler.LCNF.Code .impure → ReuseCapacityFacts →
        RuntimeState → Env → Value → Nat → Prop where
  | ret
      {actualResultKind : AbiKind}
      (sourceLookup : lookup sourceEnv result = some sourceValue)
      (resultCompiled :
        Fir.Wasm.getLocal context result =
          .ok (.localGet result, actualResultKind))
      (resultRefines : actualResultKind.refines expectedResult = true) :
      ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
        expectedResult facts sourceRuntime sourceEnv (.return result) facts
        sourceRuntime sourceEnv sourceValue 0
  | letValue
      (supported : ReuseBudgetedDirectSupported context facts decl)
      (sourceStep :
        SourceLetResult context sourceRuntime sourceEnv decl nextRuntime
          sourceValue)
      (transfer : reuseCapacityLetFacts? facts decl = some nextFacts)
      (continued :
        ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
          expectedResult nextFacts nextRuntime
          (bind sourceEnv decl.fvarId sourceValue) continuation resultFacts
          resultRuntime resultEnv resultValue continuationCost) :
      ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
        expectedResult facts sourceRuntime sourceEnv (.let decl continuation)
        resultFacts resultRuntime resultEnv resultValue
        (directLetAllocationCost decl + continuationCost)
  | externalLet
      (supported :
        PureExternalSupported context externals sourceRuntime sourceEnv decl
          continuation nextRuntime sourceValue stepCost)
      (sourceStep :
        SourceExternalLetResult context externals sourceRuntime sourceEnv decl
          continuation nextRuntime sourceValue)
      (transfer : reuseCapacityLetFacts? facts decl = some nextFacts)
      (continued :
        ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
          expectedResult nextFacts nextRuntime
          (bind sourceEnv decl.fvarId sourceValue) continuation resultFacts
          resultRuntime resultEnv resultValue continuationCost) :
      ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
        expectedResult facts sourceRuntime sourceEnv (.let decl continuation)
        resultFacts resultRuntime resultEnv resultValue
        (stepCost + continuationCost)

  | directCallLet
      {calleeFunction : Fir.Wasm.Function}
      (site : DirectInternalCallSite context decl sourceEnv)
      (row :
        LoweredInternalDeclaration context.program context.cachedDeclarations
          site.sourceDeclaration site.calleeCode calleeFunction)
      (callee :
        ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals
          row.context site.calleeResultKind [] sourceRuntime site.calleeEnv
          site.calleeCode calleeResultFacts nextRuntime calleeResultEnv
          sourceValue stepCost)
      (transfer : reuseCapacityLetFacts? facts decl = some nextFacts)
      (continued :
        ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
          expectedResult nextFacts nextRuntime
          (bind sourceEnv decl.fvarId sourceValue) continuation resultFacts
          resultRuntime resultEnv resultValue continuationCost) :
      ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
        expectedResult facts sourceRuntime sourceEnv (.let decl continuation)
        resultFacts resultRuntime resultEnv resultValue
        (stepCost + continuationCost)
  | lazyHit
      (call :
        LazyCacheCallSupported context decl declaration sourceDeclaration
          resultKind)
      (sourceStep :
        SourceLazyLetResult .hit context externals sourceRuntime sourceEnv decl
          continuation nextRuntime sourceValue)
      (transfer : reuseCapacityLetFacts? facts decl = some nextFacts)
      (continued :
        ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
          expectedResult nextFacts nextRuntime
          (bind sourceEnv decl.fvarId sourceValue) continuation resultFacts
          resultRuntime resultEnv resultValue continuationCost) :
      ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
        expectedResult facts sourceRuntime sourceEnv (.let decl continuation)
        resultFacts resultRuntime resultEnv resultValue continuationCost
  | lazyMiss
      {calleeFunction : Fir.Wasm.Function}
      (call :
        LazyCacheInternalMissSupported context decl declaration
          sourceDeclaration resultKind calleeCode)
      (row :
        LoweredInternalDeclaration context.program context.cachedDeclarations
          sourceDeclaration calleeCode calleeFunction)
      (resultClassified :
        Fir.Wasm.abiKind? sourceDeclaration.type = .ok (some resultKind))
      (notObject : resultKind ≠ .object)
      (notTObject : resultKind ≠ .tobject)
      (sourceStep :
        SourceLazyLetResult .miss context externals sourceRuntime sourceEnv decl
          continuation nextRuntime sourceValue)
      (callee :
        ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals
          row.context resultKind [] sourceRuntime [] calleeCode
          calleeResultFacts callRuntime calleeResultEnv sourceValue stepCost)
      (transfer : reuseCapacityLetFacts? facts decl = some nextFacts)
      (continued :
        ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
          expectedResult nextFacts nextRuntime
          (bind sourceEnv decl.fvarId sourceValue) continuation resultFacts
          resultRuntime resultEnv resultValue continuationCost) :
      ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
        expectedResult facts sourceRuntime sourceEnv (.let decl continuation)
        resultFacts resultRuntime resultEnv resultValue
        (stepCost + continuationCost)
  | defaultCase
      (supported :
        DefaultOnlyCaseSupported sourceRuntime sourceEnv cases selected)
      (sourceStep :
        SourceCaseResult sourceRuntime sourceEnv cases selected)
      (continued :
        ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
          expectedResult facts sourceRuntime sourceEnv selected resultFacts
          resultRuntime resultEnv resultValue requiredBytes) :
      ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
        expectedResult facts sourceRuntime sourceEnv (.cases cases) resultFacts
        resultRuntime resultEnv resultValue requiredBytes
  | singleObjectCase
      (supported :
        SingleObjectConstructorCaseSupported context sourceRuntime sourceEnv
          cases selected)
      (sourceStep :
        SourceCaseResult sourceRuntime sourceEnv cases selected)
      (continued :
        ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
          expectedResult facts sourceRuntime sourceEnv selected resultFacts
          resultRuntime resultEnv resultValue requiredBytes) :
      ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
        expectedResult facts sourceRuntime sourceEnv (.cases cases) resultFacts
        resultRuntime resultEnv resultValue requiredBytes
  | twoObjectDefaultCase
      (supported :
        TwoObjectConstructorDefaultCasesSupported context sourceRuntime
          sourceEnv cases selected)
      (sourceStep :
        SourceCaseResult sourceRuntime sourceEnv cases selected)
      (continued :
        ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
          expectedResult facts sourceRuntime sourceEnv selected resultFacts
          resultRuntime resultEnv resultValue requiredBytes) :
      ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
        expectedResult facts sourceRuntime sourceEnv (.cases cases) resultFacts
        resultRuntime resultEnv resultValue requiredBytes
  | objectCases
      (supported :
        ObjectConstructorCasesSupported context sourceRuntime sourceEnv cases
          selected)
      (sourceStep :
        SourceCaseResult sourceRuntime sourceEnv cases selected)
      (continued :
        ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
          expectedResult facts sourceRuntime sourceEnv selected resultFacts
          resultRuntime resultEnv resultValue requiredBytes) :
      ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
        expectedResult facts sourceRuntime sourceEnv (.cases cases) resultFacts
        resultRuntime resultEnv resultValue requiredBytes
  | scalarUInt8Cases
      (supported :
        ScalarUInt8CasesSupported context sourceRuntime sourceEnv cases
          selected)
      (sourceStep :
        SourceCaseResult sourceRuntime sourceEnv cases selected)
      (continued :
        ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
          expectedResult facts sourceRuntime sourceEnv selected resultFacts
          resultRuntime resultEnv resultValue requiredBytes) :
      ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
        expectedResult facts sourceRuntime sourceEnv (.cases cases) resultFacts
        resultRuntime resultEnv resultValue requiredBytes
  | persistentOwnershipEffect
      (supported :
        PersistentOwnershipEffectSupported sourceRuntime sourceEnv code
          continuation nextRuntime)
      (sourceStep :
        SourceEffectResult context sourceRuntime nextRuntime sourceEnv code
          continuation)
      (continued :
        ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
          expectedResult facts nextRuntime sourceEnv continuation resultFacts
          resultRuntime resultEnv resultValue requiredBytes) :
      ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
        expectedResult facts sourceRuntime sourceEnv code resultFacts
        resultRuntime resultEnv resultValue requiredBytes
  | ordinaryIncrementEffect
      (supported :
        OrdinaryIncrementEffectSupported context sourceRuntime sourceEnv code
          continuation nextRuntime)
      (sourceStep :
        SourceEffectResult context sourceRuntime nextRuntime sourceEnv code
          continuation)
      (continued :
        ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
          expectedResult facts nextRuntime sourceEnv continuation resultFacts
          resultRuntime resultEnv resultValue requiredBytes) :
      ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
        expectedResult facts sourceRuntime sourceEnv code resultFacts
        resultRuntime resultEnv resultValue requiredBytes
  | ordinaryDecrementEffect
      (supported :
        OrdinaryDecrementEffectSupported context sourceRuntime sourceEnv code
          continuation nextRuntime)
      (sourceStep :
        SourceEffectResult context sourceRuntime nextRuntime sourceEnv code
          continuation)
      (continued :
        ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
          expectedResult facts nextRuntime sourceEnv continuation resultFacts
          resultRuntime resultEnv resultValue requiredBytes) :
      ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
        expectedResult facts sourceRuntime sourceEnv code resultFacts
        resultRuntime resultEnv resultValue requiredBytes
  | ordinaryDeleteEffect
      (supported :
        OrdinaryDeleteEffectSupported context sourceRuntime sourceEnv code
          continuation nextRuntime)
      (sourceStep :
        SourceEffectResult context sourceRuntime nextRuntime sourceEnv code
          continuation)
      (continued :
        ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
          expectedResult facts nextRuntime sourceEnv continuation resultFacts
          resultRuntime resultEnv resultValue requiredBytes) :
      ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
        expectedResult facts sourceRuntime sourceEnv code resultFacts
        resultRuntime resultEnv resultValue requiredBytes
  | constructorTagEffect
      (supported :
        ConstructorTagEffectSupported context sourceRuntime sourceEnv code
          continuation nextRuntime)
      (sourceStep :
        SourceEffectResult context sourceRuntime nextRuntime sourceEnv code
          continuation)
      (continued :
        ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
          expectedResult facts nextRuntime sourceEnv continuation resultFacts
          resultRuntime resultEnv resultValue requiredBytes) :
      ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
        expectedResult facts sourceRuntime sourceEnv code resultFacts
        resultRuntime resultEnv resultValue requiredBytes
  | objectFieldFVarEffect
      (supported :
        ObjectFieldFVarEffectSupported context sourceRuntime sourceEnv code
          continuation nextRuntime)
      (sourceStep :
        SourceEffectResult context sourceRuntime nextRuntime sourceEnv code
          continuation)
      (continued :
        ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
          expectedResult facts nextRuntime sourceEnv continuation resultFacts
          resultRuntime resultEnv resultValue requiredBytes) :
      ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
        expectedResult facts sourceRuntime sourceEnv code resultFacts
        resultRuntime resultEnv resultValue requiredBytes
  | objectFieldErasedEffect
      (supported :
        ObjectFieldErasedEffectSupported context sourceRuntime sourceEnv code
          continuation nextRuntime)
      (sourceStep :
        SourceEffectResult context sourceRuntime nextRuntime sourceEnv code
          continuation)
      (continued :
        ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
          expectedResult facts nextRuntime sourceEnv continuation resultFacts
          resultRuntime resultEnv resultValue requiredBytes) :
      ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
        expectedResult facts sourceRuntime sourceEnv code resultFacts
        resultRuntime resultEnv resultValue requiredBytes
  | usizeFieldEffect
      (supported :
        USizeFieldEffectSupported context sourceRuntime sourceEnv code
          continuation nextRuntime)
      (sourceStep :
        SourceEffectResult context sourceRuntime nextRuntime sourceEnv code
          continuation)
      (continued :
        ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
          expectedResult facts nextRuntime sourceEnv continuation resultFacts
          resultRuntime resultEnv resultValue requiredBytes) :
      ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
        expectedResult facts sourceRuntime sourceEnv code resultFacts
        resultRuntime resultEnv resultValue requiredBytes
  | scalarFieldEffect
      (supported :
        ScalarFieldEffectSupported context sourceRuntime sourceEnv code
          continuation nextRuntime)
      (sourceStep :
        SourceEffectResult context sourceRuntime nextRuntime sourceEnv code
          continuation)
      (continued :
        ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
          expectedResult facts nextRuntime sourceEnv continuation resultFacts
          resultRuntime resultEnv resultValue requiredBytes) :
      ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
        expectedResult facts sourceRuntime sourceEnv code resultFacts
        resultRuntime resultEnv resultValue requiredBytes

/-- The structured admission remains an exact finite source execution.  In
particular, the recursive initializer premise of a miss is semantic evidence,
not merely a target-side proof device. -/
theorem ReuseCapacityStructuredPureExternalLazyCodeEvaluates.sourceResult
    {externals : ExternalImpl} {context : Fir.Wasm.Context}
    {expectedResult : AbiKind} {facts resultFacts : ReuseCapacityFacts}
    {sourceRuntime resultRuntime : RuntimeState} {sourceEnv resultEnv : Env}
    {sourceCode : Lean.Compiler.LCNF.Code .impure} {resultValue : Value}
    {requiredBytes : Nat}
    (evaluation :
      ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
        expectedResult facts sourceRuntime sourceEnv sourceCode resultFacts
        resultRuntime resultEnv resultValue requiredBytes) :
    SourceCodeResult context externals sourceRuntime sourceEnv sourceCode
      resultRuntime resultValue := by
  induction evaluation with
  | ret sourceLookup _resultCompiled _resultRefines =>
      exact (CodeEvaluates.ret sourceLookup).sourceResult externals
  | @letValue context facts decl sourceRuntime sourceEnv nextRuntime
      sourceValue nextFacts expectedResult continuation resultFacts
      resultRuntime resultEnv resultValue continuationCost supported sourceStep
      transfer continued ih =>
      apply SourceCodeResult.ofSteps
        (.step (by
          have evaluated :
              evalLetValue
                  (sourceCodeState context sourceRuntime sourceEnv
                    (.let decl continuation)) decl =
                .ok (nextRuntime, .value sourceValue) := by
            unfold SourceLetResult at sourceStep
            cases decl.value <;> exact sourceStep
          unfold sourceCodeState at evaluated
          simp [executeStep, coreStep, sourceCodeState, evaluated])
          (.refl _))
        ih
  | externalLet _ sourceStep _ _ ih =>
      apply SourceCodeResult.ofSteps (prefixCount := 3) ?_ ih
      simpa [SourceExternalLetResult, sourceCodeState] using sourceStep
  | @directCallLet callContext decl sourceEnv sourceRuntime calleeResultFacts
      nextRuntime calleeResultEnv sourceValue stepCost facts nextFacts
      expectedResult continuation resultFacts resultRuntime resultEnv resultValue
      continuationCost calleeFunction site row callee transfer continued
      calleeIH continuedIH =>
      have contexts : DeclarationContextsCoherent callContext row.context :=
        row.contextsCoherent rfl rfl
      obtain ⟨count, steps⟩ :=
        site.sourceCallLetResult contexts calleeIH
      apply SourceCodeResult.ofSteps (prefixCount := count) ?_ continuedIH
      simpa [sourceCodeState] using steps
  | lazyHit _ sourceStep _ _ ih =>
      obtain ⟨count, steps⟩ := sourceStep.execSteps
      apply SourceCodeResult.ofSteps (prefixCount := count) ?_ ih
      simpa [sourceCodeState] using steps
  | lazyMiss _ _ _ _ _ sourceStep _ _ _ _ continuedIH =>
      obtain ⟨count, steps⟩ := sourceStep.execSteps
      apply SourceCodeResult.ofSteps (prefixCount := count) ?_ continuedIH
      simpa [sourceCodeState] using steps
  | defaultCase _ sourceStep _ ih =>
      apply SourceCodeResult.ofSteps
        (.step (by
          rcases sourceStep with ⟨discrValue, tag, found, tagged, chosen⟩
          simp [executeStep, coreStep, sourceCodeState, found, tagged, chosen])
          (.refl _))
        ih
  | singleObjectCase _ sourceStep _ ih =>
      apply SourceCodeResult.ofSteps
        (.step (by
          rcases sourceStep with ⟨discrValue, tag, found, tagged, chosen⟩
          simp [executeStep, coreStep, sourceCodeState, found, tagged, chosen])
          (.refl _))
        ih
  | twoObjectDefaultCase _ sourceStep _ ih =>
      apply SourceCodeResult.ofSteps
        (.step (by
          rcases sourceStep with ⟨discrValue, tag, found, tagged, chosen⟩
          simp [executeStep, coreStep, sourceCodeState, found, tagged, chosen])
          (.refl _))
        ih
  | objectCases _ sourceStep _ ih =>
      apply SourceCodeResult.ofSteps
        (.step (by
          rcases sourceStep with ⟨discrValue, tag, found, tagged, chosen⟩
          simp [executeStep, coreStep, sourceCodeState, found, tagged, chosen])
          (.refl _))
        ih
  | scalarUInt8Cases _ sourceStep _ ih =>
      apply SourceCodeResult.ofSteps
        (.step (by
          rcases sourceStep with ⟨discrValue, tag, found, tagged, chosen⟩
          simp [executeStep, coreStep, sourceCodeState, found, tagged, chosen])
          (.refl _))
        ih
  | persistentOwnershipEffect _ sourceStep _ ih =>
      apply SourceCodeResult.ofSteps
        (.step (sourceStep externals) (.refl _)) ih
  | ordinaryIncrementEffect _ sourceStep _ ih =>
      apply SourceCodeResult.ofSteps
        (.step (sourceStep externals) (.refl _)) ih
  | ordinaryDecrementEffect _ sourceStep _ ih =>
      apply SourceCodeResult.ofSteps
        (.step (sourceStep externals) (.refl _)) ih
  | ordinaryDeleteEffect _ sourceStep _ ih =>
      apply SourceCodeResult.ofSteps
        (.step (sourceStep externals) (.refl _)) ih
  | constructorTagEffect _ sourceStep _ ih =>
      apply SourceCodeResult.ofSteps
        (.step (sourceStep externals) (.refl _)) ih
  | objectFieldFVarEffect _ sourceStep _ ih =>
      apply SourceCodeResult.ofSteps
        (.step (sourceStep externals) (.refl _)) ih
  | objectFieldErasedEffect _ sourceStep _ ih =>
      apply SourceCodeResult.ofSteps
        (.step (sourceStep externals) (.refl _)) ih
  | usizeFieldEffect _ sourceStep _ ih =>
      apply SourceCodeResult.ofSteps
        (.step (sourceStep externals) (.refl _)) ih
  | scalarFieldEffect _ sourceStep _ ih =>
      apply SourceCodeResult.ofSteps
        (.step (sourceStep externals) (.refl _)) ih

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

/-- One successful ordinary reference-count increment advances the source by
one effect step and the structured target by the exact generated unary-host
prefix.  The resulting heap, cache table, immutable closure tables, and all
entry-relative resource transports are reconstructed from the operation
contract; no target execution is admitted as a premise. -/
theorem ConcreteStructuredCodeFocus.advance_ordinaryIncrement
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode code continuation : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule} {hosts : ResolvedHosts}
    (functionSpec :
      ConcreteSupportedFunction program context functionCode sourceModule
        sourceFunction targetModule hosts)
    {externals : ExternalImpl}
    {facts : ReuseCapacityFacts} {remainingBytes : Nat}
    {sourceRuntime nextRuntime entryRuntime : RuntimeState}
    {sourceEnv : Env}
    {targetStore entryStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {witness entryWitness : RefinementWitness}
    {targetCode : Wasm.Program}
    {source : MachineState} {target : StructuredWasmState Host}
    (supported :
      OrdinaryIncrementEffectSupported context sourceRuntime sourceEnv code
        continuation nextRuntime)
    (sourceStep :
      SourceEffectResult context sourceRuntime nextRuntime sourceEnv code
        continuation)
    (related :
      ConcreteStructuredCodeFocus context sourceModule sourceFunction []
        sourceRuntime sourceEnv code targetStore targetLocals targetCode witness
        source target)
    (invariant :
      ReuseCapacityEntryRelativeFrame
        (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals)
        entryRuntime entryStore entryWitness facts remainingBytes sourceRuntime
        sourceEnv targetStore targetLocals witness) :
    ∃ sourceAfter targetAfter nextStore targetRest,
      FinitePath
          (fun before after => executeStep externals before = .next after)
          1 source sourceAfter ∧
        FinitePath
            (StructuredWasmStep targetModule.wasmModule hosts.env)
            2 target targetAfter ∧
          ConcreteStructuredCodeFocus context sourceModule sourceFunction []
              nextRuntime sourceEnv continuation nextStore targetLocals
              targetRest witness sourceAfter targetAfter ∧
            ReuseCapacityEntryRelativeFrame
              (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
                externals)
              entryRuntime entryStore entryWitness facts remainingBytes
              nextRuntime sourceEnv nextStore targetLocals witness ∧
            sourceAfter.joins = source.joins ∧
              sourceAfter.frames = source.frames ∧
                targetAfter.frames = target.frames := by
  cases supported with
  | inc sourceRuntime nextRuntime sourceEnv objectId amount check continuation
      objectKind sourceObject objectCompiled objectRefines objectLookup updated
      fits =>
      obtain ⟨objectIndex, callIndex, targetRest, objectFound, kindAt,
          callFound, continuationAdapted, targetCodeEq⟩ :=
        CodeAdapted.inc_eq functionSpec.localsAligned objectCompiled
          related.adapted
      subst targetCode
      obtain ⟨imp, imported, inBounds, contracted, parameterCount,
          resultCount⟩ :=
        functionSpec.incrementCall callFound
      have sourceLookup : lookup sourceEnv objectId = some sourceObject := by
        unfold lookupValue at objectLookup
        split at objectLookup
        · rename_i value found
          injection objectLookup with valueEq
          subst value
          exact found
        · contradiction
      obtain ⟨physicalObject, targetLookup, physicalRelated⟩ :=
        related.stateRelated.resolve sourceLookup objectFound kindAt
      have tobjectRelated := physicalRelated.toTObject objectRefines
      cases tobjectRelated with
      | word32 objectRelated =>
          rename_i word
          obtain ⟨heap, operation, runtimeRelated, cursor, capacity⟩ :=
            incrementStep_of_refines_with_capacity related.stateRelated.1
              objectRelated updated fits
          have nextRelated :
              StateRelated sourceFunction nextRuntime sourceEnv
                (replaceHeap targetStore heap) targetLocals witness :=
            ⟨runtimeRelated, by simp [replaceHeap, clearFailure],
              related.stateRelated.2.2⟩
          have effectStep :
              EffectStepSimulates context sourceModule sourceFunction []
                targetModule.wasmModule hosts.env sourceRuntime nextRuntime
                sourceEnv (.inc objectId amount check false continuation)
                continuation
                ([.localGet objectIndex, .call callIndex] ++ targetRest)
                targetRest targetStore (replaceHeap targetStore heap)
                targetLocals witness witness := by
            apply effectStepSimulates_unaryHost
              (spec := hosts.spec) (step := incrementStep amount check)
            · exact sourceStep
            · exact codeAdapted_inc objectCompiled objectFound callFound
                continuationAdapted
            · exact related.stateRelated
            · exact nextRelated
            · exact targetLookup
            · exact imported
            · exact functionSpec.hostsSatisfy
            · exact inBounds
            · exact contracted
            · exact parameterCount
            · exact resultCount
            · exact operation
          have ordinaryTransport :
              OrdinaryPersistenceTransport sourceRuntime nextRuntime :=
            incValue_ordinaryPersistenceTransport updated
          have sourceGlobals :
              nextRuntime.globals = sourceRuntime.globals := by
            rcases incValue_heapOnly updated with ⟨semanticHeap, runtimeEq⟩
            subst nextRuntime
            rfl
          have nextInvariant :
              ReuseCapacityEntryRelativeFrame
                (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
                  externals)
                entryRuntime entryStore entryWitness facts remainingBytes
                nextRuntime sourceEnv (replaceHeap targetStore heap)
                targetLocals witness :=
            invariant.ofReplaceHeapEffectStep effectStep capacity
              ordinaryTransport sourceGlobals cursor
          let sourceAfter : MachineState := {
            source with control := .code continuation
                        runtime := nextRuntime }
          have sourcePath :
              executeStep externals source = .next sourceAfter := by
            rcases source with
              ⟨sourceProgram, sourceControl, actualEnv, sourceJoinEnv,
                sourceFrames, actualRuntime⟩
            have programEq := related.sourceProgramEq
            change sourceProgram = context.program at programEq
            subst sourceProgram
            have controlEq := related.sourceControlEq
            change sourceControl = _ at controlEq
            subst sourceControl
            have envEq := related.sourceEnvEq
            change actualEnv = sourceEnv at envEq
            subst actualEnv
            have runtimeEq := related.sourceRuntimeEq
            change actualRuntime = sourceRuntime at runtimeEq
            subst actualRuntime
            simp [sourceAfter, executeStep, coreStep, objectLookup, updated]
          let targetAfter : StructuredWasmState Host := {
            store := replaceHeap targetStore heap
            control := .running
              { targetLocals with values := targetLocals.values } targetRest
            frames := target.frames }
          have targetPath :
              FinitePath
                (StructuredWasmStep targetModule.wasmModule hosts.env) 2
                target targetAfter := by
            rcases target with ⟨actualStore, actualControl, actualFrames⟩
            have storeEq := related.targetStoreEq
            change actualStore = targetStore at storeEq
            subst actualStore
            have controlEq := related.targetControlEq
            change actualControl =
              .running targetLocals
                ([.localGet objectIndex, .call callIndex] ++ targetRest)
              at controlEq
            subst actualControl
            simpa [targetAfter] using
              structuredWasmUnaryHostEffectPrefixFinitePath
                (module := targetModule.wasmModule) (env := hosts.env)
                (spec := hosts.spec) (step := incrementStep amount check)
                (initial := targetStore) (final := replaceHeap targetStore heap)
                (locals := targetLocals) (objectIndex := objectIndex)
                (physicalObject := .i32 (UInt32.ofNat word.value))
                (targetRest := targetRest) (tail := targetLocals.values)
                (frames := actualFrames) targetLookup imported
                functionSpec.hostsSatisfy inBounds contracted parameterCount
                resultCount operation
          have nextFocus :
              ConcreteStructuredCodeFocus context sourceModule sourceFunction
                [] nextRuntime sourceEnv continuation
                (replaceHeap targetStore heap) targetLocals targetRest witness
                sourceAfter targetAfter := {
            sourceProgramEq := by
              simp [sourceAfter, related.sourceProgramEq]
            sourceControlEq := by simp [sourceAfter]
            sourceEnvEq := by simp [sourceAfter, related.sourceEnvEq]
            sourceRuntimeEq := by simp [sourceAfter]
            targetStoreEq := by simp [targetAfter]
            targetControlEq := by simp [targetAfter]
            adapted := continuationAdapted
            stateRelated := nextRelated
            frameAligned := nextInvariant.1.1.1.1.2.2.1 }
          exact ⟨sourceAfter, targetAfter, replaceHeap targetStore heap,
            targetRest, .single sourcePath, targetPath, nextFocus,
            nextInvariant, by simp [sourceAfter], by simp [sourceAfter],
            by simp [targetAfter]⟩
      | word64 objectRelated => cases objectRelated
      | float32Bits objectRelated => cases objectRelated
      | float64Bits objectRelated => cases objectRelated

/-- One successful ordinary reference-count decrement advances the source by
one effect step and the structured target by the exact generated unary-host
prefix. Recursive release may update an ownership tree, but the concrete
operation supplies the same capacity and ordinary-persistence transports used
to rebuild the full entry-relative frame. -/
theorem ConcreteStructuredCodeFocus.advance_ordinaryDecrement
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode code continuation : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule} {hosts : ResolvedHosts}
    (functionSpec :
      ConcreteSupportedFunction program context functionCode sourceModule
        sourceFunction targetModule hosts)
    {externals : ExternalImpl}
    {facts : ReuseCapacityFacts} {remainingBytes : Nat}
    {sourceRuntime nextRuntime entryRuntime : RuntimeState}
    {sourceEnv : Env}
    {targetStore entryStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {witness entryWitness : RefinementWitness}
    {targetCode : Wasm.Program}
    {source : MachineState} {target : StructuredWasmState Host}
    (supported :
      OrdinaryDecrementEffectSupported context sourceRuntime sourceEnv code
        continuation nextRuntime)
    (sourceStep :
      SourceEffectResult context sourceRuntime nextRuntime sourceEnv code
        continuation)
    (related :
      ConcreteStructuredCodeFocus context sourceModule sourceFunction []
        sourceRuntime sourceEnv code targetStore targetLocals targetCode witness
        source target)
    (invariant :
      ReuseCapacityEntryRelativeFrame
        (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals)
        entryRuntime entryStore entryWitness facts remainingBytes sourceRuntime
        sourceEnv targetStore targetLocals witness) :
    ∃ sourceAfter targetAfter nextStore targetRest,
      FinitePath
          (fun before after => executeStep externals before = .next after)
          1 source sourceAfter ∧
        FinitePath
            (StructuredWasmStep targetModule.wasmModule hosts.env)
            2 target targetAfter ∧
          ConcreteStructuredCodeFocus context sourceModule sourceFunction []
              nextRuntime sourceEnv continuation nextStore targetLocals
              targetRest witness sourceAfter targetAfter ∧
            ReuseCapacityEntryRelativeFrame
              (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
                externals)
              entryRuntime entryStore entryWitness facts remainingBytes
              nextRuntime sourceEnv nextStore targetLocals witness ∧
            sourceAfter.joins = source.joins ∧
              sourceAfter.frames = source.frames ∧
                targetAfter.frames = target.frames := by
  cases supported with
  | dec sourceRuntime nextRuntime sourceEnv objectId amount check objectFields?
      continuation objectKind sourceObject objectCompiled objectRefines
      objectLookup updated =>
      obtain ⟨objectIndex, callIndex, targetRest, objectFound, kindAt,
          callFound, continuationAdapted, targetCodeEq⟩ :=
        CodeAdapted.dec_eq functionSpec.localsAligned objectCompiled
          related.adapted
      subst targetCode
      obtain ⟨imp, imported, inBounds, contracted, parameterCount,
          resultCount⟩ :=
        functionSpec.decrementCall callFound
      have sourceLookup : lookup sourceEnv objectId = some sourceObject := by
        unfold lookupValue at objectLookup
        split at objectLookup
        · rename_i value found
          injection objectLookup with valueEq
          subst value
          exact found
        · contradiction
      obtain ⟨physicalObject, targetLookup, physicalRelated⟩ :=
        related.stateRelated.resolve sourceLookup objectFound kindAt
      have tobjectRelated := physicalRelated.toTObject objectRefines
      cases tobjectRelated with
      | word32 objectRelated =>
          rename_i word
          obtain ⟨heap, operation, runtimeRelated, cursor, capacity⟩ :=
            decrementStep_of_refines_with_capacity
              (objectFields? := objectFields?) related.stateRelated.1
              objectRelated invariant.1.1.2 updated
          have nextRelated :
              StateRelated sourceFunction nextRuntime sourceEnv
                (replaceHeap targetStore heap) targetLocals witness :=
            ⟨runtimeRelated, by simp [replaceHeap, clearFailure],
              related.stateRelated.2.2⟩
          have effectStep :
              EffectStepSimulates context sourceModule sourceFunction []
                targetModule.wasmModule hosts.env sourceRuntime nextRuntime
                sourceEnv
                (.dec objectId amount check false objectFields? continuation)
                continuation
                ([.localGet objectIndex, .call callIndex] ++ targetRest)
                targetRest targetStore (replaceHeap targetStore heap)
                targetLocals witness witness := by
            apply effectStepSimulates_unaryHost
              (spec := hosts.spec)
              (step := decrementStep amount check objectFields?)
            · exact sourceStep
            · exact codeAdapted_dec objectCompiled objectFound callFound
                continuationAdapted
            · exact related.stateRelated
            · exact nextRelated
            · exact targetLookup
            · exact imported
            · exact functionSpec.hostsSatisfy
            · exact inBounds
            · exact contracted
            · exact parameterCount
            · exact resultCount
            · exact operation
          have ordinaryTransport :
              OrdinaryPersistenceTransport sourceRuntime nextRuntime :=
            decValue_ordinaryPersistenceTransport updated
          have sourceGlobals :
              nextRuntime.globals = sourceRuntime.globals :=
            (decValue_runtimeAux updated).globals
          have nextInvariant :
              ReuseCapacityEntryRelativeFrame
                (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
                  externals)
                entryRuntime entryStore entryWitness facts remainingBytes
                nextRuntime sourceEnv (replaceHeap targetStore heap)
                targetLocals witness :=
            invariant.ofReplaceHeapEffectStep effectStep capacity
              ordinaryTransport sourceGlobals cursor
          let sourceAfter : MachineState := {
            source with control := .code continuation
                        runtime := nextRuntime }
          have sourcePath :
              executeStep externals source = .next sourceAfter := by
            rcases source with
              ⟨sourceProgram, sourceControl, actualEnv, sourceJoinEnv,
                sourceFrames, actualRuntime⟩
            have programEq := related.sourceProgramEq
            change sourceProgram = context.program at programEq
            subst sourceProgram
            have controlEq := related.sourceControlEq
            change sourceControl = _ at controlEq
            subst sourceControl
            have envEq := related.sourceEnvEq
            change actualEnv = sourceEnv at envEq
            subst actualEnv
            have runtimeEq := related.sourceRuntimeEq
            change actualRuntime = sourceRuntime at runtimeEq
            subst actualRuntime
            simp [sourceAfter, executeStep, coreStep, objectLookup, updated]
          let targetAfter : StructuredWasmState Host := {
            store := replaceHeap targetStore heap
            control := .running
              { targetLocals with values := targetLocals.values } targetRest
            frames := target.frames }
          have targetPath :
              FinitePath
                (StructuredWasmStep targetModule.wasmModule hosts.env) 2
                target targetAfter := by
            rcases target with ⟨actualStore, actualControl, actualFrames⟩
            have storeEq := related.targetStoreEq
            change actualStore = targetStore at storeEq
            subst actualStore
            have controlEq := related.targetControlEq
            change actualControl =
              .running targetLocals
                ([.localGet objectIndex, .call callIndex] ++ targetRest)
              at controlEq
            subst actualControl
            simpa [targetAfter] using
              structuredWasmUnaryHostEffectPrefixFinitePath
                (module := targetModule.wasmModule) (env := hosts.env)
                (spec := hosts.spec)
                (step := decrementStep amount check objectFields?)
                (initial := targetStore) (final := replaceHeap targetStore heap)
                (locals := targetLocals) (objectIndex := objectIndex)
                (physicalObject := .i32 (UInt32.ofNat word.value))
                (targetRest := targetRest) (tail := targetLocals.values)
                (frames := actualFrames) targetLookup imported
                functionSpec.hostsSatisfy inBounds contracted parameterCount
                resultCount operation
          have nextFocus :
              ConcreteStructuredCodeFocus context sourceModule sourceFunction
                [] nextRuntime sourceEnv continuation
                (replaceHeap targetStore heap) targetLocals targetRest witness
                sourceAfter targetAfter := {
            sourceProgramEq := by
              simp [sourceAfter, related.sourceProgramEq]
            sourceControlEq := by simp [sourceAfter]
            sourceEnvEq := by simp [sourceAfter, related.sourceEnvEq]
            sourceRuntimeEq := by simp [sourceAfter]
            targetStoreEq := by simp [targetAfter]
            targetControlEq := by simp [targetAfter]
            adapted := continuationAdapted
            stateRelated := nextRelated
            frameAligned := nextInvariant.1.1.1.1.2.2.1 }
          exact ⟨sourceAfter, targetAfter, replaceHeap targetStore heap,
            targetRest, .single sourcePath, targetPath, nextFocus,
            nextInvariant, by simp [sourceAfter], by simp [sourceAfter],
            by simp [targetAfter]⟩
      | word64 objectRelated => cases objectRelated
      | float32Bits objectRelated => cases objectRelated
      | float64Bits objectRelated => cases objectRelated

/-- One successful explicit deletion advances the source by one effect step
and the structured target by the exact generated unary-host prefix. Physical
zero is admitted only through the erased-value relation supplied by the shared
delete contract; ordinary object decoding and its mapped-header obligations
remain unchanged. -/
theorem ConcreteStructuredCodeFocus.advance_ordinaryDelete
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode code continuation : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule} {hosts : ResolvedHosts}
    (functionSpec :
      ConcreteSupportedFunction program context functionCode sourceModule
        sourceFunction targetModule hosts)
    {externals : ExternalImpl}
    {facts : ReuseCapacityFacts} {remainingBytes : Nat}
    {sourceRuntime nextRuntime entryRuntime : RuntimeState}
    {sourceEnv : Env}
    {targetStore entryStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {witness entryWitness : RefinementWitness}
    {targetCode : Wasm.Program}
    {source : MachineState} {target : StructuredWasmState Host}
    (supported :
      OrdinaryDeleteEffectSupported context sourceRuntime sourceEnv code
        continuation nextRuntime)
    (sourceStep :
      SourceEffectResult context sourceRuntime nextRuntime sourceEnv code
        continuation)
    (related :
      ConcreteStructuredCodeFocus context sourceModule sourceFunction []
        sourceRuntime sourceEnv code targetStore targetLocals targetCode witness
        source target)
    (invariant :
      ReuseCapacityEntryRelativeFrame
        (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals)
        entryRuntime entryStore entryWitness facts remainingBytes sourceRuntime
        sourceEnv targetStore targetLocals witness) :
    ∃ sourceAfter targetAfter nextStore targetRest,
      FinitePath
          (fun before after => executeStep externals before = .next after)
          1 source sourceAfter ∧
        FinitePath
            (StructuredWasmStep targetModule.wasmModule hosts.env)
            2 target targetAfter ∧
          ConcreteStructuredCodeFocus context sourceModule sourceFunction []
              nextRuntime sourceEnv continuation nextStore targetLocals
              targetRest witness sourceAfter targetAfter ∧
            ReuseCapacityEntryRelativeFrame
              (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
                externals)
              entryRuntime entryStore entryWitness facts remainingBytes
              nextRuntime sourceEnv nextStore targetLocals witness ∧
            sourceAfter.joins = source.joins ∧
              sourceAfter.frames = source.frames ∧
                targetAfter.frames = target.frames := by
  cases supported with
  | del sourceRuntime nextRuntime sourceEnv objectId continuation objectKind
      sourceObject objectCompiled objectLookup updated =>
      obtain ⟨objectIndex, callIndex, targetRest, objectFound, kindAt,
          callFound, continuationAdapted, targetCodeEq⟩ :=
        CodeAdapted.del_eq functionSpec.localsAligned objectCompiled
          related.adapted
      subst targetCode
      obtain ⟨imp, imported, inBounds, contracted, parameterCount,
          resultCount⟩ :=
        functionSpec.deleteCall callFound
      have sourceLookup : lookup sourceEnv objectId = some sourceObject := by
        unfold lookupValue at objectLookup
        split at objectLookup
        · rename_i value found
          injection objectLookup with valueEq
          subst value
          exact found
        · contradiction
      obtain ⟨physicalObject, targetLookup, physicalRelated⟩ :=
        related.stateRelated.resolve sourceLookup objectFound kindAt
      cases physicalRelated with
      | word32 valueRelated =>
          rename_i word
          obtain ⟨heap, operation, runtimeRelated, capacity, cursor⟩ :=
            deleteStep_of_refines_with_capacity related.stateRelated.1
              valueRelated updated
          have nextRelated :
              StateRelated sourceFunction nextRuntime sourceEnv
                (replaceHeap targetStore heap) targetLocals witness :=
            ⟨runtimeRelated, by simp [replaceHeap, clearFailure],
              related.stateRelated.2.2⟩
          have effectStep :
              EffectStepSimulates context sourceModule sourceFunction []
                targetModule.wasmModule hosts.env sourceRuntime nextRuntime
                sourceEnv (.del objectId continuation) continuation
                ([.localGet objectIndex, .call callIndex] ++ targetRest)
                targetRest targetStore (replaceHeap targetStore heap)
                targetLocals witness witness := by
            apply effectStepSimulates_unaryHost
              (spec := hosts.spec) (step := deleteStep)
            · exact sourceStep
            · exact codeAdapted_delete objectCompiled objectFound callFound
                continuationAdapted
            · exact related.stateRelated
            · exact nextRelated
            · exact targetLookup
            · exact imported
            · exact functionSpec.hostsSatisfy
            · exact inBounds
            · exact contracted
            · exact parameterCount
            · exact resultCount
            · exact operation
          have ordinaryTransport :
              OrdinaryPersistenceTransport sourceRuntime nextRuntime :=
            deleteValue_ordinaryPersistenceTransport updated
          have sourceGlobals :
              nextRuntime.globals = sourceRuntime.globals :=
            (deleteValue_runtimeAux updated).globals
          have nextInvariant :
              ReuseCapacityEntryRelativeFrame
                (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
                  externals)
                entryRuntime entryStore entryWitness facts remainingBytes
                nextRuntime sourceEnv (replaceHeap targetStore heap)
                targetLocals witness :=
            invariant.ofReplaceHeapEffectStep effectStep capacity
              ordinaryTransport sourceGlobals cursor
          let sourceAfter : MachineState := {
            source with control := .code continuation
                        runtime := nextRuntime }
          have sourcePath :
              executeStep externals source = .next sourceAfter := by
            rcases source with
              ⟨sourceProgram, sourceControl, actualEnv, sourceJoinEnv,
                sourceFrames, actualRuntime⟩
            have programEq := related.sourceProgramEq
            change sourceProgram = context.program at programEq
            subst sourceProgram
            have controlEq := related.sourceControlEq
            change sourceControl = _ at controlEq
            subst sourceControl
            have envEq := related.sourceEnvEq
            change actualEnv = sourceEnv at envEq
            subst actualEnv
            have runtimeEq := related.sourceRuntimeEq
            change actualRuntime = sourceRuntime at runtimeEq
            subst actualRuntime
            simp [sourceAfter, executeStep, coreStep, objectLookup, updated]
          let targetAfter : StructuredWasmState Host := {
            store := replaceHeap targetStore heap
            control := .running
              { targetLocals with values := targetLocals.values } targetRest
            frames := target.frames }
          have targetPath :
              FinitePath
                (StructuredWasmStep targetModule.wasmModule hosts.env) 2
                target targetAfter := by
            rcases target with ⟨actualStore, actualControl, actualFrames⟩
            have storeEq := related.targetStoreEq
            change actualStore = targetStore at storeEq
            subst actualStore
            have controlEq := related.targetControlEq
            change actualControl =
              .running targetLocals
                ([.localGet objectIndex, .call callIndex] ++ targetRest)
              at controlEq
            subst actualControl
            simpa [targetAfter] using
              structuredWasmUnaryHostEffectPrefixFinitePath
                (module := targetModule.wasmModule) (env := hosts.env)
                (spec := hosts.spec) (step := deleteStep)
                (initial := targetStore) (final := replaceHeap targetStore heap)
                (locals := targetLocals) (objectIndex := objectIndex)
                (physicalObject := .i32 (UInt32.ofNat word.value))
                (targetRest := targetRest) (tail := targetLocals.values)
                (frames := actualFrames) targetLookup imported
                functionSpec.hostsSatisfy inBounds contracted parameterCount
                resultCount operation
          have nextFocus :
              ConcreteStructuredCodeFocus context sourceModule sourceFunction
                [] nextRuntime sourceEnv continuation
                (replaceHeap targetStore heap) targetLocals targetRest witness
                sourceAfter targetAfter := {
            sourceProgramEq := by
              simp [sourceAfter, related.sourceProgramEq]
            sourceControlEq := by simp [sourceAfter]
            sourceEnvEq := by simp [sourceAfter, related.sourceEnvEq]
            sourceRuntimeEq := by simp [sourceAfter]
            targetStoreEq := by simp [targetAfter]
            targetControlEq := by simp [targetAfter]
            adapted := continuationAdapted
            stateRelated := nextRelated
            frameAligned := nextInvariant.1.1.1.1.2.2.1 }
          exact ⟨sourceAfter, targetAfter, replaceHeap targetStore heap,
            targetRest, .single sourcePath, targetPath, nextFocus,
            nextInvariant, by simp [sourceAfter], by simp [sourceAfter],
            by simp [targetAfter]⟩
      | word64 valueRelated =>
          cases valueRelated <;> simp [deleteValue] at updated
      | float32Bits valueRelated => cases valueRelated
      | float64Bits valueRelated => cases valueRelated

/-- One successful constructor-tag mutation advances the source by one effect
step and the structured target by the exact generated unary-host prefix. The
source admission supplies the live-constructor decoder facts; concrete header
refinement and the common replace-heap transport rebuild the recursive frame. -/
theorem ConcreteStructuredCodeFocus.advance_constructorTag
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode code continuation : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule} {hosts : ResolvedHosts}
    (functionSpec :
      ConcreteSupportedFunction program context functionCode sourceModule
        sourceFunction targetModule hosts)
    {externals : ExternalImpl}
    {facts : ReuseCapacityFacts} {remainingBytes : Nat}
    {sourceRuntime nextRuntime entryRuntime : RuntimeState}
    {sourceEnv : Env}
    {targetStore entryStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {witness entryWitness : RefinementWitness}
    {targetCode : Wasm.Program}
    {source : MachineState} {target : StructuredWasmState Host}
    (supported :
      ConstructorTagEffectSupported context sourceRuntime sourceEnv code
        continuation nextRuntime)
    (sourceStep :
      SourceEffectResult context sourceRuntime nextRuntime sourceEnv code
        continuation)
    (related :
      ConcreteStructuredCodeFocus context sourceModule sourceFunction []
        sourceRuntime sourceEnv code targetStore targetLocals targetCode witness
        source target)
    (invariant :
      ReuseCapacityEntryRelativeFrame
        (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals)
        entryRuntime entryStore entryWitness facts remainingBytes sourceRuntime
        sourceEnv targetStore targetLocals witness) :
    ∃ sourceAfter targetAfter nextStore targetRest,
      FinitePath
          (fun before after => executeStep externals before = .next after)
          1 source sourceAfter ∧
        FinitePath
            (StructuredWasmStep targetModule.wasmModule hosts.env)
            2 target targetAfter ∧
          ConcreteStructuredCodeFocus context sourceModule sourceFunction []
              nextRuntime sourceEnv continuation nextStore targetLocals
              targetRest witness sourceAfter targetAfter ∧
            ReuseCapacityEntryRelativeFrame
              (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
                externals)
              entryRuntime entryStore entryWitness facts remainingBytes
              nextRuntime sourceEnv nextStore targetLocals witness ∧
            sourceAfter.joins = source.joins ∧
              sourceAfter.frames = source.frames ∧
                targetAfter.frames = target.frames := by
  cases supported with
  | setTag sourceRuntime nextRuntime sourceEnv objectId tag continuation
      location cell semantic objectCompiled objectLookup updated found live
      objectEq tagFits =>
      obtain ⟨objectIndex, callIndex, targetRest, objectFound, kindAt,
          callFound, continuationAdapted, targetCodeEq⟩ :=
        CodeAdapted.setTag_eq functionSpec.localsAligned objectCompiled
          related.adapted
      subst targetCode
      obtain ⟨imp, imported, inBounds, contracted, parameterCount,
          resultCount⟩ :=
        functionSpec.setTagCall callFound
      have sourceLookup :
          lookup sourceEnv objectId = some (.object (.heap location)) := by
        unfold lookupValue at objectLookup
        split at objectLookup
        · rename_i value foundLookup
          injection objectLookup with valueEq
          subst value
          exact foundLookup
        · contradiction
      obtain ⟨physicalObject, targetLookup, physicalRelated⟩ :=
        related.stateRelated.resolve sourceLookup objectFound kindAt
      cases physicalRelated with
      | word32 objectRelated =>
          rename_i word
          obtain ⟨heap, operation, runtimeRelated, capacity, cursor⟩ :=
            setTagStep_of_refines_with_capacity related.stateRelated.1
              objectRelated found live objectEq updated tagFits
          have nextRelated :
              StateRelated sourceFunction nextRuntime sourceEnv
                (replaceHeap targetStore heap) targetLocals witness :=
            ⟨runtimeRelated, by simp [replaceHeap, clearFailure],
              related.stateRelated.2.2⟩
          have effectStep :
              EffectStepSimulates context sourceModule sourceFunction []
                targetModule.wasmModule hosts.env sourceRuntime nextRuntime
                sourceEnv (.setTag objectId tag continuation) continuation
                ([.localGet objectIndex, .call callIndex] ++ targetRest)
                targetRest targetStore (replaceHeap targetStore heap)
                targetLocals witness witness := by
            apply effectStepSimulates_unaryHost
              (spec := hosts.spec) (step := setTagStep tag)
            · exact sourceStep
            · exact codeAdapted_setTag objectCompiled objectFound callFound
                continuationAdapted
            · exact related.stateRelated
            · exact nextRelated
            · exact targetLookup
            · exact imported
            · exact functionSpec.hostsSatisfy
            · exact inBounds
            · exact contracted
            · exact parameterCount
            · exact resultCount
            · exact operation
          have ordinaryTransport :
              OrdinaryPersistenceTransport sourceRuntime nextRuntime :=
            setTag_ordinaryPersistenceTransport updated
          have sourceGlobals :
              nextRuntime.globals = sourceRuntime.globals :=
            (setTag_runtimeAux updated).globals
          have nextInvariant :
              ReuseCapacityEntryRelativeFrame
                (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
                  externals)
                entryRuntime entryStore entryWitness facts remainingBytes
                nextRuntime sourceEnv (replaceHeap targetStore heap)
                targetLocals witness :=
            invariant.ofReplaceHeapEffectStep effectStep capacity
              ordinaryTransport sourceGlobals cursor
          let sourceAfter : MachineState := {
            source with control := .code continuation
                        runtime := nextRuntime }
          have sourcePath :
              executeStep externals source = .next sourceAfter := by
            rcases source with
              ⟨sourceProgram, sourceControl, actualEnv, sourceJoinEnv,
                sourceFrames, actualRuntime⟩
            have programEq := related.sourceProgramEq
            change sourceProgram = context.program at programEq
            subst sourceProgram
            have controlEq := related.sourceControlEq
            change sourceControl = _ at controlEq
            subst sourceControl
            have envEq := related.sourceEnvEq
            change actualEnv = sourceEnv at envEq
            subst actualEnv
            have runtimeEq := related.sourceRuntimeEq
            change actualRuntime = sourceRuntime at runtimeEq
            subst actualRuntime
            simp [sourceAfter, executeStep, coreStep, objectLookup, updated]
          let targetAfter : StructuredWasmState Host := {
            store := replaceHeap targetStore heap
            control := .running
              { targetLocals with values := targetLocals.values } targetRest
            frames := target.frames }
          have targetPath :
              FinitePath
                (StructuredWasmStep targetModule.wasmModule hosts.env) 2
                target targetAfter := by
            rcases target with ⟨actualStore, actualControl, actualFrames⟩
            have storeEq := related.targetStoreEq
            change actualStore = targetStore at storeEq
            subst actualStore
            have controlEq := related.targetControlEq
            change actualControl =
              .running targetLocals
                ([.localGet objectIndex, .call callIndex] ++ targetRest)
              at controlEq
            subst actualControl
            simpa [targetAfter] using
              structuredWasmUnaryHostEffectPrefixFinitePath
                (module := targetModule.wasmModule) (env := hosts.env)
                (spec := hosts.spec) (step := setTagStep tag)
                (initial := targetStore) (final := replaceHeap targetStore heap)
                (locals := targetLocals) (objectIndex := objectIndex)
                (physicalObject := .i32 (UInt32.ofNat word.value))
                (targetRest := targetRest) (tail := targetLocals.values)
                (frames := actualFrames) targetLookup imported
                functionSpec.hostsSatisfy inBounds contracted parameterCount
                resultCount operation
          have nextFocus :
              ConcreteStructuredCodeFocus context sourceModule sourceFunction
                [] nextRuntime sourceEnv continuation
                (replaceHeap targetStore heap) targetLocals targetRest witness
                sourceAfter targetAfter := {
            sourceProgramEq := by
              simp [sourceAfter, related.sourceProgramEq]
            sourceControlEq := by simp [sourceAfter]
            sourceEnvEq := by simp [sourceAfter, related.sourceEnvEq]
            sourceRuntimeEq := by simp [sourceAfter]
            targetStoreEq := by simp [targetAfter]
            targetControlEq := by simp [targetAfter]
            adapted := continuationAdapted
            stateRelated := nextRelated
            frameAligned := nextInvariant.1.1.1.1.2.2.1 }
          exact ⟨sourceAfter, targetAfter, replaceHeap targetStore heap,
            targetRest, .single sourcePath, targetPath, nextFocus,
            nextInvariant, by simp [sourceAfter], by simp [sourceAfter],
            by simp [targetAfter]⟩
      | word64 valueRelated => cases valueRelated
      | float32Bits valueRelated => cases valueRelated
      | float64Bits valueRelated => cases valueRelated

/-- One successful FVar object-field mutation advances the source by one
effect step and the structured target by the exact generated binary-host
prefix. Descriptor-slot alignment relates the second local at the compiler's
selected ABI kind; the concrete writer and common replace-heap transport then
restore the recursive entry frame. -/
theorem ConcreteStructuredCodeFocus.advance_objectFieldFVar
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode code continuation : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule} {hosts : ResolvedHosts}
    (functionSpec :
      ConcreteSupportedFunction program context functionCode sourceModule
        sourceFunction targetModule hosts)
    {externals : ExternalImpl}
    {facts : ReuseCapacityFacts} {remainingBytes : Nat}
    {sourceRuntime nextRuntime entryRuntime : RuntimeState}
    {sourceEnv : Env}
    {targetStore entryStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {witness entryWitness : RefinementWitness}
    {targetCode : Wasm.Program}
    {source : MachineState} {target : StructuredWasmState Host}
    (supported :
      ObjectFieldFVarEffectSupported context sourceRuntime sourceEnv code
        continuation nextRuntime)
    (sourceStep :
      SourceEffectResult context sourceRuntime nextRuntime sourceEnv code
        continuation)
    (related :
      ConcreteStructuredCodeFocus context sourceModule sourceFunction []
        sourceRuntime sourceEnv code targetStore targetLocals targetCode witness
        source target)
    (invariant :
      ReuseCapacityEntryRelativeFrame
        (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals)
        entryRuntime entryStore entryWitness facts remainingBytes sourceRuntime
        sourceEnv targetStore targetLocals witness) :
    ∃ sourceAfter targetAfter nextStore targetRest,
      FinitePath
          (fun before after => executeStep externals before = .next after)
          1 source sourceAfter ∧
        FinitePath
            (StructuredWasmStep targetModule.wasmModule hosts.env)
            3 target targetAfter ∧
          ConcreteStructuredCodeFocus context sourceModule sourceFunction []
              nextRuntime sourceEnv continuation nextStore targetLocals
              targetRest witness sourceAfter targetAfter ∧
            ReuseCapacityEntryRelativeFrame
              (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
                externals)
              entryRuntime entryStore entryWitness facts remainingBytes
              nextRuntime sourceEnv nextStore targetLocals witness ∧
            sourceAfter.joins = source.joins ∧
              sourceAfter.frames = source.frames ∧
                targetAfter.frames = target.frames := by
  cases supported with
  | oset sourceRuntime nextRuntime sourceEnv objectId fieldId index continuation
      location cell semantic field fieldKind objectCompiled fieldCompiled
      fieldObjectKind objectLookup fieldLookup updated found live objectEq
      indexValid fieldKindAligned =>
      obtain ⟨objectIndex, fieldIndex, callIndex, targetRest, objectFound,
          objectKindAt, fieldFound, fieldKindAt, callFound,
          continuationAdapted, targetCodeEq⟩ :=
        CodeAdapted.objectSetFVar_eq functionSpec.localsAligned objectCompiled
          fieldCompiled related.adapted
      subst targetCode
      have objectSourceLookup :
          lookup sourceEnv objectId = some (.object (.heap location)) := by
        unfold lookupValue at objectLookup
        split at objectLookup
        · rename_i value foundLookup
          injection objectLookup with valueEq
          subst value
          exact foundLookup
        · contradiction
      obtain ⟨physicalObject, targetObjectLookup, physicalObjectRelated⟩ :=
        related.stateRelated.resolve objectSourceLookup objectFound objectKindAt
      cases physicalObjectRelated with
      | word32 objectRelated =>
          rename_i objectWord
          have decoded :
              getConstructor sourceRuntime (.object (.heap location)) =
                .ok (location, cell, semantic) := by
            unfold getConstructor
            simp only [getLiveCell, found, live, if_true, Bind.bind,
              Except.bind]
            rw [objectEq]
            rfl
          have tobjectRelated := objectRelated.object_to_tobject
          obtain ⟨info, fieldKinds, descriptorFound⟩ :=
            ConcreteRuntimeRel.constructorDescriptor_of_getConstructor
              related.stateRelated.1 tobjectRelated decoded
          have fieldDescriptorKindAt :=
            fieldKindAligned tobjectRelated descriptorFound
          obtain ⟨imp, imported, inBounds, contracted, parameterCount,
              resultCount⟩ :=
            functionSpec.objectSetCall callFound
          have fieldArgCompiled :=
            compileArg_fvar_of_getLocal fieldCompiled
          have fieldSourceLookup : lookup sourceEnv fieldId = some field := by
            unfold lookupValue at fieldLookup
            split at fieldLookup
            · rename_i value foundLookup
              injection fieldLookup with valueEq
              subst value
              exact foundLookup
            · contradiction
          obtain ⟨physicalField, targetFieldLookup, physicalFieldRelated⟩ :=
            related.stateRelated.resolve fieldSourceLookup fieldFound fieldKindAt
          cases physicalFieldRelated with
          | word32 fieldRelated =>
              rename_i fieldWord
              obtain ⟨heap, operation, runtimeRelated, capacity, cursor⟩ :=
                objectSetStep_of_refines_with_capacity related.stateRelated.1
                  objectRelated fieldRelated found live objectEq descriptorFound
                  indexValid fieldDescriptorKindAt updated
              have nextRelated :
                  StateRelated sourceFunction nextRuntime sourceEnv
                    (replaceHeap targetStore heap) targetLocals witness :=
                ⟨runtimeRelated, by simp [replaceHeap, clearFailure],
                  related.stateRelated.2.2⟩
              have effectStep :
                  EffectStepSimulates context sourceModule sourceFunction []
                    targetModule.wasmModule hosts.env sourceRuntime nextRuntime
                    sourceEnv
                    (.oset objectId index (.fvar fieldId) continuation)
                    continuation
                    ([.localGet objectIndex, .localGet fieldIndex,
                        .call callIndex] ++ targetRest)
                    targetRest targetStore (replaceHeap targetStore heap)
                    targetLocals witness witness := by
                apply effectStepSimulates_binaryHost
                  (spec := hosts.spec)
                  (step := objectSetStep index fieldKind)
                · exact sourceStep
                · apply codeAdapted_oset
                    (targetField := [.localGet fieldIndex]) objectCompiled
                    fieldArgCompiled objectFound
                  · apply instructions_localGets (fvarIds := [fieldId])
                      (indices := [fieldIndex])
                    exact .cons
                      (by simpa [functionBindings] using fieldFound) .nil
                  · exact callFound
                  · exact continuationAdapted
                · exact related.stateRelated
                · exact nextRelated
                · exact targetObjectLookup
                · exact targetFieldLookup
                · exact imported
                · exact functionSpec.hostsSatisfy
                · exact inBounds
                · exact contracted
                · exact parameterCount
                · exact resultCount
                · exact operation
              have ordinaryTransport :
                  OrdinaryPersistenceTransport sourceRuntime nextRuntime :=
                modifyConstructor_ordinaryPersistenceTransport updated
              have sourceGlobals :
                  nextRuntime.globals = sourceRuntime.globals :=
                (setObjectField_runtimeAux updated).globals
              have nextInvariant :
                  ReuseCapacityEntryRelativeFrame
                    (ConcreteReuseCapacityCacheFrame sourceModule
                      sourceFunction externals)
                    entryRuntime entryStore entryWitness facts remainingBytes
                    nextRuntime sourceEnv (replaceHeap targetStore heap)
                    targetLocals witness :=
                invariant.ofReplaceHeapEffectStep effectStep capacity
                  ordinaryTransport sourceGlobals cursor
              let sourceAfter : MachineState := {
                source with control := .code continuation
                            runtime := nextRuntime }
              have sourcePath :
                  executeStep externals source = .next sourceAfter := by
                rcases source with
                  ⟨sourceProgram, sourceControl, actualEnv, sourceJoinEnv,
                    sourceFrames, actualRuntime⟩
                have programEq := related.sourceProgramEq
                change sourceProgram = context.program at programEq
                subst sourceProgram
                have controlEq := related.sourceControlEq
                change sourceControl = _ at controlEq
                subst sourceControl
                have envEq := related.sourceEnvEq
                change actualEnv = sourceEnv at envEq
                subst actualEnv
                have runtimeEq := related.sourceRuntimeEq
                change actualRuntime = sourceRuntime at runtimeEq
                subst actualRuntime
                change evalArg sourceEnv (.fvar fieldId) = .ok field
                  at fieldLookup
                simp [sourceAfter, executeStep, coreStep, objectLookup,
                  fieldLookup, updated]
              let targetAfter : StructuredWasmState Host := {
                store := replaceHeap targetStore heap
                control := .running
                  { targetLocals with values := targetLocals.values } targetRest
                frames := target.frames }
              have targetPath :
                  FinitePath
                    (StructuredWasmStep targetModule.wasmModule hosts.env) 3
                    target targetAfter := by
                rcases target with ⟨actualStore, actualControl, actualFrames⟩
                have storeEq := related.targetStoreEq
                change actualStore = targetStore at storeEq
                subst actualStore
                have controlEq := related.targetControlEq
                change actualControl =
                  .running targetLocals
                    ([.localGet objectIndex, .localGet fieldIndex,
                        .call callIndex] ++ targetRest)
                  at controlEq
                subst actualControl
                simpa [targetAfter] using
                  structuredWasmBinaryHostEffectPrefixFinitePath
                    (module := targetModule.wasmModule) (env := hosts.env)
                    (spec := hosts.spec)
                    (step := objectSetStep index fieldKind)
                    (initial := targetStore)
                    (final := replaceHeap targetStore heap)
                    (locals := targetLocals) (firstIndex := objectIndex)
                    (secondIndex := fieldIndex)
                    (physicalFirst :=
                      .i32 (UInt32.ofNat objectWord.value))
                    (physicalSecond :=
                      .i32 (UInt32.ofNat fieldWord.value))
                    (targetRest := targetRest) (tail := targetLocals.values)
                    (frames := actualFrames) targetObjectLookup
                    targetFieldLookup imported functionSpec.hostsSatisfy
                    inBounds contracted parameterCount resultCount operation
              have nextFocus :
                  ConcreteStructuredCodeFocus context sourceModule
                    sourceFunction [] nextRuntime sourceEnv continuation
                    (replaceHeap targetStore heap) targetLocals targetRest witness
                    sourceAfter targetAfter := {
                sourceProgramEq := by
                  simp [sourceAfter, related.sourceProgramEq]
                sourceControlEq := by simp [sourceAfter]
                sourceEnvEq := by simp [sourceAfter, related.sourceEnvEq]
                sourceRuntimeEq := by simp [sourceAfter]
                targetStoreEq := by simp [targetAfter]
                targetControlEq := by simp [targetAfter]
                adapted := continuationAdapted
                stateRelated := nextRelated
                frameAligned := nextInvariant.1.1.1.1.2.2.1 }
              exact ⟨sourceAfter, targetAfter, replaceHeap targetStore heap,
                targetRest, .single sourcePath, targetPath, nextFocus,
                nextInvariant, by simp [sourceAfter], by simp [sourceAfter],
                by simp [targetAfter]⟩
          | word64 fieldRelated =>
              cases fieldRelated <;>
                simp [AbiKind.isObjectField] at fieldObjectKind
          | float32Bits fieldRelated => cases fieldRelated
          | float64Bits fieldRelated => cases fieldRelated
      | word64 objectRelated => cases objectRelated
      | float32Bits objectRelated => cases objectRelated
      | float64Bits objectRelated => cases objectRelated

/-- One successful erased object-field mutation advances the source by one
effect step and the structured target by the exact generated
object-local/zero/imported-call prefix. The canonical zero is justified by the
erased ABI relation and never by ordinary object decoding. -/
theorem ConcreteStructuredCodeFocus.advance_objectFieldErased
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode code continuation : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule} {hosts : ResolvedHosts}
    (functionSpec :
      ConcreteSupportedFunction program context functionCode sourceModule
        sourceFunction targetModule hosts)
    {externals : ExternalImpl}
    {facts : ReuseCapacityFacts} {remainingBytes : Nat}
    {sourceRuntime nextRuntime entryRuntime : RuntimeState}
    {sourceEnv : Env}
    {targetStore entryStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {witness entryWitness : RefinementWitness}
    {targetCode : Wasm.Program}
    {source : MachineState} {target : StructuredWasmState Host}
    (supported :
      ObjectFieldErasedEffectSupported context sourceRuntime sourceEnv code
        continuation nextRuntime)
    (sourceStep :
      SourceEffectResult context sourceRuntime nextRuntime sourceEnv code
        continuation)
    (related :
      ConcreteStructuredCodeFocus context sourceModule sourceFunction []
        sourceRuntime sourceEnv code targetStore targetLocals targetCode witness
        source target)
    (invariant :
      ReuseCapacityEntryRelativeFrame
        (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals)
        entryRuntime entryStore entryWitness facts remainingBytes sourceRuntime
        sourceEnv targetStore targetLocals witness) :
    ∃ sourceAfter targetAfter nextStore targetRest,
      FinitePath
          (fun before after => executeStep externals before = .next after)
          1 source sourceAfter ∧
        FinitePath
            (StructuredWasmStep targetModule.wasmModule hosts.env)
            3 target targetAfter ∧
          ConcreteStructuredCodeFocus context sourceModule sourceFunction []
              nextRuntime sourceEnv continuation nextStore targetLocals
              targetRest witness sourceAfter targetAfter ∧
            ReuseCapacityEntryRelativeFrame
              (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
                externals)
              entryRuntime entryStore entryWitness facts remainingBytes
              nextRuntime sourceEnv nextStore targetLocals witness ∧
            sourceAfter.joins = source.joins ∧
              sourceAfter.frames = source.frames ∧
                targetAfter.frames = target.frames := by
  cases supported with
  | oset sourceRuntime nextRuntime sourceEnv objectId index continuation
      location cell semantic objectCompiled objectLookup updated found live
      objectEq indexValid fieldKindAligned =>
      obtain ⟨objectIndex, callIndex, targetRest, objectFound, objectKindAt,
          callFound, continuationAdapted, targetCodeEq⟩ :=
        CodeAdapted.objectSetErased_eq functionSpec.localsAligned
          objectCompiled related.adapted
      subst targetCode
      have objectSourceLookup :
          lookup sourceEnv objectId = some (.object (.heap location)) := by
        unfold lookupValue at objectLookup
        split at objectLookup
        · rename_i value foundLookup
          injection objectLookup with valueEq
          subst value
          exact foundLookup
        · contradiction
      obtain ⟨physicalObject, targetObjectLookup, physicalObjectRelated⟩ :=
        related.stateRelated.resolve objectSourceLookup objectFound objectKindAt
      cases physicalObjectRelated with
      | word32 objectRelated =>
          rename_i objectWord
          have decoded :
              getConstructor sourceRuntime (.object (.heap location)) =
                .ok (location, cell, semantic) := by
            unfold getConstructor
            simp only [getLiveCell, found, live, if_true, Bind.bind,
              Except.bind]
            rw [objectEq]
            rfl
          have tobjectRelated := objectRelated.object_to_tobject
          obtain ⟨info, fieldKinds, descriptorFound⟩ :=
            ConcreteRuntimeRel.constructorDescriptor_of_getConstructor
              related.stateRelated.1 tobjectRelated decoded
          have fieldDescriptorKindAt :=
            fieldKindAligned tobjectRelated descriptorFound
          obtain ⟨imp, imported, inBounds, contracted, parameterCount,
              resultCount⟩ :=
            functionSpec.objectSetCall callFound
          have fieldRelated :
              ValueRel witness .erased (.word32 Word32.zero) .erased :=
            .erased
          obtain ⟨heap, operation, runtimeRelated, capacity, cursor⟩ :=
            objectSetStep_of_refines_with_capacity related.stateRelated.1
              objectRelated fieldRelated found live objectEq descriptorFound
              indexValid fieldDescriptorKindAt updated
          have operationZero :
              objectSetStep index .erased targetStore
                  [.i32 (UInt32.ofNat objectWord.value), .i32 0] =
                .Return [] (replaceHeap targetStore heap) := by
            simpa [Word32.zero] using operation
          have nextRelated :
              StateRelated sourceFunction nextRuntime sourceEnv
                (replaceHeap targetStore heap) targetLocals witness :=
            ⟨runtimeRelated, by simp [replaceHeap, clearFailure],
              related.stateRelated.2.2⟩
          have effectStep :
              EffectStepSimulates context sourceModule sourceFunction []
                targetModule.wasmModule hosts.env sourceRuntime nextRuntime
                sourceEnv (.oset objectId index .erased continuation)
                continuation
                ([.localGet objectIndex, .const 0, .call callIndex] ++
                  targetRest)
                targetRest targetStore (replaceHeap targetStore heap)
                targetLocals witness witness := by
            apply effectStepSimulates_localI32ConstHost
              (spec := hosts.spec)
              (step := objectSetStep index .erased)
            · exact sourceStep
            · apply codeAdapted_oset
                (arg := .erased) (fieldCode := [.i32Const .erased 0])
                (targetField := [.const 0]) objectCompiled (by rfl)
                objectFound
              · simp [instructions, instruction, pure, Except.pure, Bind.bind,
                  Except.bind]
              · exact callFound
              · exact continuationAdapted
            · exact related.stateRelated
            · exact nextRelated
            · exact targetObjectLookup
            · exact imported
            · exact functionSpec.hostsSatisfy
            · exact inBounds
            · exact contracted
            · exact parameterCount
            · exact resultCount
            · exact operationZero
          have ordinaryTransport :
              OrdinaryPersistenceTransport sourceRuntime nextRuntime :=
            modifyConstructor_ordinaryPersistenceTransport updated
          have sourceGlobals :
              nextRuntime.globals = sourceRuntime.globals :=
            (setObjectField_runtimeAux updated).globals
          have nextInvariant :
              ReuseCapacityEntryRelativeFrame
                (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
                  externals)
                entryRuntime entryStore entryWitness facts remainingBytes
                nextRuntime sourceEnv (replaceHeap targetStore heap)
                targetLocals witness :=
            invariant.ofReplaceHeapEffectStep effectStep capacity
              ordinaryTransport sourceGlobals cursor
          let sourceAfter : MachineState := {
            source with control := .code continuation
                        runtime := nextRuntime }
          have sourcePath :
              executeStep externals source = .next sourceAfter := by
            rcases source with
              ⟨sourceProgram, sourceControl, actualEnv, sourceJoinEnv,
                sourceFrames, actualRuntime⟩
            have programEq := related.sourceProgramEq
            change sourceProgram = context.program at programEq
            subst sourceProgram
            have controlEq := related.sourceControlEq
            change sourceControl = _ at controlEq
            subst sourceControl
            have envEq := related.sourceEnvEq
            change actualEnv = sourceEnv at envEq
            subst actualEnv
            have runtimeEq := related.sourceRuntimeEq
            change actualRuntime = sourceRuntime at runtimeEq
            subst actualRuntime
            simp [sourceAfter, executeStep, coreStep, evalArg, objectLookup,
              updated]
          let targetAfter : StructuredWasmState Host := {
            store := replaceHeap targetStore heap
            control := .running
              { targetLocals with values := targetLocals.values } targetRest
            frames := target.frames }
          have targetPath :
              FinitePath
                (StructuredWasmStep targetModule.wasmModule hosts.env) 3
                target targetAfter := by
            rcases target with ⟨actualStore, actualControl, actualFrames⟩
            have storeEq := related.targetStoreEq
            change actualStore = targetStore at storeEq
            subst actualStore
            have controlEq := related.targetControlEq
            change actualControl =
              .running targetLocals
                ([.localGet objectIndex, .const 0, .call callIndex] ++
                  targetRest)
              at controlEq
            subst actualControl
            simpa [targetAfter] using
              structuredWasmLocalI32ConstHostEffectPrefixFinitePath
                (module := targetModule.wasmModule) (env := hosts.env)
                (spec := hosts.spec)
                (step := objectSetStep index .erased)
                (initial := targetStore) (final := replaceHeap targetStore heap)
                (locals := targetLocals) (firstIndex := objectIndex)
                (physicalFirst := .i32 (UInt32.ofNat objectWord.value))
                (constant := 0) (targetRest := targetRest)
                (tail := targetLocals.values) (frames := actualFrames)
                targetObjectLookup imported functionSpec.hostsSatisfy inBounds
                contracted parameterCount resultCount operationZero
          have nextFocus :
              ConcreteStructuredCodeFocus context sourceModule sourceFunction
                [] nextRuntime sourceEnv continuation
                (replaceHeap targetStore heap) targetLocals targetRest witness
                sourceAfter targetAfter := {
            sourceProgramEq := by
              simp [sourceAfter, related.sourceProgramEq]
            sourceControlEq := by simp [sourceAfter]
            sourceEnvEq := by simp [sourceAfter, related.sourceEnvEq]
            sourceRuntimeEq := by simp [sourceAfter]
            targetStoreEq := by simp [targetAfter]
            targetControlEq := by simp [targetAfter]
            adapted := continuationAdapted
            stateRelated := nextRelated
            frameAligned := nextInvariant.1.1.1.1.2.2.1 }
          exact ⟨sourceAfter, targetAfter, replaceHeap targetStore heap,
            targetRest, .single sourcePath, targetPath, nextFocus,
            nextInvariant, by simp [sourceAfter], by simp [sourceAfter],
            by simp [targetAfter]⟩
      | word64 objectRelated => cases objectRelated
      | float32Bits objectRelated => cases objectRelated
      | float64Bits objectRelated => cases objectRelated

/-- One successful `USize` field mutation advances the source by one effect
step and the structured target by the exact generated i32/i64 binary-host
prefix. The concrete checked slot writer preserves the witness, mapped-header
capacity, heap cursor, and all nonheap runtime state needed by recursion. -/
theorem ConcreteStructuredCodeFocus.advance_usizeField
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode code continuation : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule} {hosts : ResolvedHosts}
    (functionSpec :
      ConcreteSupportedFunction program context functionCode sourceModule
        sourceFunction targetModule hosts)
    {externals : ExternalImpl}
    {facts : ReuseCapacityFacts} {remainingBytes : Nat}
    {sourceRuntime nextRuntime entryRuntime : RuntimeState}
    {sourceEnv : Env}
    {targetStore entryStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {witness entryWitness : RefinementWitness}
    {targetCode : Wasm.Program}
    {source : MachineState} {target : StructuredWasmState Host}
    (supported :
      USizeFieldEffectSupported context sourceRuntime sourceEnv code
        continuation nextRuntime)
    (sourceStep :
      SourceEffectResult context sourceRuntime nextRuntime sourceEnv code
        continuation)
    (related :
      ConcreteStructuredCodeFocus context sourceModule sourceFunction []
        sourceRuntime sourceEnv code targetStore targetLocals targetCode witness
        source target)
    (invariant :
      ReuseCapacityEntryRelativeFrame
        (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals)
        entryRuntime entryStore entryWitness facts remainingBytes sourceRuntime
        sourceEnv targetStore targetLocals witness) :
    ∃ sourceAfter targetAfter nextStore targetRest,
      FinitePath
          (fun before after => executeStep externals before = .next after)
          1 source sourceAfter ∧
        FinitePath
            (StructuredWasmStep targetModule.wasmModule hosts.env)
            3 target targetAfter ∧
          ConcreteStructuredCodeFocus context sourceModule sourceFunction []
              nextRuntime sourceEnv continuation nextStore targetLocals
              targetRest witness sourceAfter targetAfter ∧
            ReuseCapacityEntryRelativeFrame
              (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
                externals)
              entryRuntime entryStore entryWitness facts remainingBytes
              nextRuntime sourceEnv nextStore targetLocals witness ∧
            sourceAfter.joins = source.joins ∧
              sourceAfter.frames = source.frames ∧
                targetAfter.frames = target.frames := by
  cases supported with
  | uset sourceRuntime nextRuntime sourceEnv objectId fieldId index continuation
      location cell semantic field objectCompiled fieldCompiled objectLookup
      fieldLookup updated found live objectEq slotStart slotEnd =>
      obtain ⟨objectIndex, fieldIndex, callIndex, targetRest, objectFound,
          objectKindAt, fieldFound, fieldKindAt, callFound,
          continuationAdapted, targetCodeEq⟩ :=
        CodeAdapted.usizeSet_eq functionSpec.localsAligned objectCompiled
          fieldCompiled related.adapted
      subst targetCode
      have objectSourceLookup :
          lookup sourceEnv objectId = some (.object (.heap location)) := by
        unfold lookupValue at objectLookup
        split at objectLookup
        · rename_i value foundLookup
          injection objectLookup with valueEq
          subst value
          exact foundLookup
        · contradiction
      have fieldSourceLookup :
          lookup sourceEnv fieldId = some (.usize field) := by
        unfold lookupValue at fieldLookup
        split at fieldLookup
        · rename_i value foundLookup
          injection fieldLookup with valueEq
          subst value
          exact foundLookup
        · contradiction
      obtain ⟨physicalObject, targetObjectLookup, physicalObjectRelated⟩ :=
        related.stateRelated.resolve objectSourceLookup objectFound objectKindAt
      obtain ⟨physicalField, targetFieldLookup, physicalFieldRelated⟩ :=
        related.stateRelated.resolve fieldSourceLookup fieldFound fieldKindAt
      cases physicalObjectRelated with
      | word32 objectRelated =>
          rename_i objectWord
          cases physicalFieldRelated with
          | word64 fieldRelated =>
              cases fieldRelated with
              | usize =>
                  obtain ⟨imp, imported, inBounds, contracted, parameterCount,
                      resultCount⟩ :=
                    functionSpec.usizeSetCall callFound
                  obtain ⟨heap, operation, runtimeRelated, capacity, cursor⟩ :=
                    usizeSetStep_of_refines_with_capacity
                      related.stateRelated.1 objectRelated found live objectEq
                      slotStart slotEnd updated
                  have nextRelated :
                      StateRelated sourceFunction nextRuntime sourceEnv
                        (replaceHeap targetStore heap) targetLocals witness :=
                    ⟨runtimeRelated, by simp [replaceHeap, clearFailure],
                      related.stateRelated.2.2⟩
                  have effectStep :
                      EffectStepSimulates context sourceModule sourceFunction []
                        targetModule.wasmModule hosts.env sourceRuntime
                        nextRuntime sourceEnv
                        (.uset objectId index fieldId continuation) continuation
                        ([.localGet objectIndex, .localGet fieldIndex,
                            .call callIndex] ++ targetRest)
                        targetRest targetStore (replaceHeap targetStore heap)
                        targetLocals witness witness := by
                    apply effectStepSimulates_binaryHost
                      (spec := hosts.spec) (step := usizeSetStep index)
                    · exact sourceStep
                    · exact codeAdapted_uset objectCompiled fieldCompiled
                        objectFound fieldFound callFound continuationAdapted
                    · exact related.stateRelated
                    · exact nextRelated
                    · exact targetObjectLookup
                    · exact targetFieldLookup
                    · exact imported
                    · exact functionSpec.hostsSatisfy
                    · exact inBounds
                    · exact contracted
                    · exact parameterCount
                    · exact resultCount
                    · exact operation
                  have ordinaryTransport :
                      OrdinaryPersistenceTransport sourceRuntime nextRuntime :=
                    setUSizeSlot_ordinaryPersistenceTransport updated
                  have sourceGlobals :
                      nextRuntime.globals = sourceRuntime.globals :=
                    (setUSizeSlot_runtimeAux updated).globals
                  have nextInvariant :
                      ReuseCapacityEntryRelativeFrame
                        (ConcreteReuseCapacityCacheFrame sourceModule
                          sourceFunction externals)
                        entryRuntime entryStore entryWitness facts
                        remainingBytes nextRuntime sourceEnv
                        (replaceHeap targetStore heap) targetLocals witness :=
                    invariant.ofReplaceHeapEffectStep effectStep capacity
                      ordinaryTransport sourceGlobals cursor
                  let sourceAfter : MachineState := {
                    source with control := .code continuation
                                runtime := nextRuntime }
                  have sourcePath :
                      executeStep externals source = .next sourceAfter := by
                    rcases source with
                      ⟨sourceProgram, sourceControl, actualEnv, sourceJoinEnv,
                        sourceFrames, actualRuntime⟩
                    have programEq := related.sourceProgramEq
                    change sourceProgram = context.program at programEq
                    subst sourceProgram
                    have controlEq := related.sourceControlEq
                    change sourceControl = _ at controlEq
                    subst sourceControl
                    have envEq := related.sourceEnvEq
                    change actualEnv = sourceEnv at envEq
                    subst actualEnv
                    have runtimeEq := related.sourceRuntimeEq
                    change actualRuntime = sourceRuntime at runtimeEq
                    subst actualRuntime
                    simp [sourceAfter, executeStep, coreStep, objectLookup,
                      fieldLookup, updated]
                  let targetAfter : StructuredWasmState Host := {
                    store := replaceHeap targetStore heap
                    control := .running
                      { targetLocals with values := targetLocals.values }
                        targetRest
                    frames := target.frames }
                  have targetPath :
                      FinitePath
                        (StructuredWasmStep targetModule.wasmModule hosts.env) 3
                        target targetAfter := by
                    rcases target with
                      ⟨actualStore, actualControl, actualFrames⟩
                    have storeEq := related.targetStoreEq
                    change actualStore = targetStore at storeEq
                    subst actualStore
                    have controlEq := related.targetControlEq
                    change actualControl =
                      .running targetLocals
                        ([.localGet objectIndex, .localGet fieldIndex,
                            .call callIndex] ++ targetRest)
                      at controlEq
                    subst actualControl
                    simpa [targetAfter] using
                      structuredWasmBinaryHostEffectPrefixFinitePath
                        (module := targetModule.wasmModule) (env := hosts.env)
                        (spec := hosts.spec) (step := usizeSetStep index)
                        (initial := targetStore)
                        (final := replaceHeap targetStore heap)
                        (locals := targetLocals) (firstIndex := objectIndex)
                        (secondIndex := fieldIndex)
                        (physicalFirst :=
                          .i32 (UInt32.ofNat objectWord.value))
                        (physicalSecond := .i64 field)
                        (targetRest := targetRest)
                        (tail := targetLocals.values)
                        (frames := actualFrames) targetObjectLookup
                        targetFieldLookup imported functionSpec.hostsSatisfy
                        inBounds contracted parameterCount resultCount operation
                  have nextFocus :
                      ConcreteStructuredCodeFocus context sourceModule
                        sourceFunction [] nextRuntime sourceEnv continuation
                        (replaceHeap targetStore heap) targetLocals targetRest
                        witness sourceAfter targetAfter := {
                    sourceProgramEq := by
                      simp [sourceAfter, related.sourceProgramEq]
                    sourceControlEq := by simp [sourceAfter]
                    sourceEnvEq := by
                      simp [sourceAfter, related.sourceEnvEq]
                    sourceRuntimeEq := by simp [sourceAfter]
                    targetStoreEq := by simp [targetAfter]
                    targetControlEq := by simp [targetAfter]
                    adapted := continuationAdapted
                    stateRelated := nextRelated
                    frameAligned := nextInvariant.1.1.1.1.2.2.1 }
                  exact ⟨sourceAfter, targetAfter,
                    replaceHeap targetStore heap, targetRest,
                    .single sourcePath, targetPath, nextFocus, nextInvariant,
                    by simp [sourceAfter], by simp [sourceAfter],
                    by simp [targetAfter]⟩
          | word32 fieldRelated => cases fieldRelated
          | float32Bits fieldRelated => cases fieldRelated
          | float64Bits fieldRelated => cases fieldRelated
      | word64 objectRelated => cases objectRelated
      | float32Bits objectRelated => cases objectRelated
      | float64Bits objectRelated => cases objectRelated

/-- Common structured continuation rule for every supported packed-scalar
writer. Width-specific reasoning supplies only the physical second operand and
the checked concrete operation; the generated binary prefix, source step, and
entry-relative frame reconstruction are shared. -/
private theorem ConcreteStructuredCodeFocus.advance_scalarFieldOperation
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule} {hosts : ResolvedHosts}
    (functionSpec :
      ConcreteSupportedFunction program context functionCode sourceModule
        sourceFunction targetModule hosts)
    {externals : ExternalImpl}
    {facts : ReuseCapacityFacts} {remainingBytes : Nat}
    {sourceRuntime nextRuntime entryRuntime : RuntimeState}
    {sourceEnv : Env}
    {objectId fieldId : Lean.FVarId} {slotIndex byteOffset : Nat}
    {type : Lean.Expr}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {location : Location} {field : ScalarValue} {fieldKind : AbiKind}
    {targetStore entryStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {witness entryWitness : RefinementWitness}
    {objectIndex fieldIndex callIndex : Nat}
    {targetRest : Wasm.Program}
    {objectWord : Word32} {physicalField : Wasm.Value}
    {heap : MemoryState} {imp : Wasm.ImportDecl}
    {source : MachineState} {target : StructuredWasmState Host}
    (objectLookup :
      lookupValue sourceEnv objectId = .ok (.object (.heap location)))
    (fieldLookup : lookupValue sourceEnv fieldId = .ok (.scalar field))
    (updated :
      setScalarField sourceRuntime (.object (.heap location)) slotIndex
          byteOffset (.scalar field) =
        .ok nextRuntime)
    (sourceStep :
      SourceEffectResult context sourceRuntime nextRuntime sourceEnv
        (.sset objectId slotIndex byteOffset fieldId type continuation)
        continuation)
    (related :
      ConcreteStructuredCodeFocus context sourceModule sourceFunction []
        sourceRuntime sourceEnv
        (.sset objectId slotIndex byteOffset fieldId type continuation)
        targetStore targetLocals
        ([.localGet objectIndex, .localGet fieldIndex, .call callIndex] ++
          targetRest)
        witness source target)
    (continuationAdapted :
      CodeAdapted context sourceModule sourceFunction [] continuation
        targetRest)
    (invariant :
      ReuseCapacityEntryRelativeFrame
        (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals)
        entryRuntime entryStore entryWitness facts remainingBytes sourceRuntime
        sourceEnv targetStore targetLocals witness)
    (targetObjectLookup :
      targetLocals.get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)))
    (targetFieldLookup : targetLocals.get fieldIndex = some physicalField)
    (imported : targetModule.wasmModule.imports[callIndex]? = some imp)
    (inBounds : callIndex < targetModule.wasmModule.imports.length)
    (contracted : hosts.spec.contracts[callIndex]? = some
      (scalarSetContract slotIndex byteOffset fieldKind))
    (parameterCount : imp.params.length = 2)
    (resultCount : imp.results.length = 0)
    (operation :
      scalarSetStep slotIndex byteOffset fieldKind targetStore
          [.i32 (UInt32.ofNat objectWord.value), physicalField] =
        .Return [] (replaceHeap targetStore heap))
    (runtimeRelated :
      ConcreteRuntimeRel (replaceHeap targetStore heap).host.runtime witness
        nextRuntime)
    (capacity :
      MappedHeaderCapacityTransport targetStore.host.runtime.heap heap witness)
    (cursor : heap.heapCursor = targetStore.host.runtime.heap.heapCursor) :
    ∃ sourceAfter targetAfter nextStore targetRest,
      FinitePath
          (fun before after => executeStep externals before = .next after)
          1 source sourceAfter ∧
        FinitePath
            (StructuredWasmStep targetModule.wasmModule hosts.env)
            3 target targetAfter ∧
          ConcreteStructuredCodeFocus context sourceModule sourceFunction []
              nextRuntime sourceEnv continuation nextStore targetLocals
              targetRest witness sourceAfter targetAfter ∧
            ReuseCapacityEntryRelativeFrame
              (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
                externals)
              entryRuntime entryStore entryWitness facts remainingBytes
              nextRuntime sourceEnv nextStore targetLocals witness ∧
            sourceAfter.joins = source.joins ∧
              sourceAfter.frames = source.frames ∧
                targetAfter.frames = target.frames := by
  have nextRelated :
      StateRelated sourceFunction nextRuntime sourceEnv
        (replaceHeap targetStore heap) targetLocals witness :=
    ⟨runtimeRelated, by simp [replaceHeap, clearFailure],
      related.stateRelated.2.2⟩
  have effectStep :
      EffectStepSimulates context sourceModule sourceFunction []
        targetModule.wasmModule hosts.env sourceRuntime nextRuntime sourceEnv
        (.sset objectId slotIndex byteOffset fieldId type continuation)
        continuation
        ([.localGet objectIndex, .localGet fieldIndex, .call callIndex] ++
          targetRest)
        targetRest targetStore (replaceHeap targetStore heap) targetLocals
        witness witness := by
    apply effectStepSimulates_binaryHost
      (spec := hosts.spec)
      (step := scalarSetStep slotIndex byteOffset fieldKind)
    · exact sourceStep
    · exact related.adapted
    · exact related.stateRelated
    · exact nextRelated
    · exact targetObjectLookup
    · exact targetFieldLookup
    · exact imported
    · exact functionSpec.hostsSatisfy
    · exact inBounds
    · exact contracted
    · exact parameterCount
    · exact resultCount
    · exact operation
  have ordinaryTransport :
      OrdinaryPersistenceTransport sourceRuntime nextRuntime :=
    setScalarField_ordinaryPersistenceTransport updated
  have sourceGlobals : nextRuntime.globals = sourceRuntime.globals :=
    (setScalarField_runtimeAux updated).globals
  have nextInvariant :
      ReuseCapacityEntryRelativeFrame
        (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals)
        entryRuntime entryStore entryWitness facts remainingBytes nextRuntime
        sourceEnv (replaceHeap targetStore heap) targetLocals witness :=
    invariant.ofReplaceHeapEffectStep effectStep capacity ordinaryTransport
      sourceGlobals cursor
  let sourceAfter : MachineState := {
    source with control := .code continuation
                runtime := nextRuntime }
  have sourcePath : executeStep externals source = .next sourceAfter := by
    rcases source with
      ⟨sourceProgram, sourceControl, actualEnv, sourceJoinEnv, sourceFrames,
        actualRuntime⟩
    have programEq := related.sourceProgramEq
    change sourceProgram = context.program at programEq
    subst sourceProgram
    have controlEq := related.sourceControlEq
    change sourceControl = _ at controlEq
    subst sourceControl
    have envEq := related.sourceEnvEq
    change actualEnv = sourceEnv at envEq
    subst actualEnv
    have runtimeEq := related.sourceRuntimeEq
    change actualRuntime = sourceRuntime at runtimeEq
    subst actualRuntime
    simp [sourceAfter, executeStep, coreStep, objectLookup, fieldLookup,
      updated]
  let targetAfter : StructuredWasmState Host := {
    store := replaceHeap targetStore heap
    control := .running
      { targetLocals with values := targetLocals.values } targetRest
    frames := target.frames }
  have targetPath :
      FinitePath (StructuredWasmStep targetModule.wasmModule hosts.env) 3
        target targetAfter := by
    rcases target with ⟨actualStore, actualControl, actualFrames⟩
    have storeEq := related.targetStoreEq
    change actualStore = targetStore at storeEq
    subst actualStore
    have controlEq := related.targetControlEq
    change actualControl =
      .running targetLocals
        ([.localGet objectIndex, .localGet fieldIndex, .call callIndex] ++
          targetRest)
      at controlEq
    subst actualControl
    simpa [targetAfter] using
      structuredWasmBinaryHostEffectPrefixFinitePath
        (module := targetModule.wasmModule) (env := hosts.env)
        (spec := hosts.spec)
        (step := scalarSetStep slotIndex byteOffset fieldKind)
        (initial := targetStore) (final := replaceHeap targetStore heap)
        (locals := targetLocals) (firstIndex := objectIndex)
        (secondIndex := fieldIndex)
        (physicalFirst := .i32 (UInt32.ofNat objectWord.value))
        (physicalSecond := physicalField) (targetRest := targetRest)
        (tail := targetLocals.values) (frames := actualFrames)
        targetObjectLookup targetFieldLookup imported functionSpec.hostsSatisfy
        inBounds contracted parameterCount resultCount operation
  have nextFocus :
      ConcreteStructuredCodeFocus context sourceModule sourceFunction []
        nextRuntime sourceEnv continuation (replaceHeap targetStore heap)
        targetLocals targetRest witness sourceAfter targetAfter := {
    sourceProgramEq := by simp [sourceAfter, related.sourceProgramEq]
    sourceControlEq := by simp [sourceAfter]
    sourceEnvEq := by simp [sourceAfter, related.sourceEnvEq]
    sourceRuntimeEq := by simp [sourceAfter]
    targetStoreEq := by simp [targetAfter]
    targetControlEq := by simp [targetAfter]
    adapted := continuationAdapted
    stateRelated := nextRelated
    frameAligned := nextInvariant.1.1.1.1.2.2.1 }
  exact ⟨sourceAfter, targetAfter, replaceHeap targetStore heap, targetRest,
    .single sourcePath, targetPath, nextFocus, nextInvariant,
    by simp [sourceAfter], by simp [sourceAfter], by simp [targetAfter]⟩

/-- One successful packed-integer scalar mutation advances the source by one
effect step and the structured target by the exact generated binary-host
prefix. Production inversion and state refinement select the i32 lane for
`UInt8`/`UInt16`/`UInt32` and the i64 lane for `UInt64`; each checked writer
then enters the common same-witness continuation rule. -/
theorem ConcreteStructuredCodeFocus.advance_scalarField
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode code continuation : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule} {hosts : ResolvedHosts}
    (functionSpec :
      ConcreteSupportedFunction program context functionCode sourceModule
        sourceFunction targetModule hosts)
    {externals : ExternalImpl}
    {facts : ReuseCapacityFacts} {remainingBytes : Nat}
    {sourceRuntime nextRuntime entryRuntime : RuntimeState}
    {sourceEnv : Env}
    {targetStore entryStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals}
    {witness entryWitness : RefinementWitness}
    {targetCode : Wasm.Program}
    {source : MachineState} {target : StructuredWasmState Host}
    (supported :
      ScalarFieldEffectSupported context sourceRuntime sourceEnv code
        continuation nextRuntime)
    (sourceStep :
      SourceEffectResult context sourceRuntime nextRuntime sourceEnv code
        continuation)
    (related :
      ConcreteStructuredCodeFocus context sourceModule sourceFunction []
        sourceRuntime sourceEnv code targetStore targetLocals targetCode witness
        source target)
    (invariant :
      ReuseCapacityEntryRelativeFrame
        (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals)
        entryRuntime entryStore entryWitness facts remainingBytes sourceRuntime
        sourceEnv targetStore targetLocals witness) :
    ∃ sourceAfter targetAfter nextStore targetRest,
      FinitePath
          (fun before after => executeStep externals before = .next after)
          1 source sourceAfter ∧
        FinitePath
            (StructuredWasmStep targetModule.wasmModule hosts.env)
            3 target targetAfter ∧
          ConcreteStructuredCodeFocus context sourceModule sourceFunction []
              nextRuntime sourceEnv continuation nextStore targetLocals
              targetRest witness sourceAfter targetAfter ∧
            ReuseCapacityEntryRelativeFrame
              (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
                externals)
              entryRuntime entryStore entryWitness facts remainingBytes
              nextRuntime sourceEnv nextStore targetLocals witness ∧
            sourceAfter.joins = source.joins ∧
              sourceAfter.frames = source.frames ∧
                targetAfter.frames = target.frames := by
  cases supported with
  | sset sourceRuntime nextRuntime sourceEnv objectId fieldId slotIndex
      byteOffset type continuation location cell semantic field fieldKind
      objectCompiled fieldCompiled objectLookup fieldLookup updated found live
      objectEq layoutSafe =>
      obtain ⟨objectIndex, fieldIndex, callIndex, targetRest, objectFound,
          objectKindAt, fieldFound, fieldKindAt, callFound,
          continuationAdapted, targetCodeEq⟩ :=
        CodeAdapted.scalarSet_eq functionSpec.localsAligned objectCompiled
          fieldCompiled related.adapted
      subst targetCode
      have objectSourceLookup :
          lookup sourceEnv objectId = some (.object (.heap location)) := by
        unfold lookupValue at objectLookup
        split at objectLookup
        · rename_i value foundLookup
          injection objectLookup with valueEq
          subst value
          exact foundLookup
        · contradiction
      have fieldSourceLookup :
          lookup sourceEnv fieldId = some (.scalar field) := by
        unfold lookupValue at fieldLookup
        split at fieldLookup
        · rename_i value foundLookup
          injection fieldLookup with valueEq
          subst value
          exact foundLookup
        · contradiction
      obtain ⟨physicalObject, targetObjectLookup, physicalObjectRelated⟩ :=
        related.stateRelated.resolve objectSourceLookup objectFound objectKindAt
      obtain ⟨physicalField, targetFieldLookup, physicalFieldRelated⟩ :=
        related.stateRelated.resolve fieldSourceLookup fieldFound fieldKindAt
      cases physicalObjectRelated with
      | word32 objectRelated =>
          rename_i objectWord
          have decoded :
              getConstructor sourceRuntime (.object (.heap location)) =
                .ok (location, cell, semantic) := by
            unfold getConstructor
            simp only [getLiveCell, found, live, if_true, Bind.bind,
              Except.bind]
            rw [objectEq]
            rfl
          have tobjectRelated := objectRelated.object_to_tobject
          obtain ⟨info, fieldKinds, descriptorFound⟩ :=
            ConcreteRuntimeRel.constructorDescriptor_of_getConstructor
              related.stateRelated.1 tobjectRelated decoded
          obtain ⟨historySafe, slotIndexEq, fieldFits⟩ :=
            layoutSafe tobjectRelated descriptorFound
          have fieldSupported : PackedIntegerAbiKind fieldKind := by
            cases fieldKind <;>
              simp [PackedIntegerAbiKind] at fieldFits ⊢
          cases fieldKind with
          | uint8 =>
              obtain ⟨imp, imported, inBounds, contracted, parameterCount,
                  resultCount⟩ :=
                functionSpec.scalarSetCall callFound (by trivial)
              cases physicalFieldRelated with
              | word32 fieldRelated =>
                  rename_i fieldWord
                  cases fieldRelated with
                  | uint8 encoded =>
                      obtain ⟨heap, operation, runtimeRelated, capacity,
                          cursor⟩ :=
                        scalarSetStep_uint8_of_refines_with_capacity
                          related.stateRelated.1 objectRelated (.uint8 encoded)
                          found live objectEq descriptorFound
                          (by simpa using historySafe) slotIndexEq
                          (by simpa using fieldFits) updated
                      exact
                        ConcreteStructuredCodeFocus.advance_scalarFieldOperation
                          functionSpec objectLookup fieldLookup updated sourceStep
                          related continuationAdapted invariant
                          targetObjectLookup targetFieldLookup imported inBounds
                          contracted parameterCount resultCount operation
                          runtimeRelated capacity cursor
              | word64 fieldRelated => cases fieldRelated
              | float32Bits fieldRelated => cases fieldRelated
              | float64Bits fieldRelated => cases fieldRelated
          | uint16 =>
              obtain ⟨imp, imported, inBounds, contracted, parameterCount,
                  resultCount⟩ :=
                functionSpec.scalarSetCall callFound (by trivial)
              cases physicalFieldRelated with
              | word32 fieldRelated =>
                  rename_i fieldWord
                  cases fieldRelated with
                  | uint16 encoded =>
                      obtain ⟨heap, operation, runtimeRelated, capacity,
                          cursor⟩ :=
                        scalarSetStep_uint16_of_refines_with_capacity
                          related.stateRelated.1 objectRelated (.uint16 encoded)
                          found live objectEq descriptorFound
                          (by simpa using historySafe) slotIndexEq
                          (by simpa using fieldFits) updated
                      exact
                        ConcreteStructuredCodeFocus.advance_scalarFieldOperation
                          functionSpec objectLookup fieldLookup updated sourceStep
                          related continuationAdapted invariant
                          targetObjectLookup targetFieldLookup imported inBounds
                          contracted parameterCount resultCount operation
                          runtimeRelated capacity cursor
              | word64 fieldRelated => cases fieldRelated
              | float32Bits fieldRelated => cases fieldRelated
              | float64Bits fieldRelated => cases fieldRelated
          | uint32 =>
              obtain ⟨imp, imported, inBounds, contracted, parameterCount,
                  resultCount⟩ :=
                functionSpec.scalarSetCall callFound (by trivial)
              cases physicalFieldRelated with
              | word32 fieldRelated =>
                  rename_i fieldWord
                  cases fieldRelated with
                  | uint32 encoded =>
                      obtain ⟨heap, operation, runtimeRelated, capacity,
                          cursor⟩ :=
                        scalarSetStep_uint32_of_refines_with_capacity
                          related.stateRelated.1 objectRelated (.uint32 encoded)
                          found live objectEq descriptorFound
                          (by simpa using historySafe) slotIndexEq
                          (by simpa using fieldFits) updated
                      exact
                        ConcreteStructuredCodeFocus.advance_scalarFieldOperation
                          functionSpec objectLookup fieldLookup updated sourceStep
                          related continuationAdapted invariant
                          targetObjectLookup targetFieldLookup imported inBounds
                          contracted parameterCount resultCount operation
                          runtimeRelated capacity cursor
              | word64 fieldRelated => cases fieldRelated
              | float32Bits fieldRelated => cases fieldRelated
              | float64Bits fieldRelated => cases fieldRelated
          | uint64 =>
              obtain ⟨imp, imported, inBounds, contracted, parameterCount,
                  resultCount⟩ :=
                functionSpec.scalarSetCall callFound (by trivial)
              cases physicalFieldRelated with
              | word64 fieldRelated =>
                  cases fieldRelated with
                  | uint64 =>
                      obtain ⟨heap, operation, runtimeRelated, capacity,
                          cursor⟩ :=
                        scalarSetStep_uint64_of_refines_with_capacity
                          related.stateRelated.1 objectRelated .uint64 found live
                          objectEq descriptorFound (by simpa using historySafe)
                          slotIndexEq (by simpa using fieldFits) updated
                      exact
                        ConcreteStructuredCodeFocus.advance_scalarFieldOperation
                          functionSpec objectLookup fieldLookup updated sourceStep
                          related continuationAdapted invariant
                          targetObjectLookup targetFieldLookup imported inBounds
                          contracted parameterCount resultCount operation
                          runtimeRelated capacity cursor
              | word32 fieldRelated => cases fieldRelated
              | float32Bits fieldRelated => cases fieldRelated
              | float64Bits fieldRelated => cases fieldRelated
          | object => simp [PackedIntegerAbiKind] at fieldSupported
          | tagged => simp [PackedIntegerAbiKind] at fieldSupported
          | tobject => simp [PackedIntegerAbiKind] at fieldSupported
          | erased => simp [PackedIntegerAbiKind] at fieldSupported
          | reuseToken => simp [PackedIntegerAbiKind] at fieldSupported
          | usize => simp [PackedIntegerAbiKind] at fieldSupported
          | float32 => simp [PackedIntegerAbiKind] at fieldSupported
          | float => simp [PackedIntegerAbiKind] at fieldSupported
      | word64 objectRelated => cases objectRelated
      | float32Bits objectRelated => cases objectRelated
      | float64Bits objectRelated => cases objectRelated

/-- Recursive structured partial correctness for direct values, supported pure
external results, statically named calls, generated lazy caches, erased
default-case wrappers, arbitrary normalized object and scalar `UInt8`
dispatchers, ownership effects through deletion, constructor-tag mutation,
both FVar and erased object-field mutation, `USize` field mutation, and every
supported packed-integer scalar field mutation.

External results traverse the interpreter's exact three-step request protocol
and the compiler-derived imported-call prefix. A named call is staged by the
production compiler, entered by the structured machine, discharged recursively
in the exact generated declaration row, and returned through the saved
bind/call frames. Both machine paths, the entry-relative concrete resource
frame, the result ABI refinement, and exact restoration of the enclosing frame
stacks are retained. No target trace, callee execution package, or translation
certificate is a premise. -/
theorem
    ConcreteStructuredCodeFocus.reachesYield_reuseBudgetedDirectPureExternalCallsLazyCacheCases_generated
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
    (rootGenerated :
      LazyCacheGeneratedEnvironment rootContext sourceModule)
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
      ReuseCapacityStructuredPureExternalLazyCodeEvaluates externals context
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
  | @defaultCase sourceRuntime sourceEnv cases selected context expectedResult
      facts resultFacts resultRuntime resultEnv resultValue
      requiredBytes supported sourceStep continued ih =>
      let sourceSelected : MachineState := {
        source with control := .code selected }
      have selectSourceStep :
          executeStep externals source = .next sourceSelected := by
        rcases source with
          ⟨sourceProgram, sourceControl, actualEnv, sourceJoinEnv,
            sourceFrames, actualRuntime⟩
        have programEq := related.sourceProgramEq
        change sourceProgram = context.program at programEq
        subst sourceProgram
        have controlEq := related.sourceControlEq
        change sourceControl = .code (.cases cases) at controlEq
        subst sourceControl
        have envEq := related.sourceEnvEq
        change actualEnv = sourceEnv at envEq
        subst actualEnv
        have runtimeEq := related.sourceRuntimeEq
        change actualRuntime = sourceRuntime at runtimeEq
        subst actualRuntime
        rcases sourceStep with ⟨discrValue, tag, found, tagged, chosen⟩
        simp [sourceSelected, executeStep, coreStep, found, tagged, chosen]
      have selectedFocus :
          ConcreteStructuredCodeFocus context sourceModule sourceFunction []
            sourceRuntime sourceEnv selected targetStore targetLocals targetCode
            witness sourceSelected target := {
        sourceProgramEq := by simp [sourceSelected, related.sourceProgramEq]
        sourceControlEq := by simp [sourceSelected]
        sourceEnvEq := by simp [sourceSelected, related.sourceEnvEq]
        sourceRuntimeEq := by simp [sourceSelected, related.sourceRuntimeEq]
        targetStoreEq := related.targetStoreEq
        targetControlEq := related.targetControlEq
        adapted :=
          CodeAdapted.defaultOnlyCases_selected supported related.adapted
        stateRelated := related.stateRelated
        frameAligned := related.frameAligned }
      obtain ⟨sourceAfter, targetAfter, resultStore, resultLocals,
          resultWitness, kind, physical, sourceCount, targetCount, sourceTail,
          targetPath, yielded, resultInvariant, resultRefines, resultJoins,
          sourceFramesEq, targetFramesEq⟩ :=
        ih functionSpec contextCaches selectedFocus
          (by simpa [sourceSelected] using sourceJoins) invariant
      exact ⟨sourceAfter, targetAfter, resultStore, resultLocals,
        resultWitness, kind, physical, 1 + sourceCount, targetCount,
        (FinitePath.single
          (step := fun before after =>
            executeStep externals before = .next after)
          selectSourceStep).trans sourceTail,
        targetPath, yielded, resultInvariant, resultRefines, resultJoins,
        by simpa [sourceSelected] using sourceFramesEq, targetFramesEq⟩
  | @singleObjectCase context sourceRuntime sourceEnv cases selected
      expectedResult facts resultFacts resultRuntime resultEnv resultValue
      requiredBytes supported sourceStep continued ih =>
      rcases supported with
        ⟨info, altsEq, modeEq, expectedTagFits, discrCompiled,
          actualTagFits⟩
      rcases sourceStep with
        ⟨sourceObject, actualTag, lookupFound, tagged, chosen⟩
      have sourceLookup :
          lookup sourceEnv cases.discr = some sourceObject := by
        cases lookupEq : lookup sourceEnv cases.discr with
        | none => simp [lookupValue, lookupEq] at lookupFound
        | some value =>
            have valueEq : value = sourceObject := by
              simpa [lookupValue, lookupEq] using lookupFound
            subst value
            rfl
      have tagEq : actualTag = info.cidx := by
        rw [altsEq] at chosen
        simp [chooseAlt, findCtorAlt, findDefaultAlt] at chosen
        omega
      have actualFits : actualTag < UInt32.size :=
        actualTagFits lookupFound tagged
      have expectedFits : info.cidx < UInt32.size := by
        simpa [Fir.Wasm.constructorTagFitsI32] using expectedTagFits
      obtain ⟨selectedTarget, discrIndex, getTagIndex, selectedAdapted,
          discrFound, getTagFound, targetCodeEq⟩ :=
        CodeAdapted.singleObjectConstructorCases_eq altsEq modeEq
          expectedTagFits related.adapted
      obtain ⟨alignedIndex, alignedFound, discrKind⟩ :=
        functionSpec.localsAligned discrCompiled
      rw [discrFound] at alignedFound
      have alignedEq : alignedIndex = discrIndex :=
        Option.some.inj alignedFound.symm
      subst alignedIndex
      obtain ⟨discrPhysical, targetLookup, physicalRelated⟩ :=
        related.stateRelated.resolve sourceLookup discrFound discrKind
      obtain ⟨word, physicalEq, objectRelated⟩ :
          ∃ word : Word32,
            discrPhysical = .i32 (UInt32.ofNat word.value) ∧
              ValueRel witness .tobject (.word32 word) sourceObject := by
        cases physicalRelated with
        | word32 valueRelated => exact ⟨_, rfl, valueRelated⟩
        | word64 valueRelated => cases valueRelated
        | float32Bits valueRelated => cases valueRelated
        | float64Bits valueRelated => cases valueRelated
      subst discrPhysical
      obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
        functionSpec.runtimeCallsAligned getTagFound
      have getTagContracted :
          hosts.spec.contracts[getTagIndex]? = some getTagContract := by
        change hosts.spec.contracts[getTagIndex]? =
          some (fun initial args result => result = getTagStep initial args)
        simpa only [resolvedContract?, hostFn?, Option.map_some, getTagFn]
          using contracted
      have parameterCount : imp.params.length = 1 := by
        change imp.params.length = 1 at params
        exact params
      have resultCount : imp.results.length = 1 := by
        change imp.results.length = 1 at results
        exact results
      have tagOperation :
          getTagStep targetStore [.i32 (UInt32.ofNat word.value)] =
            .Return [.i32 (UInt32.ofNat info.cidx)] targetStore := by
        have operation :=
          getTagStep_of_refines related.stateRelated.1 objectRelated tagged
            actualFits
        rw [related.stateRelated.clearFailure, tagEq] at operation
        exact operation
      let sourceSelected : MachineState := {
        source with control := .code selected }
      have selectSourceStep :
          executeStep externals source = .next sourceSelected := by
        rcases source with
          ⟨sourceProgram, sourceControl, actualEnv, sourceJoinEnv,
            sourceFrames, actualRuntime⟩
        have programEq := related.sourceProgramEq
        change sourceProgram = context.program at programEq
        subst sourceProgram
        have controlEq := related.sourceControlEq
        change sourceControl = .code (.cases cases) at controlEq
        subst sourceControl
        have envEq := related.sourceEnvEq
        change actualEnv = sourceEnv at envEq
        subst actualEnv
        have runtimeEq := related.sourceRuntimeEq
        change actualRuntime = sourceRuntime at runtimeEq
        subst actualRuntime
        simp [sourceSelected, executeStep, coreStep, lookupFound, tagged,
          chosen]
      let targetSelected : StructuredWasmState Host := {
        store := targetStore
        control := .running
          { targetLocals with values := targetLocals.values } selectedTarget
        frames :=
          .label 0 (targetLocals.values.drop 0) [] :: target.frames }
      have targetPrefix :
          FinitePath
            (StructuredWasmStep targetModule.wasmModule hosts.env) 5 target
            targetSelected := by
        rcases target with ⟨actualStore, actualControl, actualFrames⟩
        have storeEq := related.targetStoreEq
        change actualStore = targetStore at storeEq
        subst actualStore
        have controlEq := related.targetControlEq
        change actualControl = .running targetLocals targetCode at controlEq
        subst actualControl
        subst targetCode
        simpa [targetSelected] using
          structuredWasmObjectCaseHitPrefixFinitePath
            (module := targetModule.wasmModule) (hostEnv := hosts.env)
            (spec := hosts.spec) (store := targetStore)
            (locals := targetLocals) (frames := actualFrames)
            (thenTarget := selectedTarget) (elseTarget := [.unreachable])
            (discrIndex := discrIndex)
            (getTagIndex := getTagIndex) (imp := imp) (word := word)
            (actualTag := info.cidx) (expectedTag := info.cidx) rfl
            targetLookup imported functionSpec.hostsSatisfy
            inBounds getTagContracted parameterCount resultCount tagOperation
      have selectedFocus :
          ConcreteStructuredCodeFocus context sourceModule sourceFunction []
            sourceRuntime sourceEnv selected targetStore
            { targetLocals with values := targetLocals.values } selectedTarget
            witness sourceSelected targetSelected := {
        sourceProgramEq := by simp [sourceSelected, related.sourceProgramEq]
        sourceControlEq := by simp [sourceSelected]
        sourceEnvEq := by simp [sourceSelected, related.sourceEnvEq]
        sourceRuntimeEq := by simp [sourceSelected, related.sourceRuntimeEq]
        targetStoreEq := by simp [targetSelected]
        targetControlEq := by simp [targetSelected]
        adapted := selectedAdapted
        stateRelated := related.stateRelated.withValues targetLocals.values
        frameAligned := related.frameAligned.withValues targetLocals.values }
      obtain ⟨sourceAfter, targetAfter, resultStore, resultLocals,
          resultWitness, kind, physical, sourceCount, targetCount, sourceTail,
          targetTail, yielded, resultInvariant, resultRefines, resultJoins,
          sourceFramesEq, selectedTargetFramesEq⟩ :=
        ih functionSpec contextCaches selectedFocus
          (by simpa [sourceSelected] using sourceJoins)
          (invariant.withValues targetLocals.values)
      let targetFinal : StructuredWasmState Host := {
        store := resultStore
        control := .returning (physical :: resultLocals.values)
        frames := target.frames }
      have unwindTarget :
          StructuredWasmStep targetModule.wasmModule hosts.env targetAfter
            targetFinal := by
        rcases targetAfter with
          ⟨afterStore, afterControl, afterFrames⟩
        have storeEq := yielded.targetStoreEq
        change afterStore = resultStore at storeEq
        subst afterStore
        have controlEq := yielded.targetControlEq
        change afterControl = .returning (physical :: resultLocals.values)
          at controlEq
        subst afterControl
        change afterFrames = _ at selectedTargetFramesEq
        rw [show targetSelected.frames =
          .label 0 (targetLocals.values.drop 0) [] :: target.frames by
            simp [targetSelected]] at selectedTargetFramesEq
        subst afterFrames
        simpa [targetFinal] using
          (StructuredWasmStep.returnLabel
            (module := targetModule.wasmModule) (env := hosts.env)
            (values := physical :: resultLocals.values) (resultArity := 0)
            (belowStack := targetLocals.values.drop 0) (rest := [])
            (store := resultStore) (frames := target.frames))
      have finalYielded :
          ConcreteStructuredYieldFocus context sourceFunction resultRuntime
            resultEnv resultValue resultStore resultLocals resultWitness kind
            physical sourceAfter targetFinal := {
        sourceProgramEq := yielded.sourceProgramEq
        sourceControlEq := yielded.sourceControlEq
        sourceEnvEq := yielded.sourceEnvEq
        sourceRuntimeEq := yielded.sourceRuntimeEq
        targetStoreEq := by simp [targetFinal]
        targetControlEq := by simp [targetFinal]
        stateRelated := yielded.stateRelated
        frameAligned := yielded.frameAligned
        valueRelated := yielded.valueRelated }
      exact ⟨sourceAfter, targetFinal, resultStore, resultLocals,
        resultWitness, kind, physical, 1 + sourceCount, 5 + targetCount + 1,
        (FinitePath.single
          (step := fun before after =>
            executeStep externals before = .next after)
          selectSourceStep).trans sourceTail,
        (targetPrefix.trans targetTail).trans (.single unwindTarget),
        finalYielded, resultInvariant, resultRefines, resultJoins,
        by simpa [sourceSelected] using sourceFramesEq,
        by simp [targetFinal]⟩
  | @twoObjectDefaultCase context sourceRuntime sourceEnv cases selected
      expectedResult facts resultFacts resultRuntime resultEnv resultValue
      requiredBytes supported sourceStep continued ih =>
      rcases supported with
        ⟨firstInfo, secondInfo, firstBranch, secondBranch, defaultBranch,
          altsEq, modeEq, firstTagFits, secondTagFits, discrCompiled,
          actualTagFits⟩
      rcases sourceStep with
        ⟨sourceObject, actualTag, lookupFound, tagged, chosen⟩
      have sourceLookup :
          lookup sourceEnv cases.discr = some sourceObject := by
        cases lookupEq : lookup sourceEnv cases.discr with
        | none => simp [lookupValue, lookupEq] at lookupFound
        | some value =>
            have valueEq : value = sourceObject := by
              simpa [lookupValue, lookupEq] using lookupFound
            subst value
            rfl
      have actualFits : actualTag < UInt32.size :=
        actualTagFits lookupFound tagged
      have firstExpectedFits : firstInfo.cidx < UInt32.size := by
        simpa [Fir.Wasm.constructorTagFitsI32] using firstTagFits
      have secondExpectedFits : secondInfo.cidx < UInt32.size := by
        simpa [Fir.Wasm.constructorTagFitsI32] using secondTagFits
      obtain ⟨firstTarget, secondTarget, defaultTarget, discrIndex,
          getTagIndex, firstAdapted, secondAdapted, defaultAdapted,
          discrFound, getTagFound, targetCodeEq⟩ :=
        CodeAdapted.twoObjectConstructorDefaultCases_eq altsEq modeEq
          firstTagFits secondTagFits related.adapted
      obtain ⟨alignedIndex, alignedFound, discrKind⟩ :=
        functionSpec.localsAligned discrCompiled
      rw [discrFound] at alignedFound
      have alignedEq : alignedIndex = discrIndex :=
        Option.some.inj alignedFound.symm
      subst alignedIndex
      obtain ⟨discrPhysical, targetLookup, physicalRelated⟩ :=
        related.stateRelated.resolve sourceLookup discrFound discrKind
      obtain ⟨word, physicalEq, objectRelated⟩ :
          ∃ word : Word32,
            discrPhysical = .i32 (UInt32.ofNat word.value) ∧
              ValueRel witness .tobject (.word32 word) sourceObject := by
        cases physicalRelated with
        | word32 valueRelated => exact ⟨_, rfl, valueRelated⟩
        | word64 valueRelated => cases valueRelated
        | float32Bits valueRelated => cases valueRelated
        | float64Bits valueRelated => cases valueRelated
      subst discrPhysical
      obtain ⟨imp, imported, inBounds, contracted, params, results⟩ :=
        functionSpec.runtimeCallsAligned getTagFound
      have getTagContracted :
          hosts.spec.contracts[getTagIndex]? = some getTagContract := by
        change hosts.spec.contracts[getTagIndex]? =
          some (fun initial args result => result = getTagStep initial args)
        simpa only [resolvedContract?, hostFn?, Option.map_some, getTagFn]
          using contracted
      have parameterCount : imp.params.length = 1 := by
        change imp.params.length = 1 at params
        exact params
      have resultCount : imp.results.length = 1 := by
        change imp.results.length = 1 at results
        exact results
      have tagOperation :
          getTagStep targetStore [.i32 (UInt32.ofNat word.value)] =
            .Return [.i32 (UInt32.ofNat actualTag)] targetStore := by
        have operation :=
          getTagStep_of_refines related.stateRelated.1 objectRelated tagged
            actualFits
        rw [related.stateRelated.clearFailure] at operation
        exact operation
      let sourceSelected : MachineState := {
        source with control := .code selected }
      have selectSourceStep :
          executeStep externals source = .next sourceSelected := by
        rcases source with
          ⟨sourceProgram, sourceControl, actualEnv, sourceJoinEnv,
            sourceFrames, actualRuntime⟩
        have programEq := related.sourceProgramEq
        change sourceProgram = context.program at programEq
        subst sourceProgram
        have controlEq := related.sourceControlEq
        change sourceControl = .code (.cases cases) at controlEq
        subst sourceControl
        have envEq := related.sourceEnvEq
        change actualEnv = sourceEnv at envEq
        subst actualEnv
        have runtimeEq := related.sourceRuntimeEq
        change actualRuntime = sourceRuntime at runtimeEq
        subst actualRuntime
        simp [sourceSelected, executeStep, coreStep, lookupFound, tagged,
          chosen]
      have targetStateEq :
          target =
            ⟨targetStore, .running targetLocals [
                .localGet discrIndex, .call getTagIndex,
                .const (UInt32.ofNat firstInfo.cidx), .eq,
                .iff 0 0 firstTarget [
                  .localGet discrIndex, .call getTagIndex,
                  .const (UInt32.ofNat secondInfo.cidx), .eq,
                  .iff 0 0 secondTarget defaultTarget]],
              target.frames⟩ := by
        rcases target with ⟨actualStore, actualControl, actualFrames⟩
        have storeEq := related.targetStoreEq
        change actualStore = targetStore at storeEq
        subst actualStore
        have controlEq := related.targetControlEq
        change actualControl = .running targetLocals targetCode at controlEq
        subst actualControl
        subst targetCode
        rfl
      have finishCase
          (selectedTarget : Wasm.Program)
          (selectedAdapted :
            CodeAdapted context sourceModule sourceFunction [] selected
              selectedTarget)
          (testCount : Nat)
          (targetPrefix :
            FinitePath
              (StructuredWasmStep targetModule.wasmModule hosts.env)
              (5 * testCount) target
              ⟨targetStore,
                .running
                  { targetLocals with values := targetLocals.values }
                  selectedTarget,
                List.replicate testCount
                    (.label 0 (targetLocals.values.drop 0) []) ++
                  target.frames⟩) :
          ∃ sourceAfter targetAfter resultStore resultLocals resultWitness kind
              physical sourceCount targetCount,
            FinitePath
                (fun before after =>
                  executeStep externals before = .next after)
                sourceCount source sourceAfter ∧
              FinitePath
                  (StructuredWasmStep targetModule.wasmModule hosts.env)
                  targetCount target targetAfter ∧
                ConcreteStructuredYieldFocus context sourceFunction
                    resultRuntime resultEnv resultValue resultStore resultLocals
                    resultWitness kind physical sourceAfter targetAfter ∧
                  ReuseCapacityEntryRelativeFrame
                      (ConcreteReuseCapacityCacheFrame sourceModule
                        sourceFunction externals)
                      entryRuntime entryStore entryWitness resultFacts slack
                      resultRuntime resultEnv resultStore resultLocals
                      resultWitness ∧
                    kind.refines expectedResult = true ∧
                      sourceAfter.joins = [] ∧
                        sourceAfter.frames = source.frames ∧
                          targetAfter.frames = target.frames := by
        let targetSelected : StructuredWasmState Host := {
          store := targetStore
          control := .running
            { targetLocals with values := targetLocals.values } selectedTarget
          frames :=
            List.replicate testCount
                (.label 0 (targetLocals.values.drop 0) []) ++ target.frames }
        have selectedFocus :
            ConcreteStructuredCodeFocus context sourceModule sourceFunction []
              sourceRuntime sourceEnv selected targetStore
              { targetLocals with values := targetLocals.values }
              selectedTarget witness sourceSelected targetSelected := {
          sourceProgramEq := by simp [sourceSelected, related.sourceProgramEq]
          sourceControlEq := by simp [sourceSelected]
          sourceEnvEq := by simp [sourceSelected, related.sourceEnvEq]
          sourceRuntimeEq := by simp [sourceSelected, related.sourceRuntimeEq]
          targetStoreEq := by simp [targetSelected]
          targetControlEq := by simp [targetSelected]
          adapted := selectedAdapted
          stateRelated := related.stateRelated.withValues targetLocals.values
          frameAligned := related.frameAligned.withValues targetLocals.values }
        obtain ⟨sourceAfter, targetAfter, resultStore, resultLocals,
            resultWitness, kind, physical, sourceCount, targetCount, sourceTail,
            targetTail, yielded, resultInvariant, resultRefines, resultJoins,
            sourceFramesEq, selectedTargetFramesEq⟩ :=
          ih functionSpec contextCaches selectedFocus
            (by simpa [sourceSelected] using sourceJoins)
            (invariant.withValues targetLocals.values)
        let targetFinal : StructuredWasmState Host := {
          store := resultStore
          control := .returning (physical :: resultLocals.values)
          frames := target.frames }
        have unwindTarget :
            FinitePath
              (StructuredWasmStep targetModule.wasmModule hosts.env)
              testCount targetAfter targetFinal := by
          rcases targetAfter with
            ⟨afterStore, afterControl, afterFrames⟩
          have storeEq := yielded.targetStoreEq
          change afterStore = resultStore at storeEq
          subst afterStore
          have controlEq := yielded.targetControlEq
          change afterControl =
            .returning (physical :: resultLocals.values) at controlEq
          subst afterControl
          change afterFrames = _ at selectedTargetFramesEq
          rw [show targetSelected.frames =
              List.replicate testCount
                  (.label 0 (targetLocals.values.drop 0) []) ++
                target.frames by simp [targetSelected]]
            at selectedTargetFramesEq
          subst afterFrames
          simpa [targetFinal] using
            structuredWasmReturnReplicatedCaseLabelsFinitePath
              (module := targetModule.wasmModule) (hostEnv := hosts.env)
              (store := resultStore)
              (values := physical :: resultLocals.values)
              (belowStack := targetLocals.values.drop 0)
              (frames := target.frames) testCount
        have finalYielded :
            ConcreteStructuredYieldFocus context sourceFunction resultRuntime
              resultEnv resultValue resultStore resultLocals resultWitness kind
              physical sourceAfter targetFinal := {
          sourceProgramEq := yielded.sourceProgramEq
          sourceControlEq := yielded.sourceControlEq
          sourceEnvEq := yielded.sourceEnvEq
          sourceRuntimeEq := yielded.sourceRuntimeEq
          targetStoreEq := by simp [targetFinal]
          targetControlEq := by simp [targetFinal]
          stateRelated := yielded.stateRelated
          frameAligned := yielded.frameAligned
          valueRelated := yielded.valueRelated }
        exact ⟨sourceAfter, targetFinal, resultStore, resultLocals,
          resultWitness, kind, physical, 1 + sourceCount,
          5 * testCount + targetCount + testCount,
          (FinitePath.single
            (step := fun before after =>
              executeStep externals before = .next after)
            selectSourceStep).trans sourceTail,
          (targetPrefix.trans targetTail).trans unwindTarget,
          finalYielded, resultInvariant, resultRefines, resultJoins,
          by simpa [sourceSelected] using sourceFramesEq,
          by simp [targetFinal]⟩
      by_cases firstHit : actualTag = firstInfo.cidx
      · have selectedEq : selected = firstBranch := by
          have branchEq : firstBranch = selected := by
            rw [altsEq] at chosen
            simpa [chooseAlt, findCtorAlt, findDefaultAlt, firstHit]
              using chosen
          exact branchEq.symm
        subst selected
        apply finishCase firstTarget firstAdapted 1
        rw [targetStateEq]
        simpa using
          structuredWasmObjectCaseHitPrefixFinitePath
            (module := targetModule.wasmModule) (hostEnv := hosts.env)
            (spec := hosts.spec) (store := targetStore)
            (locals := targetLocals) (frames := target.frames)
            (thenTarget := firstTarget)
            (elseTarget := [
              .localGet discrIndex, .call getTagIndex,
              .const (UInt32.ofNat secondInfo.cidx), .eq,
              .iff 0 0 secondTarget defaultTarget])
            (discrIndex := discrIndex) (getTagIndex := getTagIndex)
            (imp := imp) (word := word) (actualTag := actualTag)
            (expectedTag := firstInfo.cidx) firstHit targetLookup imported
            functionSpec.hostsSatisfy inBounds getTagContracted parameterCount
            resultCount tagOperation
      · by_cases secondHit : actualTag = secondInfo.cidx
        · have selectedEq : selected = secondBranch := by
            have firstMiss' : firstInfo.cidx ≠ actualTag :=
              fun equal => firstHit equal.symm
            have different : firstInfo.cidx ≠ secondInfo.cidx :=
              fun equal => firstHit (secondHit.trans equal.symm)
            have branchEq : secondBranch = selected := by
              rw [altsEq] at chosen
              simpa [chooseAlt, findCtorAlt, findDefaultAlt, firstHit,
                firstMiss', secondHit, different] using chosen
            exact branchEq.symm
          subst selected
          let afterFirstMiss : StructuredWasmState Host :=
            ⟨targetStore,
              .running
                { targetLocals with values := targetLocals.values } [
                  .localGet discrIndex, .call getTagIndex,
                  .const (UInt32.ofNat secondInfo.cidx), .eq,
                  .iff 0 0 secondTarget defaultTarget],
              .label 0 (targetLocals.values.drop 0) [] :: target.frames⟩
          let afterSecondHit : StructuredWasmState Host :=
            ⟨targetStore,
              .running
                { targetLocals with values := targetLocals.values }
                secondTarget,
              .label 0 (targetLocals.values.drop 0) [] ::
                .label 0 (targetLocals.values.drop 0) [] :: target.frames⟩
          have firstPrefix :
              FinitePath
                (StructuredWasmStep targetModule.wasmModule hosts.env) 5
                target afterFirstMiss := by
            rw [targetStateEq]
            simpa [afterFirstMiss] using
              structuredWasmObjectCaseMissPrefixFinitePath
                (module := targetModule.wasmModule) (hostEnv := hosts.env)
                (spec := hosts.spec) (store := targetStore)
                (locals := targetLocals) (frames := target.frames)
                (thenTarget := firstTarget)
                (elseTarget := [
                  .localGet discrIndex, .call getTagIndex,
                  .const (UInt32.ofNat secondInfo.cidx), .eq,
                  .iff 0 0 secondTarget defaultTarget])
                (discrIndex := discrIndex) (getTagIndex := getTagIndex)
                (imp := imp) (word := word) (actualTag := actualTag)
                (expectedTag := firstInfo.cidx) firstHit actualFits
                firstExpectedFits targetLookup imported
                functionSpec.hostsSatisfy inBounds getTagContracted
                parameterCount resultCount tagOperation
          have secondPrefix :
              FinitePath
                (StructuredWasmStep targetModule.wasmModule hosts.env) 5
                afterFirstMiss afterSecondHit := by
            simpa [afterFirstMiss, afterSecondHit] using
              structuredWasmObjectCaseHitPrefixFinitePath
                (module := targetModule.wasmModule) (hostEnv := hosts.env)
                (spec := hosts.spec) (store := targetStore)
                (locals := targetLocals)
                (frames :=
                  .label 0 (targetLocals.values.drop 0) [] :: target.frames)
                (thenTarget := secondTarget) (elseTarget := defaultTarget)
                (discrIndex := discrIndex) (getTagIndex := getTagIndex)
                (imp := imp) (word := word) (actualTag := actualTag)
                (expectedTag := secondInfo.cidx) secondHit targetLookup imported
                functionSpec.hostsSatisfy inBounds getTagContracted
                parameterCount resultCount tagOperation
          apply finishCase secondTarget secondAdapted 2
          simpa [afterSecondHit] using firstPrefix.trans secondPrefix
        · have selectedEq : selected = defaultBranch := by
            have firstMiss' : firstInfo.cidx ≠ actualTag :=
              fun equal => firstHit equal.symm
            have secondMiss' : secondInfo.cidx ≠ actualTag :=
              fun equal => secondHit equal.symm
            have branchEq : defaultBranch = selected := by
              rw [altsEq] at chosen
              simpa [chooseAlt, findCtorAlt, findDefaultAlt, firstHit,
                firstMiss', secondHit, secondMiss'] using chosen
            exact branchEq.symm
          subst selected
          let afterFirstMiss : StructuredWasmState Host :=
            ⟨targetStore,
              .running
                { targetLocals with values := targetLocals.values } [
                  .localGet discrIndex, .call getTagIndex,
                  .const (UInt32.ofNat secondInfo.cidx), .eq,
                  .iff 0 0 secondTarget defaultTarget],
              .label 0 (targetLocals.values.drop 0) [] :: target.frames⟩
          let afterSecondMiss : StructuredWasmState Host :=
            ⟨targetStore,
              .running
                { targetLocals with values := targetLocals.values }
                defaultTarget,
              .label 0 (targetLocals.values.drop 0) [] ::
                .label 0 (targetLocals.values.drop 0) [] :: target.frames⟩
          have firstPrefix :
              FinitePath
                (StructuredWasmStep targetModule.wasmModule hosts.env) 5
                target afterFirstMiss := by
            rw [targetStateEq]
            simpa [afterFirstMiss] using
              structuredWasmObjectCaseMissPrefixFinitePath
                (module := targetModule.wasmModule) (hostEnv := hosts.env)
                (spec := hosts.spec) (store := targetStore)
                (locals := targetLocals) (frames := target.frames)
                (thenTarget := firstTarget)
                (elseTarget := [
                  .localGet discrIndex, .call getTagIndex,
                  .const (UInt32.ofNat secondInfo.cidx), .eq,
                  .iff 0 0 secondTarget defaultTarget])
                (discrIndex := discrIndex) (getTagIndex := getTagIndex)
                (imp := imp) (word := word) (actualTag := actualTag)
                (expectedTag := firstInfo.cidx) firstHit actualFits
                firstExpectedFits targetLookup imported
                functionSpec.hostsSatisfy inBounds getTagContracted
                parameterCount resultCount tagOperation
          have secondPrefix :
              FinitePath
                (StructuredWasmStep targetModule.wasmModule hosts.env) 5
                afterFirstMiss afterSecondMiss := by
            simpa [afterFirstMiss, afterSecondMiss] using
              structuredWasmObjectCaseMissPrefixFinitePath
                (module := targetModule.wasmModule) (hostEnv := hosts.env)
                (spec := hosts.spec) (store := targetStore)
                (locals := targetLocals)
                (frames :=
                  .label 0 (targetLocals.values.drop 0) [] :: target.frames)
                (thenTarget := secondTarget) (elseTarget := defaultTarget)
                (discrIndex := discrIndex) (getTagIndex := getTagIndex)
                (imp := imp) (word := word) (actualTag := actualTag)
                (expectedTag := secondInfo.cidx) secondHit actualFits
                secondExpectedFits targetLookup imported
                functionSpec.hostsSatisfy inBounds getTagContracted
                parameterCount resultCount tagOperation
          apply finishCase defaultTarget defaultAdapted 2
          simpa [afterSecondMiss] using firstPrefix.trans secondPrefix
  | @objectCases context sourceRuntime sourceEnv cases selected expectedResult
      facts resultFacts resultRuntime resultEnv resultValue requiredBytes
      supported sourceStep continued ih =>
      rcases supported with
        ⟨altsSupported, modeEq, discrCompiled, actualTagFits⟩
      rcases sourceStep with
        ⟨sourceObject, actualTag, lookupFound, tagged, chosen⟩
      have sourceLookup :
          lookup sourceEnv cases.discr = some sourceObject := by
        cases lookupEq : lookup sourceEnv cases.discr with
        | none => simp [lookupValue, lookupEq] at lookupFound
        | some value =>
            have valueEq : value = sourceObject := by
              simpa [lookupValue, lookupEq] using lookupFound
            subst value
            rfl
      have actualFits : actualTag < UInt32.size :=
        actualTagFits lookupFound tagged
      rcases CodeAdapted.cases_eq related.adapted with
        ⟨fallback, fallbackCompiled, chainAdapted⟩
      obtain ⟨selectedTarget, testCount, selectedAdapted,
          rawTargetPrefix⟩ :=
        functionSpec.objectConstructorCaseChainFinitePath altsSupported
          modeEq discrCompiled chosen sourceLookup tagged actualFits
          related.stateRelated fallbackCompiled chainAdapted
          (frames := target.frames)
      let sourceSelected : MachineState := {
        source with control := .code selected }
      have selectSourceStep :
          executeStep externals source = .next sourceSelected := by
        rcases source with
          ⟨sourceProgram, sourceControl, actualEnv, sourceJoinEnv,
            sourceFrames, actualRuntime⟩
        have programEq := related.sourceProgramEq
        change sourceProgram = context.program at programEq
        subst sourceProgram
        have controlEq := related.sourceControlEq
        change sourceControl = .code (.cases cases) at controlEq
        subst sourceControl
        have envEq := related.sourceEnvEq
        change actualEnv = sourceEnv at envEq
        subst actualEnv
        have runtimeEq := related.sourceRuntimeEq
        change actualRuntime = sourceRuntime at runtimeEq
        subst actualRuntime
        simp [sourceSelected, executeStep, coreStep, lookupFound, tagged,
          chosen]
      let targetSelected : StructuredWasmState Host := {
        store := targetStore
        control := .running
          { targetLocals with values := targetLocals.values } selectedTarget
        frames :=
          List.replicate testCount
              (.label 0 (targetLocals.values.drop 0) []) ++ target.frames }
      have targetPrefix :
          FinitePath
            (StructuredWasmStep targetModule.wasmModule hosts.env)
            (5 * testCount) target targetSelected := by
        rcases target with ⟨actualStore, actualControl, actualFrames⟩
        have storeEq := related.targetStoreEq
        change actualStore = targetStore at storeEq
        subst actualStore
        have controlEq := related.targetControlEq
        change actualControl = .running targetLocals targetCode at controlEq
        subst actualControl
        simpa [targetSelected] using rawTargetPrefix
      have selectedFocus :
          ConcreteStructuredCodeFocus context sourceModule sourceFunction []
            sourceRuntime sourceEnv selected targetStore
            { targetLocals with values := targetLocals.values } selectedTarget
            witness sourceSelected targetSelected := {
        sourceProgramEq := by simp [sourceSelected, related.sourceProgramEq]
        sourceControlEq := by simp [sourceSelected]
        sourceEnvEq := by simp [sourceSelected, related.sourceEnvEq]
        sourceRuntimeEq := by simp [sourceSelected, related.sourceRuntimeEq]
        targetStoreEq := by simp [targetSelected]
        targetControlEq := by simp [targetSelected]
        adapted := selectedAdapted
        stateRelated := related.stateRelated.withValues targetLocals.values
        frameAligned := related.frameAligned.withValues targetLocals.values }
      obtain ⟨sourceAfter, targetAfter, resultStore, resultLocals,
          resultWitness, kind, physical, sourceCount, targetCount, sourceTail,
          targetTail, yielded, resultInvariant, resultRefines, resultJoins,
          sourceFramesEq, selectedTargetFramesEq⟩ :=
        ih functionSpec contextCaches selectedFocus
          (by simpa [sourceSelected] using sourceJoins)
          (invariant.withValues targetLocals.values)
      let targetFinal : StructuredWasmState Host := {
        store := resultStore
        control := .returning (physical :: resultLocals.values)
        frames := target.frames }
      have unwindTarget :
          FinitePath
            (StructuredWasmStep targetModule.wasmModule hosts.env)
            testCount targetAfter targetFinal := by
        rcases targetAfter with ⟨afterStore, afterControl, afterFrames⟩
        have storeEq := yielded.targetStoreEq
        change afterStore = resultStore at storeEq
        subst afterStore
        have controlEq := yielded.targetControlEq
        change afterControl =
          .returning (physical :: resultLocals.values) at controlEq
        subst afterControl
        change afterFrames = _ at selectedTargetFramesEq
        rw [show targetSelected.frames =
            List.replicate testCount
                (.label 0 (targetLocals.values.drop 0) []) ++ target.frames by
              simp [targetSelected]]
          at selectedTargetFramesEq
        subst afterFrames
        simpa [targetFinal] using
          structuredWasmReturnReplicatedCaseLabelsFinitePath
            (module := targetModule.wasmModule) (hostEnv := hosts.env)
            (store := resultStore)
            (values := physical :: resultLocals.values)
            (belowStack := targetLocals.values.drop 0)
            (frames := target.frames) testCount
      have finalYielded :
          ConcreteStructuredYieldFocus context sourceFunction resultRuntime
            resultEnv resultValue resultStore resultLocals resultWitness kind
            physical sourceAfter targetFinal := {
        sourceProgramEq := yielded.sourceProgramEq
        sourceControlEq := yielded.sourceControlEq
        sourceEnvEq := yielded.sourceEnvEq
        sourceRuntimeEq := yielded.sourceRuntimeEq
        targetStoreEq := by simp [targetFinal]
        targetControlEq := by simp [targetFinal]
        stateRelated := yielded.stateRelated
        frameAligned := yielded.frameAligned
        valueRelated := yielded.valueRelated }
      exact ⟨sourceAfter, targetFinal, resultStore, resultLocals,
        resultWitness, kind, physical, 1 + sourceCount,
        5 * testCount + targetCount + testCount,
        (FinitePath.single
          (step := fun before after =>
            executeStep externals before = .next after)
          selectSourceStep).trans sourceTail,
        (targetPrefix.trans targetTail).trans unwindTarget,
        finalYielded, resultInvariant, resultRefines, resultJoins,
        by simpa [sourceSelected] using sourceFramesEq,
        by simp [targetFinal]⟩
  | @scalarUInt8Cases context sourceRuntime sourceEnv cases selected
      expectedResult facts resultFacts resultRuntime resultEnv resultValue
      requiredBytes supported sourceStep continued ih =>
      rcases supported with ⟨altsSupported, modeEq, discrCompiled⟩
      rcases sourceStep with
        ⟨sourceValue, actualTag, lookupFound, tagged, chosen⟩
      have sourceLookup :
          lookup sourceEnv cases.discr = some sourceValue := by
        cases lookupEq : lookup sourceEnv cases.discr with
        | none => simp [lookupValue, lookupEq] at lookupFound
        | some value =>
            have valueEq : value = sourceValue := by
              simpa [lookupValue, lookupEq] using lookupFound
            subst value
            rfl
      rcases CodeAdapted.cases_eq related.adapted with
        ⟨fallback, fallbackCompiled, chainAdapted⟩
      obtain ⟨selectedTarget, testCount, selectedAdapted,
          rawTargetPrefix⟩ :=
        functionSpec.scalarUInt8CaseChainFinitePath altsSupported modeEq
          discrCompiled chosen sourceLookup tagged related.stateRelated
          fallbackCompiled chainAdapted (frames := target.frames)
      let sourceSelected : MachineState := {
        source with control := .code selected }
      have selectSourceStep :
          executeStep externals source = .next sourceSelected := by
        rcases source with
          ⟨sourceProgram, sourceControl, actualEnv, sourceJoinEnv,
            sourceFrames, actualRuntime⟩
        have programEq := related.sourceProgramEq
        change sourceProgram = context.program at programEq
        subst sourceProgram
        have controlEq := related.sourceControlEq
        change sourceControl = .code (.cases cases) at controlEq
        subst sourceControl
        have envEq := related.sourceEnvEq
        change actualEnv = sourceEnv at envEq
        subst actualEnv
        have runtimeEq := related.sourceRuntimeEq
        change actualRuntime = sourceRuntime at runtimeEq
        subst actualRuntime
        simp [sourceSelected, executeStep, coreStep, lookupFound, tagged,
          chosen]
      let targetSelected : StructuredWasmState Host := {
        store := targetStore
        control := .running
          { targetLocals with values := targetLocals.values } selectedTarget
        frames :=
          List.replicate testCount
              (.label 0 (targetLocals.values.drop 0) []) ++ target.frames }
      have targetPrefix :
          FinitePath
            (StructuredWasmStep targetModule.wasmModule hosts.env)
            (4 * testCount) target targetSelected := by
        rcases target with ⟨actualStore, actualControl, actualFrames⟩
        have storeEq := related.targetStoreEq
        change actualStore = targetStore at storeEq
        subst actualStore
        have controlEq := related.targetControlEq
        change actualControl = .running targetLocals targetCode at controlEq
        subst actualControl
        simpa [targetSelected] using rawTargetPrefix
      have selectedFocus :
          ConcreteStructuredCodeFocus context sourceModule sourceFunction []
            sourceRuntime sourceEnv selected targetStore
            { targetLocals with values := targetLocals.values } selectedTarget
            witness sourceSelected targetSelected := {
        sourceProgramEq := by simp [sourceSelected, related.sourceProgramEq]
        sourceControlEq := by simp [sourceSelected]
        sourceEnvEq := by simp [sourceSelected, related.sourceEnvEq]
        sourceRuntimeEq := by simp [sourceSelected, related.sourceRuntimeEq]
        targetStoreEq := by simp [targetSelected]
        targetControlEq := by simp [targetSelected]
        adapted := selectedAdapted
        stateRelated := related.stateRelated.withValues targetLocals.values
        frameAligned := related.frameAligned.withValues targetLocals.values }
      obtain ⟨sourceAfter, targetAfter, resultStore, resultLocals,
          resultWitness, kind, physical, sourceCount, targetCount, sourceTail,
          targetTail, yielded, resultInvariant, resultRefines, resultJoins,
          sourceFramesEq, selectedTargetFramesEq⟩ :=
        ih functionSpec contextCaches selectedFocus
          (by simpa [sourceSelected] using sourceJoins)
          (invariant.withValues targetLocals.values)
      let targetFinal : StructuredWasmState Host := {
        store := resultStore
        control := .returning (physical :: resultLocals.values)
        frames := target.frames }
      have unwindTarget :
          FinitePath
            (StructuredWasmStep targetModule.wasmModule hosts.env)
            testCount targetAfter targetFinal := by
        rcases targetAfter with ⟨afterStore, afterControl, afterFrames⟩
        have storeEq := yielded.targetStoreEq
        change afterStore = resultStore at storeEq
        subst afterStore
        have controlEq := yielded.targetControlEq
        change afterControl =
          .returning (physical :: resultLocals.values) at controlEq
        subst afterControl
        change afterFrames = _ at selectedTargetFramesEq
        rw [show targetSelected.frames =
            List.replicate testCount
                (.label 0 (targetLocals.values.drop 0) []) ++ target.frames by
              simp [targetSelected]]
          at selectedTargetFramesEq
        subst afterFrames
        simpa [targetFinal] using
          structuredWasmReturnReplicatedCaseLabelsFinitePath
            (module := targetModule.wasmModule) (hostEnv := hosts.env)
            (store := resultStore)
            (values := physical :: resultLocals.values)
            (belowStack := targetLocals.values.drop 0)
            (frames := target.frames) testCount
      have finalYielded :
          ConcreteStructuredYieldFocus context sourceFunction resultRuntime
            resultEnv resultValue resultStore resultLocals resultWitness kind
            physical sourceAfter targetFinal := {
        sourceProgramEq := yielded.sourceProgramEq
        sourceControlEq := yielded.sourceControlEq
        sourceEnvEq := yielded.sourceEnvEq
        sourceRuntimeEq := yielded.sourceRuntimeEq
        targetStoreEq := by simp [targetFinal]
        targetControlEq := by simp [targetFinal]
        stateRelated := yielded.stateRelated
        frameAligned := yielded.frameAligned
        valueRelated := yielded.valueRelated }
      exact ⟨sourceAfter, targetFinal, resultStore, resultLocals,
        resultWitness, kind, physical, 1 + sourceCount,
        4 * testCount + targetCount + testCount,
        (FinitePath.single
          (step := fun before after =>
            executeStep externals before = .next after)
          selectSourceStep).trans sourceTail,
        (targetPrefix.trans targetTail).trans unwindTarget,
        finalYielded, resultInvariant, resultRefines, resultJoins,
        by simpa [sourceSelected] using sourceFramesEq,
        by simp [targetFinal]⟩
  | @persistentOwnershipEffect sourceRuntime sourceEnv code continuation
      nextRuntime context expectedResult facts resultFacts resultRuntime
      resultEnv resultValue requiredBytes supported _sourceStep continued ih =>
      cases supported with
      | inc =>
          let sourceMiddle : MachineState := {
            source with control := .code continuation }
          have firstSourceStep :
              executeStep externals source = .next sourceMiddle := by
            rcases source with
              ⟨sourceProgram, sourceControl, actualEnv, sourceJoinEnv,
                sourceFrames, actualRuntime⟩
            have controlEq := related.sourceControlEq
            change sourceControl = _ at controlEq
            subst sourceControl
            rfl
          have nextFocus :
              ConcreteStructuredCodeFocus context sourceModule sourceFunction
                [] sourceRuntime sourceEnv continuation targetStore targetLocals
                targetCode witness sourceMiddle target := {
            sourceProgramEq := by
              simp [sourceMiddle, related.sourceProgramEq]
            sourceControlEq := by simp [sourceMiddle]
            sourceEnvEq := by simp [sourceMiddle, related.sourceEnvEq]
            sourceRuntimeEq := by
              simp [sourceMiddle, related.sourceRuntimeEq]
            targetStoreEq := related.targetStoreEq
            targetControlEq := related.targetControlEq
            adapted := CodeAdapted.incPersistent_eq related.adapted
            stateRelated := related.stateRelated
            frameAligned := related.frameAligned }
          obtain ⟨sourceAfter, targetAfter, resultStore, resultLocals,
              resultWitness, kind, physical, sourceCount, targetCount,
              sourceTail, targetPath, yielded, resultInvariant,
              resultRefines, resultJoins, sourceFramesEq, targetFramesEq⟩ :=
            ih functionSpec contextCaches nextFocus
              (by simpa [sourceMiddle] using sourceJoins)
              invariant
          exact ⟨sourceAfter, targetAfter, resultStore, resultLocals,
            resultWitness, kind, physical, 1 + sourceCount, targetCount,
            (FinitePath.single
              (step := fun before after =>
                executeStep externals before = .next after)
              firstSourceStep).trans sourceTail,
            targetPath, yielded, resultInvariant, resultRefines, resultJoins,
            by simpa [sourceMiddle] using sourceFramesEq, targetFramesEq⟩
      | dec =>
          let sourceMiddle : MachineState := {
            source with control := .code continuation }
          have firstSourceStep :
              executeStep externals source = .next sourceMiddle := by
            rcases source with
              ⟨sourceProgram, sourceControl, actualEnv, sourceJoinEnv,
                sourceFrames, actualRuntime⟩
            have controlEq := related.sourceControlEq
            change sourceControl = _ at controlEq
            subst sourceControl
            rfl
          have nextFocus :
              ConcreteStructuredCodeFocus context sourceModule sourceFunction
                [] sourceRuntime sourceEnv continuation targetStore targetLocals
                targetCode witness sourceMiddle target := {
            sourceProgramEq := by
              simp [sourceMiddle, related.sourceProgramEq]
            sourceControlEq := by simp [sourceMiddle]
            sourceEnvEq := by simp [sourceMiddle, related.sourceEnvEq]
            sourceRuntimeEq := by
              simp [sourceMiddle, related.sourceRuntimeEq]
            targetStoreEq := related.targetStoreEq
            targetControlEq := related.targetControlEq
            adapted := CodeAdapted.decPersistent_eq related.adapted
            stateRelated := related.stateRelated
            frameAligned := related.frameAligned }
          obtain ⟨sourceAfter, targetAfter, resultStore, resultLocals,
              resultWitness, kind, physical, sourceCount, targetCount,
              sourceTail, targetPath, yielded, resultInvariant,
              resultRefines, resultJoins, sourceFramesEq, targetFramesEq⟩ :=
            ih functionSpec contextCaches nextFocus
              (by simpa [sourceMiddle] using sourceJoins)
              invariant
          exact ⟨sourceAfter, targetAfter, resultStore, resultLocals,
            resultWitness, kind, physical, 1 + sourceCount, targetCount,
            (FinitePath.single
              (step := fun before after =>
                executeStep externals before = .next after)
              firstSourceStep).trans sourceTail,
            targetPath, yielded, resultInvariant, resultRefines, resultJoins,
            by simpa [sourceMiddle] using sourceFramesEq, targetFramesEq⟩
  | @ordinaryIncrementEffect sourceRuntime sourceEnv code continuation
      nextRuntime context expectedResult facts resultFacts resultRuntime
      resultEnv resultValue requiredBytes supported sourceStep continued ih =>
      obtain ⟨sourceMiddle, targetMiddle, nextStore, targetRest, sourcePrefix,
          targetPrefix, nextFocus, nextInvariant, sourceMiddleJoins,
          sourceMiddleFrames, targetMiddleFrames⟩ :=
        related.advance_ordinaryIncrement functionSpec supported sourceStep
          invariant
      obtain ⟨sourceAfter, targetAfter, resultStore, resultLocals,
          resultWitness, kind, physical, sourceCount, targetCount, sourceTail,
          targetTail, yielded, resultInvariant, resultRefines, resultJoins,
          sourceFramesEq, targetFramesEq⟩ :=
        ih functionSpec contextCaches nextFocus
          (sourceMiddleJoins.trans sourceJoins) nextInvariant
      exact ⟨sourceAfter, targetAfter, resultStore, resultLocals,
        resultWitness, kind, physical, 1 + sourceCount, 2 + targetCount,
        sourcePrefix.trans sourceTail, targetPrefix.trans targetTail, yielded,
        resultInvariant, resultRefines, resultJoins,
        sourceFramesEq.trans sourceMiddleFrames,
        targetFramesEq.trans targetMiddleFrames⟩
  | @ordinaryDecrementEffect sourceRuntime sourceEnv code continuation
      nextRuntime context expectedResult facts resultFacts resultRuntime
      resultEnv resultValue requiredBytes supported sourceStep continued ih =>
      obtain ⟨sourceMiddle, targetMiddle, nextStore, targetRest, sourcePrefix,
          targetPrefix, nextFocus, nextInvariant, sourceMiddleJoins,
          sourceMiddleFrames, targetMiddleFrames⟩ :=
        related.advance_ordinaryDecrement functionSpec supported sourceStep
          invariant
      obtain ⟨sourceAfter, targetAfter, resultStore, resultLocals,
          resultWitness, kind, physical, sourceCount, targetCount, sourceTail,
          targetTail, yielded, resultInvariant, resultRefines, resultJoins,
          sourceFramesEq, targetFramesEq⟩ :=
        ih functionSpec contextCaches nextFocus
          (sourceMiddleJoins.trans sourceJoins) nextInvariant
      exact ⟨sourceAfter, targetAfter, resultStore, resultLocals,
        resultWitness, kind, physical, 1 + sourceCount, 2 + targetCount,
        sourcePrefix.trans sourceTail, targetPrefix.trans targetTail, yielded,
        resultInvariant, resultRefines, resultJoins,
        sourceFramesEq.trans sourceMiddleFrames,
        targetFramesEq.trans targetMiddleFrames⟩
  | @ordinaryDeleteEffect sourceRuntime sourceEnv code continuation
      nextRuntime context expectedResult facts resultFacts resultRuntime
      resultEnv resultValue requiredBytes supported sourceStep continued ih =>
      obtain ⟨sourceMiddle, targetMiddle, nextStore, targetRest, sourcePrefix,
          targetPrefix, nextFocus, nextInvariant, sourceMiddleJoins,
          sourceMiddleFrames, targetMiddleFrames⟩ :=
        related.advance_ordinaryDelete functionSpec supported sourceStep
          invariant
      obtain ⟨sourceAfter, targetAfter, resultStore, resultLocals,
          resultWitness, kind, physical, sourceCount, targetCount, sourceTail,
          targetTail, yielded, resultInvariant, resultRefines, resultJoins,
          sourceFramesEq, targetFramesEq⟩ :=
        ih functionSpec contextCaches nextFocus
          (sourceMiddleJoins.trans sourceJoins) nextInvariant
      exact ⟨sourceAfter, targetAfter, resultStore, resultLocals,
        resultWitness, kind, physical, 1 + sourceCount, 2 + targetCount,
        sourcePrefix.trans sourceTail, targetPrefix.trans targetTail, yielded,
        resultInvariant, resultRefines, resultJoins,
        sourceFramesEq.trans sourceMiddleFrames,
        targetFramesEq.trans targetMiddleFrames⟩
  | @constructorTagEffect sourceRuntime sourceEnv code continuation
      nextRuntime context expectedResult facts resultFacts resultRuntime
      resultEnv resultValue requiredBytes supported sourceStep continued ih =>
      obtain ⟨sourceMiddle, targetMiddle, nextStore, targetRest, sourcePrefix,
          targetPrefix, nextFocus, nextInvariant, sourceMiddleJoins,
          sourceMiddleFrames, targetMiddleFrames⟩ :=
        related.advance_constructorTag functionSpec supported sourceStep
          invariant
      obtain ⟨sourceAfter, targetAfter, resultStore, resultLocals,
          resultWitness, kind, physical, sourceCount, targetCount, sourceTail,
          targetTail, yielded, resultInvariant, resultRefines, resultJoins,
          sourceFramesEq, targetFramesEq⟩ :=
        ih functionSpec contextCaches nextFocus
          (sourceMiddleJoins.trans sourceJoins) nextInvariant
      exact ⟨sourceAfter, targetAfter, resultStore, resultLocals,
        resultWitness, kind, physical, 1 + sourceCount, 2 + targetCount,
        sourcePrefix.trans sourceTail, targetPrefix.trans targetTail, yielded,
        resultInvariant, resultRefines, resultJoins,
        sourceFramesEq.trans sourceMiddleFrames,
        targetFramesEq.trans targetMiddleFrames⟩
  | @objectFieldFVarEffect sourceRuntime sourceEnv code continuation
      nextRuntime context expectedResult facts resultFacts resultRuntime
      resultEnv resultValue requiredBytes supported sourceStep continued ih =>
      obtain ⟨sourceMiddle, targetMiddle, nextStore, targetRest, sourcePrefix,
          targetPrefix, nextFocus, nextInvariant, sourceMiddleJoins,
          sourceMiddleFrames, targetMiddleFrames⟩ :=
        related.advance_objectFieldFVar functionSpec supported sourceStep
          invariant
      obtain ⟨sourceAfter, targetAfter, resultStore, resultLocals,
          resultWitness, kind, physical, sourceCount, targetCount, sourceTail,
          targetTail, yielded, resultInvariant, resultRefines, resultJoins,
          sourceFramesEq, targetFramesEq⟩ :=
        ih functionSpec contextCaches nextFocus
          (sourceMiddleJoins.trans sourceJoins) nextInvariant
      exact ⟨sourceAfter, targetAfter, resultStore, resultLocals,
        resultWitness, kind, physical, 1 + sourceCount, 3 + targetCount,
        sourcePrefix.trans sourceTail, targetPrefix.trans targetTail, yielded,
        resultInvariant, resultRefines, resultJoins,
        sourceFramesEq.trans sourceMiddleFrames,
        targetFramesEq.trans targetMiddleFrames⟩
  | @objectFieldErasedEffect sourceRuntime sourceEnv code continuation
      nextRuntime context expectedResult facts resultFacts resultRuntime
      resultEnv resultValue requiredBytes supported sourceStep continued ih =>
      obtain ⟨sourceMiddle, targetMiddle, nextStore, targetRest, sourcePrefix,
          targetPrefix, nextFocus, nextInvariant, sourceMiddleJoins,
          sourceMiddleFrames, targetMiddleFrames⟩ :=
        related.advance_objectFieldErased functionSpec supported sourceStep
          invariant
      obtain ⟨sourceAfter, targetAfter, resultStore, resultLocals,
          resultWitness, kind, physical, sourceCount, targetCount, sourceTail,
          targetTail, yielded, resultInvariant, resultRefines, resultJoins,
          sourceFramesEq, targetFramesEq⟩ :=
        ih functionSpec contextCaches nextFocus
          (sourceMiddleJoins.trans sourceJoins) nextInvariant
      exact ⟨sourceAfter, targetAfter, resultStore, resultLocals,
        resultWitness, kind, physical, 1 + sourceCount, 3 + targetCount,
        sourcePrefix.trans sourceTail, targetPrefix.trans targetTail, yielded,
        resultInvariant, resultRefines, resultJoins,
        sourceFramesEq.trans sourceMiddleFrames,
        targetFramesEq.trans targetMiddleFrames⟩
  | @usizeFieldEffect sourceRuntime sourceEnv code continuation nextRuntime
      context expectedResult facts resultFacts resultRuntime resultEnv
      resultValue requiredBytes supported sourceStep continued ih =>
      obtain ⟨sourceMiddle, targetMiddle, nextStore, targetRest, sourcePrefix,
          targetPrefix, nextFocus, nextInvariant, sourceMiddleJoins,
          sourceMiddleFrames, targetMiddleFrames⟩ :=
        related.advance_usizeField functionSpec supported sourceStep invariant
      obtain ⟨sourceAfter, targetAfter, resultStore, resultLocals,
          resultWitness, kind, physical, sourceCount, targetCount, sourceTail,
          targetTail, yielded, resultInvariant, resultRefines, resultJoins,
          sourceFramesEq, targetFramesEq⟩ :=
        ih functionSpec contextCaches nextFocus
          (sourceMiddleJoins.trans sourceJoins) nextInvariant
      exact ⟨sourceAfter, targetAfter, resultStore, resultLocals,
        resultWitness, kind, physical, 1 + sourceCount, 3 + targetCount,
        sourcePrefix.trans sourceTail, targetPrefix.trans targetTail, yielded,
        resultInvariant, resultRefines, resultJoins,
        sourceFramesEq.trans sourceMiddleFrames,
        targetFramesEq.trans targetMiddleFrames⟩
  | @scalarFieldEffect sourceRuntime sourceEnv code continuation nextRuntime
      context expectedResult facts resultFacts resultRuntime resultEnv
      resultValue requiredBytes supported sourceStep continued ih =>
      obtain ⟨sourceMiddle, targetMiddle, nextStore, targetRest, sourcePrefix,
          targetPrefix, nextFocus, nextInvariant, sourceMiddleJoins,
          sourceMiddleFrames, targetMiddleFrames⟩ :=
        related.advance_scalarField functionSpec supported sourceStep invariant
      obtain ⟨sourceAfter, targetAfter, resultStore, resultLocals,
          resultWitness, kind, physical, sourceCount, targetCount, sourceTail,
          targetTail, yielded, resultInvariant, resultRefines, resultJoins,
          sourceFramesEq, targetFramesEq⟩ :=
        ih functionSpec contextCaches nextFocus
          (sourceMiddleJoins.trans sourceJoins) nextInvariant
      exact ⟨sourceAfter, targetAfter, resultStore, resultLocals,
        resultWitness, kind, physical, 1 + sourceCount, 3 + targetCount,
        sourcePrefix.trans sourceTail, targetPrefix.trans targetTail, yielded,
        resultInvariant, resultRefines, resultJoins,
        sourceFramesEq.trans sourceMiddleFrames,
        targetFramesEq.trans targetMiddleFrames⟩
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
  | @lazyHit context decl declaration sourceDeclaration resultKind
      sourceRuntime sourceEnv continuation nextRuntime sourceValue facts
      nextFacts expectedResult resultFacts resultRuntime resultEnv resultValue
      continuationCost call sourceStep transfer continued ih =>
        obtain ⟨valueCode, restCode, targetValue, targetRest, resultIndex,
            valueCompiled, restCompiled, valueAdapted, restAdapted, resultFound,
            targetCodeEq⟩ :=
          CodeAdapted.let_eq related.adapted
        have continuationAdapted :
            CodeAdapted context sourceModule sourceFunction [] continuation
              targetRest :=
          ⟨restCode, restCompiled, restAdapted⟩
        have ordinaryLowering :
            Fir.Wasm.lower program = .ok sourceModule :=
          LazyCacheGeneratedEnvironment.lower_of_lowerSupported
            rootSpec.lowered
        have emittedCacheNames :
            sourceModule.initializers =
              Fir.Wasm.cachedDeclarationNames program :=
          LazyCacheGeneratedEnvironment.initializers_of_lower ordinaryLowering
        have contexts : DeclarationContextsCoherent rootContext context := {
          program :=
            rootSpec.contextProgram.trans functionSpec.contextProgram.symm
          cachedDeclarations :=
            (rootGenerated.cacheNames.trans emittedCacheNames).trans
              contextCaches.symm }
        have generated :
            LazyCacheGeneratedEnvironment context sourceModule :=
          rootGenerated.ofCoherent contexts
        obtain ⟨sourceMiddle, targetMiddle, nextLocals, physical, hit,
            producedTransfer, nextCache, sourcePrefix, targetPrefix, nextFocus,
            nextSourceJoins, firstSourceFramesEq, firstTargetFramesEq⟩ :=
          related.advance_lazyHit_of_compiler functionSpec sourceJoins
            targetCodeEq continuationAdapted call generated sourceStep
            invariant.1 valueCompiled valueAdapted resultFound
        rw [transfer] at producedTransfer
        have nextFactsEq :
            nextFacts = eraseReuseCapacityFact facts decl.fvarId :=
          Option.some.inj producedTransfer
        have stepFits :
            0 ≤ continuationCost + slack := by omega
        obtain ⟨_simulates, _externalsPreserved,
            _hostDescriptorsPreserved, _witnessDescriptorsPreserved,
            _nextTransfer, nextCacheInvariant⟩ :=
          invariant.1.ofLazyCacheResult stepFits hit (fun _ => nextCache)
            resultFound (by
              simpa [nextFactsEq] using transfer)
        have ordinary :
            OrdinaryPersistenceTransport sourceRuntime nextRuntime :=
          SourceLazyLetResult.hit_ordinaryTransport_of_supported call sourceStep
        have nextEntry :
            ReuseCapacityCodeEntryTransports entryRuntime nextRuntime entryStore
              targetStore entryWitness witness :=
          invariant.2.step hit.witnessTransport
            hit.closureAllocationsPersistent hit.capacityTransport ordinary
            hit.externalsPreserved hit.toClosureTablesTransport
        have continuationInvariant :
            ReuseCapacityEntryRelativeFrame
              (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
                externals)
              entryRuntime entryStore entryWitness nextFacts
              (continuationCost + slack) nextRuntime
              (bind sourceEnv decl.fvarId sourceValue) targetStore nextLocals
              witness := by
          simpa [nextFactsEq] using
            (show
              ReuseCapacityEntryRelativeFrame
                (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
                  externals)
                entryRuntime entryStore entryWitness
                (eraseReuseCapacityFact facts decl.fvarId)
                ((continuationCost + slack) - 0) nextRuntime
                (bind sourceEnv decl.fvarId sourceValue) targetStore nextLocals
                witness from ⟨nextCacheInvariant, nextEntry⟩)
        obtain ⟨sourceAfter, targetAfter, resultStore, resultLocals,
            resultWitness, kind, resultPhysical, sourceCount, targetCount,
            sourceTail, targetTail, yielded, resultInvariant, resultRefines,
            resultJoins, tailSourceFramesEq, tailTargetFramesEq⟩ :=
          ih functionSpec contextCaches nextFocus nextSourceJoins
            (continuationInvariant.withValues targetLocals.values)
        exact ⟨sourceAfter, targetAfter, resultStore, resultLocals,
          resultWitness, kind, resultPhysical, 3 + sourceCount,
          5 + targetCount, sourcePrefix.trans sourceTail,
          targetPrefix.trans targetTail, yielded, resultInvariant,
          resultRefines, resultJoins,
          tailSourceFramesEq.trans firstSourceFramesEq,
          tailTargetFramesEq.trans firstTargetFramesEq⟩
  | @lazyMiss context decl declaration sourceDeclaration resultKind calleeCode
      sourceRuntime sourceEnv continuation nextRuntime sourceValue
      calleeResultFacts callRuntime calleeResultEnv stepCost facts nextFacts
      expectedResult resultFacts resultRuntime resultEnv resultValue
      continuationCost calleeFunction call loweredRow resultClassified
      notObject notTObject sourceStep callee transfer continued calleeIH
      continuedIH =>
      rcases call with
        ⟨⟨valueEq, kindEq, targetEq, targetResultEq, resultRefines, paramsEq,
          resultCompiled⟩, bodyEq⟩
      have programEq : context.program = program := functionSpec.contextProgram
      subst program
      obtain ⟨valueCode, restCode, targetValue, targetRest, resultIndex,
          valueCompiled, restCompiled, valueAdapted, restAdapted, resultFound,
          targetCodeEq⟩ :=
        CodeAdapted.let_eq related.adapted
      have continuationAdapted :
          CodeAdapted context sourceModule sourceFunction [] continuation
            targetRest :=
        ⟨restCode, restCompiled, restAdapted⟩
      obtain ⟨targetResultKind, cacheIndex, declarationId, cacheSetId,
          recoveredTargetResultEq, cacheEq, declarationCall, cacheSetCall,
          _valueCodeEq, targetValueEq⟩ :=
        compileCachedLetValue_adapted_inv context sourceModule sourceFunction []
          decl declaration sourceDeclaration _ valueCode targetValue valueEq
          kindEq targetEq paramsEq valueCompiled valueAdapted
      have targetKindEq : targetResultKind = resultKind :=
        Option.some.inj (recoveredTargetResultEq.symm.trans targetResultEq)
      subst targetResultKind
      obtain ⟨generatedRow⟩ :=
        ConcreteGeneratedInternalDeclaration.exists_ofSupportedPipelineAtLowered
          rfl contextCaches rootSpec.programNamesUnique rootSpec.lowered
          rootSpec.adapted targetEq loweredRow resultClassified
      have parametersEmpty : sourceDeclaration.params = #[] :=
        Array.isEmpty_iff.mp paramsEq
      have ordinaryLowering :
          Fir.Wasm.lower context.program = .ok sourceModule :=
        LazyCacheGeneratedEnvironment.lower_of_lowerSupported rootSpec.lowered
      have emittedCacheNames :
          sourceModule.initializers =
            Fir.Wasm.cachedDeclarationNames context.program :=
        LazyCacheGeneratedEnvironment.initializers_of_lower ordinaryLowering
      have contexts : DeclarationContextsCoherent rootContext context := {
        program :=
          rootSpec.contextProgram.trans functionSpec.contextProgram.symm
        cachedDeclarations :=
          (rootGenerated.cacheNames.trans emittedCacheNames).trans
            contextCaches.symm }
      have generated : LazyCacheGeneratedEnvironment context sourceModule :=
        rootGenerated.ofCoherent contexts
      have declarationNameEq : sourceDeclaration.name = declaration :=
        by
          have selected := (Array.find?_eq_some_iff_getElem.mp targetEq).1
          simpa [Fir.LeanIR.Program.findDecl?] using selected
      have exactCallIndex :
          callIndex? sourceModule (.declaration declaration) =
            some generatedRow.targetFunctionIndex := by
        simpa [declarationNameEq] using generatedRow.callIndexEq
      have declarationIdEq :
          declarationId = generatedRow.targetFunctionIndex :=
        Option.some.inj (declarationCall.symm.trans exactCallIndex)
      subst declarationId
      obtain ⟨initializerFound, signature⟩ :=
        generated.select kindEq targetEq targetResultEq paramsEq cacheEq
      obtain ⟨imp, importFound, importInBounds, contractFound,
          parameterCount, resultCount⟩ :=
        functionSpec.cacheSetCall cacheSetCall
      obtain ⟨alignedResultIndex, alignedResultFound, resultKindAt⟩ :=
        functionSpec.localsAligned resultCompiled
      rw [resultFound] at alignedResultFound
      injection alignedResultFound with resultIndexEq
      subst alignedResultIndex
      have cacheFacts :=
        SourceLazyLetResult.miss_cacheFacts_of_callee valueEq targetEq
          parametersEmpty bodyEq sourceStep callee.sourceResult
      have semanticEmpty :
          findGlobal? sourceRuntime.globals declaration = none := cacheFacts.1
      have publicationRuntimeEq :
          nextRuntime = callRuntime.setGlobal declaration sourceValue :=
        cacheFacts.2
      let sourceStaged : MachineState :=
        { program := context.program
          control := .invokeName declaration #[]
          env := sourceEnv
          joins := []
          frames :=
            .bind decl.fvarId continuation sourceEnv [] :: source.frames
          runtime := sourceRuntime }
      let sourceEntry : MachineState :=
        { program := context.program
          control := .code calleeCode
          env := []
          joins := []
          frames := .cache declaration ::
            .bind decl.fvarId continuation sourceEnv [] :: source.frames
          runtime := sourceRuntime }
      let targetEntry : StructuredWasmState Host :=
        { store := targetStore
          control := .running (generatedRow.targetFunction.toLocals [])
            generatedRow.targetFunction.body
          frames :=
            .call 1 targetLocals.values
                { targetLocals with values := targetLocals.values } [
                  .call cacheSetId,
                  .globalSet (2 * cacheIndex + 1),
                  .const 1,
                  .globalSet (2 * cacheIndex)] ::
              .label 0 targetLocals.values
                ([.globalGet (2 * cacheIndex + 1),
                  .localSet resultIndex] ++ targetRest) :: target.frames }
      have stageSourceStep :
          executeStep externals source = .next sourceStaged := by
        rcases source with
          ⟨sourceProgram, sourceControl, sourceStateEnv, sourceStateJoins,
            sourceFrames, sourceStateRuntime⟩
        have programEq := related.sourceProgramEq
        change sourceProgram = context.program at programEq
        subst sourceProgram
        have controlEq := related.sourceControlEq
        change sourceControl = .code (.let decl continuation) at controlEq
        subst sourceControl
        have envEq := related.sourceEnvEq
        change sourceStateEnv = sourceEnv at envEq
        subst sourceStateEnv
        have runtimeEq := related.sourceRuntimeEq
        change sourceStateRuntime = sourceRuntime at runtimeEq
        subst sourceStateRuntime
        change sourceStateJoins = [] at sourceJoins
        subst sourceStateJoins
        simp [sourceStaged, executeStep, coreStep, evalLetValue, valueEq,
          evalArgs, Bind.bind, Except.bind, pure, Except.pure, pushBindFrame]
      have enterSourceStep :
          executeStep externals sourceStaged = .next sourceEntry := by
        have enteredCanonical :
            executeStep externals {
                program := context.program
                control := .invokeName declaration #[]
                env := sourceEnv
                frames := [.bind decl.fvarId continuation sourceEnv []]
                runtime := sourceRuntime } =
              .next {
                program := context.program
                control := .code calleeCode
                env := []
                frames := [
                  .cache declaration,
                  .bind decl.fvarId continuation sourceEnv []]
                runtime := sourceRuntime } := by
          simp [executeStep, coreStep, semanticEmpty, invokeDecl, targetEq,
            parametersEmpty, bodyEq, bindParams]
        have lifted :=
          FirTalos.Correctness.ExecSteps.withFrameSuffix
            (suffix := source.frames)
            (ExecSteps.step enteredCanonical (ExecSteps.refl _))
        cases lifted with
        | step head tail =>
            cases tail
            simpa [sourceStaged, sourceEntry, withFrameSuffix] using head
      have sourcePrefix :
          FinitePath
            (fun before after => executeStep externals before = .next after)
            2 source sourceEntry :=
        .cons stageSourceStep (.cons enterSourceStep (.refl _))
      have flagEmpty :
          targetStore.globals.globals[2 * cacheIndex]? = some (.i32 0) :=
        invariant.1.2.1.emptySlot initializerFound signature semanticEmpty
      have targetParameterCount : generatedRow.targetFunction.numParams = 0 :=
        (generatedRow.targetParameterCount_nullary parametersEmpty).symm
      have targetPrefix :
          FinitePath
            (StructuredWasmStep targetModule.wasmModule hosts.env) 3 target
              targetEntry := by
        rcases target with ⟨targetStateStore, targetControl, targetFrames⟩
        have storeEq := related.targetStoreEq
        change targetStateStore = targetStore at storeEq
        subst targetStateStore
        have controlEq := related.targetControlEq
        rw [targetCodeEq, targetValueEq] at controlEq
        change targetControl = .running targetLocals
          ([.globalGet (2 * cacheIndex),
            .iff 0 0 [] [
              .call generatedRow.targetFunctionIndex,
              .call cacheSetId,
              .globalSet (2 * cacheIndex + 1),
              .const 1,
              .globalSet (2 * cacheIndex)],
            .globalGet (2 * cacheIndex + 1),
            .localSet resultIndex] ++ targetRest) at controlEq
        subst targetControl
        simpa [targetEntry] using
          structuredWasmLazyMissPrefixFinitePath
            (module := targetModule.wasmModule) (hostEnv := hosts.env)
            (store := targetStore) (locals := targetLocals)
            (flagIndex := 2 * cacheIndex)
            (valueIndex := 2 * cacheIndex + 1)
            (resultIndex := resultIndex)
            (declarationId := generatedRow.targetFunctionIndex)
            (cacheSetId := cacheSetId)
            (function := generatedRow.targetFunction)
            (rest := targetRest) (frames := targetFrames)
            targetLocals.values flagEmpty generatedRow.notImport
            generatedRow.targetFunctionFound targetParameterCount
            generatedRow.singleResult
      have calleeFrame :
          ConcreteReuseCapacityCacheFrame sourceModule calleeFunction externals
            [] (stepCost + (continuationCost + slack)) sourceRuntime []
            targetStore (generatedRow.targetFunction.toLocals []) witness :=
        invariant.1.generatedNullaryCalleeEntryAtCost generatedRow
          parametersEmpty (by omega)
      have calleeFocus :
          ConcreteStructuredCodeFocus loweredRow.context sourceModule
            calleeFunction [] sourceRuntime [] calleeCode targetStore
            (generatedRow.targetFunction.toLocals [])
            generatedRow.targetFunction.body witness sourceEntry targetEntry := {
        sourceProgramEq := by
          calc
            sourceEntry.program = context.program := by
              simp [sourceEntry]
            _ = loweredRow.context.program := generatedRow.contextProgram.symm
        sourceControlEq := by simp [sourceEntry]
        sourceEnvEq := by simp [sourceEntry]
        sourceRuntimeEq := by simp [sourceEntry]
        targetStoreEq := by simp [targetEntry]
        targetControlEq := by simp [targetEntry]
        adapted := generatedRow.bodyAdapted
        stateRelated := calleeFrame.1.1.1.1.1
        frameAligned := calleeFrame.1.1.1.2.2.1 }
      have calleeEntryInvariant :
          ReuseCapacityEntryRelativeFrame
            (ConcreteReuseCapacityCacheFrame sourceModule calleeFunction
              externals)
            sourceRuntime targetStore witness []
            (stepCost + (continuationCost + slack)) sourceRuntime []
            targetStore (generatedRow.targetFunction.toLocals []) witness :=
        ⟨calleeFrame,
          ReuseCapacityCodeEntryTransports.refl sourceRuntime targetStore
            witness⟩
      obtain ⟨sourceYield, targetYield, afterCall, calleeLocals, callWitness,
          actualKind, physical, calleeSourceCount, calleeTargetCount,
          calleeSourcePath, calleeTargetPath, calleeYielded, calleeInvariant,
          calleeResultRefines, _calleeResultJoins, calleeSourceFramesEq,
          calleeTargetFramesEq⟩ :=
        calleeIH (generatedRow.toSupportedFunction rootSpec)
          generatedRow.contextCaches calleeFocus rfl calleeEntryInvariant
      have sourceCallFramesEq :
          sourceYield.frames =
            .cache declaration ::
              .bind decl.fvarId continuation sourceEnv [] :: source.frames := by
        rw [calleeSourceFramesEq]
      have targetCallFramesEq :
          targetYield.frames =
            .call 1 targetLocals.values targetLocals [
                .call cacheSetId,
                .globalSet (2 * cacheIndex + 1),
                .const 1,
                .globalSet (2 * cacheIndex)] ::
              .label 0 targetLocals.values
                ([.globalGet (2 * cacheIndex + 1),
                  .localSet resultIndex] ++ targetRest) :: target.frames := by
        rw [calleeTargetFramesEq]
      obtain ⟨cacheSlot, cacheFound, cacheKindEq⟩ :=
        calleeInvariant.1.2.1.hostSlot initializerFound signature
      have valueRelated :
          PhysicalValueRel callWitness resultKind physical sourceValue :=
        calleeYielded.valueRelated.ofRefines calleeResultRefines
      have cacheDescriptorsEq :
          afterCall.host.closureDescriptors = callWitness.closureDescriptors :=
        calleeInvariant.1.1.2
      obtain ⟨runtimeAfter, operation, _runtimeAfterRelated,
          _valueStillRelated, _mappedCapacity⟩ :=
        cacheSetStep_of_refines calleeYielded.stateRelated.1 valueRelated
          cacheFound cacheKindEq cacheDescriptorsEq
      let afterCache := replaceRuntime afterCall runtimeAfter
      have operationEq :
          cacheSetStep declaration resultKind afterCall [physical] =
            .Return [physical] afterCache := by
        simpa [afterCache] using operation
      obtain ⟨oldFlag, oldValue, flagAfterCall, valueAfterCall⟩ :=
        calleeInvariant.1.2.1.slotLanesPresent initializerFound signature
      have valueAfterCache :
          afterCache.globals.globals[2 * cacheIndex + 1]? = some oldValue := by
        rw [cacheSetStep_preserves_wasmGlobals operationEq]
        exact valueAfterCall
      have flagAfterCache :
          afterCache.globals.globals[2 * cacheIndex]? = some oldFlag := by
        rw [cacheSetStep_preserves_wasmGlobals operationEq]
        exact flagAfterCall
      let valueStore :=
        writeWasmGlobal afterCache (2 * cacheIndex + 1) physical
      have valueStoreEq :
          valueStore =
            writeWasmGlobal afterCache (2 * cacheIndex + 1) physical := rfl
      have flagAfterValue :
          valueStore.globals.globals[2 * cacheIndex]? = some oldFlag := by
        rw [valueStoreEq, writeWasmGlobal_get_ne (by omega)]
        exact flagAfterCache
      let nextStore :=
        writeWasmGlobal valueStore (2 * cacheIndex) (.i32 1)
      obtain ⟨nextLocals, targetSet, nextAligned⟩ :=
        invariant.1.1.1.1.2.2.1.set?
          (nextRuntime := nextRuntime)
          (nextEnv := bind sourceEnv decl.fvarId sourceValue)
          (nextStore := nextStore) (nextWitness := callWitness)
          (physical := physical) resultFound
      let sourcePublished : MachineState := {
        program := context.program
        control := .yielded sourceValue
        env := calleeResultEnv
        joins := []
        frames := .bind decl.fvarId continuation sourceEnv [] :: source.frames
        runtime := nextRuntime }
      let sourceResumed : MachineState := {
        program := context.program
        control := .code continuation
        env := bind sourceEnv decl.fvarId sourceValue
        joins := []
        frames := source.frames
        runtime := nextRuntime }
      let targetResumed : StructuredWasmState Host := {
        store := nextStore
        control := .running
          { nextLocals with values := targetLocals.values } targetRest
        frames := target.frames }
      have publishSourceStep :
          executeStep externals sourceYield = .next sourcePublished := by
        rcases sourceYield with
          ⟨yieldProgram, yieldControl, yieldEnv, yieldJoins, yieldFrames,
            yieldRuntime⟩
        have programEq := calleeYielded.sourceProgramEq
        change yieldProgram = loweredRow.context.program at programEq
        rw [generatedRow.contextProgram] at programEq
        subst yieldProgram
        have controlEq := calleeYielded.sourceControlEq
        change yieldControl = .yielded sourceValue at controlEq
        subst yieldControl
        have envEq := calleeYielded.sourceEnvEq
        change yieldEnv = calleeResultEnv at envEq
        subst yieldEnv
        have runtimeEq := calleeYielded.sourceRuntimeEq
        change yieldRuntime = callRuntime at runtimeEq
        subst yieldRuntime
        change yieldJoins = [] at _calleeResultJoins
        subst yieldJoins
        change yieldFrames = _ at sourceCallFramesEq
        subst yieldFrames
        simp [sourcePublished, executeStep, coreStep, publicationRuntimeEq]
      have bindSourceStep :
          executeStep externals sourcePublished = .next sourceResumed := by
        simp [sourcePublished, sourceResumed, executeStep, coreStep]
      have sourceSuffix :
          FinitePath
            (fun before after => executeStep externals before = .next after)
            2 sourceYield sourceResumed :=
        .cons publishSourceStep (.cons bindSourceStep (.refl _))
      have targetSuffix :
          FinitePath
            (StructuredWasmStep targetModule.wasmModule hosts.env) 8
            targetYield targetResumed := by
        rcases targetYield with
          ⟨yieldStore, yieldControl, yieldFrames⟩
        have storeEq := calleeYielded.targetStoreEq
        change yieldStore = afterCall at storeEq
        subst yieldStore
        have controlEq := calleeYielded.targetControlEq
        change yieldControl = .returning (physical :: calleeLocals.values)
          at controlEq
        subst yieldControl
        change yieldFrames = _ at targetCallFramesEq
        subst yieldFrames
        simpa [targetResumed, nextStore] using
          structuredWasmLazyMissSuffixFinitePath
            (module := targetModule.wasmModule) (hostEnv := hosts.env)
            (spec := hosts.spec) (cacheSetId := cacheSetId) (imp := imp)
            (declaration := declaration) (kind := resultKind)
            (afterCall := afterCall) (afterCache := afterCache)
            (valueStore := valueStore) (callerLocals := targetLocals)
            (calleeLocals := calleeLocals) (nextLocals := nextLocals)
            (physical := physical) (oldValue := oldValue)
            (oldFlag := oldFlag) (flagIndex := 2 * cacheIndex)
            (valueIndex := 2 * cacheIndex + 1)
            (resultIndex := resultIndex) (rest := targetRest)
            (frames := target.frames) targetLocals.values importFound
            functionSpec.hostsSatisfy importInBounds contractFound
            parameterCount resultCount operationEq valueAfterCache
            valueStoreEq flagAfterValue (by omega) targetSet
      have nextRelated :
          StateRelated sourceFunction nextRuntime
            (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals
            callWitness := by
        rw [publicationRuntimeEq]
        exact invariant.1.1.1.1.1.1.bindAfterCacheSet
          calleeYielded.stateRelated.1 calleeInvariant.2.witness valueRelated
          cacheFound cacheKindEq cacheDescriptorsEq operationEq valueStoreEq
          resultFound resultKindAt targetSet
      have nonHeap : IsNonHeapReference sourceValue :=
        valueRelated.isNonHeapReference_of_kind notObject notTObject
      have publicationOrdinary :
          ReuseTokenOrdinaryBindTransport facts decl.fvarId callRuntime
            nextRuntime sourceEnv sourceValue := by
        rw [publicationRuntimeEq]
        exact ReuseTokenOrdinaryBindTransport.ofPublicationDisjoint declaration
          (ReuseTokenPublicationDisjoint.of_nonHeapReference nonHeap)
      have nextOrdinary :
          ReuseTokenOrdinaryRel (eraseReuseCapacityFact facts decl.fvarId)
            nextRuntime (bind sourceEnv decl.fvarId sourceValue) :=
        publicationOrdinary
          (invariant.1.1.1.1.2.1.transport calleeInvariant.2.ordinary)
      have publicationCapacity :
          HeaderCapacityTransport afterCall.host.runtime.heap
            nextStore.host.runtime.heap callWitness := by
        simpa [nextStore, writeWasmGlobal, valueStoreEq] using
          cacheSetStep_preserves_mappedHeaderCapacity_of_related
            calleeYielded.stateRelated.1 valueRelated cacheFound cacheKindEq
            cacheDescriptorsEq operationEq
      have currentCapacity :
          HeaderCapacityTransport targetStore.host.runtime.heap
            nextStore.host.runtime.heap witness :=
        calleeInvariant.2.capacity.transAcross calleeInvariant.2.witness
          publicationCapacity
      have nextReuseRelated :
          ReuseCapacityStateRelated
            (eraseReuseCapacityFact facts decl.fvarId) sourceFunction
            nextRuntime (bind sourceEnv decl.fvarId sourceValue) nextStore
            nextLocals callWitness :=
        invariant.1.1.1.1.1.eraseResult nextRelated resultFound
          (localUpdate_of_set? targetSet) calleeInvariant.2.witness
          currentCapacity
      have nextBudget :
          nextStore.host.runtime.heap.AddressSpaceBudget
            (continuationCost + slack) := by
        simpa [nextStore] using
          cachePublication_preserves_addressSpaceBudget operationEq valueStoreEq
            calleeInvariant.1.1.1.1.2.2.2
      have publicationExternals :
          nextStore.host.externals = afterCall.host.externals := by
        simp [nextStore, valueStore, afterCache, writeWasmGlobal,
          replaceRuntime, clearFailure]
      have publicationDescriptors :
          nextStore.host.closureDescriptors =
            afterCall.host.closureDescriptors := by
        simp [nextStore, valueStore, afterCache, writeWasmGlobal,
          replaceRuntime, clearFailure]
      have publicationDispatch :
          nextStore.host.closureDispatch = afterCall.host.closureDispatch := by
        simp [nextStore, valueStore, afterCache, writeWasmGlobal,
          replaceRuntime, clearFailure]
      have nextInteger :
          nextStore.host.externals.IntegerResultRefines externals := by
        rw [publicationExternals, calleeInvariant.2.externals]
        exact invariant.1.1.1.2.1
      have nextNatural :
          FirTalos.Concrete.ConcreteExternalImpl.NaturalResultRefines
            nextStore.host.externals externals := by
        rw [publicationExternals, calleeInvariant.2.externals]
        exact invariant.1.1.1.2.2.1
      have nextScalar :
          FirTalos.Concrete.ConcreteExternalImpl.ScalarResultRefines
            nextStore.host.externals externals := by
        rw [publicationExternals, calleeInvariant.2.externals]
        exact invariant.1.1.1.2.2.2
      have nextDescriptors :
          nextStore.host.closureDescriptors = callWitness.closureDescriptors :=
        publicationDescriptors.trans cacheDescriptorsEq
      have nextCache :
          LazyCacheGlobalsRel callWitness sourceModule nextRuntime nextStore := by
        have afterHost :=
          calleeInvariant.1.2.1.afterCacheSet operationEq
        simpa [nextStore] using
          afterHost.publish initializerFound signature publicationRuntimeEq
            valueRelated valueStoreEq
      have nextClosureTables : ClosureTablesAgree nextStore callWitness := by
        exact {
          dispatch :=
            calleeInvariant.1.2.2.dispatch.trans publicationDispatch.symm
          descriptors :=
            publicationDescriptors.trans
              calleeInvariant.1.2.2.descriptors }
      have nextBase :
          ConcreteReuseCapacityFrame sourceFunction
            (eraseReuseCapacityFact facts decl.fvarId)
            (continuationCost + slack) nextRuntime
            (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals
            callWitness :=
        ⟨nextReuseRelated, nextOrdinary, nextAligned, nextBudget⟩
      have nextPure :
          ConcreteReuseCapacityPureExternalFrame sourceFunction externals
            (eraseReuseCapacityFact facts decl.fvarId)
            (continuationCost + slack) nextRuntime
            (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals
            callWitness :=
        ⟨nextBase, nextInteger, nextNatural, nextScalar⟩
      have nextOwnership :
          ConcreteReuseCapacityPureExternalOwnershipFrame sourceFunction
            externals (eraseReuseCapacityFact facts decl.fvarId)
            (continuationCost + slack) nextRuntime
            (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals
            callWitness :=
        ⟨nextPure, nextDescriptors⟩
      have nextFrame :
          ConcreteReuseCapacityCacheFrame sourceModule sourceFunction externals
            (eraseReuseCapacityFact facts decl.fvarId)
            (continuationCost + slack) nextRuntime
            (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals
            callWitness :=
        ⟨nextOwnership, nextCache, nextClosureTables⟩
      have publicationOrdinaryPersistence :
          OrdinaryPersistenceTransport callRuntime nextRuntime := by
        apply (OrdinaryPersistenceTransport.refl callRuntime).congrAfter
        rw [publicationRuntimeEq]
        exact
          (RuntimeState.setGlobal_heap_eq_of_nonHeapReference callRuntime
            declaration sourceValue nonHeap).symm
      have publicationClosureTables :
          ClosureTablesTransport afterCall nextStore callWitness
            callWitness := {
        hostDispatchPreserved := publicationDispatch
        witnessDispatchPreserved := rfl
        hostDescriptorsPreserved := publicationDescriptors
        witnessDescriptorsPreserved := rfl }
      have currentToNext :
          ReuseCapacityCodeEntryTransports sourceRuntime nextRuntime
            targetStore nextStore witness callWitness :=
        calleeInvariant.2.step (WitnessTransport.refl callWitness)
          (ClosureAllocationsPersistent.refl callWitness)
          publicationCapacity publicationOrdinaryPersistence
          publicationExternals publicationClosureTables
      have nextEntry :
          ReuseCapacityCodeEntryTransports entryRuntime nextRuntime entryStore
            nextStore entryWitness callWitness :=
        invariant.2.step currentToNext.witness
          currentToNext.closureAllocationsPersistent currentToNext.capacity
          currentToNext.ordinary currentToNext.externals
          currentToNext.toClosureTablesTransport
      have expectedTransfer :
          reuseCapacityLetFacts? facts decl =
            some (eraseReuseCapacityFact facts decl.fvarId) := by
        simp [reuseCapacityLetFacts?, valueEq]
      have nextFactsEq :
          nextFacts = eraseReuseCapacityFact facts decl.fvarId :=
        Option.some.inj (transfer.symm.trans expectedTransfer)
      have continuationInvariant :
          ReuseCapacityEntryRelativeFrame
            (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
              externals)
            entryRuntime entryStore entryWitness nextFacts
            (continuationCost + slack) nextRuntime
            (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals
            callWitness := by
        simpa [nextFactsEq] using
          (show
            ReuseCapacityEntryRelativeFrame
              (ConcreteReuseCapacityCacheFrame sourceModule sourceFunction
                externals)
              entryRuntime entryStore entryWitness
              (eraseReuseCapacityFact facts decl.fvarId)
              (continuationCost + slack) nextRuntime
              (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals
              callWitness from ⟨nextFrame, nextEntry⟩)
      have nextFocus :
          ConcreteStructuredCodeFocus context sourceModule sourceFunction []
            nextRuntime (bind sourceEnv decl.fvarId sourceValue) continuation
            nextStore { nextLocals with values := targetLocals.values }
            targetRest callWitness sourceResumed targetResumed := {
        sourceProgramEq := by simp [sourceResumed]
        sourceControlEq := by simp [sourceResumed]
        sourceEnvEq := by simp [sourceResumed]
        sourceRuntimeEq := by simp [sourceResumed]
        targetStoreEq := by simp [targetResumed]
        targetControlEq := by simp [targetResumed]
        adapted := continuationAdapted
        stateRelated := by simpa using nextRelated.withValues targetLocals.values
        frameAligned := by simpa using nextAligned.withValues targetLocals.values }
      obtain ⟨sourceAfter, targetAfter, resultStore, resultLocals,
          resultWitness, kind, resultPhysical, continuationSourceCount,
          continuationTargetCount, continuationSourcePath,
          continuationTargetPath, yielded, resultInvariant, resultRefines,
          resultJoins, continuationSourceFramesEq,
          continuationTargetFramesEq⟩ :=
        continuedIH functionSpec contextCaches nextFocus rfl
          (continuationInvariant.withValues targetLocals.values)
      exact ⟨sourceAfter, targetAfter, resultStore, resultLocals,
        resultWitness, kind, resultPhysical,
        2 + calleeSourceCount + 2 + continuationSourceCount,
        3 + calleeTargetCount + 8 + continuationTargetCount,
        ((sourcePrefix.trans calleeSourcePath).trans sourceSuffix).trans
          continuationSourcePath,
        ((targetPrefix.trans calleeTargetPath).trans targetSuffix).trans
          continuationTargetPath,
        yielded, resultInvariant, resultRefines, resultJoins,
        continuationSourceFramesEq, continuationTargetFramesEq⟩

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
