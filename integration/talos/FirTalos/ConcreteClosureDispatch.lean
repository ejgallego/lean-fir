import FirTalos.ConcreteRuntime

namespace FirTalos.Concrete

open Fir.Wasm
open Fir.LeanIR.Impure
open Fir.Wasm.Concrete
open FirTalos.Correctness

/--
A physical lane related to a semantic heap object exposes the exact concrete
address and refinement-witness location mapping.

The statement is representation-polymorphic in the source ABI kind: both the
precise `.object` lane and the widened `.tobject` lane reduce to the same
wasm32 address. All scalar, erased, tagged, and wide-lane cases are ruled out
by the indexed `ValueRel`.
-/
theorem PhysicalValueRel.heapAddress
    {witness : RefinementWitness} {kind : AbiKind}
    {physical : Wasm.Value} {location : Location}
    (related :
      PhysicalValueRel witness kind physical (.object (.heap location))) :
    ∃ address,
      physical = .i32 (UInt32.ofNat address.value) ∧
        witness.locations.lookup? location = some address := by
  cases related with
  | word32 valueRelated =>
      cases valueRelated with
      | object heapRelated =>
          cases heapRelated with
          | mapped mapped =>
              exact ⟨_, rfl, mapped⟩
      | tobject objectRelated =>
          cases objectRelated with
          | heap heapRelated =>
              cases heapRelated with
              | mapped mapped =>
                  exact ⟨_, rfl, mapped⟩
  | word64 valueRelated =>
      cases valueRelated
  | float32Bits valueRelated =>
      cases valueRelated
  | float64Bits valueRelated =>
      cases valueRelated

/--
Resolve a source closure local and execute an arbitrary generated metadata
matcher from source/runtime refinement facts.

Both immutable closure-table equations are explicit. This is the precise
boundary needed by saturated-dispatch selection: it derives the physical
address and exact matcher result instead of accepting either as a call-site
certificate.
-/
theorem StateRelated.resolveClosureMatcher
    {sourceFunction : Fir.Wasm.Function}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {witness : RefinementWitness}
    {closureId : Lean.FVarId}
    {closureIndex : Nat}
    {closureKind : AbiKind}
    {location : Location}
    {cell : HeapCell}
    {function expectedFunction : Lean.Name}
    {arity expectedArity expectedFixed : Nat}
    {captures : Array Value}
    (related :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals
        witness)
    (dispatchEq :
      witness.closureDispatch = initial.host.closureDispatch)
    (descriptorsEq :
      witness.closureDescriptors = initial.host.closureDescriptors)
    (sourceLookup :
      lookup sourceEnv closureId = some (.object (.heap location)))
    (closureFound :
      findFVar? (functionBindings sourceFunction) closureId =
        some closureIndex)
    (closureKindAt :
      (functionBindings sourceFunction)[closureIndex]?.map Prod.snd =
        some closureKind)
    (cellFound : findCell? sourceRuntime.heap location = some cell)
    (cellLive : cell.live = true)
    (cellObjectEq : cell.object = .closure function arity captures) :
    ∃ address : Word32,
      locals.get closureIndex =
          some (.i32 (UInt32.ofNat address.value)) ∧
        (∀ results next,
          closureMatchesStep expectedFunction expectedArity expectedFixed initial
              [.i32 (UInt32.ofNat address.value)] = .Return results next →
            results = [
              .i32 (if function == expectedFunction && arity == expectedArity &&
                captures.size == expectedFixed then 1 else 0)]) ∧
        closureData sourceRuntime (.object (.heap location)) =
          .ok (function, arity, captures) := by
  obtain ⟨physical, localFound, physicalRelated⟩ :=
    related.resolve sourceLookup closureFound closureKindAt
  obtain ⟨address, physicalEq, mapped⟩ :=
    physicalRelated.heapAddress
  subst physical
  refine ⟨address, localFound, ?_, ?_⟩
  · intro results next operation
    exact (closureMatchesStep_result_of_refines related.1 dispatchEq
      descriptorsEq mapped cellFound cellLive cellObjectEq operation).1
  · unfold closureData
    simp only [getLiveCell, cellFound, cellLive, if_true, Bind.bind, Except.bind]
    rw [cellObjectEq]
    rfl

/-- One compiler-produced closure candidate after numeric Talos adaptation,
paired with the exact concrete matcher invocation used to select it. The body
remains abstract here: later theorems discharge it with either partial
application or direct-call correctness. -/
structure ClosureCandidateCase
    (sourceModule : Fir.Wasm.Module)
    (sourceFunction : Fir.Wasm.Function)
    (labels : List Lean.FVarId)
    (module : Wasm.Module)
    (spec : Wasm.HostSpec Host)
    (initial : Wasm.Store Host)
    (closureId : Lean.FVarId)
    (closureIndex : Nat)
    (address : Word32) where
  source : List Fir.Wasm.Instruction × List Fir.Wasm.Instruction
  targetBody : Wasm.Program
  function : Lean.Name
  arity : Nat
  fixed : Nat
  matcherIndex : Nat
  matched : UInt32
  nextStore : Wasm.Store Host
  imp : Wasm.ImportDecl
  sourceMatcher :
    source.1 = [
      .localGet closureId,
      .call (.runtime (.closureMatches function arity fixed))]
  bodyAdapted :
    instructions sourceModule sourceFunction labels source.2 = .ok targetBody
  matcherFound :
    callIndex? sourceModule
      (.runtime (.closureMatches function arity fixed)) = some matcherIndex
  importFound : module.imports[matcherIndex]? = some imp
  importInBounds : matcherIndex < module.imports.length
  contractFound :
    spec.contracts[matcherIndex]? =
      some (closureMatchesContract function arity fixed)
  parameterCount : imp.params.length = 1
  resultCount : imp.results.length = 1
  operation :
    closureMatchesStep function arity fixed initial
        [.i32 (UInt32.ofNat address.value)] =
      .Return [.i32 matched] nextStore

/--
The candidate's recorded matcher bit is determined by the related semantic
closure, rather than being an independent dynamic premise.
-/
theorem ClosureCandidateCase.matched_eq_of_refines
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {spec : Wasm.HostSpec Host}
    {initial : Wasm.Store Host}
    {closureId : Lean.FVarId}
    {closureIndex : Nat}
    {address : Word32}
    {witness : RefinementWitness}
    {runtime : RuntimeState}
    {location : Location}
    {cell : HeapCell}
    {function : Lean.Name}
    {arity : Nat}
    {captures : Array Value}
    (candidate :
      ClosureCandidateCase sourceModule sourceFunction labels module spec
        initial closureId closureIndex address)
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (dispatchEq : witness.closureDispatch = initial.host.closureDispatch)
    (descriptorsEq :
      witness.closureDescriptors = initial.host.closureDescriptors)
    (mapped : witness.locations.lookup? location = some address)
    (cellFound : findCell? runtime.heap location = some cell)
    (cellLive : cell.live = true)
    (cellObjectEq : cell.object = .closure function arity captures) :
    candidate.matched =
      if function == candidate.function && arity == candidate.arity &&
          captures.size == candidate.fixed then
        1
      else
        0 := by
  have matcher :=
    (closureMatchesStep_result_of_refines runtimeRelated dispatchEq descriptorsEq
      mapped cellFound cellLive cellObjectEq candidate.operation
      (expectedFunction := candidate.function)
      (expectedArity := candidate.arity)
      (expectedFixed := candidate.fixed)).1
  have valuesEq :
      [Wasm.Value.i32 candidate.matched] =
        [Wasm.Value.i32 (if function == candidate.function &&
          arity == candidate.arity && captures.size == candidate.fixed then
            1
          else
            0)] := by
    exact matcher
  have valueEq :
      Wasm.Value.i32 candidate.matched =
        Wasm.Value.i32 (if function == candidate.function &&
          arity == candidate.arity && captures.size == candidate.fixed then
            1
          else
            0) := by
    simpa using congrArg List.head? valuesEq
  exact Wasm.Value.i32.inj valueEq

/--
Any finite candidate list containing a nonzero matcher has a canonical
first-matching split. The prefix theorem is independent of compiler
enumeration; later dispatch induction only has to prove that the generated
candidate family contains a matching semantic closure identity.
-/
theorem exists_first_nonzero
    {α : Type} (matched : α → UInt32) (values : List α)
    (existsMatch :
      ∃ candidate ∈ values, (matched candidate != 0) = true) :
    ∃ before selected suffix,
      values = before ++ selected :: suffix ∧
        (∀ candidate, candidate ∈ before → matched candidate = 0) ∧
          (matched selected != 0) = true := by
  induction values with
  | nil =>
      simp at existsMatch
  | cons candidate values ih =>
      by_cases candidateZero : matched candidate = 0
      · have tailMatch :
            ∃ selected ∈ values, (matched selected != 0) = true := by
          obtain ⟨selected, selectedMem, selectedNonzero⟩ := existsMatch
          simp only [List.mem_cons] at selectedMem
          rcases selectedMem with selectedEq | selectedMem
          · rw [selectedEq, candidateZero] at selectedNonzero
            simp at selectedNonzero
          · exact ⟨selected, selectedMem, selectedNonzero⟩
        obtain ⟨before, selected, suffix, valuesEq, beforeZero,
            selectedNonzero⟩ :=
          ih tailMatch
        refine
          ⟨candidate :: before, selected, suffix, ?_, ?_, selectedNonzero⟩
        · simp [valuesEq]
        · intro other otherMem
          simp only [List.mem_cons] at otherMem
          rcases otherMem with otherEq | otherMem
          · simpa [otherEq] using candidateZero
          · exact beforeZero other otherMem
      · refine ⟨[], candidate, values, rfl, ?_, ?_⟩
        · simp
        · simp [candidateZero]

/--
One generated candidate with the semantic closure identity determines the
first executable matcher selected by the complete candidate fold.

The caller proves only static enumeration coverage of the closure's function,
total arity, and fixed-capture count. Concrete matcher results for that
candidate and every earlier candidate are consequences of runtime refinement.
-/
theorem closureCandidates_exists_first_match_of_refines
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {spec : Wasm.HostSpec Host}
    {initial : Wasm.Store Host}
    {closureId : Lean.FVarId}
    {closureIndex : Nat}
    {address : Word32}
    {witness : RefinementWitness}
    {runtime : RuntimeState}
    {location : Location}
    {cell : HeapCell}
    {function : Lean.Name}
    {arity : Nat}
    {captures : Array Value}
    (candidates : List
      (ClosureCandidateCase sourceModule sourceFunction labels module spec
        initial closureId closureIndex address))
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (dispatchEq : witness.closureDispatch = initial.host.closureDispatch)
    (descriptorsEq :
      witness.closureDescriptors = initial.host.closureDescriptors)
    (mapped : witness.locations.lookup? location = some address)
    (cellFound : findCell? runtime.heap location = some cell)
    (cellLive : cell.live = true)
    (cellObjectEq : cell.object = .closure function arity captures)
    (containsMatch :
      ∃ candidate ∈ candidates,
        (function == candidate.function && arity == candidate.arity &&
          captures.size == candidate.fixed) = true) :
    ∃ before selected suffix,
      candidates = before ++ selected :: suffix ∧
        (∀ candidate, candidate ∈ before →
          candidate.matched = (0 : UInt32)) ∧
          (selected.matched != 0) = true := by
  have executableMatch :
      ∃ candidate ∈ candidates, (candidate.matched != 0) = true := by
    obtain ⟨candidate, candidateMem, candidateIdentity⟩ := containsMatch
    refine ⟨candidate, candidateMem, ?_⟩
    rw [candidate.matched_eq_of_refines runtimeRelated dispatchEq
      descriptorsEq mapped cellFound cellLive cellObjectEq]
    simp [candidateIdentity]
  exact exists_first_nonzero (fun candidate => candidate.matched) candidates
    executableMatch

theorem ClosureCandidateCase.matcherAdapted
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {spec : Wasm.HostSpec Host}
    {initial : Wasm.Store Host}
    {closureId : Lean.FVarId}
    {closureIndex : Nat}
    {address : Word32}
    (candidate : ClosureCandidateCase sourceModule sourceFunction labels module
      spec initial closureId closureIndex address)
    (closureFound :
      findFVar? (functionBindings sourceFunction) closureId =
        some closureIndex) :
    instructions sourceModule sourceFunction labels candidate.source.1 =
      .ok [
        .localGet closureIndex,
        .call candidate.matcherIndex] := by
  have found :
      findFVar?
          (sourceFunction.params.toList ++ sourceFunction.locals.toList)
          closureId =
        some closureIndex := by
    simpa [functionBindings] using closureFound
  rw [candidate.sourceMatcher]
  simp [instructions, instruction, found, candidate.matcherFound]
  change Except.ok [
      Wasm.Instruction.localGet closureIndex,
      Wasm.Instruction.call candidate.matcherIndex] =
    Except.ok [
      Wasm.Instruction.localGet closureIndex,
      Wasm.Instruction.call candidate.matcherIndex]
  rfl

/-- The exact numeric Talos branch chain corresponding to a list of resolved
compiler candidates. -/
def resolvedClosureCandidateChain
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {spec : Wasm.HostSpec Host}
    {initial : Wasm.Store Host}
    {closureId : Lean.FVarId}
    {closureIndex : Nat}
    {address : Word32}
    (candidates : List
      (ClosureCandidateCase sourceModule sourceFunction labels module spec
        initial closureId closureIndex address)) :
    Wasm.Program :=
  candidates.foldr (init := [.unreachable]) fun candidate rest =>
    [.localGet closureIndex, .call candidate.matcherIndex,
      .iff 0 0 candidate.targetBody rest]

/-- Talos adaptation distributes through the compiler's complete nested
candidate fold, including the final unreachable fallback. -/
theorem instructions_compileClosureCandidateChain
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {spec : Wasm.HostSpec Host}
    {initial : Wasm.Store Host}
    {closureId : Lean.FVarId}
    {closureIndex : Nat}
    {address : Word32}
    (candidates : List
      (ClosureCandidateCase sourceModule sourceFunction labels module spec
        initial closureId closureIndex address))
    (closureFound :
      findFVar? (functionBindings sourceFunction) closureId =
        some closureIndex) :
    instructions sourceModule sourceFunction labels
        (compileClosureCandidateChain (candidates.map (·.source))) =
      .ok (resolvedClosureCandidateChain candidates) := by
  induction candidates with
  | nil =>
      simp [compileClosureCandidateChain, resolvedClosureCandidateChain,
        instructions, instruction]
      rfl
  | cons candidate candidates ih =>
      rw [show
        compileClosureCandidateChain
            ((candidate :: candidates).map (·.source)) =
          candidate.source.1 ++ [
            .ifElse candidate.source.2
              (compileClosureCandidateChain (candidates.map (·.source)))] by
        rfl]
      rw [FirTalos.Correctness.instructions_append,
        candidate.matcherAdapted closureFound]
      simp [instructions, instruction, candidate.bodyAdapted, ih,
        resolvedClosureCandidateChain]
      rfl

/-- The compiler fold, final result-local reload, and Talos adapter agree
exactly for the candidates generated by `compileClosureDispatch`. -/
theorem instructions_compileClosureDispatch
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {spec : Wasm.HostSpec Host}
    {initial : Wasm.Store Host}
    {declId closureId : Lean.FVarId}
    {resultKind : AbiKind}
    {argumentCode : List Fir.Wasm.Instruction}
    {argumentKinds : Array AbiKind}
    {closureIndex resultIndex : Nat}
    {address : Word32}
    (candidates : List
      (ClosureCandidateCase sourceModule sourceFunction labels module spec
        initial closureId closureIndex address))
    (candidatesEq :
      context.program.decls.toList.flatMap (fun target =>
        compileClosureCandidatesForTarget declId closureId resultKind
          argumentCode argumentKinds target) =
        candidates.map (·.source))
    (closureFound :
      findFVar? (functionBindings sourceFunction) closureId =
        some closureIndex)
    (resultFound :
      findFVar? (functionBindings sourceFunction) declId =
        some resultIndex) :
    instructions sourceModule sourceFunction labels
        (compileClosureDispatch context declId closureId resultKind
          argumentCode argumentKinds) =
      .ok (resolvedClosureCandidateChain candidates ++
        [.localGet resultIndex]) := by
  unfold compileClosureDispatch
  rw [candidatesEq, FirTalos.Correctness.instructions_append,
    instructions_compileClosureCandidateChain candidates closureFound]
  have found :
      findFVar?
          (sourceFunction.params.toList ++ sourceFunction.locals.toList)
          declId =
        some resultIndex := by
    simpa [functionBindings] using resultFound
  simp [instructions, instruction, found]

/-- A generated capture/argument prefix leaves the physical arguments on the
operand stack in Wasm call order and otherwise preserves the concrete state.
The judgment is suffix-polymorphic so projection and ordinary-local prefixes
compose without reopening their consumers. -/
def ClosureArgumentAssembly
    (module : Wasm.Module) (hostEnv : Wasm.HostEnv Host)
    (code : Wasm.Program) (physicalArgs : List Wasm.Value)
    (initial : Wasm.Store Host) (locals : Wasm.Locals) : Prop :=
  ∀ (rest : Wasm.Program) (Q : Wasm.Assertion Host)
      (tail : List Wasm.Value),
    Wasm.wp module rest Q initial
        { locals with values := physicalArgs.reverse ++ tail } hostEnv →
      Wasm.wp module (code ++ rest) Q initial
        { locals with values := tail } hostEnv

theorem ClosureArgumentAssembly.nil
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {initial : Wasm.Store Host} {locals : Wasm.Locals} :
    ClosureArgumentAssembly module hostEnv [] [] initial locals := by
  intro rest Q tail continued
  simpa using continued

/--
The ordinary `compileArgs` readiness theorem is exactly the argument-assembly
law needed by generated calls.

Naming this conversion keeps direct declaration-call construction on the
production compiler path: no second argument compiler or target execution
certificate is introduced.
-/
theorem ClosureArgumentAssembly.ofConstructorArgsReady
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {initial : Wasm.Store Host} {locals : Wasm.Locals}
    {code : Wasm.Program} {physicalArgs : List Wasm.Value}
    (ready : ConstructorArgsReady locals code physicalArgs) :
    ClosureArgumentAssembly module hostEnv code physicalArgs initial locals := by
  intro rest Q tail continued
  exact ready.wp continued

/-- Prepending one compiler-resolved local argument extends an already-proved
argument assembly. -/
theorem ClosureArgumentAssembly.localGet
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {initial : Wasm.Store Host} {locals : Wasm.Locals}
    {code : Wasm.Program} {physical : Wasm.Value}
    {physicalArgs : List Wasm.Value} {index : Nat}
    (hLocal : locals.get index = some physical)
    (assembled :
      ClosureArgumentAssembly module hostEnv code physicalArgs initial locals) :
    ClosureArgumentAssembly module hostEnv
      (.localGet index :: code) (physical :: physicalArgs) initial locals := by
  intro rest Q tail continued
  have hLocalTail :
      ({ locals with values := tail } : Wasm.Locals).get index =
        some physical := by
    simpa [Wasm.Locals.get] using hLocal
  change Wasm.wp module (.localGet index :: (code ++ rest)) Q initial
    { locals with values := tail } hostEnv
  apply (Wasm.wp_localGet_cons).2
  rw [hLocalTail]
  apply assembled rest Q (physical :: tail)
  simpa [List.reverse_cons, List.append_assoc] using continued

/-- Prepending one concrete typed-capture projection extends an argument
assembly while retaining the same concrete store. -/
theorem ClosureArgumentAssembly.closureProj
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {initial : Wasm.Store Host} {locals : Wasm.Locals}
    {code : Wasm.Program} {physical : Wasm.Value}
    {physicalArgs : List Wasm.Value}
    {closureIndex : Nat} {address : Word32}
    {function : Lean.Name} {arity fixed index : Nat} {kind : AbiKind}
    (hClosure : locals.get closureIndex =
      some (.i32 (UInt32.ofNat address.value)))
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (closureProjContract function arity fixed index kind))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (operation : closureProjStep function arity fixed index kind initial
        [.i32 (UInt32.ofNat address.value)] =
      .Return [physical] (clearFailure initial))
    (failureClear : clearFailure initial = initial)
    (assembled :
      ClosureArgumentAssembly module hostEnv code physicalArgs initial locals) :
    ClosureArgumentAssembly module hostEnv
      (.localGet closureIndex :: .call id :: code)
      (physical :: physicalArgs) initial locals := by
  intro rest Q tail continued
  apply wp_closureProj hClosure hImp hSat hi hContract hParams hResults
    operation
  rw [failureClear]
  apply assembled rest Q (physical :: tail)
  simpa [List.reverse_cons, List.append_assoc] using continued

/-- A proved argument assembly feeds the generated underapplication host call
and stores its closure result in the compiler-selected dispatch local. -/
theorem wp_partialApplyBody_of_assembly
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {initial nextStore : Wasm.Store Host} {locals updated : Wasm.Locals}
    {argumentTarget rest : Wasm.Program} {physicalArgs : List Wasm.Value}
    {resultIndex : Nat} {function : Lean.Name} {arity fixed : Nat}
    {fieldKinds : Array AbiKind} {resultKind : AbiKind} {word : Word32}
    {tail : List Wasm.Value} {Q : Wasm.Assertion Host}
    (assembled :
      ClosureArgumentAssembly module hostEnv argumentTarget physicalArgs
        initial locals)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (partialApplyContract function arity fixed fieldKinds resultKind))
    (hParams : imp.params.length = physicalArgs.length)
    (hResults : imp.results.length = 1)
    (operation : partialApplyStep function arity fixed fieldKinds resultKind
      initial physicalArgs =
        .Return [.i32 (UInt32.ofNat word.value)] nextStore)
    (hSet : locals.set? resultIndex (.i32 (UInt32.ofNat word.value)) =
      some updated)
    (continued : Wasm.wp module rest Q nextStore
      { updated with values := tail } hostEnv) :
    Wasm.wp module
      (argumentTarget ++ .call id :: .localSet resultIndex :: rest)
      Q initial { locals with values := tail } hostEnv := by
  apply assembled (.call id :: .localSet resultIndex :: rest) Q tail
  apply wp_exact_host_call_of_return
    (step := partialApplyStep function arity fixed fieldKinds resultKind)
    (physicalArgs := physicalArgs)
    (results := [.i32 (UInt32.ofNat word.value)]) hImp hSat hi hContract
  · simp [hParams]
  · exact operation
  · simpa [hParams, hResults] using
      FirTalos.Concrete.wp_localSet_of_set (host := Host) hSet continued

/-- The saturated sibling of `wp_partialApplyBody_of_assembly`: the same
capture/argument prefix feeds an ordinary Wasm declaration call and stores its
single physical result in the dispatch local. -/
theorem wp_directCallBody_of_assembly
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {functionIndex resultIndex : Nat} {rest : Wasm.Program}
    {Q : Wasm.Assertion Host} {initial nextStore : Wasm.Store Host}
    {locals updated : Wasm.Locals} {argumentTarget : Wasm.Program}
    {physicalArgs : List Wasm.Value} {physicalResult : Wasm.Value}
    {tail : List Wasm.Value}
    (assembled :
      ClosureArgumentAssembly module hostEnv argumentTarget physicalArgs
        initial locals)
    (called : Wasm.TerminatesWith hostEnv module functionIndex initial
      (physicalArgs.reverse ++ tail)
      (fun final results =>
        final = nextStore ∧ results = physicalResult :: tail))
    (targetSet : locals.set? resultIndex physicalResult = some updated)
    (continued : Wasm.wp module rest Q nextStore
      { updated with values := tail } hostEnv) :
    Wasm.wp module
      (argumentTarget ++ .call functionIndex :: .localSet resultIndex :: rest)
      Q initial { locals with values := tail } hostEnv := by
  apply assembled (.call functionIndex :: .localSet resultIndex :: rest) Q tail
  exact wp_directCall_let called targetSet continued

/-- Postcondition installed around one generated closure candidate. Normal
fallthrough and `break 0` resume the enclosing dispatch suffix with the
original operand tail; deeper breaks lose one nesting level. -/
def closureDispatchResumePost
    (module : Wasm.Module) (hostEnv : Wasm.HostEnv Host)
    (rest : Wasm.Program) (Q : Wasm.Assertion Host)
    (tail : List Wasm.Value) : Wasm.Assertion Host :=
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

/-- The selected candidate body sits under one branch-resumption layer for
itself and one additional layer for every preceding nonmatching candidate. -/
def closureDispatchSelectedPost
    (module : Wasm.Module) (hostEnv : Wasm.HostEnv Host)
    (tail : List Wasm.Value) :
    Nat → Wasm.Program → Wasm.Assertion Host → Wasm.Assertion Host
  | 0, rest, Q => closureDispatchResumePost module hostEnv rest Q tail
  | depth + 1, rest, Q =>
      closureDispatchSelectedPost module hostEnv tail depth []
        (closureDispatchResumePost module hostEnv rest Q tail)

/-- Execute the complete compiler-shaped candidate fold when a prefix
nonmatches and the following candidate matches. Candidates after the selected
one are unreachable and therefore need no body proof. -/
theorem wp_resolvedClosureCandidateChain_of_selected
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {closureId : Lean.FVarId}
    {closureIndex : Nat}
    {address : Word32}
    {tail : List Wasm.Value}
    (before : List
      (ClosureCandidateCase sourceModule sourceFunction labels module spec
        initial closureId closureIndex address))
    (selected :
      ClosureCandidateCase sourceModule sourceFunction labels module spec
        initial closureId closureIndex address)
    (suffix : List
      (ClosureCandidateCase sourceModule sourceFunction labels module spec
        initial closureId closureIndex address))
    (rest : Wasm.Program)
    (Q : Wasm.Assertion Host)
    (hClosure :
      locals.get closureIndex =
        some (.i32 (UInt32.ofNat address.value)))
    (hSat : hostEnv.Satisfies module spec)
    (failureClear : clearFailure initial = initial)
    (beforeNonmatching :
      ∀ candidate, candidate ∈ before →
        candidate.matched = (0 : UInt32))
    (selectedMatches : (selected.matched != 0) = true)
    (selectedBody :
      Wasm.wp module selected.targetBody
        (closureDispatchSelectedPost module hostEnv tail before.length rest Q)
        selected.nextStore { locals with values := tail } hostEnv) :
    Wasm.wp module
      (resolvedClosureCandidateChain (before ++ selected :: suffix) ++ rest)
      Q initial { locals with values := tail } hostEnv := by
  induction before generalizing rest Q with
  | nil =>
      change Wasm.wp module
        (.localGet closureIndex :: .call selected.matcherIndex ::
          .iff 0 0 selected.targetBody
            (resolvedClosureCandidateChain suffix) :: rest)
        Q initial { locals with values := tail } hostEnv
      apply wp_closureCandidate hClosure selected.importFound hSat
        selected.importInBounds selected.contractFound selected.parameterCount
        selected.resultCount selected.operation
      rw [if_pos selectedMatches]
      change Wasm.wp module selected.targetBody
        (closureDispatchResumePost module hostEnv rest Q tail)
        selected.nextStore { locals with values := tail } hostEnv
      simpa [closureDispatchSelectedPost] using selectedBody
  | cons candidate before ih =>
      have candidateNonmatching : candidate.matched = 0 :=
        beforeNonmatching candidate (by simp)
      have remainingNonmatching :
          ∀ next, next ∈ before → next.matched = (0 : UInt32) := by
        intro next found
        exact beforeNonmatching next (by simp [found])
      have recursive :
          Wasm.wp module
            (resolvedClosureCandidateChain (before ++ selected :: suffix))
            (closureDispatchResumePost module hostEnv rest Q tail)
            initial { locals with values := tail } hostEnv := by
        have nestedBody :
            Wasm.wp module selected.targetBody
              (closureDispatchSelectedPost module hostEnv tail before.length []
                (closureDispatchResumePost module hostEnv rest Q tail))
              selected.nextStore { locals with values := tail } hostEnv := by
          simpa [closureDispatchSelectedPost] using selectedBody
        have recursiveWithNil :=
          ih [] (closureDispatchResumePost module hostEnv rest Q tail)
            remainingNonmatching nestedBody
        simpa using recursiveWithNil
      change Wasm.wp module
        (.localGet closureIndex :: .call candidate.matcherIndex ::
          .iff 0 0 candidate.targetBody
            (resolvedClosureCandidateChain (before ++ selected :: suffix)) ::
          rest)
        Q initial { locals with values := tail } hostEnv
      apply wp_closureCandidate hClosure candidate.importFound hSat
        candidate.importInBounds candidate.contractFound
        candidate.parameterCount candidate.resultCount candidate.operation
      have candidateOperationZero :
          closureMatchesStep candidate.function candidate.arity candidate.fixed
              initial [.i32 (UInt32.ofNat address.value)] =
            .Return [.i32 0] candidate.nextStore := by
        simpa [candidateNonmatching] using candidate.operation
      have candidateStore : candidate.nextStore = initial :=
        (closureMatchesStep_zero_store candidateOperationZero).trans failureClear
      rw [candidateNonmatching, candidateStore]
      change Wasm.wp module
        (resolvedClosureCandidateChain (before ++ selected :: suffix))
        (closureDispatchResumePost module hostEnv rest Q tail)
        initial { locals with values := tail } hostEnv
      exact recursive

/-- Full generated dispatch execution: after the selected body stores the
candidate result, the compiler's final `local.get` and arbitrary surrounding
suffix execute exactly once. -/
theorem wp_compileClosureDispatch_of_selected
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {closureId : Lean.FVarId}
    {closureIndex resultIndex : Nat}
    {address : Word32}
    {tail : List Wasm.Value}
    (before : List
      (ClosureCandidateCase sourceModule sourceFunction labels module spec
        initial closureId closureIndex address))
    (selected :
      ClosureCandidateCase sourceModule sourceFunction labels module spec
        initial closureId closureIndex address)
    (suffix : List
      (ClosureCandidateCase sourceModule sourceFunction labels module spec
        initial closureId closureIndex address))
    (rest : Wasm.Program)
    (Q : Wasm.Assertion Host)
    (hClosure :
      locals.get closureIndex =
        some (.i32 (UInt32.ofNat address.value)))
    (hSat : hostEnv.Satisfies module spec)
    (failureClear : clearFailure initial = initial)
    (beforeNonmatching :
      ∀ candidate, candidate ∈ before →
        candidate.matched = (0 : UInt32))
    (selectedMatches : (selected.matched != 0) = true)
    (selectedBody :
      Wasm.wp module selected.targetBody
        (closureDispatchSelectedPost module hostEnv tail before.length
          (.localGet resultIndex :: rest) Q)
        selected.nextStore { locals with values := tail } hostEnv) :
    Wasm.wp module
      (resolvedClosureCandidateChain (before ++ selected :: suffix) ++
        .localGet resultIndex :: rest)
      Q initial { locals with values := tail } hostEnv := by
  exact wp_resolvedClosureCandidateChain_of_selected before selected suffix
    (.localGet resultIndex :: rest) Q hClosure hSat failureClear
    beforeNonmatching selectedMatches selectedBody

/-- End-to-end structural closure-dispatch theorem. The exact candidates
enumerated by the compiler adapt to the numeric chain that Talos executes,
and the first matching candidate after a nonmatching prefix produces the
surrounding program's WP. -/
theorem compileClosureDispatch_correct_of_selected
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host}
    {initial : Wasm.Store Host}
    {locals : Wasm.Locals}
    {declId closureId : Lean.FVarId}
    {resultKind : AbiKind}
    {argumentCode : List Fir.Wasm.Instruction}
    {argumentKinds : Array AbiKind}
    {closureIndex resultIndex : Nat}
    {address : Word32}
    {tail : List Wasm.Value}
    (before : List
      (ClosureCandidateCase sourceModule sourceFunction labels module spec
        initial closureId closureIndex address))
    (selected :
      ClosureCandidateCase sourceModule sourceFunction labels module spec
        initial closureId closureIndex address)
    (suffix : List
      (ClosureCandidateCase sourceModule sourceFunction labels module spec
        initial closureId closureIndex address))
    (rest : Wasm.Program)
    (Q : Wasm.Assertion Host)
    (candidatesEq :
      context.program.decls.toList.flatMap (fun target =>
        compileClosureCandidatesForTarget declId closureId resultKind
          argumentCode argumentKinds target) =
        (before ++ selected :: suffix).map (·.source))
    (closureFound :
      findFVar? (functionBindings sourceFunction) closureId =
        some closureIndex)
    (resultFound :
      findFVar? (functionBindings sourceFunction) declId =
        some resultIndex)
    (hClosure :
      locals.get closureIndex =
        some (.i32 (UInt32.ofNat address.value)))
    (hSat : hostEnv.Satisfies module spec)
    (failureClear : clearFailure initial = initial)
    (beforeNonmatching :
      ∀ candidate, candidate ∈ before →
        candidate.matched = (0 : UInt32))
    (selectedMatches : (selected.matched != 0) = true)
    (selectedBody :
      Wasm.wp module selected.targetBody
        (closureDispatchSelectedPost module hostEnv tail before.length
          (.localGet resultIndex :: rest) Q)
        selected.nextStore { locals with values := tail } hostEnv) :
    instructions sourceModule sourceFunction labels
        (compileClosureDispatch context declId closureId resultKind
          argumentCode argumentKinds) =
      .ok (resolvedClosureCandidateChain (before ++ selected :: suffix) ++
        [.localGet resultIndex]) ∧
    Wasm.wp module
      ((resolvedClosureCandidateChain (before ++ selected :: suffix) ++
        [.localGet resultIndex]) ++ rest)
      Q initial { locals with values := tail } hostEnv := by
  constructor
  · exact instructions_compileClosureDispatch (before ++ selected :: suffix)
      candidatesEq closureFound resultFound
  · simpa [List.append_assoc] using
      wp_compileClosureDispatch_of_selected before selected suffix rest Q
        hClosure hSat failureClear beforeNonmatching selectedMatches selectedBody

end FirTalos.Concrete
