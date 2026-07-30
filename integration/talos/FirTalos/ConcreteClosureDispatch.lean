import FirTalos.ConcreteRuntime

namespace FirTalos.Concrete

open Fir.Wasm
open Fir.LeanIR.Impure
open Fir.Wasm.Concrete
open FirTalos.Correctness

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
      .Return [.i32 matched] (clearFailure initial)

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
        initial { locals with values := tail } hostEnv) :
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
      rw [failureClear, if_pos selectedMatches]
      change Wasm.wp module selected.targetBody
        (closureDispatchResumePost module hostEnv rest Q tail)
        initial { locals with values := tail } hostEnv
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
              initial { locals with values := tail } hostEnv := by
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
      rw [failureClear, candidateNonmatching]
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
        initial { locals with values := tail } hostEnv) :
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
        initial { locals with values := tail } hostEnv) :
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
