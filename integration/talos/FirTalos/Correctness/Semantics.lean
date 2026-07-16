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
