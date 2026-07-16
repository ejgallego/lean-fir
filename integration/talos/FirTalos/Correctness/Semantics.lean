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

end FirTalos.Correctness
