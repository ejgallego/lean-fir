import FirTalos.Correctness.Lowering

namespace FirTalos.Correctness

/--
Writing a computed result to a generated local consumes exactly the stack head
and preserves the operand tail. The premise is phrased using Talos's checked
`set?` operation, so out-of-range local indices cannot be hidden by the proof.
-/
theorem wp_localSet_of_set
    {module : Wasm.Module} {env : Wasm.HostEnv RuntimeHost}
    {rest : Wasm.Program} {Q : Wasm.Assertion RuntimeHost}
    {store : Wasm.Store RuntimeHost} {locals updated : Wasm.Locals}
    {index : Nat} {value : Wasm.Value} {tail : List Wasm.Value}
    (hSet : locals.set? index value = some updated)
    (continued :
      Wasm.wp module rest Q store { updated with values := tail } env) :
    Wasm.wp module (.localSet index :: rest) Q store
      { locals with values := value :: tail } env := by
  have stackSet :
      ({ locals with values := value :: tail }.set? index value) =
        (locals.set? index value).map
          (fun next => { next with values := value :: tail }) := by
    simp only [Wasm.Locals.set?]
    split
    · rfl
    · split <;> rfl
  simp only [Wasm.wp_localSet_cons]
  rw [stackSet, hSet]
  exact continued

/--
A generated sequence of `local.get` instructions loads source-order values
onto the operand stack in reverse order, exactly the shape consumed by Talos's
host-call convention. The pre-existing operand tail is left untouched.
-/
theorem wp_localGets
    {module : Wasm.Module} {env : Wasm.HostEnv RuntimeHost}
    {rest : Wasm.Program} {Q : Wasm.Assertion RuntimeHost}
    {store : Wasm.Store RuntimeHost} {locals : Wasm.Locals}
    {indices : List Nat} {values : List Wasm.Value}
    (tail : List Wasm.Value)
    (hGets :
      List.Forall₂ (fun index value => locals.get index = some value)
        indices values)
    (continued :
      Wasm.wp module rest Q store
        { locals with values := values.reverse ++ tail } env) :
    Wasm.wp module
      (indices.map Wasm.Instruction.localGet ++ rest)
      Q store { locals with values := tail } env := by
  induction hGets generalizing tail with
  | nil =>
      simpa using continued
  | cons hGet hGets ih =>
      rename_i index value indices values
      simp only [List.map_cons, List.cons_append, Wasm.wp_localGet_cons]
      have hGetNext :
          ({ locals with values := tail } : Wasm.Locals).get index =
            some value := by
        simpa [Wasm.Locals.get] using hGet
      rw [hGetNext]
      apply ih (tail := value :: tail)
      simpa [List.reverse_cons, List.append_assoc] using continued

/--
Complete generated constructor `let` sequence: load every field local, call
the semantic constructor host with the reversed physical stack prefix, and
bind the returned handle to the destination local before continuing.
-/
theorem wp_constructor_let
    {module : Wasm.Module} {env : Wasm.HostEnv Fir.Wasm.RuntimeHost}
    {spec : Wasm.HostSpec Fir.Wasm.RuntimeHost} {id : Nat}
    {imp : Wasm.ImportDecl} {rest : Wasm.Program}
    {Q : Wasm.Assertion Fir.Wasm.RuntimeHost}
    {initial : Wasm.Store Fir.Wasm.RuntimeHost}
    {locals updated : Wasm.Locals}
    {indices : List Nat} {physicalArgs : List Wasm.Value}
    {resultIndex : Nat}
    (info : Lean.Compiler.LCNF.CtorInfo)
    (fieldKinds : Array Fir.Wasm.AbiKind)
    (resultKind : Fir.Wasm.AbiKind)
    (semanticArgs : Array Fir.LeanIR.Impure.Value)
    (sourceRuntime : Fir.LeanIR.Impure.RuntimeState)
    (sourceValue : Fir.LeanIR.Impure.Value)
    (after : Fir.Wasm.HandleTable) (handle : Fir.Wasm.Handle)
    (tail : List Wasm.Value)
    (hGets :
      List.Forall₂ (fun index value => locals.get index = some value)
        indices physicalArgs)
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract :
      spec.contracts[id]? =
        some (hostContract (.allocCtor info fieldKinds resultKind)))
    (hParams : imp.params.length = physicalArgs.length)
    (hResults : imp.results.length = 1)
    (decoded :
      decodeArgs initial.host.handles fieldKinds physicalArgs = .ok semanticArgs)
    (allocated :
      Fir.LeanIR.Impure.allocCtor initial.host.runtime info semanticArgs =
        .ok (sourceRuntime, sourceValue))
    (usesHandle : resultKind.usesHandle = true)
    (encoded :
      initial.host.handles.encode resultKind sourceValue = .ok (after, handle))
    (hSet : locals.set? resultIndex (.i32 handle) = some updated)
    (continued :
      Wasm.wp module rest Q
        { initial with host := {
            initial.host with
            runtime := sourceRuntime
            handles := after
            fault? := none
            targetFailure? := none } }
        { updated with values := tail } env) :
    Wasm.wp module
      (indices.map Wasm.Instruction.localGet ++
        .call id :: .localSet resultIndex :: rest)
      Q initial { locals with values := tail } env := by
  apply wp_localGets tail hGets
  apply wp_constructor_call info fieldKinds resultKind physicalArgs
    semanticArgs sourceRuntime sourceValue after handle tail
    hImp hSat hi hContract hParams hResults
  · rfl
  · exact decoded
  · exact allocated
  · exact usesHandle
  · exact encoded
  · apply wp_localSet_of_set hSet
    exact continued

/--
Complete generated object-projection `let` sequence: load the object handle,
project through the semantic host contract, and store the encoded field in the
destination local before continuing with the original operand tail.
-/
theorem wp_objectProjection_let
    {module : Wasm.Module} {env : Wasm.HostEnv Fir.Wasm.RuntimeHost}
    {spec : Wasm.HostSpec Fir.Wasm.RuntimeHost} {id : Nat}
    {imp : Wasm.ImportDecl} {rest : Wasm.Program}
    {Q : Wasm.Assertion Fir.Wasm.RuntimeHost}
    {initial : Wasm.Store Fir.Wasm.RuntimeHost}
    {locals updated : Wasm.Locals}
    {objectIndex resultIndex : Nat}
    (index : Nat) (resultKind : Fir.Wasm.AbiKind)
    (objectHandle : Fir.Wasm.Handle)
    (sourceObject sourceValue : Fir.LeanIR.Impure.Value)
    (after : Fir.Wasm.HandleTable) (resultHandle : Fir.Wasm.Handle)
    (tail : List Wasm.Value)
    (hObject : locals.get objectIndex = some (.i32 objectHandle))
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract :
      spec.contracts[id]? =
        some (hostContract (.objectProj index resultKind)))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (decoded :
      decodeArgs initial.host.handles #[.tobject] [.i32 objectHandle] =
        .ok #[sourceObject])
    (projected :
      Fir.LeanIR.Impure.getObjectField initial.host.runtime sourceObject index =
        .ok sourceValue)
    (usesHandle : resultKind.usesHandle = true)
    (encoded :
      initial.host.handles.encode resultKind sourceValue =
        .ok (after, resultHandle))
    (hSet : locals.set? resultIndex (.i32 resultHandle) = some updated)
    (continued :
      Wasm.wp module rest Q
        { initial with host := {
            initial.host with
            handles := after
            fault? := none
            targetFailure? := none } }
        { updated with values := tail } env) :
    Wasm.wp module
      (.localGet objectIndex :: .call id :: .localSet resultIndex :: rest)
      Q initial { locals with values := tail } env := by
  apply wp_localGets
    (indices := [objectIndex]) (values := [.i32 objectHandle]) tail
  · exact .cons hObject .nil
  · apply wp_objectProjection_call index resultKind objectHandle
      sourceObject sourceValue after resultHandle tail
      hImp hSat hi hContract hParams hResults
    · rfl
    · exact decoded
    · exact projected
    · exact usesHandle
    · exact encoded
    · apply wp_localSet_of_set hSet
      exact continued

/-- A generated `i32.const` followed by the destination `local.set`. -/
theorem wp_i32Const_let
    {Host : Type} {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {rest : Wasm.Program} {Q : Wasm.Assertion Host}
    {store : Wasm.Store Host} {locals updated : Wasm.Locals}
    {resultIndex : Nat} (value : UInt32) (tail : List Wasm.Value)
    (hSet : locals.set? resultIndex (.i32 value) = some updated)
    (continued :
      Wasm.wp module rest Q store { updated with values := tail } env) :
    Wasm.wp module (.const value :: .localSet resultIndex :: rest)
      Q store { locals with values := tail } env := by
  rw [Wasm.wp_const_cons]
  apply wp_localSet_of_set hSet
  exact continued

/-- A generated `i64.const` followed by the destination `local.set`. -/
theorem wp_i64Const_let
    {Host : Type} {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {rest : Wasm.Program} {Q : Wasm.Assertion Host}
    {store : Wasm.Store Host} {locals updated : Wasm.Locals}
    {resultIndex : Nat} (value : UInt64) (tail : List Wasm.Value)
    (hSet : locals.set? resultIndex (.i64 value) = some updated)
    (continued :
      Wasm.wp module rest Q store { updated with values := tail } env) :
    Wasm.wp module (.constI64 value :: .localSet resultIndex :: rest)
      Q store { locals with values := tail } env := by
  rw [Wasm.wp_constI64_cons]
  apply wp_localSet_of_set hSet
  exact continued

/-- Natural-literal host call followed by its generated destination store. -/
theorem wp_naturalLiteral_let
    {module : Wasm.Module} {env : Wasm.HostEnv Fir.Wasm.RuntimeHost}
    {spec : Wasm.HostSpec Fir.Wasm.RuntimeHost} {id : Nat}
    {imp : Wasm.ImportDecl} {rest : Wasm.Program}
    {Q : Wasm.Assertion Fir.Wasm.RuntimeHost}
    {locals updated : Wasm.Locals} {resultIndex : Nat}
    (initial : Wasm.Store Fir.Wasm.RuntimeHost) (value : Nat)
    (after : Fir.Wasm.HandleTable) (handle : Fir.Wasm.Handle)
    (tail : List Wasm.Value)
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract :
      spec.contracts[id]? =
        some (hostContract (.naturalLiteral value .tobject)))
    (hParams : imp.params = [])
    (hResults : imp.results = [.i32])
    (encoded :
      initial.host.handles.encode .tobject
        (Fir.LeanIR.Impure.literal initial.host.runtime (.nat value)).2 =
          .ok (after, handle))
    (hSet : locals.set? resultIndex (.i32 handle) = some updated)
    (continued :
      Wasm.wp module rest Q
        { initial with host := {
            initial.host with
            runtime :=
              (Fir.LeanIR.Impure.literal initial.host.runtime (.nat value)).1
            handles := after
            fault? := none
            targetFailure? := none } }
        { updated with values := tail } env) :
    Wasm.wp module (.call id :: .localSet resultIndex :: rest)
      Q initial { locals with values := tail } env := by
  apply wp_naturalLiteral_call initial value
    hImp hSat hi hContract hParams hResults encoded
  apply wp_localSet_of_set hSet
  exact continued

/-- String-literal host call followed by its generated destination store. -/
theorem wp_stringLiteral_let
    {module : Wasm.Module} {env : Wasm.HostEnv Fir.Wasm.RuntimeHost}
    {spec : Wasm.HostSpec Fir.Wasm.RuntimeHost} {id : Nat}
    {imp : Wasm.ImportDecl} {rest : Wasm.Program}
    {Q : Wasm.Assertion Fir.Wasm.RuntimeHost}
    {locals updated : Wasm.Locals} {resultIndex : Nat}
    (initial : Wasm.Store Fir.Wasm.RuntimeHost) (value : String)
    (after : Fir.Wasm.HandleTable) (handle : Fir.Wasm.Handle)
    (tail : List Wasm.Value)
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract :
      spec.contracts[id]? =
        some (hostContract (.stringLiteral value .object)))
    (hParams : imp.params = [])
    (hResults : imp.results = [.i32])
    (encoded :
      initial.host.handles.encode .object
        (Fir.LeanIR.Impure.literal initial.host.runtime (.str value)).2 =
          .ok (after, handle))
    (hSet : locals.set? resultIndex (.i32 handle) = some updated)
    (continued :
      Wasm.wp module rest Q
        { initial with host := {
            initial.host with
            runtime :=
              (Fir.LeanIR.Impure.literal initial.host.runtime (.str value)).1
            handles := after
            fault? := none
            targetFailure? := none } }
        { updated with values := tail } env) :
    Wasm.wp module (.call id :: .localSet resultIndex :: rest)
      Q initial { locals with values := tail } env := by
  apply wp_stringLiteral_call initial value
    hImp hSat hi hContract hParams hResults encoded
  apply wp_localSet_of_set hSet
  exact continued

/--
The terminating Talos adapter distributes over symbolic instruction
concatenation. This is the sequence equation needed to connect each local W4
rule to the recursively compiled continuation.
-/
theorem instructions_append
    (sourceModule : Fir.Wasm.Module) (sourceFunction : Fir.Wasm.Function)
    (labels : List Lean.FVarId)
    (left right : List Fir.Wasm.Instruction) :
    instructions sourceModule sourceFunction labels (left ++ right) =
      (do
        let targetLeft ←
          instructions sourceModule sourceFunction labels left
        let targetRight ←
          instructions sourceModule sourceFunction labels right
        return targetLeft ++ targetRight) := by
  induction left with
  | nil =>
      simp [instructions]
  | cons head tail ih =>
      simp [instructions, ih]

/--
A successfully resolved symbolic `local.get` sequence adapts pointwise to the
numeric sequence consumed by `wp_localGets`, at any surrounding label depth.
-/
theorem instructions_localGets
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {fvarIds : List Lean.FVarId}
    {indices : List Nat}
    (found :
      List.Forall₂
        (fun fvarId index =>
          findFVar?
            (sourceFunction.params.toList ++ sourceFunction.locals.toList)
            fvarId = some index)
        fvarIds indices) :
    instructions sourceModule sourceFunction labels
        (fvarIds.map Fir.Wasm.Instruction.localGet) =
      .ok (indices.map Wasm.Instruction.localGet) := by
  induction found with
  | nil =>
      simp only [List.map, instructions]
      rfl
  | cons head tail ih =>
      simp [instructions, instruction, head, ih]

/--
Adapter equation for one compiled `let` boundary: independently adapted value
and continuation sequences are joined by the resolved numeric destination
`local.set`. This keeps source-variable lookup out of the subsequent WP proof.
-/
theorem instructions_let_sequence
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId}
    {valueCode restCode : List Fir.Wasm.Instruction}
    {targetValue targetRest : Wasm.Program}
    {result : Lean.FVarId} {resultIndex : Nat}
    (valueAdapted :
      instructions sourceModule sourceFunction labels valueCode =
        .ok targetValue)
    (resultFound :
      findFVar?
        (sourceFunction.params.toList ++ sourceFunction.locals.toList)
        result = some resultIndex)
    (restAdapted :
      instructions sourceModule sourceFunction labels restCode =
        .ok targetRest) :
    instructions sourceModule sourceFunction labels
        (valueCode ++ .localSet result :: restCode) =
      .ok (targetValue ++ .localSet resultIndex :: targetRest) := by
  rw [instructions_append, valueAdapted]
  simp [instructions, instruction, resultFound, restAdapted]
  rfl

end FirTalos.Correctness
