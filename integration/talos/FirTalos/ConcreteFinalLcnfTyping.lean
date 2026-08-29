import FirTalos.ConcreteStructuredValidation

/-!
# Source-semantic typing for final impure LCNF

This module begins the static admission layer used to instantiate W6's
schema-indexed source invariant.  The first boundary is intentionally generic:
successful pure external results are typed at the ABI selected by final LCNF,
and binding that result preserves a semantic local-kind environment.  The
`sumTo` running example exercises all three relevant result families (`Nat`,
`UInt8`, and later arbitrary-precision clients also reuse `Int`) without
enumerating reachable program states.
-/

namespace FirTalos.Concrete

open Fir.Wasm
open Fir.Wasm.Concrete
open Fir.LeanIR.Impure

/-- Every semantic binding selected by a final-LCNF local-kind row contains a
value of the promised ABI shape.  The row is name-directed in exactly the same
way as production lowering and residual validation. -/
def SemanticEnvAtLocalKinds (locals : Fir.Wasm.LocalKinds) (env : Env) : Prop :=
  ∀ fvarId kind,
    Fir.Wasm.findLocalKind? locals fvarId = some kind →
      SemanticBindingAtAbi env fvarId kind

/-- Binding a semantically typed value under the validator's replacement
operation preserves the complete semantic local-kind environment. -/
theorem SemanticEnvAtLocalKinds.bind_insertLocal
    {locals : Fir.Wasm.LocalKinds} {env : Env}
    {fvarId : Lean.FVarId} {kind : AbiKind} {value : Value}
    (typedEnv : SemanticEnvAtLocalKinds locals env)
    (typedValue : SemanticValueAtAbi kind value) :
    SemanticEnvAtLocalKinds (Fir.Wasm.insertLocal locals fvarId kind)
      (bind env fvarId value) := by
  intro query queryKind found
  rw [findLocalKind?_insertLocal] at found
  by_cases same : fvarId.name = query.name
  · rw [if_pos same] at found
    have queryKindEq : queryKind = kind := Option.some.inj found.symm
    subst queryKind
    have queryEq : query = fvarId := by
      cases query
      cases fvarId
      simp_all
    subst query
    exact SemanticBindingAtAbi.of_lookup
      (lookup_bind_self env fvarId value) typedValue
  · rw [if_neg same] at found
    intro actualFound
    apply typedEnv query queryKind found
    simpa [Fir.LeanIR.Impure.bind, Fir.LeanIR.Impure.lookup, same] using
      actualFound

/-- Natural literal allocation always returns an object reference, independent
of whether the runtime chooses a tagged immediate, promoted tag, or limb
object. -/
theorem semanticNaturalExternalResponse_value_at_tobject
    (runtime : RuntimeState) (value : Nat) :
    SemanticValueAtAbi .tobject
      (semanticNaturalExternalResponse runtime value).value := by
  change SemanticValueAtAbi .tobject (literal runtime (.nat value)).2
  simp only [literal]
  split
  · exact .tobject _
  · exact .tobject _

/-- Arbitrary-precision integer externals return a heap object at the common
`.tobject` source ABI. -/
theorem semanticIntegerExternalResponse_value_at_tobject
    (runtime : RuntimeState) (value : Int) :
    SemanticValueAtAbi .tobject
      (semanticIntegerExternalResponse runtime value).value := by
  exact .tobject _

/-- The scalar vocabulary and its ABI index agree definitionally. -/
theorem BoxedScalar.semanticValueAtAbi (scalar : BoxedScalar) :
    SemanticValueAtAbi scalar.kind.abiKind scalar.semanticValue := by
  cases scalar <;> constructor

/-- Every admitted pure external result carries a reusable semantic ABI fact
at exactly the kind computed for its final-LCNF destination. -/
theorem PureExternalSupported.resultSemanticValueAtAbi
    {context : Fir.Wasm.Context} {externals : ExternalImpl}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {sourceValue : Value} {stepCost : Nat}
    (supported : PureExternalSupported context externals sourceRuntime
      sourceEnv decl continuation nextRuntime sourceValue stepCost) :
    ∃ kind,
      Fir.Wasm.letValueKind decl = .ok kind ∧
        SemanticValueAtAbi kind sourceValue := by
  rcases supported with integer | natural | scalar
  · cases integer with
    | intro name args argumentCode argumentKinds semanticArgs target value
        valueEq operation nonempty targetFound targetExternal valueKind
        argumentsCompiled argumentsEvaluated signature resultCompiled
        semanticCalled nextRuntimeEq sourceValueEq stepCostEq =>
      refine ⟨.tobject, valueKind, ?_⟩
      rw [sourceValueEq]
      exact semanticIntegerExternalResponse_value_at_tobject sourceRuntime value
  · cases natural with
    | intro name args argumentCode argumentKinds semanticArgs target value
        valueEq operation nonempty targetFound targetExternal valueKind
        argumentsCompiled argumentsEvaluated signature resultCompiled
        semanticCalled nextRuntimeEq sourceValueEq stepCostEq =>
      refine ⟨.tobject, valueKind, ?_⟩
      rw [sourceValueEq]
      exact semanticNaturalExternalResponse_value_at_tobject sourceRuntime value
  · cases scalar with
    | intro name args argumentCode argumentKinds semanticArgs target scalar
        valueEq operation nonempty targetFound targetExternal valueKind
        argumentsCompiled argumentsEvaluated signature resultCompiled
        semanticCalled nextRuntimeEq sourceValueEq stepCostEq =>
      refine ⟨scalar.kind.abiKind, valueKind, ?_⟩
      rw [sourceValueEq]
      exact FirTalos.Concrete.BoxedScalar.semanticValueAtAbi scalar

/-- Binding an admitted pure external result is the generic environment
preservation step needed by syntax-directed final-LCNF typing. -/
theorem PureExternalSupported.bindResult_preservesSemanticEnvAtLocalKinds
    {context : Fir.Wasm.Context} {externals : ExternalImpl}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {sourceValue : Value} {stepCost : Nat}
    {locals : Fir.Wasm.LocalKinds}
    (supported : PureExternalSupported context externals sourceRuntime
      sourceEnv decl continuation nextRuntime sourceValue stepCost)
    (typedEnv : SemanticEnvAtLocalKinds locals sourceEnv) :
    ∃ kind,
      Fir.Wasm.letValueKind decl = .ok kind ∧
        SemanticEnvAtLocalKinds
          (Fir.Wasm.insertLocal locals decl.fvarId kind)
          (bind sourceEnv decl.fvarId sourceValue) := by
  obtain ⟨kind, valueKind, typedValue⟩ :=
    supported.resultSemanticValueAtAbi
  exact ⟨kind, valueKind, typedEnv.bind_insertLocal typedValue⟩

end FirTalos.Concrete
