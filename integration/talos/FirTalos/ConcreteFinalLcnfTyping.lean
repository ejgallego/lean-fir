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

/-- Project the semantic binding selected by one compiler local-row lookup. -/
theorem SemanticEnvAtLocalKinds.binding
    {locals : Fir.Wasm.LocalKinds} {env : Env}
    (typedEnv : SemanticEnvAtLocalKinds locals env)
    {fvarId : Lean.FVarId} {kind : AbiKind}
    (found : Fir.Wasm.findLocalKind? locals fvarId = some kind) :
    SemanticBindingAtAbi env fvarId kind :=
  typedEnv fvarId kind found

/-- A compiler-row binding can be used at any directionally weaker ABI. This
is the common return/call/publication rule for every non-reversing ABI edge. -/
theorem SemanticEnvAtLocalKinds.binding_ofRefines
    {locals : Fir.Wasm.LocalKinds} {env : Env}
    (typedEnv : SemanticEnvAtLocalKinds locals env)
    {fvarId : Lean.FVarId} {actual expected : AbiKind}
    (found : Fir.Wasm.findLocalKind? locals fvarId = some actual)
    (refines : actual.refines expected = true) :
    SemanticBindingAtAbi env fvarId expected :=
  SemanticBindingAtAbi.ofRefines (typedEnv.binding found) refines

/-- Minimal semantic provenance for using one compiler local at a possibly
more precise ABI.

Directional ABI refinement needs no additional dynamic evidence.  On every
other carrier-compatible edge (in particular the object-family edges accepted
by `AbiKind.leanCompatible`) the predicate retains exactly the semantic
binding required by this use.  It does not describe future code, a target
path, or every source local. -/
def SemanticBindingAtUseSite
    (env : Env) (fvarId : Lean.FVarId)
    (actual expected : AbiKind) : Prop :=
  actual.refines expected = true ∨ SemanticBindingAtAbi env fvarId expected

namespace SemanticBindingAtUseSite

/-- Directional compiler refinement constructs use-site provenance without
an additional semantic premise. -/
theorem ofRefines
    {env : Env} {fvarId : Lean.FVarId} {actual expected : AbiKind}
    (refines : actual.refines expected = true) :
    SemanticBindingAtUseSite env fvarId actual expected :=
  Or.inl refines

/-- Exact semantic producer information closes the non-directional use-site
case. -/
theorem ofSemanticBinding
    {env : Env} {fvarId : Lean.FVarId} {actual expected : AbiKind}
    (typed : SemanticBindingAtAbi env fvarId expected) :
    SemanticBindingAtUseSite env fvarId actual expected :=
  Or.inr typed

/-- Combine the compiler local-row fact with its minimal use-site provenance.
This is the only semantic elimination rule clients need. -/
theorem binding
    {env : Env} {fvarId : Lean.FVarId} {actual expected : AbiKind}
    (useSite : SemanticBindingAtUseSite env fvarId actual expected)
    (typedActual : SemanticBindingAtAbi env fvarId actual) :
    SemanticBindingAtAbi env fvarId expected := by
  rcases useSite with refines | typedExpected
  · exact typedActual.ofRefines refines
  · exact typedExpected

/-- A non-refining ABI edge exposes the exact semantic fact retained for that
use; the predicate cannot hide carrier-only specialization. -/
theorem semanticBinding_of_not_refines
    {env : Env} {fvarId : Lean.FVarId} {actual expected : AbiKind}
    (useSite : SemanticBindingAtUseSite env fvarId actual expected)
    (notRefines : actual.refines expected ≠ true) :
    SemanticBindingAtAbi env fvarId expected := by
  rcases useSite with refines | typedExpected
  · exact False.elim (notRefines refines)
  · exact typedExpected

end SemanticBindingAtUseSite

/-- A typed compiler local plus the minimal use-site fact gives the semantic
binding at the ABI required by that use. -/
theorem SemanticEnvAtLocalKinds.binding_atUseSite
    {locals : Fir.Wasm.LocalKinds} {env : Env}
    (typedEnv : SemanticEnvAtLocalKinds locals env)
    {fvarId : Lean.FVarId} {actual expected : AbiKind}
    (found : Fir.Wasm.findLocalKind? locals fvarId = some actual)
    (useSite : SemanticBindingAtUseSite env fvarId actual expected) :
    SemanticBindingAtAbi env fvarId expected :=
  useSite.binding (typedEnv.binding found)

/-- The existing concrete state relation already semantically types every
successfully compiled local.  No separately preserved whole-environment
invariant is needed: layout alignment identifies the exact target slot and
`PhysicalValueRel` erases to the corresponding source ABI fact. -/
theorem StateRelated.semanticBindingAtAbi_of_getLocal
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {targetStore : Wasm.Store Host} {targetLocals : Wasm.Locals}
    {witness : RefinementWitness} {fvarId : Lean.FVarId} {kind : AbiKind}
    (related : StateRelated sourceFunction sourceRuntime sourceEnv targetStore
      targetLocals witness)
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (compiled : Fir.Wasm.getLocal context fvarId =
      .ok (.localGet fvarId, kind)) :
    SemanticBindingAtAbi sourceEnv fvarId kind := by
  intro value found
  obtain ⟨index, localFound, kindAt⟩ := localsAligned compiled
  obtain ⟨_physical, _targetFound, valueRelated⟩ :=
    related.resolve found localFound kindAt
  exact valueRelated.semanticValueAtAbi

/-- Residual validator locals are semantically typed directly by the live
source/target relation and compiler-local agreement.  This projection is the
reason PA1 does not need to add `SemanticEnvAtLocalKinds` as another field of
the central simulation relation. -/
theorem SemanticEnvAtLocalKinds.ofStateRelated
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {locals : Fir.Wasm.LocalKinds} {sourceRuntime : RuntimeState}
    {sourceEnv : Env} {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals} {witness : RefinementWitness}
    (agrees : ConcreteStructuredValidationLocalsAgree context locals)
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (related : StateRelated sourceFunction sourceRuntime sourceEnv targetStore
      targetLocals witness) :
    SemanticEnvAtLocalKinds locals sourceEnv := by
  intro fvarId kind found
  exact related.semanticBindingAtAbi_of_getLocal localsAligned (agrees found)

/-- Compiler-owned return provenance at one current use site.

The production compiler chooses the actual local ABI.  Directional edges are
discharged by that ABI equation alone; only a non-directional object-family
edge retains semantic evidence about this result binding.  The predicate is
current-node and contains no future source execution or target path. -/
def ConcreteStructuredReturnUseSiteProvenanceAt
    (context : Fir.Wasm.Context) (sourceEnv : Env)
    (result : Lean.FVarId) (expected : AbiKind) : Prop :=
  ∀ {actual},
    Fir.Wasm.getLocal context result = .ok (.localGet result, actual) →
      SemanticBindingAtUseSite sourceEnv result actual expected

namespace ConcreteStructuredReturnUseSiteProvenanceAt

/-- A directional result ABI constructs the current use-site boundary without
any additional semantic evidence. -/
theorem ofRefines
    {context : Fir.Wasm.Context} {sourceEnv : Env}
    {result : Lean.FVarId} {expected : AbiKind}
    (refines : ∀ {actual},
      Fir.Wasm.getLocal context result = .ok (.localGet result, actual) →
        actual.refines expected = true) :
    ConcreteStructuredReturnUseSiteProvenanceAt context sourceEnv result
      expected := by
  intro actual compiled
  exact .ofRefines (refines compiled)

/-- Exact producer information constructs the boundary for every compiler
carrier assigned to this result. -/
theorem ofSemanticBinding
    {context : Fir.Wasm.Context} {sourceEnv : Env}
    {result : Lean.FVarId} {expected : AbiKind}
    (typed : SemanticBindingAtAbi sourceEnv result expected) :
    ConcreteStructuredReturnUseSiteProvenanceAt context sourceEnv result
      expected := by
  intro _actual _compiled
  exact .ofSemanticBinding typed

/-- Eliminate current return provenance using only the already-established
compiler layout and concrete state relation. -/
theorem semanticBinding
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {targetStore : Wasm.Store Host} {targetLocals : Wasm.Locals}
    {witness : RefinementWitness} {result : Lean.FVarId}
    {actual expected : AbiKind}
    (provenance : ConcreteStructuredReturnUseSiteProvenanceAt context sourceEnv
      result expected)
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (related : StateRelated sourceFunction sourceRuntime sourceEnv targetStore
      targetLocals witness)
    (compiled : Fir.Wasm.getLocal context result =
      .ok (.localGet result, actual)) :
    SemanticBindingAtAbi sourceEnv result expected :=
  (provenance compiled).binding
    (related.semanticBindingAtAbi_of_getLocal localsAligned compiled)

end ConcreteStructuredReturnUseSiteProvenanceAt

/-- Residual return validation plus the minimal use-site boundary derives the
exact semantic return fact consumed by W6's existing return simulator. -/
theorem ConcreteStructuredAlignedValidationState.returnSemantic_ofUseSite
    {program : Fir.LeanIR.ImpureProgram} {context : Fir.Wasm.Context}
    {functionResult : AbiKind} {result : Lean.FVarId}
    {sourceFunction : Fir.Wasm.Function} {sourceRuntime : RuntimeState}
    {sourceEnv : Env} {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals} {witness : RefinementWitness}
    (validated : ConcreteStructuredAlignedValidationState program context
      functionResult (.return result))
    (localsAligned : LocalLayoutAligned context sourceFunction)
    (related : StateRelated sourceFunction sourceRuntime sourceEnv targetStore
      targetLocals witness)
    (provenance : ConcreteStructuredReturnUseSiteProvenanceAt context sourceEnv
      result functionResult) :
    SemanticBindingAtAbi sourceEnv result functionResult := by
  obtain ⟨_joins, _locals, _facts, _sharing, focus, agrees⟩ := validated
  obtain ⟨actual, found, _compatible⟩ := focus.return_eq
  exact provenance.semanticBinding localsAligned related (agrees found)

/-- Use-site provenance closes both directional returns and the precise
object-family return edges for which carrier compatibility is insufficient. -/
theorem SemanticEnvAtLocalKinds.returnValueSafe_ofUseSite
    {locals : Fir.Wasm.LocalKinds} {source : MachineState}
    (typedEnv : SemanticEnvAtLocalKinds locals source.env)
    {result : Lean.FVarId} {actual functionResult : AbiKind}
    (control : source.control = .code (.return result))
    (found : Fir.Wasm.findLocalKind? locals result = some actual)
    (useSite :
      SemanticBindingAtUseSite source.env result actual functionResult) :
    ConcreteStructuredReturnValueSafeAt functionResult source :=
  ConcreteStructuredReturnValueSafeAt.of_semanticBinding control
    (typedEnv.binding_atUseSite found useSite)

/-- Directional result refinement plus the compiler local-row invariant is
already enough for source return safety. The only remaining return gap is the
reverse object-family compatibility accepted by Lean (`tobject` to a precise
`object` or `tagged` result), which needs independent semantic provenance. -/
theorem SemanticEnvAtLocalKinds.returnValueSafe_ofRefines
    {locals : Fir.Wasm.LocalKinds} {source : MachineState}
    (typedEnv : SemanticEnvAtLocalKinds locals source.env)
    {result : Lean.FVarId} {actual functionResult : AbiKind}
    (control : source.control = .code (.return result))
    (found : Fir.Wasm.findLocalKind? locals result = some actual)
    (refines : actual.refines functionResult = true) :
    ConcreteStructuredReturnValueSafeAt functionResult source :=
  typedEnv.returnValueSafe_ofUseSite control found (.ofRefines refines)

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

/-- Publish a source result at its exact effective compiler ABI.  This named
boundary is shared by direct producers, calls, closure calls, externals, and
lazy-cache hit/miss; the producer only has to supply the one semantic value
fact. -/
theorem SemanticEnvAtLocalKinds.publishResult
    {locals : Fir.Wasm.LocalKinds} {env : Env}
    {fvarId : Lean.FVarId} {kind : AbiKind} {value : Value}
    (typedEnv : SemanticEnvAtLocalKinds locals env)
    (typedValue : SemanticValueAtAbi kind value) :
    SemanticEnvAtLocalKinds (Fir.Wasm.insertLocal locals fvarId kind)
      (bind env fvarId value) :=
  typedEnv.bind_insertLocal typedValue

/-- The call/cache publication law: every exact physical result relation
erases to the same semantic result fact and therefore preserves the compiler
local environment when the result is bound.  Direct calls, saturated closure
calls, and both lazy-cache paths already produce this relation at their
effective result ABI. -/
theorem SemanticEnvAtLocalKinds.publishPhysicalResult
    {locals : Fir.Wasm.LocalKinds} {env : Env}
    {fvarId : Lean.FVarId} {kind : AbiKind} {value : Value}
    {witness : RefinementWitness} {physical : Wasm.Value}
    (typedEnv : SemanticEnvAtLocalKinds locals env)
    (related : PhysicalValueRel witness kind physical value) :
    SemanticEnvAtLocalKinds (Fir.Wasm.insertLocal locals fvarId kind)
      (bind env fvarId value) :=
  typedEnv.publishResult related.semanticValueAtAbi

/-- Publish an exact producer result and simultaneously expose it at a weaker
public use-site ABI.  The environment deliberately records the effective
producer kind; the second conjunct is the semantic fact used by a caller whose
declared carrier is weaker. -/
theorem SemanticEnvAtLocalKinds.publishResult_ofRefines
    {locals : Fir.Wasm.LocalKinds} {env : Env}
    {fvarId : Lean.FVarId} {actual expected : AbiKind} {value : Value}
    (typedEnv : SemanticEnvAtLocalKinds locals env)
    (typedValue : SemanticValueAtAbi actual value)
    (refines : actual.refines expected = true) :
    SemanticEnvAtLocalKinds (Fir.Wasm.insertLocal locals fvarId actual)
        (bind env fvarId value) ∧
      SemanticBindingAtAbi (bind env fvarId value) fvarId expected := by
  refine ⟨typedEnv.publishResult typedValue, ?_⟩
  exact SemanticBindingAtAbi.of_lookup (lookup_bind_self env fvarId value)
    (typedValue.ofRefines refines)

/-- Physical form of `publishResult_ofRefines`.  This is the exact shared
call/cache boundary: named calls provide `calleeResultRefines`, saturated
closure resolution provides `targetResultRefines`, and lazy initialization
provides `resultRefines`; hit and miss differ only in where the same physical
result relation is recovered. -/
theorem SemanticEnvAtLocalKinds.publishPhysicalResult_ofRefines
    {locals : Fir.Wasm.LocalKinds} {env : Env}
    {fvarId : Lean.FVarId} {actual expected : AbiKind} {value : Value}
    {witness : RefinementWitness} {physical : Wasm.Value}
    (typedEnv : SemanticEnvAtLocalKinds locals env)
    (related : PhysicalValueRel witness actual physical value)
    (refines : actual.refines expected = true) :
    SemanticEnvAtLocalKinds (Fir.Wasm.insertLocal locals fvarId actual)
        (bind env fvarId value) ∧
      SemanticBindingAtAbi (bind env fvarId value) fvarId expected :=
  typedEnv.publishResult_ofRefines related.semanticValueAtAbi refines

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
  exact ⟨kind, valueKind, typedEnv.publishResult typedValue⟩

end FirTalos.Concrete
