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
open FirTalos.Correctness

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
  obtain ⟨_joins, _locals, _facts, _sharing, focus, agrees,
    _localAlignment⟩ := validated
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

/-- A successful source step at a named-call `let` exposes the exact semantic
argument array evaluated by the interpreter.

This is the dynamic half of direct-call admission.  It uses only the active
compiler-focus equalities and the successful current source step; declaration
lookup, ABI compatibility, and callee selection remain static compiler facts.
In particular, no execution certificate or future callee behavior is stored. -/
theorem ConcreteStructuredCodeFocus.evalArgs_of_fap_step
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {labels : LabelContext}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetStore : Wasm.Store Host} {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program} {witness : RefinementWitness}
    {source sourceAfter : MachineState} {target : StructuredWasmState Host}
    {declaration : Lean.Name} {args : Array (Lean.Compiler.LCNF.Arg .impure)}
    (focus : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels sourceRuntime sourceEnv (.let decl continuation) targetStore
      targetLocals targetCode witness source target)
    (valueEq : decl.value = .fap declaration args)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    ∃ semanticArgs, evalArgs sourceEnv args = .ok semanticArgs := by
  rcases source with
    ⟨sourceProgram, sourceControl, stateEnv, stateJoins, stateFrames,
      stateRuntime⟩
  have sourceProgramEq := focus.sourceProgramEq
  have sourceControlEq := focus.sourceControlEq
  have sourceEnvEq := focus.sourceEnvEq
  have sourceRuntimeEq := focus.sourceRuntimeEq
  change sourceProgram = context.program at sourceProgramEq
  change sourceControl = .code (.let decl continuation) at sourceControlEq
  change stateEnv = sourceEnv at sourceEnvEq
  change stateRuntime = sourceRuntime at sourceRuntimeEq
  subst sourceProgram
  subst sourceControl
  subst stateEnv
  subst stateRuntime
  cases evaluated : evalArgs sourceEnv args with
  | error fault =>
      simp [executeStep, coreStep, evalLetValue, valueEq, evaluated, fail]
        at sourceStep
  | ok semanticArgs =>
      exact ⟨semanticArgs, rfl⟩

/-- Equal source parameter and argument arities construct the unique callee
environment accepted by `bindParams`.

The theorem is deliberately independent of argument ABI typing: the compiler
proves ABI refinement separately, while source invocation needs only the same
array cardinality. -/
theorem bindParams_exists_of_size_eq
    (params : Array (Lean.Compiler.LCNF.Param .impure)) (args : Array Value)
    (sizeEq : params.size = args.size) :
    ∃ calleeEnv, bindParams params args = .ok calleeEnv := by
  let calleeEnv : Env :=
    (params.toList.zip args.toList).foldl
      (fun env pair => bind env pair.fst.fvarId pair.snd) []
  refine ⟨calleeEnv, ?_⟩
  simp [bindParams, sizeEq, calleeEnv]

/-- Successful `Option` traversal preserves cardinality.  This is the static
array counterpart of successful source argument evaluation and is shared by
named-call argument and declaration-parameter classifiers. -/
theorem optionListMapM_length
    {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (mapped : xs.mapM f = some ys) : ys.length = xs.length := by
  induction xs generalizing ys with
  | nil =>
      have ysEq : ys = [] := by simpa using mapped.symm
      subst ys
      rfl
  | cons head tail ih =>
      cases headResult : f head with
      | none => simp [List.mapM_cons, headResult] at mapped
      | some value =>
          cases tailResult : tail.mapM f with
          | none => simp [List.mapM_cons, headResult, tailResult] at mapped
          | some values =>
              have ysEq : ys = value :: values := by
                simpa [List.mapM_cons, headResult, tailResult] using
                  mapped.symm
              subst ys
              simp [ih tailResult]

/-- Successful production parameter classification preserves declaration
arity without requiring a generated target row. -/
theorem declarationParameterKinds?_size_of_some
    {program : Fir.LeanIR.ImpureProgram}
    {declaration : Lean.Compiler.LCNF.Decl .impure}
    {parameterKinds : Array AbiKind}
    (known : Fir.Wasm.declarationParameterKinds? program declaration =
      some parameterKinds) :
    parameterKinds.size = declaration.params.size := by
  unfold Fir.Wasm.declarationParameterKinds? at known
  rw [Array.mapM_eq_mapM_toList] at known
  cases classified : declaration.params.toList.mapM
      (Fir.Wasm.declarationParamKind? program declaration) with
  | none => simp [classified] at known
  | some kinds =>
      have kindsEq : kinds.toArray = parameterKinds := by
        simpa [classified] using known
      rw [← kindsEq]
      simpa using optionListMapM_length classified

/-- Successful residual argument classification preserves source arity. -/
theorem supportedArgumentKinds_size_of_some
    {locals : Fir.Wasm.LocalKinds}
    {args : Array (Lean.Compiler.LCNF.Arg .impure)}
    {argumentKinds : Array AbiKind}
    (known : args.mapM (Fir.Wasm.supportedArgKind? locals) =
      some argumentKinds) :
    argumentKinds.size = args.size := by
  rw [Array.mapM_eq_mapM_toList] at known
  cases classified : args.toList.mapM (Fir.Wasm.supportedArgKind? locals) with
  | none => simp [classified] at known
  | some kinds =>
      have kindsEq : kinds.toArray = argumentKinds := by
        simpa [classified] using known
      rw [← kindsEq]
      simpa using optionListMapM_length classified

/-- A successful nullary named-call check exposes the declaration and exact
effective result lane, and proves that the selected source declaration is
itself nullary.  This is a direct inversion of production validation, not a
separate call-site certificate. -/
theorem supportedNamedCall_nullary_facts
    {program : Fir.LeanIR.ImpureProgram}
    {locals : Fir.Wasm.LocalKinds}
    {declared : AbiKind} {name : Lean.Name}
    (supported : Fir.Wasm.supportedNamedCall program locals declared name #[] =
      true) :
    ∃ target resultKind,
      program.findDecl? name = some target ∧
        Fir.Wasm.effectiveDeclarationResultKind? target = some resultKind ∧
        target.params.isEmpty = true := by
  unfold Fir.Wasm.supportedNamedCall at supported
  cases targetEq : program.findDecl? name with
  | none => simp [targetEq] at supported
  | some target =>
      cases bodyEq : target.value
      all_goals
        cases resultEq : Fir.Wasm.effectiveDeclarationResultKind? target <;>
          try simp [targetEq, bodyEq, resultEq] at supported
        cases parameterEq :
            Fir.Wasm.declarationParameterKinds? program target <;>
          try simp [parameterEq] at supported
        rename_i resultKind parameterKinds
        have acceptedFull :
            ((resultKind.refines declared = true ∨
                (target.params.isEmpty = true ∧
                  resultKind.leanCompatible declared = true)) ∧
              0 = parameterKinds.size) ∧
              ((#[] : Array AbiKind).zip parameterKinds).all
                  (fun pair : AbiKind × AbiKind =>
                    pair.fst.leanCompatible pair.snd) = true := by
          simpa [targetEq, bodyEq, resultEq, parameterEq, Bool.or_eq_true,
            Bool.and_eq_true] using supported
        have accepted := acceptedFull.1
        refine ⟨target, resultKind, rfl, resultEq, ?_⟩
        have parameterSize :=
          declarationParameterKinds?_size_of_some parameterEq
        rw [Array.isEmpty_iff_size_eq_zero]
        omega

/-- Residual validation constructs the complete static lazy-cache call site
for a nullary named-call `let`.  The theorem client supplies only the syntactic
head equation that selects this compiler family; all ABI and declaration
facts are recovered from the production validator. -/
theorem ConcreteStructuredAlignedValidationState.lazyCacheCallCompilerSite
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionResult : AbiKind}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {declaration : Lean.Name}
    (validated : ConcreteStructuredAlignedValidationState program context
      functionResult (.let decl continuation))
    (contextProgram : context.program = program)
    (valueEq : decl.value = .fap declaration #[]) :
    ∃ sourceDeclaration resultKind declaredResultKind,
      LazyCacheCallCompilerSite context decl declaration sourceDeclaration
        resultKind declaredResultKind := by
  subst program
  obtain ⟨_joins, locals, _facts, _sharing, focus, _agrees,
      _localAlignment⟩ := validated
  obtain ⟨_selectedKind, supported, _continuation⟩ := focus.let_eq
  cases declaredEq : Fir.Wasm.abiValueKind? decl.type with
  | none =>
      simp [Fir.Wasm.supportedLetDeclKind?, declaredEq] at supported
  | some declaredResultKind =>
      have callEq : Fir.Wasm.supportedNamedCall context.program locals
          declaredResultKind declaration #[] = true := by
        by_contra rejected
        have callFalse := Bool.eq_false_of_not_eq_true rejected
        simp [Fir.Wasm.supportedLetDeclKind?, declaredEq, valueEq,
          callFalse] at supported
      obtain ⟨sourceDeclaration, resultKind, targetEq, targetResultEq,
          paramsEq⟩ := supportedNamedCall_nullary_facts callEq
      exact ⟨sourceDeclaration, resultKind, declaredResultKind,
        ⟨valueEq, declaredEq, targetEq, targetResultEq, paramsEq⟩⟩

/-- The real supported-function package constructs the module-wide generated
lazy-cache environment at its exact compiler context. -/
theorem ConcreteSupportedFunction.lazyCacheGeneratedEnvironment
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    (spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts)
    (contextCaches :
      context.cachedDeclarations = Fir.Wasm.cachedDeclarationNames program) :
    LazyCacheGeneratedEnvironment context sourceModule :=
  LazyCacheGeneratedEnvironment.ofSupportedPipeline spec.contextProgram
    spec.programNamesUnique spec.lowered spec.adapted contextCaches

/-- A validated nullary call whose current cache lookup is a hit has exact
zero-allocation compiler admission.  The declaration, ABI lanes, destination
local, and generated cache environment are compiler-derived; only the current
semantic lookup is dynamic. -/
theorem ConcreteStructuredAlignedValidationState.admit_lazyHit_of_compiler
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module}
    {externals : ExternalImpl}
    {functionResult : AbiKind}
    {facts : ReuseCapacityFacts}
    {sourceRuntime : RuntimeState}
    {sourceEnv : Env}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {declaration : Lean.Name}
    {sourceValue : Value}
    (validated : ConcreteStructuredAlignedValidationState program context
      functionResult (.let decl continuation))
    (contextProgram : context.program = program)
    (generated : LazyCacheGeneratedEnvironment context sourceModule)
    (valueEq : decl.value = .fap declaration #[])
    (semanticFound :
      findGlobal? sourceRuntime.globals declaration = some sourceValue) :
    ConcreteStructuredCodeStepAdmission context sourceModule externals
      functionResult facts sourceRuntime sourceEnv 0
      (.let decl continuation) := by
  obtain ⟨sourceDeclaration, resultKind, declaredResultKind, site⟩ :=
    validated.lazyCacheCallCompilerSite contextProgram valueEq
  have call := validated.lazyCacheCallSupported contextProgram site
  exact .lazyHit call generated semanticFound

/-- The current recursively validated outcome closes the complete lazy-hit
admission branch directly from production facts and the current runtime
lookup.  This is one branch of the PA2 compiler admission law, not a
source-invariant hypothesis. -/
theorem ConcreteStructuredValidatedCodeOutcome.admit_lazyHit_of_compiler
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source : MachineState}
    {target : StructuredWasmState Host}
    {declaration : Lean.Name}
    {sourceValue : Value}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.let decl continuation) targetStore targetLocals targetCode witness source
      target)
    (valueEq : decl.value = .fap declaration #[])
    (semanticFound :
      findGlobal? sourceRuntime.globals declaration = some sourceValue) :
    ConcreteStructuredCodeStepAdmission context sourceModule externals
      functionResult facts sourceRuntime sourceEnv 0
      (.let decl continuation) :=
  related.core.validation.admit_lazyHit_of_compiler spec.contextProgram
    (spec.lazyCacheGeneratedEnvironment related.contextCaches) valueEq
    semanticFound

/-- Exact remaining backend-coverage boundary for a compiler-selected lazy
cache miss.  It names only the initializer shapes not yet implemented by the
current structured simulator; hit admission does not consume it. -/
def ConcreteStructuredLazyMissBackendCoverageAt
    (context : Fir.Wasm.Context)
    (sourceRuntime : RuntimeState)
    (decl : Lean.Compiler.LCNF.LetDecl .impure)
    (declaration : Lean.Name) : Prop :=
  ∀ {sourceDeclaration : Lean.Compiler.LCNF.Decl .impure}
      {resultKind declaredResultKind : AbiKind},
    LazyCacheCallCompilerSite context decl declaration sourceDeclaration
        resultKind declaredResultKind →
      findGlobal? sourceRuntime.globals declaration = none →
        ∃ calleeCode,
          LazyCacheInternalMissSupported context decl declaration
              sourceDeclaration resultKind calleeCode ∧
            Fir.Wasm.abiKind? sourceDeclaration.type =
              .ok (some resultKind) ∧
            resultKind ≠ .object ∧ resultKind ≠ .tobject

/-- Complete current lazy-cache admission from the validated compiler
relation, modulo the named backend miss-coverage boundary above.  Runtime
lookup selects the branch internally; clients cannot choose a stale hit/miss
witness or provide compiler ABI/local facts. -/
theorem ConcreteStructuredValidatedCodeOutcome.admit_lazy_of_compiler
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionCode : Lean.Compiler.LCNF.Code .impure}
    {sourceModule : Fir.Wasm.Module}
    {sourceFunction : Fir.Wasm.Function}
    {targetModule : AdaptedModule}
    {hosts : ResolvedHosts}
    {spec : ConcreteSupportedFunction program context functionCode sourceModule
      sourceFunction targetModule hosts}
    {externals : ExternalImpl}
    {labels : LabelContext}
    {entryRuntime sourceRuntime : RuntimeState}
    {entryStore targetStore : Wasm.Store Host}
    {entryWitness witness : RefinementWitness}
    {functionResult : AbiKind}
    {callerExpectedResult : Option AbiKind}
    {facts : ReuseCapacityFacts}
    {remainingBytes : Nat}
    {sourceEnv : Env}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program}
    {source : MachineState}
    {target : StructuredWasmState Host}
    {declaration : Lean.Name}
    (related : ConcreteStructuredValidatedCodeOutcome program context
      functionCode sourceModule sourceFunction targetModule hosts spec externals
      labels entryRuntime entryStore entryWitness functionResult
      callerExpectedResult facts remainingBytes sourceRuntime sourceEnv
      (.let decl continuation) targetStore targetLocals targetCode witness source
      target)
    (valueEq : decl.value = .fap declaration #[])
    (missCoverage : ConcreteStructuredLazyMissBackendCoverageAt context
      sourceRuntime decl declaration) :
    ConcreteStructuredCodeStepAdmission context sourceModule externals
      functionResult facts sourceRuntime sourceEnv 0
      (.let decl continuation) := by
  obtain ⟨sourceDeclaration, resultKind, declaredResultKind, site⟩ :=
    related.core.validation.lazyCacheCallCompilerSite spec.contextProgram
      valueEq
  have call := related.core.validation.lazyCacheCallSupported
    spec.contextProgram site
  have generated :=
    spec.lazyCacheGeneratedEnvironment related.contextCaches
  cases lookup : findGlobal? sourceRuntime.globals declaration with
  | some sourceValue =>
      exact .lazyHit call generated lookup
  | none =>
      obtain ⟨calleeCode, internal, resultClassified, notObject,
          notTObject⟩ := missCoverage site lookup
      exact .lazyMiss internal generated resultClassified notObject notTObject
        lookup

/-- Residual-validator local agreement turns one accepted source argument
into the exact production `compileArg` equation at the same ABI. -/
theorem ConcreteStructuredValidationLocalsAgree.compileArg_of_supported
    {context : Fir.Wasm.Context} {locals : Fir.Wasm.LocalKinds}
    (agrees : ConcreteStructuredValidationLocalsAgree context locals)
    {arg : Lean.Compiler.LCNF.Arg .impure} {kind : AbiKind}
    (supported : Fir.Wasm.supportedArgKind? locals arg = some kind) :
    ∃ code, Fir.Wasm.compileArg context arg = .ok (code, kind) := by
  cases arg with
  | erased =>
      simp [Fir.Wasm.supportedArgKind?] at supported
      subst kind
      exact ⟨[.i32Const .erased 0], rfl⟩
  | fvar fvarId =>
      have compiled := agrees supported
      unfold Fir.Wasm.getLocal at compiled
      cases found : Fir.Wasm.findLocalKind? context.localKinds fvarId with
      | none =>
          rw [found] at compiled
          contradiction
      | some actual =>
          rw [found] at compiled
          have actualEq : actual = kind := by
            have pairEq :
                (Fir.Wasm.Instruction.localGet fvarId, actual) =
                  (.localGet fvarId, kind) := Except.ok.inj compiled
            exact congrArg Prod.snd pairEq
          subst actual
          exact ⟨[.localGet fvarId], by simp [Fir.Wasm.compileArg, found]⟩
  | type expr impossible => exact nomatch impossible

private theorem compileArgsList_of_supported
    {context : Fir.Wasm.Context} {locals : Fir.Wasm.LocalKinds}
    (agrees : ConcreteStructuredValidationLocalsAgree context locals)
    {args : List (Lean.Compiler.LCNF.Arg .impure)} {kinds : List AbiKind}
    (supported : args.mapM (Fir.Wasm.supportedArgKind? locals) = some kinds)
    (prefixCode : List Fir.Wasm.Instruction) (prefixKinds : Array AbiKind) :
    ∃ code,
      args.foldlM (init := (prefixCode, prefixKinds))
          (fun (instructions, accumulatedKinds) arg => do
            let (argument, kind) ← Fir.Wasm.compileArg context arg
            return (instructions ++ argument, accumulatedKinds.push kind)) =
        .ok (code, prefixKinds ++ kinds.toArray) := by
  induction args generalizing kinds prefixCode prefixKinds with
  | nil =>
      have kindsEq : kinds = [] := by simpa using supported.symm
      subst kinds
      exact ⟨prefixCode, by simp [pure, Except.pure]⟩
  | cons arg tail ih =>
      cases argFound : Fir.Wasm.supportedArgKind? locals arg with
      | none => simp [List.mapM_cons, argFound] at supported
      | some kind =>
          cases tailFound : tail.mapM (Fir.Wasm.supportedArgKind? locals) with
          | none => simp [List.mapM_cons, argFound, tailFound] at supported
          | some tailKinds =>
              have kindsEq : kinds = kind :: tailKinds := by
                simpa [List.mapM_cons, argFound, tailFound] using supported.symm
              subst kinds
              obtain ⟨argumentCode, argumentCompiled⟩ :=
                agrees.compileArg_of_supported argFound
              obtain ⟨code, tailCompiled⟩ := ih tailFound
                (prefixCode ++ argumentCode) (prefixKinds.push kind)
              refine ⟨code, ?_⟩
              simp only [List.foldlM_cons, argumentCompiled, Bind.bind,
                Except.bind]
              change
                tail.foldlM
                    (init := (prefixCode ++ argumentCode,
                      prefixKinds.push kind))
                    (fun (instructions, accumulatedKinds) arg => do
                      let (argument, nextKind) ← Fir.Wasm.compileArg context arg
                      return (instructions ++ argument,
                        accumulatedKinds.push nextKind)) =
                  .ok (code, prefixKinds ++ (kind :: tailKinds).toArray)
              rw [tailCompiled]
              simp

/-- Successful residual argument classification and local-row agreement expose
the exact production argument compiler result.  This theorem is shared by
direct calls, source externals, constructors, and closure ingress. -/
theorem ConcreteStructuredValidationLocalsAgree.compileArgs_of_supported
    {context : Fir.Wasm.Context} {locals : Fir.Wasm.LocalKinds}
    (agrees : ConcreteStructuredValidationLocalsAgree context locals)
    {args : Array (Lean.Compiler.LCNF.Arg .impure)}
    {argumentKinds : Array AbiKind}
    (supported : args.mapM (Fir.Wasm.supportedArgKind? locals) =
      some argumentKinds) :
    ∃ argumentCode,
      Fir.Wasm.compileArgs context args = .ok (argumentCode, argumentKinds) := by
  rw [Array.mapM_eq_mapM_toList] at supported
  cases classified : args.toList.mapM (Fir.Wasm.supportedArgKind? locals) with
  | none => simp [classified] at supported
  | some kinds =>
      have kindsEq : kinds.toArray = argumentKinds := by
        simpa [classified] using supported
      obtain ⟨argumentCode, compiled⟩ :=
        compileArgsList_of_supported agrees classified [] #[]
      refine ⟨argumentCode, ?_⟩
      unfold Fir.Wasm.compileArgs
      rw [← Array.foldlM_toList]
      simpa [kindsEq] using compiled

/-- The effective result selected for any declaration refines the
declaration's public ABI.  This is a definitional compiler property: the
selector either keeps the declared kind or records a straight-line result
only after checking that exact refinement. -/
theorem effectiveDeclarationResultKind?_declared_refines
    {declaration : Lean.Compiler.LCNF.Decl .impure} {result : AbiKind}
    (resultFound :
      Fir.Wasm.effectiveDeclarationResultKind? declaration = some result) :
    ∃ declared,
      Fir.Wasm.directAbiKind? declaration.type = some declared ∧
        result.refines declared = true := by
  unfold Fir.Wasm.effectiveDeclarationResultKind? at resultFound
  cases classified : Fir.Wasm.abiKind? declaration.type with
  | error error => simp [classified] at resultFound
  | ok kind? =>
      cases kind? with
      | none => simp [classified] at resultFound
      | some declared =>
          refine ⟨declared, by simp [Fir.Wasm.directAbiKind?, classified], ?_⟩
          simp only [classified, Bind.bind, Option.bind_some] at resultFound
          split at resultFound
          · simp_all [AbiKind.refines]
          · cases valueEq : declaration.value <;>
              simp_all [AbiKind.refines]
            all_goals
              split at resultFound <;> try simp_all
              split at resultFound <;> try simp_all
              all_goals
                rename_i actual actualEq
                subst declared
                change (if actual.refines .tobject = true then some actual
                  else some .tobject) = some result at resultFound
                by_cases refined : actual.refines .tobject = true
                · simp [refined] at resultFound
                  subst result
                  simpa [AbiKind.refines] using refined
                · simp [refined] at resultFound
                  subst result
                  simp

/-- Exact facts exposed by successful production validation of one internal
named call.

The result edge is directional because production validation requires the
effective callee result to refine the source `let` ABI for non-cached calls.
Ordinary arguments retain Lean's object-family carrier compatibility; their
semantic ingress is the one remaining named-call provenance boundary. -/
theorem supportedNamedCall_internal_facts
    {program : Fir.LeanIR.ImpureProgram} {locals : Fir.Wasm.LocalKinds}
    {declared : AbiKind} {name : Lean.Name}
    {args : Array (Lean.Compiler.LCNF.Arg .impure)}
    {target : Lean.Compiler.LCNF.Decl .impure}
    {calleeCode : Lean.Compiler.LCNF.Code .impure}
    (supported : Fir.Wasm.supportedNamedCall program locals declared name args =
      true)
    (targetFound : program.findDecl? name = some target)
    (bodyEq : target.value = .code calleeCode)
    (nonCached : (args.isEmpty && target.params.isEmpty) = false) :
    ∃ resultKind parameterKinds argumentKinds,
      Fir.Wasm.effectiveDeclarationResultKind? target = some resultKind ∧
      Fir.Wasm.declarationParameterKinds? program target = some parameterKinds ∧
      args.mapM (Fir.Wasm.supportedArgKind? locals) = some argumentKinds ∧
      resultKind.refines declared = true ∧
      argumentKinds.size = parameterKinds.size ∧
      (argumentKinds.zip parameterKinds).all
      (fun pair => pair.fst.leanCompatible pair.snd) = true := by
  unfold Fir.Wasm.supportedNamedCall at supported
  simp only [targetFound] at supported
  rw [bodyEq] at supported
  split at supported <;>
    simp_all [Bool.or_eq_true, Bool.and_eq_true]
  all_goals aesop

/-- Static, compiler-owned portion of one ordinary internal named-call site.

All dynamic interpreter equations are deliberately absent.  Result
refinement and destination-local selection are production validator facts.
`argumentsRefine` remains the exact difference between carrier-compatible
named-call arguments and the directional relation consumed by the current
call simulator. -/
structure DirectInternalCallCompilerAdmission
    (context : Fir.Wasm.Context) (locals : Fir.Wasm.LocalKinds)
    (decl : Lean.Compiler.LCNF.LetDecl .impure) where
  declaration : Lean.Name
  sourceDeclaration : Lean.Compiler.LCNF.Decl .impure
  calleeCode : Lean.Compiler.LCNF.Code .impure
  resultKind : AbiKind
  parameterKinds : Array AbiKind
  declaredCalleeResultKind : AbiKind
  calleeResultKind : AbiKind
  args : Array (Lean.Compiler.LCNF.Arg .impure)
  argumentKinds : Array AbiKind
  valueEq : decl.value = .fap declaration args
  kindEq : Fir.Wasm.checkedAbiKind decl.type = .ok resultKind
  declarationFound :
    context.program.findDecl? declaration = some sourceDeclaration
  parametersKnown :
    Fir.Wasm.declarationParameterKinds? context.program sourceDeclaration =
      some parameterKinds
  argumentsClassified :
    args.mapM (Fir.Wasm.supportedArgKind? locals) = some argumentKinds
  argumentsRefine :
    Fir.Wasm.kindsRefine argumentKinds parameterKinds = true
  declaredCalleeResult :
    Fir.Wasm.directAbiKind? sourceDeclaration.type =
      some declaredCalleeResultKind
  calleeResult :
    Fir.Wasm.effectiveDeclarationResultKind? sourceDeclaration =
      some calleeResultKind
  calleeResultRefines : calleeResultKind.refines resultKind = true
  nonCached :
    (args.isEmpty && sourceDeclaration.params.isEmpty) = false
  bodyEq : sourceDeclaration.value = .code calleeCode
  destinationValidated :
    Fir.Wasm.supportedLetDeclKind? context.program locals decl =
      some calleeResultKind
  resultCompiled :
    Fir.Wasm.getLocal context decl.fvarId =
      .ok (.localGet decl.fvarId, calleeResultKind)

/-- Production validation constructs the complete static direct-call
admission once the remaining argument-ingress refinement is supplied.

The existential arrays are the exact parameter and argument rows selected by
the validator.  Their carrier compatibility is compiler-derived.  The final
function shows that result refinement, declaration classification,
destination-local selection, and every other static site field no longer need
to be premises of PA2. -/
theorem ConcreteStructuredAlignedValidationState.directInternalCallBoundary
    {program : Fir.LeanIR.ImpureProgram}
    {context : Fir.Wasm.Context}
    {functionResult : AbiKind}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    (validated : ConcreteStructuredAlignedValidationState program context
      functionResult (.let decl continuation))
    (contextProgram : context.program = program)
    {declaration : Lean.Name}
    {sourceDeclaration : Lean.Compiler.LCNF.Decl .impure}
    {calleeCode : Lean.Compiler.LCNF.Code .impure}
    {args : Array (Lean.Compiler.LCNF.Arg .impure)}
    (valueEq : decl.value = .fap declaration args)
    (declarationFound :
      context.program.findDecl? declaration = some sourceDeclaration)
    (bodyEq : sourceDeclaration.value = .code calleeCode)
    (nonCached :
      (args.isEmpty && sourceDeclaration.params.isEmpty) = false) :
    ∃ locals parameterKinds argumentKinds,
      argumentKinds.size = parameterKinds.size ∧
        (argumentKinds.zip parameterKinds).all
            (fun pair => pair.fst.leanCompatible pair.snd) = true ∧
        (Fir.Wasm.kindsRefine argumentKinds parameterKinds = true →
          Nonempty (DirectInternalCallCompilerAdmission context locals decl)) := by
  subst program
  obtain ⟨joins, locals, facts, sharing, focus, _agrees, localAlignment⟩ :=
    validated
  obtain ⟨selectedKind, supportedDecl, _continuationValidation⟩ := focus.let_eq
  cases declaredFound : Fir.Wasm.abiValueKind? decl.type with
  | none =>
      unfold Fir.Wasm.supportedLetDeclKind? at supportedDecl
      simp [declaredFound] at supportedDecl
  | some declared =>
      have supportedCall :
          Fir.Wasm.supportedNamedCall context.program locals declared
            declaration args = true := by
        by_contra rejected
        have rejectedEq :
            Fir.Wasm.supportedNamedCall context.program locals declared
              declaration args = false :=
          Bool.eq_false_of_not_eq_true rejected
        unfold Fir.Wasm.supportedLetDeclKind? at supportedDecl
        simp [declaredFound, valueEq, rejectedEq] at supportedDecl
      obtain ⟨calleeResultKind, parameterKinds, argumentKinds,
          calleeResult, parametersKnown, argumentsClassified,
          calleeResultRefines, argumentSizes, argumentsCompatible⟩ :=
        supportedNamedCall_internal_facts supportedCall declarationFound bodyEq
          nonCached
      obtain ⟨declaredCalleeResultKind, declaredCalleeResult,
          _calleeRefinesDeclaration⟩ :=
        effectiveDeclarationResultKind?_declared_refines calleeResult
      have kindEq : Fir.Wasm.checkedAbiKind decl.type = .ok declared :=
        checkedAbiKind_of_abiValueKind? declaredFound
      have validatedEffective :
          Fir.Wasm.effectiveLetValueKind context.program decl =
            .ok selectedKind :=
        supportedLetDeclKind?_effectiveLetValueKind supportedDecl
      have resultCompatible :
          calleeResultKind.leanCompatible declared = true :=
        Fir.Wasm.AbiKind.leanCompatible_of_refines calleeResultRefines
      have callEffective :
          Fir.Wasm.effectiveLetValueKind context.program decl =
            .ok calleeResultKind := by
        unfold Fir.Wasm.effectiveLetValueKind Fir.Wasm.letValueKind
        rw [valueEq, kindEq]
        simp only [Bind.bind, Except.bind, pure, Except.pure]
        rw [declarationFound]
        simp only
        rw [calleeResult]
        simp only
        rw [if_pos resultCompatible]
      have selectedEq : selectedKind = calleeResultKind :=
        Except.ok.inj (validatedEffective.symm.trans callEffective)
      subst selectedKind
      have resultCompiled :
          Fir.Wasm.getLocal context decl.fvarId =
            .ok (.localGet decl.fvarId, calleeResultKind) :=
        localAlignment.letHead validatedEffective
      refine ⟨locals, parameterKinds, argumentKinds, argumentSizes,
        argumentsCompatible, ?_⟩
      intro argumentsRefine
      exact ⟨{
        declaration := declaration
        sourceDeclaration := sourceDeclaration
        calleeCode := calleeCode
        resultKind := declared
        parameterKinds := parameterKinds
        declaredCalleeResultKind := declaredCalleeResultKind
        calleeResultKind := calleeResultKind
        args := args
        argumentKinds := argumentKinds
        valueEq := valueEq
        kindEq := kindEq
        declarationFound := declarationFound
        parametersKnown := parametersKnown
        argumentsClassified := argumentsClassified
        argumentsRefine := argumentsRefine
        declaredCalleeResult := declaredCalleeResult
        calleeResult := calleeResult
        calleeResultRefines := calleeResultRefines
        nonCached := nonCached
        bodyEq := bodyEq
        destinationValidated := supportedDecl
        resultCompiled := resultCompiled }⟩

private theorem exceptListMapM_length
    {α β ε : Type} {f : α → Except ε β} {xs : List α} {ys : List β}
    (mapped : xs.mapM f = .ok ys) : ys.length = xs.length := by
  induction xs generalizing ys with
  | nil =>
      change Except.ok [] = Except.ok ys at mapped
      have ysEq : ([] : List β) = ys := Except.ok.inj mapped
      subst ys
      rfl
  | cons head tail ih =>
      rw [List.mapM_cons] at mapped
      cases headResult : f head with
      | error fault =>
          rw [headResult] at mapped
          change Except.error fault = Except.ok ys at mapped
          contradiction
      | ok value =>
          rw [headResult] at mapped
          cases tailResult : tail.mapM f with
          | error fault =>
              rw [tailResult] at mapped
              change Except.error fault = Except.ok ys at mapped
              contradiction
          | ok values =>
              rw [tailResult] at mapped
              change Except.ok (value :: values) = Except.ok ys at mapped
              have ysEq : value :: values = ys := Except.ok.inj mapped
              subst ys
              simp [ih tailResult]

/-- Successful source argument evaluation preserves source arity. -/
theorem evalArgs_size_of_ok
    {env : Env} {args : Array (Lean.Compiler.LCNF.Arg .impure)}
    {values : Array Value} (evaluated : evalArgs env args = .ok values) :
    values.size = args.size := by
  unfold evalArgs at evaluated
  rw [Array.mapM_eq_mapM_toList] at evaluated
  cases classified : args.toList.mapM (evalArg env) with
  | error fault => simp [classified] at evaluated
  | ok semanticValues =>
      have valuesEq : semanticValues.toArray = values := by
        simpa [classified] using evaluated
      rw [← valuesEq]
      simpa using exceptListMapM_length classified

/-- The static compiler admission plus the successful current source step
construct every field of the existing direct-call site.

This is the dynamic hidden-interface elimination: source argument evaluation,
callee-environment binding, and production argument compilation are all
reconstructed rather than accepted from a client.  Destination-local
compilation remains an exact static equation in the compiler boundary; the
PA1 static extractor will derive it together with the two explicitly named
directional ABI facts. -/
theorem DirectInternalCallCompilerAdmission.toSite_of_step
    {context : Fir.Wasm.Context} {locals : Fir.Wasm.LocalKinds}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : LabelContext} {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {targetStore : Wasm.Store Host} {targetLocals : Wasm.Locals}
    {targetCode : Wasm.Program} {witness : RefinementWitness}
    {source sourceAfter : MachineState} {target : StructuredWasmState Host}
    (admission : DirectInternalCallCompilerAdmission context locals decl)
    (agrees : ConcreteStructuredValidationLocalsAgree context locals)
    (focus : ConcreteStructuredCodeFocus context sourceModule sourceFunction
      labels sourceRuntime sourceEnv (.let decl continuation) targetStore
      targetLocals targetCode witness source target)
    (sourceStep : executeStep externals source = .next sourceAfter) :
    Nonempty (DirectInternalCallSite context decl sourceEnv) := by
  obtain ⟨argumentCode, argumentsCompiled⟩ :=
    agrees.compileArgs_of_supported admission.argumentsClassified
  obtain ⟨semanticArgs, argumentsEvaluated⟩ :=
    focus.evalArgs_of_fap_step admission.valueEq sourceStep
  have argumentKindsSize : admission.argumentKinds.size = admission.args.size :=
    supportedArgumentKinds_size_of_some admission.argumentsClassified
  have parameterKindsSize :
      admission.parameterKinds.size = admission.sourceDeclaration.params.size :=
    declarationParameterKinds?_size_of_some admission.parametersKnown
  have semanticArgsSize : semanticArgs.size = admission.args.size :=
    evalArgs_size_of_ok argumentsEvaluated
  have refinedSizes :
      admission.argumentKinds.size = admission.parameterKinds.size := by
    have argumentsRefine := admission.argumentsRefine
    simp only [Fir.Wasm.kindsRefine, Bool.and_eq_true] at argumentsRefine
    exact beq_iff_eq.mp argumentsRefine.1
  have parameterSemanticSize :
      admission.sourceDeclaration.params.size = semanticArgs.size := by
    calc
      admission.sourceDeclaration.params.size =
          admission.parameterKinds.size := parameterKindsSize.symm
      _ = admission.argumentKinds.size := refinedSizes.symm
      _ = admission.args.size := argumentKindsSize
      _ = semanticArgs.size := semanticArgsSize.symm
  obtain ⟨calleeEnv, parametersBound⟩ := bindParams_exists_of_size_eq
    admission.sourceDeclaration.params semanticArgs parameterSemanticSize
  exact ⟨{
    declaration := admission.declaration
    sourceDeclaration := admission.sourceDeclaration
    calleeCode := admission.calleeCode
    calleeEnv := calleeEnv
    resultKind := admission.resultKind
    parameterKinds := admission.parameterKinds
    declaredCalleeResultKind := admission.declaredCalleeResultKind
    calleeResultKind := admission.calleeResultKind
    args := admission.args
    argumentCode := argumentCode
    argumentKinds := admission.argumentKinds
    semanticArgs := semanticArgs
    valueEq := admission.valueEq
    kindEq := admission.kindEq
    declarationFound := admission.declarationFound
    parametersKnown := admission.parametersKnown
    argumentsRefine := admission.argumentsRefine
    declaredCalleeResult := admission.declaredCalleeResult
    calleeResult := admission.calleeResult
    calleeResultRefines := admission.calleeResultRefines
    nonCached := admission.nonCached
    bodyEq := admission.bodyEq
    argumentsCompiled := argumentsCompiled
    argumentsEvaluated := argumentsEvaluated
    parametersBound := parametersBound
    resultCompiled := admission.resultCompiled }⟩

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
