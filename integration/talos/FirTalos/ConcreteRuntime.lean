import FirTalos.Correctness.Semantics
import Fir.Wasm.Concrete

namespace FirTalos.Concrete

open Fir.Wasm
open Fir.LeanIR.Impure
open Fir.Wasm.Concrete
open FirTalos.Correctness

/-- Lift W6's ABI-indexed concrete lane relation to Talos runtime values. The
four constructors are the only representation conversion performed at the
host boundary; object words remain exact wasm32 bit patterns. -/
inductive PhysicalValueRel (witness : RefinementWitness) :
    AbiKind → Wasm.Value → Value → Prop where
  | word32 (related : ValueRel witness kind (.word32 word) semantic) :
      PhysicalValueRel witness kind (.i32 (UInt32.ofNat word.value)) semantic
  | word64 (related : ValueRel witness kind (.word64 word) semantic) :
      PhysicalValueRel witness kind (.i64 word) semantic
  | float32Bits (related : ValueRel witness kind (.float32Bits bits) semantic) :
      PhysicalValueRel witness kind (.f32 bits) semantic
  | float64Bits (related : ValueRel witness kind (.float64Bits bits) semantic) :
      PhysicalValueRel witness kind (.f64 bits) semantic

/-- Every live FIR binding is represented in its compiler-assigned local by a
W6 concrete lane. Unlike W5's opaque-handle relation, this relation exposes
the exact address/tag word consumed by the concrete runtime. -/
def EnvLocalsRelated (witness : RefinementWitness)
    (bindings : List (Lean.FVarId × AbiKind)) (source : Env)
    (target : Wasm.Locals) : Prop :=
  ∀ {fvar : Lean.FVarId} {value : Value}, lookup source fvar = some value →
    ∃ index kind physical,
      findFVar? bindings fvar = some index ∧
      bindings[index]?.map Prod.snd = some kind ∧
      target.get index = some physical ∧
      PhysicalValueRel witness kind physical value

theorem PhysicalValueRel.witnessExtension
    {before after : RefinementWitness} (extension : before.Extends after)
    {kind : AbiKind} {physical : Wasm.Value} {semantic : Value}
    (related : PhysicalValueRel before kind physical semantic) :
    PhysicalValueRel after kind physical semantic := by
  cases related with
  | word32 valueRelated =>
      exact .word32 (valueRelated.witnessExtension extension)
  | word64 valueRelated =>
      exact .word64 (valueRelated.witnessExtension extension)
  | float32Bits valueRelated =>
      exact .float32Bits (valueRelated.witnessExtension extension)
  | float64Bits valueRelated =>
      exact .float64Bits (valueRelated.witnessExtension extension)

/-- A concrete local write binds its semantic result while preserving every
old binding under monotone proof-witness growth. -/
theorem EnvLocalsRelated.bind
    {before after : RefinementWitness}
    {bindings : List (Lean.FVarId × AbiKind)} {source : Env}
    {target updated : Wasm.Locals} {result : Lean.FVarId}
    {resultIndex : Nat} {kind : AbiKind} {semantic : Value}
    {physical : Wasm.Value}
    (related : EnvLocalsRelated before bindings source target)
    (resultFound : findFVar? bindings result = some resultIndex)
    (kindAt : bindings[resultIndex]?.map Prod.snd = some kind)
    (localUpdate : FirTalos.Correctness.LocalUpdate target updated resultIndex
      physical)
    (extension : before.Extends after)
    (physicalRelated : PhysicalValueRel after kind physical semantic) :
    EnvLocalsRelated after bindings
      (Fir.LeanIR.Impure.bind source result semantic) updated := by
  intro fvar value sourceLookup
  by_cases sameName : (result.name == fvar.name) = true
  · have names : result.name = fvar.name := LawfulBEq.eq_of_beq sameName
    have sameFind := findFVar?_eq_of_name_eq bindings names
    have found : findFVar? bindings fvar = some resultIndex := by
      rw [← sameFind]
      exact resultFound
    have valueEq : value = semantic := by
      simpa [Fir.LeanIR.Impure.bind, lookup, sameName] using sourceLookup.symm
    subst value
    exact ⟨resultIndex, kind, physical, found, kindAt, localUpdate.1,
      physicalRelated⟩
  · have oldLookup : lookup source fvar = some value := by
      simpa [Fir.LeanIR.Impure.bind, lookup, sameName] using sourceLookup
    rcases related oldLookup with
      ⟨index, oldKind, oldPhysical, found, oldKindAt, targetLookup,
        oldRelated⟩
    have names : result.name ≠ fvar.name := by
      intro equal
      apply sameName
      rw [equal]
      exact beq_self_eq_true _
    have different := findFVar?_ne_of_name_ne bindings names resultFound found
    exact ⟨index, oldKind, oldPhysical, found, oldKindAt,
      (localUpdate.2 different.symm).trans targetLookup,
      oldRelated.witnessExtension extension⟩

/-- Failures at the concrete Talos host boundary retain either the exact W6
runtime trap or a Wasm ABI-shape error detected before the operation runs. -/
inductive HostFailure where
  | runtime (failure : ConcreteTrap)
  | arityMismatch (expected actual : Nat)
  | laneMismatch (index : Nat) (expected : Fir.Wasm.ValueType)
  deriving Inhabited, BEq, Repr

/-- Host-owned concrete linear memory and its latest structured failure. The
semantic runtime is deliberately absent: it occurs only in the refinement
relation and cannot be consulted by executable concrete host functions. -/
structure Host where
  runtime : ConcreteRuntimeState := {}
  failure? : Option HostFailure := none
  deriving Inhabited

def clearFailure (store : Wasm.Store Host) : Wasm.Store Host :=
  { store with host := { store.host with failure? := none } }

def trap (store : Wasm.Store Host) (failure : HostFailure) :
    Wasm.HostResult Host :=
  .Trap { store with host := { store.host with failure? := some failure } }
    s!"FIR concrete host failure: {repr failure}"

/-- Executable concrete implementation of the W2 `getTag` import. It accepts
one wasm32 object word, runs the checked W6 decoder over host-owned linear
memory, and returns the low i32 tag lane used by generated case tests. -/
def getTagStep (store : Wasm.Store Host) (args : List Wasm.Value) :
    Wasm.HostResult Host :=
  let store := clearFailure store
  match args with
  | [.i32 bits] =>
      match readTag store.host.runtime.heap (Word32.ofUInt32 bits) with
      | .ok tag => .Return [.i32 (UInt32.ofNat tag.toNat)] store
      | .error failure => trap store (.runtime failure.toTrap)
  | [_] => trap store (.laneMismatch 0 .i32)
  | args => trap store (.arityMismatch 1 args.length)

def getTagFn : Wasm.HostFn Host := {
  params := [.i32]
  results := [.i32]
  invoke := getTagStep }

/-- Exact proof-facing contract for the executable concrete tag host. -/
def getTagContract : Wasm.HostContract Host :=
  fun initial args result => result = getTagStep initial args

theorem getTagFn_satisfies_contract (initial args) :
    getTagContract initial args (getTagFn.invoke initial args) := by
  rfl

/-- Executable concrete implementation of an object-field projection import.
The field index and result ABI are frozen in the import; the runtime reads one
full semantic slot and returns its exact wasm32 word. -/
def objectProjStep (index : Nat) (store : Wasm.Store Host)
    (args : List Wasm.Value) : Wasm.HostResult Host :=
  let store := clearFailure store
  match args with
  | [.i32 bits] =>
      match readObjectField store.host.runtime.heap (Word32.ofUInt32 bits) index with
      | .ok word => .Return [.i32 (UInt32.ofNat word.value)] store
      | .error failure => trap store (.runtime failure.toTrap)
  | [_] => trap store (.laneMismatch 0 .i32)
  | args => trap store (.arityMismatch 1 args.length)

def objectProjFn (index : Nat) : Wasm.HostFn Host := {
  params := [.i32]
  results := [.i32]
  invoke := objectProjStep index }

def objectProjContract (index : Nat) : Wasm.HostContract Host :=
  fun initial args result => result = objectProjStep index initial args

theorem objectProjFn_satisfies_contract (index initial args) :
    objectProjContract index initial args
      ((objectProjFn index).invoke initial args) := by
  rfl

/-- Successful semantic projection identifies a mapped constructor and the
checked concrete read returns a field related at its static descriptor kind. -/
theorem ConcreteRuntimeRel.readObjectField_refines
    {concrete : ConcreteRuntimeState} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32} {sourceObject value : Value}
    {info : Lean.Compiler.LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {index : Nat} {kind : AbiKind}
    (related : ConcreteRuntimeRel concrete witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (descriptor : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (kindAt : fieldKinds[index]? = some kind)
    (projected : getObjectField runtime sourceObject index = .ok value) :
    ∃ word, readObjectField concrete.heap objectWord index = .ok word ∧
      ValueRel witness kind (.word32 word) value := by
  cases objectRelated with
  | tobject objectRelated =>
      cases objectRelated with
      | heap mapped =>
          cases mapped with
          | mapped found =>
              exact related.heap.readObjectField_refines found descriptor kindAt
                projected
      | tagged taggedRelated =>
          cases taggedRelated <;>
            simp [getObjectField, getConstructor, Bind.bind, Except.bind] at projected

theorem objectProjStep_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32} {sourceObject value : Value}
    {info : Lean.Compiler.LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {index : Nat} {kind : AbiKind}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (descriptor : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (kindAt : fieldKinds[index]? = some kind)
    (projected : getObjectField runtime sourceObject index = .ok value) :
    ∃ word,
      readObjectField initial.host.runtime.heap objectWord index = .ok word ∧
      objectProjStep index initial [.i32 (UInt32.ofNat objectWord.value)] =
        .Return [.i32 (UInt32.ofNat word.value)] (clearFailure initial) ∧
      ValueRel witness kind (.word32 word) value := by
  obtain ⟨word, read, valueRelated⟩ :=
    FirTalos.Concrete.ConcreteRuntimeRel.readObjectField_refines runtimeRelated
      objectRelated descriptor kindAt projected
  refine ⟨word, read, ?_, valueRelated⟩
  simp [objectProjStep, clearFailure, read]

/-- The complete concrete state relation used by W6.6 composition: host-owned
memory/effects refine FIR runtime state, the failure channel is clear, and
compiler-assigned locals contain related W6 lanes. -/
def StateRelated (sourceFunction : Fir.Wasm.Function)
    (sourceRuntime : RuntimeState) (sourceEnv : Env)
    (targetStore : Wasm.Store Host) (targetLocals : Wasm.Locals)
    (witness : RefinementWitness) : Prop :=
  ConcreteRuntimeRel targetStore.host.runtime witness sourceRuntime ∧
    targetStore.host.failure? = none ∧
    EnvLocalsRelated witness (functionBindings sourceFunction) sourceEnv
      targetLocals

theorem StateRelated.clearFailure
    {sourceFunction : Fir.Wasm.Function} {sourceRuntime : RuntimeState}
    {sourceEnv : Env} {targetStore : Wasm.Store Host}
    {targetLocals : Wasm.Locals} {witness : RefinementWitness}
    (related : StateRelated sourceFunction sourceRuntime sourceEnv
      targetStore targetLocals witness) :
    clearFailure targetStore = targetStore := by
  rcases targetStore with
    ⟨globals, mem, extraMems, dataSegments, tables, elementSegments, exns,
      gcHeap, host⟩
  rcases host with ⟨runtime, failure⟩
  have failureEq : failure = none := related.2.1
  subst failure
  rfl

/-- A successful read-only concrete operation may bind its result without
changing the runtime witness. -/
theorem StateRelated.bindWord32
    {sourceFunction : Fir.Wasm.Function} {sourceRuntime : RuntimeState}
    {sourceEnv : Env} {targetStore : Wasm.Store Host}
    {targetLocals updated : Wasm.Locals} {witness : RefinementWitness}
    {result : Lean.FVarId} {resultIndex : Nat} {kind : AbiKind}
    {word : Word32} {semantic : Value}
    (related : StateRelated sourceFunction sourceRuntime sourceEnv targetStore
      targetLocals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) result = some resultIndex)
    (kindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some kind)
    (valueRelated : ValueRel witness kind (.word32 word) semantic)
    (targetSet :
      targetLocals.set? resultIndex (.i32 (UInt32.ofNat word.value)) =
        some updated) :
    StateRelated sourceFunction sourceRuntime (bind sourceEnv result semantic)
      (FirTalos.Concrete.clearFailure targetStore) updated witness := by
  rw [related.clearFailure]
  exact ⟨related.1, related.2.1,
    EnvLocalsRelated.bind related.2.2 resultFound kindAt
      (localUpdate_of_set? targetSet) (.refl witness) (.word32 valueRelated)⟩

/-- W6 proof judgment for generated code over the concrete host. It mirrors
W5's structural boundary while indexing both the target runtime and locals by
the representation witness. -/
def CodeWP (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module) (sourceFunction : Fir.Wasm.Function)
    (labels : List Lean.FVarId) (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host)
    (sourceRuntime : RuntimeState) (sourceEnv : Env)
    (code : Lean.Compiler.LCNF.Code .impure) (target : Wasm.Program)
    (targetStore : Wasm.Store Host) (targetLocals : Wasm.Locals)
    (witness : RefinementWitness) (tail : List Wasm.Value)
    (Q : Wasm.Assertion Host) : Prop :=
  FirTalos.Correctness.CodeAdapted context sourceModule sourceFunction labels
      code target ∧
    StateRelated sourceFunction sourceRuntime sourceEnv targetStore targetLocals
      witness ∧
    Wasm.wp module target Q targetStore
      { targetLocals with values := tail } hostEnv

/-- One direct source `let` step paired with its concrete host/local update.
Separate witnesses allow later allocation operations to grow ghost metadata. -/
def LetStepSimulates (context : Fir.Wasm.Context)
    (sourceFunction : Fir.Wasm.Function) (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host)
    (decl : Lean.Compiler.LCNF.LetDecl .impure) (targetValue : Wasm.Program)
    (sourceRuntime nextRuntime : RuntimeState) (sourceEnv : Env)
    (sourceValue : Value)
    (targetStore nextStore : Wasm.Store Host)
    (targetLocals nextLocals : Wasm.Locals) (resultIndex : Nat)
    (witness nextWitness : RefinementWitness) : Prop :=
  FirTalos.Correctness.SourceLetResult context sourceRuntime sourceEnv decl
      nextRuntime sourceValue ∧
    StateRelated sourceFunction sourceRuntime sourceEnv targetStore targetLocals
      witness ∧
    StateRelated sourceFunction nextRuntime
      (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals nextWitness ∧
    ∀ (rest : Wasm.Program) (Q : Wasm.Assertion Host)
        (tail : List Wasm.Value),
      Wasm.wp module rest Q nextStore { nextLocals with values := tail } hostEnv →
      Wasm.wp module (targetValue ++ .localSet resultIndex :: rest) Q
        targetStore { targetLocals with values := tail } hostEnv

/-- A successful concrete tag read is the exact executable realization of the
semantic `getTag` result whenever the case tag satisfies the lowerer's checked
i32 range gate. -/
theorem getTagStep_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {semanticRuntime : RuntimeState} {word : Word32} {value : Value}
    {tag : Nat}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness semanticRuntime)
    (valueRelated : ValueRel witness .tobject (.word32 word) value)
    (tagged : getTag semanticRuntime value = .ok tag)
    (fits : tag < UInt32.size) :
    getTagStep initial [.i32 (UInt32.ofNat word.value)] =
      .Return [.i32 (UInt32.ofNat tag)] (clearFailure initial) := by
  have read := runtimeRelated.heap.readTag_tobject_refines valueRelated tagged
  have fits64 : tag < UInt64.size := by
    have sizeLe : UInt32.size ≤ UInt64.size := by native_decide
    exact lt_of_lt_of_le fits sizeLe
  have tagToNat : (UInt64.ofNat tag).toNat = tag :=
    UInt64.toNat_ofNat_of_lt' fits64
  unfold getTagStep
  simp only [clearFailure]
  rw [Word32.ofUInt32_ofNat_value, read]
  simp [tagToNat]

/-- Generic exact-contract lifting used by every W6.6 concrete host operation.
It is independent of FIR's semantic host type and therefore composes Talos WP
directly with a concrete resolver. -/
theorem wp_exact_host_call_of_return
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {spec : Wasm.HostSpec host} {id : Nat} {imp : Wasm.ImportDecl}
    {step : Wasm.Store host → List Wasm.Value → Wasm.HostResult host}
    {rest : Wasm.Program} {Q : Wasm.Assertion host}
    {initial final : Wasm.Store host} {locals : Wasm.Locals}
    {physicalArgs results : List Wasm.Value}
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some
      (fun initial args result => result = step initial args))
    (hArgs :
      (locals.values.take imp.params.length).reverse = physicalArgs)
    (operation : step initial physicalArgs = .Return results final)
    (continued :
      Wasm.wp module rest Q final
        { locals with values := results.take imp.results.length ++
            locals.values.drop imp.params.length } env) :
    Wasm.wp module (.call id :: rest) Q initial locals env := by
  apply Wasm.wp_call_host_contract hImp hSat hi hContract
  · intro actualResults actualFinal contract
    change Wasm.HostResult.Return actualResults actualFinal =
      step initial
        (locals.values.take imp.params.length).reverse at contract
    rw [hArgs, operation] at contract
    injection contract with resultsEq finalEq
    subst resultsEq
    subst finalEq
    exact continued
  · intro trapped message contract
    change Wasm.HostResult.Trap trapped message =
      step initial
        (locals.values.take imp.params.length).reverse at contract
    rw [hArgs, operation] at contract
    contradiction

/-- Host-polymorphic local-write rule used by concrete result-producing
imports. The semantic W5 rule is specialized to `RuntimeHost`; this is the
same Talos instruction fact over the W6 host. -/
theorem wp_localSet_of_set
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {rest : Wasm.Program} {Q : Wasm.Assertion host}
    {store : Wasm.Store host} {locals updated : Wasm.Locals}
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

/-- Concrete-host WP for the generated object projection and destination
write. Both the input and result are physical wasm32 words; their meanings are
established only by `ValueRel` and the constructor descriptor. -/
theorem wp_objectProjection_let
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion Host}
    {initial : Wasm.Store Host} {locals : Wasm.Locals}
    {objectIndex resultIndex : Nat} {objectWord : Word32}
    {witness : RefinementWitness} {runtime : RuntimeState}
    {sourceObject value : Value} {info : Lean.Compiler.LCNF.CtorInfo}
    {fieldKinds : Array AbiKind} {index : Nat} {kind : AbiKind}
    (tail : List Wasm.Value)
    (hObject :
      locals.get objectIndex = some (.i32 (UInt32.ofNat objectWord.value)))
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (objectProjContract index))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (descriptor : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (fieldKind : fieldKinds[index]? = some kind)
    (projected : getObjectField runtime sourceObject index = .ok value)
    (hSet :
      ∀ word,
        readObjectField initial.host.runtime.heap objectWord index = .ok word →
        ValueRel witness kind (.word32 word) value →
        ∃ nextLocals,
          locals.set? resultIndex (.i32 (UInt32.ofNat word.value)) =
            some nextLocals ∧
          Wasm.wp module rest Q (clearFailure initial)
            { nextLocals with values := tail } env) :
    Wasm.wp module
      (.localGet objectIndex :: .call id :: .localSet resultIndex :: rest)
      Q initial { locals with values := tail } env := by
  obtain ⟨word, read, operation, valueRelated⟩ :=
    objectProjStep_of_refines runtimeRelated objectRelated descriptor fieldKind
      projected
  obtain ⟨nextLocals, targetSet, continued⟩ :=
    hSet word read valueRelated
  have hObjectTail :
      ({ locals with values := tail } : Wasm.Locals).get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)) := by
    simpa [Wasm.Locals.get] using hObject
  rw [Wasm.wp_localGet_cons, hObjectTail]
  apply wp_exact_host_call_of_return
    (step := objectProjStep index)
    (physicalArgs := [.i32 (UInt32.ofNat objectWord.value)])
    (results := [.i32 (UInt32.ofNat word.value)])
    hImp hSat hi hContract
  · simp [hParams]
  · exact operation
  · simpa [hParams, hResults] using
      FirTalos.Concrete.wp_localSet_of_set (host := Host) targetSet continued

/-- Object-projection instance of the concrete direct-`let` boundary. It
proves the source interpreter step, the result-local refinement, and a Talos
WP transformer for the generated read/call/write prefix. -/
theorem letStepSimulates_objectProjection
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure} {sourceEnv : Env}
    {index : Nat} {objectId : Lean.FVarId}
    {initial : Wasm.Store Host} {locals updated : Wasm.Locals}
    {objectIndex resultIndex : Nat} {objectWord resultWord : Word32}
    {sourceObject value : Value} {resultKind : AbiKind}
    {sourceRuntime : RuntimeState}
    {witness : RefinementWitness} {info : Lean.Compiler.LCNF.CtorInfo}
    {fieldKinds : Array AbiKind}
    (valueEq : decl.value = .oproj index objectId)
    (sourceLookup : lookup sourceEnv objectId = some sourceObject)
    (projected :
      getObjectField sourceRuntime sourceObject index = .ok value)
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some resultKind)
    (hObject :
      locals.get objectIndex = some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (descriptor : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (fieldKind : fieldKinds[index]? = some resultKind)
    (concreteRead :
      readObjectField initial.host.runtime.heap objectWord index = .ok resultWord)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (objectProjContract index))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (targetSet :
      locals.set? resultIndex (.i32 (UInt32.ofNat resultWord.value)) =
        some updated) :
    LetStepSimulates context sourceFunction module hostEnv decl
      [.localGet objectIndex, .call id]
      sourceRuntime sourceRuntime sourceEnv value initial
      (clearFailure initial) locals updated resultIndex witness witness := by
  obtain ⟨actualWord, actualRead, valueRelated⟩ :=
    FirTalos.Concrete.ConcreteRuntimeRel.readObjectField_refines
      initialRelated.1 objectRelated descriptor fieldKind projected
  rw [concreteRead] at actualRead
  have wordEq : resultWord = actualWord := Except.ok.inj actualRead
  subst actualWord
  refine ⟨?_, initialRelated,
    initialRelated.bindWord32 resultFound resultKindAt valueRelated targetSet,
    ?_⟩
  · unfold FirTalos.Correctness.SourceLetResult
    simp [evalLetValue, valueEq]
    have objectLookup : lookupValue sourceEnv objectId = .ok sourceObject := by
      simp [lookupValue, sourceLookup]
    rw [objectLookup]
    change ((fun projectedValue : Value =>
      (sourceRuntime, LetAction.value projectedValue)) <$>
        getObjectField sourceRuntime sourceObject index) =
      .ok (sourceRuntime, .value value)
    rw [projected]
    rfl
  · intro rest Q tail continued
    apply wp_objectProjection_let tail hObject hImp hSat hi hContract hParams
      hResults initialRelated.1 objectRelated descriptor fieldKind projected
    intro word read related
    rw [concreteRead] at read
    have equal : resultWord = word := Except.ok.inj read
    subst word
    exact ⟨updated, targetSet, continued⟩

/-- W6.6 composition for the actual object-projection code emitted by the FIR
lowerer and Talos adapter, followed by any already-composed continuation. -/
theorem codeWP_objectProjection_let
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure} {sourceEnv : Env}
    {index : Nat} {objectId : Lean.FVarId}
    {initial : Wasm.Store Host} {locals updated : Wasm.Locals}
    {objectIndex resultIndex : Nat} {objectWord resultWord : Word32}
    {sourceObject value : Value} {resultKind : AbiKind}
    {sourceRuntime : RuntimeState}
    {witness : RefinementWitness} {info : Lean.Compiler.LCNF.CtorInfo}
    {fieldKinds : Array AbiKind} {targetRest : Wasm.Program}
    {tail : List Wasm.Value} {Q : Wasm.Assertion Host}
    (valueEq : decl.value = .oproj index objectId)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.localGet objectId,
          .call (.runtime (.objectProj index resultKind))])
    (objectFound :
      findFVar? (functionBindings sourceFunction) objectId = some objectIndex)
    (callFound :
      callIndex? sourceModule (.runtime (.objectProj index resultKind)) = some id)
    (sourceLookup : lookup sourceEnv objectId = some sourceObject)
    (projected :
      getObjectField sourceRuntime sourceObject index = .ok value)
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some resultKind)
    (hObject :
      locals.get objectIndex = some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (descriptor : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (fieldKind : fieldKinds[index]? = some resultKind)
    (concreteRead :
      readObjectField initial.host.runtime.heap objectWord index = .ok resultWord)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (objectProjContract index))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (targetSet :
      locals.set? resultIndex (.i32 (UInt32.ofNat resultWord.value)) =
        some updated)
    (continued :
      CodeWP context sourceModule sourceFunction labels module hostEnv
        sourceRuntime (bind sourceEnv decl.fvarId value)
        continuation targetRest (clearFailure initial) updated witness tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv (.let decl continuation)
      (.localGet objectIndex :: .call id :: .localSet resultIndex :: targetRest)
      initial locals witness tail Q := by
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          [.localGet objectId,
            .call (.runtime (.objectProj index resultKind))] =
        .ok [.localGet objectIndex, .call id] := by
    have objectFound' :
        findFVar? (sourceFunction.params.toList ++ sourceFunction.locals.toList)
          objectId = some objectIndex := by
      simpa [functionBindings] using objectFound
    simp [instructions, instruction, objectFound', callFound]
    rfl
  have step := letStepSimulates_objectProjection (context := context)
    valueEq sourceLookup projected initialRelated resultFound resultKindAt
    hObject objectRelated descriptor fieldKind concreteRead hImp hSat hi
    hContract hParams hResults targetSet
  rcases step with ⟨_, stepInitial, _, stepWP⟩
  rcases continued with ⟨continuationAdapted, _, continuedWP⟩
  refine ⟨codeAdapted_let valueCompiled valueAdapted resultFound
      continuationAdapted, stepInitial, ?_⟩
  exact stepWP targetRest Q tail continuedWP

/-- Host-polymorphic form of W5's exact i32 compare/branch stack rule. W6
needs the same Wasm instruction fact for a concrete host state. -/
theorem wp_i32Eq_ifElse
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {thenBody elseBody rest : Wasm.Program} {Q : Wasm.Assertion host}
    {store : Wasm.Store host} {locals : Wasm.Locals}
    (actual expected : UInt32)
    (hBody :
      Wasm.wp module (if actual = expected then thenBody else elseBody)
        (fun continuation => match continuation with
          | .Fallthrough nextStore nextLocals =>
              Wasm.wp module rest Q nextStore
                { nextLocals with values := locals.values } env
          | .Break 0 nextStore nextLocals =>
              Wasm.wp module rest Q nextStore
                { nextLocals with values := locals.values } env
          | .Break (level + 1) nextStore nextLocals =>
              Q (.Break level nextStore nextLocals)
          | other => Q other)
        store locals env) :
    Wasm.wp module
      (.const expected :: .eq :: .iff 0 0 thenBody elseBody :: rest)
      Q store { locals with values := .i32 actual :: locals.values } env := by
  rw [Wasm.wp_const_cons, Wasm.wp_eq_cons]
  apply Wasm.wp_iff_cons
    (c := if actual = expected then 1 else 0) (vs := locals.values) rfl
  have localsSelf : { locals with values := locals.values } = locals := by
    cases locals
    rfl
  rw [localsSelf]
  convert hBody using 1
  all_goals simp
  all_goals
    funext continuation
    cases continuation with
    | Break level nextStore nextLocals =>
        cases level <;> rfl
    | _ => rfl

/-- Concrete-host WP for the exact tag-test instruction sequence emitted by
the lowerer. The source and concrete object representations meet only through
`ValueRel`; no opaque semantic handle is allocated or decoded. -/
theorem wp_getTag_case_test
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {thenBody elseBody rest : Wasm.Program} {Q : Wasm.Assertion Host}
    {initial : Wasm.Store Host} {locals : Wasm.Locals}
    {localIndex : Nat} {word : Word32}
    {witness : RefinementWitness} {semanticRuntime : RuntimeState}
    {sourceObject : Value} {actualTag expectedTag : Nat}
    (hLocal :
      locals.get localIndex = some (.i32 (UInt32.ofNat word.value)))
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some getTagContract)
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness semanticRuntime)
    (valueRelated : ValueRel witness .tobject (.word32 word) sourceObject)
    (tagged : getTag semanticRuntime sourceObject = .ok actualTag)
    (actualFits : actualTag < UInt32.size)
    (expectedFits : expectedTag < UInt32.size)
    (hBody :
      Wasm.wp module
        (if actualTag = expectedTag then thenBody else elseBody)
        (fun continuation => match continuation with
          | .Fallthrough nextStore nextLocals =>
              Wasm.wp module rest Q nextStore
                { nextLocals with values := locals.values } env
          | .Break 0 nextStore nextLocals =>
              Wasm.wp module rest Q nextStore
                { nextLocals with values := locals.values } env
          | .Break (level + 1) nextStore nextLocals =>
              Q (.Break level nextStore nextLocals)
          | other => Q other)
        (clearFailure initial) locals env) :
    Wasm.wp module
      (.localGet localIndex :: .call id ::
        .const (UInt32.ofNat expectedTag) :: .eq ::
        .iff 0 0 thenBody elseBody :: rest)
      Q initial locals env := by
  rw [Wasm.wp_localGet_cons, hLocal]
  apply wp_exact_host_call_of_return
    (step := getTagStep)
    (physicalArgs := [.i32 (UInt32.ofNat word.value)])
    (results := [.i32 (UInt32.ofNat actualTag)])
    hImp hSat hi hContract
  · simp [hParams]
  · exact getTagStep_of_refines runtimeRelated valueRelated tagged actualFits
  · simpa [hParams, hResults] using
      FirTalos.Concrete.wp_i32Eq_ifElse (host := Host) (locals := locals)
        (store := clearFailure initial) (UInt32.ofNat actualTag)
        (UInt32.ofNat expectedTag)
        (by
          by_cases equal : actualTag = expectedTag
          · have physicalEqual :
                UInt32.ofNat actualTag = UInt32.ofNat expectedTag :=
              congrArg UInt32.ofNat equal
            rw [if_pos physicalEqual]
            rw [if_pos equal] at hBody
            convert hBody using 1
            funext continuation
            cases continuation with
            | Break level nextStore nextLocals =>
                cases level <;> (apply propext; rfl)
            | _ => apply propext; rfl
          · have physicalDifferent :
                UInt32.ofNat actualTag ≠ UInt32.ofNat expectedTag := by
              intro physicalEqual
              exact equal <|
                (constructorTag_i32_eq_iff actualFits expectedFits).mp
                  physicalEqual
            rw [if_neg physicalDifferent]
            rw [if_neg equal] at hBody
            convert hBody using 1
            funext continuation
            cases continuation with
            | Break level nextStore nextLocals =>
                cases level <;> (apply propext; rfl)
            | _ => apply propext; rfl)

/-- Concrete-host analogue of W5's case resumption assertion. -/
def CaseResumePost (module : Wasm.Module) (hostEnv : Wasm.HostEnv Host)
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

/-- W6.6 proof boundary for a constructor-case suffix: the actual compiler and
adapter witness is paired with concrete runtime/local refinement and Talos WP. -/
def CaseChainWP (context : Fir.Wasm.Context)
    (sourceModule : Fir.Wasm.Module) (sourceFunction : Fir.Wasm.Function)
    (labels : List Lean.FVarId) (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host)
    (sourceRuntime : RuntimeState) (sourceEnv : Env)
    (discr : Lean.FVarId) (alts : List (Lean.Compiler.LCNF.Alt .impure))
    (fallback : List Fir.Wasm.Instruction) (target : Wasm.Program)
    (targetStore : Wasm.Store Host) (targetLocals : Wasm.Locals)
    (witness : RefinementWitness) (tail : List Wasm.Value)
    (Q : Wasm.Assertion Host) : Prop :=
  FirTalos.Correctness.CaseChainAdapted context sourceModule sourceFunction
      labels discr alts fallback target ∧
    StateRelated sourceFunction sourceRuntime sourceEnv targetStore targetLocals
      witness ∧
    Wasm.wp module target Q targetStore
      { targetLocals with values := tail } hostEnv

/-- First end-to-end W6.6 composition rule. It reuses the W5 compiler/adapter
theorem but executes the generated object-case test against the concrete W6
host, deriving the exact physical discriminator word from related source and
target locals. -/
theorem caseChainWP_constructor
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {discr : Lean.FVarId} {info : Lean.Compiler.LCNF.CtorInfo}
    {code : Lean.Compiler.LCNF.Code .impure}
    {alts : List (Lean.Compiler.LCNF.Alt .impure)}
    {fallback : List Fir.Wasm.Instruction}
    {thenTarget elseTarget : Wasm.Program}
    {initial : Wasm.Store Host} {locals : Wasm.Locals}
    {witness : RefinementWitness} {tail : List Wasm.Value}
    {Q : Wasm.Assertion Host}
    {discrIndex getTagIndex : Nat} {imp : Wasm.ImportDecl}
    {sourceObject : Value} {actualTag : Nat}
    (modeEq : Fir.Wasm.caseDiscriminatorMode context discr = .objectTag)
    (fits : Fir.Wasm.constructorTagFitsI32 info = true)
    (thenAdapted :
      FirTalos.Correctness.CodeAdapted context sourceModule sourceFunction
        labels code thenTarget)
    (elseAdapted :
      FirTalos.Correctness.CaseChainAdapted context sourceModule sourceFunction
        labels discr alts fallback elseTarget)
    (discrFound :
      findFVar? (functionBindings sourceFunction) discr = some discrIndex)
    (discrKind :
      (functionBindings sourceFunction)[discrIndex]?.map Prod.snd =
        some .tobject)
    (getTagFound :
      callIndex? sourceModule (.runtime .getTag) = some getTagIndex)
    (stateRelated :
      StateRelated sourceFunction sourceRuntime sourceEnv initial locals witness)
    (sourceLookup : lookup sourceEnv discr = some sourceObject)
    (hImp : module.imports[getTagIndex]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : getTagIndex < module.imports.length)
    (hContract : spec.contracts[getTagIndex]? = some getTagContract)
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (tagged : getTag sourceRuntime sourceObject = .ok actualTag)
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
      initial locals witness tail Q := by
  obtain ⟨index, kind, physical, found, kindAt, localValue,
      physicalRelated⟩ := stateRelated.2.2 sourceLookup
  rw [discrFound] at found
  have indexEq := Option.some.inj found
  subst index
  rw [discrKind] at kindAt
  have kindEq := Option.some.inj kindAt
  subst kind
  refine ⟨caseChainAdapted_constructor modeEq fits thenAdapted elseAdapted
    discrFound getTagFound, stateRelated, ?_⟩
  cases physicalRelated with
  | word32 valueRelated =>
      apply wp_getTag_case_test
        (spec := spec) (rest := [])
        (locals := { locals with values := tail })
        (by simpa [Wasm.Locals.get] using localValue)
        hImp hSat hi hContract hParams hResults stateRelated.1 valueRelated
          tagged actualFits expectedFits
      rw [stateRelated.clearFailure]
      exact selectedWP
  | word64 valueRelated => cases valueRelated
  | float32Bits valueRelated => cases valueRelated
  | float64Bits valueRelated => cases valueRelated

end FirTalos.Concrete
