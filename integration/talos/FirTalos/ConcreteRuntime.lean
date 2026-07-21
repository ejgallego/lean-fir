import FirTalos.Correctness.Semantics
import Fir.Wasm.Concrete
import Interpreter.Wasm.Spec.Termination

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

/-- Unified natural-literal refinement assembled after both the natural and
promoted-tag proof modules are available. -/
theorem allocateNatural_liveHeapRel_extends
    (state result : MemoryState) (witness : RefinementWitness)
    (runtime : RuntimeState) (value : Nat) (word : Word32)
    (related : LiveHeapRel state witness runtime)
    (allocated : allocateNatural state value = .ok (result, word)) :
    ∃ nextWitness,
      witness.Extends nextWitness ∧
      LiveHeapRel result nextWitness (literal runtime (.nat value)).1 ∧
      ValueRel nextWitness .tobject (.word32 word)
        (literal runtime (.nat value)).2 := by
  by_cases small : value ≤ maxTaggedPayload
  · have encoded : encodeTagged state (UInt64.ofNat value) =
        .ok (result, word) := by
      unfold allocateNatural at allocated
      rw [if_pos small] at allocated
      exact allocated
    obtain ⟨nextWitness, extension, heapRelated, valueRelated⟩ :=
      encodeTagged_liveHeapRel_extends state result witness runtime
        (UInt64.ofNat value) word related encoded
    have literalEq : literal runtime (.nat value) =
        (runtime, .object (.tagged (UInt64.ofNat value))) := by
      simp [literal, small]
    rw [literalEq]
    exact ⟨nextWitness, extension, heapRelated, valueRelated⟩
  · have large : maxTaggedPayload < value := Nat.lt_of_not_ge small
    obtain ⟨_, _, _, objectAllocation, _, _⟩ :=
      allocateNatural_heap_decompose state result value word large allocated
    have freshAddress := related.frontier.allocateObject_address objectAllocation
    have locationFresh : witness.locations.lookup? runtime.nextLocation = none := by
      cases found : witness.locations.lookup? runtime.nextLocation with
      | none => rfl
      | some oldAddress =>
          exfalso
          obtain ⟨cell, semanticFound, _⟩ :=
            related.concreteToSemantic runtime.nextLocation oldAddress found
          have beforeNext :=
            related.locationsBeforeNext runtime.nextLocation cell semanticFound
          exact (Nat.lt_irrefl runtime.nextLocation) beforeNext
    have descriptorFresh : ∀ old descriptor,
        witness.descriptors.lookup? old = some descriptor →
        word.value ≠ old.value := by
      intro old descriptor found equal
      have owned := related.descriptorsOwned old descriptor found
      simp [headerBytes] at owned
      omega
    have extension := witness.bindNatural_extends runtime.nextLocation word value
      locationFresh descriptorFresh
    have refined := allocateNatural_heap_liveHeapRel state result witness runtime
      value word related large allocated
    rw [semanticLiteral_natural_heap_eq runtime value large]
    exact ⟨witness.bindNatural runtime.nextLocation word value, extension,
      refined.1, refined.2⟩

theorem ConcreteRuntimeRel.allocateNatural
    {concrete : ConcreteRuntimeState} {witness : RefinementWitness}
    {runtime : RuntimeState} {result : MemoryState} {value : Nat}
    {word : Word32}
    (related : ConcreteRuntimeRel concrete witness runtime)
    (allocated : allocateNatural concrete.heap value = .ok (result, word)) :
    ∃ nextWitness,
      witness.Extends nextWitness ∧
      ConcreteRuntimeRel { concrete with heap := result } nextWitness
        (literal runtime (.nat value)).1 ∧
      ValueRel nextWitness .tobject (.word32 word)
        (literal runtime (.nat value)).2 := by
  obtain ⟨nextWitness, extension, heapRelated, valueRelated⟩ :=
    allocateNatural_liveHeapRel_extends concrete.heap result witness runtime
      value word related.heap allocated
  have auxiliary :
      (literal runtime (.nat value)).1.globals = runtime.globals ∧
      (literal runtime (.nat value)).1.world = runtime.world ∧
      (literal runtime (.nat value)).1.trace = runtime.trace := by
    by_cases small : value ≤ maxTaggedPayload
    · simp [literal, small]
    · have large : maxTaggedPayload < value := Nat.lt_of_not_ge small
      rw [semanticLiteral_natural_heap_eq runtime value large]
      simp [semanticNaturalResult]
  refine ⟨nextWitness, extension, ?_, valueRelated⟩
  exact {
    heap := heapRelated
    globals := by
      rw [auxiliary.1]
      exact related.globals.witnessExtension extension
    world := by
      rw [auxiliary.2.1]
      exact related.world
    trace := by
      rw [auxiliary.2.2]
      exact related.trace.witnessExtension extension }

/-- Empty constructor allocation preserves semantic runtime state while its
concrete tagged result may extend the heap with a promoted-tag object. -/
theorem ConcreteRuntimeRel.allocateConstructorEmpty
    {concrete : ConcreteRuntimeState} {witness : RefinementWitness}
    {runtime : RuntimeState} {result : MemoryState}
    {info : Lean.Compiler.LCNF.CtorInfo} {fields : Array Word32}
    {semanticFields : Array Value} {word : Word32}
    (related : ConcreteRuntimeRel concrete witness runtime)
    (arity : fields.size = info.size)
    (semanticArity : semanticFields.size = info.size)
    (empty : (info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0)
    (tagFits : info.cidx < UInt32.size)
    (allocated : allocateConstructor concrete.heap info fields =
      .ok (result, word)) :
    ∃ nextWitness,
      witness.Extends nextWitness ∧
      ConcreteRuntimeRel { concrete with heap := result } nextWitness runtime ∧
      ValueRel nextWitness .tagged (.word32 word)
        (.object (.tagged (UInt64.ofNat info.cidx))) ∧
      allocCtor runtime info semanticFields =
        .ok (runtime, .object (.tagged (UInt64.ofNat info.cidx))) := by
  obtain ⟨nextWitness, extension, heapRelated, valueRelated, semanticStep⟩ :=
    allocateConstructor_empty_liveHeapRel_extends concrete.heap result witness
      runtime info fields semanticFields word related.heap arity semanticArity
      empty tagFits allocated
  refine ⟨nextWitness, extension, ?_, valueRelated, semanticStep⟩
  exact {
    heap := heapRelated
    globals := related.globals.witnessExtension extension
    world := related.world
    trace := related.trace.witnessExtension extension }

/-- Nonempty constructor allocation grows both heaps by one related object and
preserves every auxiliary runtime component under the extended witness. -/
theorem ConcreteRuntimeRel.allocateConstructorNonempty
    {concrete : ConcreteRuntimeState} {witness : RefinementWitness}
    {runtime : RuntimeState} {result : MemoryState}
    {info : Lean.Compiler.LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {fields : Array Word32} {semanticFields : Array Value} {address : Word32}
    (related : ConcreteRuntimeRel concrete witness runtime)
    (arity : fields.size = info.size)
    (semanticArity : semanticFields.size = info.size)
    (fieldKindsSize : fieldKinds.size = info.size)
    (fieldKindsValid : fieldKinds.all AbiKind.isObjectField = true)
    (fieldRelated : ∀ (index : Nat) (kind : AbiKind) (value : Value),
      fieldKinds[index]? = some kind →
      semanticFields[index]? = some value →
      ∃ word, fields[index]? = some word ∧
        ValueRel witness kind (.word32 word) value)
    (nonempty : ¬ ((info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0))
    (tagFits : info.cidx < UInt32.size)
    (objectFieldsFit : info.size < UInt32.size)
    (usizeFieldsFit : info.usize < UInt32.size)
    (scalarBytesFit : info.ssize < UInt32.size)
    (allocated : allocateConstructor concrete.heap info fields =
      .ok (result, address)) :
    let nextWitness :=
      witness.bindConstructor runtime.nextLocation address info fieldKinds
    witness.Extends nextWitness ∧
      ConcreteRuntimeRel { concrete with heap := result } nextWitness
        (semanticConstructorResult runtime info semanticFields) ∧
      ValueRel nextWitness .object (.word32 address)
        (.object (.heap runtime.nextLocation)) := by
  dsimp only
  obtain ⟨extension, heapRelated, valueRelated⟩ :=
    allocateConstructor_nonempty_liveHeapRel_extends concrete.heap result witness
      runtime info fieldKinds fields semanticFields address related.heap arity
      semanticArity fieldKindsSize fieldKindsValid fieldRelated nonempty tagFits
      objectFieldsFit usizeFieldsFit scalarBytesFit allocated
  refine ⟨extension, ?_, valueRelated⟩
  exact {
    heap := heapRelated
    globals := by
      simpa [semanticConstructorResult] using
        related.globals.witnessExtension extension
    world := by simpa [semanticConstructorResult] using related.world
    trace := by
      simpa [semanticConstructorResult] using
        related.trace.witnessExtension extension }

/-- Failures at the concrete Talos host boundary retain either the exact W6
runtime trap or a Wasm ABI-shape error detected before the operation runs. -/
inductive HostFailure where
  | runtime (failure : ConcreteTrap)
  | arityMismatch (expected actual : Nat)
  | laneMismatch (index : Nat) (expected : Fir.Wasm.ValueType)
  | unsupportedScalarKind (kind : AbiKind)
  deriving Inhabited, BEq, Repr

/-- Host-owned concrete linear memory and its latest structured failure. The
semantic runtime is deliberately absent: it occurs only in the refinement
relation and cannot be consulted by executable concrete host functions. -/
structure Host where
  runtime : ConcreteRuntimeState := {}
  closureDispatch : ClosureDispatchTable := #[]
  closureDescriptors : ClosureDescriptorTable := #[]
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

def usizeProjStep (index : Nat) (store : Wasm.Store Host)
    (args : List Wasm.Value) : Wasm.HostResult Host :=
  let store := clearFailure store
  match args with
  | [.i32 bits] =>
      match readUSizeField store.host.runtime.heap (Word32.ofUInt32 bits) index with
      | .ok value => .Return [.i64 value] store
      | .error failure => trap store (.runtime failure.toTrap)
  | [_] => trap store (.laneMismatch 0 .i32)
  | args => trap store (.arityMismatch 1 args.length)

def usizeProjFn (index : Nat) : Wasm.HostFn Host := {
  params := [.i32]
  results := [.i64]
  invoke := usizeProjStep index }

def usizeProjContract (index : Nat) : Wasm.HostContract Host :=
  fun initial args result => result = usizeProjStep index initial args

theorem usizeProjFn_satisfies_contract (index initial args) :
    usizeProjContract index initial args
      ((usizeProjFn index).invoke initial args) := by
  rfl

def scalarProjStep (width offset : Nat) (kind : AbiKind)
    (store : Wasm.Store Host) (args : List Wasm.Value) : Wasm.HostResult Host :=
  let store := clearFailure store
  match args with
  | [.i32 bits] =>
      let object := Word32.ofUInt32 bits
      match kind with
      | .uint8 =>
          match readScalarUInt8Field store.host.runtime.heap object width offset with
          | .ok value =>
              .Return [.i32 (UInt32.ofNat (Word32.ofUInt8 value).value)] store
          | .error failure => trap store (.runtime failure.toTrap)
      | .uint16 =>
          match readScalarUInt16Field store.host.runtime.heap object width offset with
          | .ok value =>
              .Return [.i32 (UInt32.ofNat (Word32.ofUInt16 value).value)] store
          | .error failure => trap store (.runtime failure.toTrap)
      | .uint32 =>
          match readScalarUInt32Field store.host.runtime.heap object width offset with
          | .ok value =>
              .Return [.i32 (UInt32.ofNat (Word32.ofUInt32 value).value)] store
          | .error failure => trap store (.runtime failure.toTrap)
      | .uint64 =>
          match readScalarUInt64Field store.host.runtime.heap object width offset with
          | .ok value => .Return [.i64 value] store
          | .error failure => trap store (.runtime failure.toTrap)
      | other => trap store (.unsupportedScalarKind other)
  | [_] => trap store (.laneMismatch 0 .i32)
  | args => trap store (.arityMismatch 1 args.length)

def scalarProjFn (width offset : Nat) (kind : AbiKind) : Wasm.HostFn Host := {
  params := [.i32]
  results := [FirTalos.abiKind kind]
  invoke := scalarProjStep width offset kind }

def scalarProjContract (width offset : Nat) (kind : AbiKind) :
    Wasm.HostContract Host :=
  fun initial args result =>
    result = scalarProjStep width offset kind initial args

theorem scalarProjFn_satisfies_contract (width offset kind initial args) :
    scalarProjContract width offset kind initial args
      ((scalarProjFn width offset kind).invoke initial args) := by
  rfl

def replaceHeap (store : Wasm.Store Host) (heap : MemoryState) :
    Wasm.Store Host :=
  let store := clearFailure store
  { store with host := { store.host with
      runtime := { store.host.runtime with heap } } }

def naturalLiteralStep (value : Nat) (store : Wasm.Store Host)
    (args : List Wasm.Value) : Wasm.HostResult Host :=
  let store := clearFailure store
  match args with
  | [] =>
      match allocateNatural store.host.runtime.heap value with
      | .ok (heap, word) =>
          .Return [.i32 (UInt32.ofNat word.value)] (replaceHeap store heap)
      | .error failure => trap store (.runtime failure.toTrap)
  | args => trap store (.arityMismatch 0 args.length)

def naturalLiteralFn (value : Nat) : Wasm.HostFn Host := {
  params := []
  results := [.i32]
  invoke := naturalLiteralStep value }

def naturalLiteralContract (value : Nat) : Wasm.HostContract Host :=
  fun initial args result => result = naturalLiteralStep value initial args

theorem naturalLiteralFn_satisfies_contract (value initial args) :
    naturalLiteralContract value initial args
      ((naturalLiteralFn value).invoke initial args) := by
  rfl

/-- Decode the i32-only physical fields accepted by constructor allocation.
The index is carried solely to produce a precise structured lane failure. -/
def decodeConstructorWords : Nat → List Wasm.Value → Except HostFailure (List Word32)
  | _, [] => .ok []
  | index, .i32 bits :: rest => do
      let tail ← decodeConstructorWords (index + 1) rest
      return Word32.ofUInt32 bits :: tail
  | index, _ :: _ => .error (.laneMismatch index .i32)

/-- Executable concrete implementation of the constructor-allocation import.
It decodes raw wasm32 fields, allocates in linear memory, and never consults
semantic values or a handle table. -/
def allocCtorStep (info : Lean.Compiler.LCNF.CtorInfo)
    (fieldKinds : Array AbiKind) (_resultKind : AbiKind)
    (store : Wasm.Store Host) (args : List Wasm.Value) : Wasm.HostResult Host :=
  let store := clearFailure store
  if args.length = fieldKinds.size then
    match decodeConstructorWords 0 args with
    | .ok fields =>
        match allocateConstructor store.host.runtime.heap info fields.toArray with
        | .ok (heap, word) =>
            .Return [.i32 (UInt32.ofNat word.value)] (replaceHeap store heap)
        | .error failure => trap store (.runtime failure.toTrap)
    | .error failure => trap store failure
  else
    trap store (.arityMismatch fieldKinds.size args.length)

def allocCtorFn (info : Lean.Compiler.LCNF.CtorInfo)
    (fieldKinds : Array AbiKind) (resultKind : AbiKind) : Wasm.HostFn Host := {
  params := fieldKinds.toList.map FirTalos.abiKind
  results := [FirTalos.abiKind resultKind]
  invoke := allocCtorStep info fieldKinds resultKind }

def allocCtorContract (info : Lean.Compiler.LCNF.CtorInfo)
    (fieldKinds : Array AbiKind) (resultKind : AbiKind) :
    Wasm.HostContract Host :=
  fun initial args result =>
    result = allocCtorStep info fieldKinds resultKind initial args

theorem allocCtorFn_satisfies_contract (info fieldKinds resultKind initial args) :
    allocCtorContract info fieldKinds resultKind initial args
      ((allocCtorFn info fieldKinds resultKind).invoke initial args) := by
  rfl

def replaceRuntime (store : Wasm.Store Host) (runtime : ConcreteRuntimeState) :
    Wasm.Store Host :=
  let store := clearFailure store
  { store with host := { store.host with runtime } }

/-- Decode one physical Talos value into W6's ABI lane selected by its static
kind. This is a bit-preserving conversion, not a semantic value decoder. -/
def decodePhysicalLane (kind : AbiKind) (physical : Wasm.Value) :
    Except HostFailure LaneValue :=
  match kind.valueType, physical with
  | .i32, .i32 bits => .ok (.word32 (Word32.ofUInt32 bits))
  | .i64, .i64 word => .ok (.word64 word)
  | .f32, .f32 bits => .ok (.float32Bits bits)
  | .f64, .f64 bits => .ok (.float64Bits bits)
  | expected, _ => .error (.laneMismatch 0 expected)

/-- Executable concrete lazy-cache update. The physical value is returned
unchanged for the following generated `global.set`. -/
def cacheSetStep (declaration : Lean.Name) (kind : AbiKind)
    (store : Wasm.Store Host) (args : List Wasm.Value) : Wasm.HostResult Host :=
  let store := clearFailure store
  match args with
  | [physical] =>
      match decodePhysicalLane kind physical with
      | .ok lane =>
          match store.host.runtime.writeGlobal declaration kind lane with
          | .ok runtime => .Return [physical] (replaceRuntime store runtime)
          | .error failure => trap store (.runtime failure.toTrap)
      | .error failure => trap store failure
  | args => trap store (.arityMismatch 1 args.length)

def cacheSetFn (declaration : Lean.Name) (kind : AbiKind) : Wasm.HostFn Host := {
  params := [FirTalos.abiKind kind]
  results := [FirTalos.abiKind kind]
  invoke := cacheSetStep declaration kind }

def cacheSetContract (declaration : Lean.Name) (kind : AbiKind) :
    Wasm.HostContract Host :=
  fun initial args result => result = cacheSetStep declaration kind initial args

theorem cacheSetFn_satisfies_contract (declaration kind initial args) :
    cacheSetContract declaration kind initial args
      ((cacheSetFn declaration kind).invoke initial args) := by
  rfl

def decodePhysicalLanes : Nat → List AbiKind → List Wasm.Value →
    Except HostFailure (List LaneValue)
  | _, [], [] => .ok []
  | index, kind :: kinds, physical :: physicals => do
      let lane ← match decodePhysicalLane kind physical with
        | .ok lane => .ok lane
        | .error (.laneMismatch _ expected) =>
            .error (.laneMismatch index expected)
        | .error failure => .error failure
      let tail ← decodePhysicalLanes (index + 1) kinds physicals
      return lane :: tail
  | _, kinds, physicals => .error (.arityMismatch kinds.length physicals.length)

def partialApplyStep (function : Lean.Name) (arity fixed : Nat)
    (fieldKinds : Array AbiKind) (_resultKind : AbiKind)
    (store : Wasm.Store Host) (args : List Wasm.Value) : Wasm.HostResult Host :=
  let store := clearFailure store
  if args.length = fixed then
    match decodePhysicalLanes 0 fieldKinds.toList args with
    | .ok captures =>
        match allocateClosure store.host.runtime.heap store.host.closureDispatch
            store.host.closureDescriptors function arity fieldKinds
            captures.toArray with
        | .ok (heap, word) =>
            .Return [.i32 (UInt32.ofNat word.value)] (replaceHeap store heap)
        | .error failure => trap store (.runtime failure.toTrap)
    | .error failure => trap store failure
  else
    trap store (.arityMismatch fixed args.length)

def partialApplyFn (function : Lean.Name) (arity fixed : Nat)
    (fieldKinds : Array AbiKind) (resultKind : AbiKind) : Wasm.HostFn Host := {
  params := fieldKinds.toList.map FirTalos.abiKind
  results := [FirTalos.abiKind resultKind]
  invoke := partialApplyStep function arity fixed fieldKinds resultKind }

def partialApplyContract (function : Lean.Name) (arity fixed : Nat)
    (fieldKinds : Array AbiKind) (resultKind : AbiKind) :
    Wasm.HostContract Host :=
  fun initial args result => result =
    partialApplyStep function arity fixed fieldKinds resultKind initial args

theorem partialApplyFn_satisfies_contract
    (function arity fixed fieldKinds resultKind initial args) :
    partialApplyContract function arity fixed fieldKinds resultKind initial args
      ((partialApplyFn function arity fixed fieldKinds resultKind).invoke
        initial args) := by
  rfl

/-- Bit-preserving conversion from W6's concrete lane vocabulary to Talos's
operand-stack values. -/
def physicalOfLane : LaneValue → Wasm.Value
  | .word32 word => .i32 (UInt32.ofNat word.value)
  | .word64 word => .i64 word
  | .float32Bits bits => .f32 bits
  | .float64Bits bits => .f64 bits

theorem physicalOfLane_related
    {witness : RefinementWitness} {kind : AbiKind} {lane : LaneValue}
    {semantic : Value} (related : ValueRel witness kind lane semantic) :
    PhysicalValueRel witness kind (physicalOfLane lane) semantic := by
  cases related with
  | object related => exact .word32 (.object related)
  | tagged related => exact .word32 (.tagged related)
  | tobject related => exact .word32 (.tobject related)
  | erased => exact .word32 .erased
  | reuseNone => exact .word32 .reuseNone
  | reuseSome related => exact .word32 (.reuseSome related)
  | uint8 encoded => exact .word32 (.uint8 encoded)
  | uint16 encoded => exact .word32 (.uint16 encoded)
  | uint32 encoded => exact .word32 (.uint32 encoded)
  | uint64 => exact .word64 .uint64
  | usize => exact .word64 .usize

/-- Concrete trampoline metadata test. It reads only the closure header and
returns the direct i32 Boolean consumed by generated `if` control flow. -/
def closureMatchesStep (function : Lean.Name) (arity fixed : Nat)
    (store : Wasm.Store Host) (args : List Wasm.Value) : Wasm.HostResult Host :=
  let store := clearFailure store
  match args with
  | [.i32 bits] =>
      match closureMatches store.host.runtime.heap store.host.closureDispatch
          store.host.closureDescriptors (Word32.ofUInt32 bits) function arity
          fixed with
      | .ok matched => .Return [.i32 matched] store
      | .error failure => trap store (.runtime failure.toTrap)
  | [_] => trap store (.laneMismatch 0 .i32)
  | args => trap store (.arityMismatch 1 args.length)

def closureMatchesFn (function : Lean.Name) (arity fixed : Nat) :
    Wasm.HostFn Host := {
  params := [.i32]
  results := [.i32]
  invoke := closureMatchesStep function arity fixed }

def closureMatchesContract (function : Lean.Name) (arity fixed : Nat) :
    Wasm.HostContract Host :=
  fun initial args result =>
    result = closureMatchesStep function arity fixed initial args

theorem closureMatchesFn_satisfies_contract
    (function arity fixed initial args) :
    closureMatchesContract function arity fixed initial args
      ((closureMatchesFn function arity fixed).invoke initial args) := by
  rfl

/-- Concrete typed capture projection used by the generated trampoline. -/
def closureProjStep (function : Lean.Name) (arity fixed index : Nat)
    (resultKind : AbiKind) (store : Wasm.Store Host)
    (args : List Wasm.Value) : Wasm.HostResult Host :=
  let store := clearFailure store
  match args with
  | [.i32 bits] =>
      match projectClosureCapture store.host.runtime.heap
          store.host.closureDispatch store.host.closureDescriptors
          (Word32.ofUInt32 bits) function arity fixed index resultKind with
      | .ok lane => .Return [physicalOfLane lane] store
      | .error failure => trap store (.runtime failure.toTrap)
  | [_] => trap store (.laneMismatch 0 .i32)
  | args => trap store (.arityMismatch 1 args.length)

def closureProjFn (function : Lean.Name) (arity fixed index : Nat)
    (resultKind : AbiKind) : Wasm.HostFn Host := {
  params := [.i32]
  results := [FirTalos.abiKind resultKind]
  invoke := closureProjStep function arity fixed index resultKind }

def closureProjContract (function : Lean.Name) (arity fixed index : Nat)
    (resultKind : AbiKind) : Wasm.HostContract Host :=
  fun initial args result =>
    result = closureProjStep function arity fixed index resultKind initial args

theorem closureProjFn_satisfies_contract
    (function arity fixed index resultKind initial args) :
    closureProjContract function arity fixed index resultKind initial args
      ((closureProjFn function arity fixed index resultKind).invoke
        initial args) := by
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

theorem ConcreteRuntimeRel.readUSizeField_refines
    {concrete : ConcreteRuntimeState} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32} {sourceObject : Value}
    {info : Lean.Compiler.LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {index : Nat} {value : UInt64}
    (related : ConcreteRuntimeRel concrete witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (descriptor : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (projected : getUSizeField runtime sourceObject index = .ok (.usize value)) :
    readUSizeField concrete.heap objectWord index = .ok value ∧
      ValueRel witness .usize (.word64 value) (.usize value) := by
  cases objectRelated with
  | tobject objectRelated =>
      cases objectRelated with
      | heap mapped =>
          cases mapped with
          | mapped found =>
              exact related.heap.readUSizeField_refines found descriptor projected
      | tagged taggedRelated =>
          cases taggedRelated <;>
            simp [getUSizeField, getConstructor, Bind.bind, Except.bind] at projected

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

theorem usizeProjStep_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32} {sourceObject : Value}
    {info : Lean.Compiler.LCNF.CtorInfo} {fieldKinds : Array AbiKind}
    {index : Nat} {value : UInt64}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (descriptor : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (projected : getUSizeField runtime sourceObject index = .ok (.usize value)) :
    readUSizeField initial.host.runtime.heap objectWord index = .ok value ∧
      usizeProjStep index initial [.i32 (UInt32.ofNat objectWord.value)] =
        .Return [.i64 value] (clearFailure initial) ∧
      ValueRel witness .usize (.word64 value) (.usize value) := by
  obtain ⟨read, valueRelated⟩ :=
    FirTalos.Concrete.ConcreteRuntimeRel.readUSizeField_refines runtimeRelated
      objectRelated descriptor projected
  refine ⟨read, ?_, valueRelated⟩
  simp [usizeProjStep, clearFailure, read]

theorem scalarProjUInt8Step_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32} {sourceObject : Value}
    {width offset : Nat} {value : UInt8}
    (runtimeRelated : ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (projected : getScalarField runtime sourceObject width offset =
      .ok (.scalar (.uint8 value))) :
    scalarProjStep width offset .uint8 initial
        [.i32 (UInt32.ofNat objectWord.value)] =
      .Return [.i32 (UInt32.ofNat (Word32.ofUInt8 value).value)]
        (clearFailure initial) ∧
      PhysicalValueRel witness .uint8
        (.i32 (UInt32.ofNat (Word32.ofUInt8 value).value))
        (.scalar (.uint8 value)) := by
  cases objectRelated with
  | tobject referenceRelated =>
      cases referenceRelated with
      | heap heapRelated =>
          cases heapRelated with
          | mapped mapped =>
              obtain ⟨read, valueRelated⟩ :=
                runtimeRelated.heap.readScalarUInt8Field_refines mapped projected
              exact ⟨by simp [scalarProjStep, clearFailure, read],
                .word32 valueRelated⟩
      | tagged taggedRelated =>
          cases taggedRelated <;>
            simp [getScalarField, getConstructor, Bind.bind, Except.bind]
              at projected

theorem scalarProjUInt16Step_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32} {sourceObject : Value}
    {width offset : Nat} {value : UInt16}
    (runtimeRelated : ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (projected : getScalarField runtime sourceObject width offset =
      .ok (.scalar (.uint16 value))) :
    scalarProjStep width offset .uint16 initial
        [.i32 (UInt32.ofNat objectWord.value)] =
      .Return [.i32 (UInt32.ofNat (Word32.ofUInt16 value).value)]
        (clearFailure initial) ∧
      PhysicalValueRel witness .uint16
        (.i32 (UInt32.ofNat (Word32.ofUInt16 value).value))
        (.scalar (.uint16 value)) := by
  cases objectRelated with
  | tobject referenceRelated =>
      cases referenceRelated with
      | heap heapRelated =>
          cases heapRelated with
          | mapped mapped =>
              obtain ⟨read, valueRelated⟩ :=
                runtimeRelated.heap.readScalarUInt16Field_refines mapped projected
              exact ⟨by simp [scalarProjStep, clearFailure, read],
                .word32 valueRelated⟩
      | tagged taggedRelated =>
          cases taggedRelated <;>
            simp [getScalarField, getConstructor, Bind.bind, Except.bind]
              at projected

theorem scalarProjUInt32Step_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32} {sourceObject : Value}
    {width offset : Nat} {value : UInt32}
    (runtimeRelated : ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (projected : getScalarField runtime sourceObject width offset =
      .ok (.scalar (.uint32 value))) :
    scalarProjStep width offset .uint32 initial
        [.i32 (UInt32.ofNat objectWord.value)] =
      .Return [.i32 (UInt32.ofNat (Word32.ofUInt32 value).value)]
        (clearFailure initial) ∧
      PhysicalValueRel witness .uint32
        (.i32 (UInt32.ofNat (Word32.ofUInt32 value).value))
        (.scalar (.uint32 value)) := by
  cases objectRelated with
  | tobject referenceRelated =>
      cases referenceRelated with
      | heap heapRelated =>
          cases heapRelated with
          | mapped mapped =>
              obtain ⟨read, valueRelated⟩ :=
                runtimeRelated.heap.readScalarUInt32Field_refines mapped projected
              exact ⟨by simp [scalarProjStep, clearFailure, read],
                .word32 valueRelated⟩
      | tagged taggedRelated =>
          cases taggedRelated <;>
            simp [getScalarField, getConstructor, Bind.bind, Except.bind]
              at projected

theorem scalarProjUInt64Step_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {objectWord : Word32} {sourceObject : Value}
    {width offset : Nat} {value : UInt64}
    (runtimeRelated : ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (projected : getScalarField runtime sourceObject width offset =
      .ok (.scalar (.uint64 value))) :
    scalarProjStep width offset .uint64 initial
        [.i32 (UInt32.ofNat objectWord.value)] =
      .Return [.i64 value] (clearFailure initial) ∧
      PhysicalValueRel witness .uint64 (.i64 value)
        (.scalar (.uint64 value)) := by
  cases objectRelated with
  | tobject referenceRelated =>
      cases referenceRelated with
      | heap heapRelated =>
          cases heapRelated with
          | mapped mapped =>
              obtain ⟨read, valueRelated⟩ :=
                runtimeRelated.heap.readScalarUInt64Field_refines mapped projected
              exact ⟨by simp [scalarProjStep, clearFailure, read],
                .word64 valueRelated⟩
      | tagged taggedRelated =>
          cases taggedRelated <;>
            simp [getScalarField, getConstructor, Bind.bind, Except.bind]
              at projected

theorem naturalLiteralStep_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {value : Nat} {heap : MemoryState}
    {word : Word32}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (allocated : allocateNatural initial.host.runtime.heap value =
      .ok (heap, word)) :
    ∃ nextWitness,
      witness.Extends nextWitness ∧
      naturalLiteralStep value initial [] =
        .Return [.i32 (UInt32.ofNat word.value)] (replaceHeap initial heap) ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime nextWitness
        (literal runtime (.nat value)).1 ∧
      PhysicalValueRel nextWitness .tobject
        (.i32 (UInt32.ofNat word.value)) (literal runtime (.nat value)).2 := by
  obtain ⟨nextWitness, extension, nextRuntimeRelated, valueRelated⟩ :=
    FirTalos.Concrete.ConcreteRuntimeRel.allocateNatural runtimeRelated allocated
  refine ⟨nextWitness, extension, ?_, ?_, .word32 valueRelated⟩
  · simp [naturalLiteralStep, replaceHeap, clearFailure, allocated]
  · simpa [replaceHeap, clearFailure] using nextRuntimeRelated

/-- The compiler may widen an exact tagged constructor result to `tobject`. -/
theorem taggedConstructorResult_of_refines
    {witness : RefinementWitness} {info : Lean.Compiler.LCNF.CtorInfo}
    {resultKind : AbiKind} {word : Word32}
    (empty : (info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0)
    (resultRefines : (constructorKind info).refines resultKind = true)
    (related : ValueRel witness .tagged (.word32 word)
      (.object (.tagged (UInt64.ofNat info.cidx)))) :
    ValueRel witness resultKind (.word32 word)
      (.object (.tagged (UInt64.ofNat info.cidx))) := by
  cases resultKind <;>
    simp [constructorKind, empty.1.1, empty.1.2, empty.2, AbiKind.refines]
      at resultRefines
  · exact related
  · exact related.tagged_to_tobject

/-- The compiler may widen an exact heap constructor result to `tobject`. -/
theorem objectConstructorResult_of_refines
    {witness : RefinementWitness} {info : Lean.Compiler.LCNF.CtorInfo}
    {resultKind : AbiKind} {word : Word32} {location : Location}
    (nonempty : ¬ ((info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0))
    (resultRefines : (constructorKind info).refines resultKind = true)
    (related : ValueRel witness .object (.word32 word)
      (.object (.heap location))) :
    ValueRel witness resultKind (.word32 word) (.object (.heap location)) := by
  cases resultKind <;>
    simp [constructorKind, nonempty, AbiKind.refines] at resultRefines
  · exact related
  · exact related.object_to_tobject

/-- Executable/refinement boundary for an empty constructor. The returned word
is immediate when possible and otherwise a fresh promoted tag. -/
theorem allocCtorEmptyStep_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {info : Lean.Compiler.LCNF.CtorInfo}
    {fieldKinds : Array AbiKind} {resultKind : AbiKind}
    {physicalArgs : List Wasm.Value} {fields : List Word32}
    {semanticFields : Array Value} {heap : MemoryState} {word : Word32}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (argsLength : physicalArgs.length = fieldKinds.size)
    (decoded : decodeConstructorWords 0 physicalArgs = .ok fields)
    (arity : fields.toArray.size = info.size)
    (semanticArity : semanticFields.size = info.size)
    (empty : (info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0)
    (tagFits : info.cidx < UInt32.size)
    (resultRefines : (constructorKind info).refines resultKind = true)
    (allocated : allocateConstructor initial.host.runtime.heap info fields.toArray =
      .ok (heap, word)) :
    ∃ nextWitness,
      witness.Extends nextWitness ∧
      allocCtorStep info fieldKinds resultKind initial physicalArgs =
        .Return [.i32 (UInt32.ofNat word.value)] (replaceHeap initial heap) ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime nextWitness runtime ∧
      PhysicalValueRel nextWitness resultKind
        (.i32 (UInt32.ofNat word.value))
        (.object (.tagged (UInt64.ofNat info.cidx))) ∧
      allocCtor runtime info semanticFields =
        .ok (runtime, .object (.tagged (UInt64.ofNat info.cidx))) := by
  obtain ⟨nextWitness, extension, nextRuntimeRelated, exactRelated,
      semanticStep⟩ :=
    FirTalos.Concrete.ConcreteRuntimeRel.allocateConstructorEmpty runtimeRelated
      arity semanticArity empty tagFits allocated
  have valueRelated := taggedConstructorResult_of_refines empty resultRefines
    exactRelated
  refine ⟨nextWitness, extension, ?_, ?_, .word32 valueRelated,
    semanticStep⟩
  · simp [allocCtorStep, argsLength, decoded, allocated, replaceHeap, clearFailure]
  · simpa [replaceHeap, clearFailure] using nextRuntimeRelated

/-- Executable/refinement boundary for a nonempty constructor allocation. -/
theorem allocCtorNonemptyStep_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {info : Lean.Compiler.LCNF.CtorInfo}
    {fieldKinds : Array AbiKind} {resultKind : AbiKind}
    {physicalArgs : List Wasm.Value} {fields : List Word32}
    {semanticFields : Array Value} {heap : MemoryState} {address : Word32}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (argsLength : physicalArgs.length = fieldKinds.size)
    (decoded : decodeConstructorWords 0 physicalArgs = .ok fields)
    (arity : fields.toArray.size = info.size)
    (semanticArity : semanticFields.size = info.size)
    (fieldKindsSize : fieldKinds.size = info.size)
    (fieldKindsValid : fieldKinds.all AbiKind.isObjectField = true)
    (fieldRelated : ∀ (index : Nat) (kind : AbiKind) (value : Value),
      fieldKinds[index]? = some kind →
      semanticFields[index]? = some value →
      ∃ word, fields.toArray[index]? = some word ∧
        ValueRel witness kind (.word32 word) value)
    (nonempty : ¬ ((info.size = 0 ∧ info.usize = 0) ∧ info.ssize = 0))
    (tagFits : info.cidx < UInt32.size)
    (objectFieldsFit : info.size < UInt32.size)
    (usizeFieldsFit : info.usize < UInt32.size)
    (scalarBytesFit : info.ssize < UInt32.size)
    (resultRefines : (constructorKind info).refines resultKind = true)
    (allocated : allocateConstructor initial.host.runtime.heap info fields.toArray =
      .ok (heap, address)) :
    let nextWitness := witness.bindConstructor runtime.nextLocation address info
      fieldKinds
    witness.Extends nextWitness ∧
      allocCtorStep info fieldKinds resultKind initial physicalArgs =
        .Return [.i32 (UInt32.ofNat address.value)] (replaceHeap initial heap) ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime nextWitness
        (semanticConstructorResult runtime info semanticFields) ∧
      PhysicalValueRel nextWitness resultKind
        (.i32 (UInt32.ofNat address.value))
        (.object (.heap runtime.nextLocation)) ∧
      allocCtor runtime info semanticFields =
        .ok (semanticConstructorResult runtime info semanticFields,
          .object (.heap runtime.nextLocation)) := by
  dsimp only
  obtain ⟨extension, nextRuntimeRelated, exactRelated⟩ :=
    FirTalos.Concrete.ConcreteRuntimeRel.allocateConstructorNonempty runtimeRelated
      arity semanticArity fieldKindsSize fieldKindsValid fieldRelated nonempty
      tagFits objectFieldsFit usizeFieldsFit scalarBytesFit allocated
  have valueRelated := objectConstructorResult_of_refines nonempty resultRefines
    exactRelated
  refine ⟨extension, ?_, ?_, .word32 valueRelated,
    allocCtor_nonempty_eq runtime info semanticFields semanticArity nonempty⟩
  · simp [allocCtorStep, argsLength, decoded, allocated, replaceHeap, clearFailure]
  · simpa [replaceHeap, clearFailure] using nextRuntimeRelated

/-- A related physical value always decodes to the exact W6 lane witnessed by
`ValueRel`. -/
theorem decodePhysicalLane_of_related
    {witness : RefinementWitness} {kind : AbiKind} {physical : Wasm.Value}
    {semantic : Value}
    (related : PhysicalValueRel witness kind physical semantic) :
    ∃ lane,
      decodePhysicalLane kind physical = .ok lane ∧
      ValueRel witness kind lane semantic := by
  cases related with
  | word32 valueRelated =>
      refine ⟨_, ?_, valueRelated⟩
      cases valueRelated <;>
        simp [decodePhysicalLane, AbiKind.valueType]
  | word64 valueRelated =>
      refine ⟨_, ?_, valueRelated⟩
      cases valueRelated <;> rfl
  | float32Bits valueRelated => cases valueRelated
  | float64Bits valueRelated => cases valueRelated

/-- Successful concrete cache update refines FIR's `setGlobal` and returns the
same physical lane for the generated Wasm global write. -/
theorem cacheSetStep_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {declaration : Lean.Name} {kind : AbiKind}
    {physical : Wasm.Value} {semantic : Value} {slot : ConcreteGlobalSlot}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (valueRelated : PhysicalValueRel witness kind physical semantic)
    (found : initial.host.runtime.globals.find? declaration = some slot)
    (kindEq : slot.kind = kind) :
    ∃ after,
      cacheSetStep declaration kind initial [physical] =
        .Return [physical] (replaceRuntime initial after) ∧
      ConcreteRuntimeRel (replaceRuntime initial after).host.runtime witness
        (runtime.setGlobal declaration semantic) ∧
      PhysicalValueRel witness kind physical semantic := by
  obtain ⟨lane, decoded, laneRelated⟩ :=
    decodePhysicalLane_of_related valueRelated
  obtain ⟨after, operation, nextRuntimeRelated⟩ :=
    Fir.Wasm.Concrete.ConcreteRuntimeRel.writeGlobal runtimeRelated found kindEq
      laneRelated
  refine ⟨after, ?_, ?_, valueRelated⟩
  · simp [cacheSetStep, clearFailure, decoded, operation, replaceRuntime]
  · simpa [replaceRuntime, clearFailure] using nextRuntimeRelated

/-- Executable/refinement boundary for partial-application closure allocation.
The `.tagged` result admitted by the current validator is deliberately absent;
see `FIR-BUG-wasm-none-partial-apply-tagged-result`. -/
theorem partialApplyStep_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {function : Lean.Name} {arity fixed : Nat}
    {fieldKinds : Array AbiKind} {resultKind : AbiKind}
    {physicalArgs : List Wasm.Value} {captures : List LaneValue}
    {semantic : Array Value} {heap : MemoryState} {address : Word32}
    {targetId descriptorId : UInt32}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (resultKindSupported : resultKind = .object ∨ resultKind = .tobject)
    (fixedArgs : physicalArgs.length = fixed)
    (decoded : decodePhysicalLanes 0 fieldKinds.toList physicalArgs =
      .ok captures)
    (count : fieldKinds.size = captures.toArray.size)
    (semanticCount : semantic.size = captures.toArray.size)
    (capturesLtArity : captures.toArray.size < arity)
    (targetIdEq : closureTargetId initial.host.closureDispatch function =
      .ok targetId)
    (targetLookup : initial.host.closureDispatch.lookup? targetId = some function)
    (descriptorIdEq : closureDescriptorId initial.host.closureDescriptors
      fieldKinds = .ok descriptorId)
    (descriptorLookup : initial.host.closureDescriptors.lookup? descriptorId =
      some fieldKinds)
    (dispatchEq : witness.closureDispatch = initial.host.closureDispatch)
    (descriptorsEq : witness.closureDescriptors =
      initial.host.closureDescriptors)
    (arityFits : arity < UInt32.size)
    (fixedFits : captures.toArray.size < UInt32.size)
    (captureTyped : ∀ (index : Nat) (kind : AbiKind) (lane : LaneValue),
      fieldKinds[index]? = some kind →
      captures.toArray[index]? = some lane →
      lane.valueType = kind.valueType)
    (captureRelated : ∀ (index : Nat) (kind : AbiKind) (lane : LaneValue)
        (value : Value),
      fieldKinds[index]? = some kind →
      captures.toArray[index]? = some lane →
      semantic[index]? = some value →
      ValueRel witness kind lane value)
    (allocated : allocateClosure initial.host.runtime.heap
      initial.host.closureDispatch initial.host.closureDescriptors function arity
      fieldKinds captures.toArray = .ok (heap, address)) :
    let nextWitness := witness.bindClosure runtime.nextLocation address function
      arity fieldKinds
    witness.Extends nextWitness ∧
      partialApplyStep function arity fixed fieldKinds resultKind initial
          physicalArgs =
        .Return [.i32 (UInt32.ofNat address.value)] (replaceHeap initial heap) ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime nextWitness
        (semanticClosureResult runtime function arity semantic) ∧
      PhysicalValueRel nextWitness resultKind
        (.i32 (UInt32.ofNat address.value))
        (.object (.heap runtime.nextLocation)) ∧
      alloc runtime (.closure function arity semantic) =
        (semanticClosureResult runtime function arity semantic,
          .heap runtime.nextLocation) := by
  dsimp only
  obtain ⟨extension, heapRelated, objectRelated, tobjectRelated⟩ :=
    allocateClosure_liveHeapRel_extends initial.host.runtime.heap heap witness
      runtime initial.host.closureDispatch initial.host.closureDescriptors
      function arity fieldKinds captures.toArray semantic address targetId
      descriptorId runtimeRelated.heap count semanticCount capturesLtArity
      targetIdEq targetLookup descriptorIdEq descriptorLookup dispatchEq
      descriptorsEq arityFits fixedFits captureTyped captureRelated allocated
  have valueRelated : ValueRel
      (witness.bindClosure runtime.nextLocation address function arity fieldKinds)
      resultKind (.word32 address) (.object (.heap runtime.nextLocation)) := by
    rcases resultKindSupported with rfl | rfl
    · exact objectRelated
    · exact tobjectRelated
  refine ⟨extension, ?_, ?_, .word32 valueRelated,
    alloc_closure_eq runtime function arity semantic⟩
  · simp [partialApplyStep, fixedArgs, decoded, allocated, replaceHeap,
      clearFailure]
  · exact {
      heap := by simpa [replaceHeap, clearFailure] using heapRelated
      globals := by
        simpa [replaceHeap, clearFailure, semanticClosureResult] using
          runtimeRelated.globals.witnessExtension extension
      world := by
        simpa [replaceHeap, clearFailure, semanticClosureResult] using
          runtimeRelated.world
      trace := by
        simpa [replaceHeap, clearFailure, semanticClosureResult] using
          runtimeRelated.trace.witnessExtension extension }

/-- Executable trampoline metadata matching agrees with the exact semantic
closure identity predicate and leaves the concrete runtime unchanged. -/
theorem closureMatchesStep_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {location : Location} {address : Word32}
    {cell : HeapCell} {function : Lean.Name} {arity : Nat}
    {captures : Array Value} {expectedFunction : Lean.Name}
    {expectedArity expectedFixed : Nat}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (dispatchEq : witness.closureDispatch = initial.host.closureDispatch)
    (descriptorsEq :
      witness.closureDescriptors = initial.host.closureDescriptors)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .closure function arity captures) :
    closureMatchesStep expectedFunction expectedArity expectedFixed initial
        [.i32 (UInt32.ofNat address.value)] =
      .Return [
        .i32 (if function == expectedFunction && arity == expectedArity &&
          captures.size == expectedFixed then 1 else 0)]
        (clearFailure initial) ∧
      closureData runtime (.object (.heap location)) =
        .ok (function, arity, captures) := by
  have concreteMatch := runtimeRelated.heap.closureMatches_refines mapped found live
    objectEq expectedFunction expectedArity expectedFixed
  constructor
  · unfold closureMatchesStep
    simp only [clearFailure]
    rw [Word32.ofUInt32_ofNat_value, ← dispatchEq, ← descriptorsEq,
      concreteMatch]
  · unfold closureData
    simp only [getLiveCell, found, live, if_true, Bind.bind, Except.bind]
    rw [objectEq]
    rfl

/-- Executable typed capture projection returns the exact Talos lane related
to the selected semantic capture and preserves the runtime state. -/
theorem closureProjStep_of_refines
    {initial : Wasm.Store Host} {witness : RefinementWitness}
    {runtime : RuntimeState} {location : Location} {address : Word32}
    {cell : HeapCell} {function : Lean.Name} {arity fixed index : Nat}
    {captures : Array Value} {captureKinds : Array AbiKind}
    {kind : AbiKind} {value : Value}
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (dispatchEq : witness.closureDispatch = initial.host.closureDispatch)
    (descriptorsEq :
      witness.closureDescriptors = initial.host.closureDescriptors)
    (mapped : witness.locations.lookup? location = some address)
    (found : findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (objectEq : cell.object = .closure function arity captures)
    (descriptorFound : witness.descriptors.lookup? address =
      some (.closure function arity captureKinds))
    (fixedSize : captures.size = fixed)
    (kindAt : captureKinds[index]? = some kind)
    (valueAt : captures[index]? = some value) :
    ∃ lane,
      closureProjStep function arity fixed index kind initial
          [.i32 (UInt32.ofNat address.value)] =
        .Return [physicalOfLane lane] (clearFailure initial) ∧
      PhysicalValueRel witness kind (physicalOfLane lane) value ∧
      closureData runtime (.object (.heap location)) =
        .ok (function, arity, captures) := by
  obtain ⟨lane, projected, valueRelated⟩ :=
    runtimeRelated.heap.projectClosureCapture_refines mapped found live objectEq
      descriptorFound kindAt valueAt
  rw [fixedSize] at projected
  refine ⟨lane, ?_, physicalOfLane_related valueRelated, ?_⟩
  · unfold closureProjStep
    simp only [clearFailure]
    rw [Word32.ofUInt32_ofNat_value, ← dispatchEq, ← descriptorsEq,
      projected]
  · unfold closureData
    simp only [getLiveCell, found, live, if_true, Bind.bind, Except.bind]
    rw [objectEq]
    rfl

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
  rcases host with ⟨runtime, closureDispatch, closureDescriptors, failure⟩
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

theorem StateRelated.bindWord64
    {sourceFunction : Fir.Wasm.Function} {sourceRuntime : RuntimeState}
    {sourceEnv : Env} {targetStore : Wasm.Store Host}
    {targetLocals updated : Wasm.Locals} {witness : RefinementWitness}
    {result : Lean.FVarId} {resultIndex : Nat} {kind : AbiKind}
    {word : UInt64} {semantic : Value}
    (related : StateRelated sourceFunction sourceRuntime sourceEnv targetStore
      targetLocals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) result = some resultIndex)
    (kindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some kind)
    (valueRelated : ValueRel witness kind (.word64 word) semantic)
    (targetSet : targetLocals.set? resultIndex (.i64 word) = some updated) :
    StateRelated sourceFunction sourceRuntime (bind sourceEnv result semantic)
      (FirTalos.Concrete.clearFailure targetStore) updated witness := by
  rw [related.clearFailure]
  exact ⟨related.1, related.2.1,
    EnvLocalsRelated.bind related.2.2 resultFound kindAt
      (localUpdate_of_set? targetSet) (.refl witness) (.word64 valueRelated)⟩

theorem StateRelated.bindPhysical
    {sourceFunction : Fir.Wasm.Function} {sourceRuntime : RuntimeState}
    {sourceEnv : Env} {targetStore : Wasm.Store Host}
    {targetLocals updated : Wasm.Locals} {witness : RefinementWitness}
    {result : Lean.FVarId} {resultIndex : Nat} {kind : AbiKind}
    {physical : Wasm.Value} {semantic : Value}
    (related : StateRelated sourceFunction sourceRuntime sourceEnv targetStore
      targetLocals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) result = some resultIndex)
    (kindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some kind)
    (valueRelated : PhysicalValueRel witness kind physical semantic)
    (targetSet : targetLocals.set? resultIndex physical = some updated) :
    StateRelated sourceFunction sourceRuntime (bind sourceEnv result semantic)
      (FirTalos.Concrete.clearFailure targetStore) updated witness := by
  rw [related.clearFailure]
  exact ⟨related.1, related.2.1,
    EnvLocalsRelated.bind related.2.2 resultFound kindAt
      (localUpdate_of_set? targetSet) (.refl witness) valueRelated⟩

theorem StateRelated.bindAfter
    {sourceFunction : Fir.Wasm.Function}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {targetStore nextStore : Wasm.Store Host}
    {targetLocals updated : Wasm.Locals}
    {witness nextWitness : RefinementWitness}
    {result : Lean.FVarId} {resultIndex : Nat} {kind : AbiKind}
    {physical : Wasm.Value} {semantic : Value}
    (related : StateRelated sourceFunction sourceRuntime sourceEnv targetStore
      targetLocals witness)
    (extension : witness.Extends nextWitness)
    (runtimeRelated :
      ConcreteRuntimeRel nextStore.host.runtime nextWitness nextRuntime)
    (failureClear : nextStore.host.failure? = none)
    (resultFound :
      findFVar? (functionBindings sourceFunction) result = some resultIndex)
    (kindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some kind)
    (valueRelated : PhysicalValueRel nextWitness kind physical semantic)
    (targetSet : targetLocals.set? resultIndex physical = some updated) :
    StateRelated sourceFunction nextRuntime (bind sourceEnv result semantic)
      nextStore updated nextWitness := by
  exact ⟨runtimeRelated, failureClear,
    EnvLocalsRelated.bind related.2.2 resultFound kindAt
      (localUpdate_of_set? targetSet) extension valueRelated⟩

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

/-- Function-body postcondition over the concrete host. It retains the caller
operand remainder exactly as prescribed by Wasm's direct-call convention. -/
def ConcreteFunctionBodyPost (function : Wasm.Function)
    (args : List Wasm.Value)
    (Post : Wasm.Store Host → List Wasm.Value → Prop) :
    Wasm.Assertion Host :=
  fun continuation =>
    match continuation with
    | .Fallthrough targetStore targetLocals =>
        Post targetStore
          (targetLocals.values.take function.results.length ++
            args.drop function.numParams)
    | .Return targetStore values =>
        Post targetStore
          (values.take function.results.length ++ args.drop function.numParams)
    | _ => False

/-- Store-specific bridge from a concrete body WP to Talos's fuel-free public
function predicate. -/
theorem concreteTerminatesWith_of_wp_body_at
    {env : Wasm.HostEnv Host} {module : Wasm.Module}
    {functionIndex : Nat} {function : Wasm.Function}
    {initial : Wasm.Store Host} {args : List Wasm.Value}
    {Post : Wasm.Store Host → List Wasm.Value → Prop}
    (notImport : module.imports[functionIndex]? = none)
    (found :
      module.funcs[functionIndex - module.imports.length]? = some function)
    (bodyWP :
      Wasm.wp module function.body
        (ConcreteFunctionBodyPost function args Post) initial
        (function.toLocals (args.take function.numParams).reverse) env) :
    Wasm.TerminatesWith env module functionIndex initial args Post := by
  unfold Wasm.wp at bodyWP
  rcases bodyWP with ⟨fuelBound, bodyWP⟩
  refine ⟨fuelBound, fun fuel enoughFuel => ?_⟩
  have bodyPost := bodyWP fuel enoughFuel
  rw [Wasm.run_eq notImport]
  simp only [found]
  cases execution : Wasm.exec fuel module initial
      (function.toLocals (args.take function.numParams).reverse)
      function.body env with
  | Fallthrough final finalLocals =>
      rw [execution] at bodyPost
      exact ⟨finalLocals.values.take function.results.length ++
          args.drop function.numParams, final, rfl, bodyPost⟩
  | Return final values =>
      rw [execution] at bodyPost
      exact ⟨values.take function.results.length ++ args.drop function.numParams,
        final, rfl, bodyPost⟩
  | Break level final finalLocals =>
      rw [execution] at bodyPost
      exact bodyPost.elim
  | Trap final message =>
      rw [execution] at bodyPost
      exact bodyPost.elim
  | Invalid message =>
      rw [execution] at bodyPost
      exact bodyPost.elim
  | OutOfFuel =>
      rw [execution] at bodyPost
      exact bodyPost.elim
  | ReturnCall callee final values =>
      rw [execution] at bodyPost
      exact bodyPost.elim
  | Throwing tag values final finalLocals =>
      rw [execution] at bodyPost
      exact bodyPost.elim

/-- A concrete semantic lowering proof for a callee body supplies the exact
fuel-free theorem consumed by `wp_directCall_let`. -/
theorem CodeWP.toConcreteTerminatesWith
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host}
    {sourceRuntime : RuntimeState} {sourceEnv : Env}
    {code : Lean.Compiler.LCNF.Code .impure} {function : Wasm.Function}
    {functionIndex : Nat} {initial : Wasm.Store Host}
    {args : List Wasm.Value} {witness : RefinementWitness}
    {Post : Wasm.Store Host → List Wasm.Value → Prop}
    (notImport : module.imports[functionIndex]? = none)
    (found :
      module.funcs[functionIndex - module.imports.length]? = some function)
    (correct :
      CodeWP context sourceModule sourceFunction labels module hostEnv
        sourceRuntime sourceEnv code function.body initial
        (function.toLocals (args.take function.numParams).reverse) witness []
        (ConcreteFunctionBodyPost function args Post)) :
    Wasm.TerminatesWith hostEnv module functionIndex initial args Post := by
  apply concreteTerminatesWith_of_wp_body_at notImport found
  simpa [Wasm.Function.toLocals] using correct.2.2

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

/-- Witness-indexed interprocedural boundary for ordinary declaration calls
and generated closure trampolines over the concrete host. -/
def CallLetStepSimulates (context : Fir.Wasm.Context)
    (sourceFunction : Fir.Wasm.Function) (module : Wasm.Module)
    (hostEnv : Wasm.HostEnv Host) (externals : ExternalImpl)
    (decl : Lean.Compiler.LCNF.LetDecl .impure)
    (continuation : Lean.Compiler.LCNF.Code .impure)
    (targetValue : Wasm.Program)
    (sourceRuntime nextRuntime : RuntimeState) (sourceEnv : Env)
    (sourceValue : Value)
    (targetStore nextStore : Wasm.Store Host)
    (targetLocals nextLocals : Wasm.Locals) (resultIndex : Nat)
    (witness nextWitness : RefinementWitness) : Prop :=
  FirTalos.Correctness.SourceCallLetResult context externals sourceRuntime
      sourceEnv decl continuation nextRuntime sourceValue ∧
    StateRelated sourceFunction sourceRuntime sourceEnv targetStore targetLocals
      witness ∧
    StateRelated sourceFunction nextRuntime
      (bind sourceEnv decl.fvarId sourceValue) nextStore nextLocals nextWitness ∧
    ∀ (rest : Wasm.Program) (Q : Wasm.Assertion Host)
        (tail : List Wasm.Value),
      Wasm.wp module rest Q nextStore { nextLocals with values := tail } hostEnv →
      Wasm.wp module (targetValue ++ .localSet resultIndex :: rest) Q
        targetStore { targetLocals with values := tail } hostEnv

/-- Recursive concrete `CodeWP` rule for a terminating interprocedural call
prefix. The operation-specific proof may grow the representation witness. -/
theorem codeWP_callLet
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {externals : ExternalImpl}
    {sourceRuntime nextRuntime : RuntimeState} {sourceEnv : Env}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {sourceValue : Value} {valueCode : List Fir.Wasm.Instruction}
    {targetValue targetRest : Wasm.Program}
    {targetStore nextStore : Wasm.Store Host}
    {targetLocals nextLocals : Wasm.Locals} {resultIndex : Nat}
    {witness nextWitness : RefinementWitness}
    {tail : List Wasm.Value} {Q : Wasm.Assertion Host}
    (valueCompiled : Fir.Wasm.compileLetValue context decl = .ok valueCode)
    (valueAdapted :
      instructions sourceModule sourceFunction labels valueCode = .ok targetValue)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (step : CallLetStepSimulates context sourceFunction module hostEnv externals
      decl continuation targetValue sourceRuntime nextRuntime sourceEnv
      sourceValue targetStore nextStore targetLocals nextLocals resultIndex
      witness nextWitness)
    (continued :
      CodeWP context sourceModule sourceFunction labels module hostEnv
        nextRuntime (bind sourceEnv decl.fvarId sourceValue) continuation
        targetRest nextStore nextLocals nextWitness tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv (.let decl continuation)
      (targetValue ++ .localSet resultIndex :: targetRest)
      targetStore targetLocals witness tail Q := by
  rcases step with ⟨_, initialRelated, _, stepWP⟩
  rcases continued with ⟨continuationAdapted, _, continuedWP⟩
  refine ⟨codeAdapted_let valueCompiled valueAdapted resultFound
      continuationAdapted, initialRelated, ?_⟩
  exact stepWP targetRest Q tail continuedWP

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

/-- Host-polymorphic generated `local.get` sequence. Constructor allocation is
the first concrete W6 operation with an arbitrary number of operands. -/
theorem wp_localGets
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {rest : Wasm.Program} {Q : Wasm.Assertion host}
    {store : Wasm.Store host} {locals : Wasm.Locals}
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
  | nil => simpa using continued
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

theorem wp_usizeProjection_let
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion Host}
    {initial : Wasm.Store Host} {locals updated : Wasm.Locals}
    {objectIndex resultIndex : Nat} {objectWord : Word32}
    {witness : RefinementWitness} {runtime : RuntimeState}
    {sourceObject : Value} {info : Lean.Compiler.LCNF.CtorInfo}
    {fieldKinds : Array AbiKind} {index : Nat} {value : UInt64}
    (tail : List Wasm.Value)
    (hObject :
      locals.get objectIndex = some (.i32 (UInt32.ofNat objectWord.value)))
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (usizeProjContract index))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (runtimeRelated :
      ConcreteRuntimeRel initial.host.runtime witness runtime)
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (descriptor : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (projected : getUSizeField runtime sourceObject index = .ok (.usize value))
    (hSet : locals.set? resultIndex (.i64 value) = some updated)
    (continued :
      Wasm.wp module rest Q (clearFailure initial)
        { updated with values := tail } env) :
    Wasm.wp module
      (.localGet objectIndex :: .call id :: .localSet resultIndex :: rest)
      Q initial { locals with values := tail } env := by
  obtain ⟨_, operation, _⟩ :=
    usizeProjStep_of_refines runtimeRelated objectRelated descriptor projected
  have hObjectTail :
      ({ locals with values := tail } : Wasm.Locals).get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)) := by
    simpa [Wasm.Locals.get] using hObject
  rw [Wasm.wp_localGet_cons, hObjectTail]
  apply wp_exact_host_call_of_return
    (step := usizeProjStep index)
    (physicalArgs := [.i32 (UInt32.ofNat objectWord.value)])
    (results := [.i64 value]) hImp hSat hi hContract
  · simp [hParams]
  · exact operation
  · simpa [hParams, hResults] using
      FirTalos.Concrete.wp_localSet_of_set (host := Host) hSet continued

theorem wp_scalarProjection_let
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion Host}
    {initial : Wasm.Store Host} {locals updated : Wasm.Locals}
    {objectIndex resultIndex : Nat} {objectWord : Word32}
    {width offset : Nat} {kind : AbiKind} {physical : Wasm.Value}
    (tail : List Wasm.Value)
    (hObject :
      locals.get objectIndex = some (.i32 (UInt32.ofNat objectWord.value)))
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract :
      spec.contracts[id]? = some (scalarProjContract width offset kind))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (operation :
      scalarProjStep width offset kind initial
          [.i32 (UInt32.ofNat objectWord.value)] =
        .Return [physical] (clearFailure initial))
    (hSet : locals.set? resultIndex physical = some updated)
    (continued :
      Wasm.wp module rest Q (clearFailure initial)
        { updated with values := tail } env) :
    Wasm.wp module
      (.localGet objectIndex :: .call id :: .localSet resultIndex :: rest)
      Q initial { locals with values := tail } env := by
  have hObjectTail :
      ({ locals with values := tail } : Wasm.Locals).get objectIndex =
        some (.i32 (UInt32.ofNat objectWord.value)) := by
    simpa [Wasm.Locals.get] using hObject
  rw [Wasm.wp_localGet_cons, hObjectTail]
  apply wp_exact_host_call_of_return
    (step := scalarProjStep width offset kind)
    (physicalArgs := [.i32 (UInt32.ofNat objectWord.value)])
    (results := [physical]) hImp hSat hi hContract
  · simp [hParams]
  · exact operation
  · simpa [hParams, hResults] using
      FirTalos.Concrete.wp_localSet_of_set (host := Host) hSet continued

theorem wp_naturalLiteral_let
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion Host}
    {initial nextStore : Wasm.Store Host} {locals updated : Wasm.Locals}
    {resultIndex : Nat} {value : Nat} {word : Word32}
    (tail : List Wasm.Value)
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (naturalLiteralContract value))
    (hParams : imp.params.length = 0)
    (hResults : imp.results.length = 1)
    (operation : naturalLiteralStep value initial [] =
      .Return [.i32 (UInt32.ofNat word.value)] nextStore)
    (hSet :
      locals.set? resultIndex (.i32 (UInt32.ofNat word.value)) = some updated)
    (continued :
      Wasm.wp module rest Q nextStore { updated with values := tail } env) :
    Wasm.wp module (.call id :: .localSet resultIndex :: rest)
      Q initial { locals with values := tail } env := by
  apply wp_exact_host_call_of_return
    (step := naturalLiteralStep value) (physicalArgs := [])
    (results := [.i32 (UInt32.ofNat word.value)]) hImp hSat hi hContract
  · simp [hParams]
  · exact operation
  · simpa [hParams, hResults] using
      FirTalos.Concrete.wp_localSet_of_set (host := Host) hSet continued

/-- Concrete-host WP for the exact arbitrary-arity constructor sequence
emitted by the lowerer. -/
theorem wp_allocCtor_let
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion Host}
    {initial nextStore : Wasm.Store Host} {locals updated : Wasm.Locals}
    {indices : List Nat} {physicalArgs : List Wasm.Value}
    {resultIndex : Nat} {info : Lean.Compiler.LCNF.CtorInfo}
    {fieldKinds : Array AbiKind} {resultKind : AbiKind} {word : Word32}
    (tail : List Wasm.Value)
    (hGets : List.Forall₂
      (fun index value => locals.get index = some value) indices physicalArgs)
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (allocCtorContract info fieldKinds resultKind))
    (hParams : imp.params.length = physicalArgs.length)
    (hResults : imp.results.length = 1)
    (operation : allocCtorStep info fieldKinds resultKind initial physicalArgs =
      .Return [.i32 (UInt32.ofNat word.value)] nextStore)
    (hSet : locals.set? resultIndex (.i32 (UInt32.ofNat word.value)) =
      some updated)
    (continued :
      Wasm.wp module rest Q nextStore { updated with values := tail } env) :
    Wasm.wp module
      (indices.map Wasm.Instruction.localGet ++
        .call id :: .localSet resultIndex :: rest)
      Q initial { locals with values := tail } env := by
  apply wp_localGets tail hGets
  apply wp_exact_host_call_of_return
    (step := allocCtorStep info fieldKinds resultKind)
    (physicalArgs := physicalArgs)
    (results := [.i32 (UInt32.ofNat word.value)]) hImp hSat hi hContract
  · simp [hParams]
  · exact operation
  · simpa [hParams, hResults] using
      FirTalos.Concrete.wp_localSet_of_set (host := Host) hSet continued

/-- Concrete-host WP for the value-preserving cache update call. -/
theorem wp_cacheSet_call
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion Host}
    {initial after : Wasm.Store Host} {locals : Wasm.Locals}
    {declaration : Lean.Name} {kind : AbiKind} {physical : Wasm.Value}
    {tail : List Wasm.Value}
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (cacheSetContract declaration kind))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (operation : cacheSetStep declaration kind initial [physical] =
      .Return [physical] after)
    (continued : Wasm.wp module rest Q after
      { locals with values := physical :: tail } env) :
    Wasm.wp module (.call id :: rest) Q initial
      { locals with values := physical :: tail } env := by
  apply wp_exact_host_call_of_return
    (step := cacheSetStep declaration kind) (physicalArgs := [physical])
    (results := [physical]) hImp hSat hi hContract
  · simp [hParams]
  · exact operation
  · simpa [hParams, hResults] using continued

/-- Atomic store update performed by one generated Wasm `global.set`. -/
def writeWasmGlobal (store : Wasm.Store Host) (index : Nat)
    (value : Wasm.Value) : Wasm.Store Host :=
  { store with globals := { globals := store.globals.globals.set index value } }

/-- Exact generated cache-write suffix after a lazy declaration has left its
result on the operand stack. The host cache and the two physical Wasm globals
are updated in their distinct stores. -/
theorem wp_cacheSet_miss_suffix
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion Host}
    {initial afterCache valueStore : Wasm.Store Host} {locals : Wasm.Locals}
    {declaration : Lean.Name} {kind : AbiKind} {physical : Wasm.Value}
    {valueIndex flagIndex : Nat} {oldValue oldFlag : Wasm.Value}
    {tail : List Wasm.Value}
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (cacheSetContract declaration kind))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (operation : cacheSetStep declaration kind initial [physical] =
      .Return [physical] afterCache)
    (hValue : afterCache.globals.globals[valueIndex]? = some oldValue)
    (valueStoreEq : valueStore = writeWasmGlobal afterCache valueIndex physical)
    (hFlag : valueStore.globals.globals[flagIndex]? = some oldFlag)
    (continued : Wasm.wp module rest Q
      (writeWasmGlobal valueStore flagIndex (.i32 1))
      { locals with values := tail } env) :
    Wasm.wp module
      (.call id :: .globalSet valueIndex :: .const 1 ::
        .globalSet flagIndex :: rest)
      Q initial { locals with values := physical :: tail } env := by
  subst valueStore
  apply wp_cacheSet_call hImp hSat hi hContract hParams hResults operation
  rw [Wasm.wp_globalSet_cons, hValue]
  change Wasm.wp module (.const 1 :: .globalSet flagIndex :: rest) Q
    (writeWasmGlobal afterCache valueIndex physical)
    { locals with values := tail } env
  rw [Wasm.wp_const_cons, Wasm.wp_globalSet_cons, hFlag]
  exact continued

/-- Concrete-host WP for the arbitrary-arity partial-application allocation
and destination-local write emitted by the lowerer. -/
theorem wp_partialApply_let
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion Host}
    {initial nextStore : Wasm.Store Host} {locals updated : Wasm.Locals}
    {indices : List Nat} {physicalArgs : List Wasm.Value}
    {resultIndex : Nat} {function : Lean.Name} {arity fixed : Nat}
    {fieldKinds : Array AbiKind} {resultKind : AbiKind} {word : Word32}
    {tail : List Wasm.Value}
    (hGets : List.Forall₂
      (fun index value => locals.get index = some value) indices physicalArgs)
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
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
      { updated with values := tail } env) :
    Wasm.wp module
      (indices.map Wasm.Instruction.localGet ++
        .call id :: .localSet resultIndex :: rest)
      Q initial { locals with values := tail } env := by
  apply wp_localGets tail hGets
  apply wp_exact_host_call_of_return
    (step := partialApplyStep function arity fixed fieldKinds resultKind)
    (physicalArgs := physicalArgs)
    (results := [.i32 (UInt32.ofNat word.value)]) hImp hSat hi hContract
  · simp [hParams]
  · exact operation
  · simpa [hParams, hResults] using
      FirTalos.Concrete.wp_localSet_of_set (host := Host) hSet continued

/-- Exact generated closure-matcher prefix. The returned i32 discriminator is
left on the operand stack for the following generated `if`. -/
theorem wp_closureMatches
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion Host}
    {initial : Wasm.Store Host} {locals : Wasm.Locals}
    {closureIndex : Nat} {address : Word32} {matched : UInt32}
    {function : Lean.Name} {arity fixed : Nat} {tail : List Wasm.Value}
    (hClosure : locals.get closureIndex =
      some (.i32 (UInt32.ofNat address.value)))
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (closureMatchesContract function arity fixed))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (operation : closureMatchesStep function arity fixed initial
        [.i32 (UInt32.ofNat address.value)] =
      .Return [.i32 matched] (clearFailure initial))
    (continued : Wasm.wp module rest Q (clearFailure initial)
      { locals with values := .i32 matched :: tail } env) :
    Wasm.wp module (.localGet closureIndex :: .call id :: rest) Q initial
      { locals with values := tail } env := by
  have hClosureTail :
      ({ locals with values := tail } : Wasm.Locals).get closureIndex =
        some (.i32 (UInt32.ofNat address.value)) := by
    simpa [Wasm.Locals.get] using hClosure
  rw [Wasm.wp_localGet_cons, hClosureTail]
  apply wp_exact_host_call_of_return
    (step := closureMatchesStep function arity fixed)
    (physicalArgs := [.i32 (UInt32.ofNat address.value)])
    (results := [.i32 matched]) hImp hSat hi hContract
  · simp [hParams]
  · exact operation
  · simpa [hParams, hResults] using continued

/-- One generated closure-dispatch candidate: execute the concrete matcher,
select the candidate body or remaining chain from its direct i32 result, and
reconnect normal block exit to the surrounding instruction suffix. -/
theorem wp_closureCandidate
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {thenBody elseBody rest : Wasm.Program} {Q : Wasm.Assertion Host}
    {initial : Wasm.Store Host} {locals : Wasm.Locals}
    {closureIndex : Nat} {address : Word32} {matched : UInt32}
    {function : Lean.Name} {arity fixed : Nat} {tail : List Wasm.Value}
    (hClosure : locals.get closureIndex =
      some (.i32 (UInt32.ofNat address.value)))
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (closureMatchesContract function arity fixed))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (operation : closureMatchesStep function arity fixed initial
        [.i32 (UInt32.ofNat address.value)] =
      .Return [.i32 matched] (clearFailure initial))
    (selected :
      Wasm.wp module (if matched != 0 then thenBody else elseBody)
        (fun continuation => match continuation with
          | .Fallthrough nextStore nextLocals =>
              Wasm.wp module rest Q nextStore
                { nextLocals with values := tail } env
          | .Break 0 nextStore nextLocals =>
              Wasm.wp module rest Q nextStore
                { nextLocals with values := tail } env
          | .Break (level + 1) nextStore nextLocals =>
              Q (.Break level nextStore nextLocals)
          | other => Q other)
        (clearFailure initial) { locals with values := tail } env) :
    Wasm.wp module
      (.localGet closureIndex :: .call id ::
        .iff 0 0 thenBody elseBody :: rest)
      Q initial { locals with values := tail } env := by
  apply wp_closureMatches hClosure hImp hSat hi hContract hParams hResults
    operation
  apply Wasm.wp_iff_cons (c := matched) (vs := tail) rfl
  convert selected using 1
  all_goals simp
  all_goals
    funext continuation
    cases continuation with
    | Break level nextStore nextLocals => cases level <;> rfl
    | _ => rfl

/-- Exact ordinary-Wasm direct-call and destination-local boundary. The
callee proof is fuel-free and store-specific, so recursive proofs may supply
their own well-founded specification without a semantic host callback. -/
theorem wp_directCall_let
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {functionIndex resultIndex : Nat} {rest : Wasm.Program}
    {Q : Wasm.Assertion Host} {initial nextStore : Wasm.Store Host}
    {locals updated : Wasm.Locals} {physicalArgs : List Wasm.Value}
    {physicalResult : Wasm.Value} {tail : List Wasm.Value}
    (called : Wasm.TerminatesWith env module functionIndex initial
      (physicalArgs.reverse ++ tail)
      (fun final results =>
        final = nextStore ∧ results = physicalResult :: tail))
    (targetSet : locals.set? resultIndex physicalResult = some updated)
    (continued : Wasm.wp module rest Q nextStore
      { updated with values := tail } env) :
    Wasm.wp module (.call functionIndex :: .localSet resultIndex :: rest) Q
      initial { locals with values := physicalArgs.reverse ++ tail } env := by
  apply Wasm.wp_call_tw called
  intro final results post
  rcases post with ⟨finalEq, resultsEq⟩
  subst final
  subst results
  change Wasm.wp module (.localSet resultIndex :: rest) Q nextStore
    { locals with values := physicalResult :: tail } env
  exact wp_localSet_of_set targetSet continued

/-- Exact generated typed-capture projection prefix. It leaves the projected
lane on the operand stack for the subsequent argument sequence/direct call. -/
theorem wp_closureProj
    {module : Wasm.Module} {env : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {rest : Wasm.Program} {Q : Wasm.Assertion Host}
    {initial : Wasm.Store Host} {locals : Wasm.Locals}
    {closureIndex : Nat} {address : Word32} {physical : Wasm.Value}
    {function : Lean.Name} {arity fixed index : Nat} {kind : AbiKind}
    {tail : List Wasm.Value}
    (hClosure : locals.get closureIndex =
      some (.i32 (UInt32.ofNat address.value)))
    (hImp : module.imports[id]? = some imp)
    (hSat : env.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (closureProjContract function arity fixed index kind))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (operation : closureProjStep function arity fixed index kind initial
        [.i32 (UInt32.ofNat address.value)] =
      .Return [physical] (clearFailure initial))
    (continued : Wasm.wp module rest Q (clearFailure initial)
      { locals with values := physical :: tail } env) :
    Wasm.wp module (.localGet closureIndex :: .call id :: rest) Q initial
      { locals with values := tail } env := by
  have hClosureTail :
      ({ locals with values := tail } : Wasm.Locals).get closureIndex =
        some (.i32 (UInt32.ofNat address.value)) := by
    simpa [Wasm.Locals.get] using hClosure
  rw [Wasm.wp_localGet_cons, hClosureTail]
  apply wp_exact_host_call_of_return
    (step := closureProjStep function arity fixed index kind)
    (physicalArgs := [.i32 (UInt32.ofNat address.value)])
    (results := [physical]) hImp hSat hi hContract
  · simp [hParams]
  · exact operation
  · simpa [hParams, hResults] using continued

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

theorem letStepSimulates_usizeProjection
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure} {sourceEnv : Env}
    {index : Nat} {objectId : Lean.FVarId}
    {initial : Wasm.Store Host} {locals updated : Wasm.Locals}
    {objectIndex resultIndex : Nat} {objectWord : Word32}
    {sourceObject : Value} {value : UInt64} {sourceRuntime : RuntimeState}
    {witness : RefinementWitness} {info : Lean.Compiler.LCNF.CtorInfo}
    {fieldKinds : Array AbiKind}
    (valueEq : decl.value = .uproj index objectId)
    (sourceLookup : lookup sourceEnv objectId = some sourceObject)
    (projected : getUSizeField sourceRuntime sourceObject index =
      .ok (.usize value))
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some .usize)
    (hObject :
      locals.get objectIndex = some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (descriptor : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (usizeProjContract index))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (targetSet : locals.set? resultIndex (.i64 value) = some updated) :
    LetStepSimulates context sourceFunction module hostEnv decl
      [.localGet objectIndex, .call id]
      sourceRuntime sourceRuntime sourceEnv (.usize value) initial
      (clearFailure initial) locals updated resultIndex witness witness := by
  obtain ⟨_, valueRelated⟩ :=
    FirTalos.Concrete.ConcreteRuntimeRel.readUSizeField_refines
      initialRelated.1 objectRelated descriptor projected
  refine ⟨?_, initialRelated,
    initialRelated.bindWord64 resultFound resultKindAt valueRelated targetSet,
    ?_⟩
  · unfold FirTalos.Correctness.SourceLetResult
    simp [evalLetValue, valueEq]
    have objectLookup : lookupValue sourceEnv objectId = .ok sourceObject := by
      simp [lookupValue, sourceLookup]
    rw [objectLookup]
    change ((fun projectedValue : Value =>
      (sourceRuntime, LetAction.value projectedValue)) <$>
        getUSizeField sourceRuntime sourceObject index) =
      .ok (sourceRuntime, .value (.usize value))
    rw [projected]
    rfl
  · intro rest Q tail continued
    exact wp_usizeProjection_let tail hObject hImp hSat hi hContract hParams
      hResults initialRelated.1 objectRelated descriptor projected targetSet
      continued

theorem codeWP_usizeProjection_let
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure} {sourceEnv : Env}
    {index : Nat} {objectId : Lean.FVarId}
    {initial : Wasm.Store Host} {locals updated : Wasm.Locals}
    {objectIndex resultIndex : Nat} {objectWord : Word32}
    {sourceObject : Value} {value : UInt64} {sourceRuntime : RuntimeState}
    {witness : RefinementWitness} {info : Lean.Compiler.LCNF.CtorInfo}
    {fieldKinds : Array AbiKind} {targetRest : Wasm.Program}
    {tail : List Wasm.Value} {Q : Wasm.Assertion Host}
    (valueEq : decl.value = .uproj index objectId)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.localGet objectId, .call (.runtime (.usizeProj index))])
    (objectFound :
      findFVar? (functionBindings sourceFunction) objectId = some objectIndex)
    (callFound :
      callIndex? sourceModule (.runtime (.usizeProj index)) = some id)
    (sourceLookup : lookup sourceEnv objectId = some sourceObject)
    (projected : getUSizeField sourceRuntime sourceObject index =
      .ok (.usize value))
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd = some .usize)
    (hObject :
      locals.get objectIndex = some (.i32 (UInt32.ofNat objectWord.value)))
    (objectRelated :
      ValueRel witness .tobject (.word32 objectWord) sourceObject)
    (descriptor : witness.descriptors.lookup? objectWord =
      some (.constructor info fieldKinds))
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (usizeProjContract index))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (targetSet : locals.set? resultIndex (.i64 value) = some updated)
    (continued :
      CodeWP context sourceModule sourceFunction labels module hostEnv
        sourceRuntime (bind sourceEnv decl.fvarId (.usize value)) continuation
        targetRest (clearFailure initial) updated witness tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv (.let decl continuation)
      (.localGet objectIndex :: .call id :: .localSet resultIndex :: targetRest)
      initial locals witness tail Q := by
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          [.localGet objectId, .call (.runtime (.usizeProj index))] =
        .ok [.localGet objectIndex, .call id] := by
    have objectFound' :
        findFVar? (sourceFunction.params.toList ++ sourceFunction.locals.toList)
          objectId = some objectIndex := by
      simpa [functionBindings] using objectFound
    simp [instructions, instruction, objectFound', callFound]
    rfl
  have step := letStepSimulates_usizeProjection (context := context)
    valueEq sourceLookup projected initialRelated resultFound resultKindAt
    hObject objectRelated descriptor hImp hSat hi hContract hParams hResults
    targetSet
  rcases step with ⟨_, stepInitial, _, stepWP⟩
  rcases continued with ⟨continuationAdapted, _, continuedWP⟩
  refine ⟨codeAdapted_let valueCompiled valueAdapted resultFound
      continuationAdapted, stepInitial, ?_⟩
  exact stepWP targetRest Q tail continuedWP

theorem letStepSimulates_scalarProjection
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure} {sourceEnv : Env}
    {width offset : Nat} {objectId : Lean.FVarId}
    {initial : Wasm.Store Host} {locals updated : Wasm.Locals}
    {objectIndex resultIndex : Nat} {objectWord : Word32}
    {sourceObject sourceValue : Value} {resultKind : AbiKind}
    {physical : Wasm.Value} {sourceRuntime : RuntimeState}
    {witness : RefinementWitness}
    (valueEq : decl.value = .sproj width offset objectId)
    (sourceLookup : lookup sourceEnv objectId = some sourceObject)
    (projected : getScalarField sourceRuntime sourceObject width offset =
      .ok sourceValue)
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some resultKind)
    (hObject :
      locals.get objectIndex = some (.i32 (UInt32.ofNat objectWord.value)))
    (physicalRelated :
      PhysicalValueRel witness resultKind physical sourceValue)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (scalarProjContract width offset resultKind))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (operation :
      scalarProjStep width offset resultKind initial
          [.i32 (UInt32.ofNat objectWord.value)] =
        .Return [physical] (clearFailure initial))
    (targetSet : locals.set? resultIndex physical = some updated) :
    LetStepSimulates context sourceFunction module hostEnv decl
      [.localGet objectIndex, .call id]
      sourceRuntime sourceRuntime sourceEnv sourceValue initial
      (clearFailure initial) locals updated resultIndex witness witness := by
  refine ⟨?_, initialRelated,
    initialRelated.bindPhysical resultFound resultKindAt physicalRelated targetSet,
    ?_⟩
  · unfold FirTalos.Correctness.SourceLetResult
    simp [evalLetValue, valueEq]
    have objectLookup : lookupValue sourceEnv objectId = .ok sourceObject := by
      simp [lookupValue, sourceLookup]
    rw [objectLookup]
    change ((fun projectedValue : Value =>
      (sourceRuntime, LetAction.value projectedValue)) <$>
        getScalarField sourceRuntime sourceObject width offset) =
      .ok (sourceRuntime, .value sourceValue)
    rw [projected]
    rfl
  · intro rest Q tail continued
    exact wp_scalarProjection_let tail hObject hImp hSat hi hContract hParams
      hResults operation targetSet continued

theorem codeWP_scalarProjection_let
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure} {sourceEnv : Env}
    {width offset : Nat} {objectId : Lean.FVarId}
    {initial : Wasm.Store Host} {locals updated : Wasm.Locals}
    {objectIndex resultIndex : Nat} {objectWord : Word32}
    {sourceObject sourceValue : Value} {resultKind : AbiKind}
    {physical : Wasm.Value} {sourceRuntime : RuntimeState}
    {witness : RefinementWitness} {targetRest : Wasm.Program}
    {tail : List Wasm.Value} {Q : Wasm.Assertion Host}
    (valueEq : decl.value = .sproj width offset objectId)
    (valueCompiled :
      Fir.Wasm.compileLetValue context decl =
        .ok [.localGet objectId,
          .call (.runtime (.scalarProj width offset resultKind))])
    (objectFound :
      findFVar? (functionBindings sourceFunction) objectId = some objectIndex)
    (callFound : callIndex? sourceModule
      (.runtime (.scalarProj width offset resultKind)) = some id)
    (sourceLookup : lookup sourceEnv objectId = some sourceObject)
    (projected : getScalarField sourceRuntime sourceObject width offset =
      .ok sourceValue)
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some resultKind)
    (hObject :
      locals.get objectIndex = some (.i32 (UInt32.ofNat objectWord.value)))
    (physicalRelated :
      PhysicalValueRel witness resultKind physical sourceValue)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (scalarProjContract width offset resultKind))
    (hParams : imp.params.length = 1)
    (hResults : imp.results.length = 1)
    (operation :
      scalarProjStep width offset resultKind initial
          [.i32 (UInt32.ofNat objectWord.value)] =
        .Return [physical] (clearFailure initial))
    (targetSet : locals.set? resultIndex physical = some updated)
    (continued :
      CodeWP context sourceModule sourceFunction labels module hostEnv
        sourceRuntime (bind sourceEnv decl.fvarId sourceValue) continuation
        targetRest (clearFailure initial) updated witness tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv (.let decl continuation)
      (.localGet objectIndex :: .call id :: .localSet resultIndex :: targetRest)
      initial locals witness tail Q := by
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          [.localGet objectId,
            .call (.runtime (.scalarProj width offset resultKind))] =
        .ok [.localGet objectIndex, .call id] := by
    have objectFound' :
        findFVar? (sourceFunction.params.toList ++ sourceFunction.locals.toList)
          objectId = some objectIndex := by
      simpa [functionBindings] using objectFound
    simp [instructions, instruction, objectFound', callFound]
    rfl
  have step := letStepSimulates_scalarProjection (context := context)
    valueEq sourceLookup projected initialRelated resultFound resultKindAt
    hObject physicalRelated hImp hSat hi hContract hParams hResults operation
    targetSet
  rcases step with ⟨_, stepInitial, _, stepWP⟩
  rcases continued with ⟨continuationAdapted, _, continuedWP⟩
  refine ⟨codeAdapted_let valueCompiled valueAdapted resultFound
      continuationAdapted, stepInitial, ?_⟩
  exact stepWP targetRest Q tail continuedWP

/-- Constructor-allocation instance of the concrete direct-`let` boundary.
The operation-specific refinement supplies the grown runtime witness; this
rule composes it with source evaluation, generated locals, and Talos WP. -/
theorem letStepSimulates_constructor
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {info : Lean.Compiler.LCNF.CtorInfo}
    {args : Array (Lean.Compiler.LCNF.Arg .impure)} {sourceEnv : Env}
    {initial nextStore : Wasm.Store Host} {locals updated : Wasm.Locals}
    {indices : List Nat} {physicalArgs : List Wasm.Value}
    {semanticArgs : Array Value} {sourceRuntime nextRuntime : RuntimeState}
    {sourceValue : Value} {resultIndex : Nat} {word : Word32}
    {fieldKinds : Array AbiKind} {resultKind : AbiKind}
    {witness nextWitness : RefinementWitness}
    (valueEq : decl.value = .ctor info args)
    (evaluated : evalArgs sourceEnv args = .ok semanticArgs)
    (semanticStep :
      allocCtor sourceRuntime info semanticArgs =
        .ok (nextRuntime, sourceValue))
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some resultKind)
    (hGets : List.Forall₂
      (fun index physical => locals.get index = some physical)
      indices physicalArgs)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (allocCtorContract info fieldKinds resultKind))
    (hParams : imp.params.length = physicalArgs.length)
    (hResults : imp.results.length = 1)
    (operation : allocCtorStep info fieldKinds resultKind initial physicalArgs =
      .Return [.i32 (UInt32.ofNat word.value)] nextStore)
    (extension : witness.Extends nextWitness)
    (nextRuntimeRelated :
      ConcreteRuntimeRel nextStore.host.runtime nextWitness nextRuntime)
    (failureClear : nextStore.host.failure? = none)
    (valueRelated : PhysicalValueRel nextWitness resultKind
      (.i32 (UInt32.ofNat word.value)) sourceValue)
    (targetSet : locals.set? resultIndex
      (.i32 (UInt32.ofNat word.value)) = some updated) :
    LetStepSimulates context sourceFunction module hostEnv decl
      (indices.map Wasm.Instruction.localGet ++ [.call id])
      sourceRuntime nextRuntime sourceEnv sourceValue initial nextStore
      locals updated resultIndex witness nextWitness := by
  refine ⟨?_, initialRelated,
    initialRelated.bindAfter extension nextRuntimeRelated failureClear
      resultFound resultKindAt valueRelated targetSet,
    ?_⟩
  · unfold FirTalos.Correctness.SourceLetResult
    simp [evalLetValue, valueEq, evaluated]
    change ((fun result : RuntimeState × Value =>
      (result.1, LetAction.value result.2)) <$>
        allocCtor sourceRuntime info semanticArgs) =
      .ok (nextRuntime, .value sourceValue)
    rw [semanticStep]
    rfl
  · intro rest Q tail continued
    simpa [List.append_assoc] using
      wp_allocCtor_let tail hGets hImp hSat hi hContract hParams hResults
        operation targetSet continued

/-- Recursive source/compiler/Talos rule for a concrete constructor `let`. -/
theorem codeWP_constructor_let
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {info : Lean.Compiler.LCNF.CtorInfo}
    {args : Array (Lean.Compiler.LCNF.Arg .impure)} {sourceEnv : Env}
    {initial nextStore : Wasm.Store Host} {locals updated : Wasm.Locals}
    {fvarIds : List Lean.FVarId} {indices : List Nat}
    {physicalArgs : List Wasm.Value} {semanticArgs : Array Value}
    {sourceRuntime nextRuntime : RuntimeState} {sourceValue : Value}
    {resultIndex : Nat}
    {word : Word32} {fieldKinds : Array AbiKind} {resultKind : AbiKind}
    {witness nextWitness : RefinementWitness}
    {targetRest : Wasm.Program} {tail : List Wasm.Value}
    {Q : Wasm.Assertion Host}
    (valueEq : decl.value = .ctor info args)
    (valueCompiled : Fir.Wasm.compileLetValue context decl =
      .ok (fvarIds.map Fir.Wasm.Instruction.localGet ++
        [.call (.runtime (.allocCtor info fieldKinds resultKind))]))
    (argumentsFound : List.Forall₂
      (fun fvarId index =>
        findFVar? (functionBindings sourceFunction) fvarId = some index)
      fvarIds indices)
    (callFound : callIndex? sourceModule
      (.runtime (.allocCtor info fieldKinds resultKind)) = some id)
    (evaluated : evalArgs sourceEnv args = .ok semanticArgs)
    (semanticStep : allocCtor sourceRuntime info semanticArgs =
      .ok (nextRuntime, sourceValue))
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some resultKind)
    (hGets : List.Forall₂
      (fun index physical => locals.get index = some physical)
      indices physicalArgs)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (allocCtorContract info fieldKinds resultKind))
    (hParams : imp.params.length = physicalArgs.length)
    (hResults : imp.results.length = 1)
    (operation : allocCtorStep info fieldKinds resultKind initial physicalArgs =
      .Return [.i32 (UInt32.ofNat word.value)] nextStore)
    (extension : witness.Extends nextWitness)
    (nextRuntimeRelated :
      ConcreteRuntimeRel nextStore.host.runtime nextWitness nextRuntime)
    (failureClear : nextStore.host.failure? = none)
    (valueRelated : PhysicalValueRel nextWitness resultKind
      (.i32 (UInt32.ofNat word.value)) sourceValue)
    (targetSet : locals.set? resultIndex
      (.i32 (UInt32.ofNat word.value)) = some updated)
    (continued : CodeWP context sourceModule sourceFunction labels module hostEnv
      nextRuntime (bind sourceEnv decl.fvarId sourceValue) continuation
      targetRest nextStore updated nextWitness tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv (.let decl continuation)
      (indices.map Wasm.Instruction.localGet ++
        .call id :: .localSet resultIndex :: targetRest)
      initial locals witness tail Q := by
  have argumentsAdapted := FirTalos.Correctness.instructions_localGets
    (sourceModule := sourceModule) (sourceFunction := sourceFunction)
    (labels := labels) (found := by
      simpa [functionBindings] using argumentsFound)
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          (fvarIds.map Fir.Wasm.Instruction.localGet ++
            [.call (.runtime (.allocCtor info fieldKinds resultKind))]) =
        .ok (indices.map Wasm.Instruction.localGet ++ [.call id]) := by
    rw [FirTalos.Correctness.instructions_append, argumentsAdapted]
    simp [instructions, instruction, callFound]
  have step := letStepSimulates_constructor (context := context) valueEq
    evaluated semanticStep initialRelated resultFound resultKindAt hGets hImp
    hSat hi hContract hParams hResults operation extension nextRuntimeRelated
    failureClear valueRelated targetSet
  rcases step with ⟨_, stepInitial, _, stepWP⟩
  rcases continued with ⟨continuationAdapted, _, continuedWP⟩
  have adapted := codeAdapted_let valueCompiled valueAdapted resultFound
    continuationAdapted
  refine ⟨?_, stepInitial, ?_⟩
  · simpa only [List.append_assoc, List.singleton_append] using adapted
  · simpa only [List.append_assoc, List.singleton_append] using
      stepWP targetRest Q tail continuedWP

/-- Partial-application instance of the concrete direct-`let` boundary.  The
source interpreter and concrete runtime allocate the same closure at the next
semantic/physical heap locations, respectively; the operation refinement
supplies the grown witness relating those locations. -/
theorem letStepSimulates_partialApply
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {function : Lean.Name} {target : Lean.Compiler.LCNF.Decl .impure}
    {args : Array (Lean.Compiler.LCNF.Arg .impure)} {sourceEnv : Env}
    {initial nextStore : Wasm.Store Host} {locals updated : Wasm.Locals}
    {indices : List Nat} {physicalArgs : List Wasm.Value}
    {semanticArgs : Array Value} {sourceRuntime : RuntimeState}
    {resultIndex : Nat} {word : Word32}
    {fieldKinds : Array AbiKind} {resultKind : AbiKind}
    {witness nextWitness : RefinementWitness}
    (valueEq : decl.value = .pap function args)
    (evaluated : evalArgs sourceEnv args = .ok semanticArgs)
    (targetFound : context.program.findDecl? function = some target)
    (semanticLt : semanticArgs.size < target.params.size)
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some resultKind)
    (hGets : List.Forall₂
      (fun index physical => locals.get index = some physical)
      indices physicalArgs)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (partialApplyContract function target.params.size args.size
        fieldKinds resultKind))
    (hParams : imp.params.length = physicalArgs.length)
    (hResults : imp.results.length = 1)
    (operation : partialApplyStep function target.params.size args.size
      fieldKinds resultKind initial physicalArgs =
        .Return [.i32 (UInt32.ofNat word.value)] nextStore)
    (extension : witness.Extends nextWitness)
    (nextRuntimeRelated :
      ConcreteRuntimeRel nextStore.host.runtime nextWitness
        (semanticClosureResult sourceRuntime function target.params.size
          semanticArgs))
    (failureClear : nextStore.host.failure? = none)
    (valueRelated : PhysicalValueRel nextWitness resultKind
      (.i32 (UInt32.ofNat word.value))
      (.object (.heap sourceRuntime.nextLocation)))
    (targetSet : locals.set? resultIndex
      (.i32 (UInt32.ofNat word.value)) = some updated) :
    LetStepSimulates context sourceFunction module hostEnv decl
      (indices.map Wasm.Instruction.localGet ++ [.call id])
      sourceRuntime
      (semanticClosureResult sourceRuntime function target.params.size
        semanticArgs)
      sourceEnv (.object (.heap sourceRuntime.nextLocation)) initial nextStore
      locals updated resultIndex witness nextWitness := by
  refine ⟨?_, initialRelated,
    initialRelated.bindAfter extension nextRuntimeRelated failureClear
      resultFound resultKindAt valueRelated targetSet,
    ?_⟩
  · unfold FirTalos.Correctness.SourceLetResult
    simp [evalLetValue, valueEq, evaluated, targetFound,
      alloc_closure_eq]
    change (if target.params.size ≤ semanticArgs.size then _ else _) = _
    rw [if_neg (Nat.not_le.mpr semanticLt)]
    rfl
  · intro rest Q tail continued
    simpa [List.append_assoc] using
      wp_partialApply_let (tail := tail) hGets hImp hSat hi hContract hParams
        hResults operation targetSet continued

/-- Recursive source/compiler/Talos rule for closure allocation by partial
application.  `argumentsAdapted` keeps this rule independent of which
supported LCNF argument forms produced the physical capture lanes. -/
theorem codeWP_partialApply_let
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure}
    {function : Lean.Name} {target : Lean.Compiler.LCNF.Decl .impure}
    {args : Array (Lean.Compiler.LCNF.Arg .impure)} {sourceEnv : Env}
    {initial nextStore : Wasm.Store Host} {locals updated : Wasm.Locals}
    {argumentCode : List Fir.Wasm.Instruction} {indices : List Nat}
    {physicalArgs : List Wasm.Value} {semanticArgs : Array Value}
    {sourceRuntime : RuntimeState} {resultIndex : Nat} {word : Word32}
    {fieldKinds : Array AbiKind} {resultKind : AbiKind}
    {witness nextWitness : RefinementWitness}
    {targetRest : Wasm.Program} {tail : List Wasm.Value}
    {Q : Wasm.Assertion Host}
    (valueEq : decl.value = .pap function args)
    (valueCompiled : Fir.Wasm.compileLetValue context decl =
      .ok (argumentCode ++ [
        .call (.runtime (.partialApply function target.params.size args.size
          fieldKinds resultKind))]))
    (argumentsAdapted :
      instructions sourceModule sourceFunction labels argumentCode =
        .ok (indices.map Wasm.Instruction.localGet))
    (callFound : callIndex? sourceModule
      (.runtime (.partialApply function target.params.size args.size
        fieldKinds resultKind)) = some id)
    (evaluated : evalArgs sourceEnv args = .ok semanticArgs)
    (targetFound : context.program.findDecl? function = some target)
    (semanticLt : semanticArgs.size < target.params.size)
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some resultKind)
    (hGets : List.Forall₂
      (fun index physical => locals.get index = some physical)
      indices physicalArgs)
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? =
      some (partialApplyContract function target.params.size args.size
        fieldKinds resultKind))
    (hParams : imp.params.length = physicalArgs.length)
    (hResults : imp.results.length = 1)
    (operation : partialApplyStep function target.params.size args.size
      fieldKinds resultKind initial physicalArgs =
        .Return [.i32 (UInt32.ofNat word.value)] nextStore)
    (extension : witness.Extends nextWitness)
    (nextRuntimeRelated :
      ConcreteRuntimeRel nextStore.host.runtime nextWitness
        (semanticClosureResult sourceRuntime function target.params.size
          semanticArgs))
    (failureClear : nextStore.host.failure? = none)
    (valueRelated : PhysicalValueRel nextWitness resultKind
      (.i32 (UInt32.ofNat word.value))
      (.object (.heap sourceRuntime.nextLocation)))
    (targetSet : locals.set? resultIndex
      (.i32 (UInt32.ofNat word.value)) = some updated)
    (continued : CodeWP context sourceModule sourceFunction labels module hostEnv
      (semanticClosureResult sourceRuntime function target.params.size
        semanticArgs)
      (bind sourceEnv decl.fvarId (.object (.heap sourceRuntime.nextLocation)))
      continuation targetRest nextStore updated nextWitness tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv (.let decl continuation)
      (indices.map Wasm.Instruction.localGet ++
        .call id :: .localSet resultIndex :: targetRest)
      initial locals witness tail Q := by
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          (argumentCode ++ [
            .call (.runtime (.partialApply function target.params.size args.size
              fieldKinds resultKind))]) =
        .ok (indices.map Wasm.Instruction.localGet ++ [.call id]) := by
    rw [FirTalos.Correctness.instructions_append, argumentsAdapted]
    simp [instructions, instruction, callFound]
  have step := letStepSimulates_partialApply (context := context) valueEq
    evaluated targetFound semanticLt initialRelated resultFound resultKindAt
    hGets hImp hSat hi hContract hParams hResults operation extension
    nextRuntimeRelated failureClear valueRelated targetSet
  rcases step with ⟨_, stepInitial, _, stepWP⟩
  rcases continued with ⟨continuationAdapted, _, continuedWP⟩
  have adapted := codeAdapted_let valueCompiled valueAdapted resultFound
    continuationAdapted
  refine ⟨?_, stepInitial, ?_⟩
  · simpa only [List.append_assoc, List.singleton_append] using adapted
  · simpa only [List.append_assoc, List.singleton_append] using
      stepWP targetRest Q tail continuedWP

theorem letStepSimulates_naturalLiteral
    {context : Fir.Wasm.Context} {sourceFunction : Fir.Wasm.Function}
    {module : Wasm.Module} {hostEnv : Wasm.HostEnv Host}
    {spec : Wasm.HostSpec Host} {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure} {sourceEnv : Env}
    {initial : Wasm.Store Host} {locals updated : Wasm.Locals}
    {resultIndex : Nat} {value : Nat} {heap : MemoryState} {word : Word32}
    {sourceRuntime : RuntimeState} {witness : RefinementWitness}
    (valueEq : decl.value = .lit (.nat value))
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some .tobject)
    (allocated : allocateNatural initial.host.runtime.heap value =
      .ok (heap, word))
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (naturalLiteralContract value))
    (hParams : imp.params.length = 0)
    (hResults : imp.results.length = 1)
    (targetSet :
      locals.set? resultIndex (.i32 (UInt32.ofNat word.value)) = some updated) :
    ∃ nextWitness,
      witness.Extends nextWitness ∧
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime nextWitness
        (literal sourceRuntime (.nat value)).1 ∧
      PhysicalValueRel nextWitness .tobject
        (.i32 (UInt32.ofNat word.value)) (literal sourceRuntime (.nat value)).2 ∧
      LetStepSimulates context sourceFunction module hostEnv decl [.call id]
        sourceRuntime (literal sourceRuntime (.nat value)).1 sourceEnv
        (literal sourceRuntime (.nat value)).2 initial (replaceHeap initial heap)
        locals updated resultIndex witness nextWitness := by
  obtain ⟨nextWitness, extension, operation, nextRuntimeRelated,
      valueRelated⟩ :=
    naturalLiteralStep_of_refines initialRelated.1 allocated
  have failureClear : (replaceHeap initial heap).host.failure? = none := by
    simp [replaceHeap, clearFailure]
  have nextState := initialRelated.bindAfter extension nextRuntimeRelated
    failureClear resultFound resultKindAt valueRelated targetSet
  refine ⟨nextWitness, extension, nextRuntimeRelated, valueRelated,
    ?_, initialRelated, nextState, ?_⟩
  · unfold FirTalos.Correctness.SourceLetResult
    simp [evalLetValue, valueEq]
    rfl
  · intro rest Q tail continued
    exact wp_naturalLiteral_let tail hImp hSat hi hContract hParams hResults
      operation targetSet continued

theorem codeWP_naturalLiteral_let
    {context : Fir.Wasm.Context}
    {sourceModule : Fir.Wasm.Module} {sourceFunction : Fir.Wasm.Function}
    {labels : List Lean.FVarId} {module : Wasm.Module}
    {hostEnv : Wasm.HostEnv Host} {spec : Wasm.HostSpec Host}
    {id : Nat} {imp : Wasm.ImportDecl}
    {decl : Lean.Compiler.LCNF.LetDecl .impure}
    {continuation : Lean.Compiler.LCNF.Code .impure} {sourceEnv : Env}
    {initial : Wasm.Store Host} {locals updated : Wasm.Locals}
    {resultIndex : Nat} {value : Nat} {heap : MemoryState} {word : Word32}
    {sourceRuntime : RuntimeState} {witness : RefinementWitness}
    {targetRest : Wasm.Program} {tail : List Wasm.Value}
    {Q : Wasm.Assertion Host}
    (valueEq : decl.value = .lit (.nat value))
    (valueCompiled : Fir.Wasm.compileLetValue context decl =
      .ok [.call (.runtime (.literal (.nat value) .tobject))])
    (callFound : callIndex? sourceModule
      (.runtime (.literal (.nat value) .tobject)) = some id)
    (initialRelated : StateRelated sourceFunction sourceRuntime sourceEnv
      initial locals witness)
    (resultFound :
      findFVar? (functionBindings sourceFunction) decl.fvarId = some resultIndex)
    (resultKindAt :
      (functionBindings sourceFunction)[resultIndex]?.map Prod.snd =
        some .tobject)
    (allocated : allocateNatural initial.host.runtime.heap value =
      .ok (heap, word))
    (hImp : module.imports[id]? = some imp)
    (hSat : hostEnv.Satisfies module spec)
    (hi : id < module.imports.length)
    (hContract : spec.contracts[id]? = some (naturalLiteralContract value))
    (hParams : imp.params.length = 0)
    (hResults : imp.results.length = 1)
    (targetSet :
      locals.set? resultIndex (.i32 (UInt32.ofNat word.value)) = some updated)
    (continued : ∀ nextWitness,
      witness.Extends nextWitness →
      ConcreteRuntimeRel (replaceHeap initial heap).host.runtime nextWitness
        (literal sourceRuntime (.nat value)).1 →
      PhysicalValueRel nextWitness .tobject
        (.i32 (UInt32.ofNat word.value)) (literal sourceRuntime (.nat value)).2 →
      CodeWP context sourceModule sourceFunction labels module hostEnv
        (literal sourceRuntime (.nat value)).1
        (bind sourceEnv decl.fvarId (literal sourceRuntime (.nat value)).2)
        continuation targetRest (replaceHeap initial heap) updated nextWitness
        tail Q) :
    CodeWP context sourceModule sourceFunction labels module hostEnv
      sourceRuntime sourceEnv (.let decl continuation)
      (.call id :: .localSet resultIndex :: targetRest)
      initial locals witness tail Q := by
  have valueAdapted :
      instructions sourceModule sourceFunction labels
          [.call (.runtime (.literal (.nat value) .tobject))] =
        .ok [.call id] := by
    simp [instructions, instruction, callFound]
    rfl
  obtain ⟨nextWitness, extension, nextRuntimeRelated, valueRelated, step⟩ :=
    letStepSimulates_naturalLiteral (context := context) valueEq initialRelated
      resultFound resultKindAt allocated hImp hSat hi hContract hParams hResults
      targetSet
  have nextCode := continued nextWitness extension nextRuntimeRelated valueRelated
  rcases step with ⟨_, stepInitial, _, stepWP⟩
  rcases nextCode with ⟨continuationAdapted, _, continuedWP⟩
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
