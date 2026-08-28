import Fir.Wasm.Concrete.NaturalAllocationCorrectness
import FirTalos.ConcreteResidentBigNumericAllocator
import FirTalos.ConcreteResidentPrimitives
import FirTalos.Correctness.Function
import FirTalos.Correctness.Locals
import Interpreter.Wasm.Wp.Tactic

namespace FirTalos.Concrete

open Fir.Wasm.Concrete

/-!
# Resident arbitrary-precision natural accessors

This module connects W7's installed BigNumeric low/high accessors to W6's
finite concrete memory at arbitrary limb indices.  Consumer-specific packages
such as USize's `CheckedNaturalCalls` stay above this Nat-independent layer.
-/

namespace ResidentBigNumeric

inductive NaturalLimbPart where
  | low
  | high
  deriving DecidableEq

def sourceFunction : NaturalLimbPart → Fir.Wasm.Function
  | .low => Fir.Wasm.Emit.ResidentBigNumeric.naturalLowFunction
  | .high => Fir.Wasm.Emit.ResidentBigNumeric.naturalHighFunction

def byteOffset : NaturalLimbPart → UInt32
  | .low => 0
  | .high => 4

def valueParam : Lean.FVarId := ⟨`value⟩
def flavorParam : Lean.FVarId := ⟨`flavor⟩
def indexParam : Lean.FVarId := ⟨`index⟩
def scaledLocal : Lean.FVarId := ⟨`scaledValue⟩
def countLocal : Lean.FVarId := ⟨`countValue⟩

/-- Public proof-side spelling of W7's common BigNumeric validator. -/
def validateCommonSource : List Fir.Wasm.Instruction :=
  let trapWhenTrue := ResidentAllocator.trapWhenTrueSource
  let trapUnlessTrue := ResidentBigNumericAllocator.trapUnlessTrueSource
  let load32 (offset : Nat) :=
    [.localGet valueParam, .i32Load .uint32 (UInt32.ofNat offset)]
  trapWhenTrue [
    .localGet valueParam,
    .i32Const .uint32 (UInt32.ofNat heapBase),
    .i32LtU] ++
  trapWhenTrue [
    .localGet valueParam,
    .i32Const .uint32 (UInt32.ofNat (target.heapAlignment - 1)),
    .i32And] ++
  trapUnlessTrue
    (load32 headerFlagsOffset ++
      [.i32Const .uint32 liveFlag, .i32And]) ++
  load32 headerAux1Offset ++
  [.localSet countLocal] ++
  trapUnlessTrue [.localGet countLocal] ++
  trapUnlessTrue [
    .localGet countLocal,
    .i32Const .uint32 536870908,
    .i32LtU] ++
  trapUnlessTrue
    (load32 headerAllocationBytesOffset ++
      ResidentBigNumericAllocator.scale8Source countLocal scaledLocal ++ [
        .i32Const .uint32 (UInt32.ofNat headerBytes),
        .localGet scaledLocal,
        .i32Add,
        .i32Eq]) ++
  [.localGet countLocal, .ret]

/-- The emitter's public common validator has exactly the proof-side shape. -/
theorem validateCommonFunction_shape :
    Fir.Wasm.Emit.ResidentBigNumeric.validateCommonFunction.body =
      validateCommonSource := by
  rfl

/-- Exact adapted instruction program for the common BigNumeric validator.
Local zero is the object word; locals one and two are count and scaled count. -/
def validateCommonProgram : Wasm.Program :=
  let trapWhenTrue := ResidentAllocator.trapWhenTrueProgram
  let trapUnlessTrue := ResidentBigNumericAllocator.trapUnlessTrueProgram
  let load32 (offset : Nat) :=
    [.localGet 0, .load32 (UInt32.ofNat offset)]
  trapWhenTrue [.localGet 0, .const (UInt32.ofNat heapBase), .ltU] ++
  trapWhenTrue [
    .localGet 0,
    .const (UInt32.ofNat (target.heapAlignment - 1)),
    .and] ++
  trapUnlessTrue
    (load32 headerFlagsOffset ++ [.const liveFlag, .and]) ++
  load32 headerAux1Offset ++
  [.localSet 1] ++
  trapUnlessTrue [.localGet 1] ++
  trapUnlessTrue [.localGet 1, .const 536870908, .ltU] ++
  trapUnlessTrue
    (load32 headerAllocationBytesOffset ++
      ResidentBigNumericAllocator.scale8Program 1 2 ++ [
        .const (UInt32.ofNat headerBytes),
        .localGet 2,
        .add,
        .eq]) ++
  [.localGet 1, .ret]

/-- Exact symbolic-to-Talos adaptation of the common validator. -/
theorem instructions_validateCommonFunction
    {sourceModule : Fir.Wasm.Module} :
    FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.validateCommonFunction []
      Fir.Wasm.Emit.ResidentBigNumeric.validateCommonFunction.body =
        .ok validateCommonProgram := by
  have valueFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.validateCommonFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.validateCommonFunction.locals.toList)
      valueParam = some 0 := by decide
  have countFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.validateCommonFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.validateCommonFunction.locals.toList)
      countLocal = some 1 := by decide
  have scaledFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.validateCommonFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.validateCommonFunction.locals.toList)
      scaledLocal = some 2 := by decide
  rw [validateCommonFunction_shape]
  set_option maxRecDepth 100000 in
    simp [validateCommonSource, validateCommonProgram,
      ResidentAllocator.trapWhenTrueSource,
      ResidentAllocator.trapWhenTrueProgram,
      ResidentBigNumericAllocator.trapUnlessTrueSource,
      ResidentBigNumericAllocator.trapUnlessTrueProgram,
      ResidentBigNumericAllocator.scale8Source,
      ResidentBigNumericAllocator.scale8Program,
      FirTalos.instructions, FirTalos.instruction, valueFound, countFound,
      scaledFound, Bind.bind, Except.bind, pure, Except.pure]

theorem validateCommonFunction_params :
    Fir.Wasm.Emit.ResidentBigNumeric.validateCommonFunction.params =
      #[(valueParam, .tobject)] := by
  rfl

theorem validateCommonFunction_locals :
    Fir.Wasm.Emit.ResidentBigNumeric.validateCommonFunction.locals =
      #[(countLocal, .uint32), (scaledLocal, .uint32)] := by
  rfl

theorem validateCommonFunction_results :
    Fir.Wasm.Emit.ResidentBigNumeric.validateCommonFunction.results =
      #[.uint32] := by
  rfl

/-- An adapted common validator consists of the exact proof-side program
followed only by the adapter's standard terminal suffix. -/
theorem adaptedValidateCommonFunction_body
    {sourceModule : Fir.Wasm.Module} {targetFunction : Wasm.Function}
    (adapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.validateCommonFunction =
        .ok targetFunction) :
    targetFunction.body = validateCommonProgram ++
      FirTalos.functionTerminal sourceModule
        Fir.Wasm.Emit.ResidentBigNumeric.validateCommonFunction := by
  exact ResidentPrimitives.adaptedFunction_body_of_exact adapted
    instructions_validateCommonFunction

def validateCommonEntry (word : UInt32) : Wasm.Locals := {
  params := [.i32 word]
  locals := [.i32 0, .i32 0]
  values := [] }

/-- Scalar execution boundary for the exact common validator program.  The
premises are precisely its three physical loads and arithmetic guards. -/
theorem wp_validateCommonProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {word flags count allocationBytes : UInt32}
    {rest : Wasm.Program}
    (addressNotBelow : ¬word < UInt32.ofNat heapBase)
    (addressAligned : word &&& UInt32.ofNat (target.heapAlignment - 1) = 0)
    (flagsInBounds :
      ¬(word.toNat + (UInt32.ofNat headerFlagsOffset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (countInBounds :
      ¬(word.toNat + (UInt32.ofNat headerAux1Offset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (allocationInBounds :
      ¬(word.toNat + (UInt32.ofNat headerAllocationBytesOffset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (flagsRead : store.mem.read32
      (word + UInt32.ofNat headerFlagsOffset) = flags)
    (countRead : store.mem.read32
      (word + UInt32.ofNat headerAux1Offset) = count)
    (allocationRead : store.mem.read32
      (word + UInt32.ofNat headerAllocationBytesOffset) = allocationBytes)
    (live : flags &&& liveFlag ≠ 0)
    (countPositive : count ≠ 0)
    (countFits : count < 536870908)
    (allocationExact : allocationBytes = UInt32.ofNat headerBytes +
      ResidentBigNumericAllocator.scale8Word count)
    (returned : Q (.Return store [.i32 count])) :
    Wasm.wp module (validateCommonProgram ++ rest) Q store
      (validateCommonEntry word) env := by
  have valueLocal (values : List Wasm.Value) :
      ({ validateCommonEntry word with values } : Wasm.Locals).get 0 =
        some (.i32 word) := by
    rfl
  have addressAligned' :
      UInt32.ofNat (target.heapAlignment - 1) &&& word = 0 := by
    simpa [UInt32.and_comm] using addressAligned
  have live' : liveFlag &&& flags ≠ 0 := by
    simpa [UInt32.and_comm] using live
  have flagsInBounds' : ¬(store.mem.pages * 65536 <
      word.toNat + headerFlagsOffset % 4294967296 + 4) := by
    simpa [wasmPageBytes] using flagsInBounds
  have countInBounds' : ¬(store.mem.pages * 65536 <
      word.toNat + headerAux1Offset % 4294967296 + 4) := by
    simpa [wasmPageBytes] using countInBounds
  have allocationInBounds' : ¬(store.mem.pages * 65536 <
      word.toNat + headerAllocationBytesOffset % 4294967296 + 4) := by
    simpa [wasmPageBytes] using allocationInBounds
  unfold validateCommonProgram
  simp only [ResidentAllocator.trapWhenTrueProgram,
    ResidentBigNumericAllocator.trapUnlessTrueProgram,
    ResidentBigNumericAllocator.scale8Program, List.cons_append,
    List.nil_append]
  simp only [Wasm.wp_localGet_cons]
  simp [validateCommonEntry, Wasm.Locals.get, addressNotBelow]
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  simp only [Wasm.wp_nil, List.take_zero, List.drop_zero, List.nil_append]
  simp only [Wasm.wp_localGet_cons, Wasm.wp_const_cons,
    Wasm.wp_and_cons]
  apply Wasm.wp_iff_cons rfl
  rw [addressAligned']
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  simp only [Wasm.wp_nil, List.take_zero, List.drop_zero, List.nil_append]
  rw [Wasm.wp_localGet_cons]
  simp [Wasm.Locals.get]
  rw [if_neg flagsInBounds', flagsRead, if_neg live']
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  simp only [Wasm.wp_nil, List.take_zero, List.drop_zero, List.nil_append]
  rw [Wasm.wp_localGet_cons]
  simp [Wasm.Locals.get]
  rw [if_neg countInBounds', countRead]
  rw [if_neg countPositive]
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  simp only [Wasm.wp_nil, List.take_zero, List.drop_zero, List.nil_append]
  rw [Wasm.wp_localGet_cons]
  simp [Wasm.Locals.get, countFits]
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  simp only [Wasm.wp_nil, List.take_zero, List.drop_zero, List.nil_append]
  rw [Wasm.wp_localGet_cons]
  simp [Wasm.Locals.get]
  rw [if_neg allocationInBounds', allocationRead, allocationExact]
  have requestEq :
      count + count + (count + count) +
          (count + count + (count + count)) + UInt32.ofNat headerBytes =
        UInt32.ofNat headerBytes +
          ResidentBigNumericAllocator.scale8Word count := by
    simp only [ResidentBigNumericAllocator.scale8Word]
    ac_rfl
  rw [requestEq, if_pos rfl]
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  simp only [Wasm.wp_nil, List.take_zero, List.drop_zero, List.nil_append]
  wp_run
  exact returned

/-- Installed common BigNumeric validator under its exact scalar memory and
arithmetic contract.  It is trace-free, preserves the store, and returns the
validated limb count ahead of the caller operand tail. -/
theorem terminatesWith_validateCommon_of_adapted
    {host : Type} {sourceModule : Fir.Wasm.Module}
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {targetFunction : Wasm.Function} {functionIndex : Nat}
    {store : Wasm.Store host} {word flags count allocationBytes : UInt32}
    {tail : List Wasm.Value}
    (adapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.validateCommonFunction =
        .ok targetFunction)
    (notImport : module.imports[functionIndex]? = none)
    (found : module.funcs[functionIndex - module.imports.length]? =
      some targetFunction)
    (addressNotBelow : ¬word < UInt32.ofNat heapBase)
    (addressAligned : word &&& UInt32.ofNat (target.heapAlignment - 1) = 0)
    (flagsInBounds :
      ¬(word.toNat + (UInt32.ofNat headerFlagsOffset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (countInBounds :
      ¬(word.toNat + (UInt32.ofNat headerAux1Offset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (allocationInBounds :
      ¬(word.toNat +
        (UInt32.ofNat headerAllocationBytesOffset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (flagsRead : store.mem.read32
      (word + UInt32.ofNat headerFlagsOffset) = flags)
    (countRead : store.mem.read32
      (word + UInt32.ofNat headerAux1Offset) = count)
    (allocationRead : store.mem.read32
      (word + UInt32.ofNat headerAllocationBytesOffset) = allocationBytes)
    (live : flags &&& liveFlag ≠ 0)
    (countPositive : count ≠ 0)
    (countFits : count < 536870908)
    (allocationExact : allocationBytes = UInt32.ofNat headerBytes +
      ResidentBigNumericAllocator.scale8Word count) :
    Wasm.TerminatesWith env module functionIndex store
      ([.i32 word] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 count :: tail) := by
  have signature :=
    FirTalos.Correctness.function_preserves_signature adapted
  rcases signature with ⟨paramsEq, localsEq, resultsEq⟩
  have body := adaptedValidateCommonFunction_body adapted
  apply FirTalos.Correctness.terminatesWith_of_wp_body_at notImport found
  rw [body]
  let arguments := [.i32 word] ++ tail
  let entry := targetFunction.toLocals
    (arguments.take targetFunction.numParams).reverse
  have returned :
      FirTalos.Correctness.FunctionBodyPost targetFunction arguments
        (fun final values =>
          final = store ∧ values = .i32 count :: tail)
        (.Return store [.i32 count]) := by
    simp [FirTalos.Correctness.FunctionBodyPost, arguments,
      Wasm.Function.numParams, paramsEq, resultsEq,
      validateCommonFunction_params, validateCommonFunction_results]
  have uint32Zero :
      (FirTalos.abiKind Fir.Wasm.AbiKind.uint32).zero = .i32 0 := by
    rfl
  simpa [entry, arguments, Wasm.Function.toLocals, validateCommonEntry,
      Wasm.Function.numParams, paramsEq, localsEq,
      validateCommonFunction_params, validateCommonFunction_locals,
      uint32Zero] using
    (wp_validateCommonProgram
      (module := module) (env := env) (store := store)
      (rest := FirTalos.functionTerminal sourceModule
        Fir.Wasm.Emit.ResidentBigNumeric.validateCommonFunction)
      addressNotBelow addressAligned flagsInBounds countInBounds
      allocationInBounds flagsRead countRead allocationRead live
      countPositive countFits allocationExact returned)

/-- Transport one exact W6 header lane to the Wasm memory view, packaging
both the validator's bounds premise and its physical `i32.load` result.  The
caller supplies only that the complete common header is in bounds. -/
theorem residentHeaderUInt32
    {heap : MemoryState} {memory : Wasm.Mem} {address : Word32}
    {offset : Nat} {word : UInt32}
    (memoryRelated : ResidentMemoryRel heap memory)
    (headerInBounds : address.value + headerBytes ≤ heap.memory.size)
    (offsetInHeader : offset + 4 ≤ headerBytes)
    (read : heap.memory.readUInt32 (address.value + offset) = .ok word) :
    ¬((UInt32.ofNat address.value).toNat +
        (UInt32.ofNat offset).toNat + 4 >
      memory.pages * wasmPageBytes) ∧
    memory.read32
      (UInt32.ofNat address.value + UInt32.ofNat offset) = word := by
  have concreteInBounds :
      address.value + offset + 3 < heap.memory.size := by
    omega
  have transported :=
    memoryRelated.readUInt32_eq_read32 concreteInBounds
  have addressToNat :
      (UInt32.ofNat address.value).toNat = address.value :=
    UInt32.toNat_ofNat_of_lt' (by
      simpa [wordModulus] using address.isLt)
  have offsetLt : offset < UInt32.size := by
    simp [headerBytes, UInt32.size] at offsetInHeader ⊢
    omega
  have offsetToNat : (UInt32.ofNat offset).toNat = offset :=
    UInt32.toNat_ofNat_of_lt' offsetLt
  have memorySize : heap.memory.size = memory.pages * wasmPageBytes :=
    memoryRelated.size_eq
  constructor
  · rw [addressToNat, offsetToNat, ← memorySize]
    omega
  · have targetAddress :
        UInt32.ofNat (address.value + offset) =
          UInt32.ofNat address.value + UInt32.ofNat offset := by
      rw [UInt32.ofNat_add]
    rw [← targetAddress]
    rw [read] at transported
    simpa using transported.symm

/-- Canonical W6 Natural admission discharges the complete common-validator
contract.  No instruction-level load, bounds, or modular-arithmetic premise
escapes this theorem. -/
theorem terminatesWith_validateCommon_of_naturalAdmission
    {host : Type} {sourceModule : Fir.Wasm.Module}
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {targetFunction : Wasm.Function} {functionIndex : Nat}
    {heap : MemoryState} {store : Wasm.Store host}
    {address : Word32} {value : Nat} {header : Header}
    {tail : List Wasm.Value}
    (adapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.validateCommonFunction =
        .ok targetFunction)
    (notImport : module.imports[functionIndex]? = none)
    (found : module.funcs[functionIndex - module.imports.length]? =
      some targetFunction)
    (memoryRelated : ResidentMemoryRel heap store.mem)
    (related : NaturalValidatorAdmission heap address value header) :
    Wasm.TerminatesWith env module functionIndex store
      ([.i32 (UInt32.ofNat address.value)] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 header.aux1 :: tail) := by
  obtain ⟨addressHeap, _, headerLive, headerMinimum, _, headerExtent⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts heap address header
      related.headerRead
  have commonHeaderInBounds :
      address.value + headerBytes ≤ heap.memory.size := by
    omega
  have addressFits32 : address.value < UInt32.size := by
    simpa [wordModulus, UInt32.size] using address.isLt
  have addressNotBelow :
      ¬UInt32.ofNat address.value < UInt32.ofNat heapBase := by
    intro below
    rw [UInt32.lt_iff_toNat_lt,
      UInt32.toNat_ofNat_of_lt' addressFits32,
      UInt32.toNat_ofNat_of_lt' (by decide : heapBase < UInt32.size)] at below
    exact (Nat.not_lt_of_ge related.addressBase) below
  have addressAlignedNat :
      address.value % target.heapAlignment = 0 := by
    unfold Word32.classify at addressHeap
    split at addressHeap <;> try contradiction
    split at addressHeap <;> try contradiction
    split at addressHeap <;> try contradiction
    assumption
  have addressAligned :
      UInt32.ofNat address.value &&&
          UInt32.ofNat (target.heapAlignment - 1) = 0 := by
    have aligned8 : address.value % 8 = 0 := by
      simpa [target] using addressAlignedNat
    simpa [target] using
      ResidentAllocator.alignedWord_of_mod8 addressFits32 aligned8
  obtain ⟨flagsInBounds, flagsRead⟩ := residentHeaderUInt32 memoryRelated
    commonHeaderInBounds (by decide) related.rawHeader.readFlags
  obtain ⟨countInBounds, countRead⟩ := residentHeaderUInt32 memoryRelated
    commonHeaderInBounds (by decide) related.rawHeader.readAux1
  obtain ⟨allocationInBounds, allocationRead⟩ :=
    residentHeaderUInt32 memoryRelated commonHeaderInBounds (by decide)
      related.rawHeader.readAllocationBytes
  have live : header.flags &&& liveFlag ≠ 0 := by
    cases persistent : header.persistent
    · simp [Header.flags, persistent, headerLive, liveFlag]
    · simp [Header.flags, persistent, headerLive, liveFlag]
      decide
  have limbsNonempty : naturalLimbs value ≠ [] := by
    rw [naturalLimbs]
    split <;> simp
  have limbLengthPositive : 0 < (naturalLimbs value).length := by
    cases limbs : naturalLimbs value with
    | nil => exact (limbsNonempty limbs).elim
    | cons limb rest => simp
  have countPositive : header.aux1 ≠ 0 := by
    intro countZero
    have countEq := related.limbCount
    rw [countZero] at countEq
    simp only [UInt32.toNat_zero] at countEq
    omega
  have allocationLt :
      header.allocationBytes.toNat < UInt32.size :=
    header.allocationBytes.toNat_lt_size
  rw [related.allocationBytes] at allocationLt
  have limbLengthFits : (naturalLimbs value).length < 536870908 := by
    simp [headerBytes, target, UInt32.size] at allocationLt ⊢
    omega
  have countFits : header.aux1 < 536870908 := by
    rw [UInt32.lt_iff_toNat_lt, related.limbCount]
    simpa using limbLengthFits
  have limbLengthFits32 : (naturalLimbs value).length < UInt32.size := by
    simp [UInt32.size] at limbLengthFits ⊢
    omega
  have countWord :
      header.aux1 = UInt32.ofNat (naturalLimbs value).length := by
    apply UInt32.toNat_inj.mp
    rw [related.limbCount,
      UInt32.toNat_ofNat_of_lt' limbLengthFits32]
  have exactBytesLt :
      headerBytes +
          target.semanticSlotBytes * (naturalLimbs value).length <
        UInt32.size := by
    exact allocationLt
  have allocationExact :
      header.allocationBytes = UInt32.ofNat headerBytes +
        ResidentBigNumericAllocator.scale8Word header.aux1 := by
    rw [countWord, ResidentBigNumericAllocator.scale8Word_ofNat,
      ← UInt32.ofNat_add]
    apply UInt32.toNat_inj.mp
    rw [related.allocationBytes,
      UInt32.toNat_ofNat_of_lt' exactBytesLt]
  exact terminatesWith_validateCommon_of_adapted adapted notImport found
    addressNotBelow addressAligned flagsInBounds countInBounds
    allocationInBounds flagsRead countRead allocationRead live countPositive
    countFits allocationExact

/-- Exact low/high view of the canonical most-significant Natural limb.  It
packages both Natural-only validator facts: the top limb is nonzero, and a
one-limb heap Natural has its high word outside the tagged range. -/
theorem NaturalValidatorAdmission.topWords
    {heap : MemoryState} {address : Word32} {value : Nat} {header : Header}
    (related : NaturalValidatorAdmission heap address value header) :
    ∃ low high : UInt32,
      heap.memory.readUInt32
          (address.value + headerBytes +
            8 * (header.aux1.toNat - 1)) = .ok low ∧
      heap.memory.readUInt32
          (address.value + headerBytes +
            8 * (header.aux1.toNat - 1) + 4) = .ok high ∧
      ¬(low = 0 ∧ high = 0) ∧
      (header.aux1.toNat = 1 → ¬high < 2147483648) := by
  obtain ⟨limb, atTop, limbNonzero, limbRead⟩ := related.topLimb
  unfold LinearMemory.readUInt64 at limbRead
  cases lowRead : heap.memory.readUInt32
      (address.value + headerBytes +
        target.semanticSlotBytes * (header.aux1.toNat - 1)) with
  | error failure =>
      rw [lowRead] at limbRead
      contradiction
  | ok low =>
      rw [lowRead] at limbRead
      cases highRead : heap.memory.readUInt32
          (address.value + headerBytes +
            target.semanticSlotBytes * (header.aux1.toNat - 1) + 4) with
      | error failure =>
          rw [highRead] at limbRead
          contradiction
      | ok high =>
          rw [highRead] at limbRead
          simp only [Bind.bind, Except.bind, pure, Except.pure,
            Except.ok.injEq] at limbRead
          have lowEq : low = limb.toUInt32 := by
            rw [← limbRead]
            exact (LinearMemory.assembledUInt64_toUInt32 low high).symm
          have highEq : high = (limb >>> (32 : UInt64)).toUInt32 := by
            rw [← limbRead]
            exact
              (LinearMemory.assembledUInt64_shiftRight_toUInt32 low high).symm
          refine ⟨low, high, ?_, ?_, ?_, ?_⟩
          · simpa [target] using lowRead
          · simpa [target] using highRead
          · rintro ⟨lowZero, highZero⟩
            have limbZero : limb = 0 := by
              rw [← limbRead, lowZero, highZero]
              decide
            exact limbNonzero limbZero
          · intro one
            obtain ⟨only, limbsEq, highNotLt⟩ :=
              related.oneLimbHigh_not_lt one
            have limbEq : limb = only := by
              rw [one, limbsEq] at atTop
              simpa using atTop.symm
            rw [highEq, limbEq]
            exact highNotLt

private def equalsConstSource (value : UInt32) :
    List Fir.Wasm.Instruction :=
  [.i32Const .uint32 value, .i32Eq]

private def loadHeaderSource (offset : Nat) : List Fir.Wasm.Instruction :=
  [.localGet valueParam, .i32Load .uint32 (UInt32.ofNat offset)]

private def requirePersistentSource : List Fir.Wasm.Instruction :=
  ResidentBigNumericAllocator.trapUnlessTrueSource
      (loadHeaderSource headerFlagsOffset ++
        [.i32Const .uint32 persistentFlag, .i32And]) ++
    ResidentAllocator.trapWhenTrueSource
      (loadHeaderSource headerRefCountOffset)

private def requireOrdinaryOrPersistentSource : List Fir.Wasm.Instruction :=
  loadHeaderSource headerFlagsOffset ++
    equalsConstSource (liveFlag + persistentFlag) ++
    [.ifElse
      (ResidentAllocator.trapWhenTrueSource
        (loadHeaderSource headerRefCountOffset))
      (ResidentBigNumericAllocator.trapUnlessTrueSource
          (loadHeaderSource headerFlagsOffset ++
            equalsConstSource liveFlag) ++
        ResidentBigNumericAllocator.trapUnlessTrueSource
          (loadHeaderSource headerRefCountOffset))]

private def requireReservedZeroSource : List Fir.Wasm.Instruction :=
  ResidentAllocator.trapWhenTrueSource
      (loadHeaderSource headerAux2Offset) ++
    ResidentAllocator.trapWhenTrueSource
      (loadHeaderSource headerAux3Offset)

private def requireOneCountSource : List Fir.Wasm.Instruction :=
  ResidentBigNumericAllocator.trapUnlessTrueSource [
    .localGet countLocal,
    .i32Const .uint32 1,
    .i32Eq]

private def loadTopLowSource : List Fir.Wasm.Instruction := [
  .localGet valueParam,
  .localGet countLocal,
  .i32Const .uint32 1,
  .i32Sub,
  .call (.declaration Fir.Wasm.Emit.ResidentBigNumeric.naturalLowName)]

private def loadTopHighSource : List Fir.Wasm.Instruction := [
  .localGet valueParam,
  .localGet countLocal,
  .i32Const .uint32 1,
  .i32Sub,
  .call (.declaration Fir.Wasm.Emit.ResidentBigNumeric.naturalHighName)]

private def requireTopNonzeroSource : List Fir.Wasm.Instruction :=
  ResidentBigNumericAllocator.trapUnlessTrueSource
    ((loadTopLowSource ++ equalsConstSource 0) ++
      (loadTopHighSource ++ equalsConstSource 0) ++
      [.i32And] ++ equalsConstSource 0)

private def naturalPromotedValidationSource : List Fir.Wasm.Instruction :=
  requireOneCountSource ++ requirePersistentSource ++
    requireReservedZeroSource ++
    ResidentBigNumericAllocator.trapUnlessTrueSource
      (loadTopHighSource ++
        [.i32Const .uint32 2147483648, .i32LtU]) ++
    loadTopHighSource ++ equalsConstSource 0 ++
    [.ifElse
      (ResidentBigNumericAllocator.trapUnlessTrueSource
        ([.i32Const .uint32 (UInt32.ofNat maxImmediatePayload)] ++
          loadTopLowSource ++ [.i32LtU]))
      []]

private def naturalBigValidationSource : List Fir.Wasm.Instruction :=
  requireOrdinaryOrPersistentSource ++ requireReservedZeroSource ++
    requireTopNonzeroSource ++ [
      .localGet countLocal,
      .i32Const .uint32 1,
      .i32Eq,
      .ifElse
        (ResidentAllocator.trapWhenTrueSource
          (loadTopHighSource ++
            [.i32Const .uint32 2147483648, .i32LtU]))
        []]

/-- Public proof-side spelling of W7's complete Natural validator. -/
def validateNaturalSource : List Fir.Wasm.Instruction := [
  .localGet valueParam,
  .i32Const .uint32 1,
  .i32And,
  .ifElse
    [.ret]
    ([.localGet valueParam,
      .call (.declaration
        Fir.Wasm.Emit.ResidentBigNumeric.validateCommonName),
      .localSet countLocal] ++
      ResidentBigNumericAllocator.trapUnlessTrueSource
        (loadHeaderSource headerKindOffset ++
          equalsConstSource ObjectKind.natural.code) ++
      loadHeaderSource headerAux0Offset ++
      equalsConstSource promotedTagMarker ++
      [.ifElse
        (naturalPromotedValidationSource ++ [.ret])
        (ResidentBigNumericAllocator.trapUnlessTrueSource
            (loadHeaderSource headerAux0Offset ++
              equalsConstSource bigNaturalMarker) ++
          naturalBigValidationSource ++ [.ret])])]

private def equalsConstProgram (value : UInt32) : Wasm.Program :=
  [.const value, .eq]

private def loadHeaderProgram (offset : Nat) : Wasm.Program :=
  [.localGet 0, .load32 (UInt32.ofNat offset)]

private def requirePersistentProgram : Wasm.Program :=
  ResidentBigNumericAllocator.trapUnlessTrueProgram
      (loadHeaderProgram headerFlagsOffset ++
        [.const persistentFlag, .and]) ++
    ResidentAllocator.trapWhenTrueProgram
      (loadHeaderProgram headerRefCountOffset)

private def requireOrdinaryOrPersistentProgram : Wasm.Program :=
  loadHeaderProgram headerFlagsOffset ++
    equalsConstProgram (liveFlag + persistentFlag) ++
    [.iff 0 0
      (ResidentAllocator.trapWhenTrueProgram
        (loadHeaderProgram headerRefCountOffset))
      (ResidentBigNumericAllocator.trapUnlessTrueProgram
          (loadHeaderProgram headerFlagsOffset ++ equalsConstProgram liveFlag) ++
        ResidentBigNumericAllocator.trapUnlessTrueProgram
          (loadHeaderProgram headerRefCountOffset))]

private def requireReservedZeroProgram : Wasm.Program :=
  ResidentAllocator.trapWhenTrueProgram
      (loadHeaderProgram headerAux2Offset) ++
    ResidentAllocator.trapWhenTrueProgram
      (loadHeaderProgram headerAux3Offset)

private def requireOneCountProgram : Wasm.Program :=
  ResidentBigNumericAllocator.trapUnlessTrueProgram [
    .localGet 1, .const 1, .eq]

private def loadTopLowProgram (naturalLowIndex : Nat) : Wasm.Program := [
  .localGet 0, .localGet 1, .const 1, .sub, .call naturalLowIndex]

private def loadTopHighProgram (naturalHighIndex : Nat) : Wasm.Program := [
  .localGet 0, .localGet 1, .const 1, .sub, .call naturalHighIndex]

private def requireTopNonzeroProgram
    (naturalLowIndex naturalHighIndex : Nat) : Wasm.Program :=
  ResidentBigNumericAllocator.trapUnlessTrueProgram
    ((loadTopLowProgram naturalLowIndex ++ equalsConstProgram 0) ++
      (loadTopHighProgram naturalHighIndex ++ equalsConstProgram 0) ++
      [.and] ++ equalsConstProgram 0)

private def naturalPromotedValidationProgram
    (naturalLowIndex naturalHighIndex : Nat) : Wasm.Program :=
  requireOneCountProgram ++ requirePersistentProgram ++
    requireReservedZeroProgram ++
    ResidentBigNumericAllocator.trapUnlessTrueProgram
      (loadTopHighProgram naturalHighIndex ++ [.const 2147483648, .ltU]) ++
    loadTopHighProgram naturalHighIndex ++ equalsConstProgram 0 ++
    [.iff 0 0
      (ResidentBigNumericAllocator.trapUnlessTrueProgram
        ([.const (UInt32.ofNat maxImmediatePayload)] ++
          loadTopLowProgram naturalLowIndex ++ [.ltU]))
      []]

private def naturalBigValidationProgram
    (naturalLowIndex naturalHighIndex : Nat) : Wasm.Program :=
  requireOrdinaryOrPersistentProgram ++ requireReservedZeroProgram ++
    requireTopNonzeroProgram naturalLowIndex naturalHighIndex ++ [
      .localGet 1, .const 1, .eq,
      .iff 0 0
        (ResidentAllocator.trapWhenTrueProgram
          (loadTopHighProgram naturalHighIndex ++
            [.const 2147483648, .ltU]))
        []]

/-- The big-Natural validator is a sequence of independent guards.  This
right-associated spelling lets their WP lemmas compose without exposing the
instruction lists of the guards to one another. -/
private theorem naturalBigValidationProgram_withReturn_factor
    (naturalLowIndex naturalHighIndex : Nat) :
    naturalBigValidationProgram naturalLowIndex naturalHighIndex ++ [.ret] =
      requireOrdinaryOrPersistentProgram ++
        (requireReservedZeroProgram ++
          (requireTopNonzeroProgram naturalLowIndex naturalHighIndex ++
            ([.localGet 1, .const 1, .eq,
              .iff 0 0
                (ResidentAllocator.trapWhenTrueProgram
                  (loadTopHighProgram naturalHighIndex ++
                    [.const 2147483648, .ltU]))
                []] ++ [.ret]))) := by
  simp only [naturalBigValidationProgram, List.append_assoc]

/-- Exact Talos instruction program for the complete Natural validator. -/
def validateNaturalProgram (validateCommonIndex naturalLowIndex
    naturalHighIndex : Nat) : Wasm.Program := [
  .localGet 0, .const 1, .and,
  .iff 0 0
    [.ret]
    ([.localGet 0, .call validateCommonIndex, .localSet 1] ++
      ResidentBigNumericAllocator.trapUnlessTrueProgram
        (loadHeaderProgram headerKindOffset ++
          equalsConstProgram ObjectKind.natural.code) ++
      loadHeaderProgram headerAux0Offset ++
      equalsConstProgram promotedTagMarker ++
      [.iff 0 0
        (naturalPromotedValidationProgram naturalLowIndex naturalHighIndex ++
          [.ret])
        (ResidentBigNumericAllocator.trapUnlessTrueProgram
            (loadHeaderProgram headerAux0Offset ++
              equalsConstProgram bigNaturalMarker) ++
          naturalBigValidationProgram naturalLowIndex naturalHighIndex ++
          [.ret])])]

/-- W7's complete Natural validator has exactly the public proof-side shape. -/
theorem validateNaturalFunction_shape :
    Fir.Wasm.Emit.ResidentBigNumeric.validateNaturalFunction.body =
      validateNaturalSource := by
  rfl

theorem validateNaturalFunction_params :
    Fir.Wasm.Emit.ResidentBigNumeric.validateNaturalFunction.params =
      #[(valueParam, .tobject)] := by
  rfl

theorem validateNaturalFunction_locals :
    Fir.Wasm.Emit.ResidentBigNumeric.validateNaturalFunction.locals =
      #[(countLocal, .uint32)] := by
  rfl

theorem validateNaturalFunction_results :
    Fir.Wasm.Emit.ResidentBigNumeric.validateNaturalFunction.results =
      #[] := by
  rfl

/-- Exact symbolic-to-Talos adaptation of the complete Natural validator. -/
theorem instructions_validateNaturalFunction
    {sourceModule : Fir.Wasm.Module}
    {validateCommonIndex naturalLowIndex naturalHighIndex : Nat}
    (validateCommonFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.validateCommonName) =
        some validateCommonIndex)
    (naturalLowFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.naturalLowName) =
        some naturalLowIndex)
    (naturalHighFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.naturalHighName) =
        some naturalHighIndex) :
    FirTalos.instructions sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.validateNaturalFunction []
      Fir.Wasm.Emit.ResidentBigNumeric.validateNaturalFunction.body =
        .ok (validateNaturalProgram validateCommonIndex naturalLowIndex
          naturalHighIndex) := by
  have valueFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.validateNaturalFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.validateNaturalFunction.locals.toList)
      valueParam = some 0 := by decide
  have countFound : FirTalos.findFVar?
      (Fir.Wasm.Emit.ResidentBigNumeric.validateNaturalFunction.params.toList ++
        Fir.Wasm.Emit.ResidentBigNumeric.validateNaturalFunction.locals.toList)
      countLocal = some 1 := by decide
  rw [validateNaturalFunction_shape]
  set_option maxRecDepth 100000 in
    simp [validateNaturalSource, validateNaturalProgram,
      naturalPromotedValidationSource, naturalPromotedValidationProgram,
      naturalBigValidationSource, naturalBigValidationProgram,
      requirePersistentSource, requirePersistentProgram,
      requireOrdinaryOrPersistentSource, requireOrdinaryOrPersistentProgram,
      requireReservedZeroSource, requireReservedZeroProgram,
      requireOneCountSource, requireOneCountProgram,
      requireTopNonzeroSource, requireTopNonzeroProgram,
      loadTopLowSource, loadTopLowProgram, loadTopHighSource,
      loadTopHighProgram, loadHeaderSource, loadHeaderProgram,
      equalsConstSource, equalsConstProgram,
      ResidentAllocator.trapWhenTrueSource,
      ResidentAllocator.trapWhenTrueProgram,
      ResidentBigNumericAllocator.trapUnlessTrueSource,
      ResidentBigNumericAllocator.trapUnlessTrueProgram,
      FirTalos.instructions, FirTalos.instruction, valueFound, countFound,
      validateCommonFound, naturalLowFound, naturalHighFound,
      Bind.bind, Except.bind, pure, Except.pure]

/-- An adapted complete Natural validator consists of the exact proof-side
program followed only by the adapter's standard terminal suffix. -/
theorem adaptedValidateNaturalFunction_body
    {sourceModule : Fir.Wasm.Module} {targetFunction : Wasm.Function}
    {validateCommonIndex naturalLowIndex naturalHighIndex : Nat}
    (adapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.validateNaturalFunction =
        .ok targetFunction)
    (validateCommonFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.validateCommonName) =
        some validateCommonIndex)
    (naturalLowFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.naturalLowName) =
        some naturalLowIndex)
    (naturalHighFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.naturalHighName) =
        some naturalHighIndex) :
    targetFunction.body =
        validateNaturalProgram validateCommonIndex naturalLowIndex
            naturalHighIndex ++
          FirTalos.functionTerminal sourceModule
            Fir.Wasm.Emit.ResidentBigNumeric.validateNaturalFunction := by
  exact ResidentPrimitives.adaptedFunction_body_of_exact adapted
    (instructions_validateNaturalFunction validateCommonFound naturalLowFound
      naturalHighFound)

/-- The three installed calls used by the heap arm of Natural validation.
The record is deliberately independent of how the helpers are generated or
linked: the validator proof needs only their exact trace-free behavior. -/
structure NaturalValidationCalls {host : Type}
    (env : Wasm.HostEnv host) (module : Wasm.Module)
    (validateCommonIndex naturalLowIndex naturalHighIndex : Nat)
    (store : Wasm.Store host) (word count topIndex low high : UInt32) : Prop where
  common : ∀ tail,
    Wasm.TerminatesWith env module validateCommonIndex store
      (.i32 word :: tail)
      (fun final values =>
        final = store ∧ values = .i32 count :: tail)
  low : ∀ tail,
    Wasm.TerminatesWith env module naturalLowIndex store
      ([.i32 topIndex, .i32 word] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 low :: tail)
  high : ∀ tail,
    Wasm.TerminatesWith env module naturalHighIndex store
      ([.i32 topIndex, .i32 word] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 high :: tail)

/-- The shared ownership check accepts exactly the two live concrete header
encodings used by resident objects: persistent with zero refcount, or
ordinary with nonzero refcount. -/
theorem wp_requireOrdinaryOrPersistentProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {locals : Wasm.Locals} {word flags refCount : UInt32}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    (valueLocal : locals.get 0 = some (.i32 word))
    (flagsInBounds :
      ¬(word.toNat + (UInt32.ofNat headerFlagsOffset).toNat + 4 >
        store.mem.pages * 65536))
    (refCountInBounds :
      ¬(word.toNat + (UInt32.ofNat headerRefCountOffset).toNat + 4 >
        store.mem.pages * 65536))
    (flagsRead : store.mem.read32
      (word + UInt32.ofNat headerFlagsOffset) = flags)
    (refCountRead : store.mem.read32
      (word + UInt32.ofNat headerRefCountOffset) = refCount)
    (ownership :
      (flags = liveFlag + persistentFlag ∧ refCount = 0) ∨
      (flags = liveFlag ∧ refCount ≠ 0))
    (continued : Wasm.wp module rest Q store
      { locals with values := tail } env) :
    Wasm.wp module (requireOrdinaryOrPersistentProgram ++ rest) Q store
      { locals with values := tail } env := by
  have valueLocal' (values : List Wasm.Value) :
      ({ locals with values } : Wasm.Locals).get 0 = some (.i32 word) := by
    simpa using valueLocal
  rcases ownership with persistent | ordinary
  · rcases persistent with ⟨flagsEq, refCountEq⟩
    unfold requireOrdinaryOrPersistentProgram
    simp only [ResidentAllocator.trapWhenTrueProgram,
      ResidentBigNumericAllocator.trapUnlessTrueProgram,
      loadHeaderProgram, equalsConstProgram, List.cons_append,
      List.nil_append, Wasm.wp_localGet_cons, valueLocal',
      Wasm.wp_load32_cons]
    rw [if_neg flagsInBounds, flagsRead, flagsEq]
    simp only [Wasm.wp_const_cons, Wasm.wp_eq_cons, if_true]
    apply Wasm.wp_iff_cons rfl
    rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
    simp only [List.take_zero, List.drop_zero, List.nil_append,
      Wasm.wp_localGet_cons, valueLocal', Wasm.wp_load32_cons]
    rw [if_neg refCountInBounds, refCountRead, refCountEq]
    apply Wasm.wp_iff_cons rfl
    rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
    simpa only [Wasm.wp_nil, List.take_zero, List.drop_zero,
      List.nil_append] using continued
  · rcases ordinary with ⟨flagsEq, refCountNe⟩
    have flagsNe : liveFlag ≠ liveFlag + persistentFlag := by decide
    unfold requireOrdinaryOrPersistentProgram
    simp only [ResidentAllocator.trapWhenTrueProgram,
      ResidentBigNumericAllocator.trapUnlessTrueProgram,
      loadHeaderProgram, equalsConstProgram, List.cons_append,
      List.nil_append, Wasm.wp_localGet_cons, valueLocal',
      Wasm.wp_load32_cons]
    rw [if_neg flagsInBounds, flagsRead, flagsEq]
    simp only [Wasm.wp_const_cons, Wasm.wp_eq_cons, if_neg flagsNe]
    apply Wasm.wp_iff_cons rfl
    rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
    simp only [List.take_zero, List.drop_zero, List.nil_append,
      Wasm.wp_localGet_cons, valueLocal', Wasm.wp_load32_cons]
    rw [if_neg flagsInBounds, flagsRead, flagsEq]
    simp only [Wasm.wp_const_cons, Wasm.wp_eq_cons, if_true,
      if_neg (by decide : (1 : UInt32) ≠ 0)]
    apply Wasm.wp_iff_cons rfl
    rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
    simp only [Wasm.wp_nil, List.take_zero, List.drop_zero, List.nil_append,
      Wasm.wp_localGet_cons, valueLocal', Wasm.wp_load32_cons]
    rw [if_neg refCountInBounds, refCountRead]
    simp only [Wasm.wp_const_cons, Wasm.wp_eq_cons, if_neg refCountNe]
    apply Wasm.wp_iff_cons rfl
    rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
    simpa only [Wasm.wp_nil, List.take_zero, List.drop_zero,
      List.nil_append] using continued

/-- Reserved-header validation is a reusable two-load guard, independent of
the payload kind whose header owns the lanes. -/
theorem wp_requireReservedZeroProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {locals : Wasm.Locals} {word aux2 aux3 : UInt32}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    (valueLocal : locals.get 0 = some (.i32 word))
    (aux2InBounds :
      ¬(word.toNat + (UInt32.ofNat headerAux2Offset).toNat + 4 >
        store.mem.pages * 65536))
    (aux3InBounds :
      ¬(word.toNat + (UInt32.ofNat headerAux3Offset).toNat + 4 >
        store.mem.pages * 65536))
    (aux2Read : store.mem.read32
      (word + UInt32.ofNat headerAux2Offset) = aux2)
    (aux3Read : store.mem.read32
      (word + UInt32.ofNat headerAux3Offset) = aux3)
    (reserved2 : aux2 = 0)
    (reserved3 : aux3 = 0)
    (continued : Wasm.wp module rest Q store
      { locals with values := tail } env) :
    Wasm.wp module (requireReservedZeroProgram ++ rest) Q store
      { locals with values := tail } env := by
  have valueLocal' (values : List Wasm.Value) :
      ({ locals with values } : Wasm.Locals).get 0 = some (.i32 word) := by
    simpa using valueLocal
  unfold requireReservedZeroProgram
  simp only [ResidentAllocator.trapWhenTrueProgram, loadHeaderProgram,
    List.cons_append, List.nil_append, Wasm.wp_localGet_cons, valueLocal',
    Wasm.wp_load32_cons]
  rw [if_neg aux2InBounds, aux2Read, reserved2]
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  simp only [Wasm.wp_nil, List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, valueLocal', Wasm.wp_load32_cons]
  rw [if_neg aux3InBounds, aux3Read, reserved3]
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  simpa only [Wasm.wp_nil, List.take_zero, List.drop_zero,
    List.nil_append] using continued

/-- Scalar execution boundary for the complete heap-backed Natural validator.
All memory reads and nested calls are explicit; canonical W6 admission below
will discharge this contract as one unit. -/
theorem wp_validateNaturalProgram_big
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {initial afterCount : Wasm.Locals}
    {validateCommonIndex naturalLowIndex naturalHighIndex : Nat}
    {word count topIndex low high kind flags refCount aux0 aux2 aux3 : UInt32}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    (calls : NaturalValidationCalls env module validateCommonIndex
      naturalLowIndex naturalHighIndex store word count topIndex low high)
    (valueLocal : initial.get 0 = some (.i32 word))
    (countSet :
      ({ initial with values := .i32 count :: tail }).set? 1 (.i32 count) =
        some afterCount)
    (heapSelected : 1 &&& word = 0)
    (topIndexEq : count - 1 = topIndex)
    (kindInBounds :
      ¬(word.toNat + (UInt32.ofNat headerKindOffset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (flagsInBounds :
      ¬(word.toNat + (UInt32.ofNat headerFlagsOffset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (refCountInBounds :
      ¬(word.toNat + (UInt32.ofNat headerRefCountOffset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (aux0InBounds :
      ¬(word.toNat + (UInt32.ofNat headerAux0Offset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (aux2InBounds :
      ¬(word.toNat + (UInt32.ofNat headerAux2Offset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (aux3InBounds :
      ¬(word.toNat + (UInt32.ofNat headerAux3Offset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (kindRead : store.mem.read32
      (word + UInt32.ofNat headerKindOffset) = kind)
    (flagsRead : store.mem.read32
      (word + UInt32.ofNat headerFlagsOffset) = flags)
    (refCountRead : store.mem.read32
      (word + UInt32.ofNat headerRefCountOffset) = refCount)
    (aux0Read : store.mem.read32
      (word + UInt32.ofNat headerAux0Offset) = aux0)
    (aux2Read : store.mem.read32
      (word + UInt32.ofNat headerAux2Offset) = aux2)
    (aux3Read : store.mem.read32
      (word + UInt32.ofNat headerAux3Offset) = aux3)
    (kindExact : kind = ObjectKind.natural.code)
    (markerExact : aux0 = bigNaturalMarker)
    (ownership :
      (flags = liveFlag + persistentFlag ∧ refCount = 0) ∨
      (flags = liveFlag ∧ refCount ≠ 0))
    (reserved2 : aux2 = 0)
    (reserved3 : aux3 = 0)
    (topNonzero : ¬(low = 0 ∧ high = 0))
    (oneHigh : count = 1 → ¬high < 2147483648)
    (returned : Q (.Return store tail)) :
    Wasm.wp module
      (validateNaturalProgram validateCommonIndex naturalLowIndex
          naturalHighIndex ++ rest)
      Q store { initial with values := tail } env := by
  have countUpdate := FirTalos.Correctness.localUpdate_of_set? countSet
  have valueAfterCount (values : List Wasm.Value) :
      ({ afterCount with values } : Wasm.Locals).get 0 = some (.i32 word) := by
    change afterCount.get 0 = some (.i32 word)
    rw [countUpdate.2 (by decide)]
    simpa using valueLocal
  have countAfterCount (values : List Wasm.Value) :
      ({ afterCount with values } : Wasm.Locals).get 1 = some (.i32 count) := by
    simpa using countUpdate.1
  have valueLocal' :
      ({ initial with values := tail } : Wasm.Locals).get 0 =
        some (.i32 word) := by
    simpa using valueLocal
  have kindInBounds' :
      ¬(word.toNat + (UInt32.ofNat headerKindOffset).toNat + 4 >
        store.mem.pages * 65536) := by
    simpa [wasmPageBytes] using kindInBounds
  have flagsInBounds' :
      ¬(word.toNat + (UInt32.ofNat headerFlagsOffset).toNat + 4 >
        store.mem.pages * 65536) := by
    simpa [wasmPageBytes] using flagsInBounds
  have refCountInBounds' :
      ¬(word.toNat + (UInt32.ofNat headerRefCountOffset).toNat + 4 >
        store.mem.pages * 65536) := by
    simpa [wasmPageBytes] using refCountInBounds
  have aux0InBounds' :
      ¬(word.toNat + (UInt32.ofNat headerAux0Offset).toNat + 4 >
        store.mem.pages * 65536) := by
    simpa [wasmPageBytes] using aux0InBounds
  have aux2InBounds' :
      ¬(word.toNat + (UInt32.ofNat headerAux2Offset).toNat + 4 >
        store.mem.pages * 65536) := by
    simpa [wasmPageBytes] using aux2InBounds
  have aux3InBounds' :
      ¬(word.toNat + (UInt32.ofNat headerAux3Offset).toNat + 4 >
        store.mem.pages * 65536) := by
    simpa [wasmPageBytes] using aux3InBounds
  unfold validateNaturalProgram loadHeaderProgram equalsConstProgram
  simp only [ResidentAllocator.trapWhenTrueProgram,
    ResidentBigNumericAllocator.trapUnlessTrueProgram,
    List.cons_append, List.nil_append, Wasm.wp_localGet_cons, valueLocal',
    Wasm.wp_const_cons, Wasm.wp_and_cons, heapSelected]
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  simp only [List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, valueLocal']
  apply Wasm.wp_call_tw (calls.common tail)
  intro final values commonRun
  rcases commonRun with ⟨rfl, valuesEq⟩
  rw [valuesEq]
  simp only [Wasm.wp_localSet_cons, countSet, Wasm.wp_localGet_cons,
    valueAfterCount, Wasm.wp_load32_cons]
  rw [if_neg kindInBounds', kindRead, kindExact]
  simp only [Wasm.wp_const_cons, Wasm.wp_eq_cons,
    if_neg (by decide : (1 : UInt32) ≠ 0), if_true]
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  simp only [Wasm.wp_nil, List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, valueAfterCount, Wasm.wp_load32_cons]
  rw [if_neg aux0InBounds', aux0Read, markerExact]
  simp only [Wasm.wp_const_cons, Wasm.wp_eq_cons,
    if_neg (by decide : bigNaturalMarker ≠ promotedTagMarker)]
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  simp only [Wasm.wp_nil, List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, valueAfterCount, Wasm.wp_load32_cons]
  rw [if_neg aux0InBounds', aux0Read, markerExact]
  simp only [Wasm.wp_const_cons, Wasm.wp_eq_cons,
    if_neg (by decide : (1 : UInt32) ≠ 0), if_true]
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  simp only [Wasm.wp_nil, List.take_zero, List.drop_zero, List.nil_append]
  rw [naturalBigValidationProgram_withReturn_factor]
  apply wp_requireOrdinaryOrPersistentProgram (valueAfterCount tail)
    flagsInBounds'
    refCountInBounds' flagsRead refCountRead ownership
  apply wp_requireReservedZeroProgram (valueAfterCount tail) aux2InBounds'
    aux3InBounds' aux2Read aux3Read reserved2 reserved3
  unfold requireTopNonzeroProgram loadTopLowProgram loadTopHighProgram
  simp only [ResidentBigNumericAllocator.trapUnlessTrueProgram,
    ResidentAllocator.trapWhenTrueProgram, equalsConstProgram,
    List.cons_append, List.nil_append,
    Wasm.wp_localGet_cons, valueAfterCount, countAfterCount,
    Wasm.wp_const_cons,
    Wasm.wp_sub_cons]
  rw [topIndexEq]
  apply Wasm.wp_call_tw (calls.low tail)
  intro final values lowRun
  rcases lowRun with ⟨rfl, valuesEq⟩
  rw [valuesEq]
  simp only [Wasm.wp_const_cons, Wasm.wp_eq_cons,
    Wasm.wp_localGet_cons, valueAfterCount, countAfterCount,
    Wasm.wp_sub_cons]
  rw [topIndexEq]
  apply Wasm.wp_call_tw (calls.high (.i32 (if low = 0 then 1 else 0) :: tail))
  intro final values highRun
  rcases highRun with ⟨rfl, valuesEq⟩
  rw [valuesEq]
  have topBitsZero :
      ((if high = 0 then 1 else 0) &&&
        (if low = 0 then 1 else 0) : UInt32) = 0 := by
    by_cases lowZero : low = 0
    · have highNonzero : high ≠ 0 := by
        intro highZero
        exact topNonzero ⟨lowZero, highZero⟩
      simp [lowZero, highNonzero]
    · simp [lowZero]
  simp only [Wasm.wp_const_cons, Wasm.wp_eq_cons, Wasm.wp_and_cons]
  rw [topBitsZero]
  simp only [if_true,
    if_neg (by decide : (1 : UInt32) ≠ 0)]
  apply Wasm.wp_iff_cons rfl
  simp only [if_neg (by decide : ¬(0 : UInt32) ≠ 0), Wasm.wp_nil,
    List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, countAfterCount, Wasm.wp_const_cons]
  rw [Wasm.wp_eq_cons]
  apply Wasm.wp_iff_cons rfl
  split
  · rename_i one
    have countOne : count = 1 := by
      simpa only [decide_eq_true_eq] using one
    simp only [if_pos (by decide : (1 : UInt32) ≠ 0),
      Wasm.wp_localGet_cons, valueAfterCount, countAfterCount,
      Wasm.wp_const_cons, Wasm.wp_sub_cons]
    rw [topIndexEq]
    apply Wasm.wp_call_tw (calls.high tail)
    intro final values highRun
    rcases highRun with ⟨rfl, valuesEq⟩
    rw [valuesEq]
    wp_run
    simp [oneHigh countOne]
    apply Wasm.wp_iff_cons rfl
    simp only [if_neg (by decide : ¬(0 : UInt32) ≠ 0), Wasm.wp_nil,
      List.take_zero, List.drop_zero, List.nil_append]
    exact returned
  · simpa only [if_neg (by decide : ¬(0 : UInt32) ≠ 0),
      Wasm.wp_nil, List.take_zero, List.drop_zero, List.nil_append,
      Wasm.wp_ret_cons] using returned

def naturalCountSourceFunction : Fir.Wasm.Function :=
  Fir.Wasm.Emit.ResidentBigNumeric.naturalCountFunction

def naturalCountSource : List Fir.Wasm.Instruction := [
  .localGet valueParam,
  .i32Const .uint32 1,
  .i32And,
  .ifElse
    [.i32Const .uint32 1, .ret]
    [.localGet valueParam,
      .i32Load .uint32 (UInt32.ofNat headerAux1Offset),
      .ret]]

def naturalCountProgram : Wasm.Program := [
  .localGet 0,
  .const 1,
  .and,
  .iff 0 0 [.const 1, .ret]
    [.localGet 0, .load32 (UInt32.ofNat headerAux1Offset), .ret]]

theorem naturalCountSourceFunction_body :
    naturalCountSourceFunction.body = naturalCountSource := by
  rfl

theorem naturalCountSourceFunction_params :
    naturalCountSourceFunction.params = #[(valueParam, .tobject)] := by
  rfl

theorem naturalCountSourceFunction_locals :
    naturalCountSourceFunction.locals = #[] := by
  rfl

theorem naturalCountSourceFunction_results :
    naturalCountSourceFunction.results = #[.uint32] := by
  rfl

/-- Exact adaptation of W7's natural limb-count helper. -/
theorem instructions_naturalCountSourceFunction
    {sourceModule : Fir.Wasm.Module} :
    FirTalos.instructions sourceModule naturalCountSourceFunction []
      naturalCountSourceFunction.body = .ok naturalCountProgram := by
  rw [naturalCountSourceFunction_body]
  have valueFound : FirTalos.findFVar?
      (naturalCountSourceFunction.params.toList ++
        naturalCountSourceFunction.locals.toList) valueParam = some 0 := by
    decide
  simp [naturalCountSource, naturalCountProgram, FirTalos.instructions,
    FirTalos.instruction, valueFound, Bind.bind, Except.bind, pure,
    Except.pure]

/-- Exact installed target body, including the adapter's terminal suffix. -/
theorem adaptedNaturalCountSourceFunction_body
    {sourceModule : Fir.Wasm.Module} {targetFunction : Wasm.Function}
    (adapted : FirTalos.function sourceModule naturalCountSourceFunction =
      .ok targetFunction) :
    targetFunction.body = naturalCountProgram ++
      FirTalos.functionTerminal sourceModule naturalCountSourceFunction := by
  exact ResidentPrimitives.adaptedFunction_body_of_exact adapted
    instructions_naturalCountSourceFunction

/-- The immediate representation always contributes one 64-bit magnitude
limb.  This proof is representation-only and performs no memory access. -/
theorem wp_naturalCountProgram_immediate
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {initial : Wasm.Locals} {word : UInt32}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    (immediate : 1 &&& word = 1)
    (valueLocal : initial.get 0 = some (.i32 word))
    (returned : Q (.Return store (.i32 1 :: tail))) :
    Wasm.wp module (naturalCountProgram ++ rest) Q store
      { initial with values := tail } env := by
  have valueLocal' :
      ({ initial with values := tail } : Wasm.Locals).get 0 =
        some (.i32 word) := by
    simpa using valueLocal
  unfold naturalCountProgram
  simp only [List.cons_append, List.nil_append, Wasm.wp_localGet_cons,
    valueLocal', Wasm.wp_const_cons, Wasm.wp_and_cons, immediate]
  apply Wasm.wp_iff_cons rfl
  rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
  simp only [Wasm.wp_const_cons, Wasm.wp_ret_cons]
  exact returned

/-- The heap representation returns the header's stored limb count, leaving
the store and caller operand tail unchanged. -/
theorem wp_naturalCountProgram_heap
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {initial : Wasm.Locals} {word count : UInt32}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    (notImmediate : 1 &&& word = 0)
    (valueLocal : initial.get 0 = some (.i32 word))
    (readInBounds :
      ¬(word.toNat + (UInt32.ofNat headerAux1Offset).toNat + 4 >
        store.mem.pages * 65536))
    (readEq : store.mem.read32
      (word + UInt32.ofNat headerAux1Offset) = count)
    (returned : Q (.Return store (.i32 count :: tail))) :
    Wasm.wp module (naturalCountProgram ++ rest) Q store
      { initial with values := tail } env := by
  have valueLocal' :
      ({ initial with values := tail } : Wasm.Locals).get 0 =
        some (.i32 word) := by
    simpa using valueLocal
  unfold naturalCountProgram
  simp only [List.cons_append, List.nil_append, Wasm.wp_localGet_cons,
    valueLocal', Wasm.wp_const_cons, Wasm.wp_and_cons, notImmediate]
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  simp only [Wasm.wp_localGet_cons, valueLocal', Wasm.wp_load32_cons]
  split
  · rename_i outOfBounds
    exact (readInBounds outOfBounds).elim
  · simp only [readEq, Wasm.wp_ret_cons]
    exact returned

/-- Installed immediate count helper, with exact trace-free store behavior. -/
theorem terminatesWith_naturalCountImmediate_of_adapted
    {host : Type} {sourceModule : Fir.Wasm.Module}
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {targetFunction : Wasm.Function} {functionIndex : Nat}
    {store : Wasm.Store host} {word : UInt32} {tail : List Wasm.Value}
    (adapted : FirTalos.function sourceModule naturalCountSourceFunction =
      .ok targetFunction)
    (notImport : module.imports[functionIndex]? = none)
    (found : module.funcs[functionIndex - module.imports.length]? =
      some targetFunction)
    (immediate : 1 &&& word = 1) :
    Wasm.TerminatesWith env module functionIndex store
      ([.i32 word] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 1 :: tail) := by
  have signature :=
    FirTalos.Correctness.function_preserves_signature adapted
  rcases signature with ⟨paramsEq, localsEq, resultsEq⟩
  have body := adaptedNaturalCountSourceFunction_body adapted
  apply FirTalos.Correctness.terminatesWith_of_wp_body_at notImport found
  rw [body]
  let arguments := [.i32 word] ++ tail
  let entry := targetFunction.toLocals
    (arguments.take targetFunction.numParams).reverse
  have valueLocal : entry.get 0 = some (.i32 word) := by
    simp [entry, arguments, Wasm.Function.toLocals,
      Wasm.Function.numParams, paramsEq, naturalCountSourceFunction_params]
  have returned :
      FirTalos.Correctness.FunctionBodyPost targetFunction arguments
        (fun final values =>
          final = store ∧ values = .i32 1 :: tail)
        (.Return store [.i32 1]) := by
    simp [FirTalos.Correctness.FunctionBodyPost, arguments,
      Wasm.Function.numParams, paramsEq, resultsEq,
      naturalCountSourceFunction_params, naturalCountSourceFunction_results]
  simpa [entry, arguments, Wasm.Function.toLocals] using
    (wp_naturalCountProgram_immediate
      (module := module) (env := env) (store := store) (initial := entry)
      (rest := FirTalos.functionTerminal sourceModule
        naturalCountSourceFunction)
      (tail := []) immediate valueLocal returned)

/-- Installed heap count helper under the exact physical load contract. -/
theorem terminatesWith_naturalCountHeap_of_adapted
    {host : Type} {sourceModule : Fir.Wasm.Module}
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {targetFunction : Wasm.Function} {functionIndex : Nat}
    {store : Wasm.Store host} {word count : UInt32}
    {tail : List Wasm.Value}
    (adapted : FirTalos.function sourceModule naturalCountSourceFunction =
      .ok targetFunction)
    (notImport : module.imports[functionIndex]? = none)
    (found : module.funcs[functionIndex - module.imports.length]? =
      some targetFunction)
    (notImmediate : 1 &&& word = 0)
    (readInBounds :
      ¬(word.toNat + (UInt32.ofNat headerAux1Offset).toNat + 4 >
        store.mem.pages * 65536))
    (readEq : store.mem.read32
      (word + UInt32.ofNat headerAux1Offset) = count) :
    Wasm.TerminatesWith env module functionIndex store
      ([.i32 word] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 count :: tail) := by
  have signature :=
    FirTalos.Correctness.function_preserves_signature adapted
  rcases signature with ⟨paramsEq, localsEq, resultsEq⟩
  have body := adaptedNaturalCountSourceFunction_body adapted
  apply FirTalos.Correctness.terminatesWith_of_wp_body_at notImport found
  rw [body]
  let arguments := [.i32 word] ++ tail
  let entry := targetFunction.toLocals
    (arguments.take targetFunction.numParams).reverse
  have valueLocal : entry.get 0 = some (.i32 word) := by
    simp [entry, arguments, Wasm.Function.toLocals,
      Wasm.Function.numParams, paramsEq, naturalCountSourceFunction_params]
  have returned :
      FirTalos.Correctness.FunctionBodyPost targetFunction arguments
        (fun final values =>
          final = store ∧ values = .i32 count :: tail)
        (.Return store [.i32 count]) := by
    simp [FirTalos.Correctness.FunctionBodyPost, arguments,
      Wasm.Function.numParams, paramsEq, resultsEq,
      naturalCountSourceFunction_params, naturalCountSourceFunction_results]
  simpa [entry, arguments, Wasm.Function.toLocals] using
    (wp_naturalCountProgram_heap
      (module := module) (env := env) (store := store) (initial := entry)
      (rest := FirTalos.functionTerminal sourceModule
        naturalCountSourceFunction)
      (tail := []) notImmediate valueLocal readInBounds readEq returned)

/-- A checked W6 live header discharges the heap count helper's physical
address, bounds, and load premises.  This is the reusable refinement boundary
for validated natural operands; consumers no longer reason about `aux1` byte
coordinates directly. -/
theorem terminatesWith_naturalCount_of_liveHeader
    {host : Type} {sourceModule : Fir.Wasm.Module}
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {targetFunction : Wasm.Function} {functionIndex : Nat}
    {heap : MemoryState} {store : Wasm.Store host}
    {address : Word32} {header : Header} {tail : List Wasm.Value}
    (adapted : FirTalos.function sourceModule naturalCountSourceFunction =
      .ok targetFunction)
    (notImport : module.imports[functionIndex]? = none)
    (found : module.funcs[functionIndex - module.imports.length]? =
      some targetFunction)
    (memoryRelated : ResidentMemoryRel heap store.mem)
    (headerRead : heap.readLiveHeader address = .ok header) :
    Wasm.TerminatesWith env module functionIndex store
      ([.i32 (UInt32.ofNat address.value)] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 header.aux1 :: tail) := by
  obtain ⟨addressHeap, rawHeaderRead, _, headerMinimum, _, headerExtent⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts heap address header
      headerRead
  have selected : 1 &&& UInt32.ofNat address.value = 0 := by
    have even := address.lowBit_zero_of_classify_heap addressHeap
    apply UInt32.toNat_inj.mp
    simp [even, UInt32.toNat_ofNat_of_lt'
      (by simpa [wordModulus] using address.isLt)]
  let concreteAddress := address.value + headerAux1Offset
  have auxFits : headerAux1Offset + 4 ≤ headerBytes := by decide
  have concreteInBounds : concreteAddress + 3 < heap.memory.size := by
    dsimp [concreteAddress]
    omega
  have concreteRead :
      heap.memory.readUInt32 concreteAddress = .ok header.aux1 := by
    simpa [concreteAddress] using
      Header.read_aux1_eq_ok heap.memory address header rawHeaderRead
  have transported :=
    memoryRelated.readUInt32_eq_read32 concreteInBounds
  have targetAddress :
      UInt32.ofNat concreteAddress =
        UInt32.ofNat address.value + UInt32.ofNat headerAux1Offset := by
    dsimp [concreteAddress]
    rw [UInt32.ofNat_add]
  have targetRead :
      store.mem.read32
        (UInt32.ofNat address.value + UInt32.ofNat headerAux1Offset) =
          header.aux1 := by
    rw [← targetAddress]
    rw [concreteRead] at transported
    simpa using transported.symm
  have addressToNat : (UInt32.ofNat address.value).toNat = address.value :=
    UInt32.toNat_ofNat_of_lt' (by
      simpa [wordModulus] using address.isLt)
  have offsetToNat :
      (UInt32.ofNat headerAux1Offset).toNat = headerAux1Offset :=
    UInt32.toNat_ofNat_of_lt' (by decide)
  have memorySize : heap.memory.size = store.mem.pages * 65536 := by
    simpa [wasmPageBytes] using memoryRelated.size_eq
  have targetInBounds :
      ¬((UInt32.ofNat address.value).toNat +
          (UInt32.ofNat headerAux1Offset).toNat + 4 >
        store.mem.pages * 65536) := by
    rw [addressToNat, offsetToNat, ← memorySize]
    dsimp [concreteAddress] at concreteInBounds
    omega
  exact terminatesWith_naturalCountHeap_of_adapted adapted notImport found
    selected targetInBounds targetRead

/-- Ordinary heap-natural decoding supplies the live-header count contract. -/
theorem terminatesWith_naturalCount_of_objectRel
    {host : Type} {sourceModule : Fir.Wasm.Module}
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {targetFunction : Wasm.Function} {functionIndex : Nat}
    {heap : MemoryState} {store : Wasm.Store host}
    {address : Word32} {header : Header} {value : Nat}
    {tail : List Wasm.Value}
    (adapted : FirTalos.function sourceModule naturalCountSourceFunction =
      .ok targetFunction)
    (notImport : module.imports[functionIndex]? = none)
    (found : module.funcs[functionIndex - module.imports.length]? =
      some targetFunction)
    (memoryRelated : ResidentMemoryRel heap store.mem)
    (related : NaturalObjectRel heap address value header) :
    Wasm.TerminatesWith env module functionIndex store
      ([.i32 (UInt32.ofNat address.value)] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 header.aux1 :: tail) := by
  exact terminatesWith_naturalCount_of_liveHeader adapted notImport found
    memoryRelated related.headerRead

def magnitudeCountSourceFunction : Fir.Wasm.Function :=
  Fir.Wasm.Emit.ResidentBigNumeric.magnitudeCountFunction

def magnitudeCountSource : List Fir.Wasm.Instruction := [
  .localGet flavorParam,
  .ifElse
    [.localGet valueParam,
      .call (.declaration
        Fir.Wasm.Emit.ResidentBigNumeric.integerCountName),
      .ret]
    [.localGet valueParam,
      .call (.declaration
        Fir.Wasm.Emit.ResidentBigNumeric.naturalCountName),
      .ret]]

def magnitudeCountProgram (integerCountIndex naturalCountIndex : Nat) :
    Wasm.Program := [
  .localGet 1,
  .iff 0 0
    [.localGet 0, .call integerCountIndex, .ret]
    [.localGet 0, .call naturalCountIndex, .ret]]

theorem magnitudeCountSourceFunction_body :
    magnitudeCountSourceFunction.body = magnitudeCountSource := by
  rfl

theorem magnitudeCountSourceFunction_params :
    magnitudeCountSourceFunction.params =
      #[(valueParam, .tobject), (flavorParam, .uint32)] := by
  rfl

theorem magnitudeCountSourceFunction_locals :
    magnitudeCountSourceFunction.locals = #[] := by
  rfl

theorem magnitudeCountSourceFunction_results :
    magnitudeCountSourceFunction.results = #[.uint32] := by
  rfl

/-- Exact adaptation of the natural/integer magnitude-count dispatcher. -/
theorem instructions_magnitudeCountSourceFunction
    {sourceModule : Fir.Wasm.Module}
    {integerCountIndex naturalCountIndex : Nat}
    (integerCountFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.integerCountName) =
        some integerCountIndex)
    (naturalCountFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.naturalCountName) =
        some naturalCountIndex) :
    FirTalos.instructions sourceModule magnitudeCountSourceFunction []
      magnitudeCountSourceFunction.body =
        .ok (magnitudeCountProgram integerCountIndex naturalCountIndex) := by
  rw [magnitudeCountSourceFunction_body]
  have valueFound : FirTalos.findFVar?
      (magnitudeCountSourceFunction.params.toList ++
        magnitudeCountSourceFunction.locals.toList) valueParam = some 0 := by
    decide
  have flavorFound : FirTalos.findFVar?
      (magnitudeCountSourceFunction.params.toList ++
        magnitudeCountSourceFunction.locals.toList) flavorParam = some 1 := by
    decide
  simp [magnitudeCountSource, magnitudeCountProgram, FirTalos.instructions,
    FirTalos.instruction, valueFound, flavorFound, integerCountFound,
    naturalCountFound, Bind.bind, Except.bind, pure, Except.pure]

theorem adaptedMagnitudeCountSourceFunction_body
    {sourceModule : Fir.Wasm.Module} {targetFunction : Wasm.Function}
    {integerCountIndex naturalCountIndex : Nat}
    (adapted : FirTalos.function sourceModule magnitudeCountSourceFunction =
      .ok targetFunction)
    (integerCountFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.integerCountName) =
        some integerCountIndex)
    (naturalCountFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.naturalCountName) =
        some naturalCountIndex) :
    targetFunction.body =
        magnitudeCountProgram integerCountIndex naturalCountIndex ++
          FirTalos.functionTerminal sourceModule
            magnitudeCountSourceFunction := by
  exact ResidentPrimitives.adaptedFunction_body_of_exact adapted
    (instructions_magnitudeCountSourceFunction integerCountFound
      naturalCountFound)

/-- Natural flavor (`0`) delegates exactly to the installed natural-count
helper.  No integer helper behavior is assumed. -/
theorem wp_magnitudeCountProgram_natural
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {initial : Wasm.Locals} {integerCountIndex naturalCountIndex : Nat}
    {word count : UInt32} {tail : List Wasm.Value}
    {rest : Wasm.Program}
    (valueLocal : initial.get 0 = some (.i32 word))
    (flavorLocal : initial.get 1 = some (.i32 0))
    (naturalCountRun : Wasm.TerminatesWith env module naturalCountIndex store
      (.i32 word :: tail)
      (fun final values =>
        final = store ∧ values = .i32 count :: tail))
    (returned : Q (.Return store (.i32 count :: tail))) :
    Wasm.wp module
      (magnitudeCountProgram integerCountIndex naturalCountIndex ++ rest)
      Q store { initial with values := tail } env := by
  have valueLocal' (values : List Wasm.Value) :
      ({ initial with values } : Wasm.Locals).get 0 =
        some (.i32 word) := by
    simpa using valueLocal
  have flavorLocal' :
      ({ initial with values := tail } : Wasm.Locals).get 1 =
        some (.i32 0) := by
    simpa using flavorLocal
  unfold magnitudeCountProgram
  simp only [List.cons_append, List.nil_append, Wasm.wp_localGet_cons,
    flavorLocal']
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  simp only [Wasm.wp_localGet_cons, valueLocal']
  apply Wasm.wp_call_tw naturalCountRun
  intro final values completed
  rcases completed with ⟨rfl, rfl⟩
  simp only [Wasm.wp_ret_cons]
  exact returned

/-- Installed natural-flavor magnitude count, composed from the installed
natural-count helper and preserving the outer caller tail exactly. -/
theorem terminatesWith_magnitudeCountNatural_of_adapted
    {host : Type} {sourceModule : Fir.Wasm.Module}
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {targetFunction : Wasm.Function} {functionIndex : Nat}
    {integerCountIndex naturalCountIndex : Nat}
    {store : Wasm.Store host} {word count : UInt32}
    {tail : List Wasm.Value}
    (adapted : FirTalos.function sourceModule magnitudeCountSourceFunction =
      .ok targetFunction)
    (integerCountFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.integerCountName) =
        some integerCountIndex)
    (naturalCountFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.naturalCountName) =
        some naturalCountIndex)
    (notImport : module.imports[functionIndex]? = none)
    (found : module.funcs[functionIndex - module.imports.length]? =
      some targetFunction)
    (naturalCountRun : Wasm.TerminatesWith env module naturalCountIndex store
      [.i32 word]
      (fun final values => final = store ∧ values = [.i32 count])) :
    Wasm.TerminatesWith env module functionIndex store
      ([.i32 0, .i32 word] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 count :: tail) := by
  have signature :=
    FirTalos.Correctness.function_preserves_signature adapted
  rcases signature with ⟨paramsEq, localsEq, resultsEq⟩
  have body := adaptedMagnitudeCountSourceFunction_body adapted
    integerCountFound naturalCountFound
  apply FirTalos.Correctness.terminatesWith_of_wp_body_at notImport found
  rw [body]
  let arguments := [.i32 0, .i32 word] ++ tail
  let entry := targetFunction.toLocals
    (arguments.take targetFunction.numParams).reverse
  have valueLocal : entry.get 0 = some (.i32 word) := by
    simp [entry, arguments, Wasm.Function.toLocals,
      Wasm.Function.numParams, paramsEq, magnitudeCountSourceFunction_params]
  have flavorLocal : entry.get 1 = some (.i32 0) := by
    simp [entry, arguments, Wasm.Function.toLocals,
      Wasm.Function.numParams, paramsEq, magnitudeCountSourceFunction_params]
  have returned :
      FirTalos.Correctness.FunctionBodyPost targetFunction arguments
        (fun final values =>
          final = store ∧ values = .i32 count :: tail)
        (.Return store [.i32 count]) := by
    simp [FirTalos.Correctness.FunctionBodyPost, arguments,
      Wasm.Function.numParams, paramsEq, resultsEq,
      magnitudeCountSourceFunction_params,
      magnitudeCountSourceFunction_results]
  simpa [entry, arguments, Wasm.Function.toLocals] using
    (wp_magnitudeCountProgram_natural
      (module := module) (env := env) (store := store) (initial := entry)
      (integerCountIndex := integerCountIndex)
      (naturalCountIndex := naturalCountIndex)
      (rest := FirTalos.functionTerminal sourceModule
        magnitudeCountSourceFunction)
      (tail := []) valueLocal flavorLocal naturalCountRun returned)

/-- Fully concrete natural-flavor count for a validated heap object. -/
theorem terminatesWith_magnitudeCountNatural_of_liveHeader
    {host : Type} {sourceModule : Fir.Wasm.Module}
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {naturalCountTarget magnitudeCountTarget : Wasm.Function}
    {naturalCountIndex magnitudeCountIndex integerCountIndex : Nat}
    {heap : MemoryState} {store : Wasm.Store host}
    {address : Word32} {header : Header} {tail : List Wasm.Value}
    (naturalCountAdapted : FirTalos.function sourceModule
      naturalCountSourceFunction = .ok naturalCountTarget)
    (naturalCountNotImport : module.imports[naturalCountIndex]? = none)
    (naturalCountInstalled :
      module.funcs[naturalCountIndex - module.imports.length]? =
        some naturalCountTarget)
    (magnitudeCountAdapted : FirTalos.function sourceModule
      magnitudeCountSourceFunction = .ok magnitudeCountTarget)
    (integerCountFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.integerCountName) =
        some integerCountIndex)
    (naturalCountFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.naturalCountName) =
        some naturalCountIndex)
    (magnitudeCountNotImport : module.imports[magnitudeCountIndex]? = none)
    (magnitudeCountInstalled :
      module.funcs[magnitudeCountIndex - module.imports.length]? =
        some magnitudeCountTarget)
    (memoryRelated : ResidentMemoryRel heap store.mem)
    (headerRead : heap.readLiveHeader address = .ok header) :
    Wasm.TerminatesWith env module magnitudeCountIndex store
      ([.i32 0, .i32 (UInt32.ofNat address.value)] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 header.aux1 :: tail) := by
  have naturalCountRun :
      Wasm.TerminatesWith env module naturalCountIndex store
        [.i32 (UInt32.ofNat address.value)]
        (fun final values =>
          final = store ∧ values = [.i32 header.aux1]) :=
    terminatesWith_naturalCount_of_liveHeader
      (env := env) (tail := []) naturalCountAdapted naturalCountNotImport
      naturalCountInstalled memoryRelated headerRead
  exact terminatesWith_magnitudeCountNatural_of_adapted
    (env := env) (tail := tail) magnitudeCountAdapted integerCountFound
    naturalCountFound magnitudeCountNotImport magnitudeCountInstalled
    naturalCountRun

/-- Fully concrete natural-flavor count for an ordinary heap natural. -/
theorem terminatesWith_magnitudeCountNatural_of_objectRel
    {host : Type} {sourceModule : Fir.Wasm.Module}
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {naturalCountTarget magnitudeCountTarget : Wasm.Function}
    {naturalCountIndex magnitudeCountIndex integerCountIndex : Nat}
    {heap : MemoryState} {store : Wasm.Store host}
    {address : Word32} {header : Header} {value : Nat}
    {tail : List Wasm.Value}
    (naturalCountAdapted : FirTalos.function sourceModule
      naturalCountSourceFunction = .ok naturalCountTarget)
    (naturalCountNotImport : module.imports[naturalCountIndex]? = none)
    (naturalCountInstalled :
      module.funcs[naturalCountIndex - module.imports.length]? =
        some naturalCountTarget)
    (magnitudeCountAdapted : FirTalos.function sourceModule
      magnitudeCountSourceFunction = .ok magnitudeCountTarget)
    (integerCountFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.integerCountName) =
        some integerCountIndex)
    (naturalCountFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.naturalCountName) =
        some naturalCountIndex)
    (magnitudeCountNotImport : module.imports[magnitudeCountIndex]? = none)
    (magnitudeCountInstalled :
      module.funcs[magnitudeCountIndex - module.imports.length]? =
        some magnitudeCountTarget)
    (memoryRelated : ResidentMemoryRel heap store.mem)
    (related : NaturalObjectRel heap address value header) :
    Wasm.TerminatesWith env module magnitudeCountIndex store
      ([.i32 0, .i32 (UInt32.ofNat address.value)] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 header.aux1 :: tail) := by
  exact terminatesWith_magnitudeCountNatural_of_liveHeader
    naturalCountAdapted naturalCountNotImport naturalCountInstalled
    magnitudeCountAdapted integerCountFound naturalCountFound
    magnitudeCountNotImport magnitudeCountInstalled memoryRelated
    related.headerRead

def magnitudeLimbSourceFunction : NaturalLimbPart → Fir.Wasm.Function
  | .low => Fir.Wasm.Emit.ResidentBigNumeric.magnitudeLowFunction
  | .high => Fir.Wasm.Emit.ResidentBigNumeric.magnitudeHighFunction

def naturalLimbCallTarget : NaturalLimbPart → Fir.Wasm.CallTarget
  | .low => .declaration Fir.Wasm.Emit.ResidentBigNumeric.naturalLowName
  | .high => .declaration Fir.Wasm.Emit.ResidentBigNumeric.naturalHighName

def integerLimbCallTarget : NaturalLimbPart → Fir.Wasm.CallTarget
  | .low => .declaration Fir.Wasm.Emit.ResidentBigNumeric.integerLowName
  | .high => .declaration Fir.Wasm.Emit.ResidentBigNumeric.integerHighName

def magnitudeLimbSource (part : NaturalLimbPart) :
    List Fir.Wasm.Instruction := [
  .localGet valueParam,
  .localGet flavorParam,
  .call (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeCountName),
  .localSet countLocal,
  .localGet indexParam,
  .localGet countLocal,
  .i32LtU,
  .ifElse
    [.localGet flavorParam,
      .ifElse
        [.localGet valueParam,
          .localGet indexParam,
          .call (integerLimbCallTarget part),
          .ret]
        [.localGet valueParam,
          .localGet indexParam,
          .call (naturalLimbCallTarget part),
          .ret]]
    [.i32Const .uint32 0, .ret]]

def magnitudeLimbProgram (magnitudeCountIndex integerLimbIndex
    naturalLimbIndex : Nat) : Wasm.Program := [
  .localGet 0,
  .localGet 1,
  .call magnitudeCountIndex,
  .localSet 3,
  .localGet 2,
  .localGet 3,
  .ltU,
  .iff 0 0
    [.localGet 1,
      .iff 0 0
        [.localGet 0, .localGet 2, .call integerLimbIndex, .ret]
        [.localGet 0, .localGet 2, .call naturalLimbIndex, .ret]]
    [.const 0, .ret]]

theorem magnitudeLimbSourceFunction_body (part : NaturalLimbPart) :
    (magnitudeLimbSourceFunction part).body = magnitudeLimbSource part := by
  cases part <;> rfl

theorem magnitudeLimbSourceFunction_params (part : NaturalLimbPart) :
    (magnitudeLimbSourceFunction part).params =
      #[(valueParam, .tobject), (flavorParam, .uint32),
        (indexParam, .uint32)] := by
  cases part <;> rfl

theorem magnitudeLimbSourceFunction_locals (part : NaturalLimbPart) :
    (magnitudeLimbSourceFunction part).locals =
      #[(countLocal, .uint32)] := by
  cases part <;> rfl

theorem magnitudeLimbSourceFunction_results (part : NaturalLimbPart) :
    (magnitudeLimbSourceFunction part).results = #[.uint32] := by
  cases part <;> rfl

/-- Exact adaptation of either magnitude low/high dispatcher. -/
theorem instructions_magnitudeLimbSourceFunction
    {sourceModule : Fir.Wasm.Module} {part : NaturalLimbPart}
    {magnitudeCountIndex integerLimbIndex naturalLimbIndex : Nat}
    (magnitudeCountFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeCountName) =
        some magnitudeCountIndex)
    (integerLimbFound : FirTalos.callIndex? sourceModule
      (integerLimbCallTarget part) = some integerLimbIndex)
    (naturalLimbFound : FirTalos.callIndex? sourceModule
      (naturalLimbCallTarget part) = some naturalLimbIndex) :
    FirTalos.instructions sourceModule (magnitudeLimbSourceFunction part) []
      (magnitudeLimbSourceFunction part).body =
        .ok (magnitudeLimbProgram magnitudeCountIndex integerLimbIndex
          naturalLimbIndex) := by
  rw [magnitudeLimbSourceFunction_body]
  have valueFound : FirTalos.findFVar?
      ((magnitudeLimbSourceFunction part).params.toList ++
        (magnitudeLimbSourceFunction part).locals.toList) valueParam =
          some 0 := by
    cases part <;> decide
  have flavorFound : FirTalos.findFVar?
      ((magnitudeLimbSourceFunction part).params.toList ++
        (magnitudeLimbSourceFunction part).locals.toList) flavorParam =
          some 1 := by
    cases part <;> decide
  have indexFound : FirTalos.findFVar?
      ((magnitudeLimbSourceFunction part).params.toList ++
        (magnitudeLimbSourceFunction part).locals.toList) indexParam =
          some 2 := by
    cases part <;> decide
  have countFound : FirTalos.findFVar?
      ((magnitudeLimbSourceFunction part).params.toList ++
        (magnitudeLimbSourceFunction part).locals.toList) countLocal =
          some 3 := by
    cases part <;> decide
  simp [magnitudeLimbSource, magnitudeLimbProgram,
    FirTalos.instructions, FirTalos.instruction, valueFound, flavorFound,
    indexFound, countFound, magnitudeCountFound, integerLimbFound,
    naturalLimbFound, Bind.bind, Except.bind, pure, Except.pure]

theorem adaptedMagnitudeLimbSourceFunction_body
    {sourceModule : Fir.Wasm.Module} {targetFunction : Wasm.Function}
    {part : NaturalLimbPart}
    {magnitudeCountIndex integerLimbIndex naturalLimbIndex : Nat}
    (adapted : FirTalos.function sourceModule
      (magnitudeLimbSourceFunction part) = .ok targetFunction)
    (magnitudeCountFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeCountName) =
        some magnitudeCountIndex)
    (integerLimbFound : FirTalos.callIndex? sourceModule
      (integerLimbCallTarget part) = some integerLimbIndex)
    (naturalLimbFound : FirTalos.callIndex? sourceModule
      (naturalLimbCallTarget part) = some naturalLimbIndex) :
    targetFunction.body =
        magnitudeLimbProgram magnitudeCountIndex integerLimbIndex
            naturalLimbIndex ++
          FirTalos.functionTerminal sourceModule
            (magnitudeLimbSourceFunction part) := by
  exact ResidentPrimitives.adaptedFunction_body_of_exact adapted
    (instructions_magnitudeLimbSourceFunction magnitudeCountFound
      integerLimbFound naturalLimbFound)

/-- An in-range natural-flavor magnitude access is exactly count, bounds
check, and delegation to the corresponding natural low/high helper. -/
theorem wp_magnitudeLimbProgram_natural_inBounds
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {initial afterCount : Wasm.Locals}
    {magnitudeCountIndex integerLimbIndex naturalLimbIndex : Nat}
    {word index count result : UInt32} {tail : List Wasm.Value}
    {rest : Wasm.Program}
    (valueLocal : initial.get 0 = some (.i32 word))
    (flavorLocal : initial.get 1 = some (.i32 0))
    (indexLocal : initial.get 2 = some (.i32 index))
    (countSet :
      ({ initial with values := .i32 count :: tail }).set? 3
        (.i32 count) = some afterCount)
    (indexInBounds : index < count)
    (magnitudeCountRun : Wasm.TerminatesWith env module magnitudeCountIndex
      store ([.i32 0, .i32 word] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 count :: tail))
    (naturalLimbRun : Wasm.TerminatesWith env module naturalLimbIndex store
      ([.i32 index, .i32 word] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 result :: tail))
    (returned : Q (.Return store (.i32 result :: tail))) :
    Wasm.wp module
      (magnitudeLimbProgram magnitudeCountIndex integerLimbIndex
          naturalLimbIndex ++ rest)
      Q store { initial with values := tail } env := by
  have countUpdate := FirTalos.Correctness.localUpdate_of_set? countSet
  have initialAt (slot : Nat) (value : Wasm.Value)
      (found : initial.get slot = some value) (values : List Wasm.Value) :
      ({ initial with values } : Wasm.Locals).get slot = some value := by
    simpa using found
  have afterCountAt (slot : Nat) (value : Wasm.Value)
      (different : slot ≠ 3) (found : initial.get slot = some value)
      (values : List Wasm.Value) :
      ({ afterCount with values } : Wasm.Locals).get slot = some value := by
    change afterCount.get slot = some value
    rw [countUpdate.2 different]
    exact found
  have countAt (values : List Wasm.Value) :
      ({ afterCount with values } : Wasm.Locals).get 3 =
        some (.i32 count) := by
    simpa using countUpdate.1
  unfold magnitudeLimbProgram
  simp only [List.cons_append, List.nil_append, Wasm.wp_localGet_cons,
    initialAt 0 (.i32 word) valueLocal,
    initialAt 1 (.i32 0) flavorLocal]
  apply Wasm.wp_call_tw magnitudeCountRun
  intro final values completedCount
  rcases completedCount with ⟨rfl, rfl⟩
  simp only [Wasm.wp_localSet_cons, countSet, Wasm.wp_localGet_cons,
    afterCountAt 2 (.i32 index) (by decide) indexLocal,
    countAt]
  rw [Wasm.wp_ltU_cons]
  simp only [indexInBounds, ↓reduceIte]
  apply Wasm.wp_iff_cons rfl
  rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
  simp only [Wasm.wp_localGet_cons,
    afterCountAt 1 (.i32 0) (by decide) flavorLocal]
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  simp only [Wasm.wp_localGet_cons,
    afterCountAt 0 (.i32 word) (by decide) valueLocal,
    afterCountAt 2 (.i32 index) (by decide) indexLocal]
  apply Wasm.wp_call_tw naturalLimbRun
  intro final values completedLimb
  rcases completedLimb with ⟨rfl, rfl⟩
  simp only [Wasm.wp_ret_cons]
  exact returned

/-- An out-of-range magnitude access returns zero after the count call and
does not require either natural or integer limb helper. -/
theorem wp_magnitudeLimbProgram_natural_outOfBounds
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {initial afterCount : Wasm.Locals}
    {magnitudeCountIndex integerLimbIndex naturalLimbIndex : Nat}
    {word index count : UInt32} {tail : List Wasm.Value}
    {rest : Wasm.Program}
    (valueLocal : initial.get 0 = some (.i32 word))
    (flavorLocal : initial.get 1 = some (.i32 0))
    (indexLocal : initial.get 2 = some (.i32 index))
    (countSet :
      ({ initial with values := .i32 count :: tail }).set? 3
        (.i32 count) = some afterCount)
    (indexOutOfBounds : ¬index < count)
    (magnitudeCountRun : Wasm.TerminatesWith env module magnitudeCountIndex
      store ([.i32 0, .i32 word] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 count :: tail))
    (returned : Q (.Return store (.i32 0 :: tail))) :
    Wasm.wp module
      (magnitudeLimbProgram magnitudeCountIndex integerLimbIndex
          naturalLimbIndex ++ rest)
      Q store { initial with values := tail } env := by
  have countUpdate := FirTalos.Correctness.localUpdate_of_set? countSet
  have initialAt (slot : Nat) (value : Wasm.Value)
      (found : initial.get slot = some value) (values : List Wasm.Value) :
      ({ initial with values } : Wasm.Locals).get slot = some value := by
    simpa using found
  have afterCountAt (slot : Nat) (value : Wasm.Value)
      (different : slot ≠ 3) (found : initial.get slot = some value)
      (values : List Wasm.Value) :
      ({ afterCount with values } : Wasm.Locals).get slot = some value := by
    change afterCount.get slot = some value
    rw [countUpdate.2 different]
    exact found
  have countAt (values : List Wasm.Value) :
      ({ afterCount with values } : Wasm.Locals).get 3 =
        some (.i32 count) := by
    simpa using countUpdate.1
  unfold magnitudeLimbProgram
  simp only [List.cons_append, List.nil_append, Wasm.wp_localGet_cons,
    initialAt 0 (.i32 word) valueLocal,
    initialAt 1 (.i32 0) flavorLocal]
  apply Wasm.wp_call_tw magnitudeCountRun
  intro final values completedCount
  rcases completedCount with ⟨rfl, rfl⟩
  simp only [Wasm.wp_localSet_cons, countSet, Wasm.wp_localGet_cons,
    afterCountAt 2 (.i32 index) (by decide) indexLocal, countAt]
  rw [Wasm.wp_ltU_cons]
  simp only [indexOutOfBounds, ↓reduceIte]
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  simp only [Wasm.wp_const_cons, Wasm.wp_ret_cons]
  exact returned

/-- Installed in-range natural-flavor magnitude access.  Its only semantic
dependencies are the exact installed count and natural-limb calls. -/
theorem terminatesWith_magnitudeLimbNatural_inBounds_of_adapted
    {host : Type} {sourceModule : Fir.Wasm.Module}
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {targetFunction : Wasm.Function} {functionIndex : Nat}
    {part : NaturalLimbPart}
    {magnitudeCountIndex integerLimbIndex naturalLimbIndex : Nat}
    {store : Wasm.Store host} {word index count result : UInt32}
    {tail : List Wasm.Value}
    (adapted : FirTalos.function sourceModule
      (magnitudeLimbSourceFunction part) = .ok targetFunction)
    (magnitudeCountFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeCountName) =
        some magnitudeCountIndex)
    (integerLimbFound : FirTalos.callIndex? sourceModule
      (integerLimbCallTarget part) = some integerLimbIndex)
    (naturalLimbFound : FirTalos.callIndex? sourceModule
      (naturalLimbCallTarget part) = some naturalLimbIndex)
    (notImport : module.imports[functionIndex]? = none)
    (found : module.funcs[functionIndex - module.imports.length]? =
      some targetFunction)
    (indexInBounds : index < count)
    (magnitudeCountRun : Wasm.TerminatesWith env module magnitudeCountIndex
      store [.i32 0, .i32 word]
      (fun final values => final = store ∧ values = [.i32 count]))
    (naturalLimbRun : Wasm.TerminatesWith env module naturalLimbIndex store
      [.i32 index, .i32 word]
      (fun final values => final = store ∧ values = [.i32 result])) :
    Wasm.TerminatesWith env module functionIndex store
      ([.i32 index, .i32 0, .i32 word] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 result :: tail) := by
  have signature :=
    FirTalos.Correctness.function_preserves_signature adapted
  rcases signature with ⟨paramsEq, localsEq, resultsEq⟩
  have body := adaptedMagnitudeLimbSourceFunction_body adapted
    magnitudeCountFound integerLimbFound naturalLimbFound
  apply FirTalos.Correctness.terminatesWith_of_wp_body_at notImport found
  rw [body]
  let arguments := [.i32 index, .i32 0, .i32 word] ++ tail
  let entry := targetFunction.toLocals
    (arguments.take targetFunction.numParams).reverse
  have valueLocal : entry.get 0 = some (.i32 word) := by
    simp [entry, arguments, Wasm.Function.toLocals,
      Wasm.Function.numParams, paramsEq,
      magnitudeLimbSourceFunction_params]
  have flavorLocal : entry.get 1 = some (.i32 0) := by
    simp [entry, arguments, Wasm.Function.toLocals,
      Wasm.Function.numParams, paramsEq,
      magnitudeLimbSourceFunction_params]
  have indexLocal : entry.get 2 = some (.i32 index) := by
    simp [entry, arguments, Wasm.Function.toLocals,
      Wasm.Function.numParams, paramsEq,
      magnitudeLimbSourceFunction_params]
  have targetLocalsLength : targetFunction.locals.length = 1 := by
    simp [localsEq, magnitudeLimbSourceFunction_locals]
  have countValid :
      ({ entry with values := [.i32 count] }).validIndex 3 := by
    simp [entry, arguments, Wasm.Function.toLocals,
      Wasm.Function.numParams, paramsEq,
      magnitudeLimbSourceFunction_params, targetLocalsLength]
  obtain ⟨afterCount, countSet⟩ :=
    FirTalos.Correctness.locals_set?_exists
      (value := .i32 count) countValid
  have returned :
      FirTalos.Correctness.FunctionBodyPost targetFunction arguments
        (fun final values =>
          final = store ∧ values = .i32 result :: tail)
        (.Return store [.i32 result]) := by
    simp [FirTalos.Correctness.FunctionBodyPost, arguments,
      Wasm.Function.numParams, paramsEq, resultsEq,
      magnitudeLimbSourceFunction_params,
      magnitudeLimbSourceFunction_results]
  simpa [entry, arguments, Wasm.Function.toLocals] using
    (wp_magnitudeLimbProgram_natural_inBounds
      (module := module) (env := env) (store := store) (initial := entry)
      (afterCount := afterCount)
      (magnitudeCountIndex := magnitudeCountIndex)
      (integerLimbIndex := integerLimbIndex)
      (naturalLimbIndex := naturalLimbIndex)
      (rest := FirTalos.functionTerminal sourceModule
        (magnitudeLimbSourceFunction part))
      (tail := []) valueLocal flavorLocal indexLocal countSet indexInBounds
      magnitudeCountRun naturalLimbRun returned)

/-- Installed out-of-range natural-flavor magnitude access.  The helper
returns zero without invoking either physical limb accessor. -/
theorem terminatesWith_magnitudeLimbNatural_outOfBounds_of_adapted
    {host : Type} {sourceModule : Fir.Wasm.Module}
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {targetFunction : Wasm.Function} {functionIndex : Nat}
    {part : NaturalLimbPart}
    {magnitudeCountIndex integerLimbIndex naturalLimbIndex : Nat}
    {store : Wasm.Store host} {word index count : UInt32}
    {tail : List Wasm.Value}
    (adapted : FirTalos.function sourceModule
      (magnitudeLimbSourceFunction part) = .ok targetFunction)
    (magnitudeCountFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.magnitudeCountName) =
        some magnitudeCountIndex)
    (integerLimbFound : FirTalos.callIndex? sourceModule
      (integerLimbCallTarget part) = some integerLimbIndex)
    (naturalLimbFound : FirTalos.callIndex? sourceModule
      (naturalLimbCallTarget part) = some naturalLimbIndex)
    (notImport : module.imports[functionIndex]? = none)
    (found : module.funcs[functionIndex - module.imports.length]? =
      some targetFunction)
    (indexOutOfBounds : ¬index < count)
    (magnitudeCountRun : Wasm.TerminatesWith env module magnitudeCountIndex
      store [.i32 0, .i32 word]
      (fun final values => final = store ∧ values = [.i32 count])) :
    Wasm.TerminatesWith env module functionIndex store
      ([.i32 index, .i32 0, .i32 word] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 0 :: tail) := by
  have signature :=
    FirTalos.Correctness.function_preserves_signature adapted
  rcases signature with ⟨paramsEq, localsEq, resultsEq⟩
  have body := adaptedMagnitudeLimbSourceFunction_body adapted
    magnitudeCountFound integerLimbFound naturalLimbFound
  apply FirTalos.Correctness.terminatesWith_of_wp_body_at notImport found
  rw [body]
  let arguments := [.i32 index, .i32 0, .i32 word] ++ tail
  let entry := targetFunction.toLocals
    (arguments.take targetFunction.numParams).reverse
  have valueLocal : entry.get 0 = some (.i32 word) := by
    simp [entry, arguments, Wasm.Function.toLocals,
      Wasm.Function.numParams, paramsEq,
      magnitudeLimbSourceFunction_params]
  have flavorLocal : entry.get 1 = some (.i32 0) := by
    simp [entry, arguments, Wasm.Function.toLocals,
      Wasm.Function.numParams, paramsEq,
      magnitudeLimbSourceFunction_params]
  have indexLocal : entry.get 2 = some (.i32 index) := by
    simp [entry, arguments, Wasm.Function.toLocals,
      Wasm.Function.numParams, paramsEq,
      magnitudeLimbSourceFunction_params]
  have targetLocalsLength : targetFunction.locals.length = 1 := by
    simp [localsEq, magnitudeLimbSourceFunction_locals]
  have countValid :
      ({ entry with values := [.i32 count] }).validIndex 3 := by
    simp [entry, arguments, Wasm.Function.toLocals,
      Wasm.Function.numParams, paramsEq,
      magnitudeLimbSourceFunction_params, targetLocalsLength]
  obtain ⟨afterCount, countSet⟩ :=
    FirTalos.Correctness.locals_set?_exists
      (value := .i32 count) countValid
  have returned :
      FirTalos.Correctness.FunctionBodyPost targetFunction arguments
        (fun final values =>
          final = store ∧ values = .i32 0 :: tail)
        (.Return store [.i32 0]) := by
    simp [FirTalos.Correctness.FunctionBodyPost, arguments,
      Wasm.Function.numParams, paramsEq, resultsEq,
      magnitudeLimbSourceFunction_params,
      magnitudeLimbSourceFunction_results]
  simpa [entry, arguments, Wasm.Function.toLocals] using
    (wp_magnitudeLimbProgram_natural_outOfBounds
      (module := module) (env := env) (store := store) (initial := entry)
      (afterCount := afterCount)
      (magnitudeCountIndex := magnitudeCountIndex)
      (integerLimbIndex := integerLimbIndex)
      (naturalLimbIndex := naturalLimbIndex)
      (rest := FirTalos.functionTerminal sourceModule
        (magnitudeLimbSourceFunction part))
      (tail := []) valueLocal flavorLocal indexLocal countSet indexOutOfBounds
      magnitudeCountRun returned)

def scale8Source : List Fir.Wasm.Instruction :=
  ResidentPrimitives.scale8Source indexParam scaledLocal

def naturalLimbSource (part : NaturalLimbPart) :
    List Fir.Wasm.Instruction := [
  .localGet valueParam,
  .i32Const .uint32 1,
  .i32And,
  .ifElse [
    .localGet indexParam,
    .i32Const .uint32 0,
    .i32Eq,
    .ifElse
      (match part with
      | .low => [
          .localGet valueParam,
          .i32Const .uint32 1,
          .i32ShrU,
          .ret]
      | .high => [.i32Const .uint32 0, .ret])
      [.i32Const .uint32 0, .ret]]
    (scale8Source ++ [
      .localGet valueParam,
      .i32Const .uint32 (UInt32.ofNat headerBytes),
      .i32Add,
      .localGet scaledLocal,
      .i32Add,
      .i32Load .uint32 (byteOffset part),
      .ret])]

def immediateLimbProgram : NaturalLimbPart → Wasm.Program
  | .low => [.localGet 0, .const 1, .shrU, .ret]
  | .high => [.const 0, .ret]

def heapLimbProgram (part : NaturalLimbPart) : Wasm.Program :=
  ResidentPrimitives.scale8Program 1 2 ++ [
  .localGet 0,
  .const (UInt32.ofNat headerBytes),
  .add,
  .localGet 2,
  .add,
  .load32 (byteOffset part),
  .ret]

def naturalLimbProgram (part : NaturalLimbPart) : Wasm.Program := [
  .localGet 0,
  .const 1,
  .and,
  .iff 0 0 [
    .localGet 1,
    .const 0,
    .eq,
    .iff 0 0 (immediateLimbProgram part) [.const 0, .ret]]
    (heapLimbProgram part)]

theorem sourceFunction_body (part : NaturalLimbPart) :
    (sourceFunction part).body = naturalLimbSource part := by
  cases part <;> rfl

theorem sourceFunction_params (part : NaturalLimbPart) :
    (sourceFunction part).params =
      #[(valueParam, .tobject), (indexParam, .uint32)] := by
  cases part <;> rfl

theorem sourceFunction_locals (part : NaturalLimbPart) :
    (sourceFunction part).locals = #[(scaledLocal, .uint32)] := by
  cases part <;> rfl

theorem sourceFunction_results (part : NaturalLimbPart) :
    (sourceFunction part).results = #[.uint32] := by
  cases part <;> rfl

/-- The adapter preserves both public limb helpers exactly. -/
theorem instructions_sourceFunction
    {sourceModule : Fir.Wasm.Module} (part : NaturalLimbPart) :
    FirTalos.instructions sourceModule (sourceFunction part) []
      (sourceFunction part).body = .ok (naturalLimbProgram part) := by
  rw [sourceFunction_body]
  have valueFound : FirTalos.findFVar?
      ((sourceFunction part).params.toList ++
        (sourceFunction part).locals.toList) valueParam = some 0 := by
    cases part <;> decide
  have indexFound : FirTalos.findFVar?
      ((sourceFunction part).params.toList ++
        (sourceFunction part).locals.toList) indexParam = some 1 := by
    cases part <;> decide
  have scaledFound : FirTalos.findFVar?
      ((sourceFunction part).params.toList ++
        (sourceFunction part).locals.toList) scaledLocal = some 2 := by
    cases part <;> decide
  cases part <;>
    simp [naturalLimbSource, scale8Source, naturalLimbProgram,
      immediateLimbProgram, heapLimbProgram,
      ResidentPrimitives.scale8Source, ResidentPrimitives.scale8Program,
      byteOffset, FirTalos.instructions, FirTalos.instruction, valueFound,
      indexFound, scaledFound, Bind.bind, Except.bind, pure, Except.pure]

/-- Exact installed target body, including the adapter's terminal suffix. -/
theorem adaptedSourceFunction_body
    {sourceModule : Fir.Wasm.Module} {targetFunction : Wasm.Function}
    {part : NaturalLimbPart}
    (adapted : FirTalos.function sourceModule (sourceFunction part) =
      .ok targetFunction) :
    targetFunction.body = naturalLimbProgram part ++
      FirTalos.functionTerminal sourceModule (sourceFunction part) := by
  exact ResidentPrimitives.adaptedFunction_body_of_exact adapted
    (instructions_sourceFunction part)

/-- Heap-classified object words select the heap arm of the public limb
accessors.  This small fact belongs with the accessor itself rather than with
any particular consumer such as USize conversion. -/
theorem heapWord_selected (word : Word32)
    (heap : word.classify = .heap) :
    1 &&& UInt32.ofNat word.value = 0 := by
  have even := word.lowBit_zero_of_classify_heap heap
  apply UInt32.toNat_inj.mp
  simp [even, UInt32.toNat_ofNat_of_lt'
    (by simpa [wordModulus] using word.isLt)]

/-- The heap arm at an arbitrary limb index returns exactly the selected
32-bit half-limb.  Its only arithmetic abstraction is the shared modular
multiply-by-eight primitive; object layout and non-wrapping facts remain for
the concrete-memory refinement theorem below. -/
theorem wp_heapLimbProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {initial afterFirst afterSecond afterThird : Wasm.Locals}
    {part : NaturalLimbPart} {word index result : UInt32}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    (valueLocal : initial.get 0 = some (.i32 word))
    (indexLocal : initial.get 1 = some (.i32 index))
    (firstSet :
      ({ initial with values := .i32 (index + index) :: tail }).set? 2
        (.i32 (index + index)) = some afterFirst)
    (secondSet :
      ({ afterFirst with values :=
          (.i32 (index + index + (index + index)) :: tail) }).set? 2
        (.i32 (index + index + (index + index))) = some afterSecond)
    (thirdSet :
      ({ afterSecond with values :=
          (.i32 (ResidentPrimitives.scale8Word index) :: tail) }).set? 2
        (.i32 (ResidentPrimitives.scale8Word index)) = some afterThird)
    (readInBounds :
      ¬((ResidentPrimitives.scale8Word index +
          (UInt32.ofNat headerBytes + word)).toNat +
        (byteOffset part).toNat + 4 > store.mem.pages * 65536))
    (readEq :
      store.mem.read32
        (ResidentPrimitives.scale8Word index +
          (UInt32.ofNat headerBytes + word) + byteOffset part) = result)
    (returned : Q (.Return store (.i32 result :: tail))) :
    Wasm.wp module (heapLimbProgram part ++ rest) Q store
      { initial with values := tail } env := by
  have firstUpdate := FirTalos.Correctness.localUpdate_of_set? firstSet
  have secondUpdate := FirTalos.Correctness.localUpdate_of_set? secondSet
  have thirdUpdate := FirTalos.Correctness.localUpdate_of_set? thirdSet
  have valueAfterFirst : afterFirst.get 0 = some (.i32 word) := by
    rw [firstUpdate.2 (show 0 ≠ 2 by decide)]
    simpa using valueLocal
  have valueAfterSecond : afterSecond.get 0 = some (.i32 word) := by
    rw [secondUpdate.2 (show 0 ≠ 2 by decide)]
    simpa using valueAfterFirst
  have valueThird (values : List Wasm.Value) :
      ({ afterThird with values } : Wasm.Locals).get 0 =
        some (.i32 word) := by
    rw [show ({ afterThird with values } : Wasm.Locals).get 0 =
      afterThird.get 0 by rfl, thirdUpdate.2 (show 0 ≠ 2 by decide)]
    simpa using valueAfterSecond
  have scaledThird (values : List Wasm.Value) :
      ({ afterThird with values } : Wasm.Locals).get 2 =
        some (.i32 (ResidentPrimitives.scale8Word index)) := by
    simpa using thirdUpdate.1
  unfold heapLimbProgram
  rw [List.append_assoc]
  apply ResidentPrimitives.wp_scale8Program indexLocal firstSet secondSet
    thirdSet
  simp only [List.cons_append, List.nil_append, Wasm.wp_localGet_cons,
    valueThird, Wasm.wp_const_cons, Wasm.wp_add_cons, scaledThird,
    Wasm.wp_load32_cons]
  split
  · rename_i outOfBounds
    exact (readInBounds outOfBounds).elim
  · simp only [readEq, Wasm.wp_ret_cons]
    simpa using returned

/-- The low-bit dispatcher selects the arbitrary-index heap accessor without
changing the store, caller tail, or loaded word. -/
theorem wp_naturalLimbProgram_heap
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {initial afterFirst afterSecond afterThird : Wasm.Locals}
    {part : NaturalLimbPart} {word index result : UInt32}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    (notImmediate : 1 &&& word = 0)
    (valueLocal : initial.get 0 = some (.i32 word))
    (indexLocal : initial.get 1 = some (.i32 index))
    (firstSet :
      ({ initial with values := .i32 (index + index) :: tail }).set? 2
        (.i32 (index + index)) = some afterFirst)
    (secondSet :
      ({ afterFirst with values :=
          (.i32 (index + index + (index + index)) :: tail) }).set? 2
        (.i32 (index + index + (index + index))) = some afterSecond)
    (thirdSet :
      ({ afterSecond with values :=
          (.i32 (ResidentPrimitives.scale8Word index) :: tail) }).set? 2
        (.i32 (ResidentPrimitives.scale8Word index)) = some afterThird)
    (readInBounds :
      ¬((ResidentPrimitives.scale8Word index +
          (UInt32.ofNat headerBytes + word)).toNat +
        (byteOffset part).toNat + 4 > store.mem.pages * 65536))
    (readEq :
      store.mem.read32
        (ResidentPrimitives.scale8Word index +
          (UInt32.ofNat headerBytes + word) + byteOffset part) = result)
    (returned : Q (.Return store (.i32 result :: tail))) :
    Wasm.wp module (naturalLimbProgram part ++ rest) Q store
      { initial with values := tail } env := by
  have valueLocal' :
      ({ initial with values := tail } : Wasm.Locals).get 0 =
        some (.i32 word) := by simpa using valueLocal
  unfold naturalLimbProgram
  simp only [List.cons_append, List.nil_append, Wasm.wp_localGet_cons,
    valueLocal', Wasm.wp_const_cons, Wasm.wp_and_cons, notImmediate]
  apply Wasm.wp_iff_cons rfl
  exact wp_heapLimbProgram valueLocal indexLocal firstSet secondSet thirdSet
    readInBounds readEq returned

/-- An adapted and installed public low/high accessor is a fuel-free call at
any in-bounds limb index.  It returns the exact selected memory word above the
caller's operand tail and leaves the complete store unchanged. -/
theorem terminatesWith_naturalLimb_of_adapted
    {host : Type} {sourceModule : Fir.Wasm.Module}
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {targetFunction : Wasm.Function} {functionIndex : Nat}
    {part : NaturalLimbPart} {store : Wasm.Store host}
    {word index result : UInt32} {tail : List Wasm.Value}
    (adapted : FirTalos.function sourceModule (sourceFunction part) =
      .ok targetFunction)
    (notImport : module.imports[functionIndex]? = none)
    (found : module.funcs[functionIndex - module.imports.length]? =
      some targetFunction)
    (notImmediate : 1 &&& word = 0)
    (readInBounds :
      ¬((ResidentPrimitives.scale8Word index +
          (UInt32.ofNat headerBytes + word)).toNat +
        (byteOffset part).toNat + 4 > store.mem.pages * 65536))
    (readEq :
      store.mem.read32
        (ResidentPrimitives.scale8Word index +
          (UInt32.ofNat headerBytes + word) + byteOffset part) = result) :
    Wasm.TerminatesWith env module functionIndex store
      ([.i32 index, .i32 word] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 result :: tail) := by
  have signature :=
    FirTalos.Correctness.function_preserves_signature adapted
  rcases signature with ⟨paramsEq, localsEq, resultsEq⟩
  have body := adaptedSourceFunction_body adapted
  apply FirTalos.Correctness.terminatesWith_of_wp_body_at notImport found
  rw [body]
  let arguments := [.i32 index, .i32 word] ++ tail
  let entry := targetFunction.toLocals
    (arguments.take targetFunction.numParams).reverse
  have valueLocal : entry.get 0 = some (.i32 word) := by
    simp [entry, arguments, Wasm.Function.toLocals,
      Wasm.Function.numParams, paramsEq, sourceFunction_params]
  have indexLocal : entry.get 1 = some (.i32 index) := by
    simp [entry, arguments, Wasm.Function.toLocals,
      Wasm.Function.numParams, paramsEq, sourceFunction_params]
  have targetLocalsLength : targetFunction.locals.length = 1 := by
    simp [localsEq, sourceFunction_locals]
  have firstValid :
      ({ entry with values := [.i32 (index + index)] }).validIndex 2 := by
    simp [entry, arguments, Wasm.Function.toLocals, Wasm.Function.numParams,
      paramsEq, sourceFunction_params, targetLocalsLength]
  obtain ⟨afterFirst, firstSet⟩ :=
    FirTalos.Correctness.locals_set?_exists
      (value := .i32 (index + index)) firstValid
  have firstLengths :=
    FirTalos.Correctness.locals_lengths_of_set? firstSet
  have secondValid :
      ({ afterFirst with values :=
          [.i32 (index + index + (index + index))] }).validIndex 2 := by
    simp [firstLengths.1, firstLengths.2, entry, arguments,
      Wasm.Function.toLocals, Wasm.Function.numParams, paramsEq,
      sourceFunction_params, targetLocalsLength]
  obtain ⟨afterSecond, secondSet⟩ :=
    FirTalos.Correctness.locals_set?_exists
      (value := .i32 (index + index + (index + index))) secondValid
  have secondLengths :=
    FirTalos.Correctness.locals_lengths_of_set? secondSet
  have thirdValid :
      ({ afterSecond with values :=
          [.i32 (ResidentPrimitives.scale8Word index)] }).validIndex 2 := by
    simp [secondLengths.1, secondLengths.2, firstLengths.1, firstLengths.2,
      entry, arguments, Wasm.Function.toLocals, Wasm.Function.numParams,
      paramsEq, sourceFunction_params, targetLocalsLength]
  obtain ⟨afterThird, thirdSet⟩ :=
    FirTalos.Correctness.locals_set?_exists
      (value := .i32 (ResidentPrimitives.scale8Word index)) thirdValid
  have returned :
      FirTalos.Correctness.FunctionBodyPost targetFunction arguments
        (fun final values =>
          final = store ∧ values = .i32 result :: tail)
        (.Return store [.i32 result]) := by
    simp [FirTalos.Correctness.FunctionBodyPost, arguments,
      Wasm.Function.numParams, paramsEq, resultsEq, sourceFunction_params,
      sourceFunction_results]
  simpa [entry, arguments, Wasm.Function.toLocals] using
    (wp_naturalLimbProgram_heap
      (module := module) (env := env) (store := store) (initial := entry)
      (rest := FirTalos.functionTerminal sourceModule (sourceFunction part))
      (tail := []) notImmediate valueLocal indexLocal firstSet secondSet
      thirdSet readInBounds readEq returned)

/-- The modular machine base used by a limb accessor is the wasm32 encoding
of the ordinary object-base-plus-eight-times-index coordinate. -/
theorem limbBaseAddress_eq_ofNat (address : Word32) (index : UInt32) :
    ResidentPrimitives.scale8Word index +
        (UInt32.ofNat headerBytes + UInt32.ofNat address.value) =
      UInt32.ofNat
        (address.value + headerBytes + 8 * index.toNat) := by
  rw [ResidentPrimitives.scale8Word_eq_mul8]
  have indexRoundtrip : UInt32.ofNat index.toNat = index := by
    apply UInt32.toNat.inj
    simp
  nth_rewrite 1 [← indexRoundtrip]
  simp only [UInt32.ofNat_add, UInt32.ofNat_mul]
  ac_rfl

/-- At limb index zero, the heap arm performs the shared scale-by-eight
sequence and returns exactly the selected 32-bit half-limb.  The local-update
premises expose only Talos's checked local setter; callers need not depend on
its list representation. -/
theorem wp_heapLimbProgram_zero
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {initial afterFirst afterSecond afterThird : Wasm.Locals}
    {part : NaturalLimbPart} {word result : UInt32}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    (valueLocal : initial.get 0 = some (.i32 word))
    (indexLocal : initial.get 1 = some (.i32 0))
    (firstSet :
      ({ initial with values := .i32 0 :: tail }).set? 2 (.i32 0) =
        some afterFirst)
    (secondSet :
      ({ afterFirst with values := .i32 0 :: tail }).set? 2 (.i32 0) =
        some afterSecond)
    (thirdSet :
      ({ afterSecond with values := .i32 0 :: tail }).set? 2 (.i32 0) =
        some afterThird)
    (readInBounds :
      ¬((UInt32.ofNat headerBytes + word).toNat +
        (byteOffset part).toNat + 4 > store.mem.pages * 65536))
    (readEq :
      store.mem.read32
        (UInt32.ofNat headerBytes + word + byteOffset part) = result)
    (returned : Q (.Return store (.i32 result :: tail))) :
    Wasm.wp module (heapLimbProgram part ++ rest) Q store
      { initial with values := tail } env := by
  have firstUpdate := FirTalos.Correctness.localUpdate_of_set? firstSet
  have secondUpdate := FirTalos.Correctness.localUpdate_of_set? secondSet
  have thirdUpdate := FirTalos.Correctness.localUpdate_of_set? thirdSet
  have indexInitial (values : List Wasm.Value) :
      ({ initial with values } : Wasm.Locals).get 1 = some (.i32 0) := by
    simpa using indexLocal
  have scaledFirst (values : List Wasm.Value) :
      ({ afterFirst with values } : Wasm.Locals).get 2 = some (.i32 0) := by
    simpa using firstUpdate.1
  have scaledSecond (values : List Wasm.Value) :
      ({ afterSecond with values } : Wasm.Locals).get 2 = some (.i32 0) := by
    simpa using secondUpdate.1
  have valueAfterFirst : afterFirst.get 0 = some (.i32 word) := by
    rw [firstUpdate.2 (show 0 ≠ 2 by decide)]
    simpa using valueLocal
  have valueAfterSecond : afterSecond.get 0 = some (.i32 word) := by
    rw [secondUpdate.2 (show 0 ≠ 2 by decide)]
    simpa using valueAfterFirst
  have valueThird (values : List Wasm.Value) :
      ({ afterThird with values } : Wasm.Locals).get 0 =
        some (.i32 word) := by
    rw [show ({ afterThird with values } : Wasm.Locals).get 0 =
      afterThird.get 0 by rfl, thirdUpdate.2 (show 0 ≠ 2 by decide)]
    simpa using valueAfterSecond
  have scaledThird (values : List Wasm.Value) :
      ({ afterThird with values } : Wasm.Locals).get 2 = some (.i32 0) := by
    simpa using thirdUpdate.1
  have zeroAdd : (0 + 0 : UInt32) = 0 := by decide
  have readInBounds' :
      ¬(store.mem.pages * 65536 <
        (headerBytes + word.toNat) % 4294967296 +
          (byteOffset part).toNat + 4) := by
    simpa [UInt32.toNat_add] using readInBounds
  unfold heapLimbProgram ResidentPrimitives.scale8Program
  simp only [List.cons_append, List.nil_append, Wasm.wp_localGet_cons,
    indexInitial, Wasm.wp_add_cons]
  rw [zeroAdd]
  simp only [Wasm.wp_localSet_cons, firstSet]
  simp only [Wasm.wp_localGet_cons, scaledFirst, Wasm.wp_add_cons]
  rw [zeroAdd]
  simp only [Wasm.wp_localSet_cons, secondSet]
  simp only [Wasm.wp_localGet_cons, scaledSecond, Wasm.wp_add_cons]
  rw [zeroAdd]
  simp only [Wasm.wp_localSet_cons, thirdSet]
  simp only [Wasm.wp_localGet_cons, valueThird, Wasm.wp_const_cons,
    scaledThird, Wasm.wp_add_cons, Wasm.wp_load32_cons]
  rw [UInt32.zero_add]
  split
  · rename_i outOfBounds
    exact (readInBounds' outOfBounds).elim
  · simp only [readEq, Wasm.wp_ret_cons]
    simpa using returned

/-- The low-bit dispatcher selects the heap accessor without changing the
store, caller tail, or the exact loaded word. -/
theorem wp_naturalLimbProgram_heap_zero
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {initial afterFirst afterSecond afterThird : Wasm.Locals}
    {part : NaturalLimbPart} {word result : UInt32}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    (notImmediate : 1 &&& word = 0)
    (valueLocal : initial.get 0 = some (.i32 word))
    (indexLocal : initial.get 1 = some (.i32 0))
    (firstSet :
      ({ initial with values := .i32 0 :: tail }).set? 2 (.i32 0) =
        some afterFirst)
    (secondSet :
      ({ afterFirst with values := .i32 0 :: tail }).set? 2 (.i32 0) =
        some afterSecond)
    (thirdSet :
      ({ afterSecond with values := .i32 0 :: tail }).set? 2 (.i32 0) =
        some afterThird)
    (readInBounds :
      ¬((UInt32.ofNat headerBytes + word).toNat +
        (byteOffset part).toNat + 4 > store.mem.pages * 65536))
    (readEq :
      store.mem.read32
        (UInt32.ofNat headerBytes + word + byteOffset part) = result)
    (returned : Q (.Return store (.i32 result :: tail))) :
    Wasm.wp module (naturalLimbProgram part ++ rest) Q store
      { initial with values := tail } env := by
  have valueLocal' :
      ({ initial with values := tail } : Wasm.Locals).get 0 =
        some (.i32 word) := by simpa using valueLocal
  unfold naturalLimbProgram
  simp only [List.cons_append, List.nil_append, Wasm.wp_localGet_cons,
    valueLocal', Wasm.wp_const_cons, Wasm.wp_and_cons, notImmediate]
  apply Wasm.wp_iff_cons rfl
  exact wp_heapLimbProgram_zero valueLocal indexLocal firstSet secondSet
    thirdSet readInBounds readEq returned

/-- An adapted and installed public low/high accessor is a fuel-free call at
limb index zero.  The exact selected memory word is returned above the caller
tail, and the complete store is unchanged. -/
theorem terminatesWith_naturalLimbZero_of_adapted
    {host : Type} {sourceModule : Fir.Wasm.Module}
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {targetFunction : Wasm.Function} {functionIndex : Nat}
    {part : NaturalLimbPart} {store : Wasm.Store host}
    {word result : UInt32} {tail : List Wasm.Value}
    (adapted : FirTalos.function sourceModule (sourceFunction part) =
      .ok targetFunction)
    (notImport : module.imports[functionIndex]? = none)
    (found : module.funcs[functionIndex - module.imports.length]? =
      some targetFunction)
    (notImmediate : 1 &&& word = 0)
    (readInBounds :
      ¬((UInt32.ofNat headerBytes + word).toNat +
        (byteOffset part).toNat + 4 > store.mem.pages * 65536))
    (readEq :
      store.mem.read32
        (UInt32.ofNat headerBytes + word + byteOffset part) = result) :
    Wasm.TerminatesWith env module functionIndex store
      ([.i32 0, .i32 word] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 result :: tail) := by
  have signature :=
    FirTalos.Correctness.function_preserves_signature adapted
  rcases signature with ⟨paramsEq, localsEq, resultsEq⟩
  have body := adaptedSourceFunction_body adapted
  apply FirTalos.Correctness.terminatesWith_of_wp_body_at notImport found
  rw [body]
  let arguments := [.i32 0, .i32 word] ++ tail
  let entry := targetFunction.toLocals
    (arguments.take targetFunction.numParams).reverse
  have valueLocal : entry.get 0 = some (.i32 word) := by
    simp [entry, arguments, Wasm.Function.toLocals,
      Wasm.Function.numParams, paramsEq, sourceFunction_params]
  have indexLocal : entry.get 1 = some (.i32 0) := by
    simp [entry, arguments, Wasm.Function.toLocals,
      Wasm.Function.numParams, paramsEq, sourceFunction_params]
  have targetLocalsLength : targetFunction.locals.length = 1 := by
    simp [localsEq, sourceFunction_locals]
  have firstValid :
      ({ entry with values := [.i32 0] }).validIndex 2 := by
    simp [entry, arguments, Wasm.Function.toLocals, Wasm.Function.numParams,
      paramsEq, sourceFunction_params, targetLocalsLength]
  obtain ⟨afterFirst, firstSet⟩ :=
    FirTalos.Correctness.locals_set?_exists (value := .i32 0) firstValid
  have firstLengths :=
    FirTalos.Correctness.locals_lengths_of_set? firstSet
  have secondValid :
      ({ afterFirst with values := [.i32 0] }).validIndex 2 := by
    simp [firstLengths.1, firstLengths.2, entry, arguments,
      Wasm.Function.toLocals, Wasm.Function.numParams, paramsEq,
      sourceFunction_params, targetLocalsLength]
  obtain ⟨afterSecond, secondSet⟩ :=
    FirTalos.Correctness.locals_set?_exists (value := .i32 0) secondValid
  have secondLengths :=
    FirTalos.Correctness.locals_lengths_of_set? secondSet
  have thirdValid :
      ({ afterSecond with values := [.i32 0] }).validIndex 2 := by
    simp [secondLengths.1, secondLengths.2, firstLengths.1, firstLengths.2,
      entry, arguments, Wasm.Function.toLocals, Wasm.Function.numParams,
      paramsEq, sourceFunction_params, targetLocalsLength]
  obtain ⟨afterThird, thirdSet⟩ :=
    FirTalos.Correctness.locals_set?_exists (value := .i32 0) thirdValid
  have returned :
      FirTalos.Correctness.FunctionBodyPost targetFunction arguments
        (fun final values =>
          final = store ∧ values = .i32 result :: tail)
        (.Return store [.i32 result]) := by
    simp [FirTalos.Correctness.FunctionBodyPost, arguments,
      Wasm.Function.numParams, paramsEq, resultsEq, sourceFunction_params,
      sourceFunction_results]
  simpa [entry, arguments, Wasm.Function.toLocals] using
    (wp_naturalLimbProgram_heap_zero
      (module := module) (env := env) (store := store) (initial := entry)
      (rest := FirTalos.functionTerminal sourceModule (sourceFunction part))
      (tail := []) notImmediate valueLocal indexLocal firstSet secondSet
      thirdSet readInBounds readEq returned)

/-- A checked read in W6's finite linear memory supplies every machine fact
needed by an installed arbitrary-index accessor.  The single payload bound
both proves the W6 read is defined and removes all wasm32 address wrapping. -/
theorem terminatesWith_naturalLimb_of_concreteRead
    {host : Type} {sourceModule : Fir.Wasm.Module}
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {targetFunction : Wasm.Function} {functionIndex : Nat}
    {part : NaturalLimbPart} {heap : MemoryState} {store : Wasm.Store host}
    {address : Word32} {index result : UInt32} {tail : List Wasm.Value}
    (adapted : FirTalos.function sourceModule (sourceFunction part) =
      .ok targetFunction)
    (notImport : module.imports[functionIndex]? = none)
    (found : module.funcs[functionIndex - module.imports.length]? =
      some targetFunction)
    (memoryRelated : ResidentMemoryRel heap store.mem)
    (addressHeap : address.classify = .heap)
    (payloadInBounds :
      address.value + headerBytes + 8 * index.toNat +
          (byteOffset part).toNat + 4 ≤ heap.memory.size)
    (concreteRead :
      heap.memory.readUInt32
        (address.value + headerBytes + 8 * index.toNat +
          (byteOffset part).toNat) = .ok result) :
    Wasm.TerminatesWith env module functionIndex store
      ([.i32 index, .i32 (UInt32.ofNat address.value)] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 result :: tail) := by
  let baseAddress := address.value + headerBytes + 8 * index.toNat
  have baseLt : baseAddress < UInt32.size := by
    have sizeLe := memoryRelated.size_le
    dsimp [baseAddress]
    omega
  have baseWord :
      ResidentPrimitives.scale8Word index +
          (UInt32.ofNat headerBytes + UInt32.ofNat address.value) =
        UInt32.ofNat baseAddress := by
    simpa [baseAddress] using limbBaseAddress_eq_ofNat address index
  have baseToNat :
      (ResidentPrimitives.scale8Word index +
        (UInt32.ofNat headerBytes + UInt32.ofNat address.value)).toNat =
          baseAddress := by
    rw [baseWord]
    exact UInt32.toNat_ofNat_of_lt' baseLt
  have selected : 1 &&& UInt32.ofNat address.value = 0 :=
    heapWord_selected address addressHeap
  have memorySize :
      heap.memory.size = store.mem.pages * 65536 := by
    simpa [wasmPageBytes] using memoryRelated.size_eq
  have targetInBounds :
      ¬((ResidentPrimitives.scale8Word index +
          (UInt32.ofNat headerBytes + UInt32.ofNat address.value)).toNat +
        (byteOffset part).toNat + 4 > store.mem.pages * 65536) := by
    rw [baseToNat, ← memorySize]
    dsimp [baseAddress]
    omega
  let concreteAddress := baseAddress + (byteOffset part).toNat
  have concreteAddressInBounds : concreteAddress + 3 < heap.memory.size := by
    dsimp [concreteAddress, baseAddress]
    omega
  have transported :=
    memoryRelated.readUInt32_eq_read32 concreteAddressInBounds
  have targetAddress :
      UInt32.ofNat concreteAddress =
        ResidentPrimitives.scale8Word index +
          (UInt32.ofNat headerBytes + UInt32.ofNat address.value) +
            byteOffset part := by
    dsimp [concreteAddress]
    rw [UInt32.ofNat_add, ← baseWord]
    simp
  have targetRead :
      store.mem.read32
        (ResidentPrimitives.scale8Word index +
          (UInt32.ofNat headerBytes + UInt32.ofNat address.value) +
            byteOffset part) = result := by
    rw [← targetAddress]
    rw [concreteRead] at transported
    simpa [concreteAddress, baseAddress] using transported.symm
  exact terminatesWith_naturalLimb_of_adapted adapted notImport found
    selected targetInBounds targetRead

/-- Compatibility specialization of the concrete accessor boundary at index
zero, retained for the USize conversion proof. -/
theorem terminatesWith_naturalLimbZero_of_concreteRead
    {host : Type} {sourceModule : Fir.Wasm.Module}
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {targetFunction : Wasm.Function} {functionIndex : Nat}
    {part : NaturalLimbPart} {heap : MemoryState} {store : Wasm.Store host}
    {address : Word32} {result : UInt32} {tail : List Wasm.Value}
    (adapted : FirTalos.function sourceModule (sourceFunction part) =
      .ok targetFunction)
    (notImport : module.imports[functionIndex]? = none)
    (found : module.funcs[functionIndex - module.imports.length]? =
      some targetFunction)
    (memoryRelated : ResidentMemoryRel heap store.mem)
    (addressHeap : address.classify = .heap)
    (payloadInBounds :
      address.value + headerBytes + (byteOffset part).toNat + 4 ≤
        heap.memory.size)
    (concreteRead :
      heap.memory.readUInt32
        (address.value + headerBytes + (byteOffset part).toNat) =
          .ok result) :
    Wasm.TerminatesWith env module functionIndex store
      ([.i32 0, .i32 (UInt32.ofNat address.value)] ++ tail)
      (fun final values =>
        final = store ∧ values = .i32 result :: tail) := by
  have addressLt : address.value < UInt32.size := by
    simpa [wordModulus] using address.isLt
  have baseLt : headerBytes + address.value < UInt32.size := by
    have sizeLe := memoryRelated.size_le
    omega
  have baseToNat :
      (UInt32.ofNat headerBytes + UInt32.ofNat address.value).toNat =
        headerBytes + address.value := by
    rw [UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat_of_lt'
      (show headerBytes < UInt32.size by decide),
      UInt32.toNat_ofNat_of_lt' addressLt]
    rw [Nat.mod_eq_of_lt baseLt]
  have selected : 1 &&& UInt32.ofNat address.value = 0 :=
    heapWord_selected address addressHeap
  have memorySize :
      heap.memory.size = store.mem.pages * 65536 := by
    simpa [wasmPageBytes] using memoryRelated.size_eq
  have targetInBounds :
      ¬((UInt32.ofNat headerBytes + UInt32.ofNat address.value).toNat +
        (byteOffset part).toNat + 4 > store.mem.pages * 65536) := by
    rw [baseToNat, ← memorySize]
    omega
  let concreteAddress :=
    address.value + headerBytes + (byteOffset part).toNat
  have concreteAddressInBounds : concreteAddress + 3 < heap.memory.size := by
    dsimp [concreteAddress]
    omega
  have transported :=
    memoryRelated.readUInt32_eq_read32 concreteAddressInBounds
  have targetAddress :
      UInt32.ofNat concreteAddress =
        UInt32.ofNat headerBytes + UInt32.ofNat address.value +
          byteOffset part := by
    dsimp [concreteAddress]
    rw [UInt32.ofNat_add, UInt32.ofNat_add]
    rw [UInt32.add_comm (UInt32.ofNat address.value)
      (UInt32.ofNat headerBytes)]
    simp
  have targetRead :
      store.mem.read32
        (UInt32.ofNat headerBytes + UInt32.ofNat address.value +
          byteOffset part) = result := by
    rw [← targetAddress]
    rw [concreteRead] at transported
    simpa using transported.symm
  exact terminatesWith_naturalLimbZero_of_adapted adapted notImport found
    selected targetInBounds targetRead

/-- Installed common/low/high helpers realize the abstract call boundary used
by the complete Natural validator for every canonical W6 admission.  The
existential words are the exact two halves of the canonical top limb. -/
theorem naturalValidationCalls_of_naturalAdmission
    {host : Type} {sourceModule : Fir.Wasm.Module}
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {validateCommonTarget naturalLowTarget naturalHighTarget : Wasm.Function}
    {validateCommonIndex naturalLowIndex naturalHighIndex : Nat}
    {heap : MemoryState} {store : Wasm.Store host}
    {address : Word32} {value : Nat} {header : Header}
    (validateCommonAdapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.validateCommonFunction =
        .ok validateCommonTarget)
    (validateCommonNotImport :
      module.imports[validateCommonIndex]? = none)
    (validateCommonInstalled :
      module.funcs[validateCommonIndex - module.imports.length]? =
        some validateCommonTarget)
    (naturalLowAdapted : FirTalos.function sourceModule
      (sourceFunction .low) = .ok naturalLowTarget)
    (naturalLowNotImport : module.imports[naturalLowIndex]? = none)
    (naturalLowInstalled :
      module.funcs[naturalLowIndex - module.imports.length]? =
        some naturalLowTarget)
    (naturalHighAdapted : FirTalos.function sourceModule
      (sourceFunction .high) = .ok naturalHighTarget)
    (naturalHighNotImport : module.imports[naturalHighIndex]? = none)
    (naturalHighInstalled :
      module.funcs[naturalHighIndex - module.imports.length]? =
        some naturalHighTarget)
    (memoryRelated : ResidentMemoryRel heap store.mem)
    (related : NaturalValidatorAdmission heap address value header) :
    ∃ low high : UInt32,
      NaturalValidationCalls env module validateCommonIndex naturalLowIndex
          naturalHighIndex store (UInt32.ofNat address.value) header.aux1
            (header.aux1 - 1) low high ∧
      ¬(low = 0 ∧ high = 0) ∧
      (header.aux1 = 1 → ¬high < 2147483648) := by
  obtain ⟨addressHeap, _, _, _, _, objectInBounds⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts heap address header
      related.headerRead
  have countPositive : 0 < header.aux1.toNat := by
    rw [related.limbCount]
    cases limbs : naturalLimbs value with
    | nil => exact (naturalLimbs_ne_nil value limbs).elim
    | cons limb rest => simp
  have oneLe : (1 : UInt32) ≤ header.aux1 := by
    rw [UInt32.le_iff_toNat_le]
    simp only [UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega
  have topIndexToNat : (header.aux1 - 1).toNat =
      header.aux1.toNat - 1 := by
    rw [UInt32.toNat_sub_of_le header.aux1 1 oneLe]
    rfl
  have payloadExtent := objectInBounds
  rw [related.allocationBytes] at payloadExtent
  simp [target] at payloadExtent
  have limbLengthPositive : 0 < (naturalLimbs value).length := by
    rw [← related.limbCount]
    exact countPositive
  obtain ⟨low, high, lowRead, highRead, topNonzero, oneHigh⟩ :=
    FirTalos.Concrete.ResidentBigNumeric.NaturalValidatorAdmission.topWords
      related
  have lowInBounds :
      address.value + headerBytes + 8 * (header.aux1 - 1).toNat +
          (byteOffset .low).toNat + 4 ≤ heap.memory.size := by
    rw [topIndexToNat]
    rw [related.limbCount]
    simp only [byteOffset, UInt32.toNat_zero, Nat.add_zero]
    omega
  have highInBounds :
      address.value + headerBytes + 8 * (header.aux1 - 1).toNat +
          (byteOffset .high).toNat + 4 ≤ heap.memory.size := by
    rw [topIndexToNat]
    rw [related.limbCount]
    simp only [byteOffset, UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega
  have lowRead' :
      heap.memory.readUInt32
        (address.value + headerBytes + 8 * (header.aux1 - 1).toNat +
          (byteOffset .low).toNat) = .ok low := by
    simpa [topIndexToNat, byteOffset] using lowRead
  have highRead' :
      heap.memory.readUInt32
        (address.value + headerBytes + 8 * (header.aux1 - 1).toNat +
          (byteOffset .high).toNat) = .ok high := by
    simpa [topIndexToNat, byteOffset] using highRead
  refine ⟨low, high, { common := ?_, low := ?_, high := ?_ },
    topNonzero, ?_⟩
  · intro tail
    exact terminatesWith_validateCommon_of_naturalAdmission
      validateCommonAdapted validateCommonNotImport validateCommonInstalled
      memoryRelated related
  · intro tail
    exact terminatesWith_naturalLimb_of_concreteRead
      (part := .low) (index := header.aux1 - 1) naturalLowAdapted
      naturalLowNotImport naturalLowInstalled memoryRelated addressHeap
      lowInBounds lowRead'
  · intro tail
    exact terminatesWith_naturalLimb_of_concreteRead
      (part := .high) (index := header.aux1 - 1) naturalHighAdapted
      naturalHighNotImport naturalHighInstalled memoryRelated addressHeap
      highInBounds highRead'
  · intro one
    apply oneHigh
    have := congrArg UInt32.toNat one
    simpa using this

/-- The installed generated Natural validator accepts every canonical W6
heap-Natural admission.  It is trace-free, preserves the complete Wasm store,
and leaves the caller operand tail unchanged.  All header loads, top-limb
accesses, ownership cases, and helper calls are discharged internally. -/
theorem terminatesWith_validateNatural_of_naturalAdmission
    {host : Type} {sourceModule : Fir.Wasm.Module}
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {validateNaturalTarget validateCommonTarget naturalLowTarget
      naturalHighTarget : Wasm.Function}
    {validateNaturalIndex validateCommonIndex naturalLowIndex
      naturalHighIndex : Nat}
    {heap : MemoryState} {store : Wasm.Store host}
    {address : Word32} {value : Nat} {header : Header}
    {tail : List Wasm.Value}
    (validateNaturalAdapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.validateNaturalFunction =
        .ok validateNaturalTarget)
    (validateCommonFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.validateCommonName) =
        some validateCommonIndex)
    (naturalLowFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.naturalLowName) =
        some naturalLowIndex)
    (naturalHighFound : FirTalos.callIndex? sourceModule
      (.declaration Fir.Wasm.Emit.ResidentBigNumeric.naturalHighName) =
        some naturalHighIndex)
    (validateNaturalNotImport :
      module.imports[validateNaturalIndex]? = none)
    (validateNaturalInstalled :
      module.funcs[validateNaturalIndex - module.imports.length]? =
        some validateNaturalTarget)
    (validateCommonAdapted : FirTalos.function sourceModule
      Fir.Wasm.Emit.ResidentBigNumeric.validateCommonFunction =
        .ok validateCommonTarget)
    (validateCommonNotImport :
      module.imports[validateCommonIndex]? = none)
    (validateCommonInstalled :
      module.funcs[validateCommonIndex - module.imports.length]? =
        some validateCommonTarget)
    (naturalLowAdapted : FirTalos.function sourceModule
      (sourceFunction .low) = .ok naturalLowTarget)
    (naturalLowNotImport : module.imports[naturalLowIndex]? = none)
    (naturalLowInstalled :
      module.funcs[naturalLowIndex - module.imports.length]? =
        some naturalLowTarget)
    (naturalHighAdapted : FirTalos.function sourceModule
      (sourceFunction .high) = .ok naturalHighTarget)
    (naturalHighNotImport : module.imports[naturalHighIndex]? = none)
    (naturalHighInstalled :
      module.funcs[naturalHighIndex - module.imports.length]? =
        some naturalHighTarget)
    (memoryRelated : ResidentMemoryRel heap store.mem)
    (related : NaturalValidatorAdmission heap address value header) :
    Wasm.TerminatesWith env module validateNaturalIndex store
      ([.i32 (UInt32.ofNat address.value)] ++ tail)
      (fun final values => final = store ∧ values = tail) := by
  have signature :=
    FirTalos.Correctness.function_preserves_signature validateNaturalAdapted
  rcases signature with ⟨paramsEq, localsEq, resultsEq⟩
  have body := adaptedValidateNaturalFunction_body validateNaturalAdapted
    validateCommonFound naturalLowFound naturalHighFound
  apply FirTalos.Correctness.terminatesWith_of_wp_body_at
    validateNaturalNotImport validateNaturalInstalled
  rw [body]
  let word := UInt32.ofNat address.value
  let arguments := [.i32 word] ++ tail
  let entry := validateNaturalTarget.toLocals
    (arguments.take validateNaturalTarget.numParams).reverse
  have valueLocal : entry.get 0 = some (.i32 word) := by
    simp [entry, arguments, Wasm.Function.toLocals,
      Wasm.Function.numParams, paramsEq, validateNaturalFunction_params]
  have targetLocalsLength : validateNaturalTarget.locals.length = 1 := by
    simp [localsEq, validateNaturalFunction_locals]
  have countValid :
      ({ entry with values := [.i32 header.aux1] }).validIndex 1 := by
    simp [entry, arguments, Wasm.Function.toLocals,
      Wasm.Function.numParams, paramsEq, validateNaturalFunction_params,
      targetLocalsLength]
  obtain ⟨afterCount, countSet⟩ :=
    FirTalos.Correctness.locals_set?_exists
      (value := .i32 header.aux1) countValid
  have returned :
      FirTalos.Correctness.FunctionBodyPost validateNaturalTarget arguments
        (fun final values => final = store ∧ values = tail)
        (.Return store []) := by
    simp [FirTalos.Correctness.FunctionBodyPost, arguments,
      Wasm.Function.numParams, paramsEq, resultsEq,
      validateNaturalFunction_params, validateNaturalFunction_results]
  obtain ⟨addressHeap, _, headerLive, headerMinimum, _, objectInBounds⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts heap address header
      related.headerRead
  have headerInBounds :
      address.value + headerBytes ≤ heap.memory.size := by
    omega
  obtain ⟨kindInBounds, kindRead⟩ := residentHeaderUInt32 memoryRelated
    headerInBounds (by decide) related.rawHeader.readKind
  obtain ⟨flagsInBounds, flagsRead⟩ := residentHeaderUInt32
    memoryRelated headerInBounds (by decide) related.rawHeader.readFlags
  obtain ⟨refCountInBounds, refCountRead⟩ := residentHeaderUInt32
    memoryRelated headerInBounds (by decide) related.rawHeader.readRefCount
  obtain ⟨aux0InBounds, aux0Read⟩ := residentHeaderUInt32 memoryRelated
    headerInBounds (by decide) related.rawHeader.readAux0
  obtain ⟨aux2InBounds, aux2Read⟩ := residentHeaderUInt32 memoryRelated
    headerInBounds (by decide) related.rawHeader.readAux2
  obtain ⟨aux3InBounds, aux3Read⟩ := residentHeaderUInt32 memoryRelated
    headerInBounds (by decide) related.rawHeader.readAux3
  obtain ⟨low, high, calls, topNonzero, oneHigh⟩ :=
    naturalValidationCalls_of_naturalAdmission validateCommonAdapted
      validateCommonNotImport validateCommonInstalled naturalLowAdapted
      naturalLowNotImport naturalLowInstalled naturalHighAdapted
      naturalHighNotImport naturalHighInstalled memoryRelated related
  have selected : 1 &&& word = 0 := by
    simpa [word] using heapWord_selected address addressHeap
  have kindExact : header.kind.code = ObjectKind.natural.code := by
    rw [related.headerKind]
  have ownership :
      (header.flags = liveFlag + persistentFlag ∧ header.refCount = 0) ∨
      (header.flags = liveFlag ∧ header.refCount ≠ 0) := by
    cases persistent : header.persistent with
    | false =>
        right
        constructor
        · simp [Header.flags, persistent, headerLive, liveFlag]
        · simpa [persistent] using related.ownership
    | true =>
        left
        constructor
        · simp [Header.flags, persistent, headerLive, liveFlag,
            persistentFlag]
        · simpa [persistent] using related.ownership
  simpa [entry, arguments, word, Wasm.Function.toLocals] using
    (wp_validateNaturalProgram_big
      (module := module) (env := env) (store := store) (initial := entry)
      (afterCount := afterCount) (tail := [])
      (rest := FirTalos.functionTerminal sourceModule
        Fir.Wasm.Emit.ResidentBigNumeric.validateNaturalFunction)
      calls valueLocal countSet selected rfl kindInBounds flagsInBounds
      refCountInBounds aux0InBounds aux2InBounds aux3InBounds kindRead
      flagsRead refCountRead aux0Read aux2Read aux3Read kindExact
      related.marker ownership related.reserved2 related.reserved3
      topNonzero oneHigh returned)

/-- The first 64-bit limb of any successful nonempty natural decode supplies
the exact low/high words used by `CheckedNaturalCalls`, independently of the
remaining arbitrary-precision limbs. -/
theorem readNaturalLimbs_firstWords
    {memory : LinearMemory} {base count value : Nat}
    (countPositive : 0 < count)
    (decoded : readNaturalLimbs memory base 0 count = .ok value) :
    ∃ low high : UInt32,
      memory.readUInt32 (base + headerBytes) = .ok low ∧
      memory.readUInt32 (base + headerBytes + 4) = .ok high ∧
      (UInt64.ofNat high.toNat <<< 32) |||
        UInt64.ofNat low.toNat = UInt64.ofNat value := by
  cases count with
  | zero => omega
  | succ count =>
      unfold readNaturalLimbs at decoded
      simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at decoded
      cases limbRead : memory.readUInt64 (base + headerBytes) with
      | error failure =>
          rw [limbRead] at decoded
          contradiction
      | ok limb =>
          rw [limbRead] at decoded
          cases restRead : readNaturalLimbs memory base 1 count with
          | error failure =>
              rw [restRead] at decoded
              contradiction
          | ok rest =>
              rw [restRead] at decoded
              simp only [Bind.bind, Except.bind, pure, Except.pure,
                Except.ok.injEq] at decoded
              unfold LinearMemory.readUInt64 at limbRead
              cases lowRead : memory.readUInt32 (base + headerBytes) with
              | error failure =>
                  rw [lowRead] at limbRead
                  contradiction
              | ok low =>
                  rw [lowRead] at limbRead
                  cases highRead : memory.readUInt32
                      (base + headerBytes + 4) with
                  | error failure =>
                      rw [highRead] at limbRead
                      contradiction
                  | ok high =>
                      rw [highRead] at limbRead
                      simp only [Bind.bind, Except.bind, pure, Except.pure,
                        Except.ok.injEq] at limbRead
                      refine ⟨low, high, ?_, ?_, ?_⟩
                      · rfl
                      · rfl
                      · have assembled :
                            (UInt64.ofNat high.toNat <<< 32) |||
                                UInt64.ofNat low.toNat = limb := by
                          simp only [UInt64.ofNat_uInt32ToNat]
                          rw [← limbRead]
                          exact LinearMemory.assembleUInt64Words low high
                        rw [assembled, ← decoded]
                        simp [UInt64.size]

/-- An ordinary heap-natural relation exposes a nonempty first limb and its
full eight-byte extent.  The only representation fact required beyond the
relation is that the semantic value is genuinely outside the tagged range. -/
theorem NaturalObjectRel.firstWords
    {heap : MemoryState} {address : Word32} {value : Nat} {header : Header}
    (related : NaturalObjectRel heap address value header)
    (large : maxTaggedPayload < value) :
    ∃ low high : UInt32,
      address.value + headerBytes + 8 ≤ heap.memory.size ∧
      heap.memory.readUInt32 (address.value + headerBytes) = .ok low ∧
      heap.memory.readUInt32 (address.value + headerBytes + 4) = .ok high ∧
      (UInt64.ofNat high.toNat <<< 32) |||
        UInt64.ofNat low.toNat = UInt64.ofNat value := by
  obtain ⟨addressHeap, _, _, _, _, extentInMemory⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts heap address header
      related.headerRead
  have accepted :
      header.kind == ObjectKind.natural && header.aux0 == bigNaturalMarker := by
    rw [related.headerKind, related.marker]
    rfl
  have decodedLimbs :
      readNaturalLimbs heap.memory address.value 0 header.aux1.toNat =
        .ok value := by
    have decoded := related.decoded
    unfold readNatural at decoded
    simp only [addressHeap, ↓reduceIte, Bind.bind, Except.bind] at decoded
    rw [related.headerRead] at decoded
    simp only [liftMemory] at decoded
    rw [accepted] at decoded
    simp only [↓reduceIte] at decoded
    cases readResult :
        readNaturalLimbs heap.memory address.value 0 header.aux1.toNat with
    | error failure =>
        rw [readResult] at decoded
        contradiction
    | ok actual =>
        rw [readResult] at decoded
        simp only [Except.ok.injEq] at decoded
        subst actual
        rfl
  have countPositive : 0 < header.aux1.toNat := by
    by_contra notPositive
    have countZero : header.aux1.toNat = 0 := Nat.eq_zero_of_not_pos notPositive
    rw [countZero] at decodedLimbs
    simp only [readNaturalLimbs, Except.ok.injEq] at decodedLimbs
    have valueZero : value = 0 := decodedLimbs.symm
    omega
  obtain ⟨low, high, lowRead, highRead, modulo⟩ :=
    readNaturalLimbs_firstWords countPositive decodedLimbs
  have payloadInBounds :
      address.value + headerBytes + 8 ≤ heap.memory.size := by
    have limbsFit := related.limbsFit
    simp [target] at limbsFit
    omega
  exact ⟨low, high, payloadInBounds, lowRead, highRead, modulo⟩

end ResidentBigNumeric

end FirTalos.Concrete
