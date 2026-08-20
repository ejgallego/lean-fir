import FirTalos.ConcreteResidentUSize

namespace FirTalos.Concrete

open Fir.Wasm.Concrete

/-!
# Resident arbitrary-precision natural accessors

This module connects W7's installed BigNumeric validation/accessor helpers to
the stable `CheckedNaturalCalls` boundary used by the Nat-to-USize proof.  The
first layer factors the common low/high limb implementation and its exact
Talos adaptation before attaching concrete heap facts.
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
def indexParam : Lean.FVarId := ⟨`index⟩
def scaledLocal : Lean.FVarId := ⟨`scaledValue⟩

def scale8Source : List Fir.Wasm.Instruction := [
  .localGet indexParam,
  .localGet indexParam,
  .i32Add,
  .localSet scaledLocal,
  .localGet scaledLocal,
  .localGet scaledLocal,
  .i32Add,
  .localSet scaledLocal,
  .localGet scaledLocal,
  .localGet scaledLocal,
  .i32Add,
  .localSet scaledLocal]

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

def heapLimbProgram (part : NaturalLimbPart) : Wasm.Program := [
  .localGet 1,
  .localGet 1,
  .add,
  .localSet 2,
  .localGet 2,
  .localGet 2,
  .add,
  .localSet 2,
  .localGet 2,
  .localGet 2,
  .add,
  .localSet 2,
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
      immediateLimbProgram, heapLimbProgram, byteOffset, FirTalos.instructions,
      FirTalos.instruction, valueFound, indexFound, scaledFound, Bind.bind,
      Except.bind, pure, Except.pure]

/-- Exact installed target body, including the adapter's terminal suffix. -/
theorem adaptedSourceFunction_body
    {sourceModule : Fir.Wasm.Module} {targetFunction : Wasm.Function}
    {part : NaturalLimbPart}
    (adapted : FirTalos.function sourceModule (sourceFunction part) =
      .ok targetFunction) :
    targetFunction.body = naturalLimbProgram part ++
      FirTalos.functionTerminal sourceModule (sourceFunction part) := by
  exact ResidentNat.adaptedFunction_body_of_exact adapted
    (instructions_sourceFunction part)

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
  unfold heapLimbProgram
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
needed by the installed index-zero accessor.  This is the reusable boundary
between concrete natural-layout proofs and the resident low/high helpers. -/
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
    ResidentUSize.checkedWord_selected address addressHeap
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
                          bv_decide
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
    decide
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

/-- Once validation of the same natural word is available, an ordinary
heap-natural relation constructs the complete `CheckedNaturalCalls` witness.
Thus the remaining validator proof is isolated from limb loading and modulo
recombination. -/
theorem NaturalObjectRel.checkedNaturalCalls_of_validate
    {host : Type} {sourceModule : Fir.Wasm.Module}
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {lowTarget highTarget : Wasm.Function}
    {validateIndex lowIndex highIndex : Nat}
    {heap : MemoryState} {store : Wasm.Store host}
    {address : Word32} {value : Nat} {header : Header}
    (related : NaturalObjectRel heap address value header)
    (large : maxTaggedPayload < value)
    (memoryRelated : ResidentMemoryRel heap store.mem)
    (lowAdapted : FirTalos.function sourceModule (sourceFunction .low) =
      .ok lowTarget)
    (lowNotImport : module.imports[lowIndex]? = none)
    (lowFound : module.funcs[lowIndex - module.imports.length]? =
      some lowTarget)
    (highAdapted : FirTalos.function sourceModule (sourceFunction .high) =
      .ok highTarget)
    (highNotImport : module.imports[highIndex]? = none)
    (highFound : module.funcs[highIndex - module.imports.length]? =
      some highTarget)
    (validateCall : ∀ tail,
      Wasm.TerminatesWith env module validateIndex store
        (.i32 (UInt32.ofNat address.value) :: tail)
        (fun final values => final = store ∧ values = tail)) :
    ∃ high low : UInt32,
      ResidentUSize.CheckedNaturalCalls env module validateIndex highIndex
        lowIndex store (UInt32.ofNat address.value) value high low := by
  obtain ⟨low, high, payloadInBounds, lowRead, highRead, modulo⟩ :=
    FirTalos.Concrete.ResidentBigNumeric.NaturalObjectRel.firstWords
      related large
  have addressHeap :=
    (MemoryState.PrefixExtension.readLiveHeader_facts heap address header
      related.headerRead).1
  refine ⟨high, low, {
    validate := validateCall
    high := ?_
    low := ?_
    modulo := modulo }⟩
  · intro tail
    apply terminatesWith_naturalLimbZero_of_concreteRead highAdapted
      highNotImport highFound memoryRelated addressHeap
    · simpa [byteOffset] using payloadInBounds
    · simpa [byteOffset] using highRead
  · intro tail
    apply terminatesWith_naturalLimbZero_of_concreteRead lowAdapted
      lowNotImport lowFound memoryRelated addressHeap
    · simp [byteOffset]
      omega
    · simpa [byteOffset] using lowRead

end ResidentBigNumeric

end FirTalos.Concrete
