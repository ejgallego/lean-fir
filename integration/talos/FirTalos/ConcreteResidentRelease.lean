import Fir.Wasm.Emit.ResidentRelease
import Fir.Wasm.Concrete.OwnershipFrameCorrectness
import FirTalos.ConcreteResidentAllocator
import FirTalos.ConcreteResidentMemory
import FirTalos.Correctness.Adapter
import FirTalos.Correctness.Function
import Interpreter.Wasm.Wp.Tactic

namespace FirTalos.Concrete

open Fir.Wasm.Concrete

/-!
# Resident release refinement

This module verifies the Wasm-resident ownership-release helpers.  The first
slice isolates their hot shared-reference path: a full-header bounds probe is
followed by a single reference-count store, without interpreting object kind
or auxiliary metadata.
-/

namespace ResidentRelease

/-- Numeric local layout of W7's resident one-step decrement helper. -/
def objectIndex : Nat := 0
def checkIndex : Nat := 1
def addressIndex : Nat := 2
def kindIndex : Nat := 3
def countIndex : Nat := 4
def captureCountIndex : Nat := 5
def descriptorIndex : Nat := 6
def refCountIndex : Nat := 7
def flagsIndex : Nat := 8
def markerIndex : Nat := 9
def arrayCursorIndex : Nat := 10
def arrayIndex : Nat := 11

/-- Concrete frame at the entry of W7's live-object arm.  The preceding
alignment prefix has cached the object address and exact raw flags; every
other helper local still contains its declared zero value. -/
def liveEntry (object check flags : UInt32) : Wasm.Locals := {
  params := [.i32 object, .i32 check]
  locals := [
    .i32 object,
    .i32 0,
    .i32 0,
    .i32 0,
    .i32 0,
    .i32 0,
    .i32 flags,
    .i32 0,
    .i32 0,
    .i32 0]
  values := [] }

/-- Live-arm frame after the terminal header word has been probed. -/
def probedLocals (object check flags descriptor : UInt32) : Wasm.Locals := {
  params := [.i32 object, .i32 check]
  locals := [
    .i32 object,
    .i32 0,
    .i32 0,
    .i32 0,
    .i32 descriptor,
    .i32 0,
    .i32 flags,
    .i32 0,
    .i32 0,
    .i32 0]
  values := [] }

/-- Persistent arm after loading the concrete object-kind lane. -/
def persistentKindLocals
    (object check flags descriptor kind : UInt32) : Wasm.Locals := {
  params := [.i32 object, .i32 check]
  locals := [
    .i32 object,
    .i32 kind,
    .i32 0,
    .i32 0,
    .i32 descriptor,
    .i32 0,
    .i32 flags,
    .i32 0,
    .i32 0,
    .i32 0]
  values := [] }

/-- Persistent arm after loading both physical lanes used to distinguish a
promoted tagged natural from an ordinary persistent allocation. -/
def persistentMarkerLocals
    (object check flags descriptor kind marker : UInt32) : Wasm.Locals := {
  params := [.i32 object, .i32 check]
  locals := [
    .i32 object,
    .i32 kind,
    .i32 0,
    .i32 0,
    .i32 descriptor,
    .i32 0,
    .i32 flags,
    .i32 marker,
    .i32 0,
    .i32 0]
  values := [] }

/-- Ordinary-arm frame after the reference count has been loaded. -/
def countedLocals (object check flags descriptor refCount : UInt32) :
    Wasm.Locals := {
  params := [.i32 object, .i32 check]
  locals := [
    .i32 object,
    .i32 0,
    .i32 0,
    .i32 0,
    .i32 descriptor,
    .i32 refCount,
    .i32 flags,
    .i32 0,
    .i32 0,
    .i32 0]
  values := [] }

/-- Concrete entry frame of the one-parameter `fir_release_header` helper. -/
def releaseHeaderEntry (object : UInt32) : Wasm.Locals := {
  params := [.i32 object]
  locals := []
  values := [] }

/-- Last-reference frame after loading all four lanes used by object-kind
dispatch and recursive child release.  Zero arguments describe the successive
intermediate frames before each lane is populated. -/
def ownedEntry (object check flags descriptor refCount kind marker count
    captureCount : UInt32) : Wasm.Locals := {
  params := [.i32 object, .i32 check]
  locals := [
    .i32 object,
    .i32 kind,
    .i32 count,
    .i32 captureCount,
    .i32 descriptor,
    .i32 refCount,
    .i32 flags,
    .i32 marker,
    .i32 0,
    .i32 0]
  values := [] }

/-- The exact common-header invariant required when resident Wasm preserves
raw lanes that the decoded W6 host may otherwise canonicalize on rewrite.
This is state, not compiler evidence: clients establish it once for an
allocation and preserve it across verified resident transitions. -/
def CanonicalLiveHeaderRel (state : MemoryState) (address : Word32) : Prop :=
  ∀ header, state.readLiveHeader address = .ok header →
    Header.ExactWords state.memory address header

/-- Global raw-header admission for every semantic location tracked by the
refinement witness.  Dead locations satisfy the live-header clause
vacuously; if a later transition observes a mapped address as live, all eight
physical header words must be canonical. -/
def CanonicalMappedHeadersRel
    (state : MemoryState) (witness : RefinementWitness) : Prop :=
  ∀ {location address},
    witness.locations.lookup? location = some address →
    CanonicalLiveHeaderRel state address

/-- A full-header ownership write preserves global raw-header admission.  The
target obtains exact words from the write itself; descriptor disjointness
frames every other mapped allocation. -/
theorem CanonicalMappedHeadersRel.ofHeaderWrite
    {before after : MemoryState} {witness : RefinementWitness}
    {runtime : Fir.LeanIR.Impure.RuntimeState}
    {targetAddress : Word32} {targetDescriptor : AllocationDescriptor}
    {oldHeader updatedHeader : Header} {memory : LinearMemory}
    (canonical : CanonicalMappedHeadersRel before witness)
    (related : LiveHeapRel before witness runtime)
    (targetFound :
      witness.descriptors.lookup? targetAddress = some targetDescriptor)
    (oldRead : Header.read before.memory targetAddress = .ok oldHeader)
    (resultEq : after = { before with memory })
    (headerInBounds :
      targetAddress.value + headerBytes ≤ before.memory.size)
    (written : updatedHeader.write before.memory targetAddress = .ok memory) :
    CanonicalMappedHeadersRel after witness := by
  intro location address mapped header headerRead
  obtain ⟨cell, _, cellRelated⟩ :=
    related.concreteToSemantic location address mapped
  obtain ⟨descriptor, descriptorFound⟩ := cellRelated.descriptor
  by_cases different : targetAddress.value ≠ address.value
  · obtain ⟨otherHeader, otherRead, minimum, _, _⟩ :=
      related.descriptorRegion address descriptor descriptorFound
    have frame := related.allocationFrame_of_headerWrite_other targetFound
      descriptorFound different oldRead otherRead resultEq headerInBounds written
    have beforeRead : before.readLiveHeader address = .ok header := by
      rw [frame.readLiveHeader minimum] at headerRead
      exact headerRead
    exact (canonical mapped header beforeRead).allocationFrame frame minimum
  · have sameValue : targetAddress.value = address.value := by omega
    have sameAddress : targetAddress = address := by
      cases targetAddress
      cases address
      simp_all
    subst address
    obtain ⟨_, decodedRead, _, _, _, _⟩ :=
      MemoryState.PrefixExtension.readLiveHeader_facts after targetAddress header
        headerRead
    have updatedRead : Header.read after.memory targetAddress = .ok updatedHeader := by
      rw [resultEq]
      exact Header.read_of_write_eq_ok before.memory memory targetAddress
        updatedHeader headerInBounds written
    have headerEq : header = updatedHeader :=
      Except.ok.inj (decodedRead.symm.trans updatedRead)
    subst header
    rw [resultEq]
    exact Header.ExactWords.ofWrite_eq_ok headerInBounds written

/-- Branch-independent physical facts for entering resident release on one
canonical live heap header.  Packaging these once keeps the semantic branch
proofs focused on ownership behavior rather than bit-level address gates. -/
structure LiveHeaderResidentFacts
    (memory : Wasm.Mem) (address : Word32) (header : Header) : Prop where
  taggedClear :
    (1 : UInt32) &&& UInt32.ofNat address.value = 0
  objectNonzero : UInt32.ofNat address.value ≠ 0
  alignmentClear :
    UInt32.ofNat (target.heapAlignment - 1) &&&
      UInt32.ofNat address.value = 0
  flagsInBounds :
    ¬((UInt32.ofNat address.value).toNat +
      (UInt32.ofNat headerFlagsOffset).toNat + 4 >
      memory.pages * wasmPageBytes)
  flagsRead : memory.read32
    (UInt32.ofNat address.value + UInt32.ofNat headerFlagsOffset) =
      header.flags
  liveSet : liveFlag &&& header.flags = liveFlag
  kindInBounds :
    ¬((UInt32.ofNat address.value).toNat +
      (UInt32.ofNat headerKindOffset).toNat + 4 >
      memory.pages * wasmPageBytes)
  kindRead : memory.read32
    (UInt32.ofNat address.value + UInt32.ofNat headerKindOffset) =
      header.kind.code
  refCountInBounds :
    ¬((UInt32.ofNat address.value).toNat +
      (UInt32.ofNat headerRefCountOffset).toNat + 4 >
      memory.pages * wasmPageBytes)
  refCountRead : memory.read32
    (UInt32.ofNat address.value + UInt32.ofNat headerRefCountOffset) =
      header.refCount
  aux0InBounds :
    ¬((UInt32.ofNat address.value).toNat +
      (UInt32.ofNat headerAux0Offset).toNat + 4 >
      memory.pages * wasmPageBytes)
  aux0Read : memory.read32
    (UInt32.ofNat address.value + UInt32.ofNat headerAux0Offset) =
      header.aux0
  aux1InBounds :
    ¬((UInt32.ofNat address.value).toNat +
      (UInt32.ofNat headerAux1Offset).toNat + 4 >
      memory.pages * wasmPageBytes)
  aux1Read : memory.read32
    (UInt32.ofNat address.value + UInt32.ofNat headerAux1Offset) =
      header.aux1
  aux2InBounds :
    ¬((UInt32.ofNat address.value).toNat +
      (UInt32.ofNat headerAux2Offset).toNat + 4 >
      memory.pages * wasmPageBytes)
  aux2Read : memory.read32
    (UInt32.ofNat address.value + UInt32.ofNat headerAux2Offset) =
      header.aux2
  aux3InBounds :
    ¬((UInt32.ofNat address.value).toNat +
      (UInt32.ofNat headerAux3Offset).toNat + 4 >
      memory.pages * wasmPageBytes)
  aux3Read : memory.read32
    (UInt32.ofNat address.value + UInt32.ofNat headerAux3Offset) =
      header.aux3

/-- Exact Talos spelling of W7's full-header terminal-word probe. -/
def probeCompleteHeaderProgram : Wasm.Program := [
  .localGet addressIndex,
  .load32 (UInt32.ofNat headerAux3Offset),
  .localSet descriptorIndex]

/-- Exact hot-path store for an ordinary object with more than one owner. -/
def decrementAboveOneProgram : Wasm.Program := [
  .localGet addressIndex,
  .localGet refCountIndex,
  .const 1,
  .sub,
  .store32 (UInt32.ofNat headerRefCountOffset),
  .ret]

/-- Exact Talos body of W7's nonrecursive header-release helper.  The
allocation-size lane is intentionally retained while kind, ownership flags,
reference count, and auxiliary metadata are cleared. -/
def releaseHeaderProgram : Wasm.Program := [
  .localGet 0,
  .const ObjectKind.freed.code,
  .store32 (UInt32.ofNat headerKindOffset),
  .localGet 0,
  .const 0,
  .store32 (UInt32.ofNat headerFlagsOffset),
  .localGet 0,
  .const 0,
  .store32 (UInt32.ofNat headerRefCountOffset),
  .localGet 0,
  .const 0,
  .store32 (UInt32.ofNat headerAux0Offset),
  .localGet 0,
  .const 0,
  .store32 (UInt32.ofNat headerAux1Offset),
  .localGet 0,
  .const 0,
  .store32 (UInt32.ofNat headerAux2Offset),
  .localGet 0,
  .const 0,
  .store32 (UInt32.ofNat headerAux3Offset),
  .ret]

/-- Physical memory produced by the seven resident header-release stores. -/
def releaseHeaderMemory (memory : Wasm.Mem) (object : UInt32) : Wasm.Mem :=
  let memory := memory.write32
    (object + UInt32.ofNat headerKindOffset) ObjectKind.freed.code
  let memory := memory.write32
    (object + UInt32.ofNat headerFlagsOffset) 0
  let memory := memory.write32
    (object + UInt32.ofNat headerRefCountOffset) 0
  let memory := memory.write32
    (object + UInt32.ofNat headerAux0Offset) 0
  let memory := memory.write32
    (object + UInt32.ofNat headerAux1Offset) 0
  let memory := memory.write32
    (object + UInt32.ofNat headerAux2Offset) 0
  memory.write32 (object + UInt32.ofNat headerAux3Offset) 0

/-- Store-level spelling of `releaseHeaderMemory`. -/
def releaseHeaderStore (store : Wasm.Store host) (object : UInt32) :
    Wasm.Store host :=
  { store with mem := releaseHeaderMemory store.mem object }

/-- Exact common prefix of W7's last-reference branch.  Descriptor-dependent
owned-field traversal remains the supplied suffix. -/
def lastReferenceProgram (releaseHeaderIndex : Nat) (owned : Wasm.Program) :
    Wasm.Program := [
  .localGet addressIndex,
  .load32 (UInt32.ofNat headerKindOffset),
  .localSet kindIndex,
  .localGet addressIndex,
  .load32 (UInt32.ofNat headerAux0Offset),
  .localSet markerIndex,
  .localGet addressIndex,
  .load32 (UInt32.ofNat headerAux1Offset),
  .localSet countIndex,
  .localGet addressIndex,
  .load32 (UInt32.ofNat headerAux2Offset),
  .localSet captureCountIndex,
  .localGet addressIndex,
  .call releaseHeaderIndex] ++ owned

/-- Exact object-kind dispatcher used after the last-reference header has
already been released.  Recursive constructor, closure, and opaque traversal
remain explicit parameters; every other live representation is a leaf. -/
def ownedReleaseProgram (constructorBody closureBody opaqueBody : Wasm.Program) :
    Wasm.Program := [
  .localGet kindIndex,
  .const ObjectKind.constructor.code,
  .eq,
  .iff 0 0 constructorBody [
    .localGet kindIndex,
    .const ObjectKind.closure.code,
    .eq,
    .iff 0 0 closureBody [
      .localGet kindIndex,
      .const ObjectKind.opaque.code,
      .eq,
      .iff 0 0 opaqueBody [.ret]]]]

/-- One recursively owned payload release.  The child word is loaded from the
parent payload and passed to `fir_dec_once` with physical check word one. -/
def releaseChildProgram (decrementIndex index : Nat) : Wasm.Program := [
  .localGet addressIndex,
  .load32 (UInt32.ofNat
    (headerBytes + target.semanticSlotBytes * index)),
  .const 1,
  .call decrementIndex]

/-- Direct sequential traversal used by closure descriptors and by the
selected-field core of constructor release. -/
def releaseChildrenProgram (decrementIndex : Nat) : List Nat → Wasm.Program
  | [] => []
  | index :: rest =>
      releaseChildProgram decrementIndex index ++
        releaseChildrenProgram decrementIndex rest

/-- Exact source-state payload reads paired with the physical indices visited
by resident ownership release.  The retained-allocation and memory bounds are
recorded at each lane so the relation applies uniformly to constructor
fields, selected closure captures, and the live prefix of resident Arrays. -/
inductive OwnedPayloadWordsRel (state : MemoryState) (object : Word32)
    (header : Header) : List Nat → List Word32 → Prop where
  | nil : OwnedPayloadWordsRel state object header [] []
  | cons {index : Nat} {indices : List Nat} {word : Word32}
      {words : List Word32}
      (within :
        headerBytes + target.semanticSlotBytes * index + 4 ≤
          header.allocationBytes.toNat)
      (inBounds :
        object.value + headerBytes + target.semanticSlotBytes * index + 3 <
          state.memory.size)
      (read : state.memory.readWord32
        (object.value + headerBytes + target.semanticSlotBytes * index) =
          .ok word)
      (tail : OwnedPayloadWordsRel state object header indices words) :
      OwnedPayloadWordsRel state object header
        (index :: indices) (word :: words)

/-- A mapped-payload frame plus the current resident-memory relation exposes
an original owned word as the exact lazy `i32.load` result in the current
Wasm store.  This is the key bridge that allows earlier recursive releases
to modify headers while later parent payload lanes are loaded on demand. -/
theorem MappedPayloadFrameTransport.residentRead32
    {source current : MemoryState} {witness : RefinementWitness}
    (frame : MappedPayloadFrameTransport source current witness)
    {memory : Wasm.Mem} (memoryRelated : ResidentMemoryRel current memory)
    {location : Fir.LeanIR.Impure.Location} {object : Word32}
    {header : Header} {offset : Nat} {word : Word32}
    (mapped : witness.locations.lookup? location = some object)
    (headerRead : Header.read source.memory object = .ok header)
    (headerOwned : object.value + headerBytes ≤ source.heapCursor)
    (afterHeader : headerBytes ≤ offset)
    (within : offset + 4 ≤ header.allocationBytes.toNat)
    (sourceInBounds : object.value + offset + 3 < source.memory.size)
    (sourceRead : source.memory.readWord32 (object.value + offset) = .ok word) :
    ¬((UInt32.ofNat object.value).toNat +
        (UInt32.ofNat offset).toNat + 4 > memory.pages * wasmPageBytes) ∧
      memory.read32
        (UInt32.ofNat object.value + UInt32.ofNat offset) =
          UInt32.ofNat word.value := by
  have currentInBounds :
      object.value + offset + 3 < current.memory.size := by
    rw [frame.memorySize]
    exact sourceInBounds
  have currentRead :
      current.memory.readWord32 (object.value + offset) = .ok word := by
    rw [frame.readWord32 mapped headerRead headerOwned offset afterHeader within]
    exact sourceRead
  have residentRead :=
    memoryRelated.readWord32_eq_read32 currentInBounds currentRead
  have objectFits : object.value < UInt32.size := by
    simpa [wordModulus] using object.isLt
  have offsetFits : offset < UInt32.size := by
    have addressFits : object.value + offset + 3 < UInt32.size :=
      Nat.lt_of_lt_of_le currentInBounds memoryRelated.size_le
    omega
  constructor
  · rw [UInt32.toNat_ofNat_of_lt' objectFits,
      UInt32.toNat_ofNat_of_lt' offsetFits, ← memoryRelated.size_eq]
    omega
  · simpa [UInt32.ofNat_add] using residentRead

/-- Fuel-free semantic call chain for direct child traversal.  Each later
payload read is stated in the store produced by the preceding child release;
this is the exact framing obligation later discharged by the heap relation. -/
inductive ReleaseChildrenRun
    {host : Type} (env : Wasm.HostEnv host) (module : Wasm.Module)
    (decrementIndex : Nat) (object : UInt32) :
    List Nat → Wasm.Store host → Wasm.Store host → Prop where
  | nil (store : Wasm.Store host) :
      ReleaseChildrenRun env module decrementIndex object [] store store
  | cons {index : Nat} {indices : List Nat}
      {initial middle final : Wasm.Store host} {child : UInt32}
      (inBounds :
        ¬(object.toNat +
          (UInt32.ofNat
            (headerBytes + target.semanticSlotBytes * index)).toNat + 4 >
          initial.mem.pages * wasmPageBytes))
      (read : initial.mem.read32
        (object + UInt32.ofNat
          (headerBytes + target.semanticSlotBytes * index)) = child)
      (call : Wasm.TerminatesWith env module decrementIndex initial
        [.i32 1, .i32 child]
        (fun next values => next = middle ∧ values = []))
      (tail : ReleaseChildrenRun env module decrementIndex object
        indices middle final) :
      ReleaseChildrenRun env module decrementIndex object
        (index :: indices) initial final

/-- Paired source/concrete/resident induction for a direct owned-child list.
The parent payload lanes are read from `source`; `sourceFrame` proves that all
earlier recursive ownership steps preserve them until each lazy Wasm load.
The abstract `step` premise is precisely the smaller recursive theorem needed
later by the full `fir_dec_once` fuel induction, including tagged and erased
no-op calls as well as mapped heap children. -/
theorem OwnershipValuesRel.releaseChildrenRun_refines
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {decrementIndex fuel : Nat}
    {source current : MemoryState} {witness : RefinementWitness}
    {runtime finalRuntime : Fir.LeanIR.Impure.RuntimeState}
    {location : Fir.LeanIR.Impure.Location} {object : Word32}
    {header : Header} {indices : List Nat} {words : List Word32}
    {values : List Fir.LeanIR.Impure.Value}
    {initial : Wasm.Store host}
    (ownership : OwnershipValuesRel witness words values)
    (payload : OwnedPayloadWordsRel source object header indices words)
    (mapped : witness.locations.lookup? location = some object)
    (headerRead : Header.read source.memory object = .ok header)
    (headerOwned : object.value + headerBytes ≤ source.heapCursor)
    (heap : LiveHeapRel current witness runtime)
    (memoryRelated : ResidentMemoryRel current initial.mem)
    (canonicalHeaders : CanonicalMappedHeadersRel current witness)
    (sourceFrame : MappedPayloadFrameTransport source current witness)
    (step : ∀ {before : MemoryState} {beforeStore : Wasm.Store host}
        {semantic nextSemantic : Fir.LeanIR.Impure.RuntimeState}
        {word : Word32} {value : Fir.LeanIR.Impure.Value},
      OwnershipValueRel witness word value →
      LiveHeapRel before witness semantic →
      ResidentMemoryRel before beforeStore.mem →
      CanonicalMappedHeadersRel before witness →
      (match value with
      | .object (.heap child) =>
          Fir.LeanIR.Impure.decLocationFuel fuel semantic child
      | _ => .ok semantic) = .ok nextSemantic →
      ∃ after middleStore,
        decrementReferenceOnceFuel fuel before word true
            witness.closureDescriptors = .ok after ∧
        LiveHeapRel after witness nextSemantic ∧
        ResidentMemoryRel after middleStore.mem ∧
        CanonicalMappedHeadersRel after witness ∧
        MappedPayloadFrameTransport before after witness ∧
        Wasm.TerminatesWith env module decrementIndex beforeStore
          [.i32 1, .i32 (UInt32.ofNat word.value)]
          (fun next results => next = middleStore ∧ results = []))
    (semanticOperation :
      values.foldlM (init := runtime) (fun next value =>
        match value with
        | .object (.heap child) =>
            Fir.LeanIR.Impure.decLocationFuel fuel next child
        | _ => .ok next) = .ok finalRuntime) :
    ∃ finalState finalStore,
      words.foldlM (init := current) (fun next word =>
        decrementReferenceOnceFuel fuel next word true
          witness.closureDescriptors) = .ok finalState ∧
      LiveHeapRel finalState witness finalRuntime ∧
      ResidentMemoryRel finalState finalStore.mem ∧
      CanonicalMappedHeadersRel finalState witness ∧
      MappedPayloadFrameTransport source finalState witness ∧
      ReleaseChildrenRun env module decrementIndex
        (UInt32.ofNat object.value) indices initial finalStore := by
  induction ownership generalizing indices current initial runtime finalRuntime with
  | nil =>
      cases payload
      simp only [List.foldlM_nil] at semanticOperation ⊢
      have runtimeEq := Except.ok.inj semanticOperation
      subst finalRuntime
      exact ⟨current, initial, rfl, heap, memoryRelated, canonicalHeaders,
        sourceFrame, .nil initial⟩
  | @cons word value words values head tail ih =>
      cases payload with
      | @cons index indices _ _ within sourceInBounds sourceRead payloadTail =>
          simp only [List.foldlM_cons, Bind.bind, Except.bind]
            at semanticOperation
          cases headSemantic :
              (match value with
              | .object (.heap child) =>
                  Fir.LeanIR.Impure.decLocationFuel fuel runtime child
              | _ => .ok runtime) with
          | error fault =>
              rw [headSemantic] at semanticOperation
              contradiction
          | ok nextRuntime =>
              rw [headSemantic] at semanticOperation
              obtain ⟨nextState, middleStore, concreteHead, nextHeap,
                  nextMemory, nextCanonical, stepFrame, targetCall⟩ :=
                step head heap memoryRelated canonicalHeaders headSemantic
              obtain ⟨finalState, finalStore, concreteTail, finalHeap,
                  finalMemory, finalCanonical, finalFrame, tailRun⟩ :=
                ih payloadTail nextHeap nextMemory nextCanonical
                  (sourceFrame.trans stepFrame) semanticOperation
              have residentHead :=
                FirTalos.Concrete.ResidentRelease.MappedPayloadFrameTransport.residentRead32
                sourceFrame memoryRelated mapped headerRead headerOwned
                (offset := headerBytes + target.semanticSlotBytes * index)
                (by omega) within
                (by simpa [Nat.add_assoc] using sourceInBounds)
                (by simpa [Nat.add_assoc] using sourceRead)
              refine ⟨finalState, finalStore, ?_, finalHeap, finalMemory,
                finalCanonical, finalFrame, ?_⟩
              · simp only [List.foldlM_cons, Bind.bind, Except.bind]
                rw [concreteHead]
                exact concreteTail
              · exact .cons residentHead.1 residentHead.2 targetCall tailRun

/-- Per-index guard used by the fixed-width constructor release frontier. -/
def guardedReleaseChildProgram
    (decrementIndex countLocal index : Nat) : Wasm.Program := [
  .const (UInt32.ofNat index),
  .localGet countLocal,
  .ltU,
  .iff 0 0 (releaseChildProgram decrementIndex index) []]

/-- Guarded traversal of a finite physical index frontier. -/
def guardedReleaseChildrenProgram
    (decrementIndex countLocal : Nat) : List Nat → Wasm.Program
  | [] => []
  | index :: rest =>
      guardedReleaseChildProgram decrementIndex countLocal index ++
        guardedReleaseChildrenProgram decrementIndex countLocal rest

/-- Exact fixed-frontier constructor-owned release body. -/
def constructorReleaseProgram (decrementIndex : Nat) : Wasm.Program := [
  .const (UInt32.ofNat
    Fir.Wasm.Emit.ResidentRelease.constructorFieldLimit),
  .localGet countIndex,
  .ltU,
  .iff 0 0 [.unreachable]
    (guardedReleaseChildrenProgram decrementIndex countIndex
      (List.range Fir.Wasm.Emit.ResidentRelease.constructorFieldLimit) ++
      [.ret])]

/-- Store-indexed execution evidence for a guarded child frontier.  Taken
entries carry the same exact load/call contract as direct descriptor fields;
skipped entries preserve the current store. -/
inductive GuardedReleaseChildrenRun
    {host : Type} (env : Wasm.HostEnv host) (module : Wasm.Module)
    (decrementIndex : Nat) (object count : UInt32) :
    List Nat → Wasm.Store host → Wasm.Store host → Prop where
  | nil (store : Wasm.Store host) :
      GuardedReleaseChildrenRun env module decrementIndex object count
        [] store store
  | skip {index : Nat} {indices : List Nat}
      {initial final : Wasm.Store host}
      (notTaken : ¬(UInt32.ofNat index < count))
      (tail : GuardedReleaseChildrenRun env module decrementIndex object count
        indices initial final) :
      GuardedReleaseChildrenRun env module decrementIndex object count
        (index :: indices) initial final
  | take {index : Nat} {indices : List Nat}
      {initial middle final : Wasm.Store host} {child : UInt32}
      (taken : UInt32.ofNat index < count)
      (inBounds :
        ¬(object.toNat +
          (UInt32.ofNat
            (headerBytes + target.semanticSlotBytes * index)).toNat + 4 >
          initial.mem.pages * wasmPageBytes))
      (read : initial.mem.read32
        (object + UInt32.ofNat
          (headerBytes + target.semanticSlotBytes * index)) = child)
      (call : Wasm.TerminatesWith env module decrementIndex initial
        [.i32 1, .i32 child]
        (fun next values => next = middle ∧ values = []))
      (tail : GuardedReleaseChildrenRun env module decrementIndex object count
        indices middle final) :
      GuardedReleaseChildrenRun env module decrementIndex object count
        (index :: indices) initial final

/-- Direct child-call evidence embeds into guarded traversal when every named
index is below the physical count. -/
theorem ReleaseChildrenRun.toGuarded
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {decrementIndex : Nat} {object count : UInt32}
    {indices : List Nat} {initial final : Wasm.Store host}
    (runs : ReleaseChildrenRun env module decrementIndex object
      indices initial final)
    (taken : ∀ index ∈ indices, UInt32.ofNat index < count) :
    GuardedReleaseChildrenRun env module decrementIndex object count
      indices initial final := by
  induction runs with
  | nil store => exact .nil store
  | @cons index indices initial middle final child inBounds read call tail ih =>
      apply GuardedReleaseChildrenRun.take (taken index (by simp))
        inBounds read call
      exact ih (by
        intro next member
        exact taken next (by simp [member]))

/-- A list of uniformly out-of-range indices forms a store-preserving guarded
suffix. -/
theorem GuardedReleaseChildrenRun.skipAll
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {decrementIndex : Nat} {object count : UInt32}
    (indices : List Nat) (store : Wasm.Store host)
    (notTaken : ∀ index ∈ indices, ¬(UInt32.ofNat index < count)) :
    GuardedReleaseChildrenRun env module decrementIndex object count
      indices store store := by
  induction indices with
  | nil => exact .nil store
  | cons index indices ih =>
      apply GuardedReleaseChildrenRun.skip (notTaken index (by simp))
      exact ih (by
        intro next member
        exact notTaken next (by simp [member]))

/-- Guarded child-call chains compose at their exact intermediate store. -/
theorem GuardedReleaseChildrenRun.append
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {decrementIndex : Nat} {object count : UInt32}
    {left right : List Nat} {initial middle final : Wasm.Store host}
    (leftRun : GuardedReleaseChildrenRun env module decrementIndex object count
      left initial middle)
    (rightRun : GuardedReleaseChildrenRun env module decrementIndex object count
      right middle final) :
    GuardedReleaseChildrenRun env module decrementIndex object count
      (left ++ right) initial final := by
  induction leftRun with
  | nil store => simpa using rightRun
  | skip notTaken tail ih =>
      exact .skip notTaken (ih rightRun)
  | take taken inBounds read call tail ih =>
      exact .take taken inBounds read call (ih rightRun)

/-- Complete the fixed constructor frontier from exact evidence for its live
fields.  Indices below `fieldCount` execute recursive decrements; every
remaining physical slot up to W7's limit is skipped without touching the
store. -/
theorem ReleaseChildrenRun.completeConstructorFrontier
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {decrementIndex fieldCount : Nat} {object count : UInt32}
    {initial final : Wasm.Store host}
    (runs : ReleaseChildrenRun env module decrementIndex object
      (List.range fieldCount) initial final)
    (fieldCountFits : fieldCount < UInt32.size)
    (withinLimit :
      fieldCount ≤ Fir.Wasm.Emit.ResidentRelease.constructorFieldLimit)
    (countEq : count = UInt32.ofNat fieldCount) :
    GuardedReleaseChildrenRun env module decrementIndex object count
      (List.range Fir.Wasm.Emit.ResidentRelease.constructorFieldLimit)
      initial final := by
  have active :
      GuardedReleaseChildrenRun env module decrementIndex object count
        (List.range fieldCount) initial final :=
    runs.toGuarded (by
      intro index member
      have indexLt : index < fieldCount := List.mem_range.mp member
      rw [UInt32.lt_iff_toNat_lt,
        UInt32.toNat_ofNat_of_lt' (indexLt.trans fieldCountFits), countEq,
        UInt32.toNat_ofNat_of_lt' fieldCountFits]
      exact indexLt)
  let remaining :=
    List.map (fun offset => fieldCount + offset)
      (List.range
        (Fir.Wasm.Emit.ResidentRelease.constructorFieldLimit - fieldCount))
  have skipped :
      GuardedReleaseChildrenRun env module decrementIndex object count
        remaining final final :=
    GuardedReleaseChildrenRun.skipAll remaining final (by
      intro index member below
      rcases List.mem_map.mp member with ⟨offset, offsetMember, rfl⟩
      have offsetLt :
          offset <
            Fir.Wasm.Emit.ResidentRelease.constructorFieldLimit - fieldCount :=
        List.mem_range.mp offsetMember
      have indexLt :
          fieldCount + offset <
            Fir.Wasm.Emit.ResidentRelease.constructorFieldLimit := by
        omega
      have indexFits : fieldCount + offset < UInt32.size :=
        indexLt.trans (by decide)
      rw [countEq, UInt32.lt_iff_toNat_lt,
        UInt32.toNat_ofNat_of_lt' indexFits,
        UInt32.toNat_ofNat_of_lt' fieldCountFits] at below
      omega)
  have combined := active.append skipped
  have frontierEq :
      List.range Fir.Wasm.Emit.ResidentRelease.constructorFieldLimit =
        List.range fieldCount ++ remaining := by
    rw [show Fir.Wasm.Emit.ResidentRelease.constructorFieldLimit =
      fieldCount +
        (Fir.Wasm.Emit.ResidentRelease.constructorFieldLimit - fieldCount) by
          omega,
      List.range_add]
  rw [frontierEq]
  exact combined

/-- Ordinary release control flow.  The count-zero and last-reference paths
remain explicit but opaque: the hot theorem below proves they are not entered. -/
def ordinaryReleaseProgram (lastReference : Wasm.Program) : Wasm.Program := [
  .localGet addressIndex,
  .load32 (UInt32.ofNat headerRefCountOffset),
  .localSet refCountIndex,
  .localGet refCountIndex,
  .const 0,
  .eq,
  .iff 0 0 [.unreachable] [
    .const 1,
    .localGet refCountIndex,
    .ltU,
    .iff 0 0 decrementAboveOneProgram lastReference]]

/-- Shared live-object dispatch with both cold branches supplied by the
caller.  Its hot path is independent of closure descriptors and payload kind. -/
def liveReleaseProgram (persistent lastReference : Wasm.Program) : Wasm.Program :=
  probeCompleteHeaderProgram ++ [
    .localGet flagsIndex,
    .const persistentFlag,
    .and,
    .const persistentFlag,
    .eq,
    .iff 0 0 persistent (ordinaryReleaseProgram lastReference)]

/-- Concrete function-entry frame of `fir_dec_once`. -/
def decrementEntry (object check : UInt32) : Wasm.Locals := {
  params := [.i32 object, .i32 check]
  locals := List.replicate 10 (.i32 0)
  values := [] }

/-- Checked no-op/trap gate shared by tagged and erased inputs. -/
def checkedNoopProgram : Wasm.Program := [
  .localGet checkIndex,
  .iff 0 0 [.ret] [.unreachable]]

/-- Exact Talos spelling of W7's persistent-object branch.  Ordinary
persistent objects return unchanged; the distinguished promoted-Nat encoding
retains the checked tagged-value behavior. -/
def persistentReleaseProgram : Wasm.Program := [
  .localGet addressIndex,
  .load32 (UInt32.ofNat headerKindOffset),
  .localSet kindIndex,
  .localGet addressIndex,
  .load32 (UInt32.ofNat headerAux0Offset),
  .localSet markerIndex,
  .localGet kindIndex,
  .const ObjectKind.natural.code,
  .eq,
  .iff 0 0 [
    .localGet addressIndex,
    .load32 (UInt32.ofNat headerAux0Offset),
    .const promotedTagMarker,
    .eq,
    .iff 0 0 checkedNoopProgram [.ret]] [.ret]]

/-- Exact target spelling of the aligned live-object dispatch. -/
def alignedReleaseProgram (persistent lastReference : Wasm.Program) :
    Wasm.Program := [
  .localGet objectIndex,
  .const 0,
  .add,
  .localSet addressIndex,
  .localGet addressIndex,
  .load32 (UInt32.ofNat headerFlagsOffset),
  .localSet flagsIndex,
  .localGet flagsIndex,
  .const liveFlag,
  .and,
  .const liveFlag,
  .eq,
  .iff 0 0 (liveReleaseProgram persistent lastReference) [.unreachable]]

/-- Exact target control flow of `fir_dec_once`, parameterized only by the
cold programs that the shared-reference theorem does not enter. -/
def decrementOnceProgram (persistent lastReference : Wasm.Program) :
    Wasm.Program := [
  .localGet objectIndex,
  .const 1,
  .and,
  .iff 0 0 checkedNoopProgram [
    .localGet objectIndex,
    .const 0,
    .eq,
    .iff 0 0 checkedNoopProgram [
      .localGet objectIndex,
      .const (UInt32.ofNat (target.heapAlignment - 1)),
      .and,
      .const 0,
      .eq,
      .iff 0 0 (alignedReleaseProgram persistent lastReference)
        [.unreachable]]]]

/-- Postcondition for branch proofs that deliberately terminate the current
function.  It excludes fallthrough and structured breaks, while treating a
normal return and a trap uniformly through the caller's assertion. -/
def TerminalPost {host : Type} (Q : Wasm.Assertion host) :
    Wasm.Assertion host
  | continuation@(.Return _ _) => Q continuation
  | continuation@(.Trap _ _) => Q continuation
  | _ => False

/-- The concrete `fir_release_header` body performs exactly its seven checked
word stores and returns no values.  A single full-header bound discharges all
seven accesses and remains stable because stores do not change memory pages. -/
theorem wp_releaseHeaderProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {object : UInt32}
    (headerInBounds :
      object.toNat + headerBytes ≤ store.mem.pages * wasmPageBytes)
    (returned : Q (.Return (releaseHeaderStore store object) [])) :
    Wasm.wp module releaseHeaderProgram Q store
      (releaseHeaderEntry object) env := by
  have addressFound : (releaseHeaderEntry object).get 0 =
      some (.i32 object) := by rfl
  unfold releaseHeaderProgram
  apply ResidentMemoryRel.wp_store32_const_of_inBounds addressFound
    (by simp [headerBytes, headerKindOffset] at headerInBounds ⊢; omega)
  apply ResidentMemoryRel.wp_store32_const_of_inBounds addressFound
    (by simp [headerBytes, headerFlagsOffset] at headerInBounds ⊢; omega)
  apply ResidentMemoryRel.wp_store32_const_of_inBounds addressFound
    (by simp [headerBytes, headerRefCountOffset] at headerInBounds ⊢; omega)
  apply ResidentMemoryRel.wp_store32_const_of_inBounds addressFound
    (by simp [headerBytes, headerAux0Offset] at headerInBounds ⊢; omega)
  apply ResidentMemoryRel.wp_store32_const_of_inBounds addressFound
    (by simp [headerBytes, headerAux1Offset] at headerInBounds ⊢; omega)
  apply ResidentMemoryRel.wp_store32_const_of_inBounds addressFound
    (by simp [headerBytes, headerAux2Offset] at headerInBounds ⊢; omega)
  apply ResidentMemoryRel.wp_store32_const_of_inBounds addressFound
    (by simpa [headerBytes, headerAux3Offset] using headerInBounds)
  simp only [Wasm.wp_ret_cons]
  simpa [releaseHeaderStore, releaseHeaderMemory,
    ResidentMemoryRel.write32Store] using returned

/-- Execute the common last-reference prefix through the release-header call.
The callee contract names its exact successor store; object-kind-specific
proofs continue from the fully populated owned-dispatch frame. -/
theorem wp_lastReferenceProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store releasedStore : Wasm.Store host}
    {object check flags descriptor refCount kind marker count
      captureCount : UInt32}
    {releaseHeaderIndex : Nat} {owned : Wasm.Program}
    (kindInBounds :
      ¬(object.toNat + (UInt32.ofNat headerKindOffset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (kindRead : store.mem.read32
      (object + UInt32.ofNat headerKindOffset) = kind)
    (markerInBounds :
      ¬(object.toNat + (UInt32.ofNat headerAux0Offset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (markerRead : store.mem.read32
      (object + UInt32.ofNat headerAux0Offset) = marker)
    (countInBounds :
      ¬(object.toNat + (UInt32.ofNat headerAux1Offset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (countRead : store.mem.read32
      (object + UInt32.ofNat headerAux1Offset) = count)
    (captureInBounds :
      ¬(object.toNat + (UInt32.ofNat headerAux2Offset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (captureRead : store.mem.read32
      (object + UInt32.ofNat headerAux2Offset) = captureCount)
    (releaseRun : Wasm.TerminatesWith env module releaseHeaderIndex store
      [.i32 object]
      (fun final values => final = releasedStore ∧ values = []))
    (ownedBody : Wasm.wp module owned Q releasedStore
      (ownedEntry object check flags descriptor refCount kind marker count
        captureCount) env) :
    Wasm.wp module (lastReferenceProgram releaseHeaderIndex owned) Q store
      (countedLocals object check flags descriptor refCount) env := by
  have countedAddress (values : List Wasm.Value) :
      ({ countedLocals object check flags descriptor refCount with values } :
        Wasm.Locals).get addressIndex = some (.i32 object) := by rfl
  have kindSet (values : List Wasm.Value) :
      ({ countedLocals object check flags descriptor refCount with
          values := .i32 kind :: values } : Wasm.Locals).set?
            kindIndex (.i32 kind) =
        some { ownedEntry object check flags descriptor refCount kind 0 0 0 with
          values := .i32 kind :: values } := by rfl
  have kindAddress (values : List Wasm.Value) :
      ({ ownedEntry object check flags descriptor refCount kind 0 0 0 with
          values } : Wasm.Locals).get addressIndex = some (.i32 object) := by
    rfl
  have markerSet (values : List Wasm.Value) :
      ({ ownedEntry object check flags descriptor refCount kind 0 0 0 with
          values := .i32 marker :: values } : Wasm.Locals).set?
            markerIndex (.i32 marker) =
        some { ownedEntry object check flags descriptor refCount kind marker 0 0 with
          values := .i32 marker :: values } := by rfl
  have markerAddress (values : List Wasm.Value) :
      ({ ownedEntry object check flags descriptor refCount kind marker 0 0 with
          values } : Wasm.Locals).get addressIndex = some (.i32 object) := by
    rfl
  have countSet (values : List Wasm.Value) :
      ({ ownedEntry object check flags descriptor refCount kind marker 0 0 with
          values := .i32 count :: values } : Wasm.Locals).set?
            countIndex (.i32 count) =
        some { ownedEntry object check flags descriptor refCount kind marker count 0 with
          values := .i32 count :: values } := by rfl
  have countAddress (values : List Wasm.Value) :
      ({ ownedEntry object check flags descriptor refCount kind marker count 0 with
          values } : Wasm.Locals).get addressIndex = some (.i32 object) := by
    rfl
  have captureSet (values : List Wasm.Value) :
      ({ ownedEntry object check flags descriptor refCount kind marker count 0 with
          values := .i32 captureCount :: values } : Wasm.Locals).set?
            captureCountIndex (.i32 captureCount) =
        some { ownedEntry object check flags descriptor refCount kind marker count
          captureCount with values := .i32 captureCount :: values } := by rfl
  have captureAddress (values : List Wasm.Value) :
      ({ ownedEntry object check flags descriptor refCount kind marker count
          captureCount with values } : Wasm.Locals).get addressIndex =
        some (.i32 object) := by rfl
  have kindInBounds' :
      ¬(object.toNat + (UInt32.ofNat headerKindOffset).toNat + 4 >
        store.mem.pages * 65536) := by
    simpa [wasmPageBytes] using kindInBounds
  have markerInBounds' :
      ¬(object.toNat + (UInt32.ofNat headerAux0Offset).toNat + 4 >
        store.mem.pages * 65536) := by
    simpa [wasmPageBytes] using markerInBounds
  have countInBounds' :
      ¬(object.toNat + (UInt32.ofNat headerAux1Offset).toNat + 4 >
        store.mem.pages * 65536) := by
    simpa [wasmPageBytes] using countInBounds
  have captureInBounds' :
      ¬(object.toNat + (UInt32.ofNat headerAux2Offset).toNat + 4 >
        store.mem.pages * 65536) := by
    simpa [wasmPageBytes] using captureInBounds
  unfold lastReferenceProgram
  simp only [List.cons_append, List.nil_append, Wasm.wp_localGet_cons,
    countedAddress, Wasm.wp_load32_cons]
  rw [if_neg kindInBounds', kindRead]
  simp only [Wasm.wp_localSet_cons, kindSet,
    Wasm.wp_localGet_cons, kindAddress, Wasm.wp_load32_cons]
  rw [if_neg markerInBounds', markerRead]
  simp only [markerSet, markerAddress]
  rw [if_neg countInBounds', countRead]
  simp only [countSet, countAddress]
  rw [if_neg captureInBounds', captureRead]
  simp only [captureSet, captureAddress]
  apply Wasm.wp_call_tw releaseRun
  intro final values completed
  rcases completed with ⟨rfl, rfl⟩
  exact ownedBody

/-- Nonrecursive object kinds return immediately after header release.  The
proof is independent of all three recursively owned suffixes. -/
theorem wp_ownedReleaseProgram_leaf
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {object check flags descriptor refCount kind marker count
      captureCount : UInt32}
    {constructorBody closureBody opaqueBody : Wasm.Program}
    (notConstructor : kind ≠ ObjectKind.constructor.code)
    (notClosure : kind ≠ ObjectKind.closure.code)
    (notOpaque : kind ≠ ObjectKind.opaque.code)
    (returned : Q (.Return store [])) :
    Wasm.wp module
      (ownedReleaseProgram constructorBody closureBody opaqueBody) Q store
      (ownedEntry object check flags descriptor refCount kind marker count
        captureCount) env := by
  have kindFound (values : List Wasm.Value) :
      ({ ownedEntry object check flags descriptor refCount kind marker count
          captureCount with values } : Wasm.Locals).get kindIndex =
        some (.i32 kind) := by rfl
  unfold ownedReleaseProgram
  simp only [Wasm.wp_localGet_cons, kindFound, Wasm.wp_const_cons,
    Wasm.wp_eq_cons, if_neg notConstructor]
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  simp only [List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, kindFound, Wasm.wp_const_cons, Wasm.wp_eq_cons,
    if_neg notClosure]
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  simp only [List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, kindFound, Wasm.wp_const_cons, Wasm.wp_eq_cons,
    if_neg notOpaque]
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  simpa only [List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_ret_cons, ownedEntry] using returned

/-- A semantic child-call chain executes the corresponding direct Wasm
payload traversal and preserves the parent frame for an arbitrary suffix. -/
theorem ReleaseChildrenRun.wp
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {initial final : Wasm.Store host}
    {object check flags descriptor refCount kind marker count
      captureCount : UInt32}
    {decrementIndex : Nat} {indices : List Nat} {rest : Wasm.Program}
    (runs : ReleaseChildrenRun env module decrementIndex object
      indices initial final)
    (continued : Wasm.wp module rest Q final
      (ownedEntry object check flags descriptor refCount kind marker count
        captureCount) env) :
    Wasm.wp module (releaseChildrenProgram decrementIndex indices ++ rest) Q
      initial
      (ownedEntry object check flags descriptor refCount kind marker count
        captureCount) env := by
  induction runs with
  | nil store =>
      simpa [releaseChildrenProgram] using continued
  | @cons index indices initial middle final child inBounds read call tail ih =>
      have addressFound (values : List Wasm.Value) :
          ({ ownedEntry object check flags descriptor refCount kind marker count
              captureCount with values } : Wasm.Locals).get addressIndex =
            some (.i32 object) := by rfl
      have inBounds' :
          ¬(object.toNat +
            (UInt32.ofNat
              (headerBytes + target.semanticSlotBytes * index)).toNat + 4 >
            initial.mem.pages * 65536) := by
        simpa [wasmPageBytes] using inBounds
      simp only [releaseChildrenProgram, releaseChildProgram,
        List.cons_append, List.nil_append,
        Wasm.wp_localGet_cons, addressFound, Wasm.wp_load32_cons]
      rw [if_neg inBounds', read]
      simp only [Wasm.wp_const_cons]
      apply Wasm.wp_call_tw call
      intro next values completed
      rcases completed with ⟨rfl, rfl⟩
      exact ih continued

/-- Execute the finite guarded child frontier from its store-indexed call
chain, preserving the parent frame and composing with an arbitrary suffix. -/
theorem GuardedReleaseChildrenRun.wp
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {initial final : Wasm.Store host}
    {object check flags descriptor refCount kind marker count
      captureCount : UInt32}
    {decrementIndex : Nat} {indices : List Nat} {rest : Wasm.Program}
    (runs : GuardedReleaseChildrenRun env module decrementIndex object count
      indices initial final)
    (continued : Wasm.wp module rest Q final
      (ownedEntry object check flags descriptor refCount kind marker count
        captureCount) env) :
    Wasm.wp module
      (guardedReleaseChildrenProgram decrementIndex countIndex indices ++ rest)
      Q initial
      (ownedEntry object check flags descriptor refCount kind marker count
        captureCount) env := by
  induction runs with
  | nil store =>
      simpa [guardedReleaseChildrenProgram] using continued
  | @skip index indices initial final notTaken tail ih =>
      have countFound (values : List Wasm.Value) :
          ({ ownedEntry object check flags descriptor refCount kind marker count
              captureCount with values } : Wasm.Locals).get countIndex =
            some (.i32 count) := by rfl
      simp only [guardedReleaseChildrenProgram, guardedReleaseChildProgram,
        List.cons_append, List.nil_append, Wasm.wp_const_cons,
        Wasm.wp_localGet_cons, countFound, Wasm.wp_ltU_cons, if_neg notTaken]
      apply Wasm.wp_iff_cons rfl
      rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
      simpa only [Wasm.wp_nil, List.take_zero, List.drop_zero, List.nil_append] using
        ih continued
  | @take index indices initial middle final child taken inBounds read call tail ih =>
      have countFound (values : List Wasm.Value) :
          ({ ownedEntry object check flags descriptor refCount kind marker count
              captureCount with values } : Wasm.Locals).get countIndex =
            some (.i32 count) := by rfl
      have addressFound (values : List Wasm.Value) :
          ({ ownedEntry object check flags descriptor refCount kind marker count
              captureCount with values } : Wasm.Locals).get addressIndex =
            some (.i32 object) := by rfl
      have inBounds' :
          ¬(object.toNat +
            (UInt32.ofNat
              (headerBytes + target.semanticSlotBytes * index)).toNat + 4 >
            initial.mem.pages * 65536) := by
        simpa [wasmPageBytes] using inBounds
      simp only [guardedReleaseChildrenProgram, guardedReleaseChildProgram,
        List.cons_append, List.nil_append, Wasm.wp_const_cons,
        Wasm.wp_localGet_cons, countFound, Wasm.wp_ltU_cons, if_pos taken]
      apply Wasm.wp_iff_cons rfl
      rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
      simp only [List.take_zero, List.drop_zero, List.nil_append,
        releaseChildProgram, Wasm.wp_localGet_cons,
        addressFound, Wasm.wp_load32_cons]
      rw [if_neg inBounds', read]
      simp only [Wasm.wp_const_cons]
      apply Wasm.wp_call_tw call
      intro next values completed
      rcases completed with ⟨rfl, rfl⟩
      simpa only [Wasm.wp_nil] using ih continued

/-- A bounded constructor frontier takes the nontrapping arm, executes its
guarded child chain, and returns the chain's exact final store. -/
theorem wp_constructorReleaseProgram
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {initial final : Wasm.Store host}
    {object check flags descriptor refCount kind marker count
      captureCount : UInt32}
    {decrementIndex : Nat}
    (withinLimit :
      ¬(UInt32.ofNat
        Fir.Wasm.Emit.ResidentRelease.constructorFieldLimit < count))
    (runs : GuardedReleaseChildrenRun env module decrementIndex object count
      (List.range Fir.Wasm.Emit.ResidentRelease.constructorFieldLimit)
      initial final)
    (returned : Q (.Return final [])) :
    Wasm.wp module (constructorReleaseProgram decrementIndex) Q initial
      (ownedEntry object check flags descriptor refCount kind marker count
        captureCount) env := by
  have countFound (values : List Wasm.Value) :
      ({ ownedEntry object check flags descriptor refCount kind marker count
          captureCount with values } : Wasm.Locals).get countIndex =
        some (.i32 count) := by rfl
  unfold constructorReleaseProgram
  simp only [Wasm.wp_const_cons, Wasm.wp_localGet_cons, countFound,
    Wasm.wp_ltU_cons, if_neg withinLimit]
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  apply runs.wp
  simpa only [List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_ret_cons, ownedEntry] using returned

/-- Execute the fixed constructor body from recursive-call evidence for only
the semantically live fields.  The theorem derives both the outer limit check
and the skipped physical suffix from the exact field count. -/
theorem wp_constructorReleaseProgram_of_children
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {initial final : Wasm.Store host}
    {object check flags descriptor refCount kind marker count
      captureCount : UInt32}
    {decrementIndex fieldCount : Nat}
    (runs : ReleaseChildrenRun env module decrementIndex object
      (List.range fieldCount) initial final)
    (fieldCountFits : fieldCount < UInt32.size)
    (withinLimit :
      fieldCount ≤ Fir.Wasm.Emit.ResidentRelease.constructorFieldLimit)
    (countEq : count = UInt32.ofNat fieldCount)
    (returned : Q (.Return final [])) :
    Wasm.wp module (constructorReleaseProgram decrementIndex) Q initial
      (ownedEntry object check flags descriptor refCount kind marker count
        captureCount) env := by
  apply wp_constructorReleaseProgram
  · intro tooMany
    rw [countEq, UInt32.lt_iff_toNat_lt,
      UInt32.toNat_ofNat_of_lt' (by decide),
      UInt32.toNat_ofNat_of_lt' fieldCountFits] at tooMany
    omega
  · exact runs.completeConstructorFrontier fieldCountFits withinLimit countEq
  · exact returned

/-- A constructor header selects exactly the supplied constructor body; the
closure and opaque branches remain unreachable. -/
theorem wp_ownedReleaseProgram_constructor
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {object check flags descriptor refCount kind marker count
      captureCount : UInt32}
    {constructorBody closureBody opaqueBody : Wasm.Program}
    (constructorKind : kind = ObjectKind.constructor.code)
    (constructorWP : Wasm.wp module constructorBody (TerminalPost Q) store
      (ownedEntry object check flags descriptor refCount kind marker count
        captureCount) env) :
    Wasm.wp module
      (ownedReleaseProgram constructorBody closureBody opaqueBody) Q store
      (ownedEntry object check flags descriptor refCount kind marker count
        captureCount) env := by
  have kindFound (values : List Wasm.Value) :
      ({ ownedEntry object check flags descriptor refCount kind marker count
          captureCount with values } : Wasm.Locals).get kindIndex =
        some (.i32 kind) := by rfl
  unfold ownedReleaseProgram
  simp only [Wasm.wp_localGet_cons, kindFound, Wasm.wp_const_cons,
    Wasm.wp_eq_cons, if_pos constructorKind]
  apply Wasm.wp_iff_cons rfl
  rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
  apply Wasm.wp.conseq _ constructorWP
  intro continuation terminal
  cases continuation <;> simp_all [TerminalPost]

/-- Constructor dispatch composed with the fixed-frontier child-release
implementation. -/
theorem wp_ownedReleaseProgram_constructorRelease
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {initial final : Wasm.Store host}
    {object check flags descriptor refCount kind marker count
      captureCount : UInt32}
    {decrementIndex : Nat} {closureBody opaqueBody : Wasm.Program}
    (constructorKind : kind = ObjectKind.constructor.code)
    (withinLimit :
      ¬(UInt32.ofNat
        Fir.Wasm.Emit.ResidentRelease.constructorFieldLimit < count))
    (runs : GuardedReleaseChildrenRun env module decrementIndex object count
      (List.range Fir.Wasm.Emit.ResidentRelease.constructorFieldLimit)
      initial final)
    (returned : Q (.Return final [])) :
    Wasm.wp module
      (ownedReleaseProgram (constructorReleaseProgram decrementIndex)
        closureBody opaqueBody) Q initial
      (ownedEntry object check flags descriptor refCount kind marker count
        captureCount) env := by
  apply wp_ownedReleaseProgram_constructor constructorKind
  apply wp_constructorReleaseProgram withinLimit runs
  simpa [TerminalPost] using returned

/-- Constructor dispatch from evidence for exactly the semantic fields.  This
is the target-level recursive interface consumed by the heap refinement: it
does not expose W7's padded 32-slot traversal. -/
theorem wp_ownedReleaseProgram_constructorRelease_of_children
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {initial final : Wasm.Store host}
    {object check flags descriptor refCount kind marker count
      captureCount : UInt32}
    {decrementIndex fieldCount : Nat}
    {closureBody opaqueBody : Wasm.Program}
    (constructorKind : kind = ObjectKind.constructor.code)
    (runs : ReleaseChildrenRun env module decrementIndex object
      (List.range fieldCount) initial final)
    (fieldCountFits : fieldCount < UInt32.size)
    (withinLimit :
      fieldCount ≤ Fir.Wasm.Emit.ResidentRelease.constructorFieldLimit)
    (countEq : count = UInt32.ofNat fieldCount)
    (returned : Q (.Return final [])) :
    Wasm.wp module
      (ownedReleaseProgram (constructorReleaseProgram decrementIndex)
        closureBody opaqueBody) Q initial
      (ownedEntry object check flags descriptor refCount kind marker count
        captureCount) env := by
  apply wp_ownedReleaseProgram_constructor constructorKind
  apply wp_constructorReleaseProgram_of_children runs fieldCountFits withinLimit
    countEq
  simpa [TerminalPost] using returned

/-- The complete last-reference body for a nonrecursive representation loads
its dispatch metadata, releases the header, and then returns without invoking
any recursive suffix. -/
theorem wp_lastReferenceProgram_leaf
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store releasedStore : Wasm.Store host}
    {object check flags descriptor refCount kind marker count
      captureCount : UInt32}
    {releaseHeaderIndex : Nat}
    {constructorBody closureBody opaqueBody : Wasm.Program}
    (kindInBounds :
      ¬(object.toNat + (UInt32.ofNat headerKindOffset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (kindRead : store.mem.read32
      (object + UInt32.ofNat headerKindOffset) = kind)
    (markerInBounds :
      ¬(object.toNat + (UInt32.ofNat headerAux0Offset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (markerRead : store.mem.read32
      (object + UInt32.ofNat headerAux0Offset) = marker)
    (countInBounds :
      ¬(object.toNat + (UInt32.ofNat headerAux1Offset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (countRead : store.mem.read32
      (object + UInt32.ofNat headerAux1Offset) = count)
    (captureInBounds :
      ¬(object.toNat + (UInt32.ofNat headerAux2Offset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (captureRead : store.mem.read32
      (object + UInt32.ofNat headerAux2Offset) = captureCount)
    (releaseRun : Wasm.TerminatesWith env module releaseHeaderIndex store
      [.i32 object]
      (fun final values => final = releasedStore ∧ values = []))
    (notConstructor : kind ≠ ObjectKind.constructor.code)
    (notClosure : kind ≠ ObjectKind.closure.code)
    (notOpaque : kind ≠ ObjectKind.opaque.code)
    (returned : Q (.Return releasedStore [])) :
    Wasm.wp module
      (lastReferenceProgram releaseHeaderIndex
        (ownedReleaseProgram constructorBody closureBody opaqueBody))
      Q store (countedLocals object check flags descriptor refCount) env := by
  apply wp_lastReferenceProgram kindInBounds kindRead markerInBounds markerRead
    countInBounds countRead captureInBounds captureRead releaseRun
  exact wp_ownedReleaseProgram_leaf notConstructor notClosure notOpaque returned

/-- Common resident-release prefix for an ordinary live object.  It validates
the complete header, selects the nonpersistent arm, loads the reference count,
and exposes the exact counted frame to the branch-specific proof. -/
theorem wp_liveReleaseProgram_ordinary
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {object check flags descriptor refCount : UInt32}
    {persistent lastReference : Wasm.Program}
    (aux3InBounds :
      ¬(object.toNat + (UInt32.ofNat headerAux3Offset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (aux3Read : store.mem.read32
      (object + UInt32.ofNat headerAux3Offset) = descriptor)
    (ordinary : flags &&& persistentFlag ≠ persistentFlag)
    (refCountInBounds :
      ¬(object.toNat + (UInt32.ofNat headerRefCountOffset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (refCountRead : store.mem.read32
      (object + UInt32.ofNat headerRefCountOffset) = refCount)
    (countBody : Wasm.wp module [
      .localGet refCountIndex,
      .const 0,
      .eq,
      .iff 0 0 [.unreachable] [
        .const 1,
        .localGet refCountIndex,
        .ltU,
        .iff 0 0 decrementAboveOneProgram lastReference]] (TerminalPost Q) store
          (countedLocals object check flags descriptor refCount) env) :
    Wasm.wp module (liveReleaseProgram persistent lastReference) Q store
      (liveEntry object check flags) env := by
  have entryAddress (values : List Wasm.Value) :
      ({ liveEntry object check flags with values } : Wasm.Locals).get
          addressIndex = some (.i32 object) := by rfl
  have descriptorSet (values : List Wasm.Value) :
      ({ liveEntry object check flags with
          values := .i32 descriptor :: values } : Wasm.Locals).set?
            descriptorIndex (.i32 descriptor) =
        some { probedLocals object check flags descriptor with
          values := .i32 descriptor :: values } := by rfl
  have entryValues : (liveEntry object check flags).values = [] := by rfl
  have probedAddress (values : List Wasm.Value) :
      ({ probedLocals object check flags descriptor with values } :
        Wasm.Locals).get addressIndex = some (.i32 object) := by rfl
  have probedFlags (values : List Wasm.Value) :
      ({ probedLocals object check flags descriptor with values } :
        Wasm.Locals).get flagsIndex = some (.i32 flags) := by rfl
  have refCountSet (values : List Wasm.Value) :
      ({ probedLocals object check flags descriptor with
          values := .i32 refCount :: values } : Wasm.Locals).set?
            refCountIndex (.i32 refCount) =
        some { countedLocals object check flags descriptor refCount with
          values := .i32 refCount :: values } := by rfl
  have probedValues :
      (probedLocals object check flags descriptor).values = [] := by rfl
  have aux3InBounds' :
      ¬(object.toNat + (UInt32.ofNat headerAux3Offset).toNat + 4 >
        store.mem.pages * 65536) := by
    simpa [wasmPageBytes] using aux3InBounds
  have refCountInBounds' :
      ¬(object.toNat + (UInt32.ofNat headerRefCountOffset).toNat + 4 >
        store.mem.pages * 65536) := by
    simpa [wasmPageBytes] using refCountInBounds
  have ordinary' : persistentFlag &&& flags ≠ persistentFlag := by
    simpa [UInt32.and_comm] using ordinary
  unfold liveReleaseProgram probeCompleteHeaderProgram
  simp only [List.cons_append, List.nil_append, Wasm.wp_localGet_cons,
    entryAddress, Wasm.wp_load32_cons]
  rw [if_neg aux3InBounds', aux3Read]
  simp only [Wasm.wp_localSet_cons, descriptorSet, entryValues]
  change Wasm.wp module [
    .localGet flagsIndex,
    .const persistentFlag,
    .and,
    .const persistentFlag,
    .eq,
    .iff 0 0 persistent (ordinaryReleaseProgram lastReference)] Q store
      (probedLocals object check flags descriptor) env
  simp only [Wasm.wp_localGet_cons, probedFlags, Wasm.wp_const_cons,
    Wasm.wp_and_cons, Wasm.wp_eq_cons]
  rw [if_neg ordinary']
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  simp only [List.take_zero, List.drop_zero, List.nil_append,
    ordinaryReleaseProgram, Wasm.wp_localGet_cons, probedAddress,
    Wasm.wp_load32_cons]
  rw [if_neg refCountInBounds', refCountRead]
  simp only [Wasm.wp_localSet_cons, refCountSet, probedValues]
  apply Wasm.wp.conseq _ countBody
  intro continuation terminal
  cases continuation <;> simp_all [TerminalPost]

/-- The early ordinary shared-reference arm probes the terminal header word,
loads only flags and the reference count, writes exactly `refCount - 1`, and
returns.  Neither cold branch is interpreted. -/
theorem wp_liveReleaseProgram_aboveOne
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {object check flags descriptor refCount : UInt32}
    {persistent lastReference : Wasm.Program}
    (aux3InBounds :
      ¬(object.toNat + (UInt32.ofNat headerAux3Offset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (aux3Read : store.mem.read32
      (object + UInt32.ofNat headerAux3Offset) = descriptor)
    (ordinary : flags &&& persistentFlag ≠ persistentFlag)
    (refCountInBounds :
      ¬(object.toNat + (UInt32.ofNat headerRefCountOffset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (refCountRead : store.mem.read32
      (object + UInt32.ofNat headerRefCountOffset) = refCount)
    (nonzero : refCount ≠ 0)
    (oneLt : (1 : UInt32) < refCount)
    (returned : Q (.Return
      (ResidentMemoryRel.write32Store store
        (object + UInt32.ofNat headerRefCountOffset) (refCount - 1)) [])) :
    Wasm.wp module (liveReleaseProgram persistent lastReference) Q store
      (liveEntry object check flags) env := by
  have countedAddress (values : List Wasm.Value) :
      ({ countedLocals object check flags descriptor refCount with values } :
        Wasm.Locals).get addressIndex = some (.i32 object) := by rfl
  have countedRefCount (values : List Wasm.Value) :
      ({ countedLocals object check flags descriptor refCount with values } :
        Wasm.Locals).get refCountIndex = some (.i32 refCount) := by rfl
  have refCountInBounds' :
      ¬(object.toNat + (UInt32.ofNat headerRefCountOffset).toNat + 4 >
        store.mem.pages * 65536) := by
    simpa [wasmPageBytes] using refCountInBounds
  apply wp_liveReleaseProgram_ordinary aux3InBounds aux3Read ordinary
    refCountInBounds refCountRead
  simp only [Wasm.wp_localGet_cons, countedRefCount, Wasm.wp_const_cons,
    Wasm.wp_eq_cons, if_neg nonzero]
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  simp only [List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_const_cons, Wasm.wp_localGet_cons, countedRefCount,
    Wasm.wp_ltU_cons, if_pos oneLt]
  apply Wasm.wp_iff_cons rfl
  rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
  unfold decrementAboveOneProgram
  simp only [List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, countedAddress, countedRefCount, Wasm.wp_const_cons,
    Wasm.wp_sub_cons, Wasm.wp_store32_cons, refCountInBounds',
    Wasm.wp_ret_cons, TerminalPost]
  exact returned

/-- An ordinary live header whose physical reference count is zero follows
the resident helper's explicit underflow trap, without entering either the
shared-decrement or last-reference body. -/
theorem wp_liveReleaseProgram_underflow
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {object check flags descriptor refCount : UInt32}
    {persistent lastReference : Wasm.Program}
    (aux3InBounds :
      ¬(object.toNat + (UInt32.ofNat headerAux3Offset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (aux3Read : store.mem.read32
      (object + UInt32.ofNat headerAux3Offset) = descriptor)
    (ordinary : flags &&& persistentFlag ≠ persistentFlag)
    (refCountInBounds :
      ¬(object.toNat + (UInt32.ofNat headerRefCountOffset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (refCountRead : store.mem.read32
      (object + UInt32.ofNat headerRefCountOffset) = refCount)
    (zero : refCount = 0)
    (trapped : Q (.Trap store "unreachable")) :
    Wasm.wp module (liveReleaseProgram persistent lastReference) Q store
      (liveEntry object check flags) env := by
  have countedRefCount (values : List Wasm.Value) :
      ({ countedLocals object check flags descriptor refCount with values } :
        Wasm.Locals).get refCountIndex = some (.i32 refCount) := by rfl
  apply wp_liveReleaseProgram_ordinary aux3InBounds aux3Read ordinary
    refCountInBounds refCountRead
  simp only [Wasm.wp_localGet_cons, countedRefCount, Wasm.wp_const_cons,
    Wasm.wp_eq_cons]
  rw [if_pos zero]
  apply Wasm.wp_iff_cons rfl
  rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
  simpa only [List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_unreachable_cons, TerminalPost] using trapped

/-- An ordinary live header with reference count one selects exactly the
caller-supplied last-reference body.  The common probe and count load are
discharged here; recursive ownership reasoning starts from the counted frame. -/
theorem wp_liveReleaseProgram_lastReference
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {object check flags descriptor refCount : UInt32}
    {persistent lastReference : Wasm.Program}
    (aux3InBounds :
      ¬(object.toNat + (UInt32.ofNat headerAux3Offset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (aux3Read : store.mem.read32
      (object + UInt32.ofNat headerAux3Offset) = descriptor)
    (ordinary : flags &&& persistentFlag ≠ persistentFlag)
    (refCountInBounds :
      ¬(object.toNat + (UInt32.ofNat headerRefCountOffset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (refCountRead : store.mem.read32
      (object + UInt32.ofNat headerRefCountOffset) = refCount)
    (one : refCount = 1)
    (lastBody : Wasm.wp module lastReference (TerminalPost Q) store
      (countedLocals object check flags descriptor refCount) env) :
    Wasm.wp module (liveReleaseProgram persistent lastReference) Q store
      (liveEntry object check flags) env := by
  have countedRefCount (values : List Wasm.Value) :
      ({ countedLocals object check flags descriptor refCount with values } :
        Wasm.Locals).get refCountIndex = some (.i32 refCount) := by rfl
  have nonzero : refCount ≠ 0 := by
    rw [one]
    decide
  have notAboveOne : ¬(1 : UInt32) < refCount := by
    rw [one]
    decide
  apply wp_liveReleaseProgram_ordinary aux3InBounds aux3Read ordinary
    refCountInBounds refCountRead
  simp only [Wasm.wp_localGet_cons, countedRefCount, Wasm.wp_const_cons,
    Wasm.wp_eq_cons, if_neg nonzero]
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  simp only [List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_const_cons, Wasm.wp_localGet_cons, countedRefCount,
    Wasm.wp_ltU_cons, if_neg notAboveOne]
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  apply Wasm.wp.conseq _ lastBody
  intro continuation terminal
  cases continuation <;> simp_all [TerminalPost]

/-- An ordinary persistent allocation returns without changing memory.  The
only nontrivial subcase in W7's branch is the promoted-Nat encoding, excluded
here by its two exact physical discriminator lanes. -/
theorem wp_persistentReleaseProgram_notPromoted
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {object check flags descriptor kind marker : UInt32}
    (kindInBounds :
      ¬(object.toNat + (UInt32.ofNat headerKindOffset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (kindRead : store.mem.read32
      (object + UInt32.ofNat headerKindOffset) = kind)
    (markerInBounds :
      ¬(object.toNat + (UInt32.ofNat headerAux0Offset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (markerRead : store.mem.read32
      (object + UInt32.ofNat headerAux0Offset) = marker)
    (notPromoted :
      kind ≠ ObjectKind.natural.code ∨ marker ≠ promotedTagMarker)
    (returned : Q (.Return store [])) :
    Wasm.wp module persistentReleaseProgram Q store
      (probedLocals object check flags descriptor) env := by
  have probedAddress (values : List Wasm.Value) :
      ({ probedLocals object check flags descriptor with values } :
        Wasm.Locals).get addressIndex = some (.i32 object) := by rfl
  have kindSet (values : List Wasm.Value) :
      ({ probedLocals object check flags descriptor with
          values := .i32 kind :: values } : Wasm.Locals).set?
            kindIndex (.i32 kind) =
        some { persistentKindLocals object check flags descriptor kind with
          values := .i32 kind :: values } := by rfl
  have probedValues :
      (probedLocals object check flags descriptor).values = [] := by rfl
  have kindAddress (values : List Wasm.Value) :
      ({ persistentKindLocals object check flags descriptor kind with values } :
        Wasm.Locals).get addressIndex = some (.i32 object) := by rfl
  have markerSet (values : List Wasm.Value) :
      ({ persistentKindLocals object check flags descriptor kind with
          values := .i32 marker :: values } : Wasm.Locals).set?
            markerIndex (.i32 marker) =
        some { persistentMarkerLocals object check flags descriptor kind marker with
          values := .i32 marker :: values } := by rfl
  have kindValues :
      (persistentKindLocals object check flags descriptor kind).values = [] := by
    rfl
  have markerAddress (values : List Wasm.Value) :
      ({ persistentMarkerLocals object check flags descriptor kind marker with values } :
        Wasm.Locals).get addressIndex = some (.i32 object) := by rfl
  have markerKind (values : List Wasm.Value) :
      ({ persistentMarkerLocals object check flags descriptor kind marker with values } :
        Wasm.Locals).get kindIndex = some (.i32 kind) := by rfl
  have markerValues :
      (persistentMarkerLocals object check flags descriptor kind marker).values = [] := by
    rfl
  have kindInBounds' :
      ¬(object.toNat + (UInt32.ofNat headerKindOffset).toNat + 4 >
        store.mem.pages * 65536) := by
    simpa [wasmPageBytes] using kindInBounds
  have markerInBounds' :
      ¬(object.toNat + (UInt32.ofNat headerAux0Offset).toNat + 4 >
        store.mem.pages * 65536) := by
    simpa [wasmPageBytes] using markerInBounds
  unfold persistentReleaseProgram
  simp only [Wasm.wp_localGet_cons, probedAddress, Wasm.wp_load32_cons]
  rw [if_neg kindInBounds', kindRead]
  simp only [Wasm.wp_localSet_cons, kindSet, probedValues,
    Wasm.wp_localGet_cons, kindAddress, Wasm.wp_load32_cons]
  rw [if_neg markerInBounds', markerRead]
  simp only [markerSet, markerKind, Wasm.wp_const_cons, Wasm.wp_eq_cons]
  by_cases kindNatural : kind = ObjectKind.natural.code
  · rw [if_pos kindNatural]
    apply Wasm.wp_iff_cons rfl
    rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
    simp only [List.take_zero, List.drop_zero, List.nil_append,
      Wasm.wp_localGet_cons, markerAddress, Wasm.wp_load32_cons]
    rw [if_neg markerInBounds', markerRead]
    simp only [Wasm.wp_const_cons, Wasm.wp_eq_cons]
    have markerNot : marker ≠ promotedTagMarker := by
      rcases notPromoted with kindNot | markerNot
      · exact False.elim (kindNot kindNatural)
      · exact markerNot
    rw [if_neg markerNot]
    apply Wasm.wp_iff_cons rfl
    rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
    simpa only [List.take_zero, List.drop_zero, List.nil_append,
      Wasm.wp_ret_cons, markerValues] using returned
  · rw [if_neg kindNatural]
    apply Wasm.wp_iff_cons rfl
    rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
    simpa only [List.take_zero, List.drop_zero, List.nil_append,
      Wasm.wp_ret_cons, markerValues] using returned

/-- The live-object dispatcher selects W7's persistent branch, after retaining
the same terminal-header probe used by the ordinary path. -/
theorem wp_liveReleaseProgram_persistent
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {object check flags descriptor kind marker : UInt32}
    {lastReference : Wasm.Program}
    (aux3InBounds :
      ¬(object.toNat + (UInt32.ofNat headerAux3Offset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (aux3Read : store.mem.read32
      (object + UInt32.ofNat headerAux3Offset) = descriptor)
    (persistent : flags &&& persistentFlag = persistentFlag)
    (kindInBounds :
      ¬(object.toNat + (UInt32.ofNat headerKindOffset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (kindRead : store.mem.read32
      (object + UInt32.ofNat headerKindOffset) = kind)
    (markerInBounds :
      ¬(object.toNat + (UInt32.ofNat headerAux0Offset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (markerRead : store.mem.read32
      (object + UInt32.ofNat headerAux0Offset) = marker)
    (notPromoted :
      kind ≠ ObjectKind.natural.code ∨ marker ≠ promotedTagMarker)
    (returned : Q (.Return store [])) :
    Wasm.wp module
      (liveReleaseProgram persistentReleaseProgram lastReference) Q store
      (liveEntry object check flags) env := by
  have entryAddress (values : List Wasm.Value) :
      ({ liveEntry object check flags with values } : Wasm.Locals).get
          addressIndex = some (.i32 object) := by rfl
  have descriptorSet (values : List Wasm.Value) :
      ({ liveEntry object check flags with
          values := .i32 descriptor :: values } : Wasm.Locals).set?
            descriptorIndex (.i32 descriptor) =
        some { probedLocals object check flags descriptor with
          values := .i32 descriptor :: values } := by rfl
  have entryValues : (liveEntry object check flags).values = [] := by rfl
  have probedFlags (values : List Wasm.Value) :
      ({ probedLocals object check flags descriptor with values } :
        Wasm.Locals).get flagsIndex = some (.i32 flags) := by rfl
  have aux3InBounds' :
      ¬(object.toNat + (UInt32.ofNat headerAux3Offset).toNat + 4 >
        store.mem.pages * 65536) := by
    simpa [wasmPageBytes] using aux3InBounds
  have persistent' : persistentFlag &&& flags = persistentFlag := by
    simpa [UInt32.and_comm] using persistent
  unfold liveReleaseProgram probeCompleteHeaderProgram
  simp only [List.cons_append, List.nil_append, Wasm.wp_localGet_cons,
    entryAddress, Wasm.wp_load32_cons]
  rw [if_neg aux3InBounds', aux3Read]
  simp only [Wasm.wp_localSet_cons, descriptorSet, entryValues]
  change Wasm.wp module [
    .localGet flagsIndex,
    .const persistentFlag,
    .and,
    .const persistentFlag,
    .eq,
    .iff 0 0 persistentReleaseProgram
      (ordinaryReleaseProgram lastReference)] Q store
        (probedLocals object check flags descriptor) env
  simp only [Wasm.wp_localGet_cons, probedFlags, Wasm.wp_const_cons,
    Wasm.wp_and_cons, Wasm.wp_eq_cons]
  rw [persistent']
  simp only [if_true]
  apply Wasm.wp_iff_cons rfl
  rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
  apply wp_persistentReleaseProgram_notPromoted kindInBounds kindRead
    markerInBounds markerRead notPromoted
  exact returned

/-- Reusable entry theorem for every well-formed live heap object.  It
discharges the tagged/null/alignment gates and the raw-flags liveness check,
then hands the exact live-object frame and caller postcondition to a
branch-specific proof. -/
theorem wp_decrementOnceProgram_live
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {object check flags : UInt32}
    {persistent lastReference : Wasm.Program}
    (taggedClear : (1 : UInt32) &&& object = 0)
    (objectNonzero : object ≠ 0)
    (alignmentClear :
      UInt32.ofNat (target.heapAlignment - 1) &&& object = 0)
    (flagsInBounds :
      ¬(object.toNat + (UInt32.ofNat headerFlagsOffset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (flagsRead : store.mem.read32
      (object + UInt32.ofNat headerFlagsOffset) = flags)
    (liveSet : liveFlag &&& flags = liveFlag)
    (liveBody : Wasm.wp module
      (liveReleaseProgram persistent lastReference) (TerminalPost Q) store
      (liveEntry object check flags) env) :
    Wasm.wp module (decrementOnceProgram persistent lastReference) Q store
      (decrementEntry object check) env := by
  have entryObject (values : List Wasm.Value) :
      ({ decrementEntry object check with values } : Wasm.Locals).get
        objectIndex = some (.i32 object) := by rfl
  have addressSet (values : List Wasm.Value) :
      ({ decrementEntry object check with
          values := .i32 object :: values } : Wasm.Locals).set?
            addressIndex (.i32 object) =
        some { liveEntry object check 0 with
          values := .i32 object :: values } := by rfl
  have entryValues : (decrementEntry object check).values = [] := by rfl
  have zeroFlagsAddressBare :
      ({ params := (liveEntry object check 0).params
         locals := (liveEntry object check 0).locals } : Wasm.Locals).get
        addressIndex = some (.i32 object) := by rfl
  have flagsSet (values : List Wasm.Value) :
      ({ liveEntry object check 0 with
          values := .i32 flags :: values } : Wasm.Locals).set?
            flagsIndex (.i32 flags) =
        some { liveEntry object check flags with
          values := .i32 flags :: values } := by rfl
  have liveFlagsBare :
      ({ params := (liveEntry object check flags).params
         locals := (liveEntry object check flags).locals } : Wasm.Locals).get
        flagsIndex = some (.i32 flags) := by rfl
  have flagsInBounds' :
      ¬(object.toNat + (UInt32.ofNat headerFlagsOffset).toNat + 4 >
        store.mem.pages * 65536) := by
    simpa [wasmPageBytes] using flagsInBounds
  unfold decrementOnceProgram
  simp only [Wasm.wp_localGet_cons, entryObject, Wasm.wp_const_cons,
    Wasm.wp_and_cons]
  rw [taggedClear]
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  simp only [List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, entryObject, Wasm.wp_const_cons, Wasm.wp_eq_cons]
  rw [if_neg objectNonzero]
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  simp only [List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, entryObject, Wasm.wp_const_cons, Wasm.wp_and_cons]
  rw [alignmentClear]
  simp only [Wasm.wp_eq_cons, if_true]
  apply Wasm.wp_iff_cons rfl
  rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
  unfold alignedReleaseProgram
  simp only [List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, entryObject, Wasm.wp_const_cons, Wasm.wp_add_cons,
    UInt32.zero_add, Wasm.wp_localSet_cons, addressSet, entryValues,
    zeroFlagsAddressBare, Wasm.wp_load32_cons]
  rw [if_neg flagsInBounds', flagsRead]
  simp only [flagsSet]
  simp only [liveFlagsBare, Wasm.wp_const_cons, Wasm.wp_and_cons]
  rw [liveSet]
  simp only [Wasm.wp_eq_cons, if_true]
  apply Wasm.wp_iff_cons rfl
  rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
  apply Wasm.wp.conseq _ liveBody
  intro continuation terminal
  cases continuation <;> simp_all [TerminalPost]

/-- Terminal-return specialization of the common live-entry theorem.  Most
semantic refinements expose an exact final store first and then discharge the
caller's postcondition at that result. -/
theorem wp_decrementOnceProgram_live_return
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {resultStore : Wasm.Store host} {results : List Wasm.Value}
    {object check flags : UInt32}
    {persistent lastReference : Wasm.Program}
    (taggedClear : (1 : UInt32) &&& object = 0)
    (objectNonzero : object ≠ 0)
    (alignmentClear :
      UInt32.ofNat (target.heapAlignment - 1) &&& object = 0)
    (flagsInBounds :
      ¬(object.toNat + (UInt32.ofNat headerFlagsOffset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (flagsRead : store.mem.read32
      (object + UInt32.ofNat headerFlagsOffset) = flags)
    (liveSet : liveFlag &&& flags = liveFlag)
    (liveBody : Wasm.wp module
      (liveReleaseProgram persistent lastReference)
      (fun continuation => continuation = .Return resultStore results) store
      (liveEntry object check flags) env)
    (returned : Q (.Return resultStore results)) :
    Wasm.wp module (decrementOnceProgram persistent lastReference) Q store
      (decrementEntry object check) env := by
  apply wp_decrementOnceProgram_live taggedClear objectNonzero alignmentClear
    flagsInBounds flagsRead liveSet
  apply Wasm.wp.conseq _ liveBody
  intro continuation terminal
  subst continuation
  simpa [TerminalPost] using returned

/-- Complete function-entry execution for a represented persistent allocation.
It is an exact no-op on the resident memory and returns normally. -/
theorem wp_decrementOnceProgram_persistent
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {object check flags descriptor kind marker : UInt32}
    {lastReference : Wasm.Program}
    (taggedClear : (1 : UInt32) &&& object = 0)
    (objectNonzero : object ≠ 0)
    (alignmentClear :
      UInt32.ofNat (target.heapAlignment - 1) &&& object = 0)
    (flagsInBounds :
      ¬(object.toNat + (UInt32.ofNat headerFlagsOffset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (flagsRead : store.mem.read32
      (object + UInt32.ofNat headerFlagsOffset) = flags)
    (liveSet : liveFlag &&& flags = liveFlag)
    (aux3InBounds :
      ¬(object.toNat + (UInt32.ofNat headerAux3Offset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (aux3Read : store.mem.read32
      (object + UInt32.ofNat headerAux3Offset) = descriptor)
    (persistent : flags &&& persistentFlag = persistentFlag)
    (kindInBounds :
      ¬(object.toNat + (UInt32.ofNat headerKindOffset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (kindRead : store.mem.read32
      (object + UInt32.ofNat headerKindOffset) = kind)
    (markerInBounds :
      ¬(object.toNat + (UInt32.ofNat headerAux0Offset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (markerRead : store.mem.read32
      (object + UInt32.ofNat headerAux0Offset) = marker)
    (notPromoted :
      kind ≠ ObjectKind.natural.code ∨ marker ≠ promotedTagMarker)
    (returned : Q (.Return store [])) :
    Wasm.wp module
      (decrementOnceProgram persistentReleaseProgram lastReference) Q store
      (decrementEntry object check) env := by
  apply wp_decrementOnceProgram_live_return taggedClear objectNonzero
    alignmentClear flagsInBounds flagsRead liveSet _ returned
  apply wp_liveReleaseProgram_persistent aux3InBounds aux3Read persistent
    kindInBounds kindRead markerInBounds markerRead notPromoted
  rfl

/-- A tagged immediate reaches the public helper's checked no-op gate before
any address arithmetic or memory access. -/
theorem wp_decrementOnceProgram_tagged
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {object check : UInt32} {persistent lastReference : Wasm.Program}
    (tagged : (1 : UInt32) &&& object ≠ 0)
    (terminal :
      if check ≠ 0 then Q (.Return store [])
      else Q (.Trap store "unreachable")) :
    Wasm.wp module (decrementOnceProgram persistent lastReference) Q store
      (decrementEntry object check) env := by
  have entryObject (values : List Wasm.Value) :
      ({ decrementEntry object check with values } : Wasm.Locals).get
        objectIndex = some (.i32 object) := by rfl
  have entryCheck (values : List Wasm.Value) :
      ({ decrementEntry object check with values } : Wasm.Locals).get
        checkIndex = some (.i32 check) := by rfl
  have entryValues : (decrementEntry object check).values = [] := by rfl
  unfold decrementOnceProgram
  simp only [Wasm.wp_localGet_cons, entryObject, Wasm.wp_const_cons,
    Wasm.wp_and_cons]
  apply Wasm.wp_iff_cons rfl
  rw [if_pos tagged]
  unfold checkedNoopProgram
  simp only [List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, entryCheck]
  by_cases checked : check ≠ 0
  · apply Wasm.wp_iff_cons rfl
    rw [if_pos checked]
    simpa only [List.take_zero, List.drop_zero, List.nil_append,
      Wasm.wp_ret_cons, entryValues, if_pos checked] using terminal
  · apply Wasm.wp_iff_cons rfl
    rw [if_neg checked]
    simpa only [List.take_zero, List.drop_zero, List.nil_append,
      Wasm.wp_unreachable_cons, if_neg checked] using terminal

/-- The erased physical zero sentinel uses the same checked no-op gate, after
the tagged test has rejected it.  It likewise performs no memory access. -/
theorem wp_decrementOnceProgram_sentinel
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {check : UInt32} {persistent lastReference : Wasm.Program}
    (terminal :
      if check ≠ 0 then Q (.Return store [])
      else Q (.Trap store "unreachable")) :
    Wasm.wp module (decrementOnceProgram persistent lastReference) Q store
      (decrementEntry 0 check) env := by
  have entryObject (values : List Wasm.Value) :
      ({ decrementEntry 0 check with values } : Wasm.Locals).get
        objectIndex = some (.i32 0) := by rfl
  have entryCheck (values : List Wasm.Value) :
      ({ decrementEntry 0 check with values } : Wasm.Locals).get
        checkIndex = some (.i32 check) := by rfl
  have entryValues : (decrementEntry 0 check).values = [] := by rfl
  unfold decrementOnceProgram
  simp only [Wasm.wp_localGet_cons, entryObject, Wasm.wp_const_cons,
    Wasm.wp_and_cons]
  rw [show (1 : UInt32) &&& 0 = 0 by decide]
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  simp only [List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, entryObject, Wasm.wp_const_cons, Wasm.wp_eq_cons,
    if_true]
  apply Wasm.wp_iff_cons rfl
  rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
  unfold checkedNoopProgram
  simp only [List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, entryCheck]
  by_cases checked : check ≠ 0
  · apply Wasm.wp_iff_cons rfl
    rw [if_pos checked]
    simpa only [List.take_zero, List.drop_zero, List.nil_append,
      Wasm.wp_ret_cons, entryValues, if_pos checked] using terminal
  · apply Wasm.wp_iff_cons rfl
    rw [if_neg checked]
    simpa only [List.take_zero, List.drop_zero, List.nil_append,
      Wasm.wp_unreachable_cons, if_neg checked] using terminal

/-- A nonzero untagged but misaligned word traps at admission, before W7 loads
the flags lane. -/
theorem wp_decrementOnceProgram_misaligned
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {object check : UInt32} {persistent lastReference : Wasm.Program}
    (taggedClear : (1 : UInt32) &&& object = 0)
    (objectNonzero : object ≠ 0)
    (misaligned :
      UInt32.ofNat (target.heapAlignment - 1) &&& object ≠ 0)
    (trapped : Q (.Trap store "unreachable")) :
    Wasm.wp module (decrementOnceProgram persistent lastReference) Q store
      (decrementEntry object check) env := by
  have entryObject (values : List Wasm.Value) :
      ({ decrementEntry object check with values } : Wasm.Locals).get
        objectIndex = some (.i32 object) := by rfl
  unfold decrementOnceProgram
  simp only [Wasm.wp_localGet_cons, entryObject, Wasm.wp_const_cons,
    Wasm.wp_and_cons]
  rw [taggedClear]
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  simp only [List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, entryObject, Wasm.wp_const_cons, Wasm.wp_eq_cons]
  rw [if_neg objectNonzero]
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  simp only [List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, entryObject, Wasm.wp_const_cons, Wasm.wp_and_cons]
  simp only [Wasm.wp_eq_cons]
  rw [if_neg misaligned]
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  simpa only [List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_unreachable_cons] using trapped

/-- A well-addressed but nonlive header traps at the liveness gate after the
single flags load.  No terminal-header probe or ownership branch is entered. -/
theorem wp_decrementOnceProgram_notLive
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {object check flags : UInt32}
    {persistent lastReference : Wasm.Program}
    (taggedClear : (1 : UInt32) &&& object = 0)
    (objectNonzero : object ≠ 0)
    (alignmentClear :
      UInt32.ofNat (target.heapAlignment - 1) &&& object = 0)
    (flagsInBounds :
      ¬(object.toNat + (UInt32.ofNat headerFlagsOffset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (flagsRead : store.mem.read32
      (object + UInt32.ofNat headerFlagsOffset) = flags)
    (notLive : liveFlag &&& flags ≠ liveFlag)
    (trapped : Q (.Trap store "unreachable")) :
    Wasm.wp module (decrementOnceProgram persistent lastReference) Q store
      (decrementEntry object check) env := by
  have entryObject (values : List Wasm.Value) :
      ({ decrementEntry object check with values } : Wasm.Locals).get
        objectIndex = some (.i32 object) := by rfl
  have addressSet (values : List Wasm.Value) :
      ({ decrementEntry object check with
          values := .i32 object :: values } : Wasm.Locals).set?
            addressIndex (.i32 object) =
        some { liveEntry object check 0 with
          values := .i32 object :: values } := by rfl
  have entryValues : (decrementEntry object check).values = [] := by rfl
  have zeroFlagsAddressBare :
      ({ params := (liveEntry object check 0).params
         locals := (liveEntry object check 0).locals } : Wasm.Locals).get
        addressIndex = some (.i32 object) := by rfl
  have flagsSet (values : List Wasm.Value) :
      ({ liveEntry object check 0 with
          values := .i32 flags :: values } : Wasm.Locals).set?
            flagsIndex (.i32 flags) =
        some { liveEntry object check flags with
          values := .i32 flags :: values } := by rfl
  have liveFlagsBare :
      ({ params := (liveEntry object check flags).params
         locals := (liveEntry object check flags).locals } : Wasm.Locals).get
        flagsIndex = some (.i32 flags) := by rfl
  have flagsInBounds' :
      ¬(object.toNat + (UInt32.ofNat headerFlagsOffset).toNat + 4 >
        store.mem.pages * 65536) := by
    simpa [wasmPageBytes] using flagsInBounds
  unfold decrementOnceProgram
  simp only [Wasm.wp_localGet_cons, entryObject, Wasm.wp_const_cons,
    Wasm.wp_and_cons]
  rw [taggedClear]
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  simp only [List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, entryObject, Wasm.wp_const_cons, Wasm.wp_eq_cons]
  rw [if_neg objectNonzero]
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  simp only [List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, entryObject, Wasm.wp_const_cons, Wasm.wp_and_cons]
  rw [alignmentClear]
  simp only [Wasm.wp_eq_cons, if_true]
  apply Wasm.wp_iff_cons rfl
  rw [if_pos (by decide : (1 : UInt32) ≠ 0)]
  unfold alignedReleaseProgram
  simp only [List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_localGet_cons, entryObject, Wasm.wp_const_cons, Wasm.wp_add_cons,
    UInt32.zero_add, Wasm.wp_localSet_cons, addressSet, entryValues,
    zeroFlagsAddressBare, Wasm.wp_load32_cons]
  rw [if_neg flagsInBounds', flagsRead]
  simp only [flagsSet, liveFlagsBare, Wasm.wp_const_cons, Wasm.wp_and_cons,
    Wasm.wp_eq_cons]
  rw [if_neg notLive]
  apply Wasm.wp_iff_cons rfl
  rw [if_neg (by decide : ¬(0 : UInt32) ≠ 0)]
  simpa only [List.take_zero, List.drop_zero, List.nil_append,
    Wasm.wp_unreachable_cons] using trapped

/-- The complete public `fir_dec_once` hot path reaches the same exact
single-store result.  This includes the tagged/null/alignment gates, raw flags
load, and liveness test that precede the live-arm theorem above. -/
theorem wp_decrementOnceProgram_aboveOne
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {object check flags descriptor refCount : UInt32}
    {persistent lastReference : Wasm.Program}
    (taggedClear : (1 : UInt32) &&& object = 0)
    (objectNonzero : object ≠ 0)
    (alignmentClear :
      UInt32.ofNat (target.heapAlignment - 1) &&& object = 0)
    (flagsInBounds :
      ¬(object.toNat + (UInt32.ofNat headerFlagsOffset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (flagsRead : store.mem.read32
      (object + UInt32.ofNat headerFlagsOffset) = flags)
    (liveSet : liveFlag &&& flags = liveFlag)
    (aux3InBounds :
      ¬(object.toNat + (UInt32.ofNat headerAux3Offset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (aux3Read : store.mem.read32
      (object + UInt32.ofNat headerAux3Offset) = descriptor)
    (ordinary : flags &&& persistentFlag ≠ persistentFlag)
    (refCountInBounds :
      ¬(object.toNat + (UInt32.ofNat headerRefCountOffset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (refCountRead : store.mem.read32
      (object + UInt32.ofNat headerRefCountOffset) = refCount)
    (nonzero : refCount ≠ 0)
    (oneLt : (1 : UInt32) < refCount)
    (returned : Q (.Return
      (ResidentMemoryRel.write32Store store
        (object + UInt32.ofNat headerRefCountOffset) (refCount - 1)) [])) :
    Wasm.wp module (decrementOnceProgram persistent lastReference) Q store
      (decrementEntry object check) env := by
  apply wp_decrementOnceProgram_live_return taggedClear objectNonzero
    alignmentClear flagsInBounds flagsRead liveSet _ returned
  apply wp_liveReleaseProgram_aboveOne aux3InBounds aux3Read ordinary
    refCountInBounds refCountRead nonzero oneLt
  rfl

/-- Complete entry-to-trap execution for an ordinary live object whose
physical reference count is already zero.  The helper detects the malformed
ownership state before entering the last-reference body. -/
theorem wp_decrementOnceProgram_underflow
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {object check flags descriptor refCount : UInt32}
    {persistent lastReference : Wasm.Program}
    (taggedClear : (1 : UInt32) &&& object = 0)
    (objectNonzero : object ≠ 0)
    (alignmentClear :
      UInt32.ofNat (target.heapAlignment - 1) &&& object = 0)
    (flagsInBounds :
      ¬(object.toNat + (UInt32.ofNat headerFlagsOffset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (flagsRead : store.mem.read32
      (object + UInt32.ofNat headerFlagsOffset) = flags)
    (liveSet : liveFlag &&& flags = liveFlag)
    (aux3InBounds :
      ¬(object.toNat + (UInt32.ofNat headerAux3Offset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (aux3Read : store.mem.read32
      (object + UInt32.ofNat headerAux3Offset) = descriptor)
    (ordinary : flags &&& persistentFlag ≠ persistentFlag)
    (refCountInBounds :
      ¬(object.toNat + (UInt32.ofNat headerRefCountOffset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (refCountRead : store.mem.read32
      (object + UInt32.ofNat headerRefCountOffset) = refCount)
    (zero : refCount = 0)
    (trapped : Q (.Trap store "unreachable")) :
    Wasm.wp module (decrementOnceProgram persistent lastReference) Q store
      (decrementEntry object check) env := by
  apply wp_decrementOnceProgram_live taggedClear objectNonzero alignmentClear
    flagsInBounds flagsRead liveSet
  apply wp_liveReleaseProgram_underflow aux3InBounds aux3Read ordinary
    refCountInBounds refCountRead zero
  simpa [TerminalPost] using trapped

/-- Complete entry theorem for the ordinary last-reference branch.  All
public admission and common-header checks are factored away; the remaining
obligation is the exact last-reference program from the counted frame. -/
theorem wp_decrementOnceProgram_lastReference
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {object check flags descriptor refCount : UInt32}
    {persistent lastReference : Wasm.Program}
    (taggedClear : (1 : UInt32) &&& object = 0)
    (objectNonzero : object ≠ 0)
    (alignmentClear :
      UInt32.ofNat (target.heapAlignment - 1) &&& object = 0)
    (flagsInBounds :
      ¬(object.toNat + (UInt32.ofNat headerFlagsOffset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (flagsRead : store.mem.read32
      (object + UInt32.ofNat headerFlagsOffset) = flags)
    (liveSet : liveFlag &&& flags = liveFlag)
    (aux3InBounds :
      ¬(object.toNat + (UInt32.ofNat headerAux3Offset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (aux3Read : store.mem.read32
      (object + UInt32.ofNat headerAux3Offset) = descriptor)
    (ordinary : flags &&& persistentFlag ≠ persistentFlag)
    (refCountInBounds :
      ¬(object.toNat + (UInt32.ofNat headerRefCountOffset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (refCountRead : store.mem.read32
      (object + UInt32.ofNat headerRefCountOffset) = refCount)
    (one : refCount = 1)
    (lastBody : Wasm.wp module lastReference (TerminalPost Q) store
      (countedLocals object check flags descriptor refCount) env) :
    Wasm.wp module (decrementOnceProgram persistent lastReference) Q store
      (decrementEntry object check) env := by
  apply wp_decrementOnceProgram_live taggedClear objectNonzero alignmentClear
    flagsInBounds flagsRead liveSet
  apply wp_liveReleaseProgram_lastReference aux3InBounds aux3Read ordinary
    refCountInBounds refCountRead one
  apply Wasm.wp.conseq _ lastBody
  intro continuation terminal
  cases continuation <;> simp_all [TerminalPost]

/-- Branch-independent composition of public decrement admission, the
count-one prefix, metadata loads, and the header-release call.  Recursive
representation proofs start only at the fully populated owned frame. -/
theorem wp_decrementOnceProgram_owned
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store releasedStore : Wasm.Store host}
    {object check flags descriptor refCount kind marker count
      captureCount : UInt32}
    {releaseHeaderIndex : Nat} {owned : Wasm.Program}
    (taggedClear : (1 : UInt32) &&& object = 0)
    (objectNonzero : object ≠ 0)
    (alignmentClear :
      UInt32.ofNat (target.heapAlignment - 1) &&& object = 0)
    (flagsInBounds :
      ¬(object.toNat + (UInt32.ofNat headerFlagsOffset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (flagsRead : store.mem.read32
      (object + UInt32.ofNat headerFlagsOffset) = flags)
    (liveSet : liveFlag &&& flags = liveFlag)
    (aux3InBounds :
      ¬(object.toNat + (UInt32.ofNat headerAux3Offset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (aux3Read : store.mem.read32
      (object + UInt32.ofNat headerAux3Offset) = descriptor)
    (ordinary : flags &&& persistentFlag ≠ persistentFlag)
    (refCountInBounds :
      ¬(object.toNat + (UInt32.ofNat headerRefCountOffset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (refCountRead : store.mem.read32
      (object + UInt32.ofNat headerRefCountOffset) = refCount)
    (one : refCount = 1)
    (kindInBounds :
      ¬(object.toNat + (UInt32.ofNat headerKindOffset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (kindRead : store.mem.read32
      (object + UInt32.ofNat headerKindOffset) = kind)
    (markerInBounds :
      ¬(object.toNat + (UInt32.ofNat headerAux0Offset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (markerRead : store.mem.read32
      (object + UInt32.ofNat headerAux0Offset) = marker)
    (countInBounds :
      ¬(object.toNat + (UInt32.ofNat headerAux1Offset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (countRead : store.mem.read32
      (object + UInt32.ofNat headerAux1Offset) = count)
    (captureInBounds :
      ¬(object.toNat + (UInt32.ofNat headerAux2Offset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (captureRead : store.mem.read32
      (object + UInt32.ofNat headerAux2Offset) = captureCount)
    (releaseRun : Wasm.TerminatesWith env module releaseHeaderIndex store
      [.i32 object]
      (fun final values => final = releasedStore ∧ values = []))
    (ownedBody : Wasm.wp module owned (TerminalPost Q) releasedStore
      (ownedEntry object check flags descriptor refCount kind marker count
        captureCount) env) :
    Wasm.wp module
      (decrementOnceProgram persistentReleaseProgram
        (lastReferenceProgram releaseHeaderIndex owned))
      Q store (decrementEntry object check) env := by
  apply wp_decrementOnceProgram_lastReference taggedClear objectNonzero
    alignmentClear flagsInBounds flagsRead liveSet aux3InBounds aux3Read ordinary
    refCountInBounds refCountRead one
  exact wp_lastReferenceProgram kindInBounds kindRead markerInBounds markerRead
    countInBounds countRead captureInBounds captureRead releaseRun ownedBody

/-- Full `fir_dec_once` control flow for a nonrecursive count-one allocation.
The only call is the already-proved header release; none of the three
recursive object-kind bodies is entered. -/
theorem wp_decrementOnceProgram_leaf
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store releasedStore : Wasm.Store host}
    {object check flags descriptor refCount kind marker count
      captureCount : UInt32}
    {releaseHeaderIndex : Nat}
    {constructorBody closureBody opaqueBody : Wasm.Program}
    (taggedClear : (1 : UInt32) &&& object = 0)
    (objectNonzero : object ≠ 0)
    (alignmentClear :
      UInt32.ofNat (target.heapAlignment - 1) &&& object = 0)
    (flagsInBounds :
      ¬(object.toNat + (UInt32.ofNat headerFlagsOffset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (flagsRead : store.mem.read32
      (object + UInt32.ofNat headerFlagsOffset) = flags)
    (liveSet : liveFlag &&& flags = liveFlag)
    (aux3InBounds :
      ¬(object.toNat + (UInt32.ofNat headerAux3Offset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (aux3Read : store.mem.read32
      (object + UInt32.ofNat headerAux3Offset) = descriptor)
    (ordinary : flags &&& persistentFlag ≠ persistentFlag)
    (refCountInBounds :
      ¬(object.toNat + (UInt32.ofNat headerRefCountOffset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (refCountRead : store.mem.read32
      (object + UInt32.ofNat headerRefCountOffset) = refCount)
    (one : refCount = 1)
    (kindInBounds :
      ¬(object.toNat + (UInt32.ofNat headerKindOffset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (kindRead : store.mem.read32
      (object + UInt32.ofNat headerKindOffset) = kind)
    (markerInBounds :
      ¬(object.toNat + (UInt32.ofNat headerAux0Offset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (markerRead : store.mem.read32
      (object + UInt32.ofNat headerAux0Offset) = marker)
    (countInBounds :
      ¬(object.toNat + (UInt32.ofNat headerAux1Offset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (countRead : store.mem.read32
      (object + UInt32.ofNat headerAux1Offset) = count)
    (captureInBounds :
      ¬(object.toNat + (UInt32.ofNat headerAux2Offset).toNat + 4 >
        store.mem.pages * wasmPageBytes))
    (captureRead : store.mem.read32
      (object + UInt32.ofNat headerAux2Offset) = captureCount)
    (releaseRun : Wasm.TerminatesWith env module releaseHeaderIndex store
      [.i32 object]
      (fun final values => final = releasedStore ∧ values = []))
    (notConstructor : kind ≠ ObjectKind.constructor.code)
    (notClosure : kind ≠ ObjectKind.closure.code)
    (notOpaque : kind ≠ ObjectKind.opaque.code)
    (returned : Q (.Return releasedStore [])) :
    Wasm.wp module
      (decrementOnceProgram persistentReleaseProgram
        (lastReferenceProgram releaseHeaderIndex
          (ownedReleaseProgram constructorBody closureBody opaqueBody)))
      Q store (decrementEntry object check) env := by
  apply wp_decrementOnceProgram_owned taggedClear objectNonzero
    alignmentClear flagsInBounds flagsRead liveSet aux3InBounds aux3Read ordinary
    refCountInBounds refCountRead one kindInBounds kindRead markerInBounds
    markerRead countInBounds countRead captureInBounds captureRead releaseRun
  apply wp_ownedReleaseProgram_leaf notConstructor notClosure notOpaque
  simpa [TerminalPost] using returned

/-- Adjacent checked W6 word stores refine the corresponding Talos stores.
Unlike the allocator specialization, this statement carries no global or
frontier premise and is therefore suitable for nonallocating helpers. -/
theorem writeUInt32sMemoryRel
    {heap : MemoryState} {memory : Wasm.Mem}
    (related : ResidentMemoryRel heap memory)
    {address : Nat} {values : List UInt32} {result : LinearMemory}
    (inBounds : address + 4 * values.length ≤ heap.memory.size)
    (written : heap.memory.writeUInt32s address values = .ok result) :
    ResidentMemoryRel { heap with memory := result }
      (ResidentMemoryRel.writeUInt32sMemory memory
        (UInt32.ofNat address) values) := by
  induction values generalizing heap memory address result with
  | nil =>
      simp [LinearMemory.writeUInt32s] at written
      subst result
      simpa [ResidentMemoryRel.writeUInt32sMemory] using related
  | cons value rest ih =>
      simp only [List.length_cons] at inBounds
      have headInBounds : address + 3 < heap.memory.size := by omega
      obtain ⟨middle, headWrite, middleSize, _, _, _, _, _⟩ :=
        LinearMemory.writeUInt32_spec heap.memory address value headInBounds
      unfold LinearMemory.writeUInt32s at written
      rw [headWrite] at written
      have middleRelated := related.writeUInt32 headInBounds headWrite
      have tailInBounds : address + 4 + 4 * rest.length ≤ middle.size := by
        omega
      have tailRelated := ih middleRelated tailInBounds written
      simpa [ResidentMemoryRel.writeUInt32sMemory, UInt32.ofNat_add] using
        tailRelated

/-- Transport one exact common-header lane to Talos memory.  The complete
header bound supplies both the concrete checked read and the Wasm load bound;
the exact-words premise preserves raw flags rather than re-encoding them. -/
theorem residentHeaderWord
    {heap : MemoryState} {memory : Wasm.Mem} {address : Word32}
    {header : Header} {index : Nat} {word : UInt32}
    (related : ResidentMemoryRel heap memory)
    (exact : Header.ExactWords heap.memory address header)
    (headerInBounds : address.value + headerBytes ≤ heap.memory.size)
    (wordAt : header.words[index]? = some word) :
    ¬((UInt32.ofNat address.value).toNat +
        (UInt32.ofNat (4 * index)).toNat + 4 >
      memory.pages * wasmPageBytes) ∧
    memory.read32
        (UInt32.ofNat address.value + UInt32.ofNat (4 * index)) = word := by
  have indexLt := (List.getElem?_eq_some_iff.mp wordAt).1
  have indexBound : 4 * index + 4 ≤ headerBytes := by
    simp [Header.words] at indexLt
    simp [headerBytes]
    omega
  have concreteInBounds :
      address.value + 4 * index + 3 < heap.memory.size := by
    omega
  have transported := related.readUInt32_eq_read32 concreteInBounds
  have concreteRead := exact.wordAt index word wordAt
  have addressToNat : (UInt32.ofNat address.value).toNat = address.value :=
    UInt32.toNat_ofNat_of_lt' (by
      simpa [wordModulus] using address.isLt)
  have offsetLt : 4 * index < UInt32.size := by
    simp [headerBytes, UInt32.size] at indexBound ⊢
    omega
  have offsetToNat : (UInt32.ofNat (4 * index)).toNat = 4 * index :=
    UInt32.toNat_ofNat_of_lt' offsetLt
  have sizeEq : heap.memory.size = memory.pages * wasmPageBytes :=
    related.size_eq
  constructor
  · rw [addressToNat, offsetToNat, ← sizeEq]
    omega
  · rw [← UInt32.ofNat_add]
    rw [concreteRead] at transported
    simpa using transported.symm

/-- A represented live heap header supplies every common resident-release
entry fact.  No ownership branch choice is made here. -/
theorem LiveHeaderResidentFacts.ofRelations
    {state : MemoryState} {memory : Wasm.Mem} {address : Word32}
    {header : Header}
    (related : ResidentMemoryRel state memory)
    (exact : Header.ExactWords state.memory address header)
    (headerInBounds : address.value + headerBytes ≤ state.memory.size)
    (heap : address.classify = .heap)
    (live : header.live = true) :
    LiveHeaderResidentFacts memory address header := by
  have kind := residentHeaderWord related exact headerInBounds
    (index := 0) (word := header.kind.code) (by simp [Header.words])
  have flags := residentHeaderWord related exact headerInBounds
    (index := 1) (word := header.flags) (by simp [Header.words])
  have refCount := residentHeaderWord related exact headerInBounds
    (index := 2) (word := header.refCount) (by simp [Header.words])
  have aux0 := residentHeaderWord related exact headerInBounds
    (index := 4) (word := header.aux0) (by simp [Header.words])
  have aux1 := residentHeaderWord related exact headerInBounds
    (index := 5) (word := header.aux1) (by simp [Header.words])
  have aux2 := residentHeaderWord related exact headerInBounds
    (index := 6) (word := header.aux2) (by simp [Header.words])
  have aux3 := residentHeaderWord related exact headerInBounds
    (index := 7) (word := header.aux3) (by simp [Header.words])
  have addressFits : address.value < UInt32.size := by
    simpa [UInt32.size, wordModulus] using address.isLt
  have addressNonzero : address.value ≠ 0 := by
    intro zero
    simp [Word32.classify, zero] at heap
  have objectNonzero : UInt32.ofNat address.value ≠ 0 := by
    intro zero
    have zeroNat := congrArg UInt32.toNat zero
    rw [UInt32.toNat_ofNat_of_lt' addressFits] at zeroNat
    simp at zeroNat
    exact addressNonzero zeroNat
  have addressAligned : address.value % target.heapAlignment = 0 := by
    unfold Word32.classify at heap
    split at heap <;> try contradiction
    split at heap <;> try contradiction
    split at heap <;> try contradiction
    assumption
  have objectLowBit : UInt32.ofNat address.value &&& 1 = 0 := by
    have aligned8 : address.value % 8 = 0 := by
      simpa [target] using addressAligned
    have even : address.value % 2 = 0 := by omega
    apply UInt32.toNat_inj.mp
    simpa [Nat.and_one_is_mod] using even
  have taggedClear : (1 : UInt32) &&& UInt32.ofNat address.value = 0 := by
    simpa [UInt32.and_comm] using objectLowBit
  have objectAligned : UInt32.ofNat address.value &&& 7 = 0 :=
    ResidentAllocator.alignedWord_of_mod8 addressFits (by
      simpa [target] using addressAligned)
  have alignmentClear :
      UInt32.ofNat (target.heapAlignment - 1) &&&
          UInt32.ofNat address.value = 0 := by
    simpa [target, UInt32.and_comm] using objectAligned
  have liveSet : liveFlag &&& header.flags = liveFlag := by
    have trueCase : (2 : UInt32) &&& 3 = 2 := by decide
    cases persistent : header.persistent
    · simp [Header.flags, live, liveFlag, persistent]
    · simpa [Header.flags, live, liveFlag, persistent] using trueCase
  exact {
    taggedClear
    objectNonzero
    alignmentClear
    flagsInBounds := flags.1
    flagsRead := flags.2
    liveSet
    kindInBounds := kind.1
    kindRead := kind.2
    refCountInBounds := refCount.1
    refCountRead := refCount.2
    aux0InBounds := aux0.1
    aux0Read := aux0.2
    aux1InBounds := aux1.1
    aux1Read := aux1.2
    aux2InBounds := aux2.1
    aux2Read := aux2.2
    aux3InBounds := aux3.1
    aux3Read := aux3.2 }

/-- A semantically nonrecursive cell has one of the four resident leaf header
kinds.  This packages the representation inversion needed by all leaf release
proofs, independently of target control flow. -/
theorem LiveCellRel.nonrecursiveHeaderKind
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : Fir.LeanIR.Impure.HeapCell}
    (related : LiveCellRel state witness address cell)
    (leafCell : NonrecursiveCell cell)
    {header : Header}
    (headerRead : state.readLiveHeader address = .ok header) :
    header.kind = .boxed ∨ header.kind = .natural ∨
      header.kind = .string ∨ header.kind = .integer := by
  cases related with
  | constructor descriptor objectEq objectRelated relatedRead headerKind
        refCount persistent live =>
      rcases leafCell with ((boxedCell | naturalCell) | stringCell) | integerCell
      · obtain ⟨kind, scalar, boxedEq⟩ := boxedCell
        rw [objectEq] at boxedEq
        contradiction
      · obtain ⟨value, naturalEq⟩ := naturalCell
        rw [objectEq] at naturalEq
        contradiction
      · obtain ⟨value, stringEq⟩ := stringCell
        rw [objectEq] at stringEq
        contradiction
      · obtain ⟨value, integerEq⟩ := integerCell
        rw [objectEq] at integerEq
        contradiction
  | @boxed kind scalar actualHeader _ descriptor objectEq objectRelated refCount
        persistent live =>
      have headerEq : header = actualHeader :=
        Except.ok.inj (headerRead.symm.trans objectRelated.headerRead)
      subst header
      exact .inl objectRelated.headerKind
  | @natural value actualHeader _ descriptor objectEq objectRelated refCount
        persistent live =>
      have headerEq : header = actualHeader :=
        Except.ok.inj (headerRead.symm.trans objectRelated.headerRead)
      subst header
      exact .inr (.inl objectRelated.headerKind)
  | @integer value actualHeader _ descriptor objectEq objectRelated refCount
        persistent live =>
      have headerEq : header = actualHeader :=
        Except.ok.inj (headerRead.symm.trans objectRelated.headerRead)
      subst header
      exact .inr (.inr (.inr objectRelated.headerKind))
  | @string value actualHeader _ descriptor objectEq objectRelated refCount
        persistent live =>
      have headerEq : header = actualHeader :=
        Except.ok.inj (headerRead.symm.trans objectRelated.headerRead)
      subst header
      exact .inr (.inr (.inl objectRelated.headerKind))
  | @array elements capacity actualHeader _ descriptor objectEq objectRelated
        refCount persistent live =>
      rcases leafCell with ((boxedCell | naturalCell) | stringCell) | integerCell
      · obtain ⟨kind, scalar, boxedEq⟩ := boxedCell
        rw [objectEq] at boxedEq
        contradiction
      · obtain ⟨value, naturalEq⟩ := naturalCell
        rw [objectEq] at naturalEq
        contradiction
      · obtain ⟨value, stringEq⟩ := stringCell
        rw [objectEq] at stringEq
        contradiction
      · obtain ⟨value, integerEq⟩ := integerCell
        rw [objectEq] at integerEq
        contradiction
  | closure closureRelated =>
      obtain ⟨function, arity, captures, closureEq⟩ := closureRelated.objectEq
      rcases leafCell with ((boxedCell | naturalCell) | stringCell) | integerCell
      · obtain ⟨kind, scalar, boxedEq⟩ := boxedCell
        rw [closureEq] at boxedEq
        contradiction
      · obtain ⟨value, naturalEq⟩ := naturalCell
        rw [closureEq] at naturalEq
        contradiction
      · obtain ⟨value, stringEq⟩ := stringCell
        rw [closureEq] at stringEq
        contradiction
      · obtain ⟨value, integerEq⟩ := integerCell
        rw [closureEq] at integerEq
        contradiction

/-- Target-level discriminator facts obtained from the semantic leaf-kind
inversion. -/
theorem LiveCellRel.nonrecursiveHeaderCode
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : Fir.LeanIR.Impure.HeapCell}
    (related : LiveCellRel state witness address cell)
    (leafCell : NonrecursiveCell cell)
    {header : Header}
    (headerRead : state.readLiveHeader address = .ok header) :
    header.kind.code ≠ ObjectKind.constructor.code ∧
      header.kind.code ≠ ObjectKind.closure.code ∧
      header.kind.code ≠ ObjectKind.opaque.code := by
  rcases FirTalos.Concrete.ResidentRelease.LiveCellRel.nonrecursiveHeaderKind
      related leafCell headerRead with
    kind | kind | kind | kind <;> simp [kind, ObjectKind.code]

/-- A logical common-header rewrite that changes only the reference-count
field has the same resident-memory effect as W7's single hot-path store. -/
theorem ResidentMemoryRel.writeHeaderRefCount
    {heap : MemoryState} {memory : Wasm.Mem}
    (related : ResidentMemoryRel heap memory)
    {address : Word32} {header : Header} {nextCount : UInt32}
    {result : LinearMemory}
    (exact : Header.ExactWords heap.memory address header)
    (headerInBounds : address.value + headerBytes ≤ heap.memory.size)
    (written : ({ header with refCount := nextCount } : Header).write
      heap.memory address = .ok result) :
    ResidentMemoryRel { heap with memory := result }
      (memory.write32
        (UInt32.ofNat address.value + UInt32.ofNat headerRefCountOffset)
        nextCount) := by
  have full := writeUInt32sMemoryRel related
    (values := ({ header with refCount := nextCount } : Header).words)
    (by simpa [Header.words, headerBytes] using headerInBounds)
    written
  have kind := residentHeaderWord related exact headerInBounds
    (index := 0) (word := header.kind.code) (by simp [Header.words])
  have flags := residentHeaderWord related exact headerInBounds
    (index := 1) (word := header.flags) (by simp [Header.words])
  have allocation := residentHeaderWord related exact headerInBounds
    (index := 3) (word := header.allocationBytes) (by simp [Header.words])
  have aux0 := residentHeaderWord related exact headerInBounds
    (index := 4) (word := header.aux0) (by simp [Header.words])
  have aux1 := residentHeaderWord related exact headerInBounds
    (index := 5) (word := header.aux1) (by simp [Header.words])
  have aux2 := residentHeaderWord related exact headerInBounds
    (index := 6) (word := header.aux2) (by simp [Header.words])
  have aux3 := residentHeaderWord related exact headerInBounds
    (index := 7) (word := header.aux3) (by simp [Header.words])
  have memoryEq :
      ResidentMemoryRel.writeUInt32sMemory memory
          (UInt32.ofNat address.value)
          ({ header with refCount := nextCount } : Header).words =
        memory.write32
          (UInt32.ofNat address.value + UInt32.ofNat headerRefCountOffset)
          nextCount := by
    have kindRead :
        memory.read32 (UInt32.ofNat address.value) = header.kind.code := by
      simpa using kind.2
    have flagsRead :
        memory.read32 (UInt32.ofNat address.value + 4) = header.flags := by
      simpa using flags.2
    simp only [Header.words, ResidentMemoryRel.writeUInt32sMemory,
      headerRefCountOffset]
    rw [← kindRead, ResidentMemoryRel.write32_read32_self]
    rw [show ({ header with refCount := nextCount } : Header).flags =
      header.flags by rfl]
    rw [← flagsRead, ResidentMemoryRel.write32_read32_self]
    have headerFits : address.value + headerBytes ≤ UInt32.size :=
      Nat.le_trans headerInBounds related.size_le
    have addressOffsetToNat (offset : Nat)
        (fits : address.value + offset < UInt32.size) :
        (UInt32.ofNat address.value + UInt32.ofNat offset).toNat =
          address.value + offset := by
      rw [← UInt32.ofNat_add, UInt32.toNat_ofNat_of_lt' fits]
    have readAfterRef (offset : Nat) (word : UInt32)
        (offsetMin : 12 ≤ offset) (offsetBound : offset + 4 ≤ headerBytes)
        (read : memory.read32
          (UInt32.ofNat address.value + UInt32.ofNat offset) = word) :
        (memory.write32
          (UInt32.ofNat address.value + UInt32.ofNat 8) nextCount).read32
            (UInt32.ofNat address.value + UInt32.ofNat offset) = word := by
      rw [ResidentMemoryRel.read32_write32_disjoint]
      · exact read
      · left
        rw [addressOffsetToNat 8 (by omega),
          addressOffsetToNat offset (by omega)]
        omega
    have allocationRead : memory.read32
        (UInt32.ofNat address.value + UInt32.ofNat 12) =
          header.allocationBytes := by
      simpa using allocation.2
    have aux0Read : memory.read32
        (UInt32.ofNat address.value + UInt32.ofNat 16) = header.aux0 := by
      simpa using aux0.2
    have aux1Read : memory.read32
        (UInt32.ofNat address.value + UInt32.ofNat 20) = header.aux1 := by
      simpa using aux1.2
    have aux2Read : memory.read32
        (UInt32.ofNat address.value + UInt32.ofNat 24) = header.aux2 := by
      simpa using aux2.2
    have aux3Read : memory.read32
        (UInt32.ofNat address.value + UInt32.ofNat 28) = header.aux3 := by
      simpa using aux3.2
    have step8 : (4 : UInt32) + 4 = UInt32.ofNat 8 := by decide
    have step12 : UInt32.ofNat 8 + 4 = UInt32.ofNat 12 := by decide
    have step16 : UInt32.ofNat 12 + 4 = UInt32.ofNat 16 := by decide
    have step20 : UInt32.ofNat 16 + 4 = UInt32.ofNat 20 := by decide
    have step24 : UInt32.ofNat 20 + 4 = UInt32.ofNat 24 := by decide
    have step28 : UInt32.ofNat 24 + 4 = UInt32.ofNat 28 := by decide
    rw [show UInt32.ofNat address.value + 4 + 4 =
      UInt32.ofNat address.value + UInt32.ofNat 8 by
        rw [UInt32.add_assoc, step8]]
    rw [show UInt32.ofNat address.value + UInt32.ofNat 8 + 4 =
      UInt32.ofNat address.value + UInt32.ofNat 12 by
        rw [UInt32.add_assoc, step12]]
    rw [← readAfterRef 12 header.allocationBytes (by decide) (by decide)
      allocationRead, ResidentMemoryRel.write32_read32_self]
    rw [show UInt32.ofNat address.value + UInt32.ofNat 12 + 4 =
      UInt32.ofNat address.value + UInt32.ofNat 16 by
        rw [UInt32.add_assoc, step16]]
    rw [← readAfterRef 16 header.aux0 (by decide) (by decide) aux0Read,
      ResidentMemoryRel.write32_read32_self]
    rw [show UInt32.ofNat address.value + UInt32.ofNat 16 + 4 =
      UInt32.ofNat address.value + UInt32.ofNat 20 by
        rw [UInt32.add_assoc, step20]]
    rw [← readAfterRef 20 header.aux1 (by decide) (by decide) aux1Read,
      ResidentMemoryRel.write32_read32_self]
    rw [show UInt32.ofNat address.value + UInt32.ofNat 20 + 4 =
      UInt32.ofNat address.value + UInt32.ofNat 24 by
        rw [UInt32.add_assoc, step24]]
    rw [← readAfterRef 24 header.aux2 (by decide) (by decide) aux2Read,
      ResidentMemoryRel.write32_read32_self]
    rw [show UInt32.ofNat address.value + UInt32.ofNat 24 + 4 =
      UInt32.ofNat address.value + UInt32.ofNat 28 by
        rw [UInt32.add_assoc, step28]]
    rw [← readAfterRef 28 header.aux3 (by decide) (by decide) aux3Read,
      ResidentMemoryRel.write32_read32_self]
  simpa [memoryEq] using full

/-- Skipping the retained allocation-size lane is extensionally equivalent to
rewriting the complete canonical released header.  Exactness of the old
header supplies the skipped word; the preceding three stores are disjoint
from that lane. -/
theorem releaseHeaderMemory_eq_writeUInt32sMemory
    {heap : MemoryState} {memory : Wasm.Mem} {address : Word32}
    {header : Header}
    (related : ResidentMemoryRel heap memory)
    (exact : Header.ExactWords heap.memory address header)
    (headerInBounds : address.value + headerBytes ≤ heap.memory.size) :
    releaseHeaderMemory memory (UInt32.ofNat address.value) =
      ResidentMemoryRel.writeUInt32sMemory memory
        (UInt32.ofNat address.value) header.forRelease.words := by
  let object := UInt32.ofNat address.value
  have allocation := residentHeaderWord related exact headerInBounds
    (index := 3) (word := header.allocationBytes) (by simp [Header.words])
  have allocationRead : memory.read32
      (object + UInt32.ofNat headerAllocationBytesOffset) =
        header.allocationBytes := by
    change memory.read32 (UInt32.ofNat address.value + 12) =
      header.allocationBytes
    simpa using allocation.2
  have headerFits : address.value + headerBytes ≤ UInt32.size :=
    Nat.le_trans headerInBounds related.size_le
  have addressOffsetToNat (offset : Nat)
      (fits : address.value + offset < UInt32.size) :
      (object + UInt32.ofNat offset).toNat = address.value + offset := by
    dsimp [object]
    rw [← UInt32.ofNat_add, UInt32.toNat_ofNat_of_lt' fits]
  have addressOffsetFits (offset : Nat) (bound : offset < headerBytes) :
      address.value + offset < UInt32.size := by
    omega
  let beforeAllocation :=
    ((memory.write32
        (object + UInt32.ofNat headerKindOffset) ObjectKind.freed.code).write32
        (object + UInt32.ofNat headerFlagsOffset) 0).write32
        (object + UInt32.ofNat headerRefCountOffset) 0
  have beforeAllocationRead : beforeAllocation.read32
      (object + UInt32.ofNat headerAllocationBytesOffset) =
        header.allocationBytes := by
    dsimp [beforeAllocation]
    rw [ResidentMemoryRel.read32_write32_disjoint]
    · rw [ResidentMemoryRel.read32_write32_disjoint]
      · rw [ResidentMemoryRel.read32_write32_disjoint]
        · exact allocationRead
        · left
          rw [addressOffsetToNat headerKindOffset
              (addressOffsetFits headerKindOffset (by decide)),
            addressOffsetToNat headerAllocationBytesOffset
              (addressOffsetFits headerAllocationBytesOffset (by decide))]
          simp [headerKindOffset, headerAllocationBytesOffset]
      · left
        rw [addressOffsetToNat headerFlagsOffset
            (addressOffsetFits headerFlagsOffset (by decide)),
          addressOffsetToNat headerAllocationBytesOffset
            (addressOffsetFits headerAllocationBytesOffset (by decide))]
        simp [headerFlagsOffset, headerAllocationBytesOffset]
    · left
      rw [addressOffsetToNat headerRefCountOffset
          (addressOffsetFits headerRefCountOffset (by decide)),
        addressOffsetToNat headerAllocationBytesOffset
          (addressOffsetFits headerAllocationBytesOffset (by decide))]
      simp [headerRefCountOffset, headerAllocationBytesOffset]
  have step8 : (4 : UInt32) + 4 = UInt32.ofNat 8 := by decide
  have step12 : UInt32.ofNat 8 + 4 = UInt32.ofNat 12 := by decide
  have step16 : UInt32.ofNat 12 + 4 = UInt32.ofNat 16 := by decide
  have step20 : UInt32.ofNat 16 + 4 = UInt32.ofNat 20 := by decide
  have step24 : UInt32.ofNat 20 + 4 = UInt32.ofNat 24 := by decide
  have step28 : UInt32.ofNat 24 + 4 = UInt32.ofNat 28 := by decide
  have beforeAllocationEq :
      ((memory.write32 (UInt32.ofNat address.value) ObjectKind.freed.code).write32
          (UInt32.ofNat address.value + 4) 0).write32
          (UInt32.ofNat address.value + UInt32.ofNat 8) 0 =
        beforeAllocation := by
    simp [beforeAllocation, object, headerKindOffset, headerFlagsOffset,
      headerRefCountOffset]
  let afterAllocation (current : Wasm.Mem) :=
    (((current.write32
      (object + UInt32.ofNat headerAux0Offset) 0).write32
      (object + UInt32.ofNat headerAux1Offset) 0).write32
      (object + UInt32.ofNat headerAux2Offset) 0).write32
      (object + UInt32.ofNat headerAux3Offset) 0
  have releaseShape :
      releaseHeaderMemory memory object = afterAllocation beforeAllocation := by
    rfl
  have fullShape :
      ResidentMemoryRel.writeUInt32sMemory memory object
          header.forRelease.words =
        afterAllocation (beforeAllocation.write32
          (object + UInt32.ofNat headerAllocationBytesOffset)
          header.allocationBytes) := by
    simp only [Header.words, Header.forRelease, Header.flags,
      Bool.false_eq_true, ↓reduceIte,
      ResidentMemoryRel.writeUInt32sMemory]
    rw [show object + 4 + 4 = object + UInt32.ofNat 8 by
      rw [UInt32.add_assoc, step8]]
    rw [show object + UInt32.ofNat 8 + 4 = object + UInt32.ofNat 12 by
      rw [UInt32.add_assoc, step12]]
    rw [show object + UInt32.ofNat 12 + 4 = object + UInt32.ofNat 16 by
      rw [UInt32.add_assoc, step16]]
    rw [show object + UInt32.ofNat 16 + 4 = object + UInt32.ofNat 20 by
      rw [UInt32.add_assoc, step20]]
    rw [show object + UInt32.ofNat 20 + 4 = object + UInt32.ofNat 24 by
      rw [UInt32.add_assoc, step24]]
    rw [show object + UInt32.ofNat 24 + 4 = object + UInt32.ofNat 28 by
      rw [UInt32.add_assoc, step28]]
    rw [show UInt32.ofNat 0 = 0 by decide]
    rw [beforeAllocationEq]
    rfl
  rw [releaseShape, fullShape, ← beforeAllocationRead,
    ResidentMemoryRel.write32_read32_self]

/-- W6's canonical released-header write and W7's seven resident stores
produce related memories. -/
theorem ResidentMemoryRel.releaseHeader
    {heap : MemoryState} {memory : Wasm.Mem}
    (related : ResidentMemoryRel heap memory)
    {address : Word32} {header : Header} {result : LinearMemory}
    (exact : Header.ExactWords heap.memory address header)
    (headerInBounds : address.value + headerBytes ≤ heap.memory.size)
    (written : header.forRelease.write heap.memory address = .ok result) :
    ResidentMemoryRel { heap with memory := result }
      (releaseHeaderMemory memory (UInt32.ofNat address.value)) := by
  have full := writeUInt32sMemoryRel related
    (values := header.forRelease.words)
    (by simpa [Header.words, headerBytes] using headerInBounds)
    written
  rw [releaseHeaderMemory_eq_writeUInt32sMemory related exact headerInBounds]
  exact full

/-- The resident header helper implements W6's canonical release transition.
The resulting concrete allocation is a proved dead cell, its memory remains
related to the exact seven-store target state, and the target body returns
normally with no values. -/
theorem LiveCellRel.releaseHeaderProgram_refines
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {store : Wasm.Store host}
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : Fir.LeanIR.Impure.HeapCell}
    (cellRelated : LiveCellRel state witness address cell)
    (valid : state.FrontierInvariant)
    (memoryRelated : ResidentMemoryRel state store.mem)
    (exactHeader : CanonicalLiveHeaderRel state address) :
    ∃ header result,
      state.readLiveHeader address = .ok header ∧
      writeLiveHeader state address header.forRelease = .ok result ∧
      result.FrontierInvariant ∧
      DeadCellRel result address ∧
      ResidentMemoryRel result
        (releaseHeaderStore store (UInt32.ofNat address.value)).mem ∧
      Wasm.wp module releaseHeaderProgram
        (fun continuation => continuation =
          .Return (releaseHeaderStore store (UInt32.ofNat address.value)) [])
        store (releaseHeaderEntry (UInt32.ofNat address.value)) env := by
  obtain ⟨header, headerRead, _, _, _, _⟩ := cellRelated.ownershipHeader
  have exact := exactHeader header headerRead
  have headerInBounds : address.value + headerBytes ≤ state.memory.size :=
    Nat.le_trans cellRelated.headerOwned valid.cursorInBounds
  obtain ⟨result, memory, operation, resultEq, headerWrite, finalValid,
      dead⟩ :=
    Fir.Wasm.Concrete.releaseHeader valid headerRead cellRelated.headerOwned
  have finalMemory : ResidentMemoryRel result
      (releaseHeaderStore store (UInt32.ofNat address.value)).mem := by
    rw [resultEq]
    simpa [releaseHeaderStore] using
      ResidentMemoryRel.releaseHeader memoryRelated exact headerInBounds
        headerWrite
  have addressToNat : (UInt32.ofNat address.value).toNat = address.value :=
    UInt32.toNat_ofNat_of_lt' (by
      simpa [UInt32.size, wordModulus] using address.isLt)
  have targetHeaderInBounds :
      (UInt32.ofNat address.value).toNat + headerBytes ≤
        store.mem.pages * wasmPageBytes := by
    rw [addressToNat, ← memoryRelated.size_eq]
    exact headerInBounds
  have physicalExecution :
      Wasm.wp module releaseHeaderProgram
        (fun continuation => continuation =
          .Return (releaseHeaderStore store (UInt32.ofNat address.value)) [])
        store (releaseHeaderEntry (UInt32.ofNat address.value)) env := by
    apply wp_releaseHeaderProgram targetHeaderInBounds
    rfl
  exact ⟨header, result, headerRead, operation, finalValid, dead,
    finalMemory, physicalExecution⟩

/-- The resident helper's early ordinary decrement is a semantic ownership
step, not merely a successful store.  Starting from the shared W6 heap
simulation, its exact physical update remains related to the result of both
the concrete host operation and FIR's `decValueOnce` semantics.  The two cold
branches remain opaque because neither is selected when the represented cell
is ordinary and has more than one reference. -/
theorem LiveHeapRel.decrementOnceProgram_aboveOne_refines
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {store : Wasm.Store host}
    {state : MemoryState} {witness : RefinementWitness}
    {runtime : Fir.LeanIR.Impure.RuntimeState}
    {location : Fir.LeanIR.Impure.Location} {address : Word32}
    {cell : Fir.LeanIR.Impure.HeapCell}
    {descriptors : ClosureDescriptorTable}
    {persistentProgram lastReference : Wasm.Program}
    (related : LiveHeapRel state witness runtime)
    (memoryRelated : ResidentMemoryRel state store.mem)
    (canonicalHeaders : CanonicalMappedHeadersRel state witness)
    (mapped : witness.locations.lookup? location = some address)
    (found : Fir.LeanIR.Impure.findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (ordinary : cell.persistent = false)
    (oneLt : 1 < cell.rc) (check : Bool) (checkWord : UInt32) :
    let object := UInt32.ofNat address.value
    let nextCount := UInt32.ofNat (cell.rc - 1)
    let finalStore := ResidentMemoryRel.write32Store store
      (object + UInt32.ofNat headerRefCountOffset) nextCount
    ∃ header result nextRuntime,
      state.readLiveHeader address = .ok header ∧
      decrementReferenceOnce state address check descriptors = .ok result ∧
      Fir.LeanIR.Impure.decValueOnce runtime (.object (.heap location)) check =
        .ok nextRuntime ∧
      LiveHeapRel result witness nextRuntime ∧
      CanonicalMappedHeadersRel result witness ∧
      ResidentMemoryRel result finalStore.mem ∧
      Wasm.wp module
        (decrementOnceProgram persistentProgram lastReference)
        (fun continuation => continuation = .Return finalStore []) store
        (decrementEntry object checkWord) env := by
  dsimp only
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  obtain ⟨header, headerRead, _, notPromoted, persistent,
      refCount⟩ := targetRelated.ownershipHeader
  have exact := canonicalHeaders mapped header headerRead
  have headerOrdinary : header.persistent = false := persistent.trans ordinary
  have headerInBounds : address.value + headerBytes ≤ state.memory.size :=
    Nat.le_trans targetRelated.headerOwned related.frontier.cursorInBounds
  let nextCount := UInt32.ofNat (cell.rc - 1)
  obtain ⟨result, updatedHeader, memory, writeOperation, updatedEq, resultEq,
      headerWrite, _, _⟩ :=
    writeReferenceCount_header related.frontier headerRead
      targetRelated.headerOwned nextCount
  obtain ⟨heap, rawHeader, headerLive, _, _, _⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts state address header
      headerRead
  have refCountNe : header.refCount ≠ 0 := by
    intro zero
    rw [zero] at refCount
    simp at refCount
    omega
  have concreteOperation :
      decrementReferenceOnce state address check descriptors = .ok result := by
    simp only [decrementReferenceOnce, decrementReferenceOnceFuel]
    rw [heap]
    simp only
    rw [headerRead]
    simp only [Bind.bind, Except.bind, liftMemory]
    rw [if_neg (by simp [notPromoted])]
    rw [if_neg (by simp [headerOrdinary])]
    rw [if_neg (by simpa using refCountNe)]
    rw [refCount, if_pos oneLt]
    simpa [updatedEq] using writeOperation
  obtain ⟨semanticResult, nextRuntime, semanticConcrete, semanticOperation,
      finalRelated, _⟩ :=
    related.decrementReferenceOnce_refines_above_one_with_capacity
      (descriptors := descriptors) mapped found live ordinary oneLt check
  have resultEqSemantic : result = semanticResult :=
    Except.ok.inj (concreteOperation.symm.trans semanticConcrete)
  subst semanticResult
  have nextCountFits : cell.rc - 1 < UInt32.size := by
    have countFits := UInt32.toNat_lt_size header.refCount
    rw [refCount] at countFits
    omega
  have physicalOneLt : (1 : UInt32) < header.refCount := by
    rw [UInt32.lt_iff_toNat_lt, refCount]
    exact oneLt
  have nextCountEq : nextCount = header.refCount - 1 := by
    have physicalOneLe : (1 : UInt32) ≤ header.refCount := by
      rw [UInt32.le_iff_toNat_le, refCount]
      simpa using (Nat.le_of_lt oneLt)
    apply UInt32.toNat.inj
    rw [UInt32.toNat_ofNat_of_lt' nextCountFits,
      UInt32.toNat_sub_of_le header.refCount 1 physicalOneLe,
      refCount]
    rfl
  have finalMemory : ResidentMemoryRel result
      (ResidentMemoryRel.write32Store store
        (UInt32.ofNat address.value + UInt32.ofNat headerRefCountOffset)
        nextCount).mem := by
    rw [resultEq]
    have headerWrite' :
        ({ header with refCount := nextCount } : Header).write
            state.memory address = .ok memory := by
      simpa [updatedEq] using headerWrite
    simpa using
      FirTalos.Concrete.ResidentRelease.ResidentMemoryRel.writeHeaderRefCount
        memoryRelated exact headerInBounds headerWrite'
  obtain ⟨descriptor, descriptorFound⟩ := targetRelated.descriptor
  have canonicalAfter : CanonicalMappedHeadersRel result witness :=
    canonicalHeaders.ofHeaderWrite related descriptorFound rawHeader resultEq
      headerInBounds headerWrite
  have entry := LiveHeaderResidentFacts.ofRelations memoryRelated exact
    headerInBounds heap headerLive
  have physicalOrdinary : header.flags &&& persistentFlag ≠ persistentFlag := by
    cases liveValue : header.live
    · simp [Header.flags, headerOrdinary, liveValue, persistentFlag]
    · simp [Header.flags, headerOrdinary, liveValue, persistentFlag]
      decide
  have physicalExecution :
      Wasm.wp module (decrementOnceProgram persistentProgram lastReference)
        (fun continuation =>
          continuation = .Return
            (ResidentMemoryRel.write32Store store
              (UInt32.ofNat address.value +
                UInt32.ofNat headerRefCountOffset) nextCount) []) store
        (decrementEntry (UInt32.ofNat address.value) checkWord) env := by
    apply wp_decrementOnceProgram_aboveOne entry.taggedClear
      entry.objectNonzero entry.alignmentClear entry.flagsInBounds
      entry.flagsRead entry.liveSet entry.aux3InBounds entry.aux3Read
      physicalOrdinary entry.refCountInBounds entry.refCountRead refCountNe
      physicalOneLt
    simp [nextCountEq]
  exact ⟨header, result, nextRuntime, headerRead, concreteOperation,
    semanticOperation, finalRelated, canonicalAfter, finalMemory,
    physicalExecution⟩

/-- Complete three-semantics refinement for a nonrecursive count-one object.
The W6 concrete runtime and FIR semantics both replace the live cell by its
dead form; resident Wasm performs the exact released-header call and returns
without entering constructor, closure, or opaque recursion. -/
theorem LiveHeapRel.decrementOnceProgram_leaf_refines
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {store : Wasm.Store host}
    {state : MemoryState} {witness : RefinementWitness}
    {runtime : Fir.LeanIR.Impure.RuntimeState}
    {location : Fir.LeanIR.Impure.Location} {address : Word32}
    {cell : Fir.LeanIR.Impure.HeapCell}
    {descriptors : ClosureDescriptorTable}
    {releaseHeaderIndex : Nat}
    {constructorBody closureBody opaqueBody : Wasm.Program}
    (related : LiveHeapRel state witness runtime)
    (memoryRelated : ResidentMemoryRel state store.mem)
    (canonicalHeaders : CanonicalMappedHeadersRel state witness)
    (mapped : witness.locations.lookup? location = some address)
    (found : Fir.LeanIR.Impure.findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (leafCell : NonrecursiveCell cell)
    (ordinary : cell.persistent = false)
    (one : cell.rc = 1) (check : Bool) (checkWord : UInt32)
    (releaseRun : Wasm.TerminatesWith env module releaseHeaderIndex store
      [.i32 (UInt32.ofNat address.value)]
      (fun final values =>
        final = releaseHeaderStore store (UInt32.ofNat address.value) ∧
          values = [])) :
    let object := UInt32.ofNat address.value
    let finalStore := releaseHeaderStore store object
    ∃ header result nextRuntime,
      state.readLiveHeader address = .ok header ∧
      decrementReferenceOnce state address check descriptors = .ok result ∧
      Fir.LeanIR.Impure.decValueOnce runtime (.object (.heap location)) check =
        .ok nextRuntime ∧
      LiveHeapRel result witness nextRuntime ∧
      CanonicalMappedHeadersRel result witness ∧
      DeadCellRel result address ∧
      ResidentMemoryRel result finalStore.mem ∧
      Wasm.wp module
        (decrementOnceProgram persistentReleaseProgram
          (lastReferenceProgram releaseHeaderIndex
            (ownedReleaseProgram constructorBody closureBody opaqueBody)))
        (fun continuation => continuation = .Return finalStore []) store
        (decrementEntry object checkWord) env := by
  dsimp only
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  obtain ⟨released, header, releasedMemory, concreteRelease, headerRead,
      releasedEq, headerWrite, releasedValid, dead⟩ :=
    targetRelated.decrementReferenceOnce_leaf_one
      (descriptors := descriptors) leafCell related.frontier ordinary one check
  obtain ⟨result, nextRuntime, concreteOperation, semanticOperation,
      finalRelated⟩ :=
    related.decrementReferenceOnce_refines_leaf_one
      (descriptors := descriptors) mapped found live leafCell ordinary one check
  have releasedEqResult : released = result :=
    Except.ok.inj (concreteRelease.symm.trans concreteOperation)
  subst result
  have exact := canonicalHeaders mapped header headerRead
  have headerInBounds : address.value + headerBytes ≤ state.memory.size :=
    Nat.le_trans targetRelated.headerOwned related.frontier.cursorInBounds
  have finalMemory : ResidentMemoryRel released
      (releaseHeaderStore store (UInt32.ofNat address.value)).mem := by
    rw [releasedEq]
    simpa [releaseHeaderStore] using
      ResidentMemoryRel.releaseHeader memoryRelated exact headerInBounds
        headerWrite
  obtain ⟨descriptor, descriptorFound⟩ := targetRelated.descriptor
  obtain ⟨heap, rawHeader, headerLive, _, _, _⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts state address header
      headerRead
  have canonicalAfter : CanonicalMappedHeadersRel released witness :=
    canonicalHeaders.ofHeaderWrite related descriptorFound rawHeader releasedEq
      headerInBounds headerWrite
  have entry := LiveHeaderResidentFacts.ofRelations memoryRelated exact
    headerInBounds heap headerLive
  obtain ⟨ownershipHeader, ownershipRead, _, _, headerPersistentRel,
      headerRefCountRel⟩ :=
    targetRelated.ownershipHeader
  have ownershipHeaderEq : ownershipHeader = header :=
    Except.ok.inj (ownershipRead.symm.trans headerRead)
  subst ownershipHeader
  have headerOrdinary : header.persistent = false :=
    headerPersistentRel.trans ordinary
  have physicalOrdinary :
      header.flags &&& persistentFlag ≠ persistentFlag := by
    cases liveValue : header.live
    · simp [Header.flags, headerOrdinary, liveValue, persistentFlag]
    · simp [Header.flags, headerOrdinary, liveValue, persistentFlag]
      decide
  have physicalOne : header.refCount = 1 := by
    apply UInt32.toNat.inj
    simpa [one] using headerRefCountRel
  obtain ⟨notConstructor, notClosure, notOpaque⟩ :=
    FirTalos.Concrete.ResidentRelease.LiveCellRel.nonrecursiveHeaderCode
      targetRelated leafCell headerRead
  have physicalExecution :
      Wasm.wp module
        (decrementOnceProgram persistentReleaseProgram
          (lastReferenceProgram releaseHeaderIndex
            (ownedReleaseProgram constructorBody closureBody opaqueBody)))
        (fun continuation => continuation =
          .Return (releaseHeaderStore store
            (UInt32.ofNat address.value)) []) store
        (decrementEntry (UInt32.ofNat address.value) checkWord) env := by
    apply wp_decrementOnceProgram_leaf entry.taggedClear entry.objectNonzero
      entry.alignmentClear entry.flagsInBounds entry.flagsRead entry.liveSet
      entry.aux3InBounds entry.aux3Read physicalOrdinary
      entry.refCountInBounds entry.refCountRead physicalOne
      entry.kindInBounds entry.kindRead entry.aux0InBounds entry.aux0Read
      entry.aux1InBounds entry.aux1Read entry.aux2InBounds entry.aux2Read
      releaseRun notConstructor notClosure notOpaque
    rfl
  exact ⟨header, released, nextRuntime, headerRead, concreteOperation,
    semanticOperation, finalRelated, canonicalAfter, dead, finalMemory,
    physicalExecution⟩

/-- A represented live ordinary zero-count cell reaches the same ownership
fault in the concrete host and FIR semantics, while resident Wasm traps before
any write or recursive release. -/
theorem LiveHeapRel.decrementOnceProgram_underflow_refines
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {store : Wasm.Store host}
    {state : MemoryState} {witness : RefinementWitness}
    {runtime : Fir.LeanIR.Impure.RuntimeState}
    {location : Fir.LeanIR.Impure.Location} {address : Word32}
    {cell : Fir.LeanIR.Impure.HeapCell}
    {descriptors : ClosureDescriptorTable}
    {persistentProgram lastReference : Wasm.Program}
    (related : LiveHeapRel state witness runtime)
    (memoryRelated : ResidentMemoryRel state store.mem)
    (canonicalHeaders : CanonicalMappedHeadersRel state witness)
    (mapped : witness.locations.lookup? location = some address)
    (found : Fir.LeanIR.Impure.findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (ordinary : cell.persistent = false)
    (zero : cell.rc = 0) (check : Bool) (checkWord : UInt32) :
    ∃ header,
      state.readLiveHeader address = .ok header ∧
      decrementReferenceOnce state address check descriptors =
        .error (.sourceAddress (.referenceCountUnderflow address)) ∧
      Fir.LeanIR.Impure.decValueOnce runtime (.object (.heap location)) check =
        .error (.referenceCountUnderflow location) ∧
      Wasm.wp module
        (decrementOnceProgram persistentProgram lastReference)
        (fun continuation => continuation = .Trap store "unreachable") store
        (decrementEntry (UInt32.ofNat address.value) checkWord) env := by
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  obtain ⟨header, headerRead, _, _, headerPersistentRel,
      headerRefCountRel⟩ := targetRelated.ownershipHeader
  have exact := canonicalHeaders mapped header headerRead
  have headerInBounds : address.value + headerBytes ≤ state.memory.size :=
    Nat.le_trans targetRelated.headerOwned related.frontier.cursorInBounds
  obtain ⟨heap, _, headerLive, _, _, _⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts state address header
      headerRead
  have entry := LiveHeaderResidentFacts.ofRelations memoryRelated exact
    headerInBounds heap headerLive
  have headerOrdinary : header.persistent = false :=
    headerPersistentRel.trans ordinary
  have physicalOrdinary :
      header.flags &&& persistentFlag ≠ persistentFlag := by
    cases liveValue : header.live
    · simp [Header.flags, headerOrdinary, liveValue, persistentFlag]
    · simp [Header.flags, headerOrdinary, liveValue, persistentFlag]
      decide
  have physicalZero : header.refCount = 0 := by
    apply UInt32.toNat.inj
    simpa [zero] using headerRefCountRel
  have concreteOperation :=
    targetRelated.decrementReferenceOnce_underflow_eq ordinary zero check
      descriptors
  have semanticFuel :=
    targetRelated.decLocationFuel_underflow_eq ordinary zero runtime location
      found runtime.heap.length
  have semanticOperation :
      Fir.LeanIR.Impure.decValueOnce runtime (.object (.heap location)) check =
        .error (.referenceCountUnderflow location) := by
    simpa [Fir.LeanIR.Impure.decValueOnce,
      Fir.LeanIR.Impure.decLocation] using semanticFuel
  have physicalExecution :
      Wasm.wp module (decrementOnceProgram persistentProgram lastReference)
        (fun continuation => continuation = .Trap store "unreachable") store
        (decrementEntry (UInt32.ofNat address.value) checkWord) env := by
    apply wp_decrementOnceProgram_underflow entry.taggedClear
      entry.objectNonzero entry.alignmentClear entry.flagsInBounds
      entry.flagsRead entry.liveSet entry.aux3InBounds entry.aux3Read
      physicalOrdinary entry.refCountInBounds entry.refCountRead physicalZero
    rfl
  exact ⟨header, headerRead, concreteOperation, semanticOperation,
    physicalExecution⟩

/-- A represented persistent allocation is an exact no-op in all three
semantics: the concrete host, FIR ownership semantics, and resident Wasm.
The result preserves the heap simulation and the canonical-header invariant
without a memory write. -/
theorem LiveHeapRel.decrementOnceProgram_persistent_refines
    {host : Type} {module : Wasm.Module} {env : Wasm.HostEnv host}
    {store : Wasm.Store host}
    {state : MemoryState} {witness : RefinementWitness}
    {runtime : Fir.LeanIR.Impure.RuntimeState}
    {location : Fir.LeanIR.Impure.Location} {address : Word32}
    {cell : Fir.LeanIR.Impure.HeapCell}
    {descriptors : ClosureDescriptorTable}
    {lastReference : Wasm.Program}
    (related : LiveHeapRel state witness runtime)
    (memoryRelated : ResidentMemoryRel state store.mem)
    (canonicalHeaders : CanonicalMappedHeadersRel state witness)
    (mapped : witness.locations.lookup? location = some address)
    (found : Fir.LeanIR.Impure.findCell? runtime.heap location = some cell)
    (live : cell.live = true)
    (persistent : cell.persistent = true)
    (check : Bool) (checkWord : UInt32) :
    decrementReferenceOnce state address check descriptors = .ok state ∧
      Fir.LeanIR.Impure.decValueOnce runtime (.object (.heap location)) check =
        .ok runtime ∧
      LiveHeapRel state witness runtime ∧
      CanonicalMappedHeadersRel state witness ∧
      ResidentMemoryRel state store.mem ∧
      Wasm.wp module
        (decrementOnceProgram persistentReleaseProgram lastReference)
        (fun continuation => continuation = .Return store []) store
        (decrementEntry (UInt32.ofNat address.value) checkWord) env := by
  obtain ⟨mappedCell, mappedFound, cellRelation⟩ :=
    related.concreteToSemantic location address mapped
  rw [found] at mappedFound
  have cellEq := Option.some.inj mappedFound
  subst mappedCell
  have targetRelated := cellRelation.live_of_eq_true live
  obtain ⟨header, headerRead, _, notPromoted, headerPersistentRel, _⟩ :=
    targetRelated.ownershipHeader
  have headerPersistent : header.persistent = true :=
    headerPersistentRel.trans persistent
  have exact := canonicalHeaders mapped header headerRead
  have headerInBounds : address.value + headerBytes ≤ state.memory.size :=
    Nat.le_trans targetRelated.headerOwned related.frontier.cursorInBounds
  obtain ⟨heap, _, headerLive, _, _, _⟩ :=
    MemoryState.PrefixExtension.readLiveHeader_facts state address header
      headerRead
  have entry := LiveHeaderResidentFacts.ofRelations memoryRelated exact
    headerInBounds heap headerLive
  have physicalPersistent :
      header.flags &&& persistentFlag = persistentFlag := by
    have trueCase : (3 : UInt32) &&& 1 = 1 := by decide
    cases liveValue : header.live
    · simp [Header.flags, headerPersistent, liveValue, persistentFlag]
    · simpa [Header.flags, headerPersistent, liveValue, persistentFlag] using
        trueCase
  have physicalNotPromoted :
      header.kind.code ≠ ObjectKind.natural.code ∨
        header.aux0 ≠ promotedTagMarker := by
    by_cases kindNatural : header.kind = .natural
    · right
      intro marker
      have promoted : header.isPromotedTag = true := by
        have naturalEq : (ObjectKind.natural == ObjectKind.natural) = true := by
          decide
        simpa [Header.isPromotedTag, kindNatural, headerPersistent, marker]
          using naturalEq
      rw [promoted] at notPromoted
      contradiction
    · left
      intro kindCode
      apply kindNatural
      cases kindValue : header.kind <;>
        simp_all [ObjectKind.code]
  have concreteOperation :
      decrementReferenceOnce state address check descriptors = .ok state := by
    unfold decrementReferenceOnce
    exact targetRelated.decrementReferenceOnceFuel_persistent_eq persistent _
      check descriptors
  have semanticOperation :
      Fir.LeanIR.Impure.decValueOnce runtime (.object (.heap location)) check =
        .ok runtime := by
    have semanticFuel := targetRelated.decLocationFuel_persistent_eq persistent
      runtime location found runtime.heap.length
    simpa [Fir.LeanIR.Impure.decValueOnce,
      Fir.LeanIR.Impure.decLocation] using semanticFuel
  have physicalExecution :
      Wasm.wp module
        (decrementOnceProgram persistentReleaseProgram lastReference)
        (fun continuation => continuation = .Return store []) store
        (decrementEntry (UInt32.ofNat address.value) checkWord) env := by
    apply wp_decrementOnceProgram_persistent entry.taggedClear
      entry.objectNonzero entry.alignmentClear entry.flagsInBounds
      entry.flagsRead entry.liveSet entry.aux3InBounds entry.aux3Read
      physicalPersistent entry.kindInBounds entry.kindRead entry.aux0InBounds
      entry.aux0Read physicalNotPromoted
    rfl
  exact ⟨concreteOperation, semanticOperation, related, canonicalHeaders,
    memoryRelated, physicalExecution⟩

end ResidentRelease

end FirTalos.Concrete
