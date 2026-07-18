import Fir.Wasm.Concrete.ClosureCorrectness

namespace Fir.Wasm.Concrete

open Fir.LeanIR.Impure

/-- Complete local relation for one live semantic closure cell. This packages
the module-wide dispatch table, allocation descriptor, checked capture
decoder, live header, owned extent, and source-visible reference-count flags
behind one boundary that can be embedded in the exhaustive heap relation. -/
inductive ClosureCellRel (state : MemoryState) (witness : RefinementWitness)
    (address : Word32) : HeapCell → Prop where
  | closure {function : Lean.Name} {arity : Nat}
      {captureKinds : Array AbiKind} {captures : Array Value}
      {header : Header} {cell : HeapCell}
      (objectEq : cell.object = .closure function arity captures)
      (related : ClosureObjectRel state witness witness.closureDispatch
        witness.closureDescriptors address function arity captureKinds captures)
      (headerRead : state.readLiveHeader address = .ok header)
      (headerKind : header.kind = .closure)
      (extent : closureCaptureAddress address.value captures.size ≤
        state.heapCursor)
      (refCount : header.refCount.toNat = cell.rc)
      (persistent : header.persistent = cell.persistent)
      (live : cell.live = true) :
      ClosureCellRel state witness address cell

/-- Every related closure owns its common header in the concrete heap
prefix. -/
theorem ClosureCellRel.headerOwned
    {state : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : ClosureCellRel state witness address cell) :
    address.value + headerBytes ≤ state.heapCursor := by
  cases related with
  | closure _ _ _ _ extent _ _ _ =>
      simp [closureCaptureAddress, target] at extent ⊢
      omega

/-- A live closure cell remains related when a fresh allocation preserves its
complete header-and-capture prefix. -/
theorem ClosureCellRel.prefixExtension
    {before after : MemoryState} {witness : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : ClosureCellRel before witness address cell)
    (extension : before.PrefixExtension after) :
    ClosureCellRel after witness address cell := by
  cases related with
  | closure objectEq objectRelated headerRead headerKind extent refCount
      persistent live =>
      have headerOwned : address.value + headerBytes ≤ before.heapCursor := by
        simp [closureCaptureAddress, target] at extent ⊢
        omega
      exact .closure objectEq
        (objectRelated.prefixExtension extension headerOwned extent)
        (extension.readLiveHeader_eq_ok address _ headerOwned headerRead)
        headerKind (Nat.le_trans extent extension.cursor) refCount persistent live

/-- A live closure cell is monotone in proof-only witness metadata. Exact
dispatch preservation in `RefinementWitness.Extends` keeps its metadata
decoder fixed while old descriptor and value facts are transported. -/
theorem ClosureCellRel.witnessExtension
    {state : MemoryState} {before after : RefinementWitness}
    {address : Word32} {cell : HeapCell}
    (related : ClosureCellRel state before address cell)
    (extension : before.Extends after) :
    ClosureCellRel state after address cell := by
  cases related with
  | closure objectEq objectRelated headerRead headerKind extent refCount
      persistent live =>
      exact .closure objectEq (by
        rw [extension.closureDispatch, extension.closureDescriptors]
        exact objectRelated.witnessExtension extension) headerRead headerKind
        extent refCount persistent live

end Fir.Wasm.Concrete
