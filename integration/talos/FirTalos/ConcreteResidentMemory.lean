import Fir.Wasm.Concrete.Memory
import Interpreter.Wasm.Wp.Atomic

namespace FirTalos.Concrete

open Fir.Wasm.Concrete

/-!
# Wasm-resident linear-memory refinement

The concrete host and the Wasm interpreter intentionally use different
physical memory models: W6 uses a finite byte array, while Talos represents
the same Wasm memory extensionally as a byte function plus a page count.  This
relation is the shared proof boundary for resident helpers.  Instruction
proofs should transport loads and stores through it instead of restating
layout facts for each helper.
-/

/-- A Talos memory and a W6 concrete heap expose exactly the same in-bounds
bytes and the same page-aligned extent.  The explicit wasm32 bound makes
address conversion facts available without smuggling them into individual
instruction proofs. -/
structure ResidentMemoryRel (heap : MemoryState) (memory : Wasm.Mem) : Prop where
  size_eq : heap.memory.size = memory.pages * wasmPageBytes
  size_le : heap.memory.size ≤ UInt32.size
  byte_eq : ∀ address, (inBounds : address < heap.memory.size) →
    memory.bytes address = heap.memory[address]

namespace ResidentMemoryRel

/-- A physical 32-bit store leaves the number of resident memory pages
unchanged.  Stating this projection fact once keeps proofs of consecutive
stores from unfolding Talos's byte-function implementation. -/
@[simp] theorem write32_pages (memory : Wasm.Mem) (address value : UInt32) :
    (memory.write32 address value).pages = memory.pages := by
  rfl

/-- Compact store-level spelling of one physical word update.  Keeping this
opaque prevents a sequence of record updates from expanding every unchanged
`Wasm.Store` field in downstream weakest-precondition goals. -/
def write32Store (store : Wasm.Store host) (address value : UInt32) :
    Wasm.Store host :=
  { store with mem := store.mem.write32 address value }

/-- Compact store-level spelling of one physical doubleword update. -/
def write64Store (store : Wasm.Store host) (address : UInt32)
    (value : UInt64) : Wasm.Store host :=
  { store with mem := store.mem.write64 address value }

@[simp] theorem write32Store_mem
    (store : Wasm.Store host) (address value : UInt32) :
    (write32Store store address value).mem = store.mem.write32 address value := by
  rfl

@[simp] theorem write32Store_pages
    (store : Wasm.Store host) (address value : UInt32) :
    (write32Store store address value).mem.pages = store.mem.pages := by
  rfl

@[simp] theorem write64Store_mem
    (store : Wasm.Store host) (address : UInt32) (value : UInt64) :
    (write64Store store address value).mem = store.mem.write64 address value := by
  rfl

@[simp] theorem write64Store_pages
    (store : Wasm.Store host) (address : UInt32) (value : UInt64) :
    (write64Store store address value).mem.pages = store.mem.pages := by
  rfl

/-- Adjacent little-endian word updates at the physical Wasm store level. -/
def writeUInt32sMemory (memory : Wasm.Mem) (address : UInt32) :
    List UInt32 → Wasm.Mem
  | [] => memory
  | value :: rest =>
      writeUInt32sMemory (memory.write32 address value) (address + 4) rest

/-- Store-level fold corresponding to `writeUInt32sMemory`. -/
def writeUInt32sStore (store : Wasm.Store host) (address : UInt32) :
    List UInt32 → Wasm.Store host
  | [] => store
  | value :: rest =>
      writeUInt32sStore (write32Store store address value) (address + 4) rest

/-- Folding compact store updates changes only memory and is extensionally the
same adjacent-word update used by the W6/Talos memory relation. -/
theorem writeUInt32sStore_eq
    (store : Wasm.Store host) (address : UInt32) (values : List UInt32) :
    writeUInt32sStore store address values =
      { store with mem := writeUInt32sMemory store.mem address values } := by
  induction values generalizing store address with
  | nil => rfl
  | cons value rest ih =>
      simp only [writeUInt32sStore, writeUInt32sMemory]
      rw [ih]
      rfl

/-- Execute one in-bounds `i32.store` from an already prepared operand stack.
This is the instruction-level composition rule used by all resident object
writers; callers prove value production separately and continue from the
exact updated store. -/
theorem wp_store32_of_inBounds
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {locals : Wasm.Locals} {address value offset : UInt32}
    {tail : List Wasm.Value} {rest : Wasm.Program}
    (inBounds : address.toNat + offset.toNat + 4 ≤
      store.mem.pages * wasmPageBytes)
    (continued : Wasm.wp module rest Q
      (write32Store store (address + offset) value)
      { locals with values := tail } env) :
    Wasm.wp module (.store32 offset :: rest) Q store
      { locals with values := .i32 value :: .i32 address :: tail } env := by
  simpa only [write32Store, Wasm.wp_store32_cons,
    if_neg (Nat.not_lt.mpr (by simpa [wasmPageBytes] using inBounds))]
    using continued

/-- Load an address and value from arbitrary locals, then execute one checked
32-bit store.  The local-lookup premises make the rule independent of any
particular resident helper's frame layout. -/
theorem wp_store32_localGet_of_inBounds
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {locals : Wasm.Locals} {address value offset : UInt32}
    {addressIndex valueIndex : Nat} {tail : List Wasm.Value}
    {rest : Wasm.Program}
    (addressFound : locals.get addressIndex = some (.i32 address))
    (valueFound : locals.get valueIndex = some (.i32 value))
    (inBounds : address.toNat + offset.toNat + 4 ≤
      store.mem.pages * wasmPageBytes)
    (continued : Wasm.wp module rest Q
      (write32Store store (address + offset) value)
      { locals with values := tail } env) :
    Wasm.wp module
      (.localGet addressIndex :: .localGet valueIndex :: .store32 offset :: rest)
      Q store { locals with values := tail } env := by
  simp only [Wasm.wp_localGet_cons]
  have addressFound' :
      ({ locals with values := tail } : Wasm.Locals).get addressIndex =
        some (.i32 address) := by
    simpa [Wasm.Locals.get] using addressFound
  simp only [addressFound']
  have valueFound' :
      ({ locals with values := .i32 address :: tail } : Wasm.Locals).get
          valueIndex = some (.i32 value) := by
    simpa [Wasm.Locals.get] using valueFound
  simp only [valueFound']
  exact wp_store32_of_inBounds inBounds continued

/-- Load an address and `i64` value from arbitrary locals, then execute one
checked 64-bit store.  This is the doubleword counterpart of the generic
resident object-writer rule above. -/
theorem wp_store64_localGet_of_inBounds
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {locals : Wasm.Locals} {address offset : UInt32} {value : UInt64}
    {addressIndex valueIndex : Nat} {tail : List Wasm.Value}
    {rest : Wasm.Program}
    (addressFound : locals.get addressIndex = some (.i32 address))
    (valueFound : locals.get valueIndex = some (.i64 value))
    (inBounds : address.toNat + offset.toNat + 8 ≤
      store.mem.pages * wasmPageBytes)
    (continued : Wasm.wp module rest Q
      (write64Store store (address + offset) value)
      { locals with values := tail } env) :
    Wasm.wp module
      (.localGet addressIndex :: .localGet valueIndex :: .store64 offset :: rest)
      Q store { locals with values := tail } env := by
  simp only [Wasm.wp_localGet_cons]
  have addressFound' :
      ({ locals with values := tail } : Wasm.Locals).get addressIndex =
        some (.i32 address) := by
    simpa [Wasm.Locals.get] using addressFound
  simp only [addressFound']
  have valueFound' :
      ({ locals with values := .i32 address :: tail } : Wasm.Locals).get
          valueIndex = some (.i64 value) := by
    simpa [Wasm.Locals.get] using valueFound
  simp only [valueFound', Wasm.wp_store64_cons]
  rw [if_neg (Nat.not_lt.mpr (by simpa [wasmPageBytes] using inBounds))]
  simpa [write64Store] using continued

/-- Load an address local and store one constant word at a checked offset. -/
theorem wp_store32_const_of_inBounds
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {locals : Wasm.Locals} {address value offset : UInt32}
    {addressIndex : Nat} {tail : List Wasm.Value} {rest : Wasm.Program}
    (addressFound : locals.get addressIndex = some (.i32 address))
    (inBounds : address.toNat + offset.toNat + 4 ≤
      store.mem.pages * wasmPageBytes)
    (continued : Wasm.wp module rest Q
      (write32Store store (address + offset) value)
      { locals with values := tail } env) :
    Wasm.wp module
      (.localGet addressIndex :: .const value :: .store32 offset :: rest)
      Q store { locals with values := tail } env := by
  simp only [Wasm.wp_localGet_cons]
  have addressFound' :
      ({ locals with values := tail } : Wasm.Locals).get addressIndex =
        some (.i32 address) := by
    simpa [Wasm.Locals.get] using addressFound
  simp only [addressFound', Wasm.wp_const_cons]
  exact wp_store32_of_inBounds inBounds continued

/-- Load an address, add a constant to a word from another local, and store
the modular sum.  This is the common allocation-size header pattern. -/
theorem wp_store32_constAddLocalGet_of_inBounds
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {locals : Wasm.Locals} {address constant value offset : UInt32}
    {addressIndex valueIndex : Nat} {tail : List Wasm.Value}
    {rest : Wasm.Program}
    (addressFound : locals.get addressIndex = some (.i32 address))
    (valueFound : locals.get valueIndex = some (.i32 value))
    (inBounds : address.toNat + offset.toNat + 4 ≤
      store.mem.pages * wasmPageBytes)
    (continued : Wasm.wp module rest Q
      (write32Store store (address + offset) (value + constant))
      { locals with values := tail } env) :
    Wasm.wp module
      (.localGet addressIndex :: .const constant :: .localGet valueIndex ::
        .add :: .store32 offset :: rest)
      Q store { locals with values := tail } env := by
  simp only [Wasm.wp_localGet_cons]
  have addressFound' :
      ({ locals with values := tail } : Wasm.Locals).get addressIndex =
        some (.i32 address) := by
    simpa [Wasm.Locals.get] using addressFound
  simp only [addressFound', Wasm.wp_const_cons, Wasm.wp_localGet_cons]
  have valueFound' :
      ({ locals with values := .i32 constant :: .i32 address :: tail } :
          Wasm.Locals).get valueIndex = some (.i32 value) := by
    simpa [Wasm.Locals.get] using valueFound
  simp only [valueFound', Wasm.wp_add_cons]
  exact wp_store32_of_inBounds inBounds continued

/-- Return one i32 local without changing the store or the caller's operand
tail.  This closes resident writer proofs without simplifying their store
representation. -/
theorem wp_localGet_return
    {module : Wasm.Module} {env : Wasm.HostEnv host}
    {Q : Wasm.Assertion host} {store : Wasm.Store host}
    {locals : Wasm.Locals} {index : Nat} {value : UInt32}
    {tail : List Wasm.Value}
    (found : locals.get index = some (.i32 value))
    (returned : Q (.Return store (.i32 value :: tail))) :
    Wasm.wp module [.localGet index, .ret] Q store
      { locals with values := tail } env := by
  simp only [Wasm.wp_localGet_cons]
  have found' :
      ({ locals with values := tail } : Wasm.Locals).get index =
        some (.i32 value) := by
    simpa [Wasm.Locals.get] using found
  simp only [found', Wasm.wp_ret_cons]
  exact returned

/-- Writing back the word just read from one address restores the Talos
memory extensionally.  Resident ABI casts use this to justify their temporary
scratch-slot overwrite without exposing the byte proof at every call site. -/
theorem write32_read32_self (memory : Wasm.Mem) (address : UInt32) :
    memory.write32 address (memory.read32 address) = memory := by
  cases memory
  simp [Wasm.Mem.write32, Wasm.Mem.read32]
  funext other
  split <;> rename_i selected
  · subst other
    bv_decide
  split <;> rename_i selected
  · subst other
    bv_decide
  split <;> rename_i selected
  · subst other
    bv_decide
  split <;> rename_i selected
  · subst other
    bv_decide
  rfl

/-- A 32-bit Talos store is immediately observable by a matching load. -/
theorem read32_write32_self
    (memory : Wasm.Mem) (address value : UInt32) :
    (memory.write32 address value).read32 address = value := by
  cases memory
  simp [Wasm.Mem.write32, Wasm.Mem.read32]
  bv_decide

/-- A 32-bit store preserves every byte outside its four-byte lane. -/
theorem bytes_write32_of_disjoint
    (memory : Wasm.Mem) (address value : UInt32) (byte : Nat)
    (disjoint : byte < address.toNat ∨ address.toNat + 3 < byte) :
    (memory.write32 address value).bytes byte = memory.bytes byte := by
  have different0 : byte ≠ address.toNat := by omega
  have different1 : byte ≠ address.toNat + 1 := by omega
  have different2 : byte ≠ address.toNat + 2 := by omega
  have different3 : byte ≠ address.toNat + 3 := by omega
  simp [Wasm.Mem.write32, different0, different1, different2, different3]

/-- A 32-bit store preserves a disjoint 32-bit read.  The premise is stated
on unbounded byte addresses; callers deriving it from wasm32 arithmetic must
therefore make nonwraparound explicit. -/
theorem read32_write32_disjoint
    (memory : Wasm.Mem) (written read value : UInt32)
    (disjoint : written.toNat + 3 < read.toNat ∨
      read.toNat + 3 < written.toNat) :
    (memory.write32 written value).read32 read = memory.read32 read := by
  simp only [Wasm.Mem.read32]
  rw [bytes_write32_of_disjoint memory written value read.toNat (by omega)]
  rw [bytes_write32_of_disjoint memory written value (read.toNat + 1)
    (by omega)]
  rw [bytes_write32_of_disjoint memory written value (read.toNat + 2)
    (by omega)]
  rw [bytes_write32_of_disjoint memory written value (read.toNat + 3)
    (by omega)]

/-- Restoring the word observed before a temporary 32-bit overwrite recovers
the original memory, including every byte outside the scratch lane. -/
theorem write32_restore (memory : Wasm.Mem) (address value : UInt32) :
    (memory.write32 address value).write32 address
        (memory.read32 address) = memory := by
  cases memory
  simp [Wasm.Mem.write32, Wasm.Mem.read32]
  funext other
  split <;> rename_i selected
  · subst other
    bv_decide
  split <;> rename_i selected
  · subst other
    bv_decide
  split <;> rename_i selected
  · subst other
    bv_decide
  split <;> rename_i selected
  · subst other
    bv_decide
  rfl

set_option linter.unusedSimpArgs false in
/-- Writing back the 64-bit lane just read from one address restores the
Talos memory extensionally.  `USize.ofNat` uses this at its scratch-memory
retyping boundary. -/
theorem write64_read64_self (memory : Wasm.Mem) (address : UInt32) :
    memory.write64 address (memory.read64 address) = memory := by
  cases memory
  simp [Wasm.Mem.write64, Wasm.Mem.read64]
  funext other
  by_cases selected0 : other = address.toNat
  · subst other
    simp (config := { maxSteps := 4000000 })
    bv_decide
  by_cases selected1 : other = address.toNat + 1
  · subst other
    simp (config := { maxSteps := 4000000 }) [selected0]
    bv_decide
  by_cases selected2 : other = address.toNat + 2
  · subst other
    simp (config := { maxSteps := 4000000 }) [selected0, selected1]
    bv_decide
  by_cases selected3 : other = address.toNat + 3
  · subst other
    simp (config := { maxSteps := 4000000 })
      [selected0, selected1, selected2]
    bv_decide
  by_cases selected4 : other = address.toNat + 4
  · subst other
    simp (config := { maxSteps := 4000000 })
      [selected0, selected1, selected2, selected3]
    bv_decide
  by_cases selected5 : other = address.toNat + 5
  · subst other
    simp (config := { maxSteps := 4000000 })
      [selected0, selected1, selected2, selected3, selected4]
    bv_decide
  by_cases selected6 : other = address.toNat + 6
  · subst other
    simp (config := { maxSteps := 4000000 })
      [selected0, selected1, selected2, selected3, selected4, selected5]
    bv_decide
  by_cases selected7 : other = address.toNat + 7
  · subst other
    simp (config := { maxSteps := 4000000 })
      [selected0, selected1, selected2, selected3, selected4, selected5,
        selected6]
    bv_decide
  simp [selected0, selected1, selected2, selected3, selected4, selected5,
    selected6, selected7]

/-- A 64-bit Talos store is immediately observable by a matching load. -/
theorem read64_write64_self
    (memory : Wasm.Mem) (address : UInt32) (value : UInt64) :
    (memory.write64 address value).read64 address = value := by
  cases memory
  simp [Wasm.Mem.write64, Wasm.Mem.read64]
  bv_decide

set_option linter.unusedSimpArgs false in
/-- Restoring the lane observed before a temporary 64-bit overwrite recovers
the original memory byte for byte. -/
theorem write64_restore
    (memory : Wasm.Mem) (address : UInt32) (value : UInt64) :
    (memory.write64 address value).write64 address
        (memory.read64 address) = memory := by
  cases memory
  simp [Wasm.Mem.write64, Wasm.Mem.read64]
  funext other
  by_cases selected0 : other = address.toNat
  · subst other
    simp (config := { maxSteps := 4000000 })
    bv_decide
  by_cases selected1 : other = address.toNat + 1
  · subst other
    simp (config := { maxSteps := 4000000 }) [selected0]
    bv_decide
  by_cases selected2 : other = address.toNat + 2
  · subst other
    simp (config := { maxSteps := 4000000 }) [selected0, selected1]
    bv_decide
  by_cases selected3 : other = address.toNat + 3
  · subst other
    simp (config := { maxSteps := 4000000 })
      [selected0, selected1, selected2]
    bv_decide
  by_cases selected4 : other = address.toNat + 4
  · subst other
    simp (config := { maxSteps := 4000000 })
      [selected0, selected1, selected2, selected3]
    bv_decide
  by_cases selected5 : other = address.toNat + 5
  · subst other
    simp (config := { maxSteps := 4000000 })
      [selected0, selected1, selected2, selected3, selected4]
    bv_decide
  by_cases selected6 : other = address.toNat + 6
  · subst other
    simp (config := { maxSteps := 4000000 })
      [selected0, selected1, selected2, selected3, selected4, selected5]
    bv_decide
  by_cases selected7 : other = address.toNat + 7
  · subst other
    simp (config := { maxSteps := 4000000 })
      [selected0, selected1, selected2, selected3, selected4, selected5,
        selected6]
    bv_decide
  simp [selected0, selected1, selected2, selected3, selected4, selected5,
    selected6, selected7]

set_option linter.unusedSimpArgs false in
/-- Restoring the original 64-bit lane after a temporary 32-bit overwrite
recovers the complete memory byte for byte.  Object-valued resident helpers
use this mixed-width form: the raw object word occupies the low half of the
scratch lane, while the saved value protects all eight bytes. -/
theorem write64_restore_after_write32
    (memory : Wasm.Mem) (address value : UInt32) :
    (memory.write32 address value).write64 address
        (memory.read64 address) = memory := by
  cases memory
  simp [Wasm.Mem.write32, Wasm.Mem.write64, Wasm.Mem.read64]
  funext other
  by_cases selected0 : other = address.toNat
  · subst other
    simp (config := { maxSteps := 4000000 })
    bv_decide
  by_cases selected1 : other = address.toNat + 1
  · subst other
    simp (config := { maxSteps := 4000000 }) [selected0]
    bv_decide
  by_cases selected2 : other = address.toNat + 2
  · subst other
    simp (config := { maxSteps := 4000000 }) [selected0, selected1]
    bv_decide
  by_cases selected3 : other = address.toNat + 3
  · subst other
    simp (config := { maxSteps := 4000000 })
      [selected0, selected1, selected2]
    bv_decide
  by_cases selected4 : other = address.toNat + 4
  · subst other
    simp (config := { maxSteps := 4000000 })
      [selected0, selected1, selected2, selected3]
    bv_decide
  by_cases selected5 : other = address.toNat + 5
  · subst other
    simp (config := { maxSteps := 4000000 })
      [selected0, selected1, selected2, selected3, selected4]
    bv_decide
  by_cases selected6 : other = address.toNat + 6
  · subst other
    simp (config := { maxSteps := 4000000 })
      [selected0, selected1, selected2, selected3, selected4, selected5]
    bv_decide
  by_cases selected7 : other = address.toNat + 7
  · subst other
    simp (config := { maxSteps := 4000000 })
      [selected0, selected1, selected2, selected3, selected4, selected5,
        selected6]
    bv_decide
  simp [selected0, selected1, selected2, selected3, selected4, selected5,
    selected6, selected7]

theorem initial :
    ResidentMemoryRel MemoryState.initial (Wasm.Mem.empty 1) := by
  constructor
  · simp [MemoryState.initial, LinearMemory.withPages, Wasm.Mem.empty,
      wasmPageBytes]
  · simp [MemoryState.initial, LinearMemory.withPages, UInt32.size,
      wasmPageBytes]
  · intro address inBounds
    simp [MemoryState.initial, LinearMemory.withPages, Wasm.Mem.empty]

theorem address_lt_uint32
    {heap : MemoryState} {memory : Wasm.Mem}
    (related : ResidentMemoryRel heap memory)
    {address bytes : Nat}
    (inBounds : address + bytes < heap.memory.size) :
    address < UInt32.size := by
  have addressInBounds : address < heap.memory.size := by omega
  exact Nat.lt_of_lt_of_le addressInBounds related.size_le

theorem address_roundtrip
    {heap : MemoryState} {memory : Wasm.Mem}
    (related : ResidentMemoryRel heap memory)
    {address bytes : Nat}
    (inBounds : address + bytes < heap.memory.size) :
    (UInt32.ofNat address).toNat = address := by
  exact UInt32.toNat_ofNat_of_lt' (related.address_lt_uint32 inBounds)

theorem readByte_eq
    {heap : MemoryState} {memory : Wasm.Mem}
    (related : ResidentMemoryRel heap memory)
    {address : Nat} (inBounds : address < heap.memory.size) :
    heap.memory.readByte address = .ok (memory.bytes address) := by
  simp [LinearMemory.readByte, inBounds, related.byte_eq address inBounds]

theorem readByte_eq_read8
    {heap : MemoryState} {memory : Wasm.Mem}
    (related : ResidentMemoryRel heap memory)
    {address : Nat} (inBounds : address < heap.memory.size) :
    heap.memory.readByte address =
      .ok (memory.read8 (UInt32.ofNat address)) := by
  rw [related.readByte_eq inBounds]
  simp [Wasm.Mem.read8,
    UInt32.toNat_ofNat_of_lt' (related.address_lt_uint32 (bytes := 0) inBounds)]

theorem readUInt32_eq_read32
    {heap : MemoryState} {memory : Wasm.Mem}
    (related : ResidentMemoryRel heap memory)
    {address : Nat} (inBounds : address + 3 < heap.memory.size) :
    heap.memory.readUInt32 address =
      .ok (memory.read32 (UInt32.ofNat address)) := by
  have h0 : address < heap.memory.size := by omega
  have h1 : address + 1 < heap.memory.size := by omega
  have h2 : address + 2 < heap.memory.size := by omega
  have h3 : address + 3 < heap.memory.size := inBounds
  unfold LinearMemory.readUInt32
  rw [related.readByte_eq h0, related.readByte_eq h1,
    related.readByte_eq h2, related.readByte_eq h3]
  simp only [bind, Except.bind, pure, Except.pure]
  congr 1
  unfold Wasm.Mem.read32
  rw [related.address_roundtrip inBounds]
  simp only [related.byte_eq address h0, related.byte_eq (address + 1) h1,
    related.byte_eq (address + 2) h2, related.byte_eq (address + 3) h3]
  bv_decide

/-- A checked little-endian W6 doubleword read exposes the same exact `i64`
lane to resident Wasm.  Keeping this transport at the byte relation boundary
lets scalar, numeric, and closure helpers share one proof of the physical
64-bit representation. -/
theorem readUInt64_eq_read64
    {heap : MemoryState} {memory : Wasm.Mem}
    (related : ResidentMemoryRel heap memory)
    {address : Nat} (inBounds : address + 7 < heap.memory.size) :
    heap.memory.readUInt64 address =
      .ok (memory.read64 (UInt32.ofNat address)) := by
  have lowInBounds : address + 3 < heap.memory.size := by omega
  have highInBounds : address + 4 + 3 < heap.memory.size := by omega
  unfold LinearMemory.readUInt64
  rw [related.readUInt32_eq_read32 lowInBounds,
    related.readUInt32_eq_read32 highInBounds]
  simp only [bind, Except.bind, pure, Except.pure]
  congr 1
  unfold Wasm.Mem.read64 Wasm.Mem.read32
  rw [related.address_roundtrip inBounds,
    related.address_roundtrip highInBounds]
  have offset5 : address + 4 + 1 = address + 5 := by omega
  have offset6 : address + 4 + 2 = address + 6 := by omega
  have offset7 : address + 4 + 3 = address + 7 := by omega
  rw [offset5, offset6, offset7]
  bv_decide

/-- A successful W6 mathematical-word read exposes the same exact i32 lane
to resident Wasm.  This packages the checked `Word32` reconstruction so
ownership traversals can reason directly about their child argument. -/
theorem readWord32_eq_read32
    {heap : MemoryState} {memory : Wasm.Mem}
    (related : ResidentMemoryRel heap memory)
    {address : Nat} {word : Word32}
    (inBounds : address + 3 < heap.memory.size)
    (read : heap.memory.readWord32 address = .ok word) :
    memory.read32 (UInt32.ofNat address) = UInt32.ofNat word.value := by
  unfold LinearMemory.readWord32 at read
  rw [related.readUInt32_eq_read32 inBounds] at read
  simp only [bind, Except.bind] at read
  cases recovered :
      Word32.ofNat? (memory.read32 (UInt32.ofNat address)).toNat with
  | none => simp [recovered] at read
  | some actual =>
      simp only [recovered, pure, Except.pure] at read
      have actualEq := Except.ok.inj read
      subst actual
      unfold Word32.ofNat? at recovered
      split at recovered
      · have sameWord := Option.some.inj recovered
        have valueEq := congrArg Word32.value sameWord
        apply UInt32.toNat.inj
        rw [UInt32.toNat_ofNat_of_lt' (by
          simpa [wordModulus] using word.isLt)]
        exact valueEq
      · simp at recovered

/-- One Wasm `i32.store` and W6's checked 32-bit store preserve the common
memory relation.  This is the byte-level frame theorem used by allocator,
header, field, cache, and scratch-slot proofs. -/
theorem writeUInt32
    {heap : MemoryState} {memory : Wasm.Mem}
    (related : ResidentMemoryRel heap memory)
    {address : Nat} {value : UInt32} {result : LinearMemory}
    (inBounds : address + 3 < heap.memory.size)
    (written : heap.memory.writeUInt32 address value = .ok result) :
    ResidentMemoryRel { heap with memory := result }
      (memory.write32 (UInt32.ofNat address) value) := by
  obtain ⟨actual, actualWrite, actualSize, byte0, byte1, byte2, byte3, frame⟩ :=
    LinearMemory.writeUInt32_spec heap.memory address value inBounds
  rw [actualWrite] at written
  cases written
  have roundtrip : (UInt32.ofNat address).toNat = address :=
    related.address_roundtrip inBounds
  have h0 : address < result.size := by simpa [actualSize] using (by omega :
    address < heap.memory.size)
  have h1 : address + 1 < result.size := by simpa [actualSize] using (by omega :
    address + 1 < heap.memory.size)
  have h2 : address + 2 < result.size := by simpa [actualSize] using (by omega :
    address + 2 < heap.memory.size)
  have h3 : address + 3 < result.size := by simpa [actualSize] using inBounds
  have at0 : result[address] = (value &&& 0xff).toUInt8 := by
    simp [LinearMemory.readByte, h0] at byte0
    rw [byte0]
    simp [LinearMemory.byte32]
    bv_decide
  have at1 : result[address + 1] = ((value >>> 8) &&& 0xff).toUInt8 := by
    simp [LinearMemory.readByte, h1] at byte1
    rw [byte1]
    simp [LinearMemory.byte32]
    bv_decide
  have at2 : result[address + 2] = ((value >>> 16) &&& 0xff).toUInt8 := by
    simp [LinearMemory.readByte, h2] at byte2
    rw [byte2]
    simp [LinearMemory.byte32]
    bv_decide
  have at3 : result[address + 3] = ((value >>> 24) &&& 0xff).toUInt8 := by
    simp [LinearMemory.readByte, h3] at byte3
    rw [byte3]
    simp [LinearMemory.byte32]
    bv_decide
  constructor
  · simpa [Wasm.Mem.write32, actualSize] using related.size_eq
  · simpa [actualSize] using related.size_le
  · intro other otherInBounds
    simp only [Wasm.Mem.write32, roundtrip]
    by_cases eq0 : other = address
    · subst other
      simpa using at0.symm
    by_cases eq1 : other = address + 1
    · subst other
      simp [at1]
    by_cases eq2 : other = address + 2
    · subst other
      simp [at2]
    by_cases eq3 : other = address + 3
    · subst other
      simp [at3]
    simp only [eq0, eq1, eq2, eq3, if_false]
    have originalInBounds : other < heap.memory.size := by
      simpa [actualSize] using otherInBounds
    have unchanged : LinearMemory.readByte result other =
        LinearMemory.readByte heap.memory other :=
      frame other (Ne.symm eq0) (Ne.symm eq1) (Ne.symm eq2) (Ne.symm eq3)
    simp [LinearMemory.readByte, otherInBounds, originalInBounds] at unchanged
    rw [unchanged]
    exact related.byte_eq other originalInBounds

/-- One checked W6 64-bit write and one resident `i64.store` preserve the
common memory relation.  The proof factors through the already-verified pair
of adjacent 32-bit stores and then identifies that pair with Talos's canonical
little-endian 64-bit update. -/
theorem writeUInt64
    {heap : MemoryState} {memory : Wasm.Mem}
    (related : ResidentMemoryRel heap memory)
    {address : Nat} {value : UInt64} {result : LinearMemory}
    (inBounds : address + 7 < heap.memory.size)
    (written : heap.memory.writeUInt64 address value = .ok result) :
    ResidentMemoryRel { heap with memory := result }
      (memory.write64 (UInt32.ofNat address) value) := by
  obtain ⟨middle, lowWrite, middleSize, highWrite⟩ :=
    LinearMemory.writeUInt64_decompose heap.memory result address value
      inBounds written
  have lowRelated := related.writeUInt32 (by omega) lowWrite
  have highRelated := lowRelated.writeUInt32 (by
    simpa [middleSize] using (show address + 4 + 3 < heap.memory.size by
      omega)) highWrite
  have addressRoundtrip : (UInt32.ofNat address).toNat = address :=
    related.address_roundtrip inBounds
  have highInBounds : address + 4 + 3 < heap.memory.size := by omega
  have highAddressRoundtrip : (UInt32.ofNat (address + 4)).toNat = address + 4 :=
    related.address_roundtrip (address := address + 4) (bytes := 3)
      highInBounds
  have physicalEq :
      (memory.write32 (UInt32.ofNat address) value.toUInt32).write32
          (UInt32.ofNat (address + 4))
          (value >>> (32 : UInt64)).toUInt32 =
        memory.write64 (UInt32.ofNat address) value := by
    cases memory
    simp only [Wasm.Mem.write32, Wasm.Mem.write64, addressRoundtrip,
      highAddressRoundtrip]
    congr 1
    funext other
    by_cases eq0 : other = address
    · subst other
      simp (config := { maxSteps := 4000000 }) [Nat.add_assoc]
    by_cases eq1 : other = address + 1
    · subst other
      simp (config := { maxSteps := 4000000 }) [Nat.add_assoc]
      bv_decide
    by_cases eq2 : other = address + 2
    · subst other
      simp (config := { maxSteps := 4000000 }) [Nat.add_assoc]
      bv_decide
    by_cases eq3 : other = address + 3
    · subst other
      simp (config := { maxSteps := 4000000 }) [Nat.add_assoc]
      bv_decide
    by_cases eq4 : other = address + 4
    · subst other
      simp (config := { maxSteps := 4000000 })
    by_cases eq5 : other = address + 5
    · subst other
      simp (config := { maxSteps := 4000000 }) [Nat.add_assoc]
      bv_decide
    by_cases eq6 : other = address + 6
    · subst other
      simp (config := { maxSteps := 4000000 }) [Nat.add_assoc]
      bv_decide
    by_cases eq7 : other = address + 7
    · subst other
      simp (config := { maxSteps := 4000000 }) [Nat.add_assoc]
      bv_decide
    simp [Nat.add_assoc, eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7]
  rw [physicalEq] at highRelated
  exact highRelated

end ResidentMemoryRel

/-- Store-level packaging used by resident instruction and helper theorems.
More resident globals, starting with the allocator cursor, can be added here
without changing the byte-level relation. -/
structure ResidentStoreRel (heap : MemoryState) (store : Wasm.Store α) : Prop where
  memory : ResidentMemoryRel heap store.mem

end FirTalos.Concrete
