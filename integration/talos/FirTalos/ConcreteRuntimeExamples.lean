import FirTalos.ConcreteResolver
import FirTalos.DifferentialExamples
import Fir.Wasm.Examples
import Fir.Wasm.Emit.Examples
import Interpreter.Wasm.Semantics

namespace FirTalos.Concrete

open Lean.Compiler
open Fir.LeanIR.Impure
open Fir.LeanIR.InterpreterExamples
open Fir.Wasm.Concrete

private structure RuntimeFixture where
  source : Fir.Wasm.Module
  target : Wasm.Module
  hosts : ResolvedHosts

private def runtimeFixture? (program : Fir.LeanIR.ImpureProgram) :
    Option RuntimeFixture := do
  let source ← match Fir.Wasm.lower program with
    | .ok source => some source
    | .error _ => none
  let adapted ← match FirTalos.adapt source with
    | .ok adapted => some adapted
    | .error _ => none
  let hosts ← match resolveHosts source with
    | .ok hosts => some hosts
    | .error _ => none
  return { source, target := adapted.wasmModule, hosts }

private def RuntimeFixture.importsResolveExactly (fixture : RuntimeFixture) : Bool :=
  fixture.source.imports.size == fixture.hosts.hosts.length &&
    fixture.target.imports.length == fixture.hosts.env.funcs.length &&
    fixture.hosts.env.funcs.length == fixture.hosts.spec.contracts.length &&
    (fixture.source.imports.toList.zip fixture.hosts.hosts).all fun pair =>
      pair.fst.key == pair.snd.key &&
        pair.snd.function.params ==
          pair.fst.signature.params.toList.map FirTalos.abiKind &&
        pair.snd.function.results ==
          pair.fst.signature.results.toList.map FirTalos.abiKind

private def RuntimeFixture.runMain (fixture : RuntimeFixture) : Wasm.Result Host :=
  Wasm.run 100 fixture.target ((fixture.target.findExport "main").getD 0)
    (initialStore fixture.source fixture.target) [] fixture.hosts.env

private def RuntimeFixture.runMainWithExternals (fixture : RuntimeFixture)
    (externals : Fir.Wasm.Concrete.ConcreteExternalImpl) : Wasm.Result Host :=
  Wasm.run 100 fixture.target ((fixture.target.findExport "main").getD 0)
    (initialStore fixture.source fixture.target externals) [] fixture.hosts.env

private def fixtureReturnsWord? (program : Fir.LeanIR.ImpureProgram)
    (expected : UInt32) : Bool :=
  (runtimeFixture? program).any fun fixture =>
    fixture.importsResolveExactly &&
      match fixture.runMain with
      | .Success [.i32 result] store =>
          result == expected && store.host.failure?.isNone
      | _ => false

private def fixtureReturnsI64? (program : Fir.LeanIR.ImpureProgram)
    (expected : UInt64) : Bool :=
  (runtimeFixture? program).any fun fixture =>
    fixture.importsResolveExactly &&
      match fixture.runMain with
      | .Success [.i64 result] store =>
          result == expected && store.host.failure?.isNone
      | _ => false

-- Complete lowered modules now execute against concrete linear memory rather
-- than semantic handles for the first artifact-ready fragment.
#guard fixtureReturnsWord? Fir.Wasm.abiLiteralProgram 85

-- The first heap allocation begins at the frozen aligned concrete frontier.
#guard fixtureReturnsWord? FirTalos.abiStringProgram 1024

#guard fixtureReturnsWord? Fir.Wasm.abiCtorProjectionProgram 15

#guard fixtureReturnsWord? Fir.Wasm.abiCaseProgram 3

#guard fixtureReturnsWord? Fir.Wasm.abiDefaultCaseProgram 11

#guard fixtureReturnsI64? FirTalos.abiUSizeProjectionProgram 0

private def acceptedScalarLayoutMismatchIsStructured : Bool :=
  match runtimeFixture? Fir.Wasm.abiMutationProgram with
  | some fixture =>
      fixture.importsResolveExactly &&
        match fixture.runMain with
        | .Trap store _ =>
            store.host.failure? == some (.runtime (.source (.runtime
              (.scalarFieldMissing 1 0))))
        | _ => false
  | none => false

#guard acceptedScalarLayoutMismatchIsStructured

/-- The positive scalar-mutation fixture uses the exact slot index emitted by
Lean 4.32's `ToImpure`: object fields plus `USize` fields. -/
private def compilerShapedScalarMutationProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] u64Type (.code <|
      .let (letDecl x LCNF.ImpureType.tobject (.lit (.nat 1))) <|
      .let (letDecl y LCNF.ImpureType.tobject (.lit (.nat 2))) <|
      .let (letDecl p objType (.ctor layoutInfo #[.fvar x])) <|
      .let (letDecl u usizeType (.lit (.usize 55))) <|
      .uset p 0 u <|
      .let (letDecl s u64Type (.lit (.uint64 66))) <|
      .sset p 2 0 s u64Type <|
      .oset p 0 (.fvar y) <|
      .setTag p 4 <|
      .let (letDecl r u64Type (.sproj 2 0 p)) <|
      .return r)] }

#guard fixtureReturnsI64? compilerShapedScalarMutationProgram 66

-- The remaining packed-integer widths cross the same complete
-- lowering/adapter/resolver/concrete-host path and return on wasm32 lanes.
#guard fixtureReturnsWord? Fir.Wasm.Emit.Examples.abiUInt8MutationProgram 255

#guard fixtureReturnsWord? Fir.Wasm.Emit.Examples.abiUInt16MutationProgram 65535

#guard fixtureReturnsWord? Fir.Wasm.Emit.Examples.abiUInt32MutationProgram
  4294967295

/-- The replacement proof boundary is executable: a second write to the same
packed coordinate supersedes the first source field and concrete bytes. -/
private def repeatedScalarMutationProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] u64Type (.code <|
      .let (letDecl x LCNF.ImpureType.tobject (.lit (.nat 1))) <|
      .let (letDecl p objType (.ctor layoutInfo #[.fvar x])) <|
      .let (letDecl s u64Type (.lit (.uint64 66))) <|
      .sset p 2 0 s u64Type <|
      .let (letDecl u u64Type (.lit (.uint64 77))) <|
      .sset p 2 0 u u64Type <|
      .let (letDecl r u64Type (.sproj 2 0 p)) <|
      .return r)] }

#guard fixtureReturnsI64? repeatedScalarMutationProgram 77

private def decrementGraphProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] LCNF.ImpureType.tobject (.code <|
      .let (letDecl x LCNF.ImpureType.tobject (.lit (.nat 10))) <|
      .let (letDecl p objType
        (.ctor { pairInfo with size := 1 } #[.fvar x])) <|
      .dec p 1 true false (some 1) <|
      .let (letDecl r LCNF.ImpureType.tobject (.lit (.nat 12))) <|
      .return r)] }

#guard fixtureReturnsWord? decrementGraphProgram 25

private def deleteObjectProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] LCNF.ImpureType.tobject (.code <|
      .let (letDecl x LCNF.ImpureType.tobject (.lit (.nat 20))) <|
      .let (letDecl p objType
        (.ctor { pairInfo with size := 1 } #[.fvar x])) <|
      .del p <|
      .let (letDecl r LCNF.ImpureType.tobject (.lit (.nat 22))) <|
      .return r)] }

#guard fixtureReturnsWord? deleteObjectProgram 45

private def cachedHeapDecl : LCNF.Decl .impure :=
  decl `FirTalos.Concrete.cachedHeap #[] objType (.code <|
    .let (letDecl x LCNF.ImpureType.tobject (.lit (.nat 42))) <|
    .let (letDecl p objType
      (.ctor { pairInfo with size := 1 } #[.fvar x])) <|
    .return p)

private def cachedQ : Lean.FVarId := Lean.FVarId.mk `cachedQ

private def cachedHeapProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[cachedHeapDecl,
      decl `main #[] LCNF.ImpureType.tobject (.code <|
        .let (letDecl p objType
          (.fap `FirTalos.Concrete.cachedHeap #[])) <|
        .let (letDecl cachedQ objType
          (.fap `FirTalos.Concrete.cachedHeap #[])) <|
        .let (letDecl r LCNF.ImpureType.tobject (.oproj 0 cachedQ)) <|
        .return r)] }

#guard fixtureReturnsWord? cachedHeapProgram 85

#guard fixtureReturnsWord? Fir.Wasm.abiObjectMutationProgram 177

/-- Erased object arguments remain canonical physical zeroes across allocation,
mutation, projection, and the complete generated-module return path. -/
private def erasedObjectMutationProgram : Fir.LeanIR.ImpureProgram :=
  { decls := #[decl `main #[] LCNF.ImpureType.erased (.code <|
      .let (letDecl p objType
        (.ctor { pairInfo with size := 1 } #[.erased])) <|
      .oset p 0 .erased <|
      .let (letDecl r LCNF.ImpureType.erased (.oproj 0 p)) <|
      .return r)] }

#guard fixtureReturnsWord? erasedObjectMutationProgram 0

#guard fixtureReturnsWord? Fir.Wasm.abiTagMutationProgram 199

#guard fixtureReturnsI64?
  (FirTalos.abiBoxRoundtripProgram FirTalos.differentialMaxUInt64)
  FirTalos.differentialMaxUInt64

#guard fixtureReturnsWord? FirTalos.abiIsSharedTaggedProgram 1

#guard fixtureReturnsWord? FirTalos.abiIsSharedUniqueProgram 0

#guard fixtureReturnsWord? Fir.Wasm.abiResetReuseProgram 143

#guard fixtureReturnsWord? Fir.Wasm.abiSharedResetProgram 163

#guard fixtureReturnsWord? Fir.Wasm.abiDirectCallProgram 23

-- Closure headers use module-derived dispatch and capture-descriptor tables.
-- This complete call allocates one closure, matches its metadata, projects the
-- fixed capture, and invokes the lowered declaration directly.
#guard fixtureReturnsWord? Fir.Wasm.abiClosureCallProgram 43

-- Successive underapplication extends the capture layout from one to two
-- fields before the final generated trampoline dispatches the three-argument
-- call. Both descriptor rows are derived from the module's runtime operations.
#guard fixtureReturnsWord? Fir.Wasm.abiClosureUnderApplyProgram 63

-- Erased captures occupy their canonical physical slot but need no metadata
-- projection in the generated trampoline.
#guard fixtureReturnsWord? Fir.Wasm.abiClosureErasedCaptureProgram 47

-- Recursive direct calls share the same generated-function index space used
-- by closure dispatch and remain executable under the concrete host store.
#guard fixtureReturnsWord? Fir.Wasm.abiRecursiveCallProgram 41

-- String literals now resolve to the executable UTF-8 concrete host.
#guard (hostFn? (.literal (.str "concrete") .object)).isSome

/-- Closed initial-state instance of the string-allocation refinement used by
the generated literal rule. -/
theorem initialUnicodeString_liveHeapRel
    (heap : MemoryState) (word : Word32)
    (allocated : allocateString MemoryState.initial "hello α_world_β" =
      .ok (heap, word)) :
    ∃ nextWitness,
      (initialWitness #[] #[]).Extends nextWitness ∧
      LiveHeapRel heap nextWitness
        (literal ({} : RuntimeState) (.str "hello α_world_β")).1 ∧
      ValueRel nextWitness .object (.word32 word)
        (literal ({} : RuntimeState) (.str "hello α_world_β")).2 := by
  exact allocateString_liveHeapRel_extends MemoryState.initial heap
    (initialWitness #[] #[]) ({} : RuntimeState) "hello α_world_β" word
    (LiveHeapRel.initial #[] #[]) allocated

-- Remaining unsupported runtime families are rejected by resolution rather
-- than reaching a concrete host that only traps after instantiation.
#guard (hostFn? (.scalarProj 1 0 .float32)).isNone

private def echoConcreteExternal : Fir.Wasm.Concrete.ConcreteExternalImpl where
  call request before :=
    match request.args[0]? with
    | some value => .ok {
        value
        heap := before.heap
        world := before.world + 1 }
    | none =>
        .error (.source (.externalFailure request.name "missing argument"))

/-- The complete lowered external fixture resolves its source metadata,
decodes UInt64 directly from the i64 lane, updates concrete world/trace state,
and returns the same physical lane without a semantic handle table. -/
private def externalFixtureReturnsAndRecords : Bool :=
  (runtimeFixture? externalProgram).any fun fixture =>
    fixture.importsResolveExactly &&
      match fixture.runMainWithExternals echoConcreteExternal with
      | .Success [.i64 result] store =>
          result == 90 && store.host.failure?.isNone &&
            store.host.runtime.world == 1 &&
            store.host.runtime.trace.size == 1 &&
            store.host.runtime.trace[0]?.any fun event =>
              event.name == `external &&
                event.paramKinds == #[.uint64] &&
                event.resultKind == .uint64 &&
                match event.args[0]?, event.result with
                | some (LaneValue.word64 argument),
                    LaneValue.word64 returned =>
                    event.args.size == 1 && argument == 90 && returned == 90
                | _, _ => false
      | _ => false

#guard externalFixtureReturnsAndRecords

private def externalFixtureRejectsByDefault : Bool :=
  (runtimeFixture? externalProgram).any fun fixture =>
    fixture.importsResolveExactly &&
      match fixture.runMain with
      | .Trap store _ =>
          store.host.failure? == some (.runtime (.source (.runtime
            (.externalFailure `external
              "no concrete external implementation installed"))))
      | _ => false

#guard externalFixtureRejectsByDefault

private def wrongLaneConcreteExternal :
    Fir.Wasm.Concrete.ConcreteExternalImpl where
  call _ before := .ok {
    value := .word32 (Word32.ofUInt32 90)
    heap := before.heap
    world := before.world }

private def externalFixtureRejectsWrongResultLane : Bool :=
  (runtimeFixture? externalProgram).any fun fixture =>
    fixture.importsResolveExactly &&
      match fixture.runMainWithExternals wrongLaneConcreteExternal with
      | .Trap store _ =>
          store.host.failure? == some (.resultLaneMismatch .i64 .i32)
      | _ => false

#guard externalFixtureRejectsWrongResultLane

private def emptyHostStore : Wasm.Store Host :=
  ({ funcs := [] } : Wasm.Module).initialStore

-- Non-ASCII literals retain the exact canonical UTF-8 bytes and frozen header
-- metadata at the concrete host boundary.
#guard match stringLiteralStep "hello α_world_β" emptyHostStore [] with
  | .Return [.i32 bits] store =>
      let address := Word32.ofUInt32 bits
      match store.host.runtime.heap.readLiveHeader address,
          readStringPayload store.host.runtime.heap address with
      | .ok header, .ok bytes =>
          header.kind == .string && header.aux0 == stringUtf8Marker &&
            header.aux1.toNat == bytes.length && header.aux2 == 0 &&
            header.aux3 == 0 &&
            bytes == stringUtf8Bytes "hello α_world_β"
      | _, _ => false
  | _ => false

-- The executable concrete host decodes immediate object words without any
-- semantic handle table.
#guard match getTagStep emptyHostStore [.i32 15] with
  | .Return [.i32 tag] store =>
      tag == 7 && store.host.failure?.isNone
  | _ => false

-- ABI arity failures are retained separately from checked heap failures.
#guard match getTagStep emptyHostStore [] with
  | .Trap store _ =>
      store.host.failure? == some (.arityMismatch 1 0)
  | _ => false

-- A correctly sized call with the wrong physical lane has its own diagnosis.
#guard match getTagStep emptyHostStore [.i64 0] with
  | .Trap store _ =>
      store.host.failure? == some (.laneMismatch 0 .i32)
  | _ => false

private def projectionInfo : Lean.Compiler.LCNF.CtorInfo := {
  name := `FirTalos.Concrete.projection
  cidx := 3
  size := 1
  usize := 0
  ssize := 0 }

private def objectProjectionFixture :
    Except ConcreteError (Wasm.Store Host × Word32) := do
  let field := Word32.encodeImmediate 11 (by decide)
  let (heap, object) ← allocateConstructor MemoryState.initial projectionInfo
    #[field]
  let store : Wasm.Store Host := {
    emptyHostStore with
    host := { emptyHostStore.host with
      runtime := { emptyHostStore.host.runtime with heap } } }
  return (store, object)

-- The concrete Talos host projects the exact word stored in an eight-byte
-- semantic object slot and leaves its failure channel clear.
#guard match objectProjectionFixture with
  | .ok (store, object) =>
      match objectProjStep 0 store [.i32 (UInt32.ofNat object.value)] with
      | .Return [.i32 field] next =>
          field == 23 && next.host.failure?.isNone
      | _ => false
  | .error _ => false

private def usizeProjectionInfo : Lean.Compiler.LCNF.CtorInfo := {
  name := `FirTalos.Concrete.usizeProjection
  cidx := 4
  size := 0
  usize := 1
  ssize := 0 }

private def usizeProjectionFixture :
    Except ConcreteError (Wasm.Store Host × Word32) := do
  let (heap, object) ← allocateConstructor MemoryState.initial
    usizeProjectionInfo #[]
  let heap ← writeUSizeField heap object 0 18446744073709551615
  let store : Wasm.Store Host := {
    emptyHostStore with
    host := { emptyHostStore.host with
      runtime := { emptyHostStore.host.runtime with heap } } }
  return (store, object)

-- USize projection preserves the full Lean64 payload in an i64 lane.
#guard match usizeProjectionFixture with
  | .ok (store, object) =>
      match usizeProjStep 0 store [.i32 (UInt32.ofNat object.value)] with
      | .Return [.i64 value] next =>
          value == 18446744073709551615 && next.host.failure?.isNone
      | _ => false
  | .error _ => false

-- USize mutation consumes and stores the full i64 lane while preserving the
-- constructor header used to locate the semantic slot.
#guard match usizeProjectionFixture with
  | .ok (store, object) =>
      match usizeSetStep 0 store
          [.i32 (UInt32.ofNat object.value), .i64 37] with
      | .Return [] next =>
          match readTag next.host.runtime.heap object,
              readUSizeField next.host.runtime.heap object 0 with
          | .ok tag, .ok field =>
              tag == 4 && field == 37 && next.host.failure?.isNone
          | _, _ => false
      | _ => false
  | .error _ => false

private def scalarProjectionInfo : Lean.Compiler.LCNF.CtorInfo := {
  name := `FirTalos.Concrete.scalarProjection
  cidx := 5
  size := 0
  usize := 0
  ssize := 8 }

private def scalarProjectionFixture :
    Except ConcreteError (Wasm.Store Host × Word32) := do
  let (heap, object) ← allocateConstructor MemoryState.initial
    scalarProjectionInfo #[]
  let heap ← writeScalarUInt64Field heap object 0 0 18446744073709551615
  let store : Wasm.Store Host := {
    emptyHostStore with
    host := { emptyHostStore.host with
      runtime := { emptyHostStore.host.runtime with heap } } }
  return (store, object)

-- The packed-scalar dispatcher preserves a 64-bit field and lane exactly.
#guard match scalarProjectionFixture with
  | .ok (store, object) =>
      match scalarProjStep 0 0 .uint64 store
          [.i32 (UInt32.ofNat object.value)] with
      | .Return [.i64 value] next =>
          value == 18446744073709551615 && next.host.failure?.isNone
      | _ => false
  | .error _ => false

-- Each supported packed-integer mutation preserves its exact physical lane
-- and is immediately observable through the matching checked reader.
#guard match scalarProjectionFixture with
  | .ok (store, object) =>
      match scalarSetStep 0 0 .uint8 store
          [.i32 (UInt32.ofNat object.value), .i32 255] with
      | .Return [] next =>
          match readScalarUInt8Field next.host.runtime.heap object 0 0 with
          | .ok value => value == 255 && next.host.failure?.isNone
          | .error _ => false
      | _ => false
  | .error _ => false

#guard match scalarProjectionFixture with
  | .ok (store, object) =>
      match scalarSetStep 0 0 .uint16 store
          [.i32 (UInt32.ofNat object.value), .i32 65535] with
      | .Return [] next =>
          match readScalarUInt16Field next.host.runtime.heap object 0 0 with
          | .ok value => value == 65535 && next.host.failure?.isNone
          | .error _ => false
      | _ => false
  | .error _ => false

#guard match scalarProjectionFixture with
  | .ok (store, object) =>
      match scalarSetStep 0 0 .uint32 store
          [.i32 (UInt32.ofNat object.value), .i32 4294967295] with
      | .Return [] next =>
          match readScalarUInt32Field next.host.runtime.heap object 0 0 with
          | .ok value => value == 4294967295 && next.host.failure?.isNone
          | .error _ => false
      | _ => false
  | .error _ => false

#guard match scalarProjectionFixture with
  | .ok (store, object) =>
      match scalarSetStep 0 0 .uint64 store
          [.i32 (UInt32.ofNat object.value), .i64 18446744073709551615] with
      | .Return [] next =>
          match readScalarUInt64Field next.host.runtime.heap object 0 0 with
          | .ok value =>
              value == 18446744073709551615 && next.host.failure?.isNone
          | .error _ => false
      | _ => false
  | .error _ => false

-- Float scalar kinds remain an explicit structured fragment gate.
#guard match scalarProjStep 0 0 .float32 emptyHostStore [.i32 1] with
  | .Trap store _ =>
      store.host.failure? == some (.unsupportedScalarKind .float32)
  | _ => false

#guard match scalarSetStep 0 0 .float32 emptyHostStore [.i32 1, .f32 0] with
  | .Trap store _ =>
      store.host.failure? == some (.unsupportedScalarKind .float32)
  | _ => false

-- Small naturals stay immediate and do not move the concrete heap frontier.
#guard match naturalLiteralStep 42 emptyHostStore [] with
  | .Return [.i32 word] store =>
      word == 85 && store.host.runtime.heap.heapCursor == heapBase &&
        store.host.failure?.isNone
  | _ => false

-- Large naturals allocate their complete little-endian limb representation.
#guard match naturalLiteralStep (UInt64.size + 5) emptyHostStore [] with
  | .Return [.i32 bits] store =>
      let word := Word32.ofUInt32 bits
      match readNatural store.host.runtime.heap word with
      | .ok value => value == UInt64.size + 5 && store.host.failure?.isNone
      | .error _ => false
  | _ => false

private def boxedScalarFixture (scalar : BoxedScalar) :
    Except ConcreteError (Wasm.Store Host × Word32) := do
  let (heap, word) ← boxScalar MemoryState.initial scalar
  let store : Wasm.Store Host := {
    emptyHostStore with
    host := { emptyHostStore.host with
      runtime := { emptyHostStore.host.runtime with heap } } }
  return (store, word)

private def boxingHostRoundtrip (scalar : BoxedScalar) : Bool :=
  match boxStep scalar.kind .tobject emptyHostStore
      [physicalOfLane scalar.lane] with
  | .Return [.i32 bits] store =>
      match unboxStep scalar.kind store [.i32 bits] with
      | .Return [physical] next =>
          physical == physicalOfLane scalar.lane && next.host.failure?.isNone
      | _ => false
  | _ => false

-- The concrete generated-call boundary accepts every supported integer lane.
-- Together these cover immediate, promoted-tag, and ordinary boxed results.
#guard boxingHostRoundtrip (.uint8 255)
#guard boxingHostRoundtrip (.uint16 65535)
#guard boxingHostRoundtrip (.uint32 4294967295)
#guard boxingHostRoundtrip (.uint64 18446744073709551615)
#guard boxingHostRoundtrip (.usize 18446744073709551615)

-- Typed unboxing preserves each supported direct scalar lane. These cases
-- jointly exercise immediate, promoted-tag, and ordinary boxed storage.
#guard match boxedScalarFixture (.uint8 255) with
  | .ok (store, word) =>
      match unboxStep .uint8 store [.i32 (UInt32.ofNat word.value)] with
      | .Return [.i32 value] next =>
          value == 255 && next.host.failure?.isNone
      | _ => false
  | .error _ => false

#guard match boxedScalarFixture (.uint16 65535) with
  | .ok (store, word) =>
      match unboxStep .uint16 store [.i32 (UInt32.ofNat word.value)] with
      | .Return [.i32 value] next =>
          value == 65535 && next.host.failure?.isNone
      | _ => false
  | .error _ => false

#guard match boxedScalarFixture (.uint32 4294967295) with
  | .ok (store, word) =>
      match unboxStep .uint32 store [.i32 (UInt32.ofNat word.value)] with
      | .Return [.i32 value] next =>
          value == 4294967295 && next.host.failure?.isNone
      | _ => false
  | .error _ => false

#guard match boxedScalarFixture (.uint64 18446744073709551615) with
  | .ok (store, word) =>
      match unboxStep .uint64 store [.i32 (UInt32.ofNat word.value)] with
      | .Return [.i64 value] next =>
          value == 18446744073709551615 && next.host.failure?.isNone
      | _ => false
  | .error _ => false

#guard match boxedScalarFixture (.usize 18446744073709551615) with
  | .ok (store, word) =>
      match unboxStep .usize store [.i32 (UInt32.ofNat word.value)] with
      | .Return [.i64 value] next =>
          value == 18446744073709551615 && next.host.failure?.isNone
      | _ => false
  | .error _ => false

private def emptyConstructorInfo : Lean.Compiler.LCNF.CtorInfo := {
  name := `FirTalos.Concrete.emptyConstructor
  cidx := 7
  size := 0
  usize := 0
  ssize := 0 }

-- Empty constructor allocation uses the exact tagged wasm32 representation
-- and does not allocate when the tag is immediate.
#guard match allocCtorStep emptyConstructorInfo #[] .tagged emptyHostStore [] with
  | .Return [.i32 word] store =>
      word == 15 && store.host.runtime.heap.heapCursor == heapBase &&
        store.host.failure?.isNone
  | _ => false

private def unaryConstructorInfo : Lean.Compiler.LCNF.CtorInfo := {
  name := `FirTalos.Concrete.unaryConstructor
  cidx := 8
  size := 1
  usize := 0
  ssize := 0 }

-- Nonempty constructor allocation writes the exact supplied object word into
-- its semantic slot and exposes the checked tag through the concrete decoder.
#guard match allocCtorStep unaryConstructorInfo #[.tagged] .object emptyHostStore
    [.i32 23] with
  | .Return [.i32 bits] store =>
      let object := Word32.ofUInt32 bits
      match readTag store.host.runtime.heap object,
          readObjectField store.host.runtime.heap object 0 with
      | .ok tag, .ok field =>
          tag == 8 && field.value == 23 && store.host.failure?.isNone
      | _, _ => false
  | _ => false

-- Resetting an immediate returns the physical empty reuse token without
-- touching the concrete heap.
#guard match resetStep 1 emptyHostStore [.i32 23] with
  | .Return [.i32 token] store =>
      token == UInt32.ofNat Word32.zero.value &&
        store.host.runtime.heap.heapCursor == heapBase &&
        store.host.runtime.heap.memory == emptyHostStore.host.runtime.heap.memory &&
        store.host.failure?.isNone
  | _ => false

-- A unique constructor enters the reset protocol: its address becomes the
-- reuse token and the cleared ownership slot contains semantic tagged zero.
#guard match allocCtorStep unaryConstructorInfo #[.tagged] .object emptyHostStore
    [.i32 23] with
  | .Return [.i32 object] store =>
      match resetStep 1 store [.i32 object] with
      | .Return [.i32 token] next =>
          match readObjectField next.host.runtime.heap
              (Word32.ofUInt32 object) 0 with
          | .ok field =>
              token == object && field == taggedZero &&
                next.host.failure?.isNone
          | .error _ => false
      | _ => false
  | _ => false

-- A nonunique constructor takes the fallback path: reset consumes one
-- reference, preserves the payload, and returns the empty reuse token.
#guard match allocCtorStep unaryConstructorInfo #[.tagged] .object emptyHostStore
    [.i32 23] with
  | .Return [.i32 object] store =>
      match incrementStep 1 true store [.i32 object] with
      | .Return [] shared =>
          match resetStep 1 shared [.i32 object] with
          | .Return [.i32 token] next =>
              match next.host.runtime.heap.readLiveHeader
                    (Word32.ofUInt32 object),
                  readObjectField next.host.runtime.heap
                    (Word32.ofUInt32 object) 0 with
              | .ok header, .ok field =>
                  token == UInt32.ofNat Word32.zero.value &&
                    header.refCount == 1 && field.value == 23 &&
                    next.host.failure?.isNone
              | _, _ => false
          | _ => false
      | _ => false
  | _ => false

-- An empty reuse token allocates an empty constructor through its exact
-- tagged representation and leaves the heap frontier unchanged.
#guard match reuseStep emptyConstructorInfo false #[] .tagged emptyHostStore
    [.i32 0] with
  | .Return [.i32 word] store =>
      word == 15 && store.host.runtime.heap.heapCursor == heapBase &&
        store.host.failure?.isNone
  | _ => false

-- Fresh nonempty reuse consumes the same token zero but allocates and
-- publishes an ordinary constructor with the supplied field.
#guard match reuseStep unaryConstructorInfo false #[.tagged] .object
    emptyHostStore [.i32 0, .i32 23] with
  | .Return [.i32 object] store =>
      match readTag store.host.runtime.heap (Word32.ofUInt32 object),
          readObjectField store.host.runtime.heap (Word32.ofUInt32 object) 0 with
      | .ok tag, .ok field =>
          tag == 8 && field.value == 23 && store.host.failure?.isNone
      | _, _ => false
  | _ => false

-- A nonempty reset token rebuilds the retained cell in place, consumes the
-- reset-protocol descriptor, and publishes the requested replacement tag.
#guard match allocCtorStep unaryConstructorInfo #[.tagged] .object emptyHostStore
    [.i32 23] with
  | .Return [.i32 object] store =>
      match resetStep 1 store [.i32 object] with
      | .Return [.i32 token] resetStore =>
          match reuseStep { unaryConstructorInfo with cidx := 9 } true
              #[.tagged] .object resetStore [.i32 token, .i32 47] with
          | .Return [.i32 result] next =>
              match readTag next.host.runtime.heap (Word32.ofUInt32 result),
                  readObjectField next.host.runtime.heap
                    (Word32.ofUInt32 result) 0 with
              | .ok tag, .ok field =>
                  token == object && result == object && tag == 9 &&
                    field.value == 47 && next.host.failure?.isNone
              | _, _ => false
          | _ => false
      | _ => false
  | _ => false

-- Ordinary objects update only their checked header reference count.
#guard match allocCtorStep unaryConstructorInfo #[.tagged] .object emptyHostStore
    [.i32 23] with
  | .Return [.i32 object] store =>
      match incrementStep 2 true store [.i32 object] with
      | .Return [] next =>
          match next.host.runtime.heap.readLiveHeader (Word32.ofUInt32 object) with
          | .ok header =>
              header.refCount == 3 && next.host.failure?.isNone
          | .error _ => false
      | _ => false
  | _ => false

-- The concrete sharing query distinguishes a unique ordinary allocation
-- from the same allocation after one checked reference-count increment.
#guard match allocCtorStep unaryConstructorInfo #[.tagged] .object emptyHostStore
    [.i32 23] with
  | .Return [.i32 object] uniqueStore =>
      match isSharedStep uniqueStore [.i32 object] with
      | .Return [.i32 unique] observedUnique =>
          match incrementStep 1 true observedUnique [.i32 object] with
          | .Return [] sharedStore =>
              match isSharedStep sharedStore [.i32 object] with
              | .Return [.i32 shared] observedShared =>
                  unique == 0 && shared == 1 &&
                    observedShared.host.failure?.isNone
              | _ => false
          | _ => false
      | _ => false
  | _ => false

-- Immediate objects are intrinsically shared and do not require a heap
-- header or semantic-handle lookup.
#guard match isSharedStep emptyHostStore [.i32 23] with
  | .Return [.i32 shared] store =>
      shared == 1 && store.host.failure?.isNone
  | _ => false

-- A tagged value promoted past wasm32's immediate range remains a checked
-- no-op even though its concrete word is a heap address.
#guard match naturalLiteralStep 2147483648 emptyHostStore [] with
  | .Return [.i32 object] store =>
      let cursor := store.host.runtime.heap.heapCursor
      match incrementStep 7 true store [.i32 object] with
      | .Return [] next =>
          match readTag next.host.runtime.heap (Word32.ofUInt32 object) with
          | .ok tag =>
              tag.toNat == 2147483648 &&
                next.host.runtime.heap.heapCursor == cursor &&
                next.host.failure?.isNone
          | .error _ => false
      | _ => false
  | _ => false

-- Promoted tags are also intrinsically shared even though their physical
-- representation occupies a checked heap allocation.
#guard match naturalLiteralStep 2147483648 emptyHostStore [] with
  | .Return [.i32 object] store =>
      match isSharedStep store [.i32 object] with
      | .Return [.i32 shared] next =>
          shared == 1 && next.host.failure?.isNone
      | _ => false
  | _ => false

-- Multi-decrement repeats the checked ordinary-header transition exactly and
-- leaves the object payload intact while the count remains positive.
#guard match allocCtorStep unaryConstructorInfo #[.tagged] .object emptyHostStore
    [.i32 23] with
  | .Return [.i32 object] store =>
      match incrementStep 2 true store [.i32 object] with
      | .Return [] shared =>
          match decrementStep 2 true (some 1) shared [.i32 object] with
          | .Return [] next =>
              match next.host.runtime.heap.readLiveHeader
                    (Word32.ofUInt32 object),
                  readObjectField next.host.runtime.heap
                    (Word32.ofUInt32 object) 0 with
              | .ok header, .ok field =>
                  header.refCount == 1 && field.value == 23 &&
                    next.host.failure?.isNone
              | _, _ => false
          | _ => false
      | _ => false
  | _ => false

-- Count-one release marks the parent dead before recursively releasing its
-- owned ordinary child; both allocations end with canonical dead headers.
#guard match allocCtorStep unaryConstructorInfo #[.tagged] .object emptyHostStore
    [.i32 23] with
  | .Return [.i32 child] childStore =>
      match allocCtorStep unaryConstructorInfo #[.object] .object childStore
          [.i32 child] with
      | .Return [.i32 parent] parentStore =>
          match decrementStep 1 true (some 1) parentStore [.i32 parent] with
          | .Return [] next =>
              match next.host.runtime.heap.readLiveHeader
                    (Word32.ofUInt32 child),
                  next.host.runtime.heap.readLiveHeader
                    (Word32.ofUInt32 parent) with
              | .error (.deadObject childAddress),
                  .error (.deadObject parentAddress) =>
                  childAddress == Word32.ofUInt32 child &&
                    parentAddress == Word32.ofUInt32 parent &&
                    next.host.failure?.isNone
              | _, _ => false
          | _ => false
      | _ => false
  | _ => false

-- Promoted tags share the heap-address bit pattern but retain the checked
-- decrement no-op contract and their complete tag payload.
#guard match naturalLiteralStep 2147483648 emptyHostStore [] with
  | .Return [.i32 object] store =>
      let cursor := store.host.runtime.heap.heapCursor
      match decrementStep 4 true none store [.i32 object] with
      | .Return [] next =>
          match readTag next.host.runtime.heap (Word32.ofUInt32 object) with
          | .ok tag =>
              tag.toNat == 2147483648 &&
                next.host.runtime.heap.heapCursor == cursor &&
                next.host.failure?.isNone
          | .error _ => false
      | _ => false
  | _ => false

-- Explicit deletion frees only the selected parent; unlike decrement it does
-- not recursively release the still-live owned child.
#guard match allocCtorStep unaryConstructorInfo #[.tagged] .object emptyHostStore
    [.i32 23] with
  | .Return [.i32 child] childStore =>
      match allocCtorStep unaryConstructorInfo #[.object] .object childStore
          [.i32 child] with
      | .Return [.i32 parent] parentStore =>
          match deleteStep parentStore [.i32 parent] with
          | .Return [] next =>
              match next.host.runtime.heap.readLiveHeader
                    (Word32.ofUInt32 child),
                  next.host.runtime.heap.readLiveHeader
                    (Word32.ofUInt32 parent) with
              | .ok childHeader, .error (.deadObject parentAddress) =>
                  childHeader.refCount == 1 &&
                    parentAddress == Word32.ofUInt32 parent &&
                    next.host.failure?.isNone
              | _, _ => false
          | _ => false
      | _ => false
  | _ => false

-- The shared erased failed-reset encoding is an operation-specific delete
-- no-op; physical zero does not become an ordinary object address.
#guard match deleteStep emptyHostStore [.i32 0] with
  | .Return [] next =>
      next.host.runtime.heap.heapCursor ==
          emptyHostStore.host.runtime.heap.heapCursor &&
        next.host.runtime.heap.memory == emptyHostStore.host.runtime.heap.memory &&
        next.host.failure?.isNone
  | _ => false

-- Constructor-tag mutation rewrites only the checked header: the new tag is
-- visible while the existing object payload remains byte-for-byte decodable.
#guard match allocCtorStep unaryConstructorInfo #[.tagged] .object emptyHostStore
    [.i32 23] with
  | .Return [.i32 object] store =>
      match setTagStep 19 store [.i32 object] with
      | .Return [] next =>
          match readTag next.host.runtime.heap (Word32.ofUInt32 object),
              readObjectField next.host.runtime.heap (Word32.ofUInt32 object) 0 with
          | .ok tag, .ok field =>
              tag == 19 && field.value == 23 && next.host.failure?.isNone
          | _, _ => false
      | _ => false
  | _ => false

-- Object-slot mutation preserves constructor metadata while replacing the
-- exact wasm32 field lane selected by the generated import.
#guard match allocCtorStep unaryConstructorInfo #[.tagged] .object emptyHostStore
    [.i32 23] with
  | .Return [.i32 object] store =>
      match objectSetStep 0 .tagged store [.i32 object, .i32 47] with
      | .Return [] next =>
          match readTag next.host.runtime.heap (Word32.ofUInt32 object),
              readObjectField next.host.runtime.heap (Word32.ofUInt32 object) 0 with
          | .ok tag, .ok field =>
              tag == 8 && field.value == 47 && next.host.failure?.isNone
          | _, _ => false
      | _ => false
  | _ => false

private def cacheDeclaration : Lean.Name := `FirTalos.Concrete.cachedValue

private def cacheStore : Wasm.Store Host := {
  emptyHostStore with
  host := { emptyHostStore.host with
    runtime := { emptyHostStore.host.runtime with
      globals := ConcreteGlobals.declare [(cacheDeclaration, .uint64)] } } }

-- Cache writes preserve the full i64 lane and return it unchanged for the
-- generated Wasm value-global update.
#guard match cacheSetStep cacheDeclaration .uint64 cacheStore
    [.i64 18446744073709551615] with
  | .Return [.i64 returned] store =>
      match store.host.runtime.readGlobal cacheDeclaration .uint64 with
      | .ok (.word64 cached) =>
          returned == 18446744073709551615 && cached == returned &&
            store.host.failure?.isNone
      | _ => false
  | _ => false

private def persistentCacheFixture :
    Except ConcreteError (Wasm.Store Host × Word32 × Word32) := do
  let immediate := Word32.encodeImmediate 11 (by decide)
  let (innerHeap, inner) ← allocateConstructor MemoryState.initial
    unaryConstructorInfo #[immediate]
  let (heap, outer) ← allocateConstructor innerHeap unaryConstructorInfo #[inner]
  let store : Wasm.Store Host := {
    emptyHostStore with
    host := { emptyHostStore.host with
      runtime := { emptyHostStore.host.runtime with
        heap
        globals := ConcreteGlobals.declare [(cacheDeclaration, .object)] } } }
  return (store, outer, inner)

-- Lean's cache transition marks the complete reachable object graph before
-- publishing the root. Both constructor headers become persistent with a
-- zero reference count, while the exact object word is retained globally.
#guard match persistentCacheFixture with
  | .ok (store, outer, inner) =>
      match cacheSetStep cacheDeclaration .object store
          [.i32 (UInt32.ofNat outer.value)] with
      | .Return [.i32 returned] next =>
          match next.host.runtime.heap.readLiveHeader outer,
              next.host.runtime.heap.readLiveHeader inner,
              next.host.runtime.readGlobal cacheDeclaration .object with
          | .ok outerHeader, .ok innerHeader, .ok (.word32 cached) =>
              returned == UInt32.ofNat outer.value && cached == outer &&
                outerHeader.persistent && innerHeader.persistent &&
                outerHeader.refCount == 0 && innerHeader.refCount == 0 &&
                next.host.failure?.isNone
          | _, _, _ => false
      | _ => false
  | .error _ => false

private def closureTarget : Lean.Name := `FirTalos.Concrete.closureTarget

private def closureStore : Wasm.Store Host := {
  emptyHostStore with
  host := { emptyHostStore.host with
    closureDispatch := #[closureTarget]
    closureDescriptors := #[#[.uint64]] } }

-- Partial application stores the exact typed capture and returns a concrete
-- heap address; no semantic closure or handle table participates at runtime.
#guard match partialApplyStep closureTarget 2 1 #[.uint64] .object closureStore
    [.i64 18446744073709551615] with
  | .Return [.i32 bits] store =>
      let object := Word32.ofUInt32 bits
      match projectClosureCapture store.host.runtime.heap
          store.host.closureDispatch store.host.closureDescriptors object
          closureTarget 2 1 0 .uint64 with
      | .ok (.word64 captured) =>
          captured == 18446744073709551615 && store.host.failure?.isNone
      | _ => false
  | _ => false

-- The generated trampoline's concrete metadata test and typed projection
-- recover the just-allocated closure without consulting semantic handles.
#guard match partialApplyStep closureTarget 2 1 #[.uint64] .object closureStore
    [.i64 18446744073709551615] with
  | .Return [.i32 object] store =>
      match closureMatchesStep closureTarget 2 1 store [.i32 object],
          closureMatchesStep `FirTalos.Concrete.otherTarget 2 1 store
            [.i32 object],
          closureProjStep closureTarget 2 1 0 .uint64 store [.i32 object] with
      | .Return [.i32 matched] matchedStore,
          .Return [.i32 mismatch] mismatchedStore,
          .Return [.i64 captured] projectedStore =>
          matched == 1 && mismatch == 0 &&
            captured == 18446744073709551615 &&
            matchedStore.host.failure?.isNone &&
            mismatchedStore.host.failure?.isNone &&
            projectedStore.host.failure?.isNone
      | _, _, _ => false
  | _ => false

end FirTalos.Concrete
