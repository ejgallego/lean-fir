import Fir.LeanIR.Interpreter

namespace Fir.LeanIR

namespace InterpreterExamples

open Lean
open Lean.Compiler
open Impure

def x : FVarId := ⟨`x⟩
def y : FVarId := ⟨`y⟩
def z : FVarId := ⟨`z⟩
def c : FVarId := ⟨`c⟩
def p : FVarId := ⟨`p⟩
def r : FVarId := ⟨`r⟩
def u : FVarId := ⟨`u⟩
def s : FVarId := ⟨`s⟩
def j : FVarId := ⟨`j⟩

def objType : Expr := LCNF.ImpureType.object
def taggedType : Expr := LCNF.ImpureType.tagged
def u8Type : Expr := LCNF.ImpureType.uint8
def u64Type : Expr := LCNF.ImpureType.uint64
def usizeType : Expr := LCNF.ImpureType.usize

def param (fvarId : FVarId) (type : Expr := objType) : LCNF.Param .impure :=
  { fvarId, binderName := fvarId.name, type, borrow := false }

def decl (name : Name) (params : Array (LCNF.Param .impure)) (type : Expr)
    (value : LCNF.DeclValue .impure) : LCNF.Decl .impure :=
  { name
    levelParams := []
    type
    params
    value
    safe := true
    recursive := false
    inlineAttr? := none }

def letDecl (fvarId : FVarId) (type : Expr) (value : LCNF.LetValue .impure) :
    LCNF.LetDecl .impure :=
  { fvarId, binderName := fvarId.name, type, value }

def returned? (result : RunResult) (expected : Value) : Bool :=
  match result with
  | .done observation => observation.outcome == .returned expected
  | .outOfFuel _ => false

def faulted? (result : RunResult) (expected : RuntimeFault) : Bool :=
  match result with
  | .done observation => observation.outcome == .fault expected
  | .outOfFuel _ => false

def runMain (program : ImpureProgram) (externals := rejectExternals) : RunResult :=
  runProgram 100 externals program `main #[]

def literalCode : LCNF.Code .impure :=
  .let (letDecl x objType (.lit (.nat 42))) (.return x)

def literalProgram : ImpureProgram :=
  { decls := #[decl `main #[] objType (.code literalCode)] }

#guard returned? (runMain literalProgram) (.object (.tagged 42))

def erasedCode : LCNF.Code .impure :=
  .let (letDecl x objType .erased) (.return x)

def erasedProgram : ImpureProgram :=
  { decls := #[decl `main #[] objType (.code erasedCode)] }

#guard returned? (runMain erasedProgram) .erased

def pairInfo : LCNF.CtorInfo :=
  { name := `Pair.mk, cidx := 0, size := 2, usize := 0, ssize := 0 }

def ctorProjectionCode : LCNF.Code .impure :=
  .let (letDecl x objType (.lit (.nat 7))) <|
  .let (letDecl y objType (.lit (.nat 8))) <|
  .let (letDecl p objType (.ctor pairInfo #[.fvar x, .fvar y])) <|
  .let (letDecl r objType (.oproj 0 p)) <|
  .return r

def ctorProjectionProgram : ImpureProgram :=
  { decls := #[decl `main #[] objType (.code ctorProjectionCode)] }

#guard returned? (runMain ctorProjectionProgram) (.object (.tagged 7))

def falseInfo : LCNF.CtorInfo :=
  { name := ``Bool.false, cidx := 0, size := 0, usize := 0, ssize := 0 }

def trueInfo : LCNF.CtorInfo :=
  { name := ``Bool.true, cidx := 1, size := 0, usize := 0, ssize := 0 }

def caseCode : LCNF.Code .impure :=
  .let (letDecl c taggedType (.ctor trueInfo #[])) <|
  .cases (.mk ``Bool objType c #[
    .ctorAlt falseInfo (.let (letDecl r objType (.lit (.nat 0))) (.return r)),
    .ctorAlt trueInfo (.let (letDecl u objType (.lit (.nat 1))) (.return u))])

def caseProgram : ImpureProgram :=
  { decls := #[decl `main #[] objType (.code caseCode)] }

#guard returned? (runMain caseProgram) (.object (.tagged 1))

def thirdInfo : LCNF.CtorInfo :=
  { name := `ScalarChoice.third, cidx := 2, size := 0, usize := 0, ssize := 0 }

def scalarCaseCode : LCNF.Code .impure :=
  .let (letDecl c u8Type (.lit (.uint8 2))) <|
  .cases (.mk `ScalarChoice objType c #[
    .ctorAlt falseInfo (.let (letDecl x objType (.lit (.nat 10))) (.return x)),
    .ctorAlt trueInfo (.let (letDecl y objType (.lit (.nat 20))) (.return y)),
    .ctorAlt thirdInfo (.let (letDecl z objType (.lit (.nat 30))) (.return z))])

def scalarCaseProgram : ImpureProgram :=
  { decls := #[decl `main #[] objType (.code scalarCaseCode)] }

#guard returned? (runMain scalarCaseProgram) (.object (.tagged 30))

def byteArrayIdentityCode : LCNF.Code .impure :=
  .inc x 1 true false <|
  .return x

def byteArrayIdentityProgram : ImpureProgram :=
  { decls := #[decl `main #[param x] objType (.code byteArrayIdentityCode)] }

def byteArrayIdentity? : Bool :=
  let bytes : Array UInt8 := #[0, 127, 128, 255]
  let (runtime, reference) := alloc {} (.byteArray bytes)
  match runProgram 100 rejectExternals byteArrayIdentityProgram `main
      #[.object reference] runtime with
  | .done observation =>
      match observation.outcome, reference with
      | .returned (.object returned), .heap location =>
          returned == reference &&
            match getLiveCell { heap := observation.heap } location with
            | .ok cell => cell.object == .byteArray bytes
            | .error _ => false
      | _, _ => false
  | .outOfFuel _ => false

#guard byteArrayIdentity?

def bigIntIdentity? : Bool :=
  let value : Int := 9223372036854775808
  let (runtime, reference) := alloc {} (.integer value)
  match runProgram 100 rejectExternals byteArrayIdentityProgram `main
      #[.object reference] runtime with
  | .done observation =>
      match observation.outcome, reference with
      | .returned (.object returned), .heap location =>
          returned == reference &&
            match getLiveCell { heap := observation.heap } location with
            | .ok cell => cell.object == .integer value
            | .error _ => false
      | _, _ => false
  | .outOfFuel _ => false

#guard bigIntIdentity?

def idDecl : LCNF.Decl .impure :=
  decl `id #[param x] objType (.code (.return x))

def directCallCode : LCNF.Code .impure :=
  .let (letDecl x objType (.lit (.nat 11))) <|
  .let (letDecl r objType (.fap `id #[.fvar x])) <|
  .return r

def directCallProgram : ImpureProgram :=
  { decls := #[idDecl, decl `main #[] objType (.code directCallCode)] }

#guard returned? (runMain directCallProgram) (.object (.tagged 11))

def firstDecl : LCNF.Decl .impure :=
  decl `first #[param x, param y] objType (.code (.return x))

def closureCallCode : LCNF.Code .impure :=
  .let (letDecl x objType (.lit (.nat 21))) <|
  .let (letDecl c objType (.pap `first #[.fvar x])) <|
  .let (letDecl y objType (.lit (.nat 22))) <|
  .let (letDecl r objType (.fvar c #[.fvar y])) <|
  .return r

def closureCallProgram : ImpureProgram :=
  { decls := #[firstDecl, decl `main #[] objType (.code closureCallCode)] }

#guard returned? (runMain closureCallProgram) (.object (.tagged 21))

def joinCode : LCNF.Code .impure :=
  .jp (.mk j `j #[param p] objType (.return p)) <|
  .let (letDecl x objType (.lit (.nat 31))) <|
  .jmp j #[.fvar x]

def joinProgram : ImpureProgram :=
  { decls := #[decl `main #[] objType (.code joinCode)] }

#guard returned? (runMain joinProgram) (.object (.tagged 31))

def scalarBoxCode : LCNF.Code .impure :=
  .let (letDecl s u64Type (.lit (.uint64 44))) <|
  .let (letDecl x objType (.box u64Type s)) <|
  .let (letDecl r u64Type (.unbox x)) <|
  .return r

def scalarBoxProgram : ImpureProgram :=
  { decls := #[decl `main #[] u64Type (.code scalarBoxCode)] }

#guard returned? (runMain scalarBoxProgram) (.scalar (.uint64 44))

def layoutInfo : LCNF.CtorInfo :=
  { name := `Layout.mk, cidx := 3, size := 1, usize := 1, ssize := 8 }

def mutationCode : LCNF.Code .impure :=
  .let (letDecl x objType (.lit (.nat 1))) <|
  .let (letDecl y objType (.lit (.nat 2))) <|
  .let (letDecl p objType (.ctor layoutInfo #[.fvar x])) <|
  .let (letDecl u usizeType (.lit (.usize 55))) <|
  .uset p 1 u <|
  .let (letDecl s u64Type (.lit (.uint64 66))) <|
  .sset p 1 0 s u64Type <|
  .oset p 0 (.fvar y) <|
  .setTag p 4 <|
  .let (letDecl r u64Type (.sproj 1 0 p)) <|
  .return r

def mutationProgram : ImpureProgram :=
  { decls := #[decl `main #[] u64Type (.code mutationCode)] }

#guard returned? (runMain mutationProgram) (.scalar (.uint64 66))

def usizeProjectionCode : LCNF.Code .impure :=
  .let (letDecl x objType (.lit (.nat 1))) <|
  .let (letDecl p objType (.ctor layoutInfo #[.fvar x])) <|
  .let (letDecl u usizeType (.lit (.usize 77))) <|
  .uset p 1 u <|
  .let (letDecl r usizeType (.uproj 1 p)) <|
  .return r

def usizeProjectionProgram : ImpureProgram :=
  { decls := #[decl `main #[] usizeType (.code usizeProjectionCode)] }

#guard returned? (runMain usizeProjectionProgram) (.usize 77)

def objectMutationCode : LCNF.Code .impure :=
  .let (letDecl x objType (.lit (.nat 1))) <|
  .let (letDecl y objType (.lit (.nat 88))) <|
  .let (letDecl p objType (.ctor { pairInfo with size := 1 } #[.fvar x])) <|
  .oset p 0 (.fvar y) <|
  .let (letDecl r objType (.oproj 0 p)) <|
  .return r

def objectMutationProgram : ImpureProgram :=
  { decls := #[decl `main #[] objType (.code objectMutationCode)] }

#guard returned? (runMain objectMutationProgram) (.object (.tagged 88))

def changedTagInfo : LCNF.CtorInfo :=
  { name := `Changed.mk, cidx := 9, size := 1, usize := 0, ssize := 0 }

def tagMutationCode : LCNF.Code .impure :=
  .let (letDecl x objType (.lit (.nat 1))) <|
  .let (letDecl p objType (.ctor { pairInfo with size := 1 } #[.fvar x])) <|
  .setTag p 9 <|
  .cases (.mk `Changed objType p #[
    .ctorAlt changedTagInfo (.let (letDecl r objType (.lit (.nat 99))) (.return r)),
    .default (.let (letDecl u objType (.lit (.nat 0))) (.return u))])

def tagMutationProgram : ImpureProgram :=
  { decls := #[decl `main #[] objType (.code tagMutationCode)] }

#guard returned? (runMain tagMutationProgram) (.object (.tagged 99))

def defaultCaseCode : LCNF.Code .impure :=
  .let (letDecl c taggedType (.ctor trueInfo #[])) <|
  .cases (.mk ``Bool objType c #[
    .default (.let (letDecl r objType (.lit (.nat 5))) (.return r)),
    .ctorAlt falseInfo (.let (letDecl u objType (.lit (.nat 0))) (.return u))])

def defaultCaseProgram : ImpureProgram :=
  { decls := #[decl `main #[] objType (.code defaultCaseCode)] }

#guard returned? (runMain defaultCaseProgram) (.object (.tagged 5))

def rcCode : LCNF.Code .impure :=
  .let (letDecl x objType (.lit (.str "owned"))) <|
  .inc x 1 true false <|
  .dec x 1 true false none <|
  .let (letDecl r u8Type (.isShared x)) <|
  .return r

def rcProgram : ImpureProgram :=
  { decls := #[decl `main #[] u8Type (.code rcCode)] }

#guard returned? (runMain rcProgram) (.scalar (.uint8 0))

def persistentRcCode : LCNF.Code .impure :=
  .let (letDecl x objType (.lit (.str "persistent instruction"))) <|
  .inc x 10 false true <|
  .dec x 10 false true none <|
  .let (letDecl r u8Type (.isShared x)) <|
  .return r

def persistentRcProgram : ImpureProgram :=
  { decls := #[decl `main #[] u8Type (.code persistentRcCode)] }

#guard returned? (runMain persistentRcProgram) (.scalar (.uint8 0))

def cachedGraphValueCode : LCNF.Code .impure :=
  .let (letDecl x objType (.lit (.str "cached child"))) <|
  .let (letDecl p objType (.ctor { pairInfo with size := 1 } #[.fvar x])) <|
  .return p

def cachedGraphMainCode : LCNF.Code .impure :=
  .let (letDecl p objType (.fap `cachedGraphValue #[])) <|
  .let (letDecl x objType (.oproj 0 p)) <|
  .let (letDecl r u8Type (.isShared x)) <|
  .return r

def cachedGraphProgram : ImpureProgram :=
  { decls := #[
      decl `cachedGraphValue #[] objType (.code cachedGraphValueCode),
      decl `main #[] u8Type (.code cachedGraphMainCode)] }

def returnedPersistentGraph? (result : RunResult) : Bool :=
  match result with
  | .done observation =>
      observation.outcome == .returned (.scalar (.uint8 1)) &&
        observation.heap.length == 2 &&
        observation.heap.all fun entry =>
          entry.snd.live && entry.snd.persistent && entry.snd.rc == 0
  | .outOfFuel _ => false

-- Nullary declarations follow `lean_mark_persistent`: both the returned root
-- and its reachable child become process-lifetime objects before the caller
-- observes the cached value.
#guard returnedPersistentGraph? (runMain cachedGraphProgram)

def isSharedCaseCode : LCNF.Code .impure :=
  .let (letDecl x objType (.lit (.nat 1))) <|
  .let (letDecl p objType (.ctor { pairInfo with size := 1 } #[.fvar x])) <|
  .let (letDecl r u8Type (.isShared p)) <|
  .cases (.mk ``Bool objType r #[
    .ctorAlt falseInfo (.let (letDecl x objType (.lit (.nat 10))) (.return x)),
    .ctorAlt trueInfo (.let (letDecl y objType (.lit (.nat 20))) (.return y))])

def isSharedCaseProgram : ImpureProgram :=
  { decls := #[decl `main #[] objType (.code isSharedCaseCode)] }

#guard returned? (runMain isSharedCaseProgram) (.object (.tagged 10))

def resetReuseCode : LCNF.Code .impure :=
  .let (letDecl x objType (.lit (.nat 70))) <|
  .let (letDecl p objType (.ctor { pairInfo with size := 1 } #[.fvar x])) <|
  .let (letDecl r objType (.reset 1 p)) <|
  .let (letDecl y objType (.lit (.nat 71))) <|
  .let (letDecl z objType (.reuse r { pairInfo with size := 1 } false #[.fvar y])) <|
  .let (letDecl s objType (.oproj 0 z)) <|
  .return s

def resetReuseProgram : ImpureProgram :=
  { decls := #[decl `main #[] objType (.code resetReuseCode)] }

#guard returned? (runMain resetReuseProgram) (.object (.tagged 71))

def resetErasedFieldCode : LCNF.Code .impure :=
  .let (letDecl p objType
    (.ctor { pairInfo with size := 1 } #[.erased])) <|
  .let (letDecl r objType (.reset 1 p)) <|
  .let (letDecl y objType (.lit (.nat 72))) <|
  .let (letDecl z objType
    (.reuse r { pairInfo with size := 1 } false #[.fvar y])) <|
  .let (letDecl s objType (.oproj 0 z)) <|
  .return s

def resetErasedFieldProgram : ImpureProgram :=
  { decls := #[decl `main #[] objType (.code resetErasedFieldCode)] }

#guard returned? (runMain resetErasedFieldProgram) (.object (.tagged 72))

def sharedResetCode : LCNF.Code .impure :=
  .let (letDecl x objType (.lit (.nat 80))) <|
  .let (letDecl p objType (.ctor { pairInfo with size := 1 } #[.fvar x])) <|
  .inc p 1 false false <|
  .let (letDecl r objType (.reset 1 p)) <|
  .let (letDecl y objType (.lit (.nat 81))) <|
  .let (letDecl z objType (.reuse r changedTagInfo true #[.fvar y])) <|
  .let (letDecl s objType (.oproj 0 z)) <|
  .return s

def sharedResetProgram : ImpureProgram :=
  { decls := #[decl `main #[] objType (.code sharedResetCode)] }

#guard returned? (runMain sharedResetProgram) (.object (.tagged 81))

def deletedCode : LCNF.Code .impure :=
  .let (letDecl x objType (.lit (.str "delete"))) <|
  .del x <|
  .let (letDecl r u8Type (.isShared x)) <|
  .return r

def deletedProgram : ImpureProgram :=
  { decls := #[decl `main #[] u8Type (.code deletedCode)] }

#guard faulted? (runMain deletedProgram) (.deadObject 0)

def externalDecl : LCNF.Decl .impure :=
  decl `external #[param x u64Type] u64Type (.extern { entries := [] })

def externalCode : LCNF.Code .impure :=
  .let (letDecl x u64Type (.lit (.uint64 90))) <|
  .let (letDecl r u64Type (.fap `external #[.fvar x])) <|
  .return r

def externalProgram : ImpureProgram :=
  { decls := #[externalDecl, decl `main #[] u64Type (.code externalCode)] }

def echoExternal : ExternalImpl where
  call request runtime :=
    match request.args[0]? with
    | some value => .ok {
        value
        heap := runtime.heap
        nextLocation := runtime.nextLocation
        world := runtime.world + 1 }
    | none => .error (.arityMismatch 1 0)

#guard returned? (runMain externalProgram echoExternal) (.scalar (.uint64 90))

def worldAndTraceUpdated? : RunResult → Bool
  | .done observation => observation.world == 1 && observation.trace.size == 1
  | .outOfFuel _ => false

#guard worldAndTraceUpdated? (runMain externalProgram echoExternal)

def capturedRcExternalDecl : LCNF.Decl .impure :=
  decl `capturedRcExternal #[param x objType, param y u64Type] u64Type
    (.extern { entries := [] })

def capturedRcExternalCode : LCNF.Code .impure :=
  .let (letDecl x objType (.lit (.str "captured"))) <|
  .let (letDecl c objType (.pap `capturedRcExternal #[.fvar x])) <|
  .inc c 1 true false <|
  .let (letDecl y u64Type (.lit (.uint64 0))) <|
  .let (letDecl r u64Type (.fvar c #[.fvar y])) <|
  .return r

def capturedRcExternalProgram : ImpureProgram :=
  { decls := #[
      capturedRcExternalDecl,
      decl `main #[] u64Type (.code capturedRcExternalCode)] }

def observeCapturedRcExternal : ExternalImpl where
  call request runtime :=
    match request.args[0]? with
    | some value =>
        match value with
        | Value.object (ObjectRef.heap location) =>
            match getLiveCell runtime location with
            | .ok cell => .ok {
                value := .scalar (.uint64 (UInt64.ofNat cell.rc))
                heap := runtime.heap
                nextLocation := runtime.nextLocation
                world := runtime.world }
            | .error fault => .error fault
        | _ =>
            .error (.externalFailure request.name
              "expected a captured heap object")
    | _ =>
        .error (.externalFailure request.name
          "expected a captured heap object")

#guard returned? (runMain capturedRcExternalProgram observeCapturedRcExternal)
  (.scalar (.uint64 2))

end InterpreterExamples

end Fir.LeanIR
