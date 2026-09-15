import Fir.Wasm.Emit.NativeSymbol
import Fir.Wasm.Emit.Binary
import Lean.Elab.Command

open Lean Lean.Elab.Command Lean.Compiler.LCNF Fir.Wasm.Emit

set_option compiler.postponeCompile false

namespace NativeSymbolTests

@[extern "fir_test_native_symbol"]
opaque external (value : String) : UInt32

@[export fir_test_native_symbol]
def implementation (_value : String) : UInt32 := 42

run_cmd do
  liftCoreM do
    let env ← getEnv
    let some sig ← getImpureSignature? ``external | throwError "missing test extern signature"
    let decl : Decl .impure := {
      name := sig.name, levelParams := sig.levelParams, params := sig.params,
      type := sig.type, safe := sig.safe, inlineAttr? := none,
      value := .extern ((getExternAttrData? env sig.name).get!) }
    let index := NativeSymbol.exportIndex env
    let some provider ← NativeSymbol.resolve index decl | throwError "provider not resolved"
    unless provider.name == ``implementation do throwError "wrong provider"
    let reject (label : String) (action : CoreM Unit) : CoreM Unit := do
      let rejected ← try action; pure false catch _ => pure true
      unless rejected do throwError "accepted negative control: {label}"
    reject "duplicate export" <| discard <| NativeSymbol.resolve
      (index.push (provider.symbol, ``implementation)) decl
    reject "self alias" <| discard <| NativeSymbol.resolve
      #[(provider.symbol, decl.name)] decl
    reject "export metadata mismatch" <| discard <| NativeSymbol.resolve
      #[(provider.symbol, ``NativeSymbol.resolve)] decl
    reject "borrow mismatch" <| discard <| NativeSymbol.resolve index
      { decl with params := decl.params.modify 0 fun p => { p with borrow := !p.borrow } }
    reject "result mismatch" <| discard <| NativeSymbol.resolve index
      { decl with type := mkConst ``UInt64 }
    reject "safety mismatch" <| discard <| NativeSymbol.resolve index
      { decl with safe := !decl.safe }
    reject "universe mismatch" <| discard <| NativeSymbol.resolve index
      { decl with levelParams := [`wrongUniverse] }
    unless (← NativeSymbol.resolve #[] decl).isNone do throwError "missing provider guessed"
    unless (NativeSymbol.checkBody provider `WrongOwner decl).toOption.isNone do
      throwError "wrong owner accepted"
    unless (NativeSymbol.checkBody provider provider.owner
      { decl with name := provider.name }).toOption.isNone do
      throwError "external stub accepted as captured implementation"

@[extern "fir_test_native_difference"]
opaque externalDifference (a b : UInt32) : UInt32

@[export fir_test_native_difference]
def difference (a b : UInt32) : UInt32 := a - b

/- External-engine control for argument order and unsigned result transport.
The symbolic callee isolates linker behavior; renderer tests cover actual LCNF
lowering. No application/runtime implementation is duplicated here. -/
run_cmd do
  liftCoreM do
    let some path ← IO.getEnv "FIR_NATIVE_SYMBOL_TEST_OUTPUT" | pure ()
    let env ← getEnv
    let some sig ← getImpureSignature? ``externalDifference | throwError "missing difference signature"
    let decl : Decl .impure := {
      name := sig.name, levelParams := sig.levelParams, params := sig.params,
      type := sig.type, safe := sig.safe, inlineAttr? := none,
      value := .extern ((getExternAttrData? env sig.name).get!) }
    let some p ← NativeSymbol.resolve (NativeSymbol.exportIndex env) decl |
      throwError "missing difference provider"
    let imported ← ofExcept <| (Fir.Wasm.externalImport decl).mapError reprStr
    let a : FVarId := ⟨`a⟩
    let b : FVarId := ⟨`b⟩
    let module : Fir.Wasm.Module := {
      imports := #[imported]
      functions := #[{
        name := p.name, params := #[(a, .uint32), (b, .uint32)], results := #[.uint32],
        locals := #[], body := [.localGet a, .localGet b, .i32Sub, .ret] }]
      exports := #[p.declaration], initializers := #[], runtimeOperations := #[] }
    let linked ← ofExcept <| NativeSymbol.link #[p] module
    let bytes ← ofExcept <| (Fir.Wasm.Emit.encode linked).mapError reprStr
    IO.FS.writeBinFile path bytes

#guard difference 7 2 == 5
#guard difference 2 7 == 4294967291

end NativeSymbolTests
