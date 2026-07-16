import FirTalos.Runtime
import Fir.Wasm.Examples
import Interpreter.Wasm.Semantics

namespace FirTalos

open Fir.Wasm
open Fir.LeanIR.Impure

private def emptyHostStore : Wasm.Store RuntimeHost :=
  ({ funcs := [] } : Wasm.Module).initialStore

private def returnedAs (kind : AbiKind) (expected : Value) :
    Wasm.HostResult RuntimeHost → Bool
  | .Return [.i32 handle] store =>
      store.host.trap?.isNone &&
        match store.host.handles.decodeAs kind handle with
        | .ok value => value == expected
        | .error _ => false
  | _ => false

def naturalLiteralHostWorks : Bool :=
  returnedAs .tobject (.object (.tagged 42)) <|
    hostStep (.naturalLiteral 42 .tobject) emptyHostStore []

#guard naturalLiteralHostWorks

def stringLiteralHostWorks : Bool :=
  match hostStep (.stringLiteral "semantic wasm" .object) emptyHostStore [] with
  | .Return [.i32 handle] store =>
      match store.host.handles.decodeAs .object handle with
      | .ok (.object (.heap location)) =>
          match getLiveCell store.host.runtime location with
          | .ok cell => cell.object == .string "semantic wasm"
          | .error _ => false
      | _ => false
  | _ => false

#guard stringLiteralHostWorks

def constructorAndProjectionHostsWork : Bool :=
  match hostStep (.naturalLiteral 7 .tobject) emptyHostStore [] with
  | .Return [.i32 seven] store =>
      match hostStep (.naturalLiteral 8 .tobject) store [] with
      | .Return [.i32 eight] store =>
          let allocate := HostOperation.allocCtor
            Fir.LeanIR.InterpreterExamples.pairInfo #[.tobject, .tobject] .object
          match hostStep allocate store [.i32 seven, .i32 eight] with
          | .Return [.i32 pair] store =>
              match hostStep (.objectProj 0 .tobject) store [.i32 pair] with
              | .Return [.i32 projected] store =>
                  projected == seven &&
                    match store.host.handles.decodeAs .tobject projected with
                    | .ok value => value == .object (.tagged 7)
                    | .error _ => false
              | _ => false
          | _ => false
      | _ => false
  | _ => false

#guard constructorAndProjectionHostsWork

def constructorTagHostWorks : Bool :=
  let allocate := HostOperation.allocCtor
    Fir.LeanIR.InterpreterExamples.trueInfo #[] .tagged
  match hostStep allocate emptyHostStore [] with
  | .Return [.i32 constructor] store =>
      match hostStep .getTag store [.i32 constructor] with
      | .Return [.i32 tag] store => tag == 1 && store.host.trap?.isNone
      | _ => false
  | _ => false

#guard constructorTagHostWorks

def badArityIsStructured : Bool :=
  match hostStep (.naturalLiteral 1 .tobject) emptyHostStore [.i32 0] with
  | .Trap store _ =>
      store.host.trap? == some (.target (.arityMismatch 0 1))
  | _ => false

#guard badArityIsStructured

def badLaneIsStructured : Bool :=
  let allocate := HostOperation.allocCtor
    Fir.LeanIR.InterpreterExamples.pairInfo #[.tobject, .tobject] .object
  match hostStep allocate emptyHostStore [.i64 0, .i32 0] with
  | .Trap store _ =>
      store.host.trap? == some (.target (.abiKindMismatch .tobject))
  | _ => false

#guard badLaneIsStructured

def badHandleIsStructured : Bool :=
  match hostStep (.objectProj 0 .tobject) emptyHostStore [.i32 99] with
  | .Trap store _ =>
      store.host.trap? == some (.target (.invalidHandle 99))
  | _ => false

#guard badHandleIsStructured

def sourceFaultIsStructured : Bool :=
  match hostStep (.naturalLiteral 1 .tobject) emptyHostStore [] with
  | .Return [.i32 natural] store =>
      match hostStep (.objectProj 0 .tobject) store [.i32 natural] with
      | .Trap store _ =>
          store.host.trap? == some (.source .expectedConstructor)
      | _ => false
  | _ => false

#guard sourceFaultIsStructured

structure RuntimeFixture where
  source : Fir.Wasm.Module
  target : Wasm.Module
  hosts : ResolvedHosts

def runtimeFixture? (program : Fir.LeanIR.ImpureProgram) : Option RuntimeFixture := do
  let source ← match Fir.Wasm.lower program with
    | .ok source => some source
    | .error _ => none
  let adapted ← match adapt source with
    | .ok adapted => some adapted
    | .error _ => none
  let hosts ← match resolveHosts source with
    | .ok hosts => some hosts
    | .error _ => none
  return { source, target := adapted.wasmModule, hosts }

def RuntimeFixture.importsResolveExactly (fixture : RuntimeFixture) : Bool :=
  fixture.source.imports.size == fixture.hosts.operations.length &&
    fixture.target.imports.length == fixture.hosts.env.funcs.length &&
    fixture.hosts.env.funcs.length == fixture.hosts.spec.contracts.length &&
    (fixture.source.imports.toList.zip fixture.hosts.operations).all fun pair =>
      pair.fst.key == .runtime pair.snd.runtimeOp &&
        pair.fst.signature == pair.snd.signature &&
        (hostFn pair.snd).params == pair.fst.signature.params.toList.map abiKind &&
        (hostFn pair.snd).results == pair.fst.signature.results.toList.map abiKind

def RuntimeFixture.runMain (fixture : RuntimeFixture) : Wasm.Result RuntimeHost :=
  Wasm.run 100 fixture.target fixture.source.imports.size
    (fixture.target.initialStore (α := RuntimeHost)) [] fixture.hosts.env

def RuntimeFixture.mainReturns (fixture : RuntimeFixture) (kind : AbiKind)
    (expected : Value) : Bool :=
  match fixture.runMain with
  | .Success [.i32 handle] store =>
      match store.host.handles.decodeAs kind handle with
      | .ok value => value == expected
      | .error _ => false
  | _ => false

def fixtureRunsAs? (program : Fir.LeanIR.ImpureProgram) (kind : AbiKind)
    (expected : Value) : Bool :=
  (runtimeFixture? program).any fun fixture =>
    fixture.importsResolveExactly && fixture.mainReturns kind expected

#guard fixtureRunsAs? Fir.Wasm.abiLiteralProgram .tobject (.object (.tagged 42))

#guard fixtureRunsAs? Fir.Wasm.abiCtorProjectionProgram .tobject (.object (.tagged 7))

#guard fixtureRunsAs? Fir.Wasm.abiCaseProgram .tobject (.object (.tagged 1))

#guard Fir.Wasm.externalModule?.any fun source =>
  match resolveHosts source with
  | .error (.externalImport 0 `external) => true
  | _ => false

end FirTalos
