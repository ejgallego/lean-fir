import FirTalos.Runtime
import Fir.Wasm.Examples
import Interpreter.Wasm.Examples.Harness

namespace FirTalos

def literalModuleLowers? : Bool :=
  match Fir.Wasm.literalModule? with
  | none => false
  | some source =>
      match module source with
      | .ok target => target.funcs.length == 1 && target.exports.length == 1
      | .error _ => false

#guard literalModuleLowers?

def literalAdapted? : Option AdaptedModule := do
  let source ← Fir.Wasm.literalModule?
  match adapt source with
  | .ok adapted => some adapted
  | .error _ => none

#guard literalAdapted?.any fun adapted =>
  adapted.sourceMap.functionOrigins.size == 2 &&
  adapted.sourceMap.origin? 0 == some (.import <|
    .runtime (.literal (.nat 42) .object)) &&
  adapted.sourceMap.origin? 1 == some (.definition `main) &&
  match adapted.wasmModule.validate with
  | .ok _ => true
  | .error _ => false

def scalarIdModule : Wasm.Module :=
  match Fir.Wasm.scalarIdModule? with
  | none => default
  | some source =>
      match module source with
      | .ok target => target
      | .error _ => default

#guard Wasm.Examples.runValues 5 scalarIdModule 0
  (scalarIdModule.initialStore (α := Unit)) [.i64 123] == [.i64 123]

def floatIdModule : Wasm.Module :=
  match Fir.Wasm.floatIdModule? with
  | none => default
  | some source =>
      match module source with
      | .ok target => target
      | .error _ => default

#guard floatIdModule.funcs[0]?.any fun function =>
  function.params == [.f32] && function.results == [.f32]

#guard Fir.Wasm.floatExternalImport?.any fun sourceImport =>
  let target := importDecl sourceImport
  target.params == [.f32] && target.results == [.f64]

def adaptsProgram? (program : Fir.LeanIR.ImpureProgram) : Bool :=
  match Fir.Wasm.lower program with
  | .error _ => false
  | .ok source =>
      match adapt source with
      | .ok _ => true
      | .error _ => false

#guard adaptsProgram? Fir.LeanIR.InterpreterExamples.directCallProgram
#guard adaptsProgram? Fir.LeanIR.InterpreterExamples.caseProgram
#guard adaptsProgram? Fir.LeanIR.InterpreterExamples.joinProgram

def adaptProgram? (program : Fir.LeanIR.ImpureProgram) : Option AdaptedModule := do
  let source ← match Fir.Wasm.lower program with
    | .ok source => some source
    | .error _ => none
  match adapt source with
  | .ok adapted => some adapted
  | .error _ => none

#guard (adaptProgram? Fir.LeanIR.InterpreterExamples.directCallProgram).any fun adapted =>
  adapted.sourceMap.origin? 1 == some (.definition `id) &&
  adapted.sourceMap.origin? 2 == some (.definition `main) &&
  adapted.wasmModule.funcs[1]?.any fun function =>
    function.body.allInstrs.any fun
      | .call 1 => true
      | _ => false

#guard (adaptProgram? Fir.LeanIR.InterpreterExamples.caseProgram).any fun adapted =>
  adapted.wasmModule.funcs[0]?.any fun function =>
    function.body.allInstrs.any fun
      | .iff .. => true
      | _ => false

#guard (adaptProgram? Fir.LeanIR.InterpreterExamples.joinProgram).any fun adapted =>
  adapted.wasmModule.funcs[0]?.any fun function =>
    function.body.allInstrs.any fun
      | .br 0 => true
      | _ => false

#guard Fir.Wasm.externalModule?.any fun source =>
  match adapt source with
  | .ok adapted =>
      adapted.sourceMap.origin? 0 == some (.import (.external `external)) &&
      adapted.sourceMap.origin? 1 == some (.definition `main)
  | .error _ => false

#guard match module (Fir.Wasm.fixtureModule <|
    Fir.Wasm.fixtureFunction [.localGet Fir.Wasm.ghost]) with
  | .error (.invalidModule (.unknownLocal `fixture fvarId)) =>
      fvarId.name == Fir.Wasm.ghost.name
  | _ => false

#guard match module (Fir.Wasm.fixtureModule <| Fir.Wasm.fixtureFunction [
    .block Fir.Wasm.outer [.block Fir.Wasm.inner [.br Fir.Wasm.outer]]]) with
  | .ok _ => true
  | _ => false

#guard match Fir.Wasm.lower Fir.LeanIR.InterpreterExamples.closureCallProgram with
  | .ok source =>
      match module source with
      | .error (.invalidModule (.unsupportedClosure _)) => true
      | _ => false
  | .error _ => false

#guard Fir.Wasm.literalModule?.any fun source =>
  match module { source with initializers := #[`main] } with
  | .error (.invalidModule (.unsupportedInitializer `main)) => true
  | _ => false

end FirTalos
