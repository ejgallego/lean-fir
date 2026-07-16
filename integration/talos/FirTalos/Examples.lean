import FirTalos.Adapter
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

def scalarIdModule : Wasm.Module :=
  match Fir.Wasm.scalarIdModule? with
  | none => default
  | some source =>
      match module source with
      | .ok target => target
      | .error _ => default

#guard Wasm.Examples.runValues 5 scalarIdModule 0
  (scalarIdModule.initialStore (α := Unit)) [.i64 123] == [.i64 123]

end FirTalos
