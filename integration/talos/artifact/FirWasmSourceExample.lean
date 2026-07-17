import Fir.Validation.Corpus
import Fir.Wasm.Emit.Command

namespace Fir.Wasm.Emit.SourceFixture

def acceptString (_value : String) : UInt64 := 18446744073709551615

def classifyNatList (values : List Nat) : UInt64 :=
  match values with
  | [] => 0
  | _ :: _ => 1

end Fir.Wasm.Emit.SourceFixture

#fir_wasm_emit Fir.Validation.Corpus.Source.maxUInt64 to "_build/source-uint64.wasm"

#fir_wasm_emit_case "usize-roundtrip"
  to "_build/source-usize-id.wasm"

#fir_wasm_emit_case "uint8-roundtrip"
  to "_build/source-uint8-id.wasm"

#fir_wasm_emit_case "uint16-roundtrip"
  to "_build/source-uint16-id.wasm"

#fir_wasm_emit_case "uint32-roundtrip"
  to "_build/source-uint32-id.wasm"

#fir_wasm_emit_case "uint64-roundtrip"
  to "_build/source-uint64-id.wasm"

#fir_wasm_emit Fir.Wasm.Emit.SourceFixture.acceptString with [string("hello α_world_β")]
  to "_build/source-string-input.wasm"

#fir_wasm_emit Fir.Wasm.Emit.SourceFixture.classifyNatList with
    [natList([0, 18446744073709551616, 42])]
  to "_build/source-nat-list-case.wasm"
