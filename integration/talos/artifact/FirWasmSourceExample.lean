import Fir.Validation.Corpus
import Fir.Wasm.Emit.Command

namespace Fir.Wasm.Emit.SourceFixture

def idUInt8 (value : UInt8) : UInt8 := value

def idUInt16 (value : UInt16) : UInt16 := value

def idUInt32 (value : UInt32) : UInt32 := value

def idUInt64 (value : UInt64) : UInt64 := value

def acceptString (_value : String) : UInt64 := 18446744073709551615

end Fir.Wasm.Emit.SourceFixture

#fir_wasm_emit Fir.Validation.Corpus.Source.maxUInt64 to "_build/source-uint64.wasm"

#fir_wasm_emit Fir.Validation.Corpus.Source.idUSize with [usize(42)]
  to "_build/source-usize-id.wasm"

#fir_wasm_emit Fir.Wasm.Emit.SourceFixture.idUInt8 with [uint8(255)]
  to "_build/source-uint8-id.wasm"

#fir_wasm_emit Fir.Wasm.Emit.SourceFixture.idUInt16 with [uint16(65535)]
  to "_build/source-uint16-id.wasm"

#fir_wasm_emit Fir.Wasm.Emit.SourceFixture.idUInt32 with [uint32(4294967295)]
  to "_build/source-uint32-id.wasm"

#fir_wasm_emit Fir.Wasm.Emit.SourceFixture.idUInt64 with [uint64(18446744073709551615)]
  to "_build/source-uint64-id.wasm"

#fir_wasm_emit Fir.Wasm.Emit.SourceFixture.acceptString with [string("hello α_world_β")]
  to "_build/source-string-input.wasm"
