import Fir.Validation.Corpus
import Fir.Wasm.Emit.Command

#fir_wasm_emit Fir.Validation.Corpus.Source.maxUInt64 to "_build/source-uint64.wasm"

#fir_wasm_emit Fir.Validation.Corpus.Source.idUSize with [usize(42)]
  to "_build/source-usize-id.wasm"
