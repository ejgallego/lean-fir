import Fir.Wasm.Concrete.Runtime

namespace Fir.Wasm.Emit.ResidentContainerLayout

/-- ASCII `ARRY`, stored in an ordinary resident Array's `opaque.aux0`. -/
def arrayMarker : UInt32 := 0x41525259

/-- ASCII `BYTE`, stored in a packed resident ByteArray's `aux0`. -/
def byteArrayMarker : UInt32 := 0x42595445

end Fir.Wasm.Emit.ResidentContainerLayout
