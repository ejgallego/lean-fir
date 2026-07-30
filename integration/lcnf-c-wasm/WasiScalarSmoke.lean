namespace Fir.LcnfCWasm

partial def buildWasiScalarArray
    (remaining state : UInt64)
    (bytes : ByteArray) : ByteArray :=
  if remaining == 0 then
    bytes
  else
    buildWasiScalarArray
      (remaining - 1)
      (state * 6364136223846793005 + 1442695040888963407)
      (bytes.push state.toUInt8)

@[export fir_lcnf_c_wasi_scalar_checksum]
def wasiScalarChecksum (rounds seed : UInt64) : UInt64 :=
  let initialCapacity : Nat := if rounds == 0 then 1 else 0
  let bytes :=
    buildWasiScalarArray
      rounds seed (ByteArray.emptyWithCapacity initialCapacity)
  let byteSum := bytes.foldl (fun sum byte => sum + byte.toUInt64) 0
  let transforms : Array (UInt64 → UInt64 → UInt64) :=
    #[fun value salt => value + salt + seed,
      fun value salt => (value ^^^ salt) + seed]
  transforms.foldl
    (fun value transform => transform value rounds)
    byteSum

end Fir.LcnfCWasm
