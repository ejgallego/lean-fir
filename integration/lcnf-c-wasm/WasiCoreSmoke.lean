namespace Fir.LcnfCWasm

partial def buildWasiCoreArray
    (remaining state : UInt64)
    (values : Array UInt64) : Array UInt64 :=
  if remaining == 0 then
    values
  else
    buildWasiCoreArray
      (remaining - 1)
      (state * 6364136223846793005 + 1442695040888963407)
      (values.push state)

@[export fir_lcnf_c_wasi_core_checksum]
def wasiCoreChecksum (rounds seed : UInt64) : UInt64 :=
  let values := buildWasiCoreArray rounds seed #[]
  let arraySum := values.foldl (fun sum value => sum + value) 0
  let transforms : Array (UInt64 → UInt64) :=
    #[fun value => value + seed, fun value => value ^^^ rounds]
  let closureValue :=
    transforms.foldl (fun value transform => transform value) arraySum
  let suffix := if rounds == 0 then "zero" else "nonzero"
  let label := "fir:" ++ suffix ++ ":λ"
  closureValue + label.utf8ByteSize.toUInt64

end Fir.LcnfCWasm
