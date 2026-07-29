namespace Fir.LcnfCWasm

partial def buildList
    (remaining state : UInt64)
    (values : List UInt64) : List UInt64 :=
  if remaining == 0 then
    values
  else
    buildList
      (remaining - 1)
      (state * 6364136223846793005 + 1442695040888963407)
      (state :: values)

partial def sumList (values : List UInt64) (sum : UInt64) : UInt64 :=
  match values with
  | [] => sum
  | value :: rest => sumList rest (sum + value)

@[export fir_lcnf_c_heap_checksum]
def heapChecksum (rounds seed : UInt64) : UInt64 :=
  sumList (buildList rounds seed []) 0

end Fir.LcnfCWasm
