namespace Fir.LcnfCWasm

@[export fir_lcnf_c_affine]
def affine (value : UInt64) : UInt64 :=
  value * 3 + 1

partial def mixLoop (remaining state : UInt64) : UInt64 :=
  if remaining == 0 then
    state
  else
    mixLoop
      (remaining - 1)
      (state * 6364136223846793005 + 1442695040888963407)

@[export fir_lcnf_c_mix]
def mix (rounds seed : UInt64) : UInt64 :=
  mixLoop rounds seed

end Fir.LcnfCWasm
