import Fir.Validation.DirectLCNF

def main (args : List String) : IO UInt32 :=
  Fir.Validation.DirectLcnf.main
    Fir.Validation.DirectLcnf.nativeBackend
    Fir.Validation.DirectLcnf.runNativeCase
    args
