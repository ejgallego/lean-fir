import Fir.Validation.DirectLCNF

def main (args : List String) : IO UInt32 :=
  Fir.Validation.DirectLcnf.main
    Fir.Validation.DirectLcnf.lcnfBackend
    Fir.Validation.DirectLcnf.runLcnfCase
    args
