import Fir.Wasm.Emit.ResidentFixedWidth
import Fir.Wasm.Emit.ResidentLiteral
import Lean.Elab.Command
import Lean.Compiler.LCNF.PhaseExt

open Lean Lean.Elab.Command Lean.Compiler.LCNF Fir.Wasm Fir.Wasm.Emit

/- Check the installed compiler's interface, not a hand-written import alone.
This file runs under both FIR's production toolchain and the isolated renderer
toolchain. Neither path consumes the other's compiled modules. -/
run_cmd do
  liftCoreM do
    let env ← getEnv
    let some sig ← getImpureSignature? ``UInt64.ofNatLT |
      throwError "missing installed UInt64.ofNatLT signature"
    unless getExternNameFor env `c sig.name == some "lean_uint64_of_nat" do
      throwError "UInt64.ofNatLT upstream symbol changed"
    unless sig.safe && sig.levelParams.isEmpty &&
        sig.type == ImpureType.uint64 &&
        sig.params.map (·.type) == #[ImpureType.tobject, ImpureType.erased] &&
        sig.params.map (·.borrow) == #[true, false] do
      throwError "UInt64.ofNatLT installed representation or borrowing changed"
    unless ResidentFixedWidth.uint64OfNatLTFunction.params.map (·.2) == #[.tobject, .erased] &&
        ResidentFixedWidth.uint64OfNatLTFunction.results == #[.uint64] &&
        ResidentFixedWidth.uint64OfNatLTFunction.body == ResidentFixedWidth.uint64OfNatFunction.body do
      throwError "UInt64.ofNatLT adapter no longer preserves the conversion body"

#guard UInt64.ofNatLT 0 (by decide) == 0
#guard UInt64.ofNatLT 9223372036854775808 (by decide) == 9223372036854775808
#guard UInt64.ofNatLT 18446744073709551615 (by decide) == 18446744073709551615
#guard Fir.Wasm.Concrete.naturalLimbs (2^64) == [0, 1]
#guard Fir.Wasm.Concrete.naturalLimbs (2^193 + 2^129 + 0x0123456789abcdef) ==
  [0x0123456789abcdef, 0, 2, 2]
