# wasm-gen lane

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: waiting
base: 78f3a9fcf1844f3c7909e9e20f128cb10b4fb992 on main
functional-head: cd75894326693c8fb195a220d940825003946032
contract-base: 78f3a9fc on main; consumes resident Float vocabulary e39d0bbb and unsigned i32 remainder 78f3a9fc
clean-at-update: true
slice: Compile the real Lean 4.32 Illuminate initialTransition/transition whole-trace closure into a 50,237-byte self-contained Wasm module; link all runtime operations in module-owned memory; publish an atomic immutable browser/Node package with structured prepare/execute/decode phases, binary64 timestamp transport, exact source/helper inventories, checksums, and normalized FrameAction output
files: Fir/Wasm/Emit/ResidentArray.lean; Fir/Wasm/Emit/ResidentNatMod.lean; Fir/Wasm/Emit/ResidentIlluminatePlayer.lean; integration/illuminate-player/**; Illuminate private-specialization bug card; this mailbox
contracts: consumes FLOAT-MACHINE and ILLUMINATE-NAT-MOD-MACHINE; no shared semantic contract changed in the functional stack; nine Illuminate specialization helpers are generation-ready against the exact 4.32 import names/signatures and remain separate from later W6 refinement theorems
checks: PASS Lean Beam update/sync with zero diagnostics for ResidentArray, ResidentNatMod, ResidentIlluminatePlayer, Facade, Compile, and Examples; PASS focused lake build IlluminateFirNative.Compile and IlluminateFirNative.Examples; PASS integration/illuminate-player/check.sh (native guards, source adapter smoke, 105/105 legacy-JS/FIR-native traces, deterministic double publication, checksum verification, packaged smoke over every PlayerEvent constructor and repeated calls); PASS zero function imports and zero memory imports; PASS git diff --check; PASS make check (642 unique cases, 1,844/1,844 comparisons equal, 104 bug cards, trusted-assumption gate); PASS make talos-setup; WAIT make talos-check and bash integration/talos/artifact/check.sh because W6-owned FirTalos.Adapter is non-exhaustive for the already-landed Float/i64 conversion vocabulary plus i32RemU, before any Illuminate execution starts
bug-cards: FIR-BUG-wasm-none-illuminate-action-at-admission fixed; FIR-BUG-wasm-none-illuminate-private-specialization-closure fixed
blockers: W6 must adapt FirTalos.Adapter and its machine/proof cone for f64Const, i32RemU, i64Or/i64Shl/i64ShrU/i64LtU, f64 Eq/Lt/Le/Add/Sub/Mul/Div/Ceil/Floor, i64ExtendI32U, f64ConvertI64U, and i64TruncSatF64U; integration then lands that W6 slice on main
handoff: none until the W6 Talos adapter catches up and both required Talos/artifact gates pass; the zero-import package is already generation-ready for external-engine differential testing
next: after W6/integration lands the Talos adaptation, rebase wasm/generation on main, rerun make talos-check and the complete artifact plus Illuminate gates, republish from a clean source head, and change this mailbox to ready
```
