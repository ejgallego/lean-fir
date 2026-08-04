# wasm-gen lane

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: 26ed9fff3c642c48169c970123c93de2e35d091e
functional-head: 4404aba07aa90fb96dc43b5ca056ca38a32fd4bc
contract-base: 26ed9fff3c642c48169c970123c93de2e35d091e on main
clean-at-update: true
slice: Stack-safe cold-entry prettyM generation: validated post-lowering direct self-tail-call elimination, cold 2,047-node packaged regression, and atomic zero-import artifact refresh
files: Fir/Wasm/Emit/TailCall.lean; Fir/Wasm/Emit/ResidentPrettyFormat.lean; integration/talos/artifact/FirWasmSourceExample.lean; integration/talos/artifact/FirWasmPrettyTraceExample.lean; integration/talos/artifact/check-prettyM-browser-adapter.mjs; integration/talos/artifact/prettyM-package/smoke.mjs; integration/talos/artifact/prettyM-package/README.md; bugs/FIR-BUG-wasm-none-prettyM-cold-entry-call-stack-overflow.md
contracts: none; consumes the existing symbolic loop/branch surface and changes no shared layout, ABI, resident-helper signature, final LCNF, or W6 helper contract
checks: PASS Lean Beam sync/save for Fir/Wasm/Emit/TailCall.lean and Fir/Wasm/Emit/ResidentPrettyFormat.lean; PASS lake build Fir.Wasm.Emit.TailCall Fir.Wasm.Emit.ResidentPrettyFormat; PASS fresh Node cold 2,047-node balanced append, reported fresh 1,026-node grouped document, and fresh 32,767-node balanced stress; PASS integration/talos/artifact/package-pretty-format.sh --no-build on temporary and canonical releases; PASS git diff --check; PASS make check (122 validator tests, 633 native/LCNF cases, 9 direct-machine cases, 601 native/LCNF/V8 cases, 1844/1844 comparisons equal, findings 0); PASS make talos-setup; PASS make talos-check (3125 jobs); PASS bash integration/talos/artifact/check.sh including deterministic source artifacts, resident helper clients, zero-function-import prettyM, cold browser-adapter regression, semantic/concrete/native-oracle paths, and atomic package smoke
bug-cards: FIR-BUG-wasm-none-prettyM-cold-entry-call-stack-overflow fixed
blockers: none
handoff: integrate functional head 4404aba07aa90fb96dc43b5ca056ca38a32fd4bc plus this ready mailbox commit; package prettyM-current-releases/4404aba07aa9-c040c75c6ef0cf70 has 104833-byte prettyM.wasm digest bb9ebbfe6e19dba3221a5a8bb16becbedd3014cc5f4a5f112927a94b35341792
next: integration fast-forwards this green W7 slice and updates coordination/BOARD.md; wasm-proof may schedule a separate correctness theorem for the post-lowering self-tail-call elimination, with no resident-helper proof invalidated
```
