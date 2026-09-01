# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: aa9f2bc9
functional-head: ce30b6ce
contract-base: f8954036
clean-at-update: true
slice: Converged W7's exact resident erased-zero repair with W6's bounded transitive erased-lane proof adaptation. The shared classifier follows compiler-generated `tobject` and explicit-boxing `tagged` carriers through statically named declaration parameters to raw `erased`/`void` sinks, while cycles, exhausted fuel, unknown declarations, arity mismatch, and external carrier parameters fail closed. W6 cache folding, structured validation, final-LCNF typing, and the production-shaped `tobject -> tagged -> void` fixture now consume that exact effective classifier. W7's `fir_mark_persistent` accepts only canonical physical zero as the erased no-op and preserves ordinary object decoding/traps. The exact VBP widget now executes mount, callback/event activity, and unmount successfully.
files: Fir/Wasm/Lower.lean; Fir/Wasm/Examples.lean; Fir/Wasm/Emit/ResidentCache.lean; integration/talos/artifact/check-resident-cache.mjs; integration/vbp-verso-viewer/package-smoke.mjs; integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteStructuredValidation.lean; integration/talos/FirTalos/ConcreteFinalLcnfTyping.lean; integration/talos/FirTalos/ConcreteCompilerCorrectnessContract.lean; bugs/FIR-BUG-wasm-none-persistent-cache-erased-sentinel.md; bugs/FIR-BUG-wasm-none-vbp-smoke-js-resource-result.md; coordination/lanes/wasm-proof.md
contracts: Shared lowering classification is strengthened only for structurally justified compiler-generated carrier paths. No global tagged/erased or object/erased compatibility is added. The resident cache helper now implements the existing W6 concrete physical-zero no-op contract without changing its signature, ABI, layout, ordinary object decoding, or nonzero failure behavior. Source semantics, symbolic Wasm, ownership, and other resident-helper contracts are unchanged.
checks: Lean Beam update/sync/save for the four changed proof modules (pass: zero blocking diagnostics); focused proof-cone lake builds (pass); two independent clean no-reuse exact VBP package generations (pass: identical package ID and Wasm SHA-256 d738584215ea9c4b3eabef3aa290245c49fc54e2128d0dddf303db82cdc26a66; 2399 captured declarations, 2247 source functions, 5360 resident helpers, 7607 complete functions, 41 host imports); exact VBP SHA256SUMS and mount/event/unmount package smoke (pass); post-rebase git diff --check (pass); post-rebase make check (pass: 730 unique cases, 2172/2172 comparisons equal, exactly one trusted axiom); make talos-setup (pass: Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254); post-rebase make talos-check (pass: 3190 jobs, exact receipt 55d0fc2d941a37307606c721d3788d323ad92eda58c06b2b439b7539412f50d0); bash integration/talos/artifact/check.sh (pass: 45/45 concrete readiness artifacts, 16/16 source probes, deterministic package and resident-helper checks)
bug-cards: FIR-BUG-wasm-none-transitive-erased-closure-dispatch (candidate fully validated; ready to mark fixed at integration); FIR-BUG-wasm-none-persistent-cache-erased-sentinel (fixed); FIR-BUG-wasm-none-vbp-smoke-js-resource-result (fixed)
blockers: none
handoff: clean evidence-only successor based on accepted integration head aa9f2bc9, shared classifier f8954036, and W6 proof functional head ce30b6ce; ready for root integration metadata closure
next: Integration marks the transitive-dispatch bug fixed, releases the contract queue row, records the exact widget evidence, and fast-forwards main. A later non-contract performance slice may memoize or otherwise reduce the approximately 15.6-minute fresh exact-widget generation cost.
```
