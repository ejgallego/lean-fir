# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 6f3c64254faaf9d32118f571b968ccae43c7e038
functional-head: b28feab9
contract-base: 6f3c64254faaf9d32118f571b968ccae43c7e038
clean-at-update: true
slice: Implement and prove persistent, exclusive-transfer, and shared-retain closure application through the concrete Talos matcher/projection boundary
files: W6-owned Fir/Wasm/Concrete/ closure runtime and ownership proofs; integration/talos/FirTalos/ concrete runtime, dispatch, call/cache compatibility proofs, semantics, contracts, and regression example; W6 bug card
contracts: consumed the integrated CLOSURE-APPLICATION-OWNERSHIP and external waiting-runtime contracts exactly; no shared semantic contract changed or duplicated
checks: PASS Lean Beam sync/save FirTalos/Correctness/Semantics.lean; PASS git diff --check 6f3c6425..b28feab9; PASS make check (633 native/LCNF cases, 9 direct-machine cases, 601 native/LCNF/V8 cases, coverage findings 0); PASS make talos-check (3125/3125 jobs)
bug-cards: FIR-BUG-wasm-none-closure-application-erased-retain fixed
blockers: none
handoff: b28feab9 is a clean, green W6 functional head based on 6f3c6425; the original b811c39a patch rebased as 112e3f46 and b28feab9 adds only the W6 Talos frame-suffix adaptation to the integrated external waiting-runtime contract
next: integrate this ready slice; afterward thread selected.nextStore and the semantic post-application runtime through general hereditary saturated/partial closure calls to remove the explicit unchanged-store compatibility specialization
```
