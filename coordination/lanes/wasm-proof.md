# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 7fb2c8ee on main
functional-head: 1b0dfc7d (accepted complete resource-indexed direct-value structured simulation spine)
contract-base: 7fb2c8ee; continues over the accepted W6.7e direct-spine, caller-transport, call-entry, and bind-frame contracts
clean-at-update: true
slice: Lift the accepted direct-value body induction through the entry-relative saved-frame relation for recursive internal calls. Compose generated direct-call entry, recursive callee progress, witness/store transport, and bind-frame return so the caller continuation regains the same compiler focus without target traces or certificates.
files: coordination/lanes/wasm-proof.md; intended proof-owned modules under integration/talos/FirTalos/
contracts: none; proof construction over accepted contracts
checks: not-run for this slice
bug-cards: none
blockers: none
handoff: none; active proof slice
next: State the recursive code-evaluation relation that admits direct lets and internal calls, then prove its structured finite-path composition from the existing entry/callee/return lemmas.
```
