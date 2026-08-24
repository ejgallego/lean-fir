# lean-zip-perf lane

This is the narrowly scoped successor to the W7-2 optimization role. It owns
one lean-zip performance experiment at a time; `wasm-gen` remains the stable
generation and integration owner.

```text
lane: lean-zip-perf
owner: lean-zip-perf
branch: perf/lean-zip-loop
worktree: .worktrees/lean-zip-perf
state: active
base: 88b8e60d, clean local main before lane bootstrap
functional-head: 88b8e60d, bootstrap baseline with no performance change
contract-base: 88b8e60d; no shared semantic, ABI, layout, ownership, helper-signature, proof, or generation contract change
clean-at-update: true
slice: Profile one immutable accepted lean-zip package, select one hotspot, test one bounded candidate, and discard it or hand a measured winner to wasm-gen
files: lean-zip-specific benchmarks, package ratchets, and performance evidence under integration/lean-zip/; coordination/lanes/lean-zip-perf.md; only explicitly leased W7 implementation files
contracts: none
checks: not-run; this is a coordination-only bootstrap with no functional candidate
bug-cards: none
blockers: none
handoff: none; experimental candidates stay in this lane until one has focused correctness evidence and a repeatable performance or size win
next: after the bootstrap lands, create the named worktree from clean main, bind the latest accepted lean-zip artifact as the immutable baseline, and select one profiled hotspot
```
