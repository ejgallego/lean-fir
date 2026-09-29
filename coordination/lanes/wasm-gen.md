# wasm-gen lane

Generic Nat remainder range facts, authorized by the user after the bounded
Collatz investigation. Root owns integration (W7-ROOT-20260929-006).

```text
lane: wasm-gen
owner: fir/wasm-gen
branch: wasm/nat-mod-range-facts-4341
worktree: .worktrees/wasm-generation
state: ready
base: 2e5c15ed6717f25a317910a7f3ba20a009173051
functional-head: 911e2aec7b5f1a496fb3c20094c51e39c0ef5b2b
contract-base: 2e5c15ed6717f25a317910a7f3ba20a009173051
clean-at-update: true
slice: Consume positive literal divisor facts to refine Nat.mod results and erase their checked releases.
files: Fir/Wasm/Emit/ResidentCallSite.lean; Fir/Wasm/Emit/ResidentNatArithmetic.lean; integration/talos/artifact/resident-nat-arithmetic-client.mjs; this snapshot
contracts: none; unchanged runtime bodies, helper signatures, layout, ABI and toolchain
checks: Functional head passes Beam; clean focused Lake build; raw and production-O3 Node arithmetic/ownership controls; eight frozen-source Collatz differentials; git diff --check; make check; make talos-setup/check; full artifact/check.sh. This snapshot is a documentation-only successor, not a claim of fresh gates on the successor.
bug-cards: none
blockers: none
handoff: Exact clean integrationCheckpoint recorded in canonical mailbox; no push, publication or live pointer changes.
next: Root review; any balanced client timing or proof attachment is separate.
```

The new fact is established at the particular argument read, from a preceding
positive canonical Nat literal in the same straight-line list. Zero, erased or
even words, out-of-range source literals, scalar words, unknown values,
overwrites and nested writes do not justify it. Facts are not imported across
blocks or loop entries. Existing result-assignment checks remain in force.
The arithmetic provider uses `n % d < d` for positive bounded `d`; the existing
release pass consumes the result kind. No runtime implementation is replaced.

Regression coverage adds 17 structural controls and four ownership callers
(zero, two, largest immediate divisor, overwritten divisor). Their engine
checks cover 42 value/ownership cases and eight malformed-input traps, including
multi-limb dividends and heap-valued zero-divisor results. Raw and optimized
execution both pass. This is generation evidence, not a new W6 refinement proof.

The unchanged authenticated Collatz source captures identically and agrees
with the frozen baseline at eight inputs up to 100000. `collatzSteps` has nine
release calls instead of ten; `collatzBest` retains its six. Local generated
Wasm is 11969 bytes, SHA-256
`b9d38807dd9ed04201282cf78491bf2f8402502675e9c50120741455f7334653`,
with zero imports and unchanged exports/ownership. No runtime speedup or
historical size-delta attribution is claimed.

Evidence and commands: `.deps/nat-mod-range-facts/READOUT.md`, bound by the
mailbox handoff digest. The preserved renderer-name and Collatz-investigation
branches and all released renderer packages are unchanged. Dynamic range facts,
cross-branch/interprocedural analysis and local-alias propagation remain out of
scope for this bounded slice.
