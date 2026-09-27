# wasm-proof lane

This is a milestone snapshot, not the live handoff. Exact clean checkpoints and
validation results are published through the canonical FIR mailbox.

```text
lane: wasm-proof
owner: fir/wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: ac56b0bf38c05c40b24079f4a48239911e5b1a49
functional-head: ac56b0bf3
contract-base: 2504f9f74817c38279e0ed3b7b0b8c12196a7c35
clean-at-update: false
slice: Execute the actual retained initializer's mkEmpty staging, allocation call and destination bind through reusable directional argument refinement.
files: ConcreteStructuredSimulation.lean; ConcreteExternalCallRequest.lean; ConcreteArrayExternalCall.lean; trust inventory/audit; retained-initializer consumer/gate; W6 docs and projection-codegen bug card.
contracts: W6 call shape distinguishes actual argument kinds from declared parameter kinds using kindsRefine. Existing pure admission remains exact-signature. No shared semantic/ABI, emitter or central admission-policy change.
checks: Beam checks, fresh batch proof cone, make check, Talos setup/check, exact-source retained reconstruction/readback/direct consumers pass. Exact clean checkpoint and forced trust result are published in the mailbox.
trust: 289 generic endpoints. Request decoding uses standard axioms; Array call/bind inherits byte-assembly debt. The retained mkEmpty endpoint additionally audits one native dependency for closed Expr ABI comparisons only, not execution/heap properties.
bug-cards: FIR-BUG-wasm-none-retained-projection-codegen; independently reproduced upstream unknown-join-point/native-compilation failure. Proof-only projections are noncomputable and kernel-check.
blockers: Installed handler conformance/resident linking and central heap-result lazy-miss closure remain explicit separate obligations.
handoff: Generic external control ac56b0bf3 is accepted main (ROOT-W6-20260927-010). The actual captured mkEmpty execution is a separate tested successor.
next: Connect literal entry and the following fresh tagged push, then thread hereditary resource scope into the existing publication suffix. The current theorem starts at the actual mkEmpty let, derives three source steps and the target argument-prefix plus call/bind; no complete initializer, compressStored or encoded-byte theorem is claimed.
```
