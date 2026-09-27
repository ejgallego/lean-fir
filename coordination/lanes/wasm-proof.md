# wasm-proof lane

This is a milestone snapshot, not the live handoff. Exact clean checkpoints and
validation results are published through the canonical FIR mailbox.

```text
lane: wasm-proof
owner: fir/wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 4861c51c9785ad7479507895110ba1012a559bcd
functional-head: 4861c51c9
contract-base: 2504f9f74817c38279e0ed3b7b0b8c12196a7c35
clean-at-update: false
slice: Complete the actual retained initializer body through heap-neutral UInt8 boxing, fresh tagged Array push, and precise object return.
files: ConcreteBoxPrefix.lean; ConcreteArrayPushCall.lean; ConcreteArrayExternalCall.lean; trust inventory/audit; RetainedArrayCalls.lean; W6 plans/consumer README and this snapshot.
contracts: Derive ten source transitions and finite target return, preserving joins/stacks and residual allocation budget. No shared semantic/ABI, emitter or central admission-policy change.
checks: Beam checks, fresh batch proof cone, make check, Talos setup/check, exact-source retained reconstruction/readback/direct consumers pass. Exact clean checkpoint and forced trust result are published in the mailbox.
trust: No new native evaluation or axiom. Exact audits record existing scalar-box policy/result-kind comparisons and byte assembly. Operand reconstruction uses only propext/Quot.sound.
bug-cards: FIR-BUG-wasm-none-retained-projection-codegen; independently reproduced upstream unknown-join-point/native-compilation failure. Proof-only projections are noncomputable and kernel-check.
blockers: Installed handler conformance/resident linking and central heap-result lazy-miss closure remain explicit separate obligations.
handoff: Literal-prefix checkpoint 4861c51c9 is accepted main. Complete body connection is the next isolated checkpoint; exact gates are in the mailbox.
next: Thread hereditary resource scope through the body and connect lazy entry with the existing publication suffix. Current endpoint derives a precise body return; no full cached initializer, compressStored or encoded-byte theorem is claimed.
```
