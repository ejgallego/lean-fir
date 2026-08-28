# wasm-gen lane

The forward-looking W7 plan lives in
[`Fir/Wasm/Emit/ROADMAP.md`](../../Fir/Wasm/Emit/ROADMAP.md). Accepted milestone
history remains on `coordination/BOARD.md`; this mailbox records the current
single-writer W7 handoff.

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: ef59c1a69b7c4aea03252d2aee809294cbbc30e6, exact accepted main
functional-head: 6a2157ce6cc44cb412d0fc61997694de99dab0d1
contract-base: ef59c1a69b7c4aea03252d2aee809294cbbc30e6; no shared semantic, helper-signature, ABI, layout, ownership, or runtime contract changed
clean-at-update: true
slice: Records and closes the rejected shared resident ByteArray.get immediate-index hot/cold experiment. The bounded candidate mirrored upstream's lean_byte_array_fget immediate mainline while retaining FIR's promoted-Nat fallback once in the shared helper. Production source was restored exactly after the candidate proved end-to-end neutral.
files: integration/lean-zip/README.md; this lane status
contracts: none. No production implementation, helper signature, ABI, layout, ownership rule, artifact ratchet, package pointer, or shared contract changed. The canonical package remains the accepted 383816-byte 2c01e190 artifact.
performance: Candidate 5413ef7f was 383824 bytes (+8) with 502 functions and an 885960-byte frontier (+24). Four same-host sampled profiles moved combined ByteArray.get/decode median Wasm self share from 0.99% to 0.38% and eliminated decoder samples. A 48-pair diagnostics-off fresh-process AB/BA campaign was end-to-end neutral: ratio 1.001593, 23/48 improving, position-adjusted ratio 1.001559. This does not meet the lean-zip acceptance rule.
checks: Candidate Lean Beam update/sync/save passed with zero diagnostics; after restoring production source, Lean Beam update/sync again passed with zero diagnostics and saveReady true. Candidate generation passed 50 native/Wasm/inflate comparisons, the zero-import levels 1-10 adapter check, package smoke, and persistent-cache/scratch frontier equality. git diff --check passed. On restored production source, make check passed 730 unique cases, 2172/2172 comparisons, zero findings, 212 bug cards, and 38 mailbox tests.
evidence: ignored worktree-local .deps/bytearray-shared-hot-cold contains the exact candidate package, two balanced timing screens plus the decisive 48-pair campaign, four candidate and four same-host baseline sampled profiles, and their aggregates. Durable conclusions are recorded in integration/lean-zip/README.md.
bug-cards: none
blockers: none
handoff: Land the documentation-only rejected-experiment record through fir/root. No W6 proof request or package publication follows.
next: Rebase on the resulting accepted main and select a fresh generation candidate from the current exact production profile; prefer source/ABI paths that avoid Nat conversion rather than another ByteArray.get placement experiment.
```
