# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 3ab5b747 on main
functional-head: 33d2b3f7
contract-base: c12dba9c; consume the landed W7 immediate Nat-to-USize dispatcher and generic BigNumeric limb accessors without changing helper signatures, semantic ABI, concrete layout, ownership, or failure contracts
clean-at-update: true
slice: Closed W7-W6-20260820-005 by independently reproducing its complete fresh-elaboration acceptance gate without changing proof source. A detached worktree at the resolved W6 head used independent `.lake`, `.beam`, and `.deps` state. The exact unchanged ConcreteResidentUSize module rebuilt directly, synced and saved through a new Lean Beam worker, and then rebuilt through an integration-shaped umbrella containing both ConcreteResidentNatDecision and ConcreteResidentUSize imports. No crash or diagnostic reproduced, so the accepted theorem statements and existing single-module organization remain intact rather than receiving a speculative split.
files: coordination/lanes/wasm-proof.md only; no proof, W7 implementation, runtime contract, or integration-owned source file changed
contracts: none changed. The fresh gate revalidated the accepted helper signatures, exact modulo-2^64 result, scratch restoration, layout, ownership, and validator-first failure ordering without weakening or restating them.
checks: In independent detached worktree `/tmp/fir-w6-usize-fresh` at 6444b010, `make talos-setup` created fresh local dependency/build state; `lake -d integration/talos build FirTalos.ConcreteResidentUSize` passed from source (3,086 jobs; target 8.4s); a new held Lean Beam daemon ran `lean-beam sync FirTalos/ConcreteResidentUSize.lean +all-diagnostics` and `lean-beam save FirTalos/ConcreteResidentUSize.lean +all-diagnostics`, both with zero diagnostics; after adding the two integration-owned imports only in that disposable worktree, `lake -d integration/talos build FirTalos` passed (3,165 jobs; NatDecision 6.6s, USize 8.0s). On the clean W6 branch, `git diff --check` passes; `make talos-setup` passes at Talos 0e05edbc; `make check` passes (163 scalar exports, 125 unit tests, 704 source cases across native/LCNF/V8, nine direct-machine cases, 2,121/2,121 comparisons equal, 713 aggregate cases, zero findings, 190 active bug cards, 25 mailbox tests); `make talos-check` passes (3,162 jobs).
bug-cards: none new
blockers: none. The previously reported exit-139/workerCrashed result did not reproduce under either fresh direct elaboration route or the full umbrella build. Integration retains ownership of the two umbrella imports and BOARD acceptance update.
handoff: No new functional commit is required. Functional head 33d2b3f7 is already on main through 3ab5b747 and now has independent fresh-source, fresh-worker, and integration-umbrella evidence. Integration may add `import FirTalos.ConcreteResidentNatDecision` and `import FirTalos.ConcreteResidentUSize`, rerun its gate, and accept the proof stack without a W6 source refactor.
next: Resume the substantive W6 frontier: prove that installed validateNatural/naturalHigh/naturalLow bodies satisfy CheckedNaturalCalls for promoted and arbitrary-limb NaturalObjectRel inputs, then instantiate the USize and Nat-decision StateRelated resident-replacement theorems. Immediate Nat multiplication and subtraction adaptation requests remain separately queued.
```
