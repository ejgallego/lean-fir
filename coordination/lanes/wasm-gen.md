# wasm-gen lane

The forward-looking W7 plan lives in
[`Fir/Wasm/Emit/ROADMAP.md`](../../Fir/Wasm/Emit/ROADMAP.md). Accepted milestone
history remains on `coordination/BOARD.md`; client-specific contracts remain
inside their integration directories. This mailbox records only the active
queue and current handoff boundary.

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: 85481c6702810d740ec2bcc571be1c602b497e66 on main
functional-head: 131efaad, resident Array trusted-call split and lean-zip scaling evidence
contract-base: 85481c6702810d740ec2bcc571be1c602b497e66 on main. Consumes the accepted generic Array layout/refinement invariant; changes no semantic operation, concrete layout, symbolic-Wasm instruction, ownership rule, emitted-helper signature, or application ABI
clean-at-update: true
slice: Split resident Array calls into checked raw/public bodies and trusted typed-closed-application bodies. The trusted bodies remove only the common address/header validator; exact symbolic suffix guards freeze unchanged bounds, reference counting, uniqueness, copy-on-write, allocation, and recursive release behavior. Preserve the existing checked linker steps and add explicitly named trusted steps used only by closed-application policies. Retain malformed raw-boundary trapping, constant-time address guards, zero imports, deterministic packages, and a thin order-balanced lean-zip scaling probe. Correct the roadmap history: 1d79658d was FIR's first O(1) Array address implementation; the validator predates it
files: Fir/Wasm/Emit/ResidentArray.lean; Fir/Wasm/Emit/ResidentLinker.lean; Fir/Wasm/Emit/ROADMAP.md; integration/talos/artifact/resident-array-client.mjs; integration/lean-zip/array-scaling-bench.mjs; integration/lean-zip/README.md; integration/lean-zip/raw-closure-contract.json
contracts: none
checks: Lean Beam sync/save on the final ResidentLinker revision passed with zero diagnostics (source hash ce750cc5206d1f45); focused lake build Fir.Wasm.Emit.ResidentLinker passed; node --check passed for both changed JavaScript files; git diff --check passed; make check passed (125 harness tests, 701 native/LCNF cases, 9 direct-machine cases, 701 native/LCNF/V8 cases, 2,112/2,112 comparisons); make talos-setup passed; make talos-check passed all 3,148 jobs; bash integration/talos/artifact/check.sh passed the standalone malformed-boundary/ownership Array checks, all validation cases, and deterministic byte-exact package builds. The exact lean-zip raw package gate passed 5 cases at all levels 1--10, independent inflate, zero-import adapter, persistent/scratch ownership, package smoke, and repeat generation; candidate Wasm is 1,628,872 bytes with SHA-256 702b6a4e9f0d9896770f52cfae8eefc9bb8b9a2c95e056950f9d6cf65d8eed84. Order-balanced raw-entry A/B was neutral at 4 KiB and improved every pair at 64/256 KiB: paired medians -5.47 ms (about 2.6%) and -15.39 ms (about 1.9%), with identical output digests and flat frontiers
bug-cards: none
blockers: none
handoff: Integration may consume the green W7 slice through 131efaad after resolving the actual wasm/generation branch head and rebasing it on the then-current main. Keep the independent W6 read-only invariant audit in thread W7-W6-20260814-001 separate from generation readiness
next: Obtain W6's proof-impact audit and land this generation slice. After acceptance, regenerate immutable lean-zip packages from accepted main rather than publishing the dirty preview. Then resume G2's production/diagnostic adapter split; the static simple-ground experiment remains parked
```
