# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 91b2f3acbf4f6a57bf73592aa53a2f6dd02aaf30
functional-head: 7998eba5e4931838b1bcf61b15262b863b94723a
contract-base: 91b2f3acbf4f6a57bf73592aa53a2f6dd02aaf30
clean-at-update: true
slice: Completed the second PA1 result slice. The existing StateRelated plus local-layout agreement now derives semantic typing for every residual compiler local, so no duplicate environment invariant is needed. Added a minimal current-node return use-site boundary for genuinely non-directional ABI edges, wired it to aligned validation, and factored one physical-result publication theorem shared by direct calls, saturated closures, and lazy-cache hit/miss. A structural audit of all 44 built-in artifact fixtures found no non-directional return edge; W6-W7-20260830-001 asks W7 to run the same read-only audit on prettyM/pretty-format and lean-zip before W6 chooses directional compiler admission versus retained precise producer origin.
files: docs/pass-correctness-plan.md; docs/w6-source-admission-audit.md; integration/talos/PLAN.md; integration/talos/FirTalos/ConcreteFinalLcnfTyping.lean; coordination/lanes/wasm-proof.md
contracts: proof-only semantic provenance and publication helpers plus planning status; no runtime semantics, ABI definition, layout, lowering, central relation, emitted-code, or shared-contract change
checks: Lean Beam ConcreteFinalLcnfTyping update/sync (pass, zero diagnostics, before the installed wrapper registry-format change); lake -d integration/talos build FirTalos.ConcreteFinalLcnfTyping (pass: 3128 jobs); git diff --check (pass); make check (pass: 730 unique validation cases, 2172/2172 comparisons equal, coverage/trusted-assumption/mailbox gates green, exactly one trusted axiom); make talos-setup (pass: Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254); make talos-check (pass: 3189 jobs, receipt e89a6bbfdbc6a12c70248eb85637ceccb5f87e53025fad6c3d3dff5c2f79aab2)
bug-cards: none
blockers: none
handoff: active clean proof checkpoint at functional head 7998eba5e4931838b1bcf61b15262b863b94723a; ready for integration as a proof-only PA1 slice while the production return-directionality audit proceeds independently
next: Consume W6-W7-20260830-001. If production returns are directional, derive the compiler-owned directional return admission and add a negative rejection fixture; otherwise construct only the precise producer-origin fact for the reported non-directional sites. Then close the remaining object/schema and case class-C rows before PA2 assembly.
```
