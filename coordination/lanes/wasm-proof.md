# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 302a58c0322dfac1a1997ae9d987f84a35030eff
functional-head: f9462c751983448a212d9cf813f3747b998f4910
contract-base: 302a58c0322dfac1a1997ae9d987f84a35030eff
clean-at-update: true
slice: Completed the third PA1 case slice. ObjectCaseDiscriminatorSupported preserves the validator's precise object-family kind and records its directional refinement to tobject. The concrete WP and finite-path simulators now transport .object, .tagged, and .tobject discriminator lanes through PhysicalValueRel.ofRefines without changing physical bits. ConcreteStructuredObjectCaseSafeAt consequently retains only the live source tag's UInt32 bound; compiler-local kind equations are fully derived. The existing abiCaseProgram exercises the precise .tagged lane.
files: docs/pass-correctness-plan.md; docs/w6-source-admission-audit.md; integration/talos/PLAN.md; integration/talos/FirTalos/ConcreteRuntime.lean; integration/talos/FirTalos/ConcreteCompilerCorrectness.lean; integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/FirTalos/ConcreteStructuredValidation.lean; coordination/lanes/wasm-proof.md
contracts: proof-interface generalization only; no shared semantic runtime, ABI, layout, validator, lowering, instruction, emitted-code, ownership, or resident-helper contract changed
checks: Lean Beam ConcreteRuntime, ConcreteCompilerCorrectness, ConcreteStructuredSimulation, and ConcreteStructuredValidation update/sync/save (pass, zero errors); lake -d integration/talos build FirTalos.ConcreteStructuredValidation FirTalos.ConcreteResumableWasm FirTalos.Correctness.FunctionCaseExample (pass: 3133 jobs); git diff --check (pass); make check (pass: 730 unique validation cases, 2172/2172 comparisons equal, coverage/trusted-assumption/mailbox gates green, exactly one trusted axiom); make talos-setup (pass: Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254); make talos-check (pass: 3189 jobs, receipt 70541be93669ea3af4ef5f522488dc236228448aadf8b5e90675364694c98b60)
bug-cards: none
blockers: none
handoff: clean W6 functional head `f9462c75`, based exactly on accepted main `302a58c0`; ready for fast-forward integration
next: Derive the remaining live object-case UInt32 tag bound from compiler-produced constructor provenance, then resume the other PA1 result/object gaps. Consume W6-W7-20260830-001 before choosing the non-directional return policy.
```
