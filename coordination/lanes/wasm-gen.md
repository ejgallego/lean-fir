# wasm-gen lane

Current slice: `ROOT-W7-20260915-012` with scope clarified by root event -017.
One-module assembly and the user-requested feasibility report are complete.
Root owns integration. No complete renderer/Wasm or host-profile claim.

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: 794b64fecec47d068c4400abe6213808081ba583
functional-head: 7b60a8dadd848e523fa4efc1d7bdb173c0793d5e
contract-base: dc94cd4f0aa716aad5e79a7f77bafa752e9994a9
clean-at-update: true
slice: Compose one actual owning-module capture into Renderer.render with signature checks, unchanged root groups and deterministic repeats. Inventory all 41 original external signatures by actual metadata/source/setup provenance and publish FEASIBILITY.md.
files: integration/vbp-native-session-probe/{ModuleAssembly.lean,module-assembly-check.sh,module-assembly-check.mjs,FEASIBILITY.md,README.md}; coordination/lanes/wasm-gen.md
contracts: none changed; production adapter, reset/importer policies, toolchains, consumer source, W6/runtime/ABI and packages untouched
checks: Beam zero blocking diagnostics; direct Lean and 629-job focused dependency cone pass. Exact functional-head assembly repeat gate passes (512 locals/103 external signatures; unchanged 28 root groups/164 declarations; selected body present; signature mismatch, missing and ambiguous setup controls reject). Original 41-row taxonomy ratchet passes. Exact functional-head make check passes 730 cases/2172 comparisons and talos-check passes 3205 jobs plus 3166 trust stage after existing setup. Authoritative root checks use explicit production-toolchain cache; fixture checks use isolated 4.34 cache. Diff/mailbox checks pass. No new artifact/browser gate: fixture-only capture/report, no production or runtime edit. Status successor is documentation only.
bug-cards: none new; initial frontend initializer error was caller API misuse, corrected with root authorization and upstream lifecycle semantics. Legacy shared-specialization reset defect remains separate.
blockers: none for this bounded slice. Seven original source signatures lack setup inputs in the isolated fixture; complete dependency closure/lowering/linking/profile/execution remain unproven.
handoff: Clean local-only checkpoint for root review; canonical completion pins containing status commit. No main/push/package/pointer changes. Stop at successful one-module assembly/report boundary.
next: Root reviews and accepts, then scopes faithful toolchain-module inputs for seven signatures in five installed Lean modules. Further source capture remains non-recursive in this checkpoint. No generated-name shim or default-setup invention.
```

## Results

The selected `VersoReact.Renderer.render` owner is resolved from actual compiler
provenance and Lake inputs. Its complete owning module has 141 groups and 565
declarations; the selected local closure has 361 declarations. Combined with the
root's 151 locals, the partial product has 512 locals and 103 typed externals.
Assembly LCNF SHA-256:
`7e09d684407485b58ba2dbbe25d8e20605b5e9b76dbdff42639c83c4ce019c7a`.

Original 41-signature source taxonomy: 24 capture-resolvable inputs, six actual
native primitives, four VIR metadata bindings, seven unavailable setup inputs
(source exists; none ambiguous). These are not final Wasm imports or profile
admission. See `integration/vbp-native-session-probe/FEASIBILITY.md` for every row,
limitations, source hashes and remaining work.

Reproduce with `bash integration/vbp-native-session-probe/module-assembly-check.sh`.
Ignored evidence under `.deps/native-session-probe/assembly/` is disposable.
Authoritative gate logs: `control/assembly-final-focused.log`,
`control/assembly-root-scoped-make-check.log`, and
`control/assembly-root-scoped-talos-check.log` under the same state root.
