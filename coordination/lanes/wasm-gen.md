# wasm-gen lane

Current slice: `ROOT-W7-20260915-010`, owning ordinary-module final-LCNF capture.
Root owns integration. No renderer lowering/linking or package publication here.

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: ready
base: 006a2e2e5570c86201e69aaf6239d279ce137103
functional-head: ca0b0a406fd8ef33eb9fa7ceed0294ecbd147394
contract-base: dc94cd4f0aa716aad5e79a7f77bafa752e9994a9
clean-at-update: true
slice: Add opt-in production owning-module frontend capture and real Verso.Doc/Renderer regressions. Preserve original compiler groups and collect final LCNF without consuming upstream native handoff.
files: Fir/Wasm/Emit/ModuleSource.lean; integration/vbp-native-session-probe/{ModuleCapture.lean,module-capture-check.sh,module-capture-check.mjs,prepare.mjs,MODULE_RESULT.md,README.md}; bugs/FIR-BUG-wasm-none-reset-shared-specialization-reader.md; coordination/lanes/wasm-gen.md
contracts: none changed; existing reset/importer/unit policies, toolchains, consumer source, runtime, W6 and ABI untouched
checks: Beam adapter/driver zero blocking diagnostics. Fresh 4.33 production adapter build 5 jobs; 4.34 adapter and actual source cone 629 jobs; driver direct Lean passes. Actual Doc and Renderer captured twice with identical final LCNF/JSON; shared helper/body edges coherent; missing entry and non-module controls reject. Exact functional HEAD make check passes 730 cases/2172 comparisons; make talos-check passes 3205 jobs plus 3166 trust stage after existing setup; deterministic artifact/check.sh passes (default non-browser gate). All three full commands rerun at functional HEAD. Final diff, 231-card validator and mailbox checks pass. Status successor changes documentation only.
bug-cards: FIR-BUG-wasm-none-reset-shared-specialization-reader (legacy reset defect remains; new provider regression passes)
blockers: No blocker to this bounded capture adapter. Renderer has 41 external source signatures, not a complete transitive closure or final host frontier.
handoff: Clean local-only checkpoint for root review, pinned by canonical completion. No main/push/package/pointer change. Stop at successful capture frontier as requested.
next: Root accepts this provider, then bounds module-owned dependency capture/assembly. Do not complete imports with the old root-local reset. ABI return/projection/join diagnostic threads remain separate.
```

## Real-source result

Verso.Doc: 317 original groups / 621 declarations. The selected DescItem.toJson
entry has seven local declarations and six external signatures, including the
formerly missing ListItem-owned helper as a real local body with both call edges.

Renderer: 28 original groups / 164 declarations. The real
`VersoBlueprint.Experimental.VirPreview.Renderer.render` entry has 151 local
declarations and 41 external signatures. Those include ordinary Lean dependencies
such as `VersoReact.Renderer.render`, not just host primitives. No Wasm import
count or execution claim follows from this inventory.

See `integration/vbp-native-session-probe/MODULE_RESULT.md` for exact source pins,
LCNF hashes, reproduction, controls and scope. Local logs live under
`.deps/native-session-probe/control/module-adapter-final-*.log` and
`module-capture-final-check.log`; evidence is disposable and reproducible.
