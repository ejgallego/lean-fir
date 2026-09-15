# Owning ordinary-module capture

Base: `006a2e2e5570c86201e69aaf6239d279ce137103`.
Scope: `ROOT-W7-20260915-010`; W7 generation only, root owns integration.

## Implementation

`Fir.Wasm.Emit.ModuleSource.compile` accepts unchanged source and Lake's resolved
`Lean.ModuleSetup`. It calls upstream `Parser.parseHeader`,
`Elab.processHeaderCore`, and `Elab.IO.processCommands`. A final impure LCNF pass
records the original completed declaration groups without consuming them. Lean's
normal validation and native handoff still run, including compile-time code;
native IR is not FIR's compilation input.

This preserves the actual module's visibility, imports, plugins, package,
specialization cache and source group boundaries. It neither imports the target
into itself nor resets/reseeds mappings. Ordinary compilation explicitly disables
postponement and asynchronous elaboration. The adapter rejects non-module inputs,
self-imported targets and leftover postponed groups. Like upstream's frontend,
its CLI caller enables initializer execution before importing modules.

`CapturedModule.artifact` checks that the root was captured, then uses upstream
`collectUsedDecls` in the completed environment. Imported functions remain typed
external signatures. It does not recompile or inject imported bodies. Existing
capture providers, reset/importer policy and source-unit selection are unchanged.

## Exact real-source results

The fixture retains its pinned VBP/Verso/VIR sources, dirty RPC overlay and exact
Lean 4.34.0-rc2 (`6a10ac8c22beadecabdbb0919c2b50214762f91d`). Production FIR
stays on 4.33. The new production adapter builds in both toolchains; the fixture
copies it through a SHA-checked overlay, not a separately maintained implementation.
`SOURCE.json` records all source identities and overlay hashes.

| Module / selected entry | Original groups | Module declarations | Reachable local declarations | External signatures |
| --- | ---: | ---: | ---: | ---: |
| Verso.Doc / private DescItem.toJson | 317 | 621 | 7 | 6 |
| VersoBlueprintVir.Preview.Renderer / real Renderer.render | 28 | 164 | 151 | 41 |

The DescItem closure contains the previously missing ListItem-owned
`Array.mapMUnsafe.map` specialization body and both its inline/block call edges.
No helper is manually seeded or extra caller selected for compilation: the real
module's original compiler groups produce this coherent result.

Final-LCNF text SHA-256:

- DescItem: `420e88ec3fb370b5f78ec11da944f76952f29175933893644c7d44e7bcb3488c`
- Renderer: `819fed859b7d21f3988072f7be53969705614de8d047f41b6c8b8bc488704073`

## Reproduce and controls

From the W7 worktree:

```sh
bash integration/vbp-native-session-probe/module-capture-check.sh
```

The script builds the exact source dependencies and adapter, directly checks the
driver, then captures each actual module twice. It checks identical JSON and
LCNF, original group/declaration counts, the shared-helper body/calls, defining
module provenance for every external signature, and rejection of missing entries
and non-module setup. All assertions pass. The 4.34 source cone is 629 Lake jobs.
Beam reports zero blocking diagnostics for both the production adapter and driver.
The production adapter's direct 4.33 cone is five jobs.

At functional commit `ca0b0a406fd8ef33eb9fa7ceed0294ecbd147394`, the exact
real-source repeat gate, `make check` (730 cases / 2172 comparisons),
`make talos-check` (3205 jobs plus 3166-job trust stage after existing setup),
and `bash integration/talos/artifact/check.sh` all pass. The latter is the
default non-browser deterministic gate; no renderer Wasm or browser execution
is part of this slice. The containing handoff adds documentation only.

Generated evidence lives under `.deps/native-session-probe/ordinary-module/`:
each `first/` and `repeat/` contains `verso-doc/` and `renderer/`, each with
`entry.lcnf` and `module-capture.json`. The latter includes the exact declaration
inventory and external name-to-defining-module map. Local evidence is disposable;
the script and immutable source identities are the reproducible record.

## Remaining boundary

The 41 signatures are **not** the historical viewer's 41 host imports. They include
Lean dependencies such as `VersoReact.Renderer.render`, JSON decoders, style
constants and generated specializations, as well as runtime and VIR bindings.
No complete transitive renderer closure, lowering, resident linking, Wasm
execution or host-profile admission is claimed here.

Next, the canonical driver needs to consume module-owned capture products across
the reachable dependency modules, preserving each compiler unit and resolving
its imports. That is a separate bounded follow-up after this adapter is accepted;
the old root-local reset must not be reintroduced as a dependency-completion step.
Only the resulting complete closure can establish the actual runtime/host frontier.

No toolchain, W6 proof, runtime, ABI/layout, consumer source, accepted package or
canonical pointer changes. The legacy reset bug remains explicit in
`FIR-BUG-wasm-none-reset-shared-specialization-reader`.
