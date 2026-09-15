# Owning-module plugin lifecycle diagnosis

Request: `ROOT-W7-20260915-025`; base:
`f7dfd06c5aac860c7562dfbfc7a2ef37984c2678`.

## Conclusion

The module-product failure is caused by **overlapping aggregate and per-module
native plugin images in one process**. The renderer's actual setup loads
`libverso_VersoManual.so`, which already initializes `VersoManual.Ext`. The
actual setup for compiling `VersoManual.Basic` later loads the separate
`verso_VersoManual_Ext.so`, whose initializer attempts the same registration.

A fresh `Basic` frontend works. Neither repeated `Basic` capture nor repeating
the renderer's same plugin list causes the duplicate. No replay of the
26-module worklist is needed: renderer followed immediately by `Basic` suffices,
and a plugin-only control removes source capture entirely.

This is a FIR fixture process-composition limitation, not invalid source or
LCNF. Installed `Lean/LoadDynlib.lean` documents that shared symbols across
plugins require separately linked shared code. No new upstream compiler defect
or justification for suppressing initializers is established here.

## Controlled matrix

Each row starts in its own Lean process, using unchanged real source and actual
Lake setups. The gate repeats all rows in independent processes and compares
all observations, including sorted mapped shared-library paths.

| Case | Result | Successful captures |
| --- | --- | ---: |
| Fresh `Basic` | Pass | 1 |
| Renderer, then `Basic` | Duplicate extension at `Basic` header | 1 |
| `Basic`, then `Basic` | Pass | 2 |
| Renderer plugin list, then the same list | Pass | 0 |
| Renderer plugin list, then standalone `Ext` | Duplicate extension in plugin load | 0 |

Fresh `Basic` records 841 groups / 2,443 declarations. The requested real
`Verso.Genre.Manual.instToJsonInline.toJson` entry has seven local declarations
and six external signatures. No resulting bodies are transported into or used
to resume the module product.

Before loading the aggregate manual plugin, both tracked extension counts are
zero. After it, `inlineExtensionExt` and `blockExtensionExt` each occur once.
The reduced failing step starts with only the aggregate manual image mapped,
then maps the standalone `Ext` image and reports:

```text
invalid environment extension, 'Verso.Genre.Manual.inlineExtensionExt' has already been used
```

Exactly one of each extension remains registered: duplicate admission fails
rather than replacing it. No subsequent action runs in that failed process.

## Reduced reproducer and mechanism

`ExtensionLifecycle.lean` mode `plugins-root-ext` reads the two actual setups,
loads the renderer's 11 plugins in their actual order through
`withImporting (loadPlugin path initFn)`, and then loads the standalone `Ext`
plugin selected from the actual `Basic` setup. This mode needs no frontend,
environment import, LCNF capture, entry selection or Wasm. The preceding plugins
retain actual native dependencies; this is a reduced real-input reproducer,
not a claim that all dependency libraries can be removed.

Read-only dynamic-symbol inspection shows that both shared images define:

```text
initialize_verso_VersoManual_Ext
lp_verso_Verso_Genre_Manual_inlineExtensionExt
lp_verso_Verso_Genre_Manual_blockExtensionExt
```

Generated `VersoManual/Ext.c` uses file-local `_G_initialized` and
`_G_runtime_initialized` guards. They do not deduplicate across these separately
loaded images. The extension names instead live in Lean's process-global
`persistentEnvExtensionsRef`, whose registration function rejects duplicates.
Plugin-only failure and passing identical-plugin repetition distinguish this
from the earlier interpreted-initializer replay hypothesis.

## Exact inputs

The isolated Lean is `4.34.0-rc2`, revision
`6a10ac8c22beadecabdbb0919c2b50214762f91d`. VBP remains
`c4430bfe2c898c0312903ae46c45b410d253ebf4` with its pinned RPC overlay; Verso is
`52c8c9557bcb5cc8c0edc0ee37e74311a3d53ee9`. No consumer build state is used.
Production FIR remains on 4.33.

| Input | SHA-256 |
| --- | --- |
| `Renderer.lean` | `f71035bbed37d779db8efdd77c4a4f471512efd2f01daa5008ff682e43230926` |
| Actual renderer setup | `87a5de6457a6159066999fa8bd76a7f053d665975ea02c66469e7b5e81bdea34` |
| `VersoManual/Basic.lean` | `09419effa741dc89284256d84219685e15c99034dd708f672e7c8d007b86457d` |
| Actual `Basic` setup | `209e878c29a4987120dcf6973a598abc3504d147bd438a3979c866730f7e315c` |
| Aggregate `libverso_VersoManual.so` | `4f1fb6fb84718bc46417279959e4c32ccdf44c1836efc6ec58bf05c79d7612c6` |
| Standalone `verso_VersoManual_Ext.so` | `89feb5232a6ecddb1d80261925138174b7810a5619f6eb89c8b5563f6aa4287e` |

Setup hashes include absolute worktree paths. These identify the exact run, not
a path-independent release format. The gate records every plugin path/hash and
initializer identity, `Ext` source/generated-C hashes, and source provenance in
`.deps/native-session-probe/lifecycle/inputs.json`, rejecting changes during the
experiment. Both setups have zero `dynlibs`; plugin counts are 11 and 16.

## Reproduce and hand off

From W7:

```sh
bash integration/vbp-native-session-probe/extension-lifecycle-check.sh
git diff --check
make check
```

The script builds the 629-job source cone, directly checks the Lean fixture,
runs the five controls twice, verifies expected steps and overlapping symbols,
and compares repeated JSON. Beam checks fixture elaboration only, never the
native lifecycle experiment. Registry and process-map reads are observation
only; captured environments stay alive through all observations.

Output: `.deps/native-session-probe/lifecycle/{first,repeat}/`, `inputs.json`,
`summary.json`. No module-product worklist, system `/tmp`, production edits,
plugin/source changes, suppression, registry reset or serialization is used.

The existing bug `FIR-BUG-wasm-none-module-product-extension-registration` is
classified, not repaired. Root must separately choose how to preserve each
frontend's native context: for example, a verified compatible image policy or
a process boundary with explicit compiler-product transport. Neither is
implemented or declared sufficient here. Capture fidelity, owner and signature
checks remain necessary. Work stops at this classification; renderer closure,
host-profile and Wasm acceptance remain outside the result.
