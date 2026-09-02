# FIR-native VBP Verso preview widget

This integration compiles the real VBP entries

- `VersoBlueprint.Experimental.VirPreview.Widget.mount`; and
- `VersoBlueprint.Experimental.VirPreview.Widget.unmount`

from VBP revision `cad90a2f59544833a81a456b72a0fd52d8f28b1c`, using
VIR revision `90aa3f4938152d455ce4d5ddb79073729fc2df71` and Lean
`v4.34.0-rc2`. The VBP state/render implementation is neither copied nor
adapted inside FIR.

The generated module owns its memory and internalizes the complete reachable
Lean/resident-runtime closure. Its deliberate external boundary is the exact
41-operation VIR React/browser host interface. The browser adapter maps those
physical Wasm imports to the existing logical host-binding names; it does not
implement React or DOM behavior itself.

The adapter exports a generic Lean component provider:

```js
const provider = createVbpVersoViewerComponentRuntimeProvider({
  bytes,
  manifest,
  build,
});
const runtime = await provider.open({ hostBindings });

runtime.invoke(
  "VersoBlueprint.Experimental.VirPreview.Widget.mount",
  ["#preview", rpcJson],
);
runtime.invoke(
  "VersoBlueprint.Experimental.VirPreview.Widget.unmount",
  ["#preview"],
);
runtime.dispose();
```

Provider setup may be asynchronous. `mount`, `unmount`, and every retained
component/event/state/effect callback are synchronous, preserving React's
ordinary call stack and lifecycle semantics.

## Ownership

Each opened runtime owns one Wasm instance, one module-owned monotonic arena,
and one opaque host-resource table. Inputs are freshly transferred into module
memory. No Wasm address escapes. Retained callbacks use explicit JavaScript
leases, and every neutral Lean bridge borrows its closure before application so
repeat React renders do not consume the retained root. Releasing the final
JavaScript lease invokes the adapter-private checked resident decrement and
returns the owned closure graph to the recycler. Callbacks become invalid after
release or runtime disposal. `unmount` releases
the root lifecycle; `dispose` invalidates all remaining callbacks, releases
host resources, and drops the instance, reclaiming the entire arena.

This is intentionally an instance-lifetime arena, not a per-call scratch
arena: React closures may retain Lean objects across updates. `lastCall` and
`initialization` expose phase timings and frontier/resource diagnostics so
consumers can report package load and update behavior without inserting timers
into generated Lean/Wasm code.

## Exact build and smoke gate

The default ignored source views are content-pinned and checked before use:

```sh
cd integration/vbp-verso-viewer
bash check.sh
```

`VBP_ROOT` and `VIR_ROOT` may point to alternative read-only copies only when
their exact source-tree and relevant-file hashes match `source-contract.json`.
The gate builds FIR through a clean source archive so Lean 4.34 products do not
enter W7's ordinary `.lake`, regenerates twice, checks immutable identity and
`SHA256SUMS`, verifies the exact 41-import and 12-export physical surface, and
runs loading mounts, a representative ready-document mount, repeated use of
the same retained callback, updates, unmounts, Unicode RpcJson,
timing, memory-frontier, and disposal checks against a deterministic fake host.

Immutable packages are published below `_build/vbp-verso-viewer-packages/`.
The atomic `_build/vbp-verso-viewer-current` symlink names the accepted local
package for the external Chromium state/DOM-identity campaign.

The callback smoke is also the permanent regression for
`FIR-BUG-wasm-none-transitive-erased-closure-dispatch`: publication fails if a
compiler-generated boxed callback is missing from generic closure dispatch.
It also covers `FIR-BUG-wasm-none-retained-callback-borrow-boundary` by invoking
one retained ready-document component callback twice before releasing it.
