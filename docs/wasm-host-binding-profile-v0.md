# FIR Wasm host-binding profile, render-core v0

Status: **draft contract** (2026-09-13). This document defines the smallest
portable host boundary that an FIR-generated Wasm renderer may use. It is a
contract for generated artifacts and their adapters, not a replacement for
VIR's native binding implementation.

VIR remains the reference for the *logical* Lean/JavaScript API. FIR must make
the physical Wasm boundary explicit and fail closed when an artifact asks for a
capability not declared by this profile.

## Scope

`fir.wasm-host-binding/render-core/v0` covers synchronous construction of host
render values from an already-typed Lean input. It is intended for
`VersoBlueprint.Experimental.VirPreview.Renderer.render` and similarly bounded
render roots.

It includes:

- exact import and export inventory validation;
- scalar and UTF-8 values marshalled through the module's Lean representation;
- opaque host-resource tokens for JavaScript objects such as React nodes,
  props, arrays, and element types; and
- synchronous host calls that return a scalar, Lean value, unit, or opaque
  host resource.

It deliberately excludes component factories, hooks, effects, retained
callbacks, `LeanRef` conversion, promises/RPC, cancellation, subscriptions,
browser mounting, and DOM ownership. A capture requiring one of these is a
profile mismatch, not permission to silently add an adapter escape hatch.

## Boundary vocabulary

Every import and public export has a descriptor containing its logical name,
physical parameter/result kinds, and ownership. The only v0 kinds are:

| Kind | Physical boundary | Rule |
|---|---|---|
| `unit` | Lean immediate unit | no host identity crosses the boundary |
| `bool`, `nat`, `float` | the existing explicit scalar codec | conversion is checked and canonical |
| `string` | an owned Lean UTF-8 string | copied; JavaScript does not retain a module pointer |
| `lean-value` | module-owned Lean word | only the generated module interprets it |
| `resource` | opaque module token naming an adapter-owned host value | it is not a JavaScript pointer or a reusable raw Wasm address |

The descriptor marks every `resource` occurrence as `borrow`, `take`, or
`return`:

- `borrow` resolves a live adapter resource without transferring it;
- `take` resolves and removes a live adapter resource exactly once; and
- `return` allocates a fresh resource token for a non-null host value.

The adapter rejects a missing, stale, double-taken, or malformed token. It must
invalidate all remaining tokens when the Wasm instance is disposed. A resource
must never be represented by a raw pointer supplied by the host.

## Manifest shape

The generated package records a versioned binding-profile section. Names are
illustrative; the authoritative emitted manifest may add ordinary package
identity and integrity fields.

```json
{
  "bindingProfile": "fir.wasm-host-binding/render-core/v0",
  "imports": [
    {
      "name": "Lean.Vir.React.Node.createElement",
      "params": ["resource:borrow", "resource:borrow", "resource:borrow"],
      "result": "resource:return",
      "mode": "sync"
    }
  ],
  "exports": [
    { "name": "…Renderer.render", "params": ["lean-value"],
      "result": "resource:return" }
  ]
}
```

Manifest validation is exact: the declared imports must equal the Wasm module's
function-import frontier, use the expected namespace, have unique names, and
have descriptors accepted by the profile. An adapter exposes exactly those
imports. Unknown imports, a duplicate descriptor, an undeclared module import,
a kind mismatch, or an unsupported mode is an initialization error.

## Conformance boundary

The shared adapter support is intentionally mechanical:

1. resource-token registry with `borrow`, `take`, return, and disposal checks;
2. manifest/import-frontier validator;
3. checked scalar and UTF-8 codecs; and
4. a synchronous descriptor dispatcher.

Each consumer supplies its host-function mapping and its rendered-input
construction. It does not copy resource ownership or import-validation code.
Conformance tests must cover an exact accepted frontier plus rejection of an
unknown import, stale/double-taken token, invalid scalar/string result, and
post-disposal use. Consumer visual/browser tests are additional; passing this
profile does not claim browser rendering or React lifecycle correctness.

## Relationship to VIR and later profiles

VIR binding metadata is a crosswalk input: it tells us the logical external
operation, signature, and retention expectation. It is not itself FIR's wire
ABI, and FIR does not import VIR's native runtime implementation.

Any retained Lean closure or host callback requires a separate profile version
that names its bridge export, argument/result descriptors, retain/release
operation, and disposal behavior. Async, promise, effect, component, and RPC
families each require the same explicit extension. They must not be folded into
render-core v0 after the fact.

## First adoption

The isolated Lean 4.34 VBP renderer probe records its actual import frontier
against this profile. If that frontier stays inside v0, wasm-gen may add a
small shared runtime implementation and profile fixture in its leased probe
directory. If it does not, the first unsupported import is reported and the
contract remains unchanged pending a separately reviewed extension.
