# Checked retained initializer: source execution and publication

This optional W6 proof cone consumes `RetainedRC2.program`, generated from the
immutable lean-zip source snapshot by the W7 checked-capture recipe. It does
not contain a copied initializer AST. `RetainedDeclarations` extracts the two
external declarations from that same definition with kernel-checked lookup
and body equations. Production ordinary/closed/resident lowering in the
unchanged `RetainedRC2` harness consumes the definition's readback too.

`RetainedInitializer.reaches_published` proves that the actual initializer
`Zip.Spec.DeflateStoredCorrect.deflateStoredPure._closed_0` reaches its exact
published source state in 12 steps from a cold cache. The runtime contains a
fresh singleton Array holding tagged zero, its cache publication, unchanged
world, and the original trace followed by exactly the `Array.mkEmpty` and
`Array.push` events. A thirteenth step returns.

`evaluates_and_preservesCaller` connects that reached state to historical
caller facts. It asks for the saved fact interpretation, witness transport
and current live-heap relation; it does not ask for a region, graph separation,
prefix preservation, body execution or target path. The caller environment
stays fixed. This remains pointwise saved-caller preservation, not recursive
suspended-stack reconstruction.

`reaches_published_withFrames` generalizes the execution to an arbitrary
suspended frame stack. `resumesCaller` derives the exact 13-step prefix through
destination binding, restoring the caller's environment, joins and remaining
frames, and discharges `ReuseTokenOrdinaryBindTransport` for that result.

`return_pop_preservesCaller` applies this to the existing concrete return/pop
consumer: the 13-step source prefix and the two target return/bind steps end
in related states with the full caller cache/ABI frame restored. Its premises
still include the target return focus, callee frame, witness/capacity transports,
historical caller scope and suspended tail. It does not establish the target
callee prefix or reconstruct the stronger hereditary resource stack.
`resumedCaller` is a transparent proof-only state description, not an extra
compiled executable or a replacement source program.

The two source external contracts are uniform primitive laws, not a
per-program invariant. `FreshArrayExternalContract` specifies empty allocation
and the fresh/non-full tagged-push branch. `freshArrayExternals_contract`
provides an executable consistency witness; other requests are rejected by
that deliberately limited model. This is **not** the production external
implementation. Its connection to concrete external admission and resident
helper execution remains to be proved. No whole lean-zip or Wasm artifact
correctness follows from this source endpoint.

## Reproduce

From the W6 worktree, with repositories containing the exact source objects:

```sh
bash integration/talos/retained-initializer/check.sh \
  /path/to/lean-zip /path/to/zip-common
```

The script archives lean-zip `273d0d6c` and zip-common `4425bab1` into the
worktree-local `.deps/retained-rc2`, copies maintained source templates, and
uses the worktree's official toolchain and Talos setup. It fetches no substitute
source revision and shares no mutable build state with W7. Lake may obtain its
pinned build dependencies if absent. Source/setup identity and the limitations
of capture are documented in `Fir/Compiler/LCNF/README.md`. Adding the Talos
proof dependency changes the private Lake setup identity, not the captured
source or initializer body.

The gate builds the consumer, imports the checked definition in a fresh
process, and forces direct batch elaboration with an exact per-endpoint axiom
audit. The source endpoint inherits the seven **existing** native-evaluation
axioms of `boxUsesTaggedRepresentation_boxedScalar`, due to upstream opaque
expression comparison. It introduces no new native evaluation or axiom.
The captured program/body equations remain free of generated axioms. Generic
external-model and finite-prefix helper proofs use standard axioms and are
also in the ordinary Talos trust inventory.
