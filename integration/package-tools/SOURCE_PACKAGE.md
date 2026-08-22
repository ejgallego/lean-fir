# Source-package discovery descriptor

`browser-benchmarks/source-package/v1` is a small, producer-authored discovery
view for immutable browser packages. FIR derives it from a package's existing
`BUILD.json`, verified Wasm module, and local verifier policy. It answers the
producer questions below without teaching a catalog the package-specific BUILD
schema:

- which exact source revisions and relevant files produced the package;
- which project, backend, and exact Lean toolchain produced the Wasm artifact;
- which adapter and API version expose it;
- which checksums, verifier policy, and smoke accept it;
- whether the verifier accepts or provisionally exposes it;
- which adapter operations are production or diagnostic, their versioned
  input/result contracts, and their public timing fields;
- which startup and initialization fields live outside per-call timings;
- which checksummed producer evidence files accompany the executable; and
- who owns memory, values crossing the boundary, and instance reclamation.

The descriptor deliberately excludes workload inputs, semantic oracles,
application result schemas, benchmark samples, thresholds, and performance
claims. Those remain in Illuminate, Verso, lean-zip, or another consumer.

The normalized shape is:

```text
schemaVersion: browser-benchmarks/source-package/v1
package: name, package-specific BUILD schema, verifier-backed acceptance
provenance.sources[]: role, repository, commit, dirty, relevantFiles[]
producer: project, backend, exact Lean identity and Wasm artifact, adapter/API
producer.adapter: startup and initialization field names
verifier: policy version/name, SHA256SUMS inventory, smoke, evidence files
operations[]: name, production|diagnostic, input/result contract, phase fields
ownership: memory/arena/reclamation plus input, encoded graph, output transfer
```

`source-package.mjs` constructs and validates this view. A package policy must
list operations in the same order as the adapter capability in `BUILD.json`, so
adding or renaming an adapter operation fails closed until its production or
diagnostic role and input/result contract are reviewed. Evidence filenames must
name checksummed payloads. Lean version text must expose both a normalized
version and full commit. Missing `relevantFiles` are normalized to an empty
array; consumers do not need package-specific optional-field checks.

The contracts are identifiers owned by the versioned adapter API, not embedded
JSON schemas. This keeps JavaScript type details and workload semantics in the
producer while still letting a catalog reject an operation it does not know how
to call. Startup and initialization inventories similarly name public result
fields; they do not impose a universal timing ontology.

For the coordination draft, `verifyBrowserPackage(...).sourcePackage` exposes
the descriptor in memory. It is not yet added to `BUILD.json`, copied as a new
payload file, or used in an immutable package identity. HitScene and selection
package bytes therefore remain unchanged while their owners review the real
generated views. Publication should happen only after the remaining consumer
review confirms the checksummed-sibling recommendation.
