# Source-package discovery descriptor

`browser-benchmarks/source-package/v1` is a small, producer-authored discovery
view for immutable browser packages. FIR derives it from a package's existing
`BUILD.json`, verified Wasm module, and local verifier policy. It answers six
questions without teaching a catalog the package-specific BUILD schema:

- which exact source revisions and relevant files produced the package;
- which project and backend produced the Wasm artifact;
- which adapter and API version expose it;
- which checksums, verifier policy, and smoke accept it;
- which adapter operations are production or diagnostic and which public timing
  fields each diagnostic operation reports; and
- who owns memory and how the instance-lifetime arena is reclaimed.

The descriptor deliberately excludes workload inputs, semantic oracles,
application result schemas, benchmark samples, thresholds, and performance
claims. Those remain in Illuminate, Verso, lean-zip, or another consumer.

The normalized shape is:

```text
schemaVersion: browser-benchmarks/source-package/v1
package: name and package-specific BUILD schema
provenance.sources[]: role, repository, commit, dirty, relevantFiles[]
producer: project, backend, exact Wasm artifact, adapter/API version
verifier: policy version/name, SHA256SUMS inventory, packaged smoke
operations[]: name, production|diagnostic, public phase/timing field names
ownership: capability version, memory owner, arena model, reclamation
```

`source-package.mjs` constructs and validates this view. A package policy must
list operations in the same order as the adapter capability in `BUILD.json`, so
adding or renaming an adapter operation fails closed until its production or
diagnostic role is reviewed. Missing `relevantFiles` are normalized to an empty
array; consumers do not need package-specific optional-field checks.

For the coordination draft, `verifyBrowserPackage(...).sourcePackage` exposes
the descriptor in memory. It is not yet added to `BUILD.json`, copied as a new
payload file, or used in an immutable package identity. HitScene and selection
package bytes therefore remain unchanged while their owners review the real
generated views. Publication should happen only after consumers accept whether
the descriptor belongs in `BUILD.json` or in a checksummed sibling file.
