# FIR Wasm artifact lane

This package turns the initial supported FIR corpus into deterministic WebAssembly 1.0
binary artifacts, then runs those artifacts in Node's standard `WebAssembly` engine with
a small semantic FIR host.

The first corpus covers natural literals, constructor allocation and projection, exact
constructor cases, and default cases. Each `.wasm` file is accompanied by a manifest that
describes its semantic runtime imports and its expected observable result. The expected
observations are checked snapshots of the W3 differential results at this lane's base;
generating or checking them directly from W3 is the next integration step once this
worktree has its own complete Talos dependency cone.

Run the complete lane-local check with:

```text
./check.sh
```

This builds the Lean emitter, emits the corpus twice, byte-compares both WebAssembly and
manifest outputs, validates and instantiates every module in Node, executes `main`, and
compares the semantic observation with its manifest. It requires Lean 4.32 and Node; no
external WAT or WebAssembly CLI is required.

To emit one fixture manually:

```text
lake exe fir-wasm-artifact literal /tmp/fir-wasm-corpus/literal.wasm
node run-artifacts.mjs /tmp/fir-wasm-corpus
```
