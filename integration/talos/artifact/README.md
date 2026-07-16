# FIR Wasm artifact lane

This package turns the initial supported FIR corpus into deterministic WebAssembly 1.0
binary artifacts, then runs those artifacts in Node's standard `WebAssembly` engine with
a small semantic FIR host.

The corpus covers tagged and heap-allocated natural literals, heap strings, constructor
allocation and projection, exact and default constructor cases, and a transitively
reachable constructor graph. Each `.wasm` file is accompanied by a manifest that describes
its semantic runtime imports. The separate `FirWasmOracleMain.lean` program runs the same
named corpus through the W3 FIR/Talos differential oracle and writes its comparable
observations beside the artifacts. The Node runner compares V8 directly with those live W3
results; no expected semantic observations are frozen in the emitter.

World and trace observations remain empty in this corpus because the current
`lowerSupported` contract deliberately excludes external declarations. Add an
effect-producing fixture only after that supported-domain change lands through W4.

Run the complete lane-local check with:

```text
./check.sh
```

This builds the Lean emitter, runs the W3 oracle through Lean, emits the corpus and oracle
results twice, byte-compares all outputs, validates and instantiates every module in Node,
executes `main`, and compares the V8 observation with W3. It requires Lean 4.32, the
worktree-local Talos setup, and Node; no external WAT or WebAssembly CLI is required. The
oracle uses `lean --run` so a fresh worktree does not native-compile the full upstream Wasm
semantics just to check this corpus.

To emit one fixture manually:

```text
lake exe fir-wasm-artifact literal /tmp/fir-wasm-corpus/literal.wasm
lake -d .. env lean --run ../FirWasmOracleMain.lean all /tmp/fir-wasm-corpus
node run-artifacts.mjs /tmp/fir-wasm-corpus
```
