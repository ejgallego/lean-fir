# FIR Wasm artifact lane

This package turns the initial supported FIR corpus into deterministic WebAssembly 1.0
binary artifacts, then runs those artifacts in Node's standard `WebAssembly` engine with
a small semantic FIR host.

The corpus covers erased and maximum-width unsigned results and entry arguments, tagged
argument handles, tagged and heap-allocated natural literals, heap strings, constructor
allocation and projection, exact and default constructor cases, and a transitively
reachable constructor graph. Each `.wasm` file is accompanied by a manifest that derives
its entry parameter and result ABI, records its semantic inputs, and describes its semantic
runtime imports. The separate `FirWasmOracleMain.lean` program runs the same named corpus
through the W3 FIR/Talos differential oracle and writes its comparable observations beside
the artifacts. The Node runner compares V8 directly with those live W3 results; no expected
semantic observations are frozen in the emitter.

World and trace observations remain empty in this corpus because the current
`lowerSupported` contract deliberately excludes external declarations. Add an
effect-producing fixture only after that supported-domain change lands through W4.
Heap-backed entry arguments likewise remain outside the corpus until the manifest and both
engines share an explicit initial-runtime format.

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

To compile a Lean source declaration through the real final-impure LCNF
pipeline and emit it directly, import the command after the declaration is
available. Closed declarations need no invocation clause:

```lean
import Fir.Wasm.Emit.Command

def answer : UInt64 := 42

#fir_wasm_emit answer to "answer.wasm"
```

Parameterized declarations record one checked semantic invocation alongside
the reusable module. The module's parameter ABI is the argument schema:

```lean
def idUSize (value : USize) : USize := value

#fir_wasm_emit idUSize with [usize(42)] to "id-usize.wasm"
```

The command writes `answer.wasm`, the Node-compatible ABI manifest
`answer.wasm.json`, and the captured final-impure program
`answer.wasm.lcnf`. Invocation arguments are checked against the ABI kinds
derived from the compiled entry; changing them changes only the manifest, not
the module or captured LCNF. The command accepts `erased`, `tagged(n)`,
`uint8(n)`, `uint16(n)`, `uint32(n)`, `uint64(n)`, and `usize(n)` arguments,
with range checks before compilation. Heap-backed initial arguments, external
declarations, and recursive source programs remain explicit follow-up work.

The lane-local source fixture executes compiler-produced identity declarations
for `UInt8`, `UInt16`, `UInt32`, `UInt64`, and `USize` at their boundary values.
The Node runner derives every physical argument from the manifest and
normalizes signed WebAssembly `i32` results back to the declared unsigned
source width before comparison.

Lean 4.32's compiler-produced small `Nat` literal currently exposes a shared
supported-domain mismatch tracked by
`FIR-BUG-wasm-none-compiler-nat-literal-kind`; the bridge rejects that program
without rewriting its final-impure types.
