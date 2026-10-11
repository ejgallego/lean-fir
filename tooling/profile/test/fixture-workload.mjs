export const metadata = {
  id: "fir-tooling-wasm-loop",
  purpose: "exercise steady-only Wasm CPU-profile attribution",
};

export async function setup({ wasmBytes, sidecar }) {
  const { instance } = await WebAssembly.instantiate(wasmBytes);
  const originalName = sidecar.functions[0].name;
  let sidecarMutationBlocked = false;
  try {
    sidecar.functions[0].name = "mutated-by-workload";
  } catch {
    sidecarMutationBlocked = true;
  }
  return {
    entry: instance.exports["fixture.entry"],
    originalName,
    sidecarMutationBlocked,
  };
}

export async function firstCall({ entry, originalName,
  sidecarMutationBlocked }) {
  const result = entry(16);
  return { ok: result === 0 && sidecarMutationBlocked,
    observation: { result, originalName, sidecarMutationBlocked } };
}

export async function warmup({ entry }) {
  const result = entry(1000);
  return { ok: result === 0, observation: { result, rounds: 1000 } };
}

export async function steady({ entry }) {
  // A fixed work budget, not a timed loop/retry: the former 50M capture could
  // finish before V8 delivered the required 100 Wasm samples on CI runners.
  // Stay below signed i32's maximum and retain the same zero endpoint/batches.
  const result = entry(1_000_000_000);
  return { ok: result === 0,
    observation: { result, rounds: 1_000_000_000 } };
}
