export const metadata = {
  id: "fir-tooling-wasm-loop",
  purpose: "exercise steady-only Wasm CPU-profile attribution",
};

export async function setup({ wasmBytes }) {
  const { instance } = await WebAssembly.instantiate(wasmBytes);
  return instance.exports["fixture.entry"];
}

export async function firstCall(entry) {
  const result = entry(16);
  return { ok: result === 0, observation: { result } };
}

export async function warmup(entry) {
  const result = entry(1000);
  return { ok: result === 0, observation: { result, rounds: 1000 } };
}

export async function steady(entry) {
  const result = entry(50_000_000);
  return { ok: result === 0,
    observation: { result, rounds: 50_000_000 } };
}
