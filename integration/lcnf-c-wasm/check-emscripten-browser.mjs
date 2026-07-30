import createModule from "../../_build/lcnf-c-wasm/emscripten/RuntimeSmoke.mjs";

import {
  asUInt64,
  expectedHeapChecksum,
  expectedRuntimeChecksum,
} from "./reference.mjs";

const root = document.documentElement;
const output = document.querySelector("#result");

try {
  if (!globalThis.crossOriginIsolated) {
    throw new Error("Emscripten pthread artifact is not cross-origin isolated");
  }

  const stderr = [];
  const module = await createModule({
    printErr: (line) => stderr.push(String(line)),
  });
  const initializationCode = module._fir_lcnf_c_initialize();
  if (initializationCode !== 0) {
    throw new Error(`runtime initialization failed with ${initializationCode}`);
  }
  if (!stderr.includes("fir-lcnf-c:init-std")) {
    throw new Error(`Init IO probe did not reach stderr: ${stderr}`);
  }

  const rounds = 1000n;
  const seed = 0x123456789abcdef0n;
  const heap = asUInt64(module._fir_lcnf_c_heap_checksum(rounds, seed));
  const runtime = asUInt64(
    module._fir_lcnf_c_runtime_checksum(rounds, seed),
  );
  if (heap !== expectedHeapChecksum(rounds, seed)) {
    throw new Error(`heap checksum mismatch: ${heap}`);
  }
  if (runtime !== expectedRuntimeChecksum(rounds, seed)) {
    throw new Error(`runtime checksum mismatch: ${runtime}`);
  }

  output.textContent = JSON.stringify({
    profile: "emscripten-browser",
    heap: heap.toString(),
    runtime: runtime.toString(),
    stderr,
  });
  root.dataset.result = "pass";
} catch (error) {
  output.textContent = String(error.stack ?? error);
  root.dataset.result = "fail";
}
