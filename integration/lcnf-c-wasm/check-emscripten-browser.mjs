import { loadEmscriptenModule } from "./emscripten-loader.mjs";
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
  const manifestURL = new URL(
    "../../_build/lcnf-c-wasm/emscripten/RuntimeSmoke.manifest.json",
    import.meta.url,
  );
  const loaded = await loadEmscriptenModule(manifestURL, {
    moduleOptions: {
      printErr: (line) => stderr.push(String(line)),
    },
  });
  if (!stderr.includes("fir-lcnf-c:init-std")) {
    throw new Error(`Init IO probe did not reach stderr: ${stderr}`);
  }

  const rounds = 1000n;
  const seed = 0x123456789abcdef0n;
  const heap = asUInt64(
    loaded.exports.fir_lcnf_c_heap_checksum(rounds, seed),
  );
  const runtime = asUInt64(
    loaded.exports.fir_lcnf_c_runtime_checksum(rounds, seed),
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
    verifiedDigests: true,
    stderr,
  });
  root.dataset.result = "pass";
} catch (error) {
  output.textContent = String(error.stack ?? error);
  root.dataset.result = "fail";
}
