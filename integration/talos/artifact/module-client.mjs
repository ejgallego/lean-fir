const INVOCATION_FIELDS = ["fixture", "arguments", "initialRuntime"];

function requireCondition(condition, message) {
  if (!condition) {
    throw new Error(message);
  }
}

export function validateModuleDescriptor(manifest) {
  requireCondition(manifest && typeof manifest === "object" && !Array.isArray(manifest),
    "module descriptor must be a JSON object");
  requireCondition(typeof manifest.sourceEntry === "string",
    "module descriptor sourceEntry must be a string");
  requireCondition(typeof manifest.entry === "string",
    "module descriptor entry must be a string");
  requireCondition(typeof manifest.result === "string",
    "module descriptor result must be a string");
  requireCondition(Array.isArray(manifest.params),
    "module descriptor params must be an array");
  requireCondition(manifest.params.every((kind) => typeof kind === "string"),
    "module descriptor params must contain ABI kind names");
  requireCondition(Array.isArray(manifest.closureDispatch),
    "module descriptor closureDispatch must be an array");
  requireCondition(manifest.closureDispatch.every((target) =>
    typeof target === "string" && target.length > 0),
  "module descriptor closureDispatch must contain target names");
  requireCondition(new Set(manifest.closureDispatch).size ===
    manifest.closureDispatch.length,
  "module descriptor closureDispatch must not contain duplicates");
  requireCondition(Array.isArray(manifest.imports),
    "module descriptor imports must be an array");
  for (const field of INVOCATION_FIELDS) {
    requireCondition(!Object.hasOwn(manifest, field),
      `module-only descriptor must not contain ${field}`);
  }
  return manifest;
}

/**
 * Instantiate an invocation-free FIR Wasm artifact from transport-neutral
 * inputs. The caller owns both the bytes and the semantic ABI host.
 *
 * This intentionally exposes the raw exported WebAssembly function. Callers
 * allocate Lean runtime values in `host`, encode them with the descriptor's
 * ABI kinds, and decode the physical result themselves.
 */
export async function instantiateModuleArtifact({ bytes, manifest, host }) {
  requireCondition(bytes instanceof ArrayBuffer || ArrayBuffer.isView(bytes),
    "module bytes must be an ArrayBuffer or an ArrayBuffer view");
  validateModuleDescriptor(manifest);
  requireCondition(host && typeof host.imports === "function",
    "module artifact host must provide imports(operations)");
  requireCondition(WebAssembly.validate(bytes), "module failed WebAssembly validation");

  const { instance } = await WebAssembly.instantiate(bytes, host.imports(manifest.imports));
  const memory = instance.exports.memory;
  if (memory instanceof WebAssembly.Memory) {
    requireCondition(typeof host.attachMemory === "function",
      "module exports memory but its host does not provide attachMemory(memory)");
    host.attachMemory(memory);
    const frontier = instance.exports.fir_heap_frontier;
    const setFrontier = instance.exports.fir_heap_set_frontier;
    if (frontier !== undefined || setFrontier !== undefined) {
      requireCondition(typeof frontier === "function",
        "fir_heap_frontier export must be callable");
      requireCondition(typeof setFrontier === "function",
        "fir_heap_set_frontier export must be callable");
      requireCondition(Number.isInteger(host.heapCursor) &&
        host.heapCursor >= 0 && host.heapCursor <= 0xffffffff,
      "resident allocator host must expose a wasm32 heapCursor");
      setFrontier(host.heapCursor);
      requireCondition(typeof host.attachResidentFrontier === "function",
        "resident allocator host must provide attachResidentFrontier(frontier, setFrontier)");
      host.attachResidentFrontier(frontier, setFrontier);
    }
  }
  const entry = instance.exports[manifest.entry];
  requireCondition(typeof entry === "function",
    `module export ${manifest.entry} must be a function`);
  return { manifest, host, instance, entry };
}

/** Load the same low-level boundary through the web-standard Fetch API. */
export async function fetchModuleArtifact(artifactUrl, options) {
  const {
    descriptorUrl = `${artifactUrl}.json`,
    host,
    fetchImpl = globalThis.fetch,
  } = options ?? {};
  requireCondition(typeof fetchImpl === "function",
    "fetchModuleArtifact requires a Fetch API implementation");

  const [moduleResponse, descriptorResponse] = await Promise.all([
    fetchImpl(artifactUrl),
    fetchImpl(descriptorUrl),
  ]);
  requireCondition(moduleResponse.ok,
    `failed to fetch module ${artifactUrl}: HTTP ${moduleResponse.status}`);
  requireCondition(descriptorResponse.ok,
    `failed to fetch module descriptor ${descriptorUrl}: HTTP ${descriptorResponse.status}`);

  return instantiateModuleArtifact({
    bytes: await moduleResponse.arrayBuffer(),
    manifest: await descriptorResponse.json(),
    host,
  });
}
