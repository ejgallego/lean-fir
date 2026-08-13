import {
  createLeanZipByteArrayAdapter,
  fetchLeanZipByteArrayAdapter,
} from "./lean-zip-byte-array-browser-adapter.mjs";
import { STANDARD_MATH_RUNTIME_RESERVED_MEMORY_BYTES } from
  "./standard-math-runtime-contract.mjs";

const ENTRY = "Zip.Wasm.compressRaw";
const PARAMETER_KINDS = Object.freeze(["object", "uint8"]);

export const LEAN_ZIP_RAW_PERSISTENT_INITIALIZER =
  "fir_initialize_persistent_caches";
export const LEAN_ZIP_RAW_ADAPTER_API_VERSION =
  "fir.lean-zip.raw.browser/v1";
export const LEAN_ZIP_RAW_OWNERSHIP_VERSION =
  "fir.lean-zip.raw.scratch-transfer/v1";

export function createLeanZipRawAdapter(options = {}) {
  return createLeanZipByteArrayAdapter({
    ...options,
    entry: ENTRY,
    label: "lean-zip raw dispatcher",
    parameterKinds: PARAMETER_KINDS,
    persistentInitializer: LEAN_ZIP_RAW_PERSISTENT_INITIALIZER,
    reservedMemoryBytes: STANDARD_MATH_RUNTIME_RESERVED_MEMORY_BYTES,
  });
}

export function fetchLeanZipRawAdapter(options) {
  return fetchLeanZipByteArrayAdapter({
    ...options,
    entry: ENTRY,
    label: "lean-zip raw dispatcher",
    parameterKinds: PARAMETER_KINDS,
    persistentInitializer: LEAN_ZIP_RAW_PERSISTENT_INITIALIZER,
    reservedMemoryBytes: STANDARD_MATH_RUNTIME_RESERVED_MEMORY_BYTES,
  });
}
