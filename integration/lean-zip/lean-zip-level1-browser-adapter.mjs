import {
  createLeanZipByteArrayAdapter,
  fetchLeanZipByteArrayAdapter,
} from "./lean-zip-byte-array-browser-adapter.mjs";

const ENTRY = "Zip.Wasm.compressLevel1";

export const LEAN_ZIP_LEVEL1_PERSISTENT_INITIALIZER =
  null;

export const LEAN_ZIP_LEVEL1_ADAPTER_API_VERSION =
  "fir.lean-zip.level1.browser/v3";
export const LEAN_ZIP_LEVEL1_OWNERSHIP_VERSION =
  "fir.lean-zip.level1.lazy-cache-floor/v3";

export function createLeanZipLevel1Adapter(options = {}) {
  return createLeanZipByteArrayAdapter({
    ...options,
    entry: ENTRY,
    label: "lean-zip Level-1",
    persistentInitializer: LEAN_ZIP_LEVEL1_PERSISTENT_INITIALIZER,
    allowPersistentCheckpointGrowth: true,
  });
}

export function fetchLeanZipLevel1Adapter(options) {
  return fetchLeanZipByteArrayAdapter({
    ...options,
    entry: ENTRY,
    label: "lean-zip Level-1",
    persistentInitializer: LEAN_ZIP_LEVEL1_PERSISTENT_INITIALIZER,
    allowPersistentCheckpointGrowth: true,
  });
}
