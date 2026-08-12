import {
  createLeanZipByteArrayAdapter,
  fetchLeanZipByteArrayAdapter,
} from "./lean-zip-byte-array-browser-adapter.mjs";

const ENTRY = "Zip.Wasm.compressStored";

export { LEAN_ZIP_BYTE_ARRAY_LAYOUT_VERSION } from
  "./lean-zip-byte-array-browser-adapter.mjs";
export const LEAN_ZIP_STORED_ADAPTER_API_VERSION =
  "fir.lean-zip.stored.browser/v1";
export const LEAN_ZIP_STORED_OWNERSHIP_VERSION =
  "fir.lean-zip.stored.scratch-transfer/v2";

export function createLeanZipStoredAdapter(options = {}) {
  return createLeanZipByteArrayAdapter({
    ...options,
    entry: ENTRY,
    label: "lean-zip stored",
  });
}

export function fetchLeanZipStoredAdapter(options) {
  return fetchLeanZipByteArrayAdapter({
    ...options,
    entry: ENTRY,
    label: "lean-zip stored",
  });
}
