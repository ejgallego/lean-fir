import { checkFetchedPrettyFormat } from "./fetch-pretty-format.mjs";
import { checkFetchedResidentGetTag } from "./resident-get-tag-client.mjs";

try {
  const results = await Promise.all([
    checkFetchedPrettyFormat("./_build/source-pretty-format-module.wasm"),
    checkFetchedResidentGetTag("./_build/resident-get-tag.wasm"),
  ]);
  globalThis.postMessage({ ok: true, result: results.join("\n") });
} catch (error) {
  globalThis.postMessage({ ok: false, error: String(error.stack ?? error) });
}
