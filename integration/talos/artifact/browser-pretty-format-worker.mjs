import { checkFetchedPrettyFormat } from "./fetch-pretty-format.mjs";
import { checkFetchedConcretePrettyFormat } from "./fetch-concrete-pretty-format.mjs";
import { checkFetchedResidentGetTag } from "./resident-get-tag-client.mjs";

try {
  const results = await Promise.all([
    checkFetchedPrettyFormat("./_build/source-pretty-format-module.wasm"),
    checkFetchedConcretePrettyFormat(
      "./_build/source-pretty-format-resident-get-tag.wasm",
    ),
    checkFetchedResidentGetTag("./_build/resident-get-tag.wasm"),
  ]);
  globalThis.postMessage({ ok: true, result: results.join("\n") });
} catch (error) {
  globalThis.postMessage({ ok: false, error: String(error.stack ?? error) });
}
