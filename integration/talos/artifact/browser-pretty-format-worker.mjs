import { checkFetchedPrettyFormat } from "./fetch-pretty-format.mjs";

try {
  const result = await checkFetchedPrettyFormat(
    "./_build/source-pretty-format-module.wasm",
  );
  globalThis.postMessage({ ok: true, result });
} catch (error) {
  globalThis.postMessage({ ok: false, error: String(error.stack ?? error) });
}
