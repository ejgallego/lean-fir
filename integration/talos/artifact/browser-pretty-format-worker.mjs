import { checkFetchedPrettyFormat } from "./fetch-pretty-format.mjs";
import { checkFetchedConcretePrettyFormat } from "./fetch-concrete-pretty-format.mjs";
import { checkFetchedResidentGetTag } from "./resident-get-tag-client.mjs";
import { checkFetchedResidentIsShared } from "./resident-is-shared-client.mjs";
import {
  checkFetchedResidentReadProjections,
} from "./resident-read-projections-client.mjs";
import {
  checkFetchedResidentClosureProjections,
} from "./resident-closure-projections-client.mjs";

try {
  const results = await Promise.all([
    checkFetchedPrettyFormat("./_build/source-pretty-format-module.wasm"),
    checkFetchedConcretePrettyFormat(
      "./_build/source-pretty-format-resident-get-tag.wasm",
    ),
    checkFetchedConcretePrettyFormat(
      "./_build/source-pretty-format-resident-runtime.wasm",
    ),
    checkFetchedConcretePrettyFormat(
      "./_build/source-pretty-format-resident-projections.wasm",
    ),
    checkFetchedConcretePrettyFormat(
      "./_build/source-pretty-format-resident-closure-projections.wasm",
    ),
    checkFetchedResidentGetTag("./_build/resident-get-tag.wasm"),
    checkFetchedResidentIsShared("./_build/resident-is-shared.wasm"),
    checkFetchedResidentReadProjections(
      "./_build/resident-read-projections.wasm",
    ),
    checkFetchedResidentClosureProjections(
      "./_build/resident-closure-projections.wasm",
    ),
  ]);
  globalThis.postMessage({ ok: true, result: results.join("\n") });
} catch (error) {
  globalThis.postMessage({ ok: false, error: String(error.stack ?? error) });
}
