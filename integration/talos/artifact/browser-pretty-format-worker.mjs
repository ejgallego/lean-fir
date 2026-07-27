import { checkFetchedPrettyFormat } from "./fetch-pretty-format.mjs";
import { checkFetchedResidentGlobal } from "./resident-global-client.mjs";
import {
  checkFetchedResidentMemorySurface,
} from "./resident-memory-surface-client.mjs";
import {
  checkFetchedResidentAllocator,
} from "./resident-allocator-client.mjs";
import {
  checkFetchedResidentConstructors,
} from "./resident-constructor-client.mjs";
import {
  checkFetchedResidentClosureAllocation,
} from "./resident-closure-allocation-client.mjs";
import {
  checkFetchedResidentLiterals,
} from "./resident-literal-client.mjs";
import { checkFetchedConcretePrettyFormat } from "./fetch-concrete-pretty-format.mjs";
import {
  checkFetchedConcretePrettyFormatTrace,
} from "./fetch-concrete-pretty-format-trace.mjs";
import { checkFetchedResidentGetTag } from "./resident-get-tag-client.mjs";
import { checkFetchedResidentIsShared } from "./resident-is-shared-client.mjs";
import {
  checkFetchedResidentReadProjections,
} from "./resident-read-projections-client.mjs";
import {
  checkFetchedResidentClosureProjections,
} from "./resident-closure-projections-client.mjs";
import {
  checkFetchedResidentClosureMatches,
} from "./resident-closure-matches-client.mjs";

try {
  const results = await Promise.all([
    checkFetchedResidentGlobal("./_build/resident-global.wasm"),
    checkFetchedResidentMemorySurface("./_build/resident-memory-surface.wasm"),
    checkFetchedResidentAllocator("./_build/resident-allocator.wasm"),
    checkFetchedResidentConstructors("./_build/resident-constructors.wasm"),
    checkFetchedResidentClosureAllocation(
      "./_build/resident-closure-allocation.wasm",
    ),
    checkFetchedResidentLiterals("./_build/resident-literals.wasm"),
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
    checkFetchedConcretePrettyFormat(
      "./_build/source-pretty-format-resident-closure-matches.wasm",
    ),
    checkFetchedConcretePrettyFormat(
      "./_build/source-pretty-format-resident-allocator.wasm",
    ),
    checkFetchedConcretePrettyFormat(
      "./_build/source-pretty-format-resident-constructors.wasm",
    ),
    checkFetchedConcretePrettyFormat(
      "./_build/source-pretty-format-resident-partial-applications.wasm",
    ),
    checkFetchedConcretePrettyFormatTrace(
      "./_build/source-pretty-format-trace-resident-partial-applications.wasm",
    ),
    checkFetchedResidentGetTag("./_build/resident-get-tag.wasm"),
    checkFetchedResidentIsShared("./_build/resident-is-shared.wasm"),
    checkFetchedResidentReadProjections(
      "./_build/resident-read-projections.wasm",
    ),
    checkFetchedResidentClosureProjections(
      "./_build/resident-closure-projections.wasm",
    ),
    checkFetchedResidentClosureMatches(
      "./_build/resident-closure-matches.wasm",
    ),
  ]);
  globalThis.postMessage({ ok: true, result: results.join("\n") });
} catch (error) {
  globalThis.postMessage({ ok: false, error: String(error.stack ?? error) });
}
