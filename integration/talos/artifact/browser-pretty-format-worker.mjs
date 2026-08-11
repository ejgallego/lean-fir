import { checkFetchedPrettyFormat } from "./fetch-pretty-format.mjs";
import { checkFetchedResidentGlobal } from "./resident-global-client.mjs";
import {
  checkFetchedResidentMemorySurface,
} from "./resident-memory-surface-client.mjs";
import {
  checkFetchedResidentAllocator,
} from "./resident-allocator-client.mjs";
import {
  checkFetchedResidentByteArray,
} from "./resident-byte-array-client.mjs";
import {
  checkFetchedResidentFixedWidth,
} from "./resident-fixed-width-client.mjs";
import {
  checkFetchedResidentConstructors,
} from "./resident-constructor-client.mjs";
import {
  checkFetchedResidentClosureAllocation,
} from "./resident-closure-allocation-client.mjs";
import {
  checkFetchedResidentScalarBox,
} from "./resident-scalar-box-client.mjs";
import {
  checkFetchedResidentLiterals,
} from "./resident-literal-client.mjs";
import {
  checkFetchedResidentSetters,
} from "./resident-setter-client.mjs";
import {
  checkFetchedResidentTagSetter,
} from "./resident-tag-setter-client.mjs";
import {
  checkFetchedResidentIncrements,
} from "./resident-increment-client.mjs";
import {
  checkFetchedResidentReleases,
} from "./resident-release-client.mjs";
import {
  checkFetchedResidentCache,
} from "./resident-cache-client.mjs";
import {
  checkFetchedResidentNumeric,
} from "./resident-numeric-client.mjs";
import {
  checkFetchedResidentBigNumeric,
} from "./resident-big-numeric-client.mjs";
import {
  checkFetchedResidentString,
} from "./resident-string-client.mjs";
import {
  checkFetchedResidentFallbacks,
} from "./resident-fallback-client.mjs";
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
import {
  checkFetchedPrettyMBrowserAdapter,
} from "./check-prettyM-browser-adapter.mjs";

try {
  const results = await Promise.all([
    checkFetchedResidentGlobal("./_build/resident-global.wasm"),
    checkFetchedResidentMemorySurface("./_build/resident-memory-surface.wasm"),
    checkFetchedResidentAllocator("./_build/resident-allocator.wasm"),
    checkFetchedResidentByteArray("./_build/resident-byte-arrays.wasm"),
    checkFetchedResidentFixedWidth("./_build/resident-fixed-width.wasm"),
    checkFetchedResidentConstructors("./_build/resident-constructors.wasm"),
    checkFetchedResidentClosureAllocation(
      "./_build/resident-closure-allocation.wasm",
    ),
    checkFetchedResidentScalarBox("./_build/resident-scalar-box.wasm"),
    checkFetchedResidentLiterals("./_build/resident-literals.wasm"),
    checkFetchedResidentSetters("./_build/resident-setters.wasm"),
    checkFetchedResidentTagSetter("./_build/resident-tag-setter.wasm"),
    checkFetchedResidentIncrements("./_build/resident-increments.wasm"),
    checkFetchedResidentReleases("./_build/resident-releases.wasm"),
    checkFetchedResidentCache("./_build/resident-cache.wasm"),
    checkFetchedResidentNumeric("./_build/resident-numeric.wasm"),
    checkFetchedResidentBigNumeric("./_build/resident-big-numeric.wasm"),
    checkFetchedResidentString("./_build/resident-string.wasm"),
    checkFetchedResidentFallbacks("./_build/resident-fallbacks.wasm"),
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
      "./_build/source-pretty-format-resident-increments.wasm",
    ),
    checkFetchedConcretePrettyFormat(
      "./_build/source-pretty-format-resident-releases.wasm",
    ),
    checkFetchedConcretePrettyFormat(
      "./_build/source-pretty-format-resident-cache.wasm",
    ),
    checkFetchedConcretePrettyFormat(
      "./_build/source-pretty-format-resident-numeric.wasm",
    ),
    checkFetchedResidentNumeric(
      "./_build/source-pretty-format-resident-numeric.wasm",
    ),
    checkFetchedConcretePrettyFormat(
      "./_build/source-pretty-format-resident-big-numeric.wasm",
    ),
    checkFetchedResidentBigNumeric(
      "./_build/source-pretty-format-resident-big-numeric.wasm",
    ),
    checkFetchedConcretePrettyFormat(
      "./_build/source-pretty-format-resident-string.wasm",
    ),
    checkFetchedResidentBigNumeric(
      "./_build/source-pretty-format-resident-string.wasm",
    ),
    checkFetchedResidentString(
      "./_build/source-pretty-format-resident-string.wasm",
    ),
    checkFetchedConcretePrettyFormat(
      "./_build/source-pretty-format-resident-closed.wasm",
    ),
    checkFetchedResidentString(
      "./_build/source-pretty-format-resident-closed.wasm",
    ),
    checkFetchedResidentBigNumeric(
      "./_build/source-pretty-format-resident-closed.wasm",
    ),
    checkFetchedResidentFallbacks(
      "./_build/source-pretty-format-resident-closed.wasm",
    ),
    checkFetchedConcretePrettyFormatTrace(
      "./_build/source-pretty-format-trace-resident-increments.wasm",
    ),
    checkFetchedConcretePrettyFormatTrace(
      "./_build/source-pretty-format-trace-resident-releases.wasm",
    ),
    checkFetchedConcretePrettyFormatTrace(
      "./_build/source-pretty-format-trace-resident-tag-setters.wasm",
    ),
    checkFetchedConcretePrettyFormatTrace(
      "./_build/source-pretty-format-trace-resident-cache.wasm",
    ),
    checkFetchedConcretePrettyFormatTrace(
      "./_build/source-pretty-format-trace-resident-numeric.wasm",
    ),
    checkFetchedResidentNumeric(
      "./_build/source-pretty-format-trace-resident-numeric.wasm",
    ),
    checkFetchedConcretePrettyFormatTrace(
      "./_build/source-pretty-format-trace-resident-big-numeric.wasm",
    ),
    checkFetchedResidentBigNumeric(
      "./_build/source-pretty-format-trace-resident-big-numeric.wasm",
    ),
    checkFetchedConcretePrettyFormatTrace(
      "./_build/source-pretty-format-trace-resident-string.wasm",
    ),
    checkFetchedResidentBigNumeric(
      "./_build/source-pretty-format-trace-resident-string.wasm",
    ),
    checkFetchedResidentString(
      "./_build/source-pretty-format-trace-resident-string.wasm",
    ),
    checkFetchedConcretePrettyFormatTrace(
      "./_build/source-pretty-format-trace-resident-closed.wasm",
    ),
    checkFetchedResidentString(
      "./_build/source-pretty-format-trace-resident-closed.wasm",
    ),
    checkFetchedResidentBigNumeric(
      "./_build/source-pretty-format-trace-resident-closed.wasm",
    ),
    checkFetchedResidentFallbacks(
      "./_build/source-pretty-format-trace-resident-closed.wasm",
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
    checkFetchedPrettyMBrowserAdapter(
      "./_build/prettyM-current/prettyM.wasm",
    ),
  ]);
  globalThis.postMessage({ ok: true, result: results.join("\n") });
} catch (error) {
  globalThis.postMessage({ ok: false, error: String(error.stack ?? error) });
}
