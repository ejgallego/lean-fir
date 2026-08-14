import assert from "node:assert/strict";
import test from "node:test";

import { buildPostponedSourceView } from "./postponed-source-view.mjs";

const valid = {
  lean: "/does/not/run",
  leanPath: "/lean/path",
  moduleName: "Client.Source",
  outputRoot: "/tmp/fir-postponed-source-view-test",
  packageName: "ClientSourceView",
  sourceFile: "/client/Source.lean",
};

test("rejects an empty required argument before invoking Lean", () => {
  assert.throws(() => buildPostponedSourceView({ ...valid, sourceFile: "" }),
    /sourceFile must be a non-empty string/);
});

test("rejects a non-canonical Lean module name before invoking Lean", () => {
  assert.throws(() => buildPostponedSourceView({
    ...valid,
    moduleName: "Client/Source",
  }), /moduleName is not a canonical Lean module name/);
});
