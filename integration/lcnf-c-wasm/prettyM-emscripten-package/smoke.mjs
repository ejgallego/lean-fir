import assert from "node:assert/strict";

import {
  loadEmscriptenPrettyMAdapter,
  PrettyFormat as F,
} from "./prettyM-emscripten-adapter.mjs";

const adapter = await loadEmscriptenPrettyMAdapter(
  new URL("./prettyM.manifest.json", import.meta.url));
try {
  const result = adapter.render({
    format: F.group(F.append(F.text("hello"),
      F.append(F.line(), F.text("λ")))),
    width: 80,
  });
  assert.equal(result.trace.text, "hello λ");
  assert.ok(Array.isArray(result.trace.events));
  assert.ok(result.memory.requestBytes > 0);
  assert.ok(result.memory.responseBytes > 0);
  assert.ok(result.timings.totalMs >= 0);
} finally {
  adapter.dispose();
}
console.log("PASS packaged C/Emscripten prettyM smoke");
