import { readFile } from "node:fs/promises";
import { pathToFileURL } from "node:url";

import {
  checkConcreteSourceInventory,
} from "./check-concrete-source-probes.mjs";

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  const artifactDirectory = process.argv[2];
  if (!artifactDirectory) {
    console.error("usage: node run-concrete-source-artifacts.mjs SOURCE_ARTIFACT_DIR");
    process.exit(2);
  }
  const inventory = await checkConcreteSourceInventory(async (id) => {
    const wasmPath = `${artifactDirectory}/${id}.wasm`;
    return {
      bytes: await readFile(wasmPath),
      manifest: JSON.parse(await readFile(`${wasmPath}.json`, "utf8")),
    };
  });
  console.log(inventory.message);
}
