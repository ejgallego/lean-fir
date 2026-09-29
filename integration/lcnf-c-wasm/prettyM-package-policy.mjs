import { BROWSER_PACKAGE_POLICY_VERSION } from "../package-tools/verified-package.mjs";

export const PRETTY_M_PACKAGE_FILES = Object.freeze([
  "BUILD.json",
  "README.md",
  "emscripten-loader.mjs",
  "prettyM-emscripten-adapter.mjs",
  "prettyM.manifest.json",
  "prettyM.mjs",
  "prettyM.wasm",
  "smoke.mjs",
]);

export const prettyMPackagePolicy = {
  version: BROWSER_PACKAGE_POLICY_VERSION,
  name: "fir-c-emscripten-prettyM",
  payloadFiles: PRETTY_M_PACKAGE_FILES,
  build: {
    schemaVersion: 1,
    requiredValues: [
      { path: ["format"], equals: "fir.prettyM.emscripten.package/v1" },
      { path: ["abi", "browserApi"], equals: "fir.prettyM.browser/v1" },
      { path: ["abi", "inputLayout"],
        equals: "lean-4.33-Std.Format.compact/v1" },
      { path: ["abi", "wire"], equals: "fir.prettyM.emscripten-wire/v1" },
      { path: ["ownership", "memoryOwner"], equals: "emscripten-loader" },
    ],
  },
  wasm: {
    file: "prettyM.wasm",
    memoryOwner: "emscripten-loader",
  },
  smokeFile: "smoke.mjs",
};
