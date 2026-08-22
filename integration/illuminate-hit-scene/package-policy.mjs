import {
  ILLUMINATE_HIT_SCENE_ADAPTER_API_VERSION,
  ILLUMINATE_HIT_SCENE_INPUT_LAYOUT_VERSION,
  ILLUMINATE_HIT_SCENE_OWNERSHIP_VERSION,
} from "./illuminate-hit-scene-browser-adapter.mjs";
import { BROWSER_PACKAGE_POLICY_VERSION } from
  "../package-tools/verified-package.mjs";

export const hitScenePayloadFiles = Object.freeze([
  "BUILD.json",
  "hit-scene-benchmark.json",
  "illuminate-hit-scene-browser-adapter.mjs",
  "illuminate-hit-scene.wasm",
  "illuminate-hit-scene.wasm.json",
  "smoke.mjs",
]);

export const hitScenePackagePolicy = Object.freeze({
  version: BROWSER_PACKAGE_POLICY_VERSION,
  name: "Illuminate HitScene v2",
  payloadFiles: hitScenePayloadFiles,
  smokeFile: "smoke.mjs",
  build: {
    schemaVersion: "fir.illuminate-hit-scene.build/v2",
    requiredValues: [
      { path: ["capabilities", "completeRuntime", "version"],
        equals: "fir.illuminate-hit-scene.complete-runtime/v1" },
      { path: ["capabilities", "completeRuntime", "selfContained"],
        equals: true },
      { path: ["capabilities", "inputLayout", "version"],
        equals: ILLUMINATE_HIT_SCENE_INPUT_LAYOUT_VERSION },
      { path: ["capabilities", "ownership", "version"],
        equals: ILLUMINATE_HIT_SCENE_OWNERSHIP_VERSION },
      { path: ["capabilities", "browserAdapter", "apiVersion"],
        equals: ILLUMINATE_HIT_SCENE_ADAPTER_API_VERSION },
    ],
  },
  wasm: {
    file: "illuminate-hit-scene.wasm",
    descriptorFile: "illuminate-hit-scene.wasm.json",
    requireCompleteRuntime: true,
    requireZeroImports: true,
    memoryOwner: "module",
  },
  sourcePackage: {
    producer: { project: "fir", backend: "fir-native-wasm" },
    adapter: {
      file: "illuminate-hit-scene-browser-adapter.mjs",
      apiVersionPath: ["capabilities", "browserAdapter", "apiVersion"],
      operationInventoryPath: ["capabilities", "browserAdapter", "operations"],
    },
    operations: [
      { name: "createHitScene", mode: "production",
        phases: ["instantiateMs", "parseProjectMs", "encodeMs", "totalMs",
          "overheadMs"] },
      { name: "hitTest", mode: "production", phases: [] },
      { name: "hitTestDiagnostic", mode: "diagnostic",
        phases: ["inputMs", "executeMs", "decodeMs", "rewindMs", "totalMs",
          "overheadMs"] },
      { name: "disposeHitScene", mode: "production", phases: [] },
    ],
    ownership: {
      capabilityPath: ["capabilities", "ownership"],
      model: "persistent-checkpoint-per-instance",
      arena: "persistent-prefix-with-rewound-scratch",
      reclamation: "drop-instance",
      rawAddressesExposed: false,
    },
  },
});
