import {
  ILLUMINATE_SELECTION_PLAYER_ADAPTER_API_VERSION,
  ILLUMINATE_SELECTION_PLAYER_HOT_EVENT_VERSION,
  ILLUMINATE_SELECTION_PLAYER_INPUT_LAYOUT_VERSION,
  ILLUMINATE_SELECTION_PLAYER_OWNERSHIP_VERSION,
  ILLUMINATE_SELECTION_PLAYER_RUNTIME_VERSION,
} from "./illuminate-selection-player-browser-adapter.mjs";
import { BROWSER_PACKAGE_POLICY_VERSION } from
  "../package-tools/verified-package.mjs";

export const selectionPayloadFiles = Object.freeze([
  "BUILD.json",
  "illuminate-selection-player-browser-adapter.mjs",
  "illuminate-selection-player.wasm",
  "illuminate-selection-player.wasm.json",
  "smoke.mjs",
]);

export const selectionExpectedExports = Object.freeze([
  { name: "Illuminate.AnimationPlayer.initialSelectionLive", kind: "function" },
  { name: "Illuminate.AnimationPlayer.transitionSelectionLive", kind: "function" },
  { name: "IlluminateFirNative.transitionSelectionTickLive._fir_bit_exact",
    kind: "function" },
  { name: "fir_heap_frontier", kind: "function" },
  { name: "fir_heap_set_frontier", kind: "function" },
  { name: "fir_heap_rewind", kind: "function" },
  { name: "fir_heap_alloc", kind: "function" },
  { name: "memory", kind: "memory" },
]);

export const selectionPackagePolicy = Object.freeze({
  version: BROWSER_PACKAGE_POLICY_VERSION,
  name: "Illuminate selection player v3",
  payloadFiles: selectionPayloadFiles,
  smokeFile: "smoke.mjs",
  build: {
    schemaVersion: "fir.illuminate-selection-player.build/v3",
    requiredValues: [
      { path: ["capabilities", "completeRuntime", "version"],
        equals: "fir.illuminate-player.complete-runtime/v2" },
      { path: ["capabilities", "completeRuntime", "selfContained"],
        equals: true },
      { path: ["capabilities", "completeRuntime", "residentRuntime", "version"],
        equals: ILLUMINATE_SELECTION_PLAYER_RUNTIME_VERSION },
      { path: ["capabilities", "completeRuntime", "residentRuntime", "provider"],
        equals: "none" },
      { path: ["capabilities", "completeRuntime", "residentRuntime",
        "externalDeclarations"], equals: [] },
      { path: ["capabilities", "browserAdapter", "apiVersion"],
        equals: ILLUMINATE_SELECTION_PLAYER_ADAPTER_API_VERSION },
      { path: ["capabilities", "hotEvent", "version"],
        equals: ILLUMINATE_SELECTION_PLAYER_HOT_EVENT_VERSION },
      { path: ["capabilities", "inputLayout", "version"],
        equals: ILLUMINATE_SELECTION_PLAYER_INPUT_LAYOUT_VERSION },
      { path: ["capabilities", "ownership", "version"],
        equals: ILLUMINATE_SELECTION_PLAYER_OWNERSHIP_VERSION },
    ],
  },
  wasm: {
    file: "illuminate-selection-player.wasm",
    descriptorFile: "illuminate-selection-player.wasm.json",
    requireCompleteRuntime: true,
    requireZeroImports: true,
    memoryOwner: "module",
    expectedExports: selectionExpectedExports,
  },
});
