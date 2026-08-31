import { BROWSER_PACKAGE_POLICY_VERSION } from
  "../package-tools/verified-package.mjs";
import {
  VBP_MANIFEST_RESOLVER_ADAPTER_API_VERSION,
  VBP_MANIFEST_RESOLVER_INPUT_LAYOUT_VERSION,
  VBP_MANIFEST_RESOLVER_OWNERSHIP_VERSION,
} from "./vbp-manifest-resolver-browser-adapter.mjs";

export const vbpManifestResolverPayloadFiles = Object.freeze([
  "BUILD.json",
  "runtime-manifest-resolver.json",
  "smoke.mjs",
  "vbp-manifest-resolver-browser-adapter.mjs",
  "vbp-manifest-resolver.wasm",
  "vbp-manifest-resolver.wasm.json",
]);

export const vbpManifestResolverPackagePolicy = Object.freeze({
  version: BROWSER_PACKAGE_POLICY_VERSION,
  name: "VBP portable manifest resolver",
  payloadFiles: vbpManifestResolverPayloadFiles,
  smokeFile: "smoke.mjs",
  build: {
    schemaVersion: "fir.vbp-manifest-resolver.build/v1",
    requiredValues: [
      { path: ["abi", "version"], equals: 1 },
      { path: ["abi", "logical"], equals: "String -> String" },
      { path: ["capabilities", "completeRuntime", "selfContained"],
        equals: true },
      { path: ["capabilities", "browserAdapter", "apiVersion"],
        equals: VBP_MANIFEST_RESOLVER_ADAPTER_API_VERSION },
      { path: ["capabilities", "inputLayout", "version"],
        equals: VBP_MANIFEST_RESOLVER_INPUT_LAYOUT_VERSION },
      { path: ["capabilities", "ownership", "version"],
        equals: VBP_MANIFEST_RESOLVER_OWNERSHIP_VERSION },
    ],
  },
  wasm: {
    file: "vbp-manifest-resolver.wasm",
    descriptorFile: "vbp-manifest-resolver.wasm.json",
    requireCompleteRuntime: true,
    requireZeroImports: true,
    memoryOwner: "module",
  },
  sourcePackage: {
    producer: {
      project: "fir",
      backend: "fir-native-wasm",
      lean: {
        toolchainPath: ["toolchain", "leanToolchain"],
        versionPath: ["toolchain", "leanVersion"],
      },
    },
    acceptance: { status: "provisional", authority: "vbp/performance" },
    evidenceFiles: ["vbp-manifest-resolver.wasm.json",
      "runtime-manifest-resolver.json"],
    adapter: {
      file: "vbp-manifest-resolver-browser-adapter.mjs",
      apiVersionPath: ["capabilities", "browserAdapter", "apiVersion"],
      operationInventoryPath: ["capabilities", "browserAdapter", "operations"],
      startupFields: ["fetchMs", "compileMs", "instantiateMs", "totalMs"],
      initializationFields: [],
    },
    operations: [{
      name: "invoke",
      mode: "production",
      inputContract: `${VBP_MANIFEST_RESOLVER_ADAPTER_API_VERSION}#invoke/input`,
      resultContract: `${VBP_MANIFEST_RESOLVER_ADAPTER_API_VERSION}#invoke/result`,
      phases: ["encodeMs", "executeMs", "decodeMs", "rewindMs", "totalMs",
        "overheadMs"],
    }],
    ownership: {
      capabilityPath: ["capabilities", "ownership"],
      model: "stateless-rewound-call",
      arena: "one-module-owned-scratch-arena",
      reclamation: "rewind-after-every-call-and-drop-instance-on-dispose",
      rawAddressesExposed: false,
      transfer: {
        publicInput: "borrowed-javascript-string",
        encodedInput: "fresh-transferred-lean-string",
        output: "decoded-javascript-string-copy",
      },
    },
  },
});
