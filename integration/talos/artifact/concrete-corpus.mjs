export const CONCRETE_FIXTURES = Object.freeze([
  "arg-erased",
  "arg-tagged-first",
  "arg-uint16-max",
  "arg-uint32-max",
  "arg-uint64-max",
  "arg-uint8-max",
  "arg-usize-max",
  "box-heap",
  "box-roundtrip",
  "case",
  "cached-constructor",
  "cached-external",
  "closure-call",
  "closure-underapply",
  "compiler-shaped-mutation",
  "constructor-delete-fault",
  "constructor-graph-release",
  "constructor-reference-counting",
  "ctor-projection",
  "default-case",
  "delete-fault",
  "direct-call",
  "erased",
  "external-echo",
  "literal",
  "natural-heap",
  "nested-heap",
  "object-mutation",
  "projection-fault",
  "recursive-call",
  "reference-counting",
  "reset-reuse",
  "scalar-uint16-mutation",
  "scalar-uint32-mutation",
  "scalar-uint8-mutation",
  "shared-reset-reuse",
  "string-heap",
  "tag-mutation",
  "uint16-max",
  "uint32-max",
  "uint64-max",
  "uint8-max",
  "usize-max",
]);

export const REJECTED_FRAGMENT_FIXTURES = Object.freeze([]);

export const DEFAULT_EXTERNAL_FAULTS = Object.freeze([
  Object.freeze(["external-echo", Object.freeze({
    kind: "externalFailure",
    name: "external",
    message: "no concrete external implementation installed",
  })]),
]);

export const EXPECTED_CONCRETE_FAULTS = Object.freeze([
  Object.freeze(["mutation", Object.freeze({
    kind: "scalarFieldMissing",
    width: 1,
    offset: 0,
  })]),
]);

/** Compiler-produced source artifacts audited by the concrete-switch preflight. */
export const CONCRETE_SOURCE_PROBES = Object.freeze([
  "source-nat",
  "source-nat-list-case",
  "source-pretty-format",
  "source-pretty-format-coverage",
  "source-pretty-format-module",
  "source-string-input",
  "source-uint16-id",
  "source-uint32-id",
  "source-uint64",
  "source-uint64-id",
  "source-uint8-id",
  "source-usize-id",
  "source-usize-id-module",
]);
