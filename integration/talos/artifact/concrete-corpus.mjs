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
  "closure-call",
  "closure-underapply",
  "compiler-shaped-mutation",
  "constructor-delete-fault",
  "constructor-graph-release",
  "constructor-reference-counting",
  "ctor-projection",
  "default-case",
  "direct-call",
  "erased",
  "literal",
  "natural-heap",
  "object-mutation",
  "projection-fault",
  "recursive-call",
  "reset-reuse",
  "shared-reset-reuse",
  "tag-mutation",
  "uint16-max",
  "uint32-max",
  "uint64-max",
  "uint8-max",
  "usize-max",
]);

export const REJECTED_FRAGMENT_FIXTURES = Object.freeze([
  "external-echo",
  "string-heap",
]);

export const EXPECTED_CONCRETE_FAULTS = Object.freeze([
  Object.freeze(["mutation", Object.freeze({
    kind: "scalarFieldMissing",
    width: 1,
    offset: 0,
  })]),
]);
