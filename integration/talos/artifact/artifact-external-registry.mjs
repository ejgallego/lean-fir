/**
 * Browser-safe foreign implementations shared by the semantic and concrete
 * artifact hosts. Both hosts expose the same decoded-value interface; their
 * internal heap representations remain independent.
 */
export const artifactExternalRegistry = Object.freeze({
  external: ({ args, world }) => ({ value: args[0], world: world + 1 }),
  cachedBinaryExternal: ({ world }) => ({
    value: { kind: "scalar", scalarKind: "uint64", value: 91n },
    world: world + 1,
  }),
});
