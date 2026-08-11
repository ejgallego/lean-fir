/** Public ownership and value-domain contract for the shared math runtime. */

export const STANDARD_MATH_RUNTIME_VERSION = "fir.standard-math/v1";
export const STANDARD_MATH_RUNTIME_RESERVED_MEMORY_BYTES = 65536;
export const STANDARD_MATH_RUNTIME_NATURAL_DOMAIN =
  "canonical immediate or one-limb u64";
export const STANDARD_MATH_RUNTIME_SCIENTIFIC_EXPONENT_MAXIMUM = 20;

export function standardMathRuntimeCapability(declarations) {
  return Object.freeze({
    version: STANDARD_MATH_RUNTIME_VERSION,
    declarations: Object.freeze([...declarations]),
    reservedMemoryBytes: STANDARD_MATH_RUNTIME_RESERVED_MEMORY_BYTES,
    naturalDomain: STANDARD_MATH_RUNTIME_NATURAL_DOMAIN,
    scientificExponentMaximum:
      STANDARD_MATH_RUNTIME_SCIENTIFIC_EXPONENT_MAXIMUM,
  });
}
