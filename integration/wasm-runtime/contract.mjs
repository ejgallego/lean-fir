/**
 * Current, generic capability for Lean's genuine platform-libm boundary.
 * It contains no Lean heap objects and imposes no bounded-Nat or
 * decimal-construction domain.
 */
export const STANDARD_LIBM_RUNTIME_VERSION = "fir.standard-libm/v2";
export const STANDARD_LIBM_RUNTIME_RESERVED_MEMORY_BYTES = 65536;
export const STANDARD_LIBM_RUNTIME_DECLARATIONS = Object.freeze([
  "Float.sin",
  "Float.cos",
  "Float.acos",
  "Float.atan2",
  "Float.cbrt",
  "Float.log2",
]);

export function standardLibmRuntimeCapability(declarations) {
  const requested = [...declarations];
  for (const declaration of requested) {
    if (!STANDARD_LIBM_RUNTIME_DECLARATIONS.includes(declaration)) {
      throw new Error(`unsupported standard-libm declaration ${declaration}`);
    }
  }
  return Object.freeze({
    version: STANDARD_LIBM_RUNTIME_VERSION,
    declarations: Object.freeze(requested),
    reservedMemoryBytes: STANDARD_LIBM_RUNTIME_RESERVED_MEMORY_BYTES,
    numericContract: "platform-libm-special-values-and-bounded-error",
  });
}
