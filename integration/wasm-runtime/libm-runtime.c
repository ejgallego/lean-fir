#include <math.h>

#define EXPORT(name) __attribute__((export_name(name)))

/*
 * Lean implements these opaque Float declarations through the platform C
 * math library.  Keep this provider at the same boundary: core-Wasm Float
 * operations and exposed Lean conversions belong in FIR's resident linker.
 */
EXPORT("Float.sin") double fir_float_sin(double value) { return sin(value); }
EXPORT("Float.cos") double fir_float_cos(double value) { return cos(value); }
EXPORT("Float.acos") double fir_float_acos(double value) { return acos(value); }
EXPORT("Float.atan2") double fir_float_atan2(double y, double x) {
  return atan2(y, x);
}
EXPORT("Float.cbrt") double fir_float_cbrt(double value) { return cbrt(value); }
EXPORT("Float.log2") double fir_float_log2(double value) { return log2(value); }
