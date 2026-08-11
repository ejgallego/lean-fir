#include <math.h>
#include <stdint.h>

#define EXPORT(name) __attribute__((export_name(name)))

/*
 * FIR's current external-math boundary accepts canonical Naturals with at
 * most one 64-bit limb. The compiled runtime reads the shared module-owned
 * Lean representation directly; application JavaScript is never involved.
 */
static uint64_t fir_natural_u64(uint32_t word) {
  if ((word & 1u) != 0u) return (uint64_t)(word >> 1);
  if (word < 1024u || (word & 7u) != 0u) __builtin_trap();
  const uint32_t *header = (const uint32_t *)(uintptr_t)word;
  if (header[0] != 5u || (header[1] & 2u) == 0u || header[3] < 40u ||
      header[5] != 1u || header[7] != 0u) {
    __builtin_trap();
  }
  const uint64_t *payload = (const uint64_t *)(uintptr_t)(word + 32u);
  return payload[0];
}

static unsigned fir_log2_u128(unsigned __int128 value) {
  if (value == 0) return 0;
  uint64_t high = (uint64_t)(value >> 64);
  if (high != 0) return 127u - (unsigned)__builtin_clzll(high);
  return 63u - (unsigned)__builtin_clzll((uint64_t)value);
}

static unsigned __int128 fir_pow5(unsigned exponent) {
  unsigned __int128 result = 1;
  for (unsigned index = 0; index < exponent; ++index) result *= 5;
  return result;
}

static double fir_binary_scientific(unsigned __int128 mantissa, int exponent) {
  if (mantissa == 0) return 0.0;
  unsigned log = fir_log2_u128(mantissa);
  unsigned shift = log > 63u ? log - 63u : 0u;
  uint64_t narrowed = (uint64_t)(mantissa >> shift);
  return scalbn((double)narrowed, exponent + (int)shift);
}

EXPORT("Float.ofNat")
double fir_float_of_nat(uint32_t value) {
  return (double)fir_natural_u64(value);
}

/*
 * This is the Lean 4.32 Init.Data.OfScientific algorithm on the checked
 * one-limb Natural domain.  Exponents through 20 guarantee that every
 * intermediate fits in u128 for either exponent sign and every u64 mantissa.
 */
EXPORT("Float.ofScientific")
double fir_float_of_scientific(uint32_t mantissa_word, uint8_t negative_exp,
                               uint32_t exponent_word) {
  uint64_t mantissa = fir_natural_u64(mantissa_word);
  uint64_t exponent64 = fir_natural_u64(exponent_word);
  if (exponent64 > 20u) __builtin_trap();
  unsigned exponent = (unsigned)exponent64;
  unsigned __int128 power5 = fir_pow5(exponent);
  if (negative_exp != 0u) {
    unsigned log = mantissa == 0 ? 0u : fir_log2_u128(mantissa);
    unsigned shift = log < 64u ? 64u - log : 0u;
    unsigned total_shift = 3u * exponent + shift;
    if (total_shift >= 128u ||
        (total_shift != 0u &&
         (unsigned __int128)mantissa >
             (~(unsigned __int128)0 >> total_shift))) {
      __builtin_trap();
    }
    unsigned __int128 scaled = (unsigned __int128)mantissa << total_shift;
    return fir_binary_scientific(scaled / power5,
                                 -4 * (int)exponent - (int)shift);
  }
  if (mantissa != 0u &&
      (unsigned __int128)mantissa > ~(unsigned __int128)0 / power5) {
    __builtin_trap();
  }
  return fir_binary_scientific((unsigned __int128)mantissa * power5,
                               (int)exponent);
}

EXPORT("UInt64.toFloat")
double fir_uint64_to_float(uint64_t value) { return (double)value; }

EXPORT("Float.add")
double fir_float_add(double left, double right) { return left + right; }
EXPORT("Float.sub")
double fir_float_sub(double left, double right) { return left - right; }
EXPORT("Float.mul")
double fir_float_mul(double left, double right) { return left * right; }
EXPORT("Float.div")
double fir_float_div(double left, double right) { return left / right; }
EXPORT("Float.neg")
double fir_float_neg(double value) { return -value; }
EXPORT("Float.beq")
uint8_t fir_float_beq(double left, double right) { return left == right; }
EXPORT("Float.decLt")
uint8_t fir_float_dec_lt(double left, double right) { return left < right; }
EXPORT("Float.decLe")
uint8_t fir_float_dec_le(double left, double right) { return left <= right; }

EXPORT("Float.abs")
double fir_float_abs(double value) { return fabs(value); }
EXPORT("Float.sqrt")
double fir_float_sqrt(double value) { return sqrt(value); }
EXPORT("Float.sin")
double fir_float_sin(double value) { return sin(value); }
EXPORT("Float.cos")
double fir_float_cos(double value) { return cos(value); }
EXPORT("Float.acos")
double fir_float_acos(double value) { return acos(value); }
EXPORT("Float.atan2")
double fir_float_atan2(double y, double x) { return atan2(y, x); }
EXPORT("Float.cbrt")
double fir_float_cbrt(double value) { return cbrt(value); }
EXPORT("Float.floor")
double fir_float_floor(double value) { return floor(value); }
