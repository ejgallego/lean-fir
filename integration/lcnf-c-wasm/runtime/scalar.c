#include <stdint.h>

#if defined(__clang__) || defined(__GNUC__)
#define FIR_WASM_CONST __attribute__((const))
#else
#define FIR_WASM_CONST
#endif

FIR_WASM_CONST uint8_t lean_uint64_dec_eq(uint64_t lhs, uint64_t rhs) {
    return lhs == rhs;
}

FIR_WASM_CONST uint64_t lean_uint64_add(uint64_t lhs, uint64_t rhs) {
    return lhs + rhs;
}

FIR_WASM_CONST uint64_t lean_uint64_sub(uint64_t lhs, uint64_t rhs) {
    return lhs - rhs;
}

FIR_WASM_CONST uint64_t lean_uint64_mul(uint64_t lhs, uint64_t rhs) {
    return lhs * rhs;
}
