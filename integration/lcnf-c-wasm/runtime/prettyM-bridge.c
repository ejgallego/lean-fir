#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include <lean/lean.h>

#define FIR_PRETTY_MAX_REQUEST_BYTES (64U * 1024U * 1024U)

lean_object *fir_lcnf_c_pretty_render_wire(lean_object *input);

static uint8_t *fir_pretty_input = NULL;
static uint32_t fir_pretty_input_capacity = 0;
static uint8_t *fir_pretty_result = NULL;
static uint32_t fir_pretty_result_size = 0;

static void fir_pretty_clear_result(void) {
    free(fir_pretty_result);
    fir_pretty_result = NULL;
    fir_pretty_result_size = 0;
}

LEAN_EXPORT uint32_t fir_lcnf_c_pretty_input_alloc(uint32_t size) {
    uint8_t *next;

    if (size > FIR_PRETTY_MAX_REQUEST_BYTES) {
        return 0;
    }
    free(fir_pretty_input);
    fir_pretty_input = NULL;
    fir_pretty_input_capacity = 0;
    if (size == 0) {
        return 1;
    }
    next = malloc(size);
    if (next == NULL) {
        return 0;
    }
    fir_pretty_input = next;
    fir_pretty_input_capacity = size;
    return (uint32_t)(uintptr_t)next;
}

LEAN_EXPORT uint32_t fir_lcnf_c_pretty_render(uint32_t size) {
    lean_object *input;
    lean_object *result;
    size_t result_size;

    fir_pretty_clear_result();
    if (size > fir_pretty_input_capacity ||
        (size != 0 && fir_pretty_input == NULL)) {
        return 1;
    }
    input = lean_alloc_sarray(1, size, size);
    if (size != 0) {
        memcpy(lean_sarray_cptr(input), fir_pretty_input, size);
    }
    result = fir_lcnf_c_pretty_render_wire(input);
    result_size = lean_sarray_size(result);
    if (result_size > UINT32_MAX) {
        lean_dec(result);
        return 2;
    }
    if (result_size != 0) {
        fir_pretty_result = malloc(result_size);
        if (fir_pretty_result == NULL) {
            lean_dec(result);
            return 3;
        }
        memcpy(fir_pretty_result, lean_sarray_cptr(result), result_size);
    }
    fir_pretty_result_size = (uint32_t)result_size;
    lean_dec(result);
    return 0;
}

LEAN_EXPORT uint32_t fir_lcnf_c_pretty_result_ptr(void) {
    return (uint32_t)(uintptr_t)fir_pretty_result;
}

LEAN_EXPORT uint32_t fir_lcnf_c_pretty_result_len(void) {
    return fir_pretty_result_size;
}

LEAN_EXPORT void fir_lcnf_c_pretty_release(void) {
    free(fir_pretty_input);
    fir_pretty_input = NULL;
    fir_pretty_input_capacity = 0;
    fir_pretty_clear_result();
}
