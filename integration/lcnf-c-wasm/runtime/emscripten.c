#include <stdint.h>

#include <lean/lean.h>

void lean_initialize_runtime_module(void);
lean_object * initialize_RuntimeSmoke(uint8_t builtin);
lean_object * fir_lcnf_c_runtime_probe(void);

LEAN_EXPORT uint32_t fir_lcnf_c_runtime_initialize(void) {
    static uint32_t result = UINT32_MAX;
    lean_object * io_result;

    if (result != UINT32_MAX) {
        return result;
    }

    lean_initialize_runtime_module();
    io_result = initialize_RuntimeSmoke(/* builtin */ 1);
    if (lean_io_result_is_error(io_result)) {
        lean_io_result_show_error(io_result);
        lean_dec(io_result);
        result = 1;
        return result;
    }
    lean_dec(io_result);

    io_result = fir_lcnf_c_runtime_probe();
    if (lean_io_result_is_error(io_result)) {
        lean_io_result_show_error(io_result);
        lean_dec(io_result);
        result = 2;
        return result;
    }
    result = lean_unbox_uint32(lean_io_result_get_value(io_result));
    lean_dec(io_result);
    return result;
}
