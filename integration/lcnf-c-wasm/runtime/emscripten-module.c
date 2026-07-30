#include <stdint.h>

#include <lean/lean.h>

#ifndef FIR_LCNF_C_MODULE_INITIALIZER
#error "FIR_LCNF_C_MODULE_INITIALIZER must name the generated Lean initializer"
#endif

void lean_initialize_runtime_module(void);
void lean_io_mark_end_initialization(void);
lean_object * FIR_LCNF_C_MODULE_INITIALIZER(uint8_t builtin);

#ifdef FIR_LCNF_C_IO_START
lean_object * FIR_LCNF_C_IO_START(void);
#endif

LEAN_EXPORT uint32_t fir_lcnf_c_initialize(void) {
    static uint8_t attempted = 0;
    static uint32_t result = 0;
    lean_object * io_result;

    if (attempted) {
        return result;
    }
    attempted = 1;

    lean_initialize_runtime_module();
    io_result = FIR_LCNF_C_MODULE_INITIALIZER(/* builtin */ 1);
    lean_io_mark_end_initialization();
    if (lean_io_result_is_error(io_result)) {
        lean_io_result_show_error(io_result);
        lean_dec(io_result);
        result = 1;
        return result;
    }
    lean_dec(io_result);

#ifdef FIR_LCNF_C_IO_START
    io_result = FIR_LCNF_C_IO_START();
    if (lean_io_result_is_error(io_result)) {
        lean_io_result_show_error(io_result);
        lean_dec(io_result);
        result = 2;
        return result;
    }
    result = lean_unbox_uint32(lean_io_result_get_value(io_result));
    lean_dec(io_result);
#else
    result = 0;
#endif
    return result;
}
