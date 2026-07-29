#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>

#include <lean/lean.h>

void lean_initialize_runtime_module(void);
void lean_io_mark_end_initialization(void);
lean_object * initialize_RuntimeSmoke(uint8_t builtin);
uint64_t fir_lcnf_c_runtime_checksum(uint64_t rounds, uint64_t seed);

struct runtime_case {
    uint64_t rounds;
    uint64_t seed;
};

int main(void) {
    static const struct runtime_case cases[] = {
        {0, 17},
        {1, 17},
        {10, 17},
        {1000, UINT64_C(0x123456789abcdef0)},
        {16384, UINT64_MAX},
    };
    lean_object * result;
    size_t index;

    lean_initialize_runtime_module();
    result = initialize_RuntimeSmoke(/* builtin */ 1);
    lean_io_mark_end_initialization();
    if (lean_io_result_is_error(result)) {
        lean_io_result_show_error(result);
        lean_dec(result);
        return 1;
    }
    lean_dec(result);

    for (index = 0; index < sizeof(cases) / sizeof(cases[0]); ++index) {
        uint64_t checksum = fir_lcnf_c_runtime_checksum(
            cases[index].rounds,
            cases[index].seed);
        printf(
            "%" PRIu64 " %" PRIu64 " %" PRIu64 "\n",
            cases[index].rounds,
            cases[index].seed,
            checksum);
    }
    return 0;
}
