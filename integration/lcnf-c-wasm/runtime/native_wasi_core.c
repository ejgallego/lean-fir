#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>

uint64_t fir_lcnf_c_wasi_core_checksum(uint64_t rounds, uint64_t seed);

struct wasi_core_case {
    uint64_t rounds;
    uint64_t seed;
};

int main(void) {
    static const struct wasi_core_case cases[] = {
        {0, 17},
        {1, 17},
        {10, 17},
        {1000, UINT64_C(0x123456789abcdef0)},
        {65536, UINT64_MAX},
    };
    size_t index;

    for (index = 0; index < sizeof(cases) / sizeof(cases[0]); ++index) {
        uint64_t checksum = fir_lcnf_c_wasi_core_checksum(
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
