#define _POSIX_C_SOURCE 200809L

#include <errno.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <time.h>

#include <lean/lean.h>

void lean_initialize_runtime_module(void);
void lean_io_mark_end_initialization(void);
lean_object * initialize_RuntimeSmoke(uint8_t builtin);
uint64_t fir_lcnf_c_runtime_checksum(uint64_t rounds, uint64_t seed);

static volatile uint64_t benchmark_sink;

static uint64_t monotonic_nanoseconds(void) {
    struct timespec timestamp;
    if (clock_gettime(CLOCK_MONOTONIC, &timestamp) != 0) {
        perror("clock_gettime");
        exit(2);
    }
    return (uint64_t)timestamp.tv_sec * UINT64_C(1000000000) +
        (uint64_t)timestamp.tv_nsec;
}

static uint64_t parse_uint64(const char * label, const char * text) {
    char * end = NULL;
    unsigned long long value;

    errno = 0;
    value = strtoull(text, &end, 0);
    if (errno != 0 || end == text || *end != '\0') {
        fprintf(stderr, "invalid %s: %s\n", label, text);
        exit(2);
    }
    return (uint64_t)value;
}

static uint64_t max_rss_bytes(void) {
    struct rusage usage;
    if (getrusage(RUSAGE_SELF, &usage) != 0) {
        return 0;
    }
#if defined(__APPLE__)
    return (uint64_t)usage.ru_maxrss;
#else
    return (uint64_t)usage.ru_maxrss * UINT64_C(1024);
#endif
}

static long process_thread_count(void) {
    FILE * status = fopen("/proc/self/status", "r");
    char line[256];
    long threads = -1;

    if (status == NULL) {
        return -1;
    }
    while (fgets(line, sizeof(line), status) != NULL) {
        if (sscanf(line, "Threads: %ld", &threads) == 1) {
            break;
        }
    }
    fclose(status);
    return threads;
}

static uint64_t initialize_module(void) {
    uint64_t start = monotonic_nanoseconds();
    lean_object * result;

    lean_initialize_runtime_module();
    result = initialize_RuntimeSmoke(/* builtin */ 1);
    lean_io_mark_end_initialization();
    if (lean_io_result_is_error(result)) {
        lean_io_result_show_error(result);
        lean_dec(result);
        exit(1);
    }
    lean_dec(result);
    return monotonic_nanoseconds() - start;
}

int main(int argc, char ** argv) {
    const char * phase;
    uint64_t rounds;
    uint64_t iterations;
    uint64_t warmup_iterations;
    uint64_t seed;
    uint64_t initialization_nanoseconds;
    uint64_t subject_nanoseconds;
    uint64_t aggregate = 0;
    uint64_t index;
    long threads;

    if (argc != 6) {
        fprintf(
            stderr,
            "usage: %s <startup|steady> <rounds> <iterations> "
            "<warmup-iterations> <seed>\n",
            argv[0]);
        return 2;
    }
    phase = argv[1];
    rounds = parse_uint64("rounds", argv[2]);
    iterations = parse_uint64("iterations", argv[3]);
    warmup_iterations = parse_uint64("warmup iterations", argv[4]);
    seed = parse_uint64("seed", argv[5]);
    if (iterations == 0) {
        fprintf(stderr, "iterations must be positive\n");
        return 2;
    }

    initialization_nanoseconds = initialize_module();
    if (strcmp(phase, "startup") == 0) {
        aggregate = fir_lcnf_c_runtime_checksum(rounds, seed);
        subject_nanoseconds = initialization_nanoseconds;
    } else if (strcmp(phase, "steady") == 0) {
        for (index = 0; index < warmup_iterations; ++index) {
            benchmark_sink = fir_lcnf_c_runtime_checksum(rounds, seed);
        }
        {
            uint64_t start = monotonic_nanoseconds();
            for (index = 0; index < iterations; ++index) {
                aggregate +=
                    fir_lcnf_c_runtime_checksum(rounds, seed) + index;
            }
            subject_nanoseconds = monotonic_nanoseconds() - start;
        }
    } else {
        fprintf(stderr, "unknown phase: %s\n", phase);
        return 2;
    }

    benchmark_sink = aggregate;
    threads = process_thread_count();
    printf(
        "{\"schemaVersion\":1,\"profile\":\"native\","
        "\"phase\":\"%s\",\"subjectElapsedNs\":\"%" PRIu64 "\","
        "\"initializationElapsedNs\":\"%" PRIu64 "\","
        "\"result\":\"%" PRIu64 "\",\"runtime\":{"
        "\"maxRssBytes\":%" PRIu64 ",\"processThreadCount\":%ld,"
        "\"declaredMemory\":null,\"sharedMemory\":false}}\n",
        phase,
        subject_nanoseconds,
        initialization_nanoseconds,
        aggregate,
        max_rss_bytes(),
        threads);
    return 0;
}
