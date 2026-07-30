#include <stdint.h>
#include <stdlib.h>

#include <lean/lean.h>

_Static_assert(
    sizeof(void *) == 4,
    "the WASI Lean constructor core requires wasm32");

/*
This is the single-threaded constructor subset of Lean's object runtime. It
uses the object layout, allocation path, and reference-count ABI from the
pinned public lean.h. Non-constructor objects and multi-threaded reference
counts are outside this profile and fail closed instead of acquiring partial
host-service implementations.
*/

static uint64_t g_allocations;
static uint64_t g_deallocations;
static uint64_t g_live_objects;
static uint64_t g_peak_live_objects;

static void fir_lcnf_c_wasi_runtime_abort(void) {
    abort();
}

LEAN_EXPORT void lean_inc_heartbeat(void) {
    ++g_allocations;
    ++g_live_objects;
    if (g_live_objects > g_peak_live_objects) {
        g_peak_live_objects = g_live_objects;
    }
}

LEAN_EXPORT LEAN_NORETURN void lean_internal_panic_out_of_memory(void) {
    fir_lcnf_c_wasi_runtime_abort();
    __builtin_unreachable();
}

static void fir_lcnf_c_wasi_free_constructor(lean_object *object) {
    size_t *allocation;

    if (lean_ptr_tag(object) > LeanMaxCtorTag || g_live_objects == 0) {
        fir_lcnf_c_wasi_runtime_abort();
    }

    allocation = (size_t *)object - 1;
    free(allocation);
    ++g_deallocations;
    --g_live_objects;
}

LEAN_EXPORT void lean_free_object(lean_object *object) {
    fir_lcnf_c_wasi_free_constructor(object);
}

static void fir_lcnf_c_wasi_push(
    lean_object **todo,
    lean_object *object) {
    *(lean_object **)object = *todo;
    *todo = object;
}

static lean_object *fir_lcnf_c_wasi_pop(lean_object **todo) {
    lean_object *object = *todo;
    *todo = *(lean_object **)object;
    return object;
}

static void fir_lcnf_c_wasi_release_edge(
    lean_object *object,
    lean_object **todo) {
    if (lean_is_scalar(object) || object->m_rc == 0) {
        return;
    }
    if (object->m_rc > 1) {
        --object->m_rc;
        return;
    }
    if (object->m_rc == 1) {
        fir_lcnf_c_wasi_push(todo, object);
        return;
    }

    /* Multi-threaded objects are not admitted by this reactor profile. */
    fir_lcnf_c_wasi_runtime_abort();
}

LEAN_EXPORT void lean_dec_ref_cold(lean_object *object) {
    lean_object *todo = NULL;

    if (object->m_rc != 1) {
        fir_lcnf_c_wasi_runtime_abort();
    }

    for (;;) {
        lean_object **field;
        lean_object **end;

        if (lean_ptr_tag(object) > LeanMaxCtorTag) {
            fir_lcnf_c_wasi_runtime_abort();
        }

        field = lean_ctor_obj_cptr(object);
        end = field + lean_ctor_num_objs(object);
        for (; field != end; ++field) {
            fir_lcnf_c_wasi_release_edge(*field, &todo);
        }
        fir_lcnf_c_wasi_free_constructor(object);

        if (todo == NULL) {
            return;
        }
        object = fir_lcnf_c_wasi_pop(&todo);
    }
}

LEAN_EXPORT uint32_t fir_lcnf_c_wasi_runtime_abi(void) {
    return 1;
}

LEAN_EXPORT uint64_t fir_lcnf_c_wasi_allocations(void) {
    return g_allocations;
}

LEAN_EXPORT uint64_t fir_lcnf_c_wasi_deallocations(void) {
    return g_deallocations;
}

LEAN_EXPORT uint64_t fir_lcnf_c_wasi_live_objects(void) {
    return g_live_objects;
}

LEAN_EXPORT uint64_t fir_lcnf_c_wasi_peak_live_objects(void) {
    return g_peak_live_objects;
}
