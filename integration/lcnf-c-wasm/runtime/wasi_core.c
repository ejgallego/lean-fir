#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include <lean/lean.h>

_Static_assert(
    sizeof(void *) == 4,
    "the WASI Lean core-object runtime requires wasm32");

/*
This is the single-threaded core-object subset of Lean's runtime. It uses the
object layout, allocation paths, and reference-count ABI from the pinned
public lean.h. The admitted large objects are closures, ordinary object
arrays, scalar byte arrays, and strings. Other object kinds, partial
application, and multi-threaded reference counts fail closed instead of
acquiring partial host-service implementations.
*/

static uint64_t g_allocations;
static uint64_t g_deallocations;
static uint64_t g_live_objects;
static uint64_t g_peak_live_objects;
static uint64_t g_constructor_deallocations;
static uint64_t g_closure_deallocations;
static uint64_t g_array_deallocations;
static uint64_t g_scalar_array_deallocations;
static uint64_t g_string_deallocations;

static LEAN_NORETURN void fir_lcnf_c_wasi_runtime_abort(void) {
    abort();
    __builtin_unreachable();
}

static void fir_lcnf_c_wasi_record_allocation(void) {
    ++g_allocations;
    ++g_live_objects;
    if (g_live_objects > g_peak_live_objects) {
        g_peak_live_objects = g_live_objects;
    }
}

LEAN_EXPORT void lean_inc_heartbeat(void) {
    fir_lcnf_c_wasi_record_allocation();
}

LEAN_EXPORT lean_object *lean_alloc_object(size_t size) {
    lean_object *object = (lean_object *)malloc(size);
    if (object == NULL) {
        lean_internal_panic_out_of_memory();
    }
    fir_lcnf_c_wasi_record_allocation();
    return object;
}

LEAN_EXPORT LEAN_NORETURN void lean_internal_panic_out_of_memory(void) {
    fir_lcnf_c_wasi_runtime_abort();
    __builtin_unreachable();
}

LEAN_EXPORT LEAN_NORETURN void lean_internal_panic_overflow(void) {
    fir_lcnf_c_wasi_runtime_abort();
    __builtin_unreachable();
}

LEAN_EXPORT LEAN_NORETURN void lean_internal_panic_rc_overflow(void) {
    fir_lcnf_c_wasi_runtime_abort();
    __builtin_unreachable();
}

static void fir_lcnf_c_wasi_free_storage(lean_object *object) {
    uint8_t tag = lean_ptr_tag(object);

    if (g_live_objects == 0) {
        fir_lcnf_c_wasi_runtime_abort();
    }

    if (tag <= LeanMaxCtorTag) {
        free((size_t *)object - 1);
        ++g_constructor_deallocations;
    } else {
        switch (tag) {
        case LeanClosure:
            ++g_closure_deallocations;
            break;
        case LeanArray:
            ++g_array_deallocations;
            break;
        case LeanScalarArray:
            ++g_scalar_array_deallocations;
            break;
        case LeanString:
            ++g_string_deallocations;
            break;
        default:
            fir_lcnf_c_wasi_runtime_abort();
        }
        free(object);
    }

    ++g_deallocations;
    --g_live_objects;
}

LEAN_EXPORT void lean_free_object(lean_object *object) {
    fir_lcnf_c_wasi_free_storage(object);
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
        lean_object **field = NULL;
        lean_object **end = NULL;
        uint8_t tag = lean_ptr_tag(object);

        if (tag <= LeanMaxCtorTag) {
            field = lean_ctor_obj_cptr(object);
            end = field + lean_ctor_num_objs(object);
        } else if (tag == LeanClosure) {
            field = lean_closure_arg_cptr(object);
            end = field + lean_closure_num_fixed(object);
        } else if (tag == LeanArray) {
            field = lean_array_cptr(object);
            end = field + lean_array_size(object);
        } else if (tag != LeanScalarArray && tag != LeanString) {
            fir_lcnf_c_wasi_runtime_abort();
        }

        for (; field != end; ++field) {
            fir_lcnf_c_wasi_release_edge(*field, &todo);
        }
        fir_lcnf_c_wasi_free_storage(object);

        if (todo == NULL) {
            return;
        }
        object = fir_lcnf_c_wasi_pop(&todo);
    }
}

static size_t fir_lcnf_c_wasi_expanded_capacity(size_t capacity) {
    if (capacity > (SIZE_MAX / 2) - 1) {
        lean_internal_panic_overflow();
    }
    return (capacity + 1) * 2;
}

LEAN_EXPORT lean_object *lean_copy_expand_array(
    lean_object *array,
    bool expand) {
    size_t size;
    size_t capacity;
    lean_object *result;
    lean_object **source;
    lean_object **destination;
    size_t index;

    if (!lean_is_array(array) || array->m_rc < 0) {
        fir_lcnf_c_wasi_runtime_abort();
    }
    size = lean_array_size(array);
    capacity = lean_array_capacity(array);
    if (capacity < size) {
        fir_lcnf_c_wasi_runtime_abort();
    }
    if (expand) {
        capacity = fir_lcnf_c_wasi_expanded_capacity(capacity);
    }
    if (capacity < size || (expand && capacity == size)) {
        lean_internal_panic_overflow();
    }

    result = lean_alloc_array(size, capacity);
    source = lean_array_cptr(array);
    destination = lean_array_cptr(result);
    if (lean_is_exclusive(array)) {
        memcpy(destination, source, size * sizeof(lean_object *));
        lean_free_object(array);
    } else {
        for (index = 0; index < size; ++index) {
            destination[index] = source[index];
            lean_inc(source[index]);
        }
        lean_dec(array);
    }
    return result;
}

LEAN_EXPORT lean_object *lean_copy_expand_array_nonlinear(
    lean_object *array,
    bool expand) {
    return lean_copy_expand_array(array, expand);
}

LEAN_EXPORT lean_object *lean_array_push(
    lean_object *array,
    lean_object *value) {
    lean_object *result;
    size_t size;
    size_t capacity;

    if (!lean_is_array(array) || array->m_rc < 0) {
        fir_lcnf_c_wasi_runtime_abort();
    }
    size = lean_array_size(array);
    capacity = lean_array_capacity(array);
    if (capacity < size) {
        fir_lcnf_c_wasi_runtime_abort();
    }
    if (lean_is_exclusive(array)) {
        result = capacity > size
            ? array
            : lean_copy_expand_array(array, true);
    } else {
        bool expand;
        if (size > (SIZE_MAX - 1) / 2) {
            expand = true;
        } else {
            expand = capacity < 2 * size + 1;
        }
        result = lean_copy_expand_array_nonlinear(array, expand);
    }

    size = lean_array_size(result);
    if (lean_array_capacity(result) <= size) {
        fir_lcnf_c_wasi_runtime_abort();
    }
    lean_array_cptr(result)[size] = value;
    lean_to_array(result)->m_size = size + 1;
    return result;
}

LEAN_EXPORT lean_object *lean_copy_byte_array(lean_object *array) {
    size_t size;
    size_t capacity;
    lean_object *result;

    if (!lean_is_sarray(array) ||
        lean_sarray_elem_size(array) != 1 ||
        array->m_rc < 0) {
        fir_lcnf_c_wasi_runtime_abort();
    }
    size = lean_sarray_size(array);
    capacity = lean_sarray_capacity(array);
    if (capacity < size ||
        lean_alloc_sarray_would_overflow(1, capacity)) {
        fir_lcnf_c_wasi_runtime_abort();
    }

    result = lean_alloc_sarray(1, size, capacity);
    memcpy(lean_sarray_cptr(result), lean_sarray_cptr(array), size);
    lean_dec(array);
    return result;
}

LEAN_EXPORT lean_object *lean_byte_array_push(
    lean_object *array,
    uint8_t value) {
    size_t size;
    size_t capacity;
    size_t minimum_capacity;
    lean_object *result;

    if (!lean_is_sarray(array) ||
        lean_sarray_elem_size(array) != 1 ||
        array->m_rc < 0) {
        fir_lcnf_c_wasi_runtime_abort();
    }
    size = lean_sarray_size(array);
    capacity = lean_sarray_capacity(array);
    if (capacity < size || size == SIZE_MAX) {
        lean_internal_panic_overflow();
    }
    minimum_capacity = size + 1;

    if (lean_is_exclusive(array) && capacity >= minimum_capacity) {
        result = array;
    } else {
        size_t new_capacity = capacity;

        if (new_capacity < minimum_capacity) {
            if (minimum_capacity > SIZE_MAX / 2) {
                lean_internal_panic_overflow();
            }
            new_capacity = minimum_capacity * 2;
        }
        if (lean_alloc_sarray_would_overflow(1, new_capacity)) {
            lean_internal_panic_overflow();
        }
        result = lean_alloc_sarray(1, size, new_capacity);
        memcpy(lean_sarray_cptr(result), lean_sarray_cptr(array), size);
        lean_dec(array);
    }

    lean_sarray_cptr(result)[size] = value;
    lean_sarray_set_size(result, minimum_capacity);
    return result;
}

static lean_object *fir_lcnf_c_wasi_ensure_string_capacity(
    lean_object *string,
    size_t extra) {
    size_t size = lean_string_size(string);
    size_t capacity = lean_string_capacity(string);
    size_t required;

    if (!lean_is_exclusive(string) ||
        lean_usize_add_would_overflow(size, extra)) {
        fir_lcnf_c_wasi_runtime_abort();
    }
    required = size + extra;
    if (required > capacity) {
        size_t new_capacity;
        lean_object *result;

        if (lean_usize_add_would_overflow(capacity, required)) {
            lean_internal_panic_overflow();
        }
        new_capacity = capacity + required;
        result = lean_alloc_string(
            size,
            new_capacity,
            lean_string_len(string));
        memcpy(lean_to_string(result)->m_data, lean_string_cstr(string), size);
        lean_free_object(string);
        return result;
    }
    return string;
}

LEAN_EXPORT lean_object *lean_string_append(
    lean_object *left,
    lean_object *right) {
    size_t left_size;
    size_t right_size;
    size_t new_size;
    size_t new_length;
    lean_object *result;

    if (!lean_is_string(left) || !lean_is_string(right) ||
        left->m_rc < 0 || right->m_rc < 0) {
        fir_lcnf_c_wasi_runtime_abort();
    }
    left_size = lean_string_size(left);
    right_size = lean_string_size(right);
    if (left_size == 0 || right_size == 0 ||
        lean_usize_add_would_overflow(left_size, right_size - 1) ||
        lean_usize_add_would_overflow(
            lean_string_len(left),
            lean_string_len(right))) {
        lean_internal_panic_overflow();
    }
    new_size = left_size + right_size - 1;
    new_length = lean_string_len(left) + lean_string_len(right);

    if (!lean_is_exclusive(left)) {
        size_t new_capacity;
        if (new_size > SIZE_MAX / 2) {
            lean_internal_panic_overflow();
        }
        new_capacity = new_size * 2;
        result = lean_alloc_string(new_size, new_capacity, new_length);
        memcpy(
            lean_to_string(result)->m_data,
            lean_string_cstr(left),
            left_size - 1);
        lean_dec_ref(left);
    } else {
        if (left == right) {
            fir_lcnf_c_wasi_runtime_abort();
        }
        result = fir_lcnf_c_wasi_ensure_string_capacity(
            left,
            right_size - 1);
    }

    memcpy(
        lean_to_string(result)->m_data + left_size - 1,
        lean_string_cstr(right),
        right_size - 1);
    lean_to_string(result)->m_size = new_size;
    lean_to_string(result)->m_length = new_length;
    lean_to_string(result)->m_data[new_size - 1] = '\0';
    return result;
}

typedef lean_object *(*fir_lcnf_c_wasi_fn1)(lean_object *);
typedef lean_object *(*fir_lcnf_c_wasi_fn2)(
    lean_object *,
    lean_object *);
typedef lean_object *(*fir_lcnf_c_wasi_fn3)(
    lean_object *,
    lean_object *,
    lean_object *);

static fir_lcnf_c_wasi_fn1 fir_lcnf_c_wasi_closure_fn1(
    lean_object *closure) {
    fir_lcnf_c_wasi_fn1 function;
    void *raw = lean_closure_fun(closure);

    _Static_assert(
        sizeof(function) == sizeof(raw),
        "WASI closure code and data pointers must have the same size");
    memcpy(&function, &raw, sizeof(function));
    return function;
}

static fir_lcnf_c_wasi_fn2 fir_lcnf_c_wasi_closure_fn2(
    lean_object *closure) {
    fir_lcnf_c_wasi_fn2 function;
    void *raw = lean_closure_fun(closure);

    _Static_assert(
        sizeof(function) == sizeof(raw),
        "WASI closure code and data pointers must have the same size");
    memcpy(&function, &raw, sizeof(function));
    return function;
}

static fir_lcnf_c_wasi_fn3 fir_lcnf_c_wasi_closure_fn3(
    lean_object *closure) {
    fir_lcnf_c_wasi_fn3 function;
    void *raw = lean_closure_fun(closure);

    _Static_assert(
        sizeof(function) == sizeof(raw),
        "WASI closure code and data pointers must have the same size");
    memcpy(&function, &raw, sizeof(function));
    return function;
}

LEAN_EXPORT lean_object *lean_apply_1(
    lean_object *closure,
    lean_object *argument) {
    unsigned arity;
    unsigned fixed;
    bool exclusive;
    lean_object *result;

    if (lean_is_scalar(closure)) {
        lean_dec(argument);
        return closure;
    }
    if (!lean_is_closure(closure) || closure->m_rc < 0) {
        fir_lcnf_c_wasi_runtime_abort();
    }

    arity = lean_closure_arity(closure);
    fixed = lean_closure_num_fixed(closure);
    if (arity != fixed + 1) {
        fir_lcnf_c_wasi_runtime_abort();
    }
    exclusive = lean_is_exclusive(closure);

    if (arity == 1) {
        result = fir_lcnf_c_wasi_closure_fn1(closure)(argument);
    } else if (arity == 2) {
        lean_object *captured = lean_closure_get(closure, 0);
        if (!exclusive) {
            lean_inc(captured);
        }
        result = fir_lcnf_c_wasi_closure_fn2(closure)(captured, argument);
    } else {
        fir_lcnf_c_wasi_runtime_abort();
    }

    if (exclusive) {
        lean_free_object(closure);
    } else {
        lean_dec_ref(closure);
    }
    return result;
}

LEAN_EXPORT lean_object *lean_apply_2(
    lean_object *closure,
    lean_object *first,
    lean_object *second) {
    unsigned arity;
    unsigned fixed;
    bool exclusive;
    lean_object *result;

    if (lean_is_scalar(closure)) {
        lean_dec(first);
        lean_dec(second);
        return closure;
    }
    if (!lean_is_closure(closure) || closure->m_rc < 0) {
        fir_lcnf_c_wasi_runtime_abort();
    }

    arity = lean_closure_arity(closure);
    fixed = lean_closure_num_fixed(closure);
    if (arity != fixed + 2) {
        fir_lcnf_c_wasi_runtime_abort();
    }
    exclusive = lean_is_exclusive(closure);

    if (arity == 2) {
        result = fir_lcnf_c_wasi_closure_fn2(closure)(first, second);
    } else if (arity == 3) {
        lean_object *captured = lean_closure_get(closure, 0);
        if (!exclusive) {
            lean_inc(captured);
        }
        result = fir_lcnf_c_wasi_closure_fn3(closure)(
            captured,
            first,
            second);
    } else {
        fir_lcnf_c_wasi_runtime_abort();
    }

    if (exclusive) {
        lean_free_object(closure);
    } else {
        lean_dec_ref(closure);
    }
    return result;
}

LEAN_EXPORT uint32_t fir_lcnf_c_wasi_runtime_abi(void) {
    return 3;
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

LEAN_EXPORT uint64_t fir_lcnf_c_wasi_constructor_deallocations(void) {
    return g_constructor_deallocations;
}

LEAN_EXPORT uint64_t fir_lcnf_c_wasi_closure_deallocations(void) {
    return g_closure_deallocations;
}

LEAN_EXPORT uint64_t fir_lcnf_c_wasi_array_deallocations(void) {
    return g_array_deallocations;
}

LEAN_EXPORT uint64_t fir_lcnf_c_wasi_scalar_array_deallocations(void) {
    return g_scalar_array_deallocations;
}

LEAN_EXPORT uint64_t fir_lcnf_c_wasi_string_deallocations(void) {
    return g_string_deallocations;
}
