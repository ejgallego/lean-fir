#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include <lean/lean.h>

#define FIR_SELECTION_MAX_REQUEST_BYTES (64U * 1024U * 1024U)
#define FIR_SELECTION_INITIAL_PLAYER_CAPACITY 8U

lean_object *fir_illuminate_selection_create_wire(lean_object *input);
lean_object *fir_illuminate_selection_dispatch_wire(
    lean_object *player,
    lean_object *input);
lean_object *fir_illuminate_selection_dispatch_tick(
    lean_object *player,
    double timestamp);

static uint8_t *fir_selection_input = NULL;
static uint32_t fir_selection_input_capacity = 0;
static uint8_t *fir_selection_result = NULL;
static uint32_t fir_selection_result_size = 0;
static lean_object **fir_selection_players = NULL;
static uint32_t fir_selection_player_capacity = 0;
static uint32_t fir_selection_live_players = 0;
static uint32_t fir_selection_created_handle = 0;

static void fir_selection_clear_result(void) {
    free(fir_selection_result);
    fir_selection_result = NULL;
    fir_selection_result_size = 0;
}

static uint32_t fir_selection_copy_result(lean_object *response) {
    size_t size = lean_sarray_size(response);

    fir_selection_clear_result();
    if (size > UINT32_MAX) {
        return 4;
    }
    if (size != 0) {
        fir_selection_result = malloc(size);
        if (fir_selection_result == NULL) {
            return 5;
        }
        memcpy(fir_selection_result, lean_sarray_cptr(response), size);
    }
    fir_selection_result_size = (uint32_t)size;
    return 0;
}

static lean_object *fir_selection_input_object(uint32_t size) {
    lean_object *input = lean_alloc_sarray(1, size, size);
    if (size != 0) {
        memcpy(lean_sarray_cptr(input), fir_selection_input, size);
    }
    return input;
}

static uint32_t fir_selection_validate_input(uint32_t size) {
    if (size > fir_selection_input_capacity ||
        (size != 0 && fir_selection_input == NULL)) {
        return 1;
    }
    return 0;
}

static uint32_t fir_selection_reserve_player_slot(void) {
    uint32_t index;
    uint32_t next_capacity;
    lean_object **next;

    for (index = 0; index < fir_selection_player_capacity; ++index) {
        if (fir_selection_players[index] == NULL) {
            return index + 1;
        }
    }
    if (fir_selection_player_capacity == UINT32_MAX) {
        return 0;
    }
    next_capacity = fir_selection_player_capacity == 0
        ? FIR_SELECTION_INITIAL_PLAYER_CAPACITY
        : fir_selection_player_capacity * 2;
    if (next_capacity <= fir_selection_player_capacity) {
        next_capacity = UINT32_MAX;
    }
    next = realloc(
        fir_selection_players,
        (size_t)next_capacity * sizeof(lean_object *));
    if (next == NULL) {
        return 0;
    }
    memset(
        next + fir_selection_player_capacity,
        0,
        (size_t)(next_capacity - fir_selection_player_capacity) *
            sizeof(lean_object *));
    index = fir_selection_player_capacity;
    fir_selection_players = next;
    fir_selection_player_capacity = next_capacity;
    return index + 1;
}

static lean_object **fir_selection_player_slot(uint32_t handle) {
    if (handle == 0 || handle > fir_selection_player_capacity) {
        return NULL;
    }
    lean_object **slot = &fir_selection_players[handle - 1];
    return *slot == NULL ? NULL : slot;
}

/*
`WireResult.error` has constructor tag 0 and one ByteArray field.
`WireResult.ok` has constructor tag 1 and RetainedPlayer/ByteArray fields.
The generated entry functions consume their arguments. The table retains its
own reference and increments it before dispatch.
*/
static uint32_t fir_selection_accept_create_result(lean_object *result) {
    lean_object *response;
    lean_object *player;
    uint32_t status;
    uint32_t handle;

    fir_selection_created_handle = 0;
    if (lean_obj_tag(result) == 0) {
        response = lean_ctor_get(result, 0);
        status = fir_selection_copy_result(response);
        lean_dec(result);
        return status;
    }
    if (lean_obj_tag(result) != 1) {
        lean_dec(result);
        return 6;
    }
    player = lean_ctor_get(result, 0);
    response = lean_ctor_get(result, 1);
    status = fir_selection_copy_result(response);
    if (status != 0) {
        lean_dec(result);
        return status;
    }
    handle = fir_selection_reserve_player_slot();
    if (handle == 0) {
        lean_dec(result);
        fir_selection_clear_result();
        return 7;
    }
    lean_inc(player);
    fir_selection_players[handle - 1] = player;
    fir_selection_live_players += 1;
    fir_selection_created_handle = handle;
    lean_dec(result);
    return 0;
}

static uint32_t fir_selection_accept_dispatch_result(
    lean_object **slot,
    lean_object *result) {
    lean_object *response;
    lean_object *next_player;
    lean_object *previous_player;
    uint32_t status;

    if (lean_obj_tag(result) == 0) {
        response = lean_ctor_get(result, 0);
        status = fir_selection_copy_result(response);
        lean_dec(result);
        return status;
    }
    if (lean_obj_tag(result) != 1) {
        lean_dec(result);
        return 6;
    }
    next_player = lean_ctor_get(result, 0);
    response = lean_ctor_get(result, 1);
    status = fir_selection_copy_result(response);
    if (status != 0) {
        lean_dec(result);
        return status;
    }
    lean_inc(next_player);
    previous_player = *slot;
    *slot = next_player;
    lean_dec(previous_player);
    lean_dec(result);
    return 0;
}

LEAN_EXPORT uint32_t fir_illuminate_selection_input_alloc(uint32_t size) {
    uint8_t *next;

    if (size > FIR_SELECTION_MAX_REQUEST_BYTES) {
        return 0;
    }
    free(fir_selection_input);
    fir_selection_input = NULL;
    fir_selection_input_capacity = 0;
    if (size == 0) {
        return 1;
    }
    next = malloc(size);
    if (next == NULL) {
        return 0;
    }
    fir_selection_input = next;
    fir_selection_input_capacity = size;
    return (uint32_t)(uintptr_t)next;
}

LEAN_EXPORT uint32_t fir_illuminate_selection_create(uint32_t size) {
    uint32_t status = fir_selection_validate_input(size);
    if (status != 0) {
        return status;
    }
    return fir_selection_accept_create_result(
        fir_illuminate_selection_create_wire(
            fir_selection_input_object(size)));
}

LEAN_EXPORT uint32_t fir_illuminate_selection_created_handle(void) {
    return fir_selection_created_handle;
}

LEAN_EXPORT uint32_t fir_illuminate_selection_dispatch(
    uint32_t handle,
    uint32_t size) {
    lean_object **slot = fir_selection_player_slot(handle);
    uint32_t status;

    if (slot == NULL) {
        return 2;
    }
    status = fir_selection_validate_input(size);
    if (status != 0) {
        return status;
    }
    lean_inc(*slot);
    return fir_selection_accept_dispatch_result(
        slot,
        fir_illuminate_selection_dispatch_wire(
            *slot,
            fir_selection_input_object(size)));
}

LEAN_EXPORT uint32_t fir_illuminate_selection_dispatch_tick_scalar(
    uint32_t handle,
    double timestamp) {
    lean_object **slot = fir_selection_player_slot(handle);
    if (slot == NULL) {
        return 2;
    }
    lean_inc(*slot);
    return fir_selection_accept_dispatch_result(
        slot,
        fir_illuminate_selection_dispatch_tick(*slot, timestamp));
}

LEAN_EXPORT uint32_t fir_illuminate_selection_result_ptr(void) {
    return (uint32_t)(uintptr_t)fir_selection_result;
}

LEAN_EXPORT uint32_t fir_illuminate_selection_result_len(void) {
    return fir_selection_result_size;
}

LEAN_EXPORT uint32_t fir_illuminate_selection_dispose(uint32_t handle) {
    if (handle == 0 || handle > fir_selection_player_capacity) {
        return 2;
    }
    lean_object **slot = &fir_selection_players[handle - 1];
    if (*slot != NULL) {
        lean_dec(*slot);
        *slot = NULL;
        fir_selection_live_players -= 1;
    }
    return 0;
}

LEAN_EXPORT uint32_t fir_illuminate_selection_live_count(void) {
    return fir_selection_live_players;
}

LEAN_EXPORT void fir_illuminate_selection_release(void) {
    uint32_t index;
    for (index = 0; index < fir_selection_player_capacity; ++index) {
        if (fir_selection_players[index] != NULL) {
            lean_dec(fir_selection_players[index]);
        }
    }
    free(fir_selection_players);
    fir_selection_players = NULL;
    fir_selection_player_capacity = 0;
    fir_selection_live_players = 0;
    fir_selection_created_handle = 0;
    free(fir_selection_input);
    fir_selection_input = NULL;
    fir_selection_input_capacity = 0;
    fir_selection_clear_result();
}
