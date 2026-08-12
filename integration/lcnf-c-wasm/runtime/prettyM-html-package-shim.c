#include <stdint.h>

#include <lean/lean.h>

lean_object *initialize_VersoSlides_Pretty(uint8_t builtin);

/*
 * The source module publicly imports Lean only for browser-independent JSON
 * instances that are unreachable from `formatHtmlForRuntime`. The bounded
 * Emscripten runtime intentionally links Init and Std, not Lean's compiler
 * implementation. LTO removes that unreachable meta surface; these two
 * initializers satisfy the generated module prologue without initializing a
 * compiler that is absent from the artifact.
 */
LEAN_EXPORT lean_object *initialize_Lean(uint8_t builtin) {
    (void)builtin;
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_object *runtime_initialize_Lean(uint8_t builtin) {
    (void)builtin;
    return lean_io_result_mk_ok(lean_box(0));
}

/*
 * `VersoSlides.Pretty` is built as an external source library of the
 * VersoFirHtml package. Its package-private functions retain the package ID,
 * while Lean's generated module initializer keeps the public module name.
 * Bridge those two compiler-generated names without changing the source API.
 */
LEAN_EXPORT lean_object *initialize_VersoFirHtml_VersoSlides_Pretty(
    uint8_t builtin) {
    return initialize_VersoSlides_Pretty(builtin);
}
