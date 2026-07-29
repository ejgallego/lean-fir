#include <stdio.h>

#include <lean/lean.h>

/*
 * libleanrt uses this Init-level export only for debug traces. Standalone
 * generated modules do not otherwise need libInit, so keep the bridge narrow
 * and preserve the consuming Lean ABI of IO.eprintln.
 */
lean_object * lean_io_eprintln(lean_object * message) {
    fputs(lean_string_cstr(message), stderr);
    fputc('\n', stderr);
    lean_dec(message);
    return lean_io_result_mk_ok(lean_box(0));
}
