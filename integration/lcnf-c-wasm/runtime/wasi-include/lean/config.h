/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

WASI core-runtime configuration for the pinned Lean public C ABI.
*/
#pragma once
#include <lean/version.h>

/*
The host Lean installation uses mimalloc. The WASI core profile deliberately
uses lean.h's libc allocator path instead, because wasi-sdk does not ship that
host-specific allocator. Keep every object header and calling convention in
the pinned public lean.h; only the allocator selection changes here.
*/

#define LEAN_IS_STAGE0 0
