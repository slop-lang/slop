#ifndef SLOP_path_H
#define SLOP_path_H

#include "../runtime/slop_runtime.h"
#ifndef SLOP_RUNTIME_ABI
#error "this module was generated for SLOP runtime ABI 2026-1 (SLOP_RUNTIME_ABI 202601), but slop_runtime.h predates runtime ABI versioning: use the slop_runtime.h of the SLOP release that generated this code"
#elif SLOP_RUNTIME_ABI != 202601
#error "this module was generated for SLOP runtime ABI 2026-1 (SLOP_RUNTIME_ABI 202601), which this slop_runtime.h does not provide (SLOP_RUNTIME_ABI differs): regenerate the C with the SLOP release that matches the runtime, or use the slop_runtime.h of the release that generated it"
#endif
#include <stdint.h>
#include <stdbool.h>
#include "slop_strlib.h"

slop_string std_path_path_dirname(slop_arena* arena, slop_string path);
slop_string std_path_path_join(slop_arena* arena, slop_string base, slop_string rel);
slop_string std_path_path_basename(slop_arena* arena, slop_string path);
slop_string std_path_path_extension(slop_arena* arena, slop_string path);


#endif
