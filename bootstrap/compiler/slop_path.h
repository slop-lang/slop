#ifndef SLOP_path_H
#define SLOP_path_H

#include "../runtime/slop_runtime.h"
#include <stdint.h>
#include <stdbool.h>
#include "slop_strlib.h"

slop_string path_path_dirname(slop_arena* arena, slop_string path);
slop_string path_path_join(slop_arena* arena, slop_string base, slop_string rel);
slop_string path_path_basename(slop_arena* arena, slop_string path);
slop_string path_path_extension(slop_arena* arena, slop_string path);


#endif
