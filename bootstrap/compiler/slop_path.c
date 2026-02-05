#include "../runtime/slop_runtime.h"
#include "slop_path.h"

slop_string path_path_dirname(slop_arena* arena, slop_string path);
slop_string path_path_join(slop_arena* arena, slop_string base, slop_string rel);
slop_string path_path_basename(slop_arena* arena, slop_string path);
slop_string path_path_extension(slop_arena* arena, slop_string path);

slop_string path_path_dirname(slop_arena* arena, slop_string path) {
    {
        __auto_type len = ((int64_t)(path.len));
        if ((len == 0)) {
            return SLOP_STR(".");
        } else {
            __auto_type _mv_1111 = strlib_last_index_of(path, SLOP_STR("/"));
            if (_mv_1111.has_value) {
                __auto_type idx = _mv_1111.value;
                if ((idx == 0)) {
                    return SLOP_STR("/");
                } else {
                    return strlib_substring(arena, path, 0, ((int64_t)(idx)));
                }
            } else if (!_mv_1111.has_value) {
                return SLOP_STR(".");
            }
        }
    }
}

slop_string path_path_join(slop_arena* arena, slop_string base, slop_string rel) {
    {
        __auto_type base_len = ((int64_t)(base.len));
        __auto_type rel_len = ((int64_t)(rel.len));
        if ((base_len == 0)) {
            return rel;
        } else if ((rel_len == 0)) {
            return base;
        } else {
            {
                __auto_type slash = SLOP_STR("/");
                return string_concat(arena, base, string_concat(arena, slash, rel));
            }
        }
    }
}

slop_string path_path_basename(slop_arena* arena, slop_string path) {
    {
        __auto_type len = ((int64_t)(path.len));
        if ((len == 0)) {
            return SLOP_STR("");
        } else {
            __auto_type _mv_1112 = strlib_last_index_of(path, SLOP_STR("/"));
            if (_mv_1112.has_value) {
                __auto_type idx = _mv_1112.value;
                {
                    __auto_type start = (idx + 1);
                    __auto_type remaining = (len - start);
                    if ((remaining <= 0)) {
                        return SLOP_STR("");
                    } else {
                        return strlib_substring(arena, path, ((int64_t)(start)), ((int64_t)(remaining)));
                    }
                }
            } else if (!_mv_1112.has_value) {
                return path;
            }
        }
    }
}

slop_string path_path_extension(slop_arena* arena, slop_string path) {
    {
        __auto_type len = ((int64_t)(path.len));
        if ((len == 0)) {
            return SLOP_STR("");
        } else {
            __auto_type _mv_1113 = strlib_last_index_of(path, SLOP_STR("."));
            if (_mv_1113.has_value) {
                __auto_type idx = _mv_1113.value;
                {
                    __auto_type ext_len = (len - idx);
                    if ((ext_len <= 0)) {
                        return SLOP_STR("");
                    } else {
                        return strlib_substring(arena, path, ((int64_t)(idx)), ((int64_t)(ext_len)));
                    }
                }
            } else if (!_mv_1113.has_value) {
                return SLOP_STR("");
            }
        }
    }
}

