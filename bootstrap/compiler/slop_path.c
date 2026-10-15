#include "../runtime/slop_runtime.h"
#include "slop_path.h"

slop_string std_path_path_dirname(slop_arena* arena, slop_string path);
slop_string std_path_path_join(slop_arena* arena, slop_string base, slop_string rel);
slop_string std_path_path_basename(slop_arena* arena, slop_string path);
slop_string std_path_path_extension(slop_arena* arena, slop_string path);

slop_string std_path_path_dirname(slop_arena* arena, slop_string path) {
    {
        __auto_type len = ((int64_t)(path.len));
        if (len == 0) {
            return SLOP_STR(".");
        } else {
            __auto_type _mv_919 = std_strlib_last_index_of(path, SLOP_STR("/"));
            if (_mv_919.has_value) {
                __auto_type idx = _mv_919.value;
                if (idx == 0) {
                    return SLOP_STR("/");
                } else {
                    return std_strlib_substring(arena, path, 0, ((int64_t)(idx)));
                }
            } else if (!_mv_919.has_value) {
                return SLOP_STR(".");
            }
            SLOP_UNREACHABLE();
        }
    }
}

slop_string std_path_path_join(slop_arena* arena, slop_string base, slop_string rel) {
    {
        __auto_type base_len = ((int64_t)(base.len));
        __auto_type rel_len = ((int64_t)(rel.len));
        if (base_len == 0) {
            return rel;
        } else if (rel_len == 0) {
            return base;
        } else {
            {
                __auto_type slash = SLOP_STR("/");
                return string_concat(arena, base, string_concat(arena, slash, rel));
            }
        }
    }
}

slop_string std_path_path_basename(slop_arena* arena, slop_string path) {
    {
        __auto_type len = ((int64_t)(path.len));
        if (len == 0) {
            return SLOP_STR("");
        } else {
            __auto_type _mv_920 = std_strlib_last_index_of(path, SLOP_STR("/"));
            if (_mv_920.has_value) {
                __auto_type idx = _mv_920.value;
                {
                    __auto_type start = (idx + 1);
                    __auto_type remaining = (len - start);
                    if (remaining <= 0) {
                        return SLOP_STR("");
                    } else {
                        return std_strlib_substring(arena, path, ((int64_t)(SLOP_RANGE(int64_t, start, 1, 0, 0, 0, "(Int 0 ..) at path.slop:78:56"))), ((int64_t)(SLOP_RANGE(int64_t, remaining, 1, 0, 0, 0, "(Int 0 ..) at path.slop:78:80"))));
                    }
                }
            } else if (!_mv_920.has_value) {
                return path;
            }
            SLOP_UNREACHABLE();
        }
    }
}

slop_string std_path_path_extension(slop_arena* arena, slop_string path) {
    {
        __auto_type len = ((int64_t)(path.len));
        if (len == 0) {
            return SLOP_STR("");
        } else {
            __auto_type _mv_921 = std_strlib_last_index_of(path, SLOP_STR("."));
            if (_mv_921.has_value) {
                __auto_type idx = _mv_921.value;
                {
                    __auto_type ext_len = (len - idx);
                    if (ext_len <= 0) {
                        return SLOP_STR("");
                    } else {
                        return std_strlib_substring(arena, path, ((int64_t)(idx)), ((int64_t)(SLOP_RANGE(int64_t, ext_len, 1, 0, 0, 0, "(Int 0 ..) at path.slop:96:78"))));
                    }
                }
            } else if (!_mv_921.has_value) {
                return SLOP_STR("");
            }
            SLOP_UNREACHABLE();
        }
    }
}

