#include "../runtime/slop_runtime.h"
#include "slop_file.h"

slop_result_file_File_file_FileError file_file_open(slop_string path, file_FileMode mode);
slop_result_u8_file_FileError file_file_close(file_File* f);
slop_result_bytes_file_FileError file_file_read(slop_arena* arena, file_File* f, int64_t max_bytes);
slop_result_string_file_FileError file_file_read_line(slop_arena* arena, file_File* f, int64_t max_len);
slop_result_string_file_FileError file_file_read_all(slop_arena* arena, file_File* f);
slop_result_int_file_FileError file_file_write(file_File* f, slop_bytes data);
slop_result_int_file_FileError file_file_write_line(file_File* f, slop_string line);
slop_result_u8_file_FileError file_file_flush(file_File* f);
slop_result_u8_file_FileError file_file_seek(file_File* f, int64_t offset, int64_t whence);
slop_result_int_file_FileError file_file_tell(file_File* f);
uint8_t file_file_exists(slop_string path);
slop_result_int_file_FileError file_file_size(slop_string path);

slop_result_file_File_file_FileError file_file_open(slop_string path, file_FileMode mode) {
    SLOP_PRE(((path.len > 0)), "(> (. path len) 0)");
    {
        __auto_type mode_str = ({ __auto_type _mv = mode; int _mi = (_mv == file_FileMode_read) ? 1 : (_mv == file_FileMode_write) ? 2 : (_mv == file_FileMode_append) ? 3 : (_mv == file_FileMode_read_write) ? 4 : (_mv == file_FileMode_write_read) ? 5 : (_mv == file_FileMode_append_read) ? 6 : 0; if (!_mi) { SLOP_UNREACHABLE(); } _mi == 1 ? (SLOP_STR("rb")) : _mi == 2 ? (SLOP_STR("wb")) : _mi == 3 ? (SLOP_STR("ab")) : _mi == 4 ? (SLOP_STR("r+b")) : _mi == 5 ? (SLOP_STR("w+b")) : (SLOP_STR("a+b")); });
        {
            __auto_type handle = fopen(((uint8_t*)(path.data)), ((uint8_t*)(mode_str.data)));
            if (handle == NULL) {
                return ((slop_result_file_File_file_FileError){ .is_ok = false, .data.err = file_FileError_not_found });
            } else {
                return ((slop_result_file_File_file_FileError){ .is_ok = true, .data.ok = (file_File){handle, mode, 1} });
            }
        }
    }
}

slop_result_u8_file_FileError file_file_close(file_File* f) {
    SLOP_PRE(((*f).is_open), "(. (deref f) is-open)");
    slop_result_u8_file_FileError _retval = {0};
    (*f).is_open = 0;
    {
        __auto_type result = fclose((*f).handle);
        if (result == 0) {
            _retval = ((slop_result_u8_file_FileError){ .is_ok = true, .data.ok = 1 });
            goto _slop_post;
        } else {
            _retval = ((slop_result_u8_file_FileError){ .is_ok = false, .data.err = file_FileError_io_error });
            goto _slop_post;
        }
    }
    _slop_post: ;
    SLOP_POST((!((*f).is_open)), "(not (. (deref f) is-open))");
    return _retval;
}

slop_result_bytes_file_FileError file_file_read(slop_arena* arena, file_File* f, int64_t max_bytes) {
    SLOP_PRE(((*f).is_open), "(. (deref f) is-open)");
    {
        __auto_type buf = ((uint8_t*)(({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, max_bytes); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })));
        {
            __auto_type bytes_read = fread(((void*)(buf)), ((uint64_t)(1)), ((uint64_t)(max_bytes)), (*f).handle);
            if ((bytes_read == 0) && (ferror((*f).handle) != 0)) {
                return ((slop_result_bytes_file_FileError){ .is_ok = false, .data.err = file_FileError_io_error });
            } else {
                return ((slop_result_bytes_file_FileError){ .is_ok = true, .data.ok = (slop_bytes){.len = bytes_read, .cap = bytes_read, .data = buf} });
            }
        }
    }
}

slop_result_string_file_FileError file_file_read_line(slop_arena* arena, file_File* f, int64_t max_len) {
    SLOP_PRE(((*f).is_open), "(. (deref f) is-open)");
    {
        __auto_type buf = ({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, (max_len + 1)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; });
        {
            __auto_type result = fgets(((uint8_t*)(buf)), ((int64_t)(max_len)), (*f).handle);
            if (result == NULL) {
                if (feof((*f).handle) != 0) {
                    return ((slop_result_string_file_FileError){ .is_ok = false, .data.err = file_FileError_eof });
                } else {
                    return ((slop_result_string_file_FileError){ .is_ok = false, .data.err = file_FileError_io_error });
                }
            } else {
                return ((slop_result_string_file_FileError){ .is_ok = true, .data.ok = string_new(arena, ((uint8_t*)(buf))) });
            }
        }
    }
}

slop_result_string_file_FileError file_file_read_all(slop_arena* arena, file_File* f) {
    SLOP_PRE(((*f).is_open), "(. (deref f) is-open)");
    {
        __auto_type start_pos = slop_ftell64((*f).handle);
        slop_fseek64((*f).handle, ((int64_t)(0)), SEEK_END);
        {
            __auto_type size = slop_ftell64((*f).handle);
            slop_fseek64((*f).handle, start_pos, SEEK_SET);
            {
                __auto_type buf = ({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, (size + 1)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; });
                {
                    __auto_type bytes_read = fread(((void*)(buf)), ((uint64_t)(1)), ((uint64_t)(size)), (*f).handle);
                    return ((slop_result_string_file_FileError){ .is_ok = true, .data.ok = (slop_string){.len = bytes_read, .data = ((uint8_t*)(buf))} });
                }
            }
        }
    }
}

slop_result_int_file_FileError file_file_write(file_File* f, slop_bytes data) {
    SLOP_PRE(((*f).is_open), "(. (deref f) is-open)");
    {
        __auto_type written = fwrite(((void*)(data.data)), ((uint64_t)(1)), ((uint64_t)(data.len)), (*f).handle);
        if (ferror((*f).handle) != 0) {
            return ((slop_result_int_file_FileError){ .is_ok = false, .data.err = file_FileError_io_error });
        } else {
            return ((slop_result_int_file_FileError){ .is_ok = true, .data.ok = ((int64_t)(SLOP_RANGE(int64_t, written, 1, 0, 0, 0, "(Int 0 ..) at file.slop:171:30"))) });
        }
    }
}

slop_result_int_file_FileError file_file_write_line(file_File* f, slop_string line) {
    SLOP_PRE(((*f).is_open), "(. (deref f) is-open)");
    {
        __auto_type written1 = fwrite(((void*)(line.data)), ((uint64_t)(1)), ((uint64_t)(line.len)), (*f).handle);
        {
            __auto_type written2 = fwrite(((void*)(SLOP_STR("\n").data)), ((uint64_t)(1)), ((uint64_t)(1)), (*f).handle);
            if (ferror((*f).handle) != 0) {
                return ((slop_result_int_file_FileError){ .is_ok = false, .data.err = file_FileError_io_error });
            } else {
                return ((slop_result_int_file_FileError){ .is_ok = true, .data.ok = ((int64_t)(SLOP_RANGE(int64_t, (written1 + written2), 1, 0, 0, 0, "(Int 0 ..) at file.slop:182:32"))) });
            }
        }
    }
}

slop_result_u8_file_FileError file_file_flush(file_File* f) {
    SLOP_PRE(((*f).is_open), "(. (deref f) is-open)");
    {
        __auto_type result = fflush((*f).handle);
        if (result == 0) {
            return ((slop_result_u8_file_FileError){ .is_ok = true, .data.ok = 1 });
        } else {
            return ((slop_result_u8_file_FileError){ .is_ok = false, .data.err = file_FileError_io_error });
        }
    }
}

slop_result_u8_file_FileError file_file_seek(file_File* f, int64_t offset, int64_t whence) {
    SLOP_PRE(((*f).is_open), "(. (deref f) is-open)");
    SLOP_PRE((((whence >= 0) && (whence <= 2))), "(and (>= whence 0) (<= whence 2))");
    {
        __auto_type result = slop_fseek64((*f).handle, offset, whence);
        if (result == 0) {
            return ((slop_result_u8_file_FileError){ .is_ok = true, .data.ok = 1 });
        } else {
            return ((slop_result_u8_file_FileError){ .is_ok = false, .data.err = file_FileError_io_error });
        }
    }
}

slop_result_int_file_FileError file_file_tell(file_File* f) {
    SLOP_PRE(((*f).is_open), "(. (deref f) is-open)");
    {
        __auto_type pos = slop_ftell64((*f).handle);
        if (pos < 0) {
            return ((slop_result_int_file_FileError){ .is_ok = false, .data.err = file_FileError_io_error });
        } else {
            return ((slop_result_int_file_FileError){ .is_ok = true, .data.ok = pos });
        }
    }
}

uint8_t file_file_exists(slop_string path) {
    return slop_file_exists(((uint8_t*)(path.data)));
}

slop_result_int_file_FileError file_file_size(slop_string path) {
    {
        __auto_type size = slop_file_size(((uint8_t*)(path.data)));
        if (size < 0) {
            return ((slop_result_int_file_FileError){ .is_ok = false, .data.err = file_FileError_not_found });
        } else {
            return ((slop_result_int_file_FileError){ .is_ok = true, .data.ok = size });
        }
    }
}

