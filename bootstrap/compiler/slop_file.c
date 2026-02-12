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
        __auto_type mode_str = ((mode == file_FileMode_read) ? SLOP_STR("r") : ((mode == file_FileMode_write) ? SLOP_STR("w") : ((mode == file_FileMode_append) ? SLOP_STR("a") : ((mode == file_FileMode_read_write) ? SLOP_STR("r+") : ((mode == file_FileMode_write_read) ? SLOP_STR("w+") : SLOP_STR("a+"))))));
        {
            __auto_type handle = fopen(((uint8_t*)(path.data)), ((uint8_t*)(mode_str.data)));
            if ((handle == NULL)) {
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
        if ((result == 0)) {
            _retval = ((slop_result_u8_file_FileError){ .is_ok = true, .data.ok = 1 });
        } else {
            _retval = ((slop_result_u8_file_FileError){ .is_ok = false, .data.err = file_FileError_io_error });
        }
    }
    SLOP_POST((!((*f).is_open)), "(not (. (deref f) is-open))");
    return _retval;
}

slop_result_bytes_file_FileError file_file_read(slop_arena* arena, file_File* f, int64_t max_bytes) {
    SLOP_PRE(((*f).is_open), "(. (deref f) is-open)");
    {
        __auto_type buf = ((uint8_t*)(({ __auto_type _alloc = (uint8_t*)slop_arena_alloc(arena, max_bytes); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; })));
        {
            __auto_type bytes_read = fread(((void*)(buf)), ((uint64_t)(1)), ((uint64_t)(max_bytes)), (*f).handle);
            if (((bytes_read == 0) && (ferror((*f).handle) != 0))) {
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
            if ((result == NULL)) {
                if ((feof((*f).handle) != 0)) {
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
        __auto_type start_pos = ftell((*f).handle);
        fseek((*f).handle, ((int64_t)(0)), SEEK_END);
        {
            __auto_type size = ftell((*f).handle);
            fseek((*f).handle, start_pos, SEEK_SET);
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
        if ((ferror((*f).handle) != 0)) {
            return ((slop_result_int_file_FileError){ .is_ok = false, .data.err = file_FileError_io_error });
        } else {
            return ((slop_result_int_file_FileError){ .is_ok = true, .data.ok = ((int64_t)(written)) });
        }
    }
}

slop_result_int_file_FileError file_file_write_line(file_File* f, slop_string line) {
    SLOP_PRE(((*f).is_open), "(. (deref f) is-open)");
    {
        __auto_type written1 = fwrite(((void*)(line.data)), ((uint64_t)(1)), ((uint64_t)(line.len)), (*f).handle);
        {
            __auto_type written2 = fwrite(((void*)(SLOP_STR("\n").data)), ((uint64_t)(1)), ((uint64_t)(1)), (*f).handle);
            if ((ferror((*f).handle) != 0)) {
                return ((slop_result_int_file_FileError){ .is_ok = false, .data.err = file_FileError_io_error });
            } else {
                return ((slop_result_int_file_FileError){ .is_ok = true, .data.ok = ((int64_t)((written1 + written2))) });
            }
        }
    }
}

slop_result_u8_file_FileError file_file_flush(file_File* f) {
    SLOP_PRE(((*f).is_open), "(. (deref f) is-open)");
    {
        __auto_type result = fflush((*f).handle);
        if ((result == 0)) {
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
        __auto_type result = fseek((*f).handle, offset, whence);
        if ((result == 0)) {
            return ((slop_result_u8_file_FileError){ .is_ok = true, .data.ok = 1 });
        } else {
            return ((slop_result_u8_file_FileError){ .is_ok = false, .data.err = file_FileError_io_error });
        }
    }
}

slop_result_int_file_FileError file_file_tell(file_File* f) {
    SLOP_PRE(((*f).is_open), "(. (deref f) is-open)");
    {
        __auto_type pos = ftell((*f).handle);
        if ((pos < 0)) {
            return ((slop_result_int_file_FileError){ .is_ok = false, .data.err = file_FileError_io_error });
        } else {
            return ((slop_result_int_file_FileError){ .is_ok = true, .data.ok = pos });
        }
    }
}

uint8_t file_file_exists(slop_string path) {
    return (access(((uint8_t*)(path.data)), F_OK) == 0);
}

slop_result_int_file_FileError file_file_size(slop_string path) {
    {
        #ifdef SLOP_DEBUG
        SLOP_PRE((256) > 0, "with-arena size must be positive");
        #endif
        slop_arena _arena = slop_arena_new(256);
        #ifdef SLOP_DEBUG
        SLOP_PRE(_arena.base != NULL, "arena allocation failed");
        #endif
        slop_arena* arena = &_arena;
        {
            __auto_type buf = ({ __auto_type _alloc = (struct stat*)slop_arena_alloc(arena, sizeof(struct stat)); if (_alloc == NULL) { fprintf(stderr, "SLOP: arena alloc failed at %s:%d\n", __FILE__, __LINE__); abort(); } _alloc; });
            {
                __auto_type result = stat(((uint8_t*)(path.data)), ((void*)(buf)));
                if ((result != 0)) {
                    return ((slop_result_int_file_FileError){ .is_ok = false, .data.err = file_FileError_not_found });
                } else {
                    return ((slop_result_int_file_FileError){ .is_ok = true, .data.ok = ((int64_t)(((struct stat*)(buf))->st_size)) });
                }
            }
        }
        slop_arena_free(arena);
    }
}

