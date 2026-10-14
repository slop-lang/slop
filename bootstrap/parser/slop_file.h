#ifndef SLOP_file_H
#define SLOP_file_H

#include "../runtime/slop_runtime.h"
#ifndef SLOP_RUNTIME_ABI
#error "this module was generated for SLOP runtime ABI 2026-1 (SLOP_RUNTIME_ABI 202601), but slop_runtime.h predates runtime ABI versioning: use the slop_runtime.h of the SLOP release that generated this code"
#elif SLOP_RUNTIME_ABI != 202601
#error "this module was generated for SLOP runtime ABI 2026-1 (SLOP_RUNTIME_ABI 202601), which this slop_runtime.h does not provide (SLOP_RUNTIME_ABI differs): regenerate the C with the SLOP release that matches the runtime, or use the slop_runtime.h of the release that generated it"
#endif
#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <slop_runtime.h>

typedef struct std_file_File std_file_File;

typedef enum {
    std_file_FileMode_read,
    std_file_FileMode_write,
    std_file_FileMode_append,
    std_file_FileMode_read_write,
    std_file_FileMode_write_read,
    std_file_FileMode_append_read
} std_file_FileMode;

typedef enum {
    std_file_FileError_not_found,
    std_file_FileError_permission,
    std_file_FileError_io_error,
    std_file_FileError_eof,
    std_file_FileError_invalid_mode,
    std_file_FileError_closed
} std_file_FileError;

struct std_file_File {
    void* handle;
    std_file_FileMode mode;
    uint8_t is_open;
};
typedef struct std_file_File std_file_File;

#ifndef SLOP_OPTION_STD_FILE_FILE_DEFINED
#define SLOP_OPTION_STD_FILE_FILE_DEFINED
SLOP_OPTION_DEFINE(std_file_File, slop_option_std_file_File)
#endif

#ifndef SLOP_RESULT_STD_FILE_FILE_STD_FILE_FILEERROR_DEFINED
#define SLOP_RESULT_STD_FILE_FILE_STD_FILE_FILEERROR_DEFINED
typedef struct { bool is_ok; union { std_file_File ok; std_file_FileError err; } data; } slop_result_std_file_File_std_file_FileError;
#endif

#ifndef SLOP_RESULT_U8_STD_FILE_FILEERROR_DEFINED
#define SLOP_RESULT_U8_STD_FILE_FILEERROR_DEFINED
typedef struct { bool is_ok; union { uint8_t ok; std_file_FileError err; } data; } slop_result_u8_std_file_FileError;
#endif

#ifndef SLOP_RESULT_BYTES_STD_FILE_FILEERROR_DEFINED
#define SLOP_RESULT_BYTES_STD_FILE_FILEERROR_DEFINED
typedef struct { bool is_ok; union { slop_bytes ok; std_file_FileError err; } data; } slop_result_bytes_std_file_FileError;
#endif

#ifndef SLOP_RESULT_STRING_STD_FILE_FILEERROR_DEFINED
#define SLOP_RESULT_STRING_STD_FILE_FILEERROR_DEFINED
typedef struct { bool is_ok; union { slop_string ok; std_file_FileError err; } data; } slop_result_string_std_file_FileError;
#endif

#ifndef SLOP_RESULT_INT_STD_FILE_FILEERROR_DEFINED
#define SLOP_RESULT_INT_STD_FILE_FILEERROR_DEFINED
typedef struct { bool is_ok; union { int64_t ok; std_file_FileError err; } data; } slop_result_int_std_file_FileError;
#endif

slop_result_std_file_File_std_file_FileError std_file_file_open(slop_string path, std_file_FileMode mode);
slop_result_u8_std_file_FileError std_file_file_close(std_file_File* f);
slop_result_bytes_std_file_FileError std_file_file_read(slop_arena* arena, std_file_File* f, int64_t max_bytes);
slop_result_string_std_file_FileError std_file_file_read_line(slop_arena* arena, std_file_File* f, int64_t max_len);
slop_result_string_std_file_FileError std_file_file_read_all(slop_arena* arena, std_file_File* f);
slop_result_int_std_file_FileError std_file_file_write(std_file_File* f, slop_bytes data);
slop_result_int_std_file_FileError std_file_file_write_line(std_file_File* f, slop_string line);
slop_result_u8_std_file_FileError std_file_file_flush(std_file_File* f);
slop_result_u8_std_file_FileError std_file_file_seek(std_file_File* f, int64_t offset, int64_t whence);
slop_result_int_std_file_FileError std_file_file_tell(std_file_File* f);
uint8_t std_file_file_exists(slop_string path);
slop_result_int_std_file_FileError std_file_file_size(slop_string path);

#ifndef SLOP_OPTION_STD_FILE_FILE_DEFINED
#define SLOP_OPTION_STD_FILE_FILE_DEFINED
SLOP_OPTION_DEFINE(std_file_File, slop_option_std_file_File)
#endif


#endif
