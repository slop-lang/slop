#ifndef SLOP_file_H
#define SLOP_file_H

#include "../runtime/slop_runtime.h"
#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <sys/stat.h>
#include <unistd.h>

typedef struct file_File file_File;

typedef enum {
    file_FileMode_read,
    file_FileMode_write,
    file_FileMode_append,
    file_FileMode_read_write,
    file_FileMode_write_read,
    file_FileMode_append_read
} file_FileMode;

typedef enum {
    file_FileError_not_found,
    file_FileError_permission,
    file_FileError_io_error,
    file_FileError_eof,
    file_FileError_invalid_mode,
    file_FileError_closed
} file_FileError;

struct file_File {
    void* handle;
    file_FileMode mode;
    uint8_t is_open;
};
typedef struct file_File file_File;

#ifndef SLOP_OPTION_FILE_FILE_DEFINED
#define SLOP_OPTION_FILE_FILE_DEFINED
SLOP_OPTION_DEFINE(file_File, slop_option_file_File)
#endif

#ifndef SLOP_RESULT_FILE_FILE_FILE_FILEERROR_DEFINED
#define SLOP_RESULT_FILE_FILE_FILE_FILEERROR_DEFINED
typedef struct { bool is_ok; union { file_File ok; file_FileError err; } data; } slop_result_file_File_file_FileError;
#endif

#ifndef SLOP_RESULT_U8_FILE_FILEERROR_DEFINED
#define SLOP_RESULT_U8_FILE_FILEERROR_DEFINED
typedef struct { bool is_ok; union { uint8_t ok; file_FileError err; } data; } slop_result_u8_file_FileError;
#endif

#ifndef SLOP_RESULT_BYTES_FILE_FILEERROR_DEFINED
#define SLOP_RESULT_BYTES_FILE_FILEERROR_DEFINED
typedef struct { bool is_ok; union { slop_bytes ok; file_FileError err; } data; } slop_result_bytes_file_FileError;
#endif

#ifndef SLOP_RESULT_STRING_FILE_FILEERROR_DEFINED
#define SLOP_RESULT_STRING_FILE_FILEERROR_DEFINED
typedef struct { bool is_ok; union { slop_string ok; file_FileError err; } data; } slop_result_string_file_FileError;
#endif

#ifndef SLOP_RESULT_INT_FILE_FILEERROR_DEFINED
#define SLOP_RESULT_INT_FILE_FILEERROR_DEFINED
typedef struct { bool is_ok; union { int64_t ok; file_FileError err; } data; } slop_result_int_file_FileError;
#endif

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

#ifndef SLOP_OPTION_FILE_FILE_DEFINED
#define SLOP_OPTION_FILE_FILE_DEFINED
SLOP_OPTION_DEFINE(file_File, slop_option_file_File)
#endif


#endif
