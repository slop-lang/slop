#include "../runtime/slop_runtime.h"
#include "slop_parser_cli.h"

slop_string parser_cli_argv_to_string(uint8_t** argv, int64_t index);
void parser_cli_print_json_array(slop_arena* arena, slop_list_types_SExpr_ptr exprs);
void parser_cli_print_sexp_list(slop_arena* arena, slop_list_types_SExpr_ptr exprs);
int parser_cli_main(int64_t argc, uint8_t** argv);

slop_string parser_cli_argv_to_string(uint8_t** argv, int64_t index) {
    {
        __auto_type ptr = argv[index];
        return (slop_string){.len = strlen(ptr), .data = ptr};
    }
}

void parser_cli_print_json_array(slop_arena* arena, slop_list_types_SExpr_ptr exprs) {
    {
        __auto_type len = ((int64_t)((exprs).len));
        int64_t i = 0;
        printf("%s", "[");
        while ((i < len)) {
            __auto_type _mv_51 = ({ __auto_type _lst = exprs; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_51.has_value) {
                __auto_type expr = _mv_51.value;
                if ((i > 0)) {
                    printf("%s", ",");
                }
                printf("%.*s", (int)(parser_json_print(arena, expr)).len, (parser_json_print(arena, expr)).data);
            } else if (!_mv_51.has_value) {
            }
            i = (i + 1);
        }
        printf("%s\n", "]");
    }
}

void parser_cli_print_sexp_list(slop_arena* arena, slop_list_types_SExpr_ptr exprs) {
    {
        __auto_type len = ((int64_t)((exprs).len));
        int64_t i = 0;
        while ((i < len)) {
            __auto_type _mv_52 = ({ __auto_type _lst = exprs; size_t _idx = (size_t)i; slop_option_types_SExpr_ptr _r; if (_idx < _lst.len) { _r.has_value = true; _r.value = _lst.data[_idx]; } else { _r.has_value = false; } _r; });
            if (_mv_52.has_value) {
                __auto_type expr = _mv_52.value;
                printf("%.*s\n", (int)(parser_pretty_print(arena, expr)).len, (parser_pretty_print(arena, expr)).data);
            } else if (!_mv_52.has_value) {
            }
            i = (i + 1);
        }
    }
}

int main(int64_t argc, uint8_t** argv) {
    if ((argc < 2)) {
        printf("%s\n", "Usage: slop-parser [--format sexp|json] <file.slop>");
        return 1;
    } else {
        {
            #ifdef SLOP_DEBUG
            SLOP_PRE((2097152) > 0, "with-arena size must be positive");
            #endif
            slop_arena _arena = slop_arena_new(2097152);
            #ifdef SLOP_DEBUG
            SLOP_PRE(_arena.base != NULL, "arena allocation failed");
            #endif
            slop_arena* arena = &_arena;
            {
                __auto_type format = parser_cli_OutputFormat_fmt_sexp;
                int64_t file_idx = 1;
                if (((argc >= 4) && string_eq(parser_cli_argv_to_string(argv, 1), SLOP_STR("--format")))) {
                    {
                        __auto_type fmt_arg = parser_cli_argv_to_string(argv, 2);
                        if (string_eq(fmt_arg, SLOP_STR("json"))) {
                            format = parser_cli_OutputFormat_fmt_json;
                        } else if (string_eq(fmt_arg, SLOP_STR("sexp"))) {
                            format = parser_cli_OutputFormat_fmt_sexp;
                        } else {
                            printf("%s", "Unknown format: ");
                            printf("%.*s\n", (int)(fmt_arg).len, (fmt_arg).data);
                            return 1;
                        }
                    }
                    file_idx = 3;
                }
                {
                    __auto_type path = parser_cli_argv_to_string(argv, file_idx);
                    __auto_type _mv_53 = file_file_open(path, file_FileMode_read);
                    if (!_mv_53.is_ok) {
                        __auto_type e = _mv_53.data.err;
                        printf("%s", "Error: Could not open file: ");
                        printf("%.*s\n", (int)(path).len, (path).data);
                        return 1;
                    } else if (_mv_53.is_ok) {
                        __auto_type f = _mv_53.data.ok;
                        __auto_type _mv_54 = file_file_read_all(arena, (&f));
                        if (!_mv_54.is_ok) {
                            __auto_type e = _mv_54.data.err;
                            file_file_close((&f));
                            printf("%s\n", "Error: Could not read file");
                            return 1;
                        } else if (_mv_54.is_ok) {
                            __auto_type source = _mv_54.data.ok;
                            file_file_close((&f));
                            __auto_type _mv_55 = parser_parse(arena, source);
                            if (!_mv_55.is_ok) {
                                __auto_type e = _mv_55.data.err;
                                printf("%s", "Parse error at line ");
                                printf("%lld", (long long)(e.line));
                                printf("%s", ", col ");
                                printf("%lld", (long long)(e.col));
                                printf("%s", ": ");
                                printf("%.*s\n", (int)(e.message).len, (e.message).data);
                                return 1;
                            } else if (_mv_55.is_ok) {
                                __auto_type exprs = _mv_55.data.ok;
                                if ((format == parser_cli_OutputFormat_fmt_json)) {
                                    parser_cli_print_json_array(arena, exprs);
                                    return 0;
                                } else {
                                    parser_cli_print_sexp_list(arena, exprs);
                                    return 0;
                                }
                            }
                        }
                    }
                }
            }
            slop_arena_free(arena);
        }
    }
}

