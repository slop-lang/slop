#ifndef SLOP_tester_main_H
#define SLOP_tester_main_H

#include "../runtime/slop_runtime.h"
#include <stdint.h>
#include <stdbool.h>
#include "slop_types.h"
#include "slop_tester.h"
#include <stdio.h>
#include <stdlib.h>

slop_option_string tester_main_read_file(slop_arena* arena, char* filename);
void tester_main_print_str(char* s);
void tester_main_print_string(slop_string s);
void tester_main_print_json_string(slop_string s);
slop_string tester_main_lines_to_string(slop_arena* arena, slop_list_string lines);
void tester_main_print_int(int64_t n);
int main(int64_t argc, uint8_t** argv);


#endif
