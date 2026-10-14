/* The other translation unit of test_intern_shared.c: it includes the
 * runtime header too, so it defines the shared globals as well. */
#include "slop_runtime.h"

slop_intern_pool** second_tu_pool(void) {
    return &slop_global_intern_pool;
}

slop_string second_tu_intern(const char* s) {
    return slop_intern_cstring(s);
}
