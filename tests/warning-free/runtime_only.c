/* Including the runtime header alone must be warning-free (#361): gcc
 * warned on noinline meeting static inline in slop_list_grow_raw. */
#include "slop_runtime.h"
int main(void) { return 0; }
