/*
 * SLOP Runtime - Minimal runtime for SLOP-generated C code
 * 
 * Provides:
 * - Arena allocator
 * - String type
 * - List type
 * - Map type
 * - Contract macros
 */

#ifndef SLOP_RUNTIME_H
#define SLOP_RUNTIME_H

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdatomic.h>

#ifdef SLOP_INTERN_THREADSAFE
#include <pthread.h>
#endif

/* ============================================================
 * Configuration
 * ============================================================ */

#ifndef SLOP_ARENA_DEFAULT_SIZE
#define SLOP_ARENA_DEFAULT_SIZE 4096
#endif

#ifndef SLOP_MAP_INITIAL_CAPACITY
#define SLOP_MAP_INITIAL_CAPACITY 16
#endif

#ifndef SLOP_ARENA_MAX_TOTAL_BYTES
#define SLOP_ARENA_MAX_TOTAL_BYTES (256UL * 1024UL * 1024UL)  /* 256 MB */
#endif

/* Global allocation tracking across all arenas (atomic for thread safety).
 * Weak attribute ensures linker merges all TU definitions into one symbol. */
_Atomic size_t slop_global_allocated __attribute__((weak)) = 0;

/* ============================================================
 * Contracts
 * ============================================================ */

#ifdef SLOP_DEBUG
    #define SLOP_PRE(cond, msg) \
        do { if (!(cond)) { \
            fprintf(stderr, "SLOP precondition failed: %s\n  at %s:%d\n", \
                    msg, __FILE__, __LINE__); \
            abort(); \
        }} while(0)
    
    #define SLOP_POST(cond, msg) \
        do { if (!(cond)) { \
            fprintf(stderr, "SLOP postcondition failed: %s\n  at %s:%d\n", \
                    msg, __FILE__, __LINE__); \
            abort(); \
        }} while(0)
    
    #define SLOP_ASSERT(cond, msg) \
        do { if (!(cond)) { \
            fprintf(stderr, "SLOP assertion failed: %s\n  at %s:%d\n", \
                    msg, __FILE__, __LINE__); \
            abort(); \
        }} while(0)
#else
    #define SLOP_PRE(cond, msg) ((void)0)
    #define SLOP_POST(cond, msg) ((void)0)
    #define SLOP_ASSERT(cond, msg) ((void)0)
#endif

/* Reached when a match in return position matched none of its arms.
 *
 * Deliberately NOT gated on SLOP_DEBUG, unlike the contracts above. The checker
 * warns about a non-exhaustive match but does not yet reject one, so this path is
 * genuinely reachable -- and __builtin_unreachable() on a path that actually runs
 * licenses the optimiser to do considerably worse than the fall-off-the-end this
 * replaces. One cold branch at the tail of a match is the cheaper mistake.
 *
 * Emitted AFTER the closed if-chain or switch rather than as a final else/default,
 * so -Wswitch still fires on a missing enum case. */
#define SLOP_UNREACHABLE() \
    do { \
        fprintf(stderr, "SLOP: non-exhaustive match reached\n  at %s:%d\n", \
                __FILE__, __LINE__); \
        abort(); \
    } while(0)

/* Expression-form range check - returns value after checking bounds.
 * Unlike SLOP_PRE, this can be used in expression contexts like return statements. */
#ifdef SLOP_DEBUG
    #define SLOP_RANGE_CHECK(val, cond, msg) \
        ({ __auto_type _v = (val); \
           if (!(cond)) { \
               fprintf(stderr, "SLOP range check failed: %s\n  at %s:%d\n", \
                       msg, __FILE__, __LINE__); \
               abort(); \
           } \
           _v; })
#else
    #define SLOP_RANGE_CHECK(val, cond, msg) (val)
#endif

/* ============================================================
 * Arena Allocator
 * ============================================================ */

typedef struct slop_arena {
    uint8_t* base;
    size_t offset;
    size_t capacity;
    size_t total_allocated;   /* Total bytes across all arenas in chain */
    struct slop_arena* next;  /* For overflow arenas */
} slop_arena;

/* ============================================================
 * String Interning Pool
 * ============================================================ */

#ifndef SLOP_INTERN_BUCKET_COUNT
#define SLOP_INTERN_BUCKET_COUNT 4096
#endif

/* Forward declare slop_string for intern pool */
struct slop_string_fwd;

typedef struct slop_intern_entry {
    uint64_t hash;
    size_t len;
    const char* data;
    struct slop_intern_entry* next;
} slop_intern_entry;

typedef struct {
    slop_intern_entry** buckets;
    size_t bucket_count;
    size_t entry_count;
    slop_arena* arena;  /* Pool owns its own arena */
#ifdef SLOP_INTERN_THREADSAFE
    pthread_mutex_t lock;
#endif
} slop_intern_pool;

static slop_intern_pool* slop_global_intern_pool = NULL;

static inline slop_arena slop_arena_new(size_t capacity) {
    /* Check global cap BEFORE allocating (atomic load for thread safety) */
#ifndef SLOP_ARENA_NO_CAP
    if (atomic_load(&slop_global_allocated) + capacity > SLOP_ARENA_MAX_TOTAL_BYTES) {
        fprintf(stderr, "SLOP: arena allocation cap exceeded (%zu bytes). "
                "Increase SLOP_ARENA_MAX_TOTAL_BYTES or reduce allocation.\n",
                (size_t)SLOP_ARENA_MAX_TOTAL_BYTES);
        abort();
    }
#endif

    slop_arena arena;
    arena.base = (uint8_t*)malloc(capacity);
    arena.offset = 0;
    arena.capacity = (arena.base != NULL) ? capacity : 0;
    arena.total_allocated = arena.capacity;  /* Keep for per-chain tracking */
    arena.next = NULL;

    if (arena.base != NULL) {
        atomic_fetch_add(&slop_global_allocated, capacity);  /* Track globally */
    }
    return arena;
}

static inline void* slop_arena_alloc(slop_arena* arena, size_t size) {
    /* Handle failed arena */
    if (arena->base == NULL) return NULL;

    /* Align to 8 bytes */
    size = (size + 7) & ~7;

    /* Check if we need overflow arena */
    if (arena->offset + size > arena->capacity) {
        if (arena->next == NULL) {
            size_t new_cap = arena->capacity * 2;
            if (new_cap < size) new_cap = size * 2;

            /* Check GLOBAL cap before allocating overflow (atomic load for thread safety) */
#ifndef SLOP_ARENA_NO_CAP
            if (atomic_load(&slop_global_allocated) + new_cap > SLOP_ARENA_MAX_TOTAL_BYTES) {
                fprintf(stderr, "SLOP: arena allocation cap exceeded (%zu bytes). "
                        "Increase SLOP_ARENA_MAX_TOTAL_BYTES or reduce allocation.\n",
                        (size_t)SLOP_ARENA_MAX_TOTAL_BYTES);
                abort();
            }
#endif

            arena->next = (slop_arena*)malloc(sizeof(slop_arena));
            if (arena->next == NULL) {
                fprintf(stderr, "SLOP: arena overflow malloc failed (requested %zu bytes).\n", sizeof(slop_arena));
                abort();
            }

            /* Create overflow arena (slop_arena_new will increment global counter) */
            *arena->next = slop_arena_new(new_cap);
            if (arena->next->base == NULL) {
                fprintf(stderr, "SLOP: arena block malloc failed (requested %zu bytes).\n", new_cap);
                free(arena->next);
                arena->next = NULL;
                abort();
            }

            /* Propagate per-chain total */
            arena->next->total_allocated = arena->total_allocated + new_cap;
        }
        return slop_arena_alloc(arena->next, size);
    }

    void* ptr = arena->base + arena->offset;
    arena->offset += size;
    return ptr;
}

/* Grow the allocation at ptr from old_size to new_size bytes where it stands,
 * when it is the last allocation in its block of this arena's chain and the
 * block has room: a bump-pointer realloc. Returns false, changing nothing,
 * otherwise -- including when ptr is not in this arena at all, so storage is
 * only ever extended inside the arena the caller names. The bytes past
 * old_size are unused block space and are not cleared. */
static inline bool slop_arena_try_extend(slop_arena* arena, void* ptr,
                                         size_t old_size, size_t new_size) {
    old_size = (old_size + 7) & ~(size_t)7;
    new_size = (new_size + 7) & ~(size_t)7;
    uint8_t* p = (uint8_t*)ptr;
    for (slop_arena* a = arena; a != NULL; a = a->next) {
        if (a->base == NULL || p < a->base || p >= a->base + a->capacity) continue;
        if (p + old_size != a->base + a->offset) return false;
        if ((size_t)(p - a->base) + new_size > a->capacity) return false;
        a->offset = (size_t)(p - a->base) + new_size;
        return true;
    }
    return false;
}

/* Resize the allocation at ptr to new_size bytes when it is the ONLY
 * allocation in its block of this arena's chain, by realloc'ing the block
 * itself: the old storage goes back to the allocator instead of lying
 * abandoned in the arena. Returns the (possibly moved) allocation, or NULL,
 * changing nothing, when ptr shares its block, is not in this arena, or the
 * realloc fails. On success the old address is dead, so this is only for
 * storage with exactly one owner pointer -- a map's table, held only by its
 * slop_map -- and never for a List's buffer, which every copy of the list
 * header points at. */
static inline void* slop_arena_realloc_sole(slop_arena* arena, void* ptr,
                                            size_t old_size, size_t new_size) {
    old_size = (old_size + 7) & ~(size_t)7;
    new_size = (new_size + 7) & ~(size_t)7;
    uint8_t* p = (uint8_t*)ptr;
    for (slop_arena* a = arena; a != NULL; a = a->next) {
        if (a->base == NULL || p < a->base || p >= a->base + a->capacity) continue;
        if (p != a->base || a->offset != old_size) return NULL;
        if (new_size <= a->capacity) {
            a->offset = new_size;
            return p;
        }
#ifndef SLOP_ARENA_NO_CAP
        if (atomic_load(&slop_global_allocated) + (new_size - a->capacity) > SLOP_ARENA_MAX_TOTAL_BYTES) {
            fprintf(stderr, "SLOP: arena allocation cap exceeded (%zu bytes). "
                    "Increase SLOP_ARENA_MAX_TOTAL_BYTES or reduce allocation.\n",
                    (size_t)SLOP_ARENA_MAX_TOTAL_BYTES);
            abort();
        }
#endif
        uint8_t* nb = (uint8_t*)realloc(a->base, new_size);
        if (nb == NULL) return NULL;
        atomic_fetch_add(&slop_global_allocated, new_size - a->capacity);
        a->total_allocated += new_size - a->capacity;
        a->base = nb;
        a->capacity = new_size;
        a->offset = new_size;
        return nb;
    }
    return NULL;
}

static inline void slop_arena_free(slop_arena* arena) {
    if (arena->next) {
        slop_arena_free(arena->next);
        free(arena->next);
        arena->next = NULL;
    }

    /* Decrement global counter (atomic for thread safety) */
    if (arena->base != NULL && arena->capacity > 0) {
        atomic_fetch_sub(&slop_global_allocated, arena->capacity);
    }

    free(arena->base);
    arena->base = NULL;
    arena->offset = 0;
    arena->capacity = 0;
    arena->total_allocated = 0;
}

static inline void slop_arena_reset(slop_arena* arena) {
    arena->offset = 0;
    if (arena->next) {
        slop_arena_free(arena->next);
        free(arena->next);
        arena->next = NULL;
    }
    arena->total_allocated = arena->capacity;
}

/* ============================================================
 * String Type (immutable, length-prefixed)
 * ============================================================ */

typedef struct {
    size_t len;
    const char* data;
} slop_string;

#define SLOP_STR(literal) ((slop_string){sizeof(literal)-1, literal})

/* String constructor macro for native transpiler: String(data, len) -> slop_string */
#define String(data, len) ((slop_string){(len), (const char*)(data)})

/* Generic Option constructors for native transpiler */
/* These use anonymous struct literals compatible with slop_option types */
typedef struct { bool has_value; int64_t value; } _slop_option_generic;
#define some(v) ((_slop_option_generic){true, (int64_t)(v)})
#define none ((_slop_option_generic){false, 0})
/* Generic unwrap for any Option type */
#define unwrap(opt) ({ __auto_type _opt = (opt); SLOP_PRE(_opt.has_value, "unwrap on None"); _opt.value; })

/* Generic Result type for native transpiler */
/* ok/error constructors produce generic result that can be assigned to typed results */
typedef struct { bool is_ok; union { int64_t ok; int64_t err; } data; } _slop_result_generic;
#define ok(v) ((_slop_result_generic){true, {.ok = (int64_t)(v)}})
#define error(e) ((_slop_result_generic){false, {.err = (int64_t)(e)}})

/* Closure type for lambda expressions with captured variables */
typedef struct { void* fn; void* env; } slop_closure_t;

/* ============================================================
 * String Interning Functions
 * ============================================================ */

/* Byte-string hash: 8 bytes per step, after xxHash64's per-lane round and
 * avalanche. It is a pure function of the bytes -- no seed, no addresses, and
 * words are read little-endian on every host -- so a given key hashes the
 * same across runs and platforms, and Map/Set iteration order with it. */
#define SLOP_HASH_P1 0x9E3779B185EBCA87ULL
#define SLOP_HASH_P2 0xC2B2AE3D27D4EB4FULL
#define SLOP_HASH_P3 0x165667B19E3779F9ULL
#define SLOP_HASH_P4 0x85EBCA77C2B2AE63ULL

static inline uint64_t slop_hash_rotl(uint64_t x, int r) {
    return (x << r) | (x >> (64 - r));
}

static inline uint64_t slop_hash_load64(const uint8_t* p) {
    uint64_t w;
    memcpy(&w, p, sizeof(w));
#if defined(__BYTE_ORDER__) && __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
    w = __builtin_bswap64(w);
#endif
    return w;
}

static inline uint64_t slop_hash_word(uint64_t h, uint64_t w) {
    h ^= slop_hash_rotl(w * SLOP_HASH_P2, 31) * SLOP_HASH_P1;
    return slop_hash_rotl(h, 27) * SLOP_HASH_P1 + SLOP_HASH_P4;
}

static inline uint64_t slop_hash_avalanche(uint64_t h) {
    h ^= h >> 33;
    h *= SLOP_HASH_P2;
    h ^= h >> 29;
    h *= SLOP_HASH_P3;
    h ^= h >> 32;
    return h;
}

static inline uint64_t slop_hash_bytes(const void* data, size_t len) {
    const uint8_t* p = (const uint8_t*)data;
    uint64_t h = SLOP_HASH_P3 ^ ((uint64_t)len * SLOP_HASH_P1);
    while (len >= 8) {
        h = slop_hash_word(h, slop_hash_load64(p));
        p += 8;
        len -= 8;
    }
    if (len > 0) {
        /* Assembled byte by byte, so the tail is little-endian everywhere too. */
        uint64_t w = 0;
        for (size_t i = 0; i < len; i++) w |= (uint64_t)p[i] << (8 * i);
        h = slop_hash_word(h, w);
    }
    return slop_hash_avalanche(h);
}

/* Fold one more 64-bit hash into a running one (generated hash functions
 * use it to combine a tag with a payload hash). */
static inline uint64_t slop_hash_combine(uint64_t h, uint64_t v) {
    return slop_hash_word(h, v);
}

/* Hash for raw string data (used by interning) */
static inline uint64_t slop_hash_string_data(const char* str, size_t len) {
    return slop_hash_bytes(str, len);
}

/* Initialize the global intern pool (called lazily) */
#ifdef SLOP_INTERN_THREADSAFE
static pthread_once_t slop_intern_once = PTHREAD_ONCE_INIT;
static void slop_intern_pool_init_impl(void) {
    slop_global_intern_pool = (slop_intern_pool*)malloc(sizeof(slop_intern_pool));
    slop_global_intern_pool->bucket_count = SLOP_INTERN_BUCKET_COUNT;
    slop_global_intern_pool->entry_count = 0;
    slop_global_intern_pool->buckets = (slop_intern_entry**)calloc(
        SLOP_INTERN_BUCKET_COUNT, sizeof(slop_intern_entry*));
    slop_global_intern_pool->arena = (slop_arena*)malloc(sizeof(slop_arena));
    *slop_global_intern_pool->arena = slop_arena_new(1024 * 1024);
    pthread_mutex_init(&slop_global_intern_pool->lock, NULL);
}
static inline void slop_intern_pool_init(void) {
    pthread_once(&slop_intern_once, slop_intern_pool_init_impl);
}
#else
static inline void slop_intern_pool_init(void) {
    if (slop_global_intern_pool) return;

    slop_global_intern_pool = (slop_intern_pool*)malloc(sizeof(slop_intern_pool));
    slop_global_intern_pool->bucket_count = SLOP_INTERN_BUCKET_COUNT;
    slop_global_intern_pool->entry_count = 0;
    slop_global_intern_pool->buckets = (slop_intern_entry**)calloc(
        SLOP_INTERN_BUCKET_COUNT, sizeof(slop_intern_entry*));

    /* Create dedicated arena for interned strings */
    slop_global_intern_pool->arena = (slop_arena*)malloc(sizeof(slop_arena));
    *slop_global_intern_pool->arena = slop_arena_new(1024 * 1024);  /* 1MB initial */
}
#endif

/* Intern a string - returns existing string if already interned, otherwise allocates new */
static inline slop_string slop_intern_string(const char* str, size_t len) {
    slop_intern_pool_init();

    uint64_t hash = slop_hash_string_data(str, len);
    size_t bucket = hash % slop_global_intern_pool->bucket_count;

#ifdef SLOP_INTERN_THREADSAFE
    pthread_mutex_lock(&slop_global_intern_pool->lock);
#endif

    /* Check existing entries */
    slop_intern_entry* entry = slop_global_intern_pool->buckets[bucket];
    while (entry) {
        if (entry->hash == hash &&
            entry->len == len &&
            memcmp(entry->data, str, len) == 0) {
            /* Found existing - return it */
#ifdef SLOP_INTERN_THREADSAFE
            pthread_mutex_unlock(&slop_global_intern_pool->lock);
#endif
            return (slop_string){entry->len, entry->data};
        }
        entry = entry->next;
    }

    /* Allocate new interned string in pool's arena */
    char* data = (char*)slop_arena_alloc(slop_global_intern_pool->arena, len + 1);
    memcpy(data, str, len);
    data[len] = '\0';

    /* Add entry to pool */
    slop_intern_entry* new_entry = (slop_intern_entry*)slop_arena_alloc(
        slop_global_intern_pool->arena, sizeof(slop_intern_entry));
    new_entry->hash = hash;
    new_entry->len = len;
    new_entry->data = data;
    new_entry->next = slop_global_intern_pool->buckets[bucket];
    slop_global_intern_pool->buckets[bucket] = new_entry;
    slop_global_intern_pool->entry_count++;

#ifdef SLOP_INTERN_THREADSAFE
    pthread_mutex_unlock(&slop_global_intern_pool->lock);
#endif
    return (slop_string){len, data};
}

/* Intern a null-terminated string */
static inline slop_string slop_intern_cstring(const char* str) {
    return slop_intern_string(str, strlen(str));
}

/* Interning version of string_new - use for strings that will be compared often */
static inline slop_string slop_string_intern(slop_arena* arena, const char* cstr) {
    (void)arena;  /* Interned strings use global pool, not passed arena */
    return slop_intern_cstring(cstr);
}

/* ============================================================
 * String Construction Functions
 * ============================================================ */

/* String interning mode - set to 1 to enable global interning for all strings */
#ifndef SLOP_STRING_INTERN_ALL
#define SLOP_STRING_INTERN_ALL 1
#endif

static inline slop_string slop_string_new(slop_arena* arena, const char* cstr) {
#if SLOP_STRING_INTERN_ALL
    (void)arena;  /* Interned strings use global pool */
    return slop_intern_cstring(cstr);
#else
    size_t len = strlen(cstr);
    char* data = (char*)slop_arena_alloc(arena, len + 1);
    memcpy(data, cstr, len + 1);
    return (slop_string){len, data};
#endif
}

static inline slop_string string_new(slop_arena* arena, const char* cstr) {
    return slop_string_new(arena, cstr);
}

static inline slop_string slop_string_new_len(slop_arena* arena, const char* src, size_t len) {
#if SLOP_STRING_INTERN_ALL
    (void)arena;  /* Interned strings use global pool */
    return slop_intern_string(src, len);
#else
    char* data = (char*)slop_arena_alloc(arena, len + 1);
    memcpy(data, src, len);
    data[len] = '\0';
    return (slop_string){len, data};
#endif
}

static inline bool slop_string_eq(slop_string a, slop_string b) {
    if (a.len != b.len) return false;
    /* Interned strings (SLOP_STRING_INTERN_ALL) that are equal share storage. */
    if (a.data == b.data) return true;
    return memcmp(a.data, b.data, a.len) == 0;
}

static inline slop_string slop_string_concat(slop_arena* arena, slop_string a, slop_string b) {
    size_t len = a.len + b.len;
    char* data = (char*)slop_arena_alloc(arena, len + 1);
    memcpy(data, a.data, a.len);
    memcpy(data + a.len, b.data, b.len);
    data[len] = '\0';
    return (slop_string){len, data};
}

static inline slop_string slop_string_push_char(slop_arena* arena, slop_string s, uint8_t c) {
    size_t len = s.len + 1;
    char* data = (char*)slop_arena_alloc(arena, len + 1);
    memcpy(data, s.data, s.len);
    data[s.len] = (char)c;
    data[len] = '\0';
    return (slop_string){len, data};
}

static inline slop_string slop_string_slice(slop_string s, size_t start, size_t end) {
    SLOP_PRE(start <= end && end <= s.len, "valid slice bounds");
    return (slop_string){end - start, s.data + start};
}

static inline size_t string_len(slop_string s) {
    return s.len;
}

static inline int32_t string_char_at(slop_string s, size_t index) {
    if (index >= s.len) return 0;
    return (int32_t)(unsigned char)s.data[index];
}

static inline slop_string string_slice(slop_string s, size_t start, size_t end) {
    return slop_string_slice(s, start, end);
}

static inline int64_t string_to_int(slop_string s) {
    int64_t result = 0;
    int negative = 0;
    size_t i = 0;
    if (s.len > 0 && s.data[0] == '-') {
        negative = 1;
        i = 1;
    }
    for (; i < s.len; i++) {
        if (s.data[i] >= '0' && s.data[i] <= '9') {
            result = result * 10 + (s.data[i] - '0');
        }
    }
    return negative ? -result : result;
}

static inline slop_string int_to_string(slop_arena* arena, int64_t n) {
    char buf[32];
    int len = snprintf(buf, sizeof(buf), "%ld", (long)n);
    return slop_string_new_len(arena, buf, len);
}

static inline slop_string string_concat(slop_arena* arena, slop_string a, slop_string b) {
    return slop_string_concat(arena, a, b);
}

static inline bool string_eq(slop_string a, slop_string b) {
    return slop_string_eq(a, b);
}

/* ============================================================
 * Bytes Type (mutable, length + capacity)
 * ============================================================ */

typedef struct {
    size_t len;
    size_t cap;
    uint8_t* data;
} slop_bytes;

static inline slop_bytes slop_bytes_new(slop_arena* arena, size_t capacity) {
    uint8_t* data = (uint8_t*)slop_arena_alloc(arena, capacity);
    return (slop_bytes){0, capacity, data};
}

static inline slop_bytes slop_bytes_from(slop_arena* arena, const uint8_t* src, size_t len) {
    uint8_t* data = (uint8_t*)slop_arena_alloc(arena, len);
    memcpy(data, src, len);
    return (slop_bytes){len, len, data};
}

/* ============================================================
 * List Type (dynamic array, generic via macros)
 * ============================================================ */

#ifndef SLOP_LIST_FIRST_CAPACITY
#define SLOP_LIST_FIRST_CAPACITY 4
#endif

/* Make room for one more element in a list whose len has reached its cap:
 * the capacity doubles (a list with no storage gets SLOP_LIST_FIRST_CAPACITY),
 * a new buffer is allocated in `arena`, the first len elements are copied, and
 * the new data pointer is returned. Every list-push, generated or
 * SLOP_LIST_IMPL's, grows through here.
 *
 * The buffer always moves, even when it is the last allocation in its block
 * and could be extended where it stands (slop_arena_try_extend, as a map's
 * table is). A List header is a value, and every copy of it -- a `mut`
 * parameter, a record read out of a map -- points at the same buffer. Moving
 * on growth is what separates a copy that outgrew its capacity from the
 * others: were it extended in place, another header with spare capacity would
 * still write into the grown copy's elements. The old buffer stays in the
 * arena, so any copy of the old header still reads it. */
static inline void* slop_list_grow_raw(slop_arena* arena, void* data, size_t* cap,
                                       size_t len, size_t elem_size) {
    size_t new_cap = *cap == 0 ? SLOP_LIST_FIRST_CAPACITY : *cap * 2;
    void* new_data = slop_arena_alloc(arena, new_cap * elem_size);
    if (new_data == NULL) {
        fprintf(stderr, "SLOP: list growth failed (arena has no storage)\n");
        abort();
    }
    if (len > 0) memcpy(new_data, data, len * elem_size);
    *cap = new_cap;
    return new_data;
}

/* SLOP_LIST_DECLARE: struct only — safe with incomplete element types (uses T*) */
#define SLOP_LIST_DECLARE(T, Name) \
    typedef struct { \
        size_t len; \
        size_t cap; \
        T* data; \
    } Name;

/* SLOP_LIST_IMPL: inline functions — requires sizeof(T), so T must be complete */
#define SLOP_LIST_IMPL(T, Name) \
    static inline Name Name##_new(slop_arena* arena, size_t initial_cap) { \
        T* data = (T*)slop_arena_alloc(arena, initial_cap * sizeof(T)); \
        return (Name){0, initial_cap, data}; \
    } \
    \
    /* An empty list may have no storage yet ({NULL, 0, 0}, as list-new \
     * creates it): slop_list_grow_raw gives it its first buffer. */ \
    static inline void Name##_push(slop_arena* arena, Name* list, T item) { \
        if (list->len >= list->cap) { \
            list->data = (T*)slop_list_grow_raw(arena, list->data, &list->cap, \
                                                list->len, sizeof(T)); \
        } \
        list->data[list->len++] = item; \
    } \
    \
    static inline T* Name##_get(Name* list, size_t i) { \
        SLOP_PRE(i < list->len, "list index in bounds"); \
        return &list->data[i]; \
    } \
    \
    static inline bool Name##_set(Name* list, size_t i, T item) { \
        if (i >= list->len) { return false; } \
        list->data[i] = item; \
        return true; \
    }

/* SLOP_LIST_DEFINE: combined declare + impl (original convenience macro) */
#define SLOP_LIST_DEFINE(T, Name) SLOP_LIST_DECLARE(T, Name) SLOP_LIST_IMPL(T, Name)

/* Pre-define common list types */
SLOP_LIST_DEFINE(int64_t, slop_list_int)
SLOP_LIST_DEFINE(double, slop_list_float)
SLOP_LIST_DEFINE(slop_string, slop_list_string)
SLOP_LIST_DEFINE(void*, slop_list_ptr)

/* String split - splits string on single-char delimiter */
static inline slop_list_string string_split(slop_arena* arena, slop_string s, slop_string delim) {
    SLOP_PRE(delim.len == 1, "delimiter must be single character");
    char dc = delim.data[0];

    /* Count segments */
    size_t count = 1;
    for (size_t i = 0; i < s.len; i++) {
        if (s.data[i] == dc) count++;
    }

    slop_list_string result = slop_list_string_new(arena, count);

    size_t start = 0;
    for (size_t i = 0; i <= s.len; i++) {
        if (i == s.len || s.data[i] == dc) {
            slop_string seg = slop_string_new_len(arena, s.data + start, i - start);
            slop_list_string_push(arena, &result, seg);
            start = i + 1;
        }
    }
    return result;
}

/* ============================================================
 * Map and Set (one hash table; a Set is a Map with no value)
 *
 * LAYOUT. A map is a slop_map header -- allocated once and shared by
 * pointer, which is why a Map or Set in a record field is shared by every
 * copy of the record -- whose `table` is ONE arena block:
 *
 *   [entry 0][entry 1] ... [entry cap-1]   dense, entries 0..len-1 live
 *   [slot][slot] ... [slot]                2*cap index slots
 *
 * An entry is the key's bytes, then the value's (none for a Set), then, for
 * keys whose eq is costly, the key's mixed 64-bit hash: [key][pad][value]
 * [hash]. Offsets and sizes come from the map's slop_map_desc, a static
 * constant the transpiler emits per key/value type. An index slot holds an
 * entry number plus one, 0 meaning empty, and above it a few bits of the
 * key's hash, in 1, 2, 4 or 8 bytes as cap requires; the index is
 * linear-probed from slop_map_mix(hash) and is never more than half full, so
 * probe chains stay short, and the hash bits let a probe skip another key's
 * slot without reading its entry.
 *
 * WHY INLINE AND DENSE. Keys and values live in the table, so a put
 * allocates nothing per entry: a new key is copied into entries[len], and an
 * overwrite copies the value over the old one where it stands. Storing a
 * pointer per key or value instead cost HOWL, an OWL reasoner whose store is
 * millions of Set and Map entries, ~150 bytes per element (a 32-byte padded
 * slot at 37-75% load, an arena copy of each key, and a fresh copy of the
 * value on every put, overwrites included), where this layout costs the entry
 * plus a few bytes of index. Entries are dense rather than scattered through
 * the probe table so that an empty slot costs an index slot, not a whole
 * key and value: a large value is no dearer per element than its own size.
 * Do not reintroduce a per-entry slop_arena_alloc.
 *
 * RULES.
 * - Nothing may keep a pointer into the table across a put or a remove: a
 *   put can move the whole table, a remove moves the last entry into the
 *   hole. Generated code copies a key or value out the moment it reads one
 *   (map-get builds an Option by value, for-each binds copies).
 * - Growth doubles cap when a put finds len == cap. It extends the block in
 *   place when the block is the last allocation in its block of the put-site
 *   arena (slop_arena_try_extend); reallocs the arena block when the table is
 *   its only allocation (slop_arena_realloc_sole), which frees the old
 *   storage; and otherwise moves the table into the put-site arena, abandoning
 *   one old block. Every way the index is rebuilt from the entries in order,
 *   so the layout, and iteration order with it, is the same. Growth goes only
 *   to the arena named at the put site. (A List never grows in place: see
 *   slop_list_grow_raw.)
 * - Iteration is entries 0..len-1: insertion order, except that a remove
 *   moves the last entry into the hole. So order is a pure function of the
 *   operations and the keys (even for Ptr keys). The language promises only
 *   that it is deterministic.
 * - Reads (get, has, iteration) never write, so any number of threads may read
 *   a map nobody is changing. There is no locking.
 * ============================================================ */

/* Function pointer types for hash and equality */
typedef uint64_t (*slop_hash_fn)(const void* key);
typedef bool (*slop_eq_fn)(const void* a, const void* b);

/* How a probe decides that an entry holds the key it is looking for */
typedef enum {
    SLOP_KEY_BITS = 0,    /* key bytes compared directly; no stored hash (integers, Bool,
                             Symbol, Ptr, ranges) */
    SLOP_KEY_CALL = 1,    /* eq called; no stored hash (Float and F32, whose -0.0 == 0.0) */
    SLOP_KEY_HASHED = 2   /* stored hash compared first, then eq (String, and every type
                             with a generated hash: records, unions, enums, Option, Result) */
} slop_key_mode;

typedef struct slop_map_desc {
    slop_hash_fn hash;
    slop_eq_fn eq;
    uint32_t key_size;
    uint32_t value_size;  /* 0 for a Set */
    uint32_t value_off;   /* offset of the value in an entry */
    uint32_t hash_off;    /* offset of the stored hash, when mode is SLOP_KEY_HASHED */
    uint32_t entry_size;  /* a multiple of the entry's alignment */
    uint32_t mode;        /* slop_key_mode */
} slop_map_desc;

typedef struct slop_map {
    size_t len;
    size_t cap;           /* entry capacity: 0 (no table yet) or a power of two */
    const slop_map_desc* desc;
    uint8_t* table;       /* NULL while cap is 0 */
} slop_map;

/* A key or value is aligned to at most 8, the arena's alignment; the
 * negative array size is a compile error for a wider one. */
#define SLOP_MAP_ALIGN_OK(T) (0 * sizeof(char[_Alignof(T) <= 8 ? 1 : -1]))
#define SLOP_MAP_ROUND(n, a) ((((n) + (a) - 1) / (a)) * (a))
#define SLOP_MAP_MAX(a, b) ((a) > (b) ? (a) : (b))

#ifdef SLOP_MAP_FORCE_KEY_MODE
#define SLOP_MAP_MODE(MODE) (SLOP_MAP_FORCE_KEY_MODE)
#else
#define SLOP_MAP_MODE(MODE) (MODE)
#endif

/* Descriptor initializers: SLOP_MAP_DESC(K, HASH, EQ, MODE, V) and
 * SLOP_SET_DESC(K, HASH, EQ, MODE), key first so the transpiler emits one key
 * description for both. MODE is a slop_key_mode; SLOP_KEY_BITS is only for
 * keys with no padding whose equality is byte equality. SLOP_MAP_FORCE_KEY_MODE
 * overrides every map's mode, for measuring. */
#define SLOP_MAP_DESC_(KSIZE, KALIGN, VSIZE, VALIGN, HASH, EQ, MODE) { \
    .hash = (HASH), .eq = (EQ), \
    .key_size = (uint32_t)(KSIZE), \
    .value_size = (uint32_t)(VSIZE), \
    .value_off = (uint32_t)SLOP_MAP_ROUND((KSIZE), (VALIGN)), \
    .hash_off = (uint32_t)SLOP_MAP_ROUND(SLOP_MAP_ROUND((KSIZE), (VALIGN)) + (VSIZE), 8), \
    .entry_size = (uint32_t)(SLOP_MAP_MODE(MODE) == SLOP_KEY_HASHED \
        ? SLOP_MAP_ROUND(SLOP_MAP_ROUND((KSIZE), (VALIGN)) + (VSIZE), 8) + 8 \
        : SLOP_MAP_ROUND(SLOP_MAP_ROUND((KSIZE), (VALIGN)) + (VSIZE), \
                         SLOP_MAP_MAX((KALIGN), (VALIGN)))), \
    .mode = (uint32_t)SLOP_MAP_MODE(MODE) }

#define SLOP_MAP_DESC(K, HASH, EQ, MODE, V) \
    SLOP_MAP_DESC_(sizeof(K) + SLOP_MAP_ALIGN_OK(K), _Alignof(K), \
                   sizeof(V) + SLOP_MAP_ALIGN_OK(V), _Alignof(V), HASH, EQ, MODE)

#define SLOP_SET_DESC(K, HASH, EQ, MODE) \
    SLOP_MAP_DESC_(sizeof(K) + SLOP_MAP_ALIGN_OK(K), _Alignof(K), 0, 1, HASH, EQ, MODE)

/* ============================================================
 * Hash functions for primitive types
 * ============================================================ */

static inline uint64_t slop_hash_string(const void* key) {
    const slop_string* s = (const slop_string*)key;
    return slop_hash_bytes(s->data, s->len);
}

static inline bool slop_eq_string(const void* a, const void* b) {
    return slop_string_eq(*(const slop_string*)a, *(const slop_string*)b);
}

/* Hash for integers (uses splitmix64) */
static inline uint64_t slop_hash_int(const void* key) {
    uint64_t x = *(const int64_t*)key;
    x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
    x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
    return x ^ (x >> 31);
}

static inline bool slop_eq_int(const void* a, const void* b) {
    return *(const int64_t*)a == *(const int64_t*)b;
}

/* Hash for unsigned integers */
static inline uint64_t slop_hash_uint(const void* key) {
    uint64_t x = *(const uint64_t*)key;
    x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
    x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
    return x ^ (x >> 31);
}

static inline bool slop_eq_uint(const void* a, const void* b) {
    return *(const uint64_t*)a == *(const uint64_t*)b;
}

/* Hash/eq for keys narrower than 64 bits. Each reads exactly its own width --
 * a key is stored in key_size bytes, so reading 8 would run past it -- and
 * widens before hashing, so a value hashes as it would as an Int. */
#define SLOP_NARROW_KEY_HASH_EQ(NAME, T, WIDE, HASH) \
    static inline uint64_t slop_hash_##NAME(const void* key) { \
        WIDE x = (WIDE)*(const T*)key; \
        return HASH(&x); \
    } \
    static inline bool slop_eq_##NAME(const void* a, const void* b) { \
        return *(const T*)a == *(const T*)b; \
    }

SLOP_NARROW_KEY_HASH_EQ(i32, int32_t, int64_t, slop_hash_int)
SLOP_NARROW_KEY_HASH_EQ(i16, int16_t, int64_t, slop_hash_int)
SLOP_NARROW_KEY_HASH_EQ(i8, int8_t, int64_t, slop_hash_int)
SLOP_NARROW_KEY_HASH_EQ(u32, uint32_t, uint64_t, slop_hash_uint)
SLOP_NARROW_KEY_HASH_EQ(u16, uint16_t, uint64_t, slop_hash_uint)
SLOP_NARROW_KEY_HASH_EQ(u8, uint8_t, uint64_t, slop_hash_uint)
SLOP_NARROW_KEY_HASH_EQ(bool, bool, uint64_t, slop_hash_uint)

/* Hash/eq for Float (double) and F32 (float) keys. eq is C's ==, so -0.0
 * and 0.0 are one key and must hash alike, and a NaN key is never found. */
static inline uint64_t slop_hash_double(const void* key) {
    double d = *(const double*)key;
    if (d == 0.0) d = 0.0;
    uint64_t bits;
    memcpy(&bits, &d, sizeof(bits));
    return slop_hash_uint(&bits);
}

static inline bool slop_eq_double(const void* a, const void* b) {
    return *(const double*)a == *(const double*)b;
}

static inline uint64_t slop_hash_float(const void* key) {
    double d = (double)*(const float*)key;
    return slop_hash_double(&d);
}

static inline bool slop_eq_float(const void* a, const void* b) {
    return *(const float*)a == *(const float*)b;
}

/* Hash for pointers (useful for identity maps) */
static inline uint64_t slop_hash_ptr(const void* key) {
    uint64_t x = (uint64_t)(*(const void**)key);
    x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
    x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
    return x ^ (x >> 31);
}

static inline bool slop_eq_ptr(const void* a, const void* b) {
    return *(const void**)a == *(const void**)b;
}

/* Hash for symbols (which are just integers internally) */
#define slop_hash_symbol slop_hash_int
#define slop_eq_symbol slop_eq_int

/* Generate hash/eq functions over the raw bytes of a type with no padding
 * (an enum, a range alias) */
#define SLOP_STRUCT_HASH_EQ_DEFINE(T) \
    static inline uint64_t slop_hash_##T(const void* key) { \
        return slop_hash_bytes(key, sizeof(T)); \
    } \
    static inline bool slop_eq_##T(const void* a, const void* b) { \
        return memcmp(a, b, sizeof(T)) == 0; \
    }

/* ============================================================
 * Map operations
 * ============================================================ */

/* Spread a key hash across the low bits before masking. Generated hash
 * functions fold fields with FNV-style steps and slop_hash_int's low bits come
 * from a multiply, so neither can be trusted to vary in the bits a small
 * power-of-two index looks at. The result is what an entry stores. */
static inline uint64_t slop_map_mix(uint64_t h) {
    h ^= h >> 32;
    h *= 0x9E3779B97F4A7C15ULL;
    h ^= h >> 29;
    return h;
}

/* The capacity of the first table a map with no table gets */
#ifndef SLOP_MAP_FIRST_CAPACITY
#define SLOP_MAP_FIRST_CAPACITY 4
#endif

/* Smallest power of two >= n, and at least SLOP_MAP_FIRST_CAPACITY */
static inline size_t slop_map_round_cap(size_t n) {
    size_t cap = SLOP_MAP_FIRST_CAPACITY;
    while (cap < n) cap <<= 1;
    return cap;
}

/* An index slot holds an entry number plus one (0 is empty) in its low
 * idx_bits, and in the bits above them a tag: the top bits of the entry's
 * mixed hash. A probe compares the tag before it reads the entry, so a slot
 * belonging to another key is passed over without touching that key's entry
 * -- which, in a big table of large entries, is a cache and TLB miss. */
static inline size_t slop_map_idx_bits(size_t cap) {
    return (size_t)__builtin_ctzll((unsigned long long)cap) + 1;
}

/* Bytes per index slot for a table of cap entries: room for the entry number
 * and a tag of at least 1, 4, 8 and 30 bits respectively */
static inline size_t slop_map_index_width(size_t cap) {
    if (cap <= 64) return 1;
    if (cap <= 2048) return 2;
    if (cap <= ((size_t)1 << 23)) return 4;
    return 8;
}

/* The slot value for entry i with mixed hash h */
static inline size_t slop_map_slot_value(size_t cap, size_t i, uint64_t h) {
    size_t idx_bits = slop_map_idx_bits(cap);
    size_t tag_bits = 8 * slop_map_index_width(cap) - idx_bits;
    return (i + 1) | (size_t)((h >> (64 - tag_bits)) << idx_bits);
}

/* The entry number a non-empty slot value points at */
static inline size_t slop_map_slot_entry(size_t cap, size_t v) {
    return (v & (((size_t)1 << slop_map_idx_bits(cap)) - 1)) - 1;
}

/* The index starts after the entries, 8-aligned */
static inline size_t slop_map_index_off(const slop_map_desc* d, size_t cap) {
    return (cap * d->entry_size + 7) & ~(size_t)7;
}

static inline size_t slop_map_table_bytes(const slop_map_desc* d, size_t cap) {
    return slop_map_index_off(d, cap) + 2 * cap * slop_map_index_width(cap);
}

/* Entry i's key, and its value (a Set's is zero bytes long) */
static inline void* slop_map_key_at(const slop_map* m, size_t i) {
    return m->table + i * m->desc->entry_size;
}

static inline void* slop_map_value_at(const slop_map* m, size_t i) {
    return m->table + i * m->desc->entry_size + m->desc->value_off;
}

static inline size_t slop_map_slot_load(const uint8_t* index, size_t w, size_t s) {
    switch (w) {
    case 1: return index[s];
    case 2: return ((const uint16_t*)index)[s];
    case 4: return ((const uint32_t*)index)[s];
    default: return (size_t)((const uint64_t*)index)[s];
    }
}

static inline void slop_map_slot_store(uint8_t* index, size_t w, size_t s, size_t v) {
    switch (w) {
    case 1: index[s] = (uint8_t)v; break;
    case 2: ((uint16_t*)index)[s] = (uint16_t)v; break;
    case 4: ((uint32_t*)index)[s] = (uint32_t)v; break;
    default: ((uint64_t*)index)[s] = (uint64_t)v; break;
    }
}

/* Entry i's mixed hash: stored, or recomputed from its key */
static inline uint64_t slop_map_entry_hash(const slop_map* m, size_t i) {
    const slop_map_desc* d = m->desc;
    const uint8_t* e = (const uint8_t*)slop_map_key_at(m, i);
    if (d->mode == SLOP_KEY_HASHED) {
        uint64_t h;
        memcpy(&h, e + d->hash_off, sizeof(h));
        return h;
    }
    return slop_map_mix(d->hash(e));
}

static inline bool slop_map_key_eq(const slop_map_desc* d, const uint8_t* e,
                                   const void* key, uint64_t h) {
    switch (d->mode) {
    case SLOP_KEY_BITS:
        switch (d->key_size) {
        case 8: { uint64_t a, b; memcpy(&a, e, 8); memcpy(&b, key, 8); return a == b; }
        case 4: { uint32_t a, b; memcpy(&a, e, 4); memcpy(&b, key, 4); return a == b; }
        case 2: { uint16_t a, b; memcpy(&a, e, 2); memcpy(&b, key, 2); return a == b; }
        case 1: return *e == *(const uint8_t*)key;
        default: return memcmp(e, key, d->key_size) == 0;
        }
    case SLOP_KEY_CALL:
        return d->eq(e, key);
    default: {
        uint64_t eh;
        memcpy(&eh, e + d->hash_off, sizeof(eh));
        return eh == h && d->eq(e, key);
    }
    }
}

/* Probe the index for key (mixed hash h). Returns the slot holding its entry
 * with *found set, or the empty slot that ended the search. The index is at
 * most half full, so an empty slot always exists. The caller ensures cap > 0. */
static inline size_t slop_map_probe(const slop_map* m, const void* key, uint64_t h,
                                    bool* found) {
    size_t mask = 2 * m->cap - 1;
    size_t w = slop_map_index_width(m->cap);
    size_t idx_bits = slop_map_idx_bits(m->cap);
    size_t tag = slop_map_slot_value(m->cap, 0, h) >> idx_bits;
    const uint8_t* index = m->table + slop_map_index_off(m->desc, m->cap);
    size_t s = h & mask;
    for (;;) {
        size_t v = slop_map_slot_load(index, w, s);
        if (v == 0) { *found = false; return s; }
        if ((v >> idx_bits) == tag &&
            slop_map_key_eq(m->desc, (const uint8_t*)slop_map_key_at(m, slop_map_slot_entry(m->cap, v)),
                            key, h)) {
            *found = true;
            return s;
        }
        s = (s + 1) & mask;
    }
}

/* Point the first empty slot on hash h's probe chain at entry i */
static inline void slop_map_link(slop_map* m, uint64_t h, size_t i) {
    size_t mask = 2 * m->cap - 1;
    size_t w = slop_map_index_width(m->cap);
    uint8_t* index = m->table + slop_map_index_off(m->desc, m->cap);
    size_t s = h & mask;
    while (slop_map_slot_load(index, w, s) != 0) s = (s + 1) & mask;
    slop_map_slot_store(index, w, s, slop_map_slot_value(m->cap, i, h));
}

/* Give the map a table of new_cap entries (a power of two >= len), keeping
 * its entries in order and rebuilding the index from them. In order of
 * preference the table is
 *   - extended where it stands, when it is the last allocation in its block
 *     of `arena` and the block has room;
 *   - realloc'd with its block, when it is the only allocation in that block
 *     (a large table ends up alone in the block made for it, and the blocks
 *     of a chain grow no faster than it does, so without this it would move
 *     on every growth); the old storage is freed, so this needs
 *     may_free_old, which a put clears when its key or value points into
 *     the table;
 *   - moved into a new allocation in `arena`, abandoning the old one.
 * All three give the same layout. The table's one pointer is m->table: no
 * other pointer into it survives a put (see the RULES above). */
static inline void slop_map_resize_(slop_arena* arena, slop_map* m, size_t new_cap,
                                    bool may_free_old) {
    const slop_map_desc* d = m->desc;
    size_t new_bytes = slop_map_table_bytes(d, new_cap);
    bool placed = false;
    if (m->table != NULL) {
        size_t old_bytes = slop_map_table_bytes(d, m->cap);
        if (slop_arena_try_extend(arena, m->table, old_bytes, new_bytes)) {
            placed = true;
        } else if (may_free_old) {
            uint8_t* t = (uint8_t*)slop_arena_realloc_sole(arena, m->table, old_bytes, new_bytes);
            if (t != NULL) {
                m->table = t;
                placed = true;
            }
        }
    }
    if (!placed) {
        uint8_t* table = (uint8_t*)slop_arena_alloc(arena, new_bytes);
        if (table == NULL) {
            fprintf(stderr, "SLOP: map growth failed (arena has no storage)\n");
            abort();
        }
        if (m->len > 0) memcpy(table, m->table, m->len * d->entry_size);
        m->table = table;
    }
    m->cap = new_cap;
    memset(m->table + slop_map_index_off(d, new_cap), 0,
           2 * new_cap * slop_map_index_width(new_cap));
    for (size_t i = 0; i < m->len; i++) {
        slop_map_link(m, slop_map_entry_hash(m, i), i);
    }
}

static inline void slop_map_resize(slop_arena* arena, slop_map* m, size_t new_cap) {
    slop_map_resize_(arena, m, new_cap, true);
}

/* Double the table -- or, for a map with none yet, create the first */
static inline void slop_map_grow(slop_arena* arena, slop_map* m) {
    slop_map_resize(arena, m, m->cap == 0 ? SLOP_MAP_FIRST_CAPACITY : m->cap * 2);
}

/* Whether p points into m's table */
static inline bool slop_map_in_table(const slop_map* m, const void* p) {
    if (m->table == NULL || p == NULL) return false;
    const uint8_t* q = (const uint8_t*)p;
    return q >= m->table && q < m->table + slop_map_table_bytes(m->desc, m->cap);
}

/* capacity 0 creates a map with no table (cap 0, table NULL), which the first
 * put allocates; map-new and set-new ask for that, so an empty Map or Set
 * costs only this struct. Any other capacity is rounded up to a power of two
 * and allocated now. */
static inline slop_map slop_map_new(slop_arena* arena, size_t capacity,
                                    const slop_map_desc* desc) {
    slop_map m = {0, 0, desc, NULL};
    if (capacity > 0) slop_map_resize(arena, &m, slop_map_round_cap(capacity));
    return m;
}

/* Return pointer to arena-allocated map (for slop_map* type) */
static inline slop_map* slop_map_new_ptr(slop_arena* arena, size_t capacity,
                                         const slop_map_desc* desc) {
    slop_map* map = (slop_map*)slop_arena_alloc(arena, sizeof(slop_map));
    *map = slop_map_new(arena, capacity, desc);
    return map;
}

/* The stored value for key, or NULL. The pointer is into the table: copy what
 * it points at before the next put or remove. Reads never write, so any
 * number of threads may read a map that nobody is mutating. */
static inline void* slop_map_get(const slop_map* map, const void* key) {
    if (map->len == 0) return NULL;         /* nothing to find; hash nothing */
    uint64_t h = slop_map_mix(map->desc->hash(key));
    bool found;
    size_t s = slop_map_probe(map, key, h, &found);
    if (!found) return NULL;
    const uint8_t* index = map->table + slop_map_index_off(map->desc, map->cap);
    return slop_map_value_at(map, slop_map_slot_entry(map->cap,
                                  slop_map_slot_load(index, slop_map_index_width(map->cap), s)));
}

static inline bool slop_map_has(const slop_map* map, const void* key) {
    if (map->len == 0) return false;
    bool found;
    slop_map_probe(map, key, slop_map_mix(map->desc->hash(key)), &found);
    return found;
}

/* Store a copy of key and of the value_size bytes at value (a Set passes
 * NULL, 0). value_size must be the map's own value size: it is checked, and a
 * mismatch -- a transpiler bug, since both come from the map's value type --
 * aborts rather than write past an entry. */
static inline void slop_map_put(slop_arena* arena, slop_map* map,
                                const void* key, const void* value, size_t value_size) {
    const slop_map_desc* d = map->desc;
    if (value_size != d->value_size) {
        fprintf(stderr, "SLOP: map value size mismatch (put %zu bytes into %u-byte values)\n",
                value_size, (unsigned)d->value_size);
        abort();
    }
    uint64_t h = slop_map_mix(d->hash(key));
    if (map->len > 0) {
        bool found;
        size_t s = slop_map_probe(map, key, h, &found);
        if (found) {
            const uint8_t* index = map->table + slop_map_index_off(d, map->cap);
            size_t i = slop_map_slot_entry(map->cap,
                                           slop_map_slot_load(index, slop_map_index_width(map->cap), s));
            if (value_size > 0) memcpy(slop_map_value_at(map, i), value, value_size);
            return;
        }
    }
    if (map->len == map->cap) {
        /* A key or value read out of this very table stays readable: the
         * old table is then moved from, never freed */
        bool aliased = slop_map_in_table(map, key) || slop_map_in_table(map, value);
        slop_map_resize_(arena, map, map->cap == 0 ? SLOP_MAP_FIRST_CAPACITY : map->cap * 2,
                         !aliased);
    }
    size_t i = map->len;
    uint8_t* e = (uint8_t*)slop_map_key_at(map, i);
    memcpy(e, key, d->key_size);
    if (value_size > 0) memcpy(e + d->value_off, value, value_size);
    if (d->mode == SLOP_KEY_HASHED) memcpy(e + d->hash_off, &h, sizeof(h));
    slop_map_link(map, h, i);
    map->len++;
}

static inline bool slop_map_remove(slop_map* map, const void* key) {
    if (map->len == 0) return false;
    bool found;
    size_t hole = slop_map_probe(map, key, slop_map_mix(map->desc->hash(key)), &found);
    if (!found) return false;

    size_t mask = 2 * map->cap - 1;
    size_t w = slop_map_index_width(map->cap);
    uint8_t* index = map->table + slop_map_index_off(map->desc, map->cap);
    size_t gone = slop_map_slot_entry(map->cap, slop_map_slot_load(index, w, hole));

    /* Unlink the slot by backward-shift deletion (Knuth 6.4R, adapted to
     * forward probing). Emptying the slot on its own would truncate every
     * probe chain that ran through it, so a probe would stop early and miss
     * keys that are present, and a put would insert a duplicate. Shifting
     * later slots back keeps every chain contiguous from its home slot. The
     * index is at most half full, so the scan always meets an empty slot. */
    size_t i = hole;
    for (;;) {
        slop_map_slot_store(index, w, i, 0);
        size_t j = i;
        size_t v;
        for (;;) {
            j = (j + 1) & mask;
            v = slop_map_slot_load(index, w, j);
            if (v == 0) goto unlinked;
            size_t k = slop_map_entry_hash(map, slop_map_slot_entry(map->cap, v)) & mask;
            /* Slot j may fill the hole at i only if its home slot k does not
             * lie cyclically within (i, j]. */
            if (i <= j ? (i < k && k <= j) : (i < k || k <= j)) continue;
            break;
        }
        slop_map_slot_store(index, w, i, v);
        i = j;
    }
unlinked:
    /* Keep the entries dense: the last one moves into the gap, and the slot
     * that pointed at it is repointed. */
    {
        size_t last = map->len - 1;
        if (gone != last) {
            uint64_t lh = slop_map_entry_hash(map, last);
            size_t s = lh & mask;
            while (slop_map_slot_entry(map->cap, slop_map_slot_load(index, w, s)) != last)
                s = (s + 1) & mask;
            slop_map_slot_store(index, w, s, slop_map_slot_value(map->cap, gone, lh));
            memcpy(slop_map_key_at(map, gone), slop_map_key_at(map, last),
                   map->desc->entry_size);
        }
        map->len--;
    }
    return true;
}

static inline size_t slop_map_key_count(slop_map* map) {
    return map->len;
}

/* String keys, in iteration order, as a list */
static inline slop_list_string slop_map_keys(slop_arena* arena, slop_map* map) {
    slop_list_string result = slop_list_string_new(arena, map->len > 0 ? map->len : 1);
    for (size_t i = 0; i < map->len; i++) {
        slop_list_string_push(arena, &result, *(slop_string*)slop_map_key_at(map, i));
    }
    return result;
}

/* Generic set elements - returns raw pointer to arena-allocated array of keys
 * The caller should cast the data pointer to the appropriate element type.
 * Returns a struct with data pointer, len, and cap (list-compatible layout). */
typedef struct {
    void* data;
    size_t len;
    size_t cap;
} slop_set_elements_result;

static inline slop_set_elements_result slop_set_elements_raw(slop_arena* arena, slop_map* set) {
    size_t count = set->len;
    if (count == 0) {
        return (slop_set_elements_result){NULL, 0, 0};
    }
    size_t key_size = set->desc->key_size;
    void* result = slop_arena_alloc(arena, count * key_size);
    if (set->desc->entry_size == key_size) {
        memcpy(result, set->table, count * key_size);
    } else {
        for (size_t i = 0; i < count; i++) {
            memcpy((char*)result + i * key_size, slop_map_key_at(set, i), key_size);
        }
    }
    return (slop_set_elements_result){result, count, count};
}

/* ============================================================
 * Typed String-Keyed Map (generic via macro)
 *
 * Generates a type-safe wrapper around slop_map for (Map String V) types.
 * The typedef allows assignment compatibility while providing typed accessors.
 * ============================================================ */

#define SLOP_STRING_MAP_DEFINE(V, Name, OptName) \
    typedef slop_map Name; \
    \
    static inline const slop_map_desc* Name##_desc(void) { \
        static const slop_map_desc d = \
            SLOP_MAP_DESC(slop_string, slop_hash_string, slop_eq_string, SLOP_KEY_HASHED, V); \
        return &d; \
    } \
    \
    static inline Name Name##_new(slop_arena* arena, size_t cap) { \
        return slop_map_new(arena, cap, Name##_desc()); \
    } \
    \
    static inline OptName Name##_get(Name* map, slop_string key) { \
        void* v = slop_map_get(map, &key); \
        if (v) return (OptName){ .has_value = true, .value = *(V*)v }; \
        return (OptName){ .has_value = false }; \
    } \
    \
    static inline void Name##_put(slop_arena* arena, Name* map, slop_string key, V value) { \
        slop_map_put(arena, map, &key, &value, sizeof(V)); \
    } \
    \
    static inline bool Name##_has(Name* map, slop_string key) { \
        return slop_map_has(map, &key); \
    }

/* ============================================================
 * Generic Map Operations (for transpiled SLOP code)
 *
 * Integer-keyed map with fixed-size value storage (up to 256 bytes).
 * Used for SLOP Map types with integer keys (e.g., Map PetId Pet).
 * ============================================================ */

/* Entry states for hash map with tombstone support */
typedef enum {
    SLOP_GMAP_EMPTY = 0,      /* Never used - stops probing */
    SLOP_GMAP_OCCUPIED = 1,   /* Contains valid key/value */
    SLOP_GMAP_TOMBSTONE = 2   /* Deleted - continue probing */
} slop_gmap_state;

/* Generic map entry with fixed-size value storage */
typedef struct slop_gmap_entry_t {
    int64_t gmap_key;
    uint64_t gmap_hash;           /* cached hash value for O(1) lookup */
    uint8_t gmap_value[256];
    size_t gmap_value_size;
    slop_gmap_state gmap_state;   /* EMPTY, OCCUPIED, or TOMBSTONE */
} slop_gmap_entry_t;

typedef struct slop_gmap_t {
    size_t gmap_len;
    size_t gmap_cap;
    slop_gmap_entry_t* gmap_entries;
} slop_gmap_t;

/* Hash function for integer keys - splitmix64 (same as slop_hash_int) */
static inline uint64_t _slop_gmap_hash(int64_t key) {
    uint64_t x = (uint64_t)key;
    x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
    x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
    return x ^ (x >> 31);
}

/* Grow and rehash the map when load factor exceeds 75% */
static inline void _slop_gmap_grow(slop_gmap_t* m) {
    size_t old_cap = m->gmap_cap;
    slop_gmap_entry_t* old_entries = m->gmap_entries;

    size_t new_cap = old_cap * 2;
    m->gmap_entries = (slop_gmap_entry_t*)calloc(new_cap, sizeof(slop_gmap_entry_t));
    m->gmap_cap = new_cap;
    m->gmap_len = 0;

    /* Rehash only occupied entries (tombstones are discarded) */
    for (size_t i = 0; i < old_cap; i++) {
        if (old_entries[i].gmap_state == SLOP_GMAP_OCCUPIED) {
            uint64_t hash = old_entries[i].gmap_hash;
            size_t idx = hash % new_cap;

            for (size_t j = 0; j < new_cap; j++) {
                size_t probe = (idx + j) % new_cap;
                if (m->gmap_entries[probe].gmap_state == SLOP_GMAP_EMPTY) {
                    m->gmap_entries[probe] = old_entries[i];
                    m->gmap_len++;
                    break;
                }
            }
        }
    }
    free(old_entries);
}

/* Create empty generic map */
static inline void* map_empty(void) {
    slop_gmap_t* m = (slop_gmap_t*)malloc(sizeof(slop_gmap_t));
    m->gmap_len = 0;
    m->gmap_cap = SLOP_MAP_INITIAL_CAPACITY;
    m->gmap_entries = (slop_gmap_entry_t*)calloc(m->gmap_cap, sizeof(slop_gmap_entry_t));
    return m;
}

/* Check if key exists - O(1) average using hash + linear probing */
static inline bool map_has(void* gmap_ptr, int64_t gmap_lookup_key) {
    slop_gmap_t* m = (slop_gmap_t*)gmap_ptr;
    if (m->gmap_cap == 0) return false;

    uint64_t hash = _slop_gmap_hash(gmap_lookup_key);
    size_t idx = hash % m->gmap_cap;

    for (size_t i = 0; i < m->gmap_cap; i++) {
        size_t probe = (idx + i) % m->gmap_cap;
        slop_gmap_state state = m->gmap_entries[probe].gmap_state;
        if (state == SLOP_GMAP_EMPTY) {
            return false;  /* Empty slot = not found */
        }
        if (state == SLOP_GMAP_OCCUPIED &&
            m->gmap_entries[probe].gmap_hash == hash &&
            m->gmap_entries[probe].gmap_key == gmap_lookup_key) {
            return true;
        }
        /* TOMBSTONE: continue probing */
    }
    return false;
}

/* Remove key - O(1) average using hash + linear probing with tombstone */
static inline void* map_remove(void* gmap_ptr, int64_t gmap_lookup_key) {
    slop_gmap_t* m = (slop_gmap_t*)gmap_ptr;
    if (m->gmap_cap == 0) return m;

    uint64_t hash = _slop_gmap_hash(gmap_lookup_key);
    size_t idx = hash % m->gmap_cap;

    for (size_t i = 0; i < m->gmap_cap; i++) {
        size_t probe = (idx + i) % m->gmap_cap;
        slop_gmap_state state = m->gmap_entries[probe].gmap_state;
        if (state == SLOP_GMAP_EMPTY) {
            return m;  /* Not found */
        }
        if (state == SLOP_GMAP_OCCUPIED &&
            m->gmap_entries[probe].gmap_hash == hash &&
            m->gmap_entries[probe].gmap_key == gmap_lookup_key) {
            m->gmap_entries[probe].gmap_state = SLOP_GMAP_TOMBSTONE;
            m->gmap_len--;
            return m;
        }
        /* TOMBSTONE: continue probing */
    }
    return m;
}

/* Map put - implemented as a macro to handle any value type */
/* Returns the map pointer (functional style but mutates in place) */
#define map_put(gmap_ptr, gmap_k, gmap_v) \
    _slop_map_put_impl((gmap_ptr), (gmap_k), &(gmap_v), sizeof(gmap_v))

static inline void* _slop_map_put_impl(void* gmap_ptr, int64_t gmap_k, const void* gmap_v, size_t gmap_vsz) {
    slop_gmap_t* m = (slop_gmap_t*)gmap_ptr;

    /* Grow if load factor > 75% */
    if (m->gmap_len * 4 >= m->gmap_cap * 3) {
        _slop_gmap_grow(m);
    }

    uint64_t hash = _slop_gmap_hash(gmap_k);
    size_t idx = hash % m->gmap_cap;
    size_t first_tombstone = (size_t)-1;  /* Track first tombstone for reuse */

    for (size_t i = 0; i < m->gmap_cap; i++) {
        size_t probe = (idx + i) % m->gmap_cap;
        slop_gmap_state state = m->gmap_entries[probe].gmap_state;

        if (state == SLOP_GMAP_EMPTY) {
            /* Use first tombstone if found, otherwise use this empty slot */
            size_t insert_at = (first_tombstone != (size_t)-1) ? first_tombstone : probe;
            m->gmap_entries[insert_at].gmap_key = gmap_k;
            m->gmap_entries[insert_at].gmap_hash = hash;
            memcpy(m->gmap_entries[insert_at].gmap_value, gmap_v, gmap_vsz);
            m->gmap_entries[insert_at].gmap_value_size = gmap_vsz;
            m->gmap_entries[insert_at].gmap_state = SLOP_GMAP_OCCUPIED;
            m->gmap_len++;
            return m;
        }

        if (state == SLOP_GMAP_TOMBSTONE) {
            /* Remember first tombstone for potential reuse */
            if (first_tombstone == (size_t)-1) {
                first_tombstone = probe;
            }
            continue;  /* Keep probing to check for existing key */
        }

        /* state == SLOP_GMAP_OCCUPIED */
        if (m->gmap_entries[probe].gmap_hash == hash &&
            m->gmap_entries[probe].gmap_key == gmap_k) {
            /* Update existing entry */
            memcpy(m->gmap_entries[probe].gmap_value, gmap_v, gmap_vsz);
            m->gmap_entries[probe].gmap_value_size = gmap_vsz;
            return m;
        }
    }

    /* Table is full (shouldn't happen with proper load factor) */
    /* Use first tombstone if available */
    if (first_tombstone != (size_t)-1) {
        m->gmap_entries[first_tombstone].gmap_key = gmap_k;
        m->gmap_entries[first_tombstone].gmap_hash = hash;
        memcpy(m->gmap_entries[first_tombstone].gmap_value, gmap_v, gmap_vsz);
        m->gmap_entries[first_tombstone].gmap_value_size = gmap_vsz;
        m->gmap_entries[first_tombstone].gmap_state = SLOP_GMAP_OCCUPIED;
        m->gmap_len++;
    }
    return m;
}

/* Map get - returns Option-like struct matching generated types layout:
 * typedef struct { uint8_t tag; union { T some; } data; } slop_option_T;
 * We use a large enough buffer to hold any value type.
 */
typedef struct {
    uint8_t tag;
    union { uint8_t some[256]; } data;
} slop_gmap_option_raw;

static inline slop_gmap_option_raw _slop_map_get_raw(void* gmap_ptr, int64_t gmap_k) {
    slop_gmap_option_raw result = {1, {{0}}}; /* tag=1 means none */
    slop_gmap_t* m = (slop_gmap_t*)gmap_ptr;
    if (m->gmap_cap == 0) return result;

    uint64_t hash = _slop_gmap_hash(gmap_k);
    size_t idx = hash % m->gmap_cap;

    for (size_t i = 0; i < m->gmap_cap; i++) {
        size_t probe = (idx + i) % m->gmap_cap;
        slop_gmap_state state = m->gmap_entries[probe].gmap_state;

        if (state == SLOP_GMAP_EMPTY) {
            return result;  /* Not found */
        }

        if (state == SLOP_GMAP_OCCUPIED &&
            m->gmap_entries[probe].gmap_hash == hash &&
            m->gmap_entries[probe].gmap_key == gmap_k) {
            result.tag = 0; /* tag=0 means some */
            memcpy(result.data.some, m->gmap_entries[probe].gmap_value,
                   m->gmap_entries[probe].gmap_value_size);
            return result;
        }
        /* TOMBSTONE: continue probing */
    }
    return result;
}

/* Map values - returns List-like struct matching generated types layout:
 * typedef struct { T* data; size_t len; size_t cap; } slop_list_T;
 */
typedef struct { uint8_t* data; size_t len; size_t cap; } slop_gmap_list;

static inline slop_gmap_list _slop_map_values_raw(void* gmap_ptr, size_t value_size) {
    slop_gmap_t* m = (slop_gmap_t*)gmap_ptr;
    if (m->gmap_len == 0) {
        return (slop_gmap_list){NULL, 0, 0};
    }
    uint8_t* data = (uint8_t*)malloc(m->gmap_len * value_size);
    size_t write_idx = 0;
    /* Scan all slots since entries are scattered via hash */
    for (size_t idx = 0; idx < m->gmap_cap; idx++) {
        if (m->gmap_entries[idx].gmap_state == SLOP_GMAP_OCCUPIED) {
            memcpy(data + (write_idx * value_size),
                   m->gmap_entries[idx].gmap_value, value_size);
            write_idx++;
        }
    }
    return (slop_gmap_list){data, m->gmap_len, m->gmap_len};
}

/* Map keys - returns list of all int64_t keys */
static inline slop_list_int _slop_map_keys_raw(void* gmap_ptr) {
    slop_gmap_t* m = (slop_gmap_t*)gmap_ptr;
    if (m->gmap_len == 0) {
        return (slop_list_int){0, 0, NULL};
    }
    int64_t* data = (int64_t*)malloc(m->gmap_len * sizeof(int64_t));
    size_t write_idx = 0;
    /* Scan all slots since entries are scattered via hash */
    for (size_t idx = 0; idx < m->gmap_cap; idx++) {
        if (m->gmap_entries[idx].gmap_state == SLOP_GMAP_OCCUPIED) {
            data[write_idx++] = m->gmap_entries[idx].gmap_key;
        }
    }
    return (slop_list_int){m->gmap_len, m->gmap_len, data};
}

static inline slop_list_int map_keys(void* m) {
    return _slop_map_keys_raw(m);
}

/* Take first n elements from list - modifies in place and returns */
static inline slop_gmap_list _slop_take_raw(slop_gmap_list lst, int64_t n) {
    if ((size_t)n < lst.len) lst.len = (size_t)n;
    return lst;
}

/*
 * Type-specific map_get/map_values/take must be generated by the transpiler.
 * Define a macro that generates them for a given value type:
 */
#define SLOP_MAP_OPS_DEFINE(V, OptName, ListName) \
    static inline OptName map_get_##V(void* m, int64_t k) { \
        slop_gmap_option_raw raw = _slop_map_get_raw(m, k); \
        OptName result; \
        result.tag = raw.tag; \
        if (raw.tag == 0) memcpy(&result.data.some, raw.some, sizeof(V)); \
        return result; \
    } \
    static inline ListName map_values_##V(void* m) { \
        slop_gmap_list raw = _slop_map_values_raw(m, sizeof(V)); \
        return (ListName){(V*)raw.data, raw.len, raw.cap}; \
    } \
    static inline ListName take_##V(int64_t n, ListName lst) { \
        if ((size_t)n < lst.len) lst.len = (size_t)n; \
        return lst; \
    }

/*
 * Type-specific map operations are generated by the transpiler.
 * Use SLOP_MAP_GET_DEFINE(ValueType, OptionType) to define map_get for a type.
 * Use SLOP_MAP_VALUES_DEFINE(ValueType, ListType) to define map_values for a type.
 */

#define SLOP_MAP_GET_DEFINE(V, OptType) \
    static inline OptType map_get_##V(void* m, int64_t k) { \
        slop_gmap_option_raw raw = _slop_map_get_raw(m, k); \
        OptType result = {0}; \
        result.has_value = (raw.tag == 0); \
        if (raw.tag == 0) memcpy(&result.value, raw.data.some, sizeof(V)); \
        return result; \
    }

#define SLOP_MAP_VALUES_DEFINE(V, ListType) \
    static inline ListType map_values_##V(void* m) { \
        slop_gmap_list raw = _slop_map_values_raw(m, sizeof(V)); \
        return (ListType){(V*)raw.data, raw.len, raw.cap}; \
    }

#define SLOP_TAKE_DEFINE(V, ListType) \
    static inline ListType take_##V(int64_t n, ListType lst) { \
        if ((size_t)n < lst.len) lst.len = (size_t)n; \
        return lst; \
    }

/* Generic take that works with any list type */
#define take(n, lst) ({ \
    __auto_type _take_lst = (lst); \
    int64_t _take_n = (n); \
    if ((size_t)_take_n < _take_lst.len) _take_lst.len = (size_t)_take_n; \
    _take_lst; \
})

/* ============================================================
 * Option Type (generic via macros)
 * ============================================================ */

#define SLOP_OPTION_DEFINE(T, Name) \
    typedef struct { \
        bool has_value; \
        T value; \
    } Name; \
    \
    static inline Name Name##_some(T val) { \
        return (Name){true, val}; \
    } \
    \
    static inline Name Name##_none(void) { \
        return (Name){false}; \
    } \
    \
    static inline bool Name##_is_some(Name opt) { \
        return opt.has_value; \
    } \
    \
    static inline T Name##_unwrap(Name opt) { \
        SLOP_PRE(opt.has_value, "unwrap on Some"); \
        return opt.value; \
    }

SLOP_OPTION_DEFINE(int64_t, slop_option_int)
SLOP_OPTION_DEFINE(double, slop_option_float)
SLOP_OPTION_DEFINE(slop_string, slop_option_string)
SLOP_OPTION_DEFINE(void*, slop_option_ptr)
SLOP_OPTION_DEFINE(bool, slop_option_bool)

/* Pre-define common string-keyed maps (must come after SLOP_OPTION_DEFINE) */
SLOP_STRING_MAP_DEFINE(slop_string, slop_map_string_string, slop_option_string)
SLOP_STRING_MAP_DEFINE(int64_t, slop_map_string_int, slop_option_int)

/* ============================================================
 * Result Type (generic via macros)
 * ============================================================ */

#define SLOP_RESULT_DEFINE(T, E, Name) \
    typedef struct { \
        bool is_ok; \
        union { T ok; E err; } data; \
    } Name; \
    \
    static inline Name Name##_ok(T val) { \
        Name r; r.is_ok = true; r.data.ok = val; return r; \
    } \
    \
    static inline Name Name##_err(E e) { \
        Name r; r.is_ok = false; r.data.err = e; return r; \
    } \
    \
    static inline T Name##_unwrap(Name res) { \
        SLOP_PRE(res.is_ok, "unwrap on Ok"); \
        return res.data.ok; \
    }

/* Common error type */
typedef enum {
    SLOP_ERR_NONE = 0,
    SLOP_ERR_NULL_POINTER,
    SLOP_ERR_OUT_OF_BOUNDS,
    SLOP_ERR_INVALID_ARGUMENT,
    SLOP_ERR_NOT_FOUND,
    SLOP_ERR_ALREADY_EXISTS,
    SLOP_ERR_IO_ERROR,
    SLOP_ERR_PARSE_ERROR,
    SLOP_ERR_INSUFFICIENT_FUNDS,  /* Example domain error */
} slop_error;

static inline const char* slop_error_str(slop_error e) {
    switch (e) {
        case SLOP_ERR_NONE: return "none";
        case SLOP_ERR_NULL_POINTER: return "null pointer";
        case SLOP_ERR_OUT_OF_BOUNDS: return "out of bounds";
        case SLOP_ERR_INVALID_ARGUMENT: return "invalid argument";
        case SLOP_ERR_NOT_FOUND: return "not found";
        case SLOP_ERR_ALREADY_EXISTS: return "already exists";
        case SLOP_ERR_IO_ERROR: return "io error";
        case SLOP_ERR_PARSE_ERROR: return "parse error";
        case SLOP_ERR_INSUFFICIENT_FUNDS: return "insufficient funds";
        default: return "unknown error";
    }
}

SLOP_RESULT_DEFINE(int64_t, slop_error, slop_result_int)
SLOP_RESULT_DEFINE(void*, slop_error, slop_result_ptr)
SLOP_RESULT_DEFINE(slop_string, slop_error, slop_result_string)

/* ============================================================
 * Time
 * ============================================================ */

#ifdef _WIN32
#include <windows.h>
static inline int64_t slop_now_ms(void) {
    return (int64_t)GetTickCount64();
}
#else
#include <time.h>
static inline int64_t slop_now_ms(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (int64_t)ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}
#endif

static inline void slop_sleep_ms(int64_t ms) {
#ifdef _WIN32
    Sleep((DWORD)ms);
#else
    struct timespec ts = {ms / 1000, (ms % 1000) * 1000000};
    nanosleep(&ts, NULL);
#endif
}

static inline void sleep_ms(int64_t ms) {
    slop_sleep_ms(ms);
}

/* ============================================================
 * Integer formatting (for output)
 * ============================================================ */

static inline slop_string slop_int_to_string(slop_arena* arena, int64_t n) {
    char buf[32];
    int len = snprintf(buf, sizeof(buf), "%ld", (long)n);
    return slop_string_new_len(arena, buf, len);
}

static inline slop_string slop_float_to_string(slop_arena* arena, double n) {
    char buf[64];
    int len = snprintf(buf, sizeof(buf), "%g", n);
    return slop_string_new_len(arena, buf, len);
}

/* ============================================================
 * Stderr output helpers
 * ============================================================ */

static inline void slop_eprint(const char* s) {
    fputs(s, stderr);
}

static inline void slop_eputc(int c) {
    fputc(c, stderr);
}

#endif /* SLOP_RUNTIME_H */
