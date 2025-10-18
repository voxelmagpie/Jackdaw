// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

#include <stdint.h>
#include <stdbool.h>

#if defined(__GNUC__) || defined(__clang__)
#define likely(x)   __builtin_expect(!!(x), 1)
#define unlikely(x) __builtin_expect(!!(x), 0)
#else
#define likely(x) (x)
#define unlikely(x) (x)
#endif

#define NULL ((void*)0)

#if __STDC_VERSION__ >= 201112L

#include <stdnoreturn.h>

#if defined(MULTITHREADED) && defined(__STDC_NO_THREADS__)
#error "Compiler does not support multithreading"
#endif

#else

#define noreturn

#ifdef MULTITHREADED
#error "C11 required for multithreaded code (_Thread_local for exceptions)"
#endif

#endif


void * getStdInPtr  (void);
void * getStdOutPtr (void);
void * getStdErrPtr (void);

typedef struct {
    const char * ptr;
    int64_t length;
    int64_t cap;
} AString;

extern
#ifdef MULTITHREADED
_Thread_local
#endif
void* thrownException;


static inline void * _takeException (void) {
    void * x = thrownException;
    thrownException = NULL;
    return x;
}

static inline void _restoreException (void * x) {
    thrownException =  x;
}

noreturn void abort(void);
noreturn void _panicExInNoThrow (void);
noreturn void __panic (const char * msg);
void _assert(bool x);


// int8_t *
static inline noreturn void _panic(void * msg) {
    __panic((const char *)msg);
}

static inline noreturn void panic_(void) {
    __panic("");
}

// Takes *const String
// This function definitions assumes the structure of String and List
static inline noreturn void _panic_String_ptr (void * s) {
    _panic(*(void**)s);
}



// Macros for defining operator functions

#define f(ret, name, arg, op) \
    static inline ret name(arg x, arg y) { return x op y; }

#define g(t, name, op) f(t, name, t, op)

extern const AString _overflow_msg;
extern const AString _div0_msg;

#if defined(__GNUC__) || defined(__clang__)
#define g_s(t, name, op, fn) \
    static inline t name(t x, t y) { \
        t r; \
        if (unlikely(fn(x, y, &r))) {thrownException = &_overflow_msg;} \
        return r; \
    }
#else
#define g_s(t, name, op, fn) \
    static t name(t x, t y) { \
        __panic("Compiler does not support checked arithmetic"); \
    }
#endif

#define checked_div_fn(t, name, op) \
    static inline t name(t x, t y) { \
        if (unlikely(y == 0)) {thrownException = &_div0_msg; return 0;} \
        return x op y; \
    }

// F32, F64

#define h(T, t) \
    g(T, _add_##t, +)  \
    g(T, _sub_##t, -)  \
    g(T, _mul_##t, *)  \
    g(T, _div_##t, /)  \
    f(bool, _gt_##t, T, >)  \
    f(bool, _lt_##t, T, <)  \
    f(bool, _gte_##t, T, >=)  \
    f(bool, _lte_##t, T, <=)  \
    f(bool, _eq_##t, T, ==)  \
    f(bool, _neq_##t, T, !=) \
    static inline T _neg_##t  (T x) { return -x; }

h(float, f32)
h(double, f64)
#undef h

// Bool

g(bool, _eq_bool, ==)
g(bool, _neq_bool, !=)
g(bool, _and_bool, &&)
g(bool, _or_bool, ||)

// Integer types


#define h(T, t, UT) \
    g(T, _add_##t, +) \
    g_s(T, _checked_add_##t, +, __builtin_add_overflow) \
    g(T, _sub_##t, -) \
    g_s(T, _checked_sub_##t, +, __builtin_sub_overflow) \
    g(T, _mul_##t, *) \
    g_s(T, _checked_mul_##t, +, __builtin_mul_overflow) \
    static inline T _wadd_##t(T x, T y) { return (T)((UT)x + (UT)y); } \
    static inline T _wsub_##t(T x, T y) { return (T)((UT)x - (UT)y); } \
    g(T, _div_##t, /) \
    g(T, _rem_##t, %) \
    checked_div_fn(T, _checked_div_##t, /) \
    checked_div_fn(T, _checked_rem_##t, %) \
    f(bool, _gt_##t, T, >) \
    f(bool, _lt_##t, T, <) \
    f(bool, _gte_##t, T, >=) \
    f(bool, _lte_##t, T, <=) \
    f(bool, _eq_##t, T, ==) \
    f(bool, _neq_##t, T, !=) \
    static inline T _lsh_##t(T x, int32_t y) { return x << y; } \
    static inline T _rsh_##t(T x, int32_t y) { return x >> y; } \
    f(T, _and_##t, T, &) \
    f(T, _or_##t, T, |) \
    f(T, _xor_##t, T, ^) \
    static inline T _neg_##t  (T x) { return -x; }

h(int8_t, i8, uint8_t)
h(int16_t, i16, uint16_t)
h(int32_t, i32, uint32_t)
h(int64_t, i64, uint64_t)
h(uint8_t, u8, uint8_t)
h(uint16_t, u16, uint16_t)
h(uint32_t, u32, uint32_t)
h(uint64_t, u64, uint64_t)

#undef h

#define h(T, t, min) \
    static inline T _checked_neg_##t  (T x) \
        { if (unlikely(x == min)) {thrownException = &_overflow_msg;} return -x; }

h(int8_t, i8, -128)
h(int16_t, i16, -32768)
h(int32_t, i32, -2147483648)
h(int64_t, i64, -0x8000000000000000L)

#undef h

#define h(T, t) \
    static inline T _wmul_##t  (T x, T y) { return x*y; }

h(uint8_t, u8)
h(uint16_t, u16)
h(uint32_t, u32)
h(uint64_t, u64)

#undef h
#undef f
#undef g
#undef g_s

static inline bool _not_bool  (bool x) { return !x; }

static inline int8_t _not_i8  (int8_t x) { return ~x; }
static inline int16_t _not_i16  (int16_t x) { return ~x; }
static inline int32_t _not_i32  (int32_t x) { return ~x; }
static inline int64_t _not_i64  (int64_t x) { return ~x; }
static inline uint8_t _not_u8  (uint8_t x) { return ~x; }
static inline uint16_t _not_u16  (uint16_t x) { return ~x; }
static inline uint32_t _not_u32  (uint32_t x) { return ~x; }
static inline uint64_t _not_u64  (uint64_t x) { return ~x; }

// #define f (T, t, name, op) static inline T name  (T x) { return op x; }

static inline int32_t _f64_to_i32_lossy (double x) { return (int32_t)x; }


int32_t readI32(void);
void writeI32(int32_t x);
double readF64(void);
void writeF64(double x);


void traceU64Hex(uint64_t x);
void traceI32(int32_t x);
// int8_t*
void traceCStr(void* x);
void traceUnformattedByte(uint8_t x);
