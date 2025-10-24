// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

#include "prelude.h"

#include <locale.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>



void * getStdInPtr (void) { return stdin; }
void * getStdOutPtr (void) { return stdout; }
void * getStdErrPtr (void) { return stderr; }



#ifdef MULTITHREADED
_Thread_local
#endif
void* thrownException = NULL;


noreturn void _panicExInNoThrow (void) {
    const AString * s = thrownException;
    fputs("Exception in function marked @NoThrow:\n", stderr);
    fputs(s->ptr, stderr);
    fputc('\n', stderr);
    abort();
}


noreturn void __panic (const char * msg) {
    fputs(msg, stderr);
    fputc('\n', stderr);
    abort();
}


int32_t snprintf_f32(int8_t* buf, size_t n, float x) { return snprintf((const char *)buf, n, "%g", x); }
int32_t snprintf_f64(int8_t* buf, size_t n, double x) { return snprintf((const char *)buf, n, "%g", x); }



// int32_t, int8_t**
int _kStart(int32_t, void*);

int main(int argc, char ** argv) {
    setlocale(LC_ALL, "");
    return _kStart((int32_t)argc, (int8_t**)argv);
}

const AString _expected_i32_msg = {"Expected I32", 13, 0};

int32_t readI32(void) {
    int32_t x;
    if(scanf("%d", &x) != 1) {thrownException=&_expected_i32_msg;}
    return x;
}

void writeI32(int32_t x) {
    printf("%d\n", x);
}

const AString _expected_f64_msg = {"Expected F64", 13, 0};

double readF64(void) {
    double x;
    if(scanf("%lf", &x) != 1) {thrownException=&_expected_i32_msg;}
    return x;
}

void writeF64(double x) {
    printf("%.2f\n", x);
}



void traceU64Hex(uint64_t x) {
    fprintf(stderr, "0x%lx\n", x);
}
void traceI32(int32_t x) {
    fprintf(stderr, "%d\n", x);
}
// int8_t*
void traceCStr(void* x) {
    fprintf(stderr, "%s\n", (const char *)x);
}
void traceCStrLen(void* x, int32_t n) {
    fprintf(stderr, "%.*s\n", n, (const char *)x);
}
void traceUnformattedByte(uint8_t x) {
    fputc(x, stderr);
}

const AString _overflow_msg = {"Overflow", 9, 0};
const AString _div0_msg = {"Divide by 0", 12, 0};

