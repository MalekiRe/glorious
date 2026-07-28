#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

enum {
    G1_RUNTIME_FAULT_ARITHMETIC_OVERFLOW = 1,
    G1_RUNTIME_FAULT_DIVISION_BY_ZERO = 2,
    G1_RUNTIME_FAULT_INVALID_SHIFT_COUNT = 3,
    G1_RUNTIME_FAULT_INVALID_CHARACTER = 4,
    G1_RUNTIME_FAULT_INVALID_UTF8 = 5,
    G1_RUNTIME_FAULT_INDEX_OUT_OF_BOUNDS = 6,
    G1_RUNTIME_FAULT_EMPTY_ARRAY_SLOT = 7,
    G1_RUNTIME_FAULT_ARRAY_SLOT_ALREADY_INITIALIZED = 8,
    G1_RUNTIME_FAULT_ARRAY_NOT_DRAINED = 9,
    G1_RUNTIME_FAULT_ALLOCATION_OVERFLOW = 10,
    G1_RUNTIME_FAULT_ALLOCATION_LIMIT = 11,
    G1_RUNTIME_FAULT_UNHANDLED_EFFECT = 12,
    G1_RUNTIME_FAULT_EXPLICIT_ABORT = 13,
};

static void g1_write_text(const char *text) {
    while (*text != '\0') {
        (void)fputc((unsigned char)*text, stderr);
        ++text;
    }
}

static void g1_write_u32(uint32_t value) {
    char digits[10];
    size_t length = 0;
    do {
        digits[length++] = (char)('0' + (value % 10));
        value /= 10;
    } while (value != 0);
    while (length != 0) {
        (void)fputc((unsigned char)digits[--length], stderr);
    }
}

_Noreturn void g1_runtime_fault(uint32_t detail, uint32_t arg0, uint32_t arg1,
                                const unsigned char *message,
                                size_t message_len) {
    g1_write_text("grandiose: ");
    switch (detail) {
    case G1_RUNTIME_FAULT_ARITHMETIC_OVERFLOW:
        g1_write_text("checked arithmetic overflow");
        break;
    case G1_RUNTIME_FAULT_DIVISION_BY_ZERO:
        g1_write_text("division by zero");
        break;
    case G1_RUNTIME_FAULT_INVALID_SHIFT_COUNT:
        g1_write_text("invalid integer shift count");
        break;
    case G1_RUNTIME_FAULT_INVALID_CHARACTER:
        g1_write_text("invalid Unicode scalar value");
        break;
    case G1_RUNTIME_FAULT_INVALID_UTF8:
        g1_write_text("invalid UTF-8");
        break;
    case G1_RUNTIME_FAULT_INDEX_OUT_OF_BOUNDS:
        g1_write_text("index or slice is out of bounds");
        break;
    case G1_RUNTIME_FAULT_EMPTY_ARRAY_SLOT:
        g1_write_text("array slot is empty");
        break;
    case G1_RUNTIME_FAULT_ARRAY_SLOT_ALREADY_INITIALIZED:
        g1_write_text("array slot is already initialized");
        break;
    case G1_RUNTIME_FAULT_ARRAY_NOT_DRAINED:
        g1_write_text("array still contains initialized slots");
        break;
    case G1_RUNTIME_FAULT_ALLOCATION_OVERFLOW:
        g1_write_text("array capacity overflow");
        break;
    case G1_RUNTIME_FAULT_ALLOCATION_LIMIT:
        g1_write_text("runtime allocation limit exceeded");
        break;
    case G1_RUNTIME_FAULT_UNHANDLED_EFFECT:
        g1_write_text("unhandled effect ");
        g1_write_u32(arg0);
        (void)fputc('/', stderr);
        g1_write_u32(arg1);
        break;
    case G1_RUNTIME_FAULT_EXPLICIT_ABORT:
        g1_write_text("aborted");
        if (arg0 != 0) {
            g1_write_text(": ");
            if (message != NULL && message_len != 0) {
                (void)fwrite(message, 1, message_len, stderr);
            }
        }
        break;
    default:
        g1_write_text("unknown native runtime fault");
        break;
    }
    (void)fputc('\n', stderr);
    (void)fflush(stderr);
    exit(EXIT_FAILURE);
}
