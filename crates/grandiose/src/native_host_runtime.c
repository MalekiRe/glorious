#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
    int64_t references;
    size_t length;
    unsigned char data[];
} G1Bytes;

typedef struct {
    size_t length;
    size_t capacity;
    size_t element_size;
    void *data;
    unsigned char *initialized;
} G1Array;

static int g1_process_argc;
static char **g1_process_argv;

static int g1_host_utf8_valid(const unsigned char *data, size_t length) {
    size_t index = 0;
    while (index < length) {
        unsigned char first = data[index++];
        if (first <= 0x7f) {
            continue;
        }
        if (first >= 0xc2 && first <= 0xdf) {
            if (index >= length || data[index++] < 0x80 ||
                data[index - 1] > 0xbf) {
                return 0;
            }
            continue;
        }
        if (first >= 0xe0 && first <= 0xef) {
            if (index + 1 >= length) {
                return 0;
            }
            unsigned char second = data[index++];
            unsigned char third = data[index++];
            if (third < 0x80 || third > 0xbf ||
                (first == 0xe0 && (second < 0xa0 || second > 0xbf)) ||
                (first == 0xed && (second < 0x80 || second > 0x9f)) ||
                (first != 0xe0 && first != 0xed &&
                 (second < 0x80 || second > 0xbf))) {
                return 0;
            }
            continue;
        }
        if (first >= 0xf0 && first <= 0xf4) {
            if (index + 2 >= length) {
                return 0;
            }
            unsigned char second = data[index++];
            unsigned char third = data[index++];
            unsigned char fourth = data[index++];
            if (third < 0x80 || third > 0xbf || fourth < 0x80 ||
                fourth > 0xbf ||
                (first == 0xf0 && (second < 0x90 || second > 0xbf)) ||
                (first == 0xf4 && (second < 0x80 || second > 0x8f)) ||
                (first != 0xf0 && first != 0xf4 &&
                 (second < 0x80 || second > 0xbf))) {
                return 0;
            }
            continue;
        }
        return 0;
    }
    return 1;
}

static G1Bytes *g1_host_bytes_allocate(size_t length) {
    if (length > SIZE_MAX - sizeof(G1Bytes)) {
        return NULL;
    }
    G1Bytes *bytes = malloc(sizeof(G1Bytes) + length);
    if (bytes == NULL) {
        return NULL;
    }
    bytes->references = 1;
    bytes->length = length;
    return bytes;
}

static char *g1_host_path(G1Bytes *path) {
    if (path == NULL || path->length == SIZE_MAX ||
        memchr(path->data, 0, path->length) != NULL) {
        return NULL;
    }
    char *terminated = malloc(path->length + 1);
    if (terminated == NULL) {
        return NULL;
    }
    memcpy(terminated, path->data, path->length);
    terminated[path->length] = 0;
    return terminated;
}

void g1_host_process_init(int argc, char **argv) {
    g1_process_argc = argc > 0 ? argc - 1 : 0;
    g1_process_argv = argc > 0 ? argv + 1 : argv;
}

G1Array *g1_host_process_args_get(void) {
    size_t length = (size_t)g1_process_argc;
    G1Array *array = malloc(sizeof(G1Array));
    if (array == NULL) {
        return NULL;
    }
    array->length = 0;
    array->capacity = length;
    array->element_size = sizeof(G1Bytes *);
    array->data = NULL;
    array->initialized = NULL;
    if (length == 0) {
        return array;
    }
    if (length > SIZE_MAX / sizeof(G1Bytes *)) {
        free(array);
        return NULL;
    }
    G1Bytes **elements = malloc(length * sizeof(G1Bytes *));
    unsigned char *initialized = calloc(length, 1);
    if (elements == NULL || initialized == NULL) {
        free(elements);
        free(initialized);
        free(array);
        return NULL;
    }
    array->data = elements;
    array->initialized = initialized;
    for (size_t index = 0; index < length; ++index) {
        size_t argument_length = strlen(g1_process_argv[index]);
        if (!g1_host_utf8_valid(
                (const unsigned char *)g1_process_argv[index],
                argument_length)) {
            for (size_t initialized_index = 0; initialized_index < index;
                 ++initialized_index) {
                free(elements[initialized_index]);
            }
            free(elements);
            free(initialized);
            free(array);
            return NULL;
        }
        G1Bytes *argument = g1_host_bytes_allocate(argument_length);
        if (argument == NULL) {
            for (size_t initialized_index = 0; initialized_index < index;
                 ++initialized_index) {
                free(elements[initialized_index]);
            }
            free(elements);
            free(initialized);
            free(array);
            return NULL;
        }
        memcpy(argument->data, g1_process_argv[index], argument_length);
        elements[index] = argument;
        initialized[index] = 1;
        array->length = index + 1;
    }
    return array;
}

G1Bytes *g1_host_fs_read(G1Bytes *path) {
    char *terminated = g1_host_path(path);
    if (terminated == NULL) {
        return NULL;
    }
    FILE *file = fopen(terminated, "rb");
    free(terminated);
    if (file == NULL || fseek(file, 0, SEEK_END) != 0) {
        if (file != NULL) {
            fclose(file);
        }
        return NULL;
    }
    long end = ftell(file);
    if (end < 0 || (uintmax_t)end > SIZE_MAX || fseek(file, 0, SEEK_SET) != 0) {
        fclose(file);
        return NULL;
    }
    size_t length = (size_t)end;
    G1Bytes *bytes = g1_host_bytes_allocate(length);
    if (bytes == NULL) {
        fclose(file);
        return NULL;
    }
    if (length != 0 && fread(bytes->data, 1, length, file) != length) {
        free(bytes);
        fclose(file);
        return NULL;
    }
    if (fclose(file) != 0) {
        free(bytes);
        return NULL;
    }
    return bytes;
}

void g1_host_fs_write(G1Bytes *path, G1Bytes *bytes) {
    char *terminated = g1_host_path(path);
    if (terminated == NULL || bytes == NULL) {
        free(terminated);
        return;
    }
    FILE *file = fopen(terminated, "wb");
    free(terminated);
    if (file == NULL) {
        return;
    }
    if (bytes->length != 0) {
        (void)fwrite(bytes->data, 1, bytes->length, file);
    }
    (void)fclose(file);
}

void g1_host_diagnostic_write(G1Bytes *text) {
    if (text == NULL) {
        return;
    }
    if (text->length != 0) {
        (void)fwrite(text->data, 1, text->length, stderr);
    }
    (void)fflush(stderr);
}
