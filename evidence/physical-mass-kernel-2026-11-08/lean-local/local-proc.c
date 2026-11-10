#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
ssize_t readlink(const char *path, char *buf, size_t size) {
    ssize_t (*original)(const char *, char *, size_t) = dlsym(RTLD_NEXT, "readlink");
    char own[80];
    snprintf(own, sizeof(own), "/proc/%d/exe", getpid());
    return original(strcmp(path, own) == 0 ? "/proc/self/exe" : path, buf, size);
}
