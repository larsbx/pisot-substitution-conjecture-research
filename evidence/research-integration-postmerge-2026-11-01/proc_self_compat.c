#define _GNU_SOURCE
#include <dlfcn.h>
#include <unistd.h>
#include <stdio.h>
#include <string.h>
/* Namespace compatibility only: numeric current-pid proc links are not
   mounted in this sandbox, while /proc/self/exe names the same executable.
   No proof checker, source file, or other requested path is changed. */
ssize_t readlink(const char *path, char *buf, size_t size) {
    static ssize_t (*real_readlink)(const char *, char *, size_t);
    if (!real_readlink) real_readlink = dlsym(RTLD_NEXT, "readlink");
    char own[64];
    snprintf(own, sizeof own, "/proc/%ld/exe", (long)getpid());
    return real_readlink(strcmp(path, own) == 0 ? "/proc/self/exe" : path, buf, size);
}
