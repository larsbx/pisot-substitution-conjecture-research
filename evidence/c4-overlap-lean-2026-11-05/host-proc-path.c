#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
/* Normalize only Lean's own executable-path lookup across this host's PID namespace. */
ssize_t readlink(const char *path, char *buf, size_t size) {
  static ssize_t (*original)(const char *, char *, size_t);
  if (!original) original = dlsym(RTLD_NEXT, "readlink");
  char self[64];
  snprintf(self, sizeof(self), "/proc/%d/exe", (int)getpid());
  return original(strcmp(path, self) == 0 ? "/proc/self/exe" : path, buf, size);
}
