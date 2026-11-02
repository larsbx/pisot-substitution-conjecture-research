#include <assert.h>
#include <errno.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
int main(void) {
    char own[64],a[4096],b[4096];
    snprintf(own,sizeof own,"/proc/%ld/exe",(long)getpid());
    ssize_t na=readlink(own,a,sizeof a),nb=readlink("/proc/self/exe",b,sizeof b);
    assert(na>0 && na==nb && memcmp(a,b,(size_t)na)==0);
    errno=0; assert(readlink("/tmp/proc-compat-deliberately-missing",b,sizeof b)==-1 && errno==ENOENT);
    errno=0; assert(readlink("/proc/1/exe",b,sizeof b)==-1 && errno==EACCES);
    puts("PASS: current executable alias agrees; missing and unrelated-process links retain original refusal");
}
