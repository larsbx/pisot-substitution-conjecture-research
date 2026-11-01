"""Execute a local command with an inherited seccomp ban on networking.

Close inherited descriptors, deny socket creation and all socket connection /
transmission syscalls, and disable io_uring before exec. Refuse if loading the
filter fails. This restriction is inherited by compiler child processes.
"""
import ctypes,errno,os,socket,sys
lib=ctypes.CDLL('libseccomp.so.2',use_errno=True)
lib.seccomp_init.argtypes=[ctypes.c_uint32];lib.seccomp_init.restype=ctypes.c_void_p
lib.seccomp_syscall_resolve_name.argtypes=[ctypes.c_char_p];lib.seccomp_syscall_resolve_name.restype=ctypes.c_int
lib.seccomp_rule_add.argtypes=[ctypes.c_void_p,ctypes.c_uint32,ctypes.c_int,ctypes.c_uint];lib.seccomp_rule_add.restype=ctypes.c_int
lib.seccomp_load.argtypes=[ctypes.c_void_p];lib.seccomp_load.restype=ctypes.c_int
lib.seccomp_release.argtypes=[ctypes.c_void_p]
ctx=lib.seccomp_init(0x7fff0000)
if not ctx:raise RuntimeError('cannot initialize offline sandbox')
for name in ('socket','socketpair','connect','bind','listen','accept','accept4','sendto','sendmsg','sendmmsg','io_uring_setup'):
    num=lib.seccomp_syscall_resolve_name(name.encode())
    if num>=0 and lib.seccomp_rule_add(ctx,0x00050000|errno.EPERM,num,0)!=0:raise RuntimeError('cannot deny '+name)
os.closerange(3,1048576)
if lib.seccomp_load(ctx)!=0:raise RuntimeError('cannot load offline sandbox')
lib.seccomp_release(ctx)
for family in (socket.AF_INET,socket.AF_INET6,socket.AF_UNIX):
    try:socket.socket(family)
    except PermissionError:pass
    else:raise RuntimeError('network ban failed')
if sys.argv[1:]==['--self-test']:
    print('OFFLINE_SANDBOX_OK IPv4 IPv6 Unix socket creation denied; inherited descriptors closed')
else:
    os.execvp(sys.argv[1],sys.argv[1:])
