"""The compiler runner's network ban is inherited by executed children."""
import ctypes.util
import pytest
import subprocess
import sys
from pathlib import Path


@pytest.mark.skipif(sys.platform != "linux" or not ctypes.util.find_library("seccomp"), reason="Linux seccomp is unavailable")
def test_offline_runner_denies_socket_creation_after_exec():
    root=Path(__file__).resolve().parents[1]
    code='''
import socket
for family in (socket.AF_INET,socket.AF_INET6,socket.AF_UNIX):
    try:
        socket.socket(family)
    except PermissionError:
        pass
    else:
        raise SystemExit('network ban was not inherited')
print('inherited network ban verified')
'''
    result=subprocess.run([sys.executable,str(root/'tools/run_without_network.py'),sys.executable,'-c',code],capture_output=True,text=True)
    assert result.returncode==0,result.stderr
    assert result.stdout.strip()=='inherited network ban verified'
