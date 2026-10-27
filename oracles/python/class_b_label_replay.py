"""Orchestrate byte comparisons of canonical native exports; no graph mathematics."""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import re
import subprocess
import sys

if __name__=='__main__':
    binary=str(Path(sys.argv[1]).resolve());packet=Path(sys.argv[2]);out=Path(sys.argv[3]);out.mkdir(parents=True,exist_ok=True)
    files=sorted(packet.glob('labels/*.labels'))+sorted(packet.glob('witnesses/*.labels'))
    def one(path):
        m=re.fullmatch(r'(plus|minus)-g(\d+)-q(\d+)\.labels',path.name)
        if m is None:raise ValueError('unrecognized fixture')
        args=[binary,*m.groups()]+(['witnesses'] if path.parent.name=='witnesses' else [])
        result=subprocess.run(args,capture_output=True,check=True)
        if result.stdout!=path.read_bytes():
            (out/path.name).write_bytes(result.stdout)
            raise ValueError(f'fresh export disagrees: {path}')
        return str(path)
    # Fixed budget, deterministic fold; no shell dependency or relaxed comparisons.
    with ThreadPoolExecutor(2) as pool:
        for path in pool.map(one,files):print('BYTE_IDENTICAL',path,flush=True)
