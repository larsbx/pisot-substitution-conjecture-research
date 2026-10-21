"""Reproduce the minimal locked compiler/runtime; does not replace pixi.lock.

Usage: python bootstrap-pinned-mojo.py /tmp/psc-pinned-mojo
This extraction script requires Python >=3.12 and zstandard. Archive hashes are from kernel/pixi.lock.
The full Modular/Pixi dependency environment is a separate validation gate.
"""
import hashlib
import io
from pathlib import Path
import sys
import tarfile
import urllib.request
import zipfile
import zstandard

PACKAGES = [
    ('linux-64/mojo-compiler-1.1.0.dev2026090805-release.conda',
     '0d71889abb0887e2fa8a556c1081af4026034cdf98d27ad05b57cb096d7ad4f6'),
    ('noarch/mojo-python-1.1.0.dev2026090805-release.conda',
     '113c7d202236f943c91fdcb115f0a278e9c6027e1b7783bbc8b9a2076bb43838'),
]

def main():
    root = Path(sys.argv[1]).resolve()
    if root.exists():
        raise SystemExit('Use a fresh destination; existing runtime is not overwritten.')
    root.mkdir(parents=True)
    for relative, expected in PACKAGES:
        with urllib.request.urlopen('https://conda.modular.com/max-nightly/'+relative) as response:
            data = response.read()
        actual = hashlib.sha256(data).hexdigest()
        if actual != expected:
            raise SystemExit(f'Hash mismatch: {relative}')
        print(relative, actual)
        with zipfile.ZipFile(io.BytesIO(data)) as archive:
            for name in archive.namelist():
                if name.startswith('pkg-') and name.endswith('.tar.zst'):
                    with archive.open(name) as f, zstandard.ZstdDecompressor().stream_reader(f) as stream:
                        with tarfile.open(fileobj=stream, mode='r|') as tar:
                            tar.extractall(root, filter='data')
    print('Set MODULAR_MAX_PACKAGE_ROOT and MODULAR_MOJO_MAX_PACKAGE_ROOT to', root)
    print('Set MODULAR_MOJO_MAX_IMPORT_PATH to', root/'lib/mojo')
    print('Invoke', root/'bin/mojo')

if __name__ == '__main__':
    main()
