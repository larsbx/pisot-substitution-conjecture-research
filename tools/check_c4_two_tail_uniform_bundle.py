#!/usr/bin/env python3
"""Restore, authenticate and replay the immutable two-tail research bundle.

Runs in a temporary directory so historical receipts are never overwritten.
The Python implementation remains a secondary prototype, not a native/Lean proof.
"""
from __future__ import annotations
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
BUNDLE = ROOT / 'experiments/c4_two_tail_uniform'
MAX_RECEIPT_BYTES = 1_000_000


def authenticated_copy(destination: Path) -> int:
    shutil.copytree(BUNDLE, destination, ignore=shutil.ignore_patterns('__pycache__', '.pytest_cache'))
    compressed = destination / 'evidence/receipt.json.gz'
    with gzip.open(compressed, 'rb') as stream:
        raw = stream.read(MAX_RECEIPT_BYTES + 1)
    if len(raw) > MAX_RECEIPT_BYTES:
        raise ValueError('receipt decompression budget exceeded')
    for name in ('receipt.json', 'receipt-regenerated.stdout.txt'):
        (destination / 'evidence' / name).write_bytes(raw)
    manifest = json.loads((destination / 'evidence/local-validation.json').read_text())
    pins = manifest['source_hashes']
    for name, pin in pins.items():
        path = (destination / name).resolve()
        if not path.is_relative_to(destination.resolve()) or not path.is_file():
            raise ValueError(f'invalid pinned path: {name}')
        data = path.read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        if (len(data) != pin['bytes'] or hashlib.sha256(data).hexdigest() != pin['sha256']
                or blob != pin['git_blob_sha']):
            raise ValueError(f'original bundle pin mismatch: {name}')
    return len(pins)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='Separate directory for this run, never historical evidence')
    parser.add_argument('--verify-only', action='store_true', help='Authenticate bytes without claiming tests ran')
    args = parser.parse_args()
    output = args.output.resolve() if args.output else None
    if output is not None:
        if output.is_relative_to(BUNDLE.resolve()):
            raise ValueError('fresh output must not overwrite the archived bundle')
        output.mkdir(parents=True, exist_ok=True)
    runs = []
    with tempfile.TemporaryDirectory(prefix='psc-two-tail-') as temp:
        work = Path(temp) / 'bundle'
        count = authenticated_copy(work)
        if not args.verify_only:
            commands = (
                ('python-tests', [sys.executable, '-m', 'pytest', '-q', 'tests/test_two_tail_uniform.py']),
                ('independent-replay', [sys.executable, 'tools/independent_replay.py']),
                ('receipt-regenerated', [sys.executable, 'oracles/two_tail_uniform.py', '--receipt']),
            )
            for label, command in commands:
                started = time.monotonic()
                result = subprocess.run(command, cwd=work, env={**os.environ, 'PYTEST_DISABLE_PLUGIN_AUTOLOAD': '1'},
                                        capture_output=True, text=True, timeout=300)
                record = {'label': label, 'argv': command, 'exit_code': result.returncode,
                          'seconds': round(time.monotonic() - started, 3)}
                runs.append(record)
                if output is not None:
                    (output / f'{label}.stdout.txt').write_text(result.stdout)
                    (output / f'{label}.stderr.txt').write_text(result.stderr)
                if result.returncode:
                    sys.stderr.write(result.stdout + result.stderr)
                    return result.returncode
                if label == 'receipt-regenerated':
                    if json.loads(result.stdout) != json.loads((work / 'evidence/receipt.json').read_text()):
                        raise ValueError('regenerated receipt differs from archived data')
                    record['receipt_equal'] = True
                elif label == 'independent-replay':
                    record['result'] = json.loads(result.stdout)
                else:
                    record['result'] = result.stdout.strip()
        report = {'status': 'hashes-only' if args.verify_only else 'passed', 'authenticated_files': count,
                  'runs': runs, 'native_or_lean_validation': False,
                  'scope': 'finite exact replay and symbolic identities; universal word proof is separate'}
        text = json.dumps(report, indent=2, sort_keys=True) + '\n'
        if output is not None:
            (output / 'integration-validation.json').write_text(text)
        print(text, end='')
    return 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (ValueError, KeyError, OSError, subprocess.TimeoutExpired) as exc:
        print(f'two-tail validation failed: {exc}', file=sys.stderr)
        raise SystemExit(1)
