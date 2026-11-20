"""Session diagnostics: name a shallow clone instead of letting history-reading
provenance tests fail with an opaque CalledProcessError.

Nothing is skipped. Tests that replay pinned revisions still fail on a shallow
clone; this only says why, at the top and in the summary."""
from __future__ import annotations

import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
HINT = ('shallow clone: provenance tests that read pinned revisions will fail; '
        'fetch with fetch-depth: 0 or run `git fetch --unshallow`')


def _shallow() -> bool:
    done = subprocess.run(['git', 'rev-parse', '--is-shallow-repository'], cwd=ROOT,
                          capture_output=True, text=True)
    return done.returncode == 0 and done.stdout.strip() == 'true'


def pytest_report_header(config):
    return [f'WARNING {HINT}'] if _shallow() else []


def pytest_terminal_summary(terminalreporter, exitstatus, config):
    if exitstatus and _shallow():
        terminalreporter.write_sep('!', HINT, red=True)
