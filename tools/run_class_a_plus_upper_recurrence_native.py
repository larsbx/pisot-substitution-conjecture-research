"""Run canonical Mojo with immutable source bindings and preserved raw output.

This is provenance tooling; mathematical construction stays in kernel/.
Refuses overwriting an earlier attempt. Exit/cap/source changes never accept.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-prefix", type=Path, required=True)
    parser.add_argument("--mojo", type=Path, default=root / "kernel/.pixi/envs/default/bin/mojo")
    args = parser.parse_args()
    prefix, mojo = args.output_prefix.resolve(), args.mojo.resolve()
    outputs = {kind: Path(str(prefix) + suffix) for kind, suffix in
               (("stdout", ".log"), ("stderr", ".stderr"), ("receipt", ".json"))}
    if any(path.exists() for path in outputs.values()):
        raise ValueError("attempt exists; historical output must be preserved")
    prefix.parent.mkdir(parents=True, exist_ok=True)
    def snapshot():
        paths = sorted(p for p in (root / "kernel").rglob("*.mojo")
                       if ".pixi" not in p.parts and "build" not in p.parts)
        paths += [root / "kernel/pixi.toml", root / "kernel/pixi.lock", Path(__file__).resolve()]
        return {str(p.relative_to(root)): digest(p) for p in paths}
    before = snapshot()
    env = os.environ.copy()
    env["MODULAR_HOME"] = str(mojo.parent.parent / "share/max")
    env["MODULAR_TELEMETRY_ENABLED"] = "0"
    command = [str(mojo), "run", "-j", "1", "-I", str(root / "kernel"),
               str(root / "kernel/tests/test_class_a_plus_upper_recurrence.mojo"), "--emit"]
    version = subprocess.check_output([str(mojo), "--version"], env=env, text=True).strip()
    started = datetime.now(timezone.utc).isoformat()
    start = time.monotonic()
    cap_exhausted = False
    with outputs["stdout"].open("xb") as out, outputs["stderr"].open("xb") as err:
        try:
            exit_code = subprocess.run(command, env=env, stdout=out, stderr=err,
                                       timeout=1200).returncode
        except subprocess.TimeoutExpired:
            exit_code, cap_exhausted = 124, True
    after = snapshot()
    receipt = dict(command=command, started_at_utc=started,
        finished_at_utc=datetime.now(timezone.utc).isoformat(),
        seconds=time.monotonic() - start, exit_code=exit_code,
        runtime_cap_seconds=1200, cap_exhausted=cap_exhausted,
        mojo_version=version, mojo_sha256=digest(mojo), source_inputs=before,
        sources_unchanged=before == after,
        stdout_sha256=digest(outputs["stdout"]), stderr_sha256=digest(outputs["stderr"]),
        status="completed" if exit_code == 0 and before == after else "no_verdict")
    outputs["receipt"].write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps({k: v for k, v in receipt.items() if k != "source_inputs"}, sort_keys=True))
    return exit_code or (0 if before == after else 1)


if __name__ == "__main__":
    raise SystemExit(main())
