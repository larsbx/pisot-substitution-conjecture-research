#!/usr/bin/env bash
# Native/oracle replay only: computation remains in the canonical Mojo builder.
# Usage: bash kernel/check_forward_carrier.sh [EMPTY_OUTPUT_DIRECTORY]
# Default: build both executables with the repository's locked Pixi environment.
# Optional existing executables (supply both): PSC_FORWARD_EXPORTER, PSC_FORWARD_TEST.
# Optional compiler provenance for existing executables: PSC_FORWARD_MOJO.
# PSC_FORWARD_PYTHON selects Python with pytest installed; PYTHONPATH is preserved.
# Existing executables are hashed and replayed, never claimed to be rebuilt here.
set -euo pipefail
if (( $# > 1 )); then
    echo "usage: $0 [EMPTY_OUTPUT_DIRECTORY]" >&2
    exit 2
fi
psc_forward_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
psc_forward_output="${1:-$psc_forward_root/kernel/build/forward-carrier}"
exec "${PSC_FORWARD_PYTHON:-python3}" - "$psc_forward_root" "$psc_forward_output" <<'PY'
"""Provenance and command orchestration; no carrier construction in Python."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time


root = Path(sys.argv[1]).resolve()
out = Path(sys.argv[2]).resolve()
kernel = root / "kernel"
evidence = root / "evidence/c4-forward-carrier-2026-11-12"
if out.exists() and (not out.is_dir() or any(out.iterdir())):
    raise SystemExit(f"Refusing to overwrite existing evidence: {out}; choose an empty directory")
out.mkdir(parents=True, exist_ok=True)
started = time.monotonic()
env = dict(os.environ)
env["MODULAR_TELEMETRY_ENABLED"] = "0"
provided_exporter = env.get("PSC_FORWARD_EXPORTER")
provided_test = env.get("PSC_FORWARD_TEST")
provided = bool(provided_exporter or provided_test)
if not provided:
    env["MODULAR_HOME"] = str(kernel / ".pixi/envs/default/share/max")
receipt = {
    "schema": "psc-forward-carrier-replay-v1",
    "scope": "native bounded exports, byte reproduction, independent literal rows and refusal controls",
    "status": "running",
    "build_mode": "provided-binaries" if provided else "pixi-locked-build",
    "binaries_built_by_this_gate": False,
    "lean_kernel_acceptance": False,
    "productivity_claimed": False,
    "infinitude_claimed_from_caps": False,
    "python_executable": sys.executable,
    "python_version": sys.version,
    "environment": {key: env.get(key) for key in (
        "MODULAR_HOME", "MODULAR_TELEMETRY_ENABLED", "PYTHONPATH",
        "PYTEST_ADDOPTS", "PYTEST_DISABLE_PLUGIN_AUTOLOAD")},
    "commands": [],
    "budget_refusals": [],
    "binaries": {},
}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    result = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            result.update(chunk)
    return result.hexdigest()


def run(name, command, cwd=root, allow_failure=False, stdout_name=None):
    stdout = out / (stdout_name or f"{name}.stdout.log")
    stderr = out / f"{name}.stderr.log"
    record = {"name": name, "argv": list(map(str, command)), "cwd": str(cwd),
              "stdout": stdout.name, "stderr": stderr.name, "exit_code": None}
    receipt["commands"].append(record)
    step_started = time.monotonic()
    try:
        with stdout.open("wb") as output, stderr.open("wb") as errors:
            result = subprocess.run(record["argv"], cwd=cwd, env=env,
                                    stdout=output, stderr=errors, check=False)
        record["exit_code"] = result.returncode
    except OSError as error:
        record["launch_error"] = str(error)
        raise
    finally:
        record["elapsed_seconds"] = round(time.monotonic() - step_started, 6)
    print(f"{name}: exit {result.returncode}, {record['elapsed_seconds']:.3f}s", flush=True)
    require(allow_failure or result.returncode == 0,
            f"{name} failed with exit {result.returncode}; see {stdout} and {stderr}")
    return record


def executable(value):
    path = Path(value).expanduser().resolve()
    require(path.is_file() and os.access(path, os.X_OK), f"Not an executable file: {path}")
    return path


def compiler_provenance(path, version):
    # Match the installed package's URL and archive digest to the exact lock.
    # The archive itself is not rehashed here; Pixi verifies it on installation.
    lock = (kernel / "pixi.lock").read_text()
    locked = dict(re.findall(
        r"(?m)^- conda: (https://[^\n]+/mojo-compiler-[^\n]+)\n  sha256: ([0-9a-f]{64})$", lock))
    require(locked, "No compiler package pins found in kernel/pixi.lock")
    candidates = []
    for metadata_path in (path.parent.parent / "conda-meta").glob("mojo-compiler-*.json"):
        metadata = json.loads(metadata_path.read_text())
        if (metadata.get("url") in locked
                and metadata.get("sha256") == locked[metadata["url"]]):
            candidates.append((metadata_path, metadata))
    require(len(candidates) == 1, "Installed compiler metadata does not uniquely match the repository lock")
    metadata_path, metadata = candidates[0]
    require(f"Mojo {metadata['version']} " in version,
            "Observed compiler version does not match its locked package metadata")
    return {
        "path": str(path), "binary_sha256": digest(path), "observed_version": version.strip(),
        "installed_package_metadata": str(metadata_path),
        "installed_package_metadata_sha256": digest(metadata_path),
        "installed_package_metadata_matches_lock": True,
        "package_url": metadata["url"], "package_sha256": metadata["sha256"],
        "package_archive_rehashed_by_this_gate": False,
        "lock_sha256": digest(kernel / "pixi.lock"),
    }


def source_snapshot():
    paths = {root / path for path in (
        "kernel/pixi.toml", "kernel/pixi.lock", "kernel/check_forward_carrier.sh",
        ".github/workflows/c4-forward-carrier.yml", "vendored.toml", "pyproject.toml",
        "oracles/python/check_forward_carrier.py", "tests/test_forward_carrier_evidence.py",
        "evidence/c4-forward-carrier-2026-11-12/fixture0.json",
        "evidence/c4-forward-carrier-2026-11-12/fixture1.json",
        "proof/PscVerif/PscVerif/NamedForwardCarrierData0.lean",
        "proof/PscVerif/PscVerif/NamedForwardCarrierData1.lean",
        "proof/PscVerif/PscVerif/NamedForwardCarrierWords0.lean",
        "proof/PscVerif/PscVerif/NamedForwardCarrierWords1.lean")}
    # Hash all Mojo sources, including new local files and the vendored imports,
    # without traversing installed environments or generated build directories.
    for directory, subdirs, files in os.walk(kernel):
        subdirs[:] = [name for name in subdirs if not name.startswith(".") and name != "build"]
        paths.update(Path(directory) / name for name in files if name.endswith(".mojo"))
    return {str(path.relative_to(root)): digest(path) for path in sorted(paths)}


def cap_refusal(name, exporter, state_cap, length_cap, kind):
    record = run(name, [exporter, "0", str(state_cap), str(length_cap)], allow_failure=True)
    require(record["exit_code"] != 0, f"{name}: exhausted budget unexpectedly succeeded")
    require((out / record["stdout"]).stat().st_size == 0,
            f"{name}: exhausted budget emitted a packet on stdout")
    require(f"budget exhausted (kind={kind})" in (out / record["stderr"]).read_text(),
            f"{name}: failed for an unexpected reason")
    receipt["budget_refusals"].append({
        "command": name, "fixture": 0, "state_cap": state_cap, "length_cap": length_cap,
        "expected_exhaustion_kind": kind, "exit_code": record["exit_code"],
        "stdout_empty": True, "interpretation": "inconclusive budget refusal; no infinitude verdict",
    })


exit_code = 1
try:
    require(bool(provided_exporter) == bool(provided_test),
            "Supply both PSC_FORWARD_EXPORTER and PSC_FORWARD_TEST, or neither")
    revision_record = run("revision-before", ["git", "rev-parse", "HEAD", "HEAD^{tree}"])
    revision = (out / revision_record["stdout"]).read_text().splitlines()
    receipt["revision"] = {"commit": revision[0], "tree": revision[1]}
    if env.get("PSC_FORWARD_EXPECTED_HEAD"):
        require(revision[0] == env["PSC_FORWARD_EXPECTED_HEAD"], "Checkout is not the requested exact revision")
    run("worktree-before", ["git", "status", "--porcelain", "--untracked-files=normal"])
    before = source_snapshot()
    (out / "SOURCES.sha256").write_text("".join(f"{value}  {name}\n" for name, value in before.items()))

    if provided:
        exporter = executable(provided_exporter)
        native_test = executable(provided_test)
        receipt["provided_binary_provenance"] = (
            "Existing binaries are hashed and replayed; their build/source binding must be supplied separately.")
        if env.get("PSC_FORWARD_MOJO"):
            compiler = executable(env["PSC_FORWARD_MOJO"])
            version_record = run("compiler-version", [compiler, "--version"], cwd=kernel)
            receipt["compiler"] = compiler_provenance(
                compiler, (out / version_record["stdout"]).read_text())
        else:
            receipt["compiler"] = {"observed": False, "reason": "PSC_FORWARD_MOJO was not supplied"}
    else:
        compiler_record = run("compiler-path", ["pixi", "run", "--locked", "python", "-c",
                                               "import shutil; print(shutil.which('mojo') or '')"], cwd=kernel)
        compiler = executable((out / compiler_record["stdout"]).read_text().strip())
        version_record = run("compiler-version", ["pixi", "run", "--locked", "mojo", "--version"], cwd=kernel)
        receipt["compiler"] = compiler_provenance(
            compiler, (out / version_record["stdout"]).read_text())
        native_test, exporter = out / "native-test", out / "forward-carrier-export"
        run("build-native-test", ["pixi", "run", "--locked", "mojo", "build", "-I", ".",
                                  "tests/test_forward_carrier.mojo", "-o", native_test], cwd=kernel)
        run("build-exporter", ["pixi", "run", "--locked", "mojo", "build", "-I", ".",
                               "forward_carrier_export.mojo", "-o", exporter], cwd=kernel)
        receipt["binaries_built_by_this_gate"] = True

    receipt["binaries"] = {name: {"path": str(path), "sha256": digest(path)}
                           for name, path in (("native_test", native_test), ("exporter", exporter))}
    (out / "BINARIES.sha256").write_text("".join(
        f"{record['sha256']}  {record['path']}\n" for record in receipt["binaries"].values()))
    run("native-controls", [native_test], cwd=kernel)
    lean_source_files = []
    for fixture, length_cap in ((0, 100000), (1, 10000)):
        run(f"export-fixture{fixture}", [exporter, str(fixture), "20000", str(length_cap)],
            cwd=kernel, stdout_name=f"fixture{fixture}.json")
        run(f"compare-fixture{fixture}", ["cmp", evidence / f"fixture{fixture}.json", out / f"fixture{fixture}.json"])
        for kind, flag, stem in (
                ("lean-data", "--lean-data", "NamedForwardCarrierWords"),
                ("lean", "--lean", "NamedForwardCarrierData")):
            filename = f"{stem}{fixture}.lean"
            run(f"emit-{kind}-fixture{fixture}",
                [exporter, str(fixture), "20000", str(length_cap), flag],
                cwd=kernel, stdout_name=filename)
            run(f"compare-{kind}-fixture{fixture}", ["cmp",
                root / "proof/PscVerif/PscVerif" / filename, out / filename])
            lean_source_files.append(filename)
    receipt["archived_packets_reproduced_byte_for_byte"] = True
    receipt["lean_sources_reproduced_byte_for_byte"] = True
    receipt["lean_source_files"] = lean_source_files
    cap_refusal("fixture0-length-cap-refusal", exporter, 20000, 10000, 2)
    cap_refusal("fixture0-state-cap-refusal", exporter, 1, 100000, 1)
    run("independent-oracle", [sys.executable, "-O", root / "oracles/python/check_forward_carrier.py",
                              out / "fixture0.json", out / "fixture1.json"], stdout_name="oracle-receipt.json")
    run("oracle-tests", [sys.executable, "-m", "pytest", "-o", "addopts=", "-q",
                         "tests/test_forward_carrier_evidence.py"])

    require(source_snapshot() == before, "Source bytes changed during replay")
    receipt["source_bytes_unchanged_during_replay"] = True
    run("revision-after", ["git", "rev-parse", "HEAD", "HEAD^{tree}"])
    require((out / "revision-after.stdout.log").read_text().splitlines() == revision,
            "Source revision changed during replay")
    run("worktree-after", ["git", "status", "--porcelain", "--untracked-files=normal"])
    for record in receipt["binaries"].values():
        require(digest(Path(record["path"])) == record["sha256"], "A native binary changed during replay")
    receipt["status"] = "passed"
    exit_code = 0
except Exception as error:
    receipt["status"] = "failed"
    receipt["error"] = str(error)
    print(f"Forward-carrier replay refused: {error}", file=sys.stderr, flush=True)
finally:
    receipt["elapsed_seconds"] = round(time.monotonic() - started, 6)
    receipt["exit_code"] = exit_code
    (out / "replay-receipt.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    artifacts = sorted(path for path in out.rglob("*") if path.is_file() and path.name != "SHA256SUMS")
    (out / "SHA256SUMS").write_text("".join(
        f"{digest(path)}  {path.relative_to(out)}\n" for path in artifacts))
if exit_code == 0:
    print(f"PASS native/oracle forward-carrier replay; receipts: {out}")
    print("Caps were inconclusive refusals. No Lean acceptance or productivity verdict is supplied.")
sys.exit(exit_code)
PY
