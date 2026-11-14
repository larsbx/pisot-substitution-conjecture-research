#!/usr/bin/env python3
"""Verify provider ZIP provenance and safely extract without executing content."""
from __future__ import annotations
import argparse
import datetime as dt
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import stat
import zipfile

COMMIT = "8a6bd5732fefba94ad4fef5df2333065c1302452"
TREE = "a7dcb3ebf30f3bb686d8f1beb3545dec26df8448"
RUN = 43570948106
JOB = 132374993239
REPOSITORY = "larsbx/pisot-substitution-conjecture-research"

def require(condition, message):
    if not condition:
        raise ValueError(message)

def file_hash(path):
    h = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()

def timestamp(value):
    return dt.datetime.fromisoformat(value.replace("Z", "+00:00"))

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("zip", "run-metadata", "jobs-metadata", "artifacts-metadata", "output", "receipt"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--requested-artifact-id", type=int, required=True)
    parser.add_argument("--connector-file-id", required=True)
    args = parser.parse_args()
    require(not args.output.exists() and not args.receipt.exists(), "Refusing existing output or receipt")
    run = json.loads(args.run_metadata.read_bytes())
    jobs = json.loads(args.jobs_metadata.read_bytes())
    artifacts = json.loads(args.artifacts_metadata.read_bytes())
    require(run["id"] == RUN and run["head_sha"] == COMMIT and run["head_commit"]["tree_id"] == TREE,
            "Unexpected run or source identity")
    require(run["repository"]["full_name"] == REPOSITORY and run["status"] == "completed"
            and run["conclusion"] == "success", "Expected successful completed repository run")
    require(jobs["total_count"] == len(jobs["jobs"]), "Incomplete jobs response")
    relevant = [item for item in jobs["jobs"] if item["id"] == JOB]
    require(len(relevant) == 1, "Missing unique expected job")
    job = relevant[0]
    require(job["run_id"] == RUN and job["head_sha"] == COMMIT and job["run_attempt"] == run["run_attempt"]
            and job["status"] == "completed" and job["conclusion"] == "success", "Unexpected job identity or verdict")
    require(artifacts["total_count"] == len(artifacts["artifacts"]), "Incomplete artifact response")
    matches = [a for a in artifacts["artifacts"] if a["id"] == args.requested_artifact_id]
    require(len(matches) == 1, "Missing unique requested artifact ID")
    artifact = matches[0]
    require(artifact["name"] == "original-c4-payload-" + COMMIT and not artifact["expired"],
            "Unexpected artifact name or expired artifact")
    require(artifact["workflow_run"]["id"] == RUN and artifact["workflow_run"]["head_sha"] == COMMIT
            and artifact["workflow_run"]["repository_id"] == run["repository"]["id"],
            "Artifact is bound to another run, repository or source")
    start, finish = timestamp(job["started_at"]), timestamp(job["completed_at"])
    require(start <= timestamp(artifact["created_at"]) <= finish
            and start <= timestamp(artifact["updated_at"]) <= finish,
            "Artifact timestamps do not belong to inspected attempt's job")
    actual = file_hash(args.zip)
    require(artifact["digest"] == "sha256:" + actual, "Downloaded ZIP differs from provider digest")
    require(args.zip.stat().st_size == artifact["size_in_bytes"], "ZIP size differs from provider metadata")
    require(re.fullmatch(r"file_[a-zA-Z0-9]+", args.connector_file_id), "Malformed connector file ID")
    manifest, names = [], set()
    with zipfile.ZipFile(args.zip) as archive:
        members = archive.infolist()
        for info in members:
            name = info.filename
            path = PurePosixPath(name)
            normalized = name[:-1] if name.endswith("/") else name
            require(bool(normalized) and "\\" not in name and "\x00" not in name
                    and not path.is_absolute() and ".." not in path.parts
                    and path.as_posix() == normalized, f"Unsafe archive path: {name!r}")
            require(normalized not in names, f"Duplicate archive member: {name!r}")
            names.add(normalized)
            kind = stat.S_IFMT(info.external_attr >> 16)
            require(kind in (0, stat.S_IFREG, stat.S_IFDIR)
                    and (kind != stat.S_IFDIR or info.is_dir())
                    and (kind != stat.S_IFREG or not info.is_dir()), f"Nonregular archive member: {name!r}")
            require(not info.flag_bits & 1, "Encrypted archive member refused")
        require(sum(i.file_size for i in members) <= 2 * 1024**3, "Unexpected artifact expansion exceeds 2 GiB")
        args.output.mkdir(parents=True, exist_ok=False)
        output = args.output.resolve(strict=True)
        for info in members:
            destination = output.joinpath(*PurePosixPath(info.filename).parts)
            require(destination.resolve().is_relative_to(output), "Archive destination escapes output")
            if info.is_dir():
                destination.mkdir(parents=True, exist_ok=True)
                continue
            destination.parent.mkdir(parents=True, exist_ok=True)
            h, size = hashlib.sha256(), 0
            with archive.open(info) as source, destination.open("xb") as target:
                for block in iter(lambda: source.read(1024 * 1024), b""):
                    size += len(block)
                    require(size <= info.file_size, "Extracted member exceeds declared size")
                    target.write(block)
                    h.update(block)
            require(size == info.file_size, "Extracted member size mismatch")
            manifest.append({"path": info.filename, "bytes": size, "sha256": h.hexdigest()})
    require((args.output / "revision.txt").read_text().splitlines() == [COMMIT, TREE],
            "Extracted artifact revision differs from inspected source")
    receipt = {"schema": "psc-hosted-artifact-download-extraction-v1",
               "checked_at_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
               "repository": REPOSITORY, "commit": COMMIT, "tree": TREE,
               "run_id": RUN, "run_attempt": run["run_attempt"], "job_id": JOB,
               "requested_artifact_id": args.requested_artifact_id,
               "returned_connector_file_id": args.connector_file_id,
               "artifact": artifact, "zip_sha256": actual, "zip_bytes": args.zip.stat().st_size,
               "provider_digest_matches": True, "artifact_timestamps_within_job": True,
               "download_method": "GitHub plugin download_workflow_artifact returned file URI; HTTPS retrieval of that URI",
               "extracted_root": str(output), "files": manifest,
               "no_artifact_code_executed": True, "mathematical_acceptance_claimed": False,
               "scope": "Transport, provider/source/attempt binding, and safe extraction only"}
    args.receipt.parent.mkdir(parents=True, exist_ok=True)
    with args.receipt.open("x") as stream:
        json.dump(receipt, stream, sort_keys=True, indent=2)
        stream.write("\n")
    print(json.dumps({"artifact_id": args.requested_artifact_id, "file_count": len(manifest),
                      "zip_sha256": actual, "output": str(output), "receipt": str(args.receipt)}, indent=2))

if __name__ == "__main__":
    main()
