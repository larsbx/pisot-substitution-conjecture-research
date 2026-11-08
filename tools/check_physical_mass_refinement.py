#!/usr/bin/env python3
"""Bind PR #515 source and export bytes; do not reimplement its mathematics.

Canonical graph reconstruction and physical-mass arithmetic remain in the
pinned Mojo program. Its independent Python oracle is replayed separately.
This governance checker authenticates their source and packet receipts only.
Failure means refusal to issue an acceptance receipt, never a zero verdict.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import subprocess
import sys
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = ROOT / "evidence/physical-mass-kernel-2026-11-08/source-manifest.json"
SOURCE_HEAD = "51dd090a6aefeb92210410a3f7e20d51926d7e86"
SOURCE_TREE = "25b480b58b5766efdb59c17592c5ae679326a284"
SOURCE_PARENT = "49bc7e1af11b6ab04f84b79f8737500b6de3748b"
PACKET_SHA256 = "9eee6485f202becb8761e52f77e795b34916edf49ce75d6df821bf7fa1646683"
INTEGER = re.compile(r"(?:0|-[1-9][0-9]*|[1-9][0-9]*)\Z")


class Refusal(Exception):
    """Evidence does not meet the fixed source-binding contract."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise Refusal(message)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git(source: Path, *args: str) -> bytes:
    env = dict(os.environ, GIT_NO_REPLACE_OBJECTS="1")
    result = subprocess.run(
        ["git", "-C", str(source), *args], capture_output=True, env=env, check=False
    )
    require(result.returncode == 0, "Git source inspection failed: " + " ".join(args))
    return result.stdout


def load_manifest(path: Path, snapshot: bytes | None = None) -> dict[str, Any]:
    manifest = json.loads(path.read_bytes() if snapshot is None else snapshot)
    require(manifest["schema"] == "physical-mass-source-manifest-v1", "manifest schema")
    require(manifest["source"]["commit"] == SOURCE_HEAD, "manifest changed source commit")
    require(manifest["source"]["tree"] == SOURCE_TREE, "manifest changed source tree")
    require(manifest["source"]["parents"] == [SOURCE_PARENT], "manifest changed source parent")
    require(manifest["packet"]["sha256"] == PACKET_SHA256, "manifest changed packet digest")
    require(manifest["packet"]["bytes"] == 1085652, "manifest packet size")
    require(manifest["packet"]["records"] == 43940, "manifest packet record count")
    require([g["source"] for g in manifest["graphs"]] == list(range(12)), "manifest source inventory")
    middles = ("012", "021", "102", "120", "201", "210")
    for source_id, graph in enumerate(manifest["graphs"]):
        require(graph["images"] == ["11", middles[source_id // 2], ("01", "10")[source_id % 2]],
                "manifest changed the ordered source substitution labels")
    require(manifest["roots"]["vertex_ids_per_graph"] == [0, 1, 2], "manifest root inventory")
    require(
        manifest["roots"]["states_per_graph"]
        == [[0, 1, 0, 0, 0], [0, 2, 0, 0, 0], [1, 2, 0, 0, 0]],
        "manifest root states",
    )
    return manifest


def check_blob(data: bytes, expected_oid: str, label: str) -> None:
    header = b"blob " + str(len(data)).encode("ascii") + b"\0"
    actual = hashlib.sha1(header + data).hexdigest()
    require(actual == expected_oid, "working-tree bytes differ from pinned Git blob: " + label)


def authenticate_source(source: Path, manifest: dict[str, Any]) -> dict[str, Any]:
    """Hash all tracked working files, including ones hidden by index flags."""
    expected = manifest["source"]
    actual_head = git(source, "rev-parse", "HEAD").decode("ascii").strip()
    require(actual_head == expected["commit"], "source HEAD is not the pinned PR #515 revision")
    actual_tree = git(source, "rev-parse", "HEAD^{tree}").decode("ascii").strip()
    require(actual_tree == expected["tree"], "source tree differs from the authenticated tree")
    commit = git(source, "cat-file", "commit", actual_head)
    parents = [line[7:].decode("ascii") for line in commit.split(b"\n\n", 1)[0].splitlines()
               if line.startswith(b"parent ")]
    require(parents == expected["parents"], "source commit parent differs from PR #497")

    tree: dict[bytes, tuple[bytes, bytes]] = {}
    entries = git(source, "ls-tree", "-rz", "--full-tree", actual_head).split(b"\0")
    for entry in filter(None, entries):
        metadata, path = entry.split(b"\t", 1)
        mode, kind, oid = metadata.split(b" ")
        require(kind == b"blob" and mode in (b"100644", b"100755"), "unsupported source object mode")
        require(not path.startswith(b"/") and b".." not in path.split(b"/"), "unsafe tracked source path")
        require(path not in tree, "duplicate tracked source path")
        tree[path] = (mode, oid)
    require(len(tree) == expected["tracked_files"], "tracked source inventory changed")

    # Check index entries as well as the HEAD tree. The byte pass below does
    # not trust git diff, assume-unchanged, skip-worktree, or timestamp caches.
    index: dict[bytes, tuple[bytes, bytes]] = {}
    for entry in filter(None, git(source, "ls-files", "--stage", "-z").split(b"\0")):
        metadata, path = entry.split(b"\t", 1)
        mode, oid, stage = metadata.split(b" ")
        require(stage == b"0" and path not in index, "unmerged or duplicate source index entry")
        index[path] = (mode, oid)
    require(index == tree, "source index differs from the pinned tree")

    # Extra source files can shadow canonical imports even when every tracked
    # file is intact. Installed Pixi dependencies and bytecode caches have a
    # separate toolchain/cache boundary; they are not repository source.
    for import_root in (source / "kernel", source / "oracles"):
        for directory, subdirectories, files in os.walk(import_root):
            current = Path(directory)
            subdirectories[:] = [name for name in subdirectories
                                  if name != "__pycache__" and current / name != source / "kernel/.pixi"]
            require(all(not (current / name).is_symlink() for name in subdirectories),
                    "untracked symbolic import directory under source")
            for filename in files:
                if Path(filename).suffix in (".mojo", ".py"):
                    relative = (current / filename).relative_to(source).as_posix().encode("utf-8")
                    require(relative in tree, "extra importable source file: " + relative.decode("utf-8"))

    contents_digest = hashlib.sha256()
    total_bytes = 0
    reference_files = {f["path"]: f for f in manifest["reference_files"]}
    require(len(reference_files) == len(manifest["reference_files"]), "duplicate reference file")
    checked_references = []
    for raw_path, (mode, oid) in tree.items():
        name = raw_path.decode("utf-8")
        path = source / name
        require(path.exists() and not path.is_symlink(), "missing or substituted tracked file: " + name)
        require(stat.S_ISREG(path.stat().st_mode), "non-regular tracked source file: " + name)
        require(bool(path.stat().st_mode & stat.S_IXUSR) == (mode == b"100755"),
                "tracked executable mode differs: " + name)
        data = path.read_bytes()
        check_blob(data, oid.decode("ascii"), name)
        digest = sha256(data)
        # Same framing as the committed manifest; ls-tree supplies canonical
        # path order. This additionally binds all bytes with SHA-256.
        contents_digest.update(mode + b" " + oid + b"\t" + raw_path + b"\0")
        contents_digest.update(bytes.fromhex(digest) + b"\0")
        total_bytes += len(data)
        if name in reference_files:
            wanted = reference_files[name]
            require(wanted["git_blob"] == oid.decode("ascii"), "reference Git identity differs: " + name)
            require(wanted["sha256"] == digest and wanted["bytes"] == len(data),
                    "reference source digest differs: " + name)
            checked_references.append(name)
    require(len(checked_references) == len(reference_files), "reference source file omitted from Git tree")
    require(total_bytes == expected["tracked_bytes"], "tracked source byte inventory changed")
    require(contents_digest.hexdigest() == expected["tracked_contents_sha256"],
            "full tracked-source SHA-256 digest changed")
    return {
        "expected_commit": expected["commit"],
        "observed_commit": actual_head,
        "expected_tree": expected["tree"],
        "observed_tree": actual_tree,
        "observed_parents": parents,
        "tracked_files_checked": len(tree),
        "tracked_bytes_checked": total_bytes,
        "tracked_contents_sha256": contents_digest.hexdigest(),
        "reference_files_checked": checked_references,
        "working_tree_matches_pinned_tree": True,
        "extra_importable_source_files": 0,
        "source_scan_exclusions": ["kernel/.pixi", "__pycache__ directories"],
        "authentication_scope": "Git object identity and source-byte integrity; unsigned commit, not a geometric proof",
    }


def integers(line: str, tag: str, count: int) -> list[int]:
    fields = line.split(" ")
    require(len(fields) == count + 1 and fields[0] == tag,
            "packet record shape: expected " + tag)
    require(all(INTEGER.fullmatch(token) for token in fields[1:]), "noncanonical packet integer")
    return [int(token) for token in fields[1:]]


def authenticate_packet(data: bytes, manifest: dict[str, Any], label: str) -> dict[str, Any]:
    """Check framing and declared facts, then the exact historical byte digest.

    This does not prove positivity from the three coefficient coordinates,
    nor reconstruct graph edges that are not fields in this packet format.
    Those checks belong to the separately replayed, source-pinned producers.
    """
    require(data.endswith(b"\n") and b"\r" not in data, label + ": noncanonical line endings")
    try:
        lines = data.decode("ascii").splitlines()
    except UnicodeDecodeError as exc:
        raise Refusal(label + ": non-ASCII packet") from exc
    require(len(lines) == manifest["packet"]["records"], label + ": missing or extra packet records")
    require(lines[0] == "schema " + manifest["packet"]["schema"], label + ": packet schema")
    cursor = 1
    declared_states = declared_occurrences = declared_losses = source_blocks = source_vertices = 0
    summary_lines: list[str] = []
    for graph in manifest["graphs"]:
        source_id = graph["source"]
        deficits = []
        for vertex in range(graph["states"]):
            fields = integers(lines[cursor], "row", 8)
            require(fields[:2] == [source_id, vertex], label + ": omitted, duplicated, or reordered row")
            require(fields[2:5] != [0, 0, 0], label + ": zero mass coefficient row")
            deficits.append(fields[5:8])
            cursor += 1
        # Nonzero is only the serialized declaration of a losing row. Exact
        # positivity was checked by the native/oracle real-sign certificates.
        losses = sum(row != [0, 0, 0] for row in deficits)
        require(losses == graph["positive_deficit_rows"], label + ": declared deficit inventory changed")
        for block in graph["source_blocks"]:
            fields = integers(lines[cursor], "block", 4)
            require(fields == [source_id, block["component"], block["size"], block["losing_vertex"]],
                    label + ": source component or losing witness declaration changed")
            witness = block["losing_vertex"]
            require(0 <= witness < len(deficits) and deficits[witness] != [0, 0, 0],
                    label + ": source witness has no declared deficit")
            summary_lines.append(lines[cursor])
            cursor += 1
            source_blocks += 1
            source_vertices += block["size"]
        fields = integers(lines[cursor], "graph", 5)
        require(fields == [source_id, graph["states"], graph["retained_occurrences"],
                           graph["positive_deficit_rows"], len(graph["source_blocks"])],
                label + ": graph summary declaration changed")
        summary_lines.append(lines[cursor])
        cursor += 1
        require(len(deficits) >= 3, label + ": declared roots are absent from row inventory")
        declared_states += graph["states"]
        declared_occurrences += graph["retained_occurrences"]
        declared_losses += losses
    require(cursor == len(lines), label + ": trailing packet records")
    require(declared_states == 43915 and declared_occurrences == 253395 and declared_losses == 3508,
            label + ": aggregate graph declarations changed")
    require(source_blocks == 12 and source_vertices == 2648, label + ": source component totals changed")
    summary_digest = sha256(("\n".join(summary_lines) + "\n").encode("ascii"))
    require(summary_digest == manifest["packet"]["summary_sha256"], label + ": source summary digest changed")
    require(len(data) == manifest["packet"]["bytes"], label + ": packet byte count changed")
    require(sha256(data) == manifest["packet"]["sha256"], label + ": packet digest changed")
    return {
        "schema": manifest["packet"]["schema"],
        "sha256": sha256(data),
        "bytes": len(data),
        "records": len(lines),
        "declared_states": declared_states,
        "declared_retained_occurrences": declared_occurrences,
        "declared_positive_deficit_rows": declared_losses,
        "declared_source_sccs": source_blocks,
        "declared_source_scc_vertices": source_vertices,
        "declared_roots": 36,
        "root_vertex_ids_per_graph": [0, 1, 2],
        "all_declared_source_witness_rows_present_and_nonzero": True,
        "summary_sha256": summary_digest,
    }


def packet_pair(native: bytes, oracle: bytes) -> None:
    require(native == oracle, "native and independent oracle exports differ byte for byte")


def self_test(packet: bytes, manifest: dict[str, Any]) -> list[dict[str, str]]:
    """Receipt mutations must be refused without changing the source checkout."""
    results = []

    def rejects(name: str, operation: Any) -> None:
        try:
            operation()
        except Refusal as exc:
            results.append({"control": name, "result": "refused", "reason": str(exc)})
            return
        raise Refusal("self-test incorrectly accepted " + name)

    lines = packet.splitlines(keepends=True)
    rejects("omitted-row", lambda: authenticate_packet(b"".join(lines[:1] + lines[2:]), manifest, "control"))
    duplicated = lines.copy()
    duplicated[2] = duplicated[1]
    rejects("duplicated-row", lambda: authenticate_packet(b"".join(duplicated), manifest, "control"))
    omitted_block = [line for line in lines if not line.startswith(b"block 0 ")]
    rejects("omitted-source-witness", lambda: authenticate_packet(b"".join(omitted_block), manifest, "control"))
    wrong_witness = packet.replace(b"block 0 1 1 2\n", b"block 0 1 1 0\n", 1)
    rejects("changed-source-witness", lambda: authenticate_packet(wrong_witness, manifest, "control"))
    changed_mass = packet.replace(b"row 0 0 1 0 0 0 0 0\n", b"row 0 0 2 0 0 0 0 0\n", 1)
    rejects("same-size-mass-byte-mutation", lambda: authenticate_packet(changed_mass, manifest, "control"))
    zero_mass = packet.replace(b"row 0 0 1 0 0 0 0 0\n", b"row 0 0 0 0 0 0 0 0\n", 1)
    rejects("zero-mass-row", lambda: authenticate_packet(zero_mass, manifest, "control"))
    rejects("native-oracle-mismatch", lambda: packet_pair(packet, changed_mass))
    # The same helper is used for every real tracked file, even a file whose
    # index has assume-unchanged or skip-worktree set.
    original = b"pinned source\n"
    original_oid = hashlib.sha1(b"blob " + str(len(original)).encode("ascii") + b"\0" + original).hexdigest()
    check_blob(original, original_oid, "control")
    rejects("tracked-source-byte-mutation", lambda: check_blob(b"mutant source\n", original_oid, "control"))
    require(len(results) == 8, "negative-control inventory")
    return results


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True, help="checkout at the exact PR #515 source revision")
    parser.add_argument("--native", type=Path, required=True, help="fresh canonical Mojo packet")
    parser.add_argument("--oracle", type=Path, required=True, help="independently produced Python packet")
    parser.add_argument("--output", type=Path, required=True, help="write the source-binding receipt")
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--self-test", action="store_true", help="also require receipt mutation controls to be refused")
    args = parser.parse_args()
    output_allowed = False
    try:
        inputs = {args.manifest.resolve(), args.native.resolve(), args.oracle.resolve()}
        output_allowed = (args.output.resolve() not in inputs
                          and not args.output.resolve().is_relative_to(args.source.resolve()))
        require(output_allowed, "receipt output must be outside the source checkout and distinct from all inputs")
        checker_path = Path(__file__).resolve()
        checker_snapshot = checker_path.read_bytes()
        manifest_snapshot = args.manifest.read_bytes()
        manifest = load_manifest(args.manifest, manifest_snapshot)
        source = authenticate_source(args.source.resolve(), manifest)
        native = args.native.read_bytes()
        oracle = args.oracle.read_bytes()
        packet_pair(native, oracle)
        packet = authenticate_packet(native, manifest, "native and oracle")
        controls = self_test(native, manifest) if args.self_test else []
        status_args = ["status", "--porcelain", "--untracked-files=normal", "--", "."]
        excluded_checkout = None
        if args.source.resolve().is_relative_to(ROOT):
            excluded_checkout = args.source.resolve().relative_to(ROOT).as_posix()
            status_args.append(":(exclude)" + excluded_checkout)
        kernel_revision = {
            "commit": git(ROOT, "rev-parse", "HEAD").decode("ascii").strip(),
            "tree": git(ROOT, "rev-parse", "HEAD^{tree}").decode("ascii").strip(),
            "worktree_dirty": bool(git(ROOT, *status_args)),
            "status_excludes_nested_pinned_source_checkout": excluded_checkout,
        }
        require(args.manifest.read_bytes() == manifest_snapshot, "manifest changed during validation")
        require(checker_path.read_bytes() == checker_snapshot, "checker changed during validation")
        receipt = {
            "schema": "physical-mass-source-refinement-receipt-v1",
            "status": "passed-source-binding-and-packet-parity",
            "manifest_sha256": sha256(manifest_snapshot),
            "checker_sha256": sha256(checker_snapshot),
            "kernel_revision": kernel_revision,
            "source": source,
            "packet": packet,
            "native_oracle_byte_equality": True,
            "negative_controls": controls,
            "proof_boundary": {
                "producer_execution": "Separate workflow steps must run both pinned producers; this checker authenticates supplied outputs, not execution history",
                "finite_arithmetic_and_sccs": "Evidence from pinned native reconstruction and independent oracle, not reimplemented here",
                "lean_implication": "Audited in a separate Lean job; this receipt does not run or instantiate Lean",
                "concrete_lean_instantiation": "OPEN: no kernel-checked decoding of this physical-mass packet and graph into the abstract hypotheses",
                "geometric_realization_and_haar_supersolution": "OPEN as a Lean refinement: written source arguments are not formalized by digest checks",
                "uniform_conservative_class_exclusion": "OPEN beyond the twelve declared source graphs",
                "one_step_sync_newborn_bridge": "OPEN for the uniform issue #461 target",
                "general_C4_and_PSC": "OPEN",
            },
        }
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(json.dumps({"status": receipt["status"], "source_commit": SOURCE_HEAD,
                          "packet_sha256": packet["sha256"], "tracked_files": source["tracked_files_checked"],
                          "records": packet["records"], "negative_controls": len(controls),
                          "receipt": str(args.output)}, sort_keys=True))
        return 0
    except (Refusal, OSError, ValueError, KeyError, TypeError, IndexError) as exc:
        # A failed rerun must not leave a stale successful receipt at --output.
        # Inputs are not modified. The explicitly requested output is a run
        # receipt, not a source archive.
        if output_allowed:
            try:
                args.output.parent.mkdir(parents=True, exist_ok=True)
                args.output.write_text(json.dumps({
                    "schema": "physical-mass-source-refinement-receipt-v1",
                    "status": "refused",
                    "expected_source_commit": SOURCE_HEAD,
                    "reason": str(exc),
                }, indent=2, sort_keys=True) + "\n", encoding="utf-8")
            except OSError:
                pass
        print("physical mass refinement REFUSED: " + str(exc), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
