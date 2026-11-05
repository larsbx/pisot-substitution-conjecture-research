#!/usr/bin/env python3
"""Replay generated Lean proofs and bind their emitted data to the native oracle.

Provenance orchestration only. Graph construction lives in Mojo, finite
soundness in Lean, and independent packet reconstruction in the existing oracle.
The caller supplies a freshly isolated, pinned, compiled Lean workspace.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


class ReplayIncomplete(ValueError):
    pass


def audit_source(index: int) -> str:
    return f'''import Source{index}
import Lean.Util.CollectAxioms
example : PscVerif.OverlapGenerated.Source{index}.packet.check = true :=
  PscVerif.OverlapGenerated.Source{index}.accepted
example : (PscVerif.OverlapGenerated.Source{index}.packet.toCertificate
  (PscVerif.OverlapGenerated.Source{index}.packet.check_iff.mp
    PscVerif.OverlapGenerated.Source{index}.accepted)).check = true :=
  PscVerif.OverlapGenerated.Source{index}.typed_accepted
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `Source{index} | throwError "Missing generated module"
  let data := env.header.moduleData[idx.toNat]!
  let mut count := 0
  let mut proofs := 0
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for info in data.constants do
    let name := info.name
    if info.isAxiom then throwError "Local generated axiom"
    let axs ← collectAxioms name
    for ax in axs do
      if !allowed.contains ax then throwError "Nonstandard generated axiom"
    count := count+1
    if info.isTheorem then proofs := proofs+1
    let names := String.intercalate "," (axs.toList.map toString)
    liftIO <| IO.println s!"PSC_PACKET_AXIOMS {index}\\t{{name}}\\t{{names}}"
  if proofs < 2 then throwError "Missing generated proofs"
  liftIO <| IO.println s!"PSC_PACKET_AUDIT_COMPLETE {index}\\t{{count}}\\t{{proofs}}"
def main : IO Unit := PscVerif.OverlapPacket.Packet.emit PscVerif.OverlapGenerated.Source{index}.packet
'''


def extract_packet(index: int, log: Path, packet) -> dict:
    declarations = set()
    completion = None
    graph_seen = False
    for line in log.read_text().splitlines():
        if line.startswith(f"PSC_PACKET_AXIOMS {index}\t"):
            if completion is not None:
                raise ReplayIncomplete("declaration after audit completion")
            fields = line.split("\t")
            if len(fields) != 3 or not fields[1] or fields[1] in declarations:
                raise ReplayIncomplete("malformed or duplicate generated declaration")
            if set(filter(None, fields[2].split(","))) - ALLOWED:
                raise ReplayIncomplete("nonstandard generated axiom")
            declarations.add(fields[1])
        elif line.startswith(f"PSC_PACKET_AUDIT_COMPLETE {index}\t"):
            fields = line.split("\t")
            if len(fields) != 3 or completion is not None:
                raise ReplayIncomplete("malformed or duplicate audit completion")
            completion = tuple(map(int, fields[1:]))
        elif line.startswith(("graph ", "node ", "row ")):
            if completion is None:
                raise ReplayIncomplete("packet before generated audit completion")
            if line.startswith("graph "):
                if graph_seen or line.split()[1] != str(index):
                    raise ReplayIncomplete("wrong or duplicate source graph")
                graph_seen = True
            elif not graph_seen:
                raise ReplayIncomplete("record before source graph")
            packet.write(line + "\n")
        elif line.strip():
            raise ReplayIncomplete("unexpected Lean output: " + line[:160])
    expected = {f"PscVerif.OverlapGenerated.Source{index}.accepted",
                f"PscVerif.OverlapGenerated.Source{index}.typed_accepted"}
    if (not graph_seen or completion is None or completion[0] != len(declarations)
            or not 2 <= completion[1] <= completion[0] or not expected <= declarations):
        raise ReplayIncomplete("missing concrete proofs, graph or audit receipt")
    return {"declarations": completion[0], "theorem_declarations": completion[1]}


def validate_negative_control(project: Path, root: Path, output: Path, pin: str, lake_path: str) -> None:
    """Reject standard-axiom declarations with the right names but wrong types."""
    control = output / "audit-negative-control"
    control.mkdir()
    source = control / "Source0.lean"
    source.write_bytes((root / "tests/fixtures/c4_overlap_bad_binding.lean").read_bytes())
    audit = control / "Audit0.lean"
    audit.write_text(audit_source(0))
    with (control / "compile.log").open("w") as log:
        subprocess.run(["elan", "run", pin, "lake", "--no-cache", "env", "lean",
                        "--root="+str(control), "-o", str(source.with_suffix(".olean")), str(source)],
                       cwd=project, stdout=log, stderr=subprocess.STDOUT, check=True, timeout=300)
    env = {**os.environ, "LEAN_PATH": str(control)+os.pathsep+lake_path}
    result = subprocess.run(["elan", "run", pin, "lean", "--run", str(audit)],
                            cwd=project, env=env, capture_output=True, text=True, timeout=300)
    diagnostics = result.stdout+result.stderr
    (control / "audit.log").write_text(diagnostics)
    if result.returncode == 0 or "type mismatch" not in diagnostics.lower() or "accepted" not in diagnostics:
        raise ReplayIncomplete("wrong-proof-type calibration did not refuse for the expected reason")
    (control / "receipt.json").write_text(json.dumps({
        "fixture_compiles": True, "independent_binding_audit_refuses": True,
        "reason": "accepted declarations prove True rather than the packet check",
        "fixture_sha256": hashlib.sha256(source.read_bytes()).hexdigest()}, indent=2)+"\n")


def run(exporter: Path, project: Path, root: Path, output: Path, source_index: int | None = None) -> dict:
    if source_index is not None and not 0 <= source_index < 18:
        raise ReplayIncomplete("unsupported source-order index")
    output.mkdir(parents=True, exist_ok=True)
    if any(output.iterdir()):
        raise ReplayIncomplete("refuse stale or nonempty replay directory")
    pin = (project / "lean-toolchain").read_text().strip()
    lake_path = subprocess.run(["elan", "run", pin, "lake", "--no-cache", "env", "printenv", "LEAN_PATH"],
                               cwd=project, capture_output=True, text=True, check=True).stdout.strip()
    audit_env = {**os.environ, "LEAN_PATH": str(output) + os.pathsep + lake_path}
    validate_negative_control(project, root, output, pin, lake_path)
    sources = []
    combined = output / "lean-emitted-packet.txt"
    with combined.open("w") as packet:
        packet.write("schema c4-pair-overlap-class-v1\n")
        for index in (range(18) if source_index is None else (source_index,)):
            started = time.monotonic()
            source = output / f"Source{index}.lean"
            log = output / f"Source{index}.log"
            with source.open("w") as stream, (output / f"Source{index}.mojo.log").open("w") as err:
                subprocess.run([str(exporter), str(index)], stdout=stream, stderr=err,
                               check=True, timeout=300)
            with log.open("w") as stream, (output / f"Source{index}.stderr").open("w") as err:
                subprocess.run(["elan", "run", pin, "lake", "--no-cache", "env", "lean",
                                "--root=" + str(output), "-o", str(source.with_suffix(".olean")), str(source)],
                               cwd=project, stdout=stream, stderr=err,
                               check=True, timeout=900)
            # Import the freshly kernel-checked module. Lean's export extension
            # caches transitive axiom sets with one shared traversal; auditing
            # every current declaration separately before export is quadratic.
            audit = output / f"Audit{index}.lean"
            audit.write_text(audit_source(index))
            with log.open("a") as stream, (output / f"Audit{index}.stderr").open("w") as err:
                subprocess.run(["elan", "run", pin, "lean", "--run", str(audit)], cwd=project,
                               env=audit_env, stdout=stream, stderr=err, check=True, timeout=300)
            audit = extract_packet(index, log, packet)
            sources.append({"source": index, "lean_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                            "seconds": round(time.monotonic()-started, 3),
                            "audit_and_packet_log_sha256": hashlib.sha256(log.read_bytes()).hexdigest(), **audit})
            print(f"Lean source {index}: kernel acceptance, typed binding and generated axiom audit passed",
                  flush=True)
    if source_index is None:
        oracle = subprocess.run([sys.executable, str(root / "oracles/python/c4_pair_overlap_class.py"),
                                 "--native", str(combined)], capture_output=True, text=True,
                                check=True, timeout=600)
        actual = json.loads(oracle.stdout)
        expected = json.loads((root / "evidence/c4-pair-overlap-class-2026-11-05/receipt.json").read_text())
        if actual != expected:
            raise ReplayIncomplete("full Lean-emitted/native-reference receipt mismatch")
        (output / "oracle-receipt.json").write_text(oracle.stdout)
    else:
        # Budgeted single-source development replay, explicitly no class verdict.
        # Reuse the independent oracle's exact graph/packet/receipt functions.
        sys.path.insert(0, str(root / "oracles/python"))
        import c4_pair_overlap_class as oracle_module
        graph, weights, sweeps, _ = oracle_module.reference(source_index)
        expected_lines = ["schema c4-pair-overlap-class-v1",
                          *oracle_module.packet_lines(graph, weights, sweeps)]
        if combined.read_text().splitlines() != expected_lines:
            raise ReplayIncomplete("single-source full packet mismatch")
        summary = oracle_module.summary(source_index)
        committed = json.loads((root / "evidence/c4-pair-overlap-class-2026-11-05/receipt.json").read_text())
        if summary != committed["sources"][source_index]:
            raise ReplayIncomplete("single-source committed receipt mismatch")
        actual = {"sources": [summary]}
        (output / "oracle-receipt.json").write_text(json.dumps(actual, indent=2)+"\n")
    result = {"schema": "c4-overlap-lean-packet-replay-v1", "sources_verified": len(sources),
              "all_18_sources_verified": source_index is None,
              "states": sum(s["states"] for s in actual["sources"]),
              "occurrence_edges": sum(s["occurrence_edges"] for s in actual["sources"]),
              "kernel_evaluation": "decide +kernel; no native_decide",
              "geometry_formalized": False,
              "exporter_sha256": hashlib.sha256(exporter.read_bytes()).hexdigest(),
              "generic_packet_source_sha256": hashlib.sha256((project / "PscVerif/OverlapPacket.lean").read_bytes()).hexdigest(),
              "complete_packet_sha256": hashlib.sha256(combined.read_bytes()).hexdigest(),
              "sources": sources}
    (output / "receipt.json").write_text(json.dumps(result, indent=2)+"\n")
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exporter", type=Path, required=True)
    parser.add_argument("--project", type=Path, required=True)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--source", type=int, choices=range(18),
                        help="Single-source development replay; never issues a class verdict")
    args = parser.parse_args()
    try:
        result = run(args.exporter.resolve(), args.project.resolve(), args.root.resolve(), args.output.resolve(), args.source)
    except (ReplayIncomplete, subprocess.CalledProcessError, subprocess.TimeoutExpired) as error:
        raise SystemExit(f"Lean packet replay incomplete; no class verdict: {error}") from error
    print(json.dumps({k: v for k, v in result.items() if k != "sources"}, indent=2))


if __name__ == "__main__":
    main()
