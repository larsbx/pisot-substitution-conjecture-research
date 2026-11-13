#!/usr/bin/env python3
"""Compile original archived payloads, audit their types/axioms, and replay all data.

This file orchestrates provenance. Mathematical graph construction is canonical
Mojo, finite soundness is Lean, and full reconstruction is the Python oracle.
The caller must supply the freshly built isolated pinned Lean workspace.
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
COUNTS = (7150, 7083)
PROOFS = {"valid", "accepted", "typed_accepted", "domain_iff", "roots_null", "ancestors_null",
          "no_strict_system", "seed_terminates", "reachable_terminates"}
TERMINATION_PROOFS = ("seed_terminates", "reachable_terminates")
RECORDS = {"graph", "image", "digit", "node", "row", "slot", "packed", "lookup"}


class ReplayIncomplete(ValueError):
    pass


def exclusion_type_check(index: int) -> str:
    """Check the closed exclusion at the literal source fixture, with no Haar premise."""
    if index not in (0, 1):
        raise ReplayIncomplete("unsupported original fixture")
    ns = f"Psc.ArchivedPayloadGenerated.Source{index}"
    return f'''example (C : Finset Psc.OccurrenceTransport.WordPair) :
    ¬ Psc.StrictSystem.StrictSystem (Psc.NamedPrefixCompact.substitution ({index} : Fin 2)) C :=
  {ns}.no_strict_system C
'''


def termination_type_check(index: int, name: str) -> str:
    """Bind each endpoint to its literal fixture without a caller validity premise."""
    if index not in (0, 1):
        raise ReplayIncomplete("unsupported original fixture")
    if name not in TERMINATION_PROOFS:
        raise ReplayIncomplete("unsupported termination endpoint")
    ns = f"Psc.ArchivedPayloadGenerated.Source{index}"
    sigma = f"Psc.NamedPrefixCompact.substitution ({index} : Fin 2)"
    if name == "seed_terminates":
        premise = "T ∈ (Psc.Descendants.seeds : Finset Psc.OccurrenceTransport.WordPair)"
    else:
        premise = f"T ∈ Psc.Descendants.bpaStatesNC ({sigma})"
    return f'''example {{T : Psc.OccurrenceTransport.WordPair}}
    (hT : {premise}) :
    Psc.StrictSystem.TerminatesWithCoincidence ({sigma}) T :=
  {ns}.{name} hT
'''


def audit_source(index: int) -> str:
    if index not in (0, 1):
        raise ReplayIncomplete("unsupported original fixture")
    ns = f"Psc.ArchivedPayloadGenerated.Source{index}"
    return f'''import Source{index}
import PscVerif.ArchivedPayloadEmit
import Lean.Util.CollectAxioms
open Set MeasureTheory
open Psc.OccurrenceTransport Psc.OccurrenceInverse Psc.OccurrenceGraphBinding
open Psc.OccurrencePiece Psc.OccurrenceResidue
open Psc.NamedStableChart Psc.NamedPrefixCompact Psc.NamedProductHaar
open Psc.ArchivedGraphRefinement
example : {ns}.packet.fixture = {index} := rfl
example : {ns}.packet.count = {COUNTS[index]} := rfl
example : {ns}.packet.Valid := {ns}.valid
example : {ns}.packet.check = true := {ns}.accepted
example : ({ns}.packet.toCertificate {ns}.valid).check = true := {ns}.typed_accepted
example (u : Psc.OccurrenceTransport.Packet) :
    (u ∈ orderedLift {ns}.packet.states ∧
      (overlap (ambientStar (substitution {ns}.packet.fixture) piZ)
        (tiles {ns}.packet.fixture) u).Nonempty) ↔
    (Ancestry (iterateImages (substitution {ns}.packet.fixture) 2) ArchivedRoot u ∧
      (overlap (ambientStar (substitution {ns}.packet.fixture) piZ)
        (tiles {ns}.packet.fixture) u).Nonempty) := {ns}.domain_iff u
example (ν : Measure (H (substitution {ns}.packet.fixture)))
    [ν.IsAddHaarMeasure] [IsProbabilityMeasure ν] :
    ∀ k, (volume.prod ν)
      (overlap (ambientStar (substitution {ns}.packet.fixture) piZ)
        (tiles {ns}.packet.fixture) (archivedRoot k)) = 0 := {ns}.roots_null ν
example (ν : Measure (H (substitution {ns}.packet.fixture)))
    [ν.IsAddHaarMeasure] [IsProbabilityMeasure ν]
    (u : Psc.OccurrenceTransport.Packet)
    (hu : Ancestry (iterateImages (substitution {ns}.packet.fixture) 2) ArchivedRoot u) :
    (volume.prod ν)
      (overlap (ambientStar (substitution {ns}.packet.fixture) piZ)
        (tiles {ns}.packet.fixture) u) = 0 := {ns}.ancestors_null ν u hu
{exclusion_type_check(index)}
{termination_type_check(index, "seed_terminates")}
{termination_type_check(index, "reachable_terminates")}
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
    count := count + 1
    if info.isTheorem then proofs := proofs + 1
    let names := String.intercalate "," (axs.toList.map toString)
    liftIO <| IO.println s!"PSC_ARCHIVED_AXIOMS {index}\\t{{name}}\\t{{names}}"
  if proofs < {len(PROOFS)} then throwError "Missing concrete semantic proofs"
  liftIO <| IO.println s!"PSC_ARCHIVED_AUDIT_COMPLETE {index}\\t{{count}}\\t{{proofs}}"
def main : IO Unit := {ns}.packet.emit
'''


def extract_packet(index: int, log: Path, packet) -> dict:
    """Strictly parse a fresh compiled-module audit, never a name-only receipt."""
    if index not in (0, 1):
        raise ReplayIncomplete("unsupported original fixture")
    declarations: set[str] = set()
    completion = None
    graph_seen = False
    kinds: set[str] = set()
    for line in log.read_text().splitlines():
        if line.startswith(f"PSC_ARCHIVED_AXIOMS {index}\t"):
            if completion is not None:
                raise ReplayIncomplete("declaration after audit completion")
            fields = line.split("\t")
            if len(fields) != 3 or not fields[1] or fields[1] in declarations:
                raise ReplayIncomplete("malformed or duplicate declaration")
            if set(filter(None, fields[2].split(","))) - ALLOWED:
                raise ReplayIncomplete("nonstandard transitive axiom")
            declarations.add(fields[1])
        elif line.startswith(f"PSC_ARCHIVED_AUDIT_COMPLETE {index}\t"):
            fields = line.split("\t")
            if len(fields) != 3 or completion is not None:
                raise ReplayIncomplete("malformed or duplicate completion")
            try:
                completion = tuple(map(int, fields[1:]))
            except ValueError as exc:
                raise ReplayIncomplete("nonnumeric completion") from exc
        elif line.split(" ", 1)[0] in RECORDS:
            fields = line.split()
            if completion is None or len(fields) < 2 or fields[1] != str(index):
                raise ReplayIncomplete("unaudited or wrong-fixture payload record")
            if fields[0] == "graph":
                if graph_seen:
                    raise ReplayIncomplete("duplicate source graph")
                graph_seen = True
            elif not graph_seen:
                raise ReplayIncomplete("record before graph")
            kinds.add(fields[0])
            packet.write(line + "\n")
        elif line.strip():
            raise ReplayIncomplete("unexpected audit output: " + line[:160])
    expected = {f"Psc.ArchivedPayloadGenerated.Source{index}.{name}" for name in PROOFS}
    if (not graph_seen or kinds != RECORDS or completion is None
            or completion[0] != len(declarations)
            or not len(PROOFS) <= completion[1] <= completion[0]
            or not expected <= declarations):
        raise ReplayIncomplete("missing concrete proofs, complete packet or audit receipt")
    return {"declarations": completion[0], "theorem_declarations": completion[1]}


def validate_negative_control(project: Path, root: Path, output: Path, pin: str,
                              lake_path: str) -> None:
    """Compile harmless right-name/wrong-type declarations and reject their use."""
    control = output / "wrong-proof-type-control"
    control.mkdir()
    source = control / "Source0.lean"
    source.write_bytes((root / "tests/fixtures/c4_archived_bad_binding.lean").read_bytes())
    audit = control / "Audit0.lean"
    audit.write_text(audit_source(0))
    with (control / "compile.log").open("w") as log:
        subprocess.run(["elan", "run", pin, "lake", "--no-cache", "env", "lean",
                        "--root=" + str(control), "-o", str(source.with_suffix(".olean")), str(source)],
                       cwd=project, stdout=log, stderr=subprocess.STDOUT, check=True, timeout=600)
    env = {**os.environ, "LEAN_PATH": str(control) + os.pathsep + lake_path}
    result = subprocess.run(["elan", "run", pin, "lean", "--run", str(audit)],
                            cwd=project, env=env, capture_output=True, text=True, timeout=600)
    diagnostics = result.stdout + result.stderr
    (control / "audit.log").write_text(diagnostics)
    if result.returncode == 0 or "type mismatch" not in diagnostics.lower() or "accepted" not in diagnostics:
        raise ReplayIncomplete("wrong-proof-type control did not refuse for the expected reason")
    # Isolate the new obligation so failures of the earlier wrong-type proofs
    # cannot make this exclusion check appear to have been reached.
    exclusion_audit = control / "ExclusionAudit0.lean"
    exclusion_audit.write_text("import Source0\n" + exclusion_type_check(0))
    exclusion_result = subprocess.run(["elan", "run", pin, "lean", str(exclusion_audit)],
                                      cwd=project, env=env, capture_output=True, text=True, timeout=600)
    exclusion_diagnostics = exclusion_result.stdout + exclusion_result.stderr
    (control / "exclusion-audit.log").write_text(exclusion_diagnostics)
    if (exclusion_result.returncode == 0 or "type mismatch" not in exclusion_diagnostics.lower()
            or "no_strict_system" not in exclusion_diagnostics):
        raise ReplayIncomplete("wrong-type strict-system exclusion did not refuse for the expected reason")
    # Compile each endpoint use in its own module. An earlier rejected proof
    # must not earn credit for a termination type check that was never reached.
    termination_controls = {}
    for name in TERMINATION_PROOFS:
        endpoint_audit = control / f"{name}_audit.lean"
        endpoint_audit.write_text("import Source0\n" + termination_type_check(0, name))
        endpoint_result = subprocess.run(["elan", "run", pin, "lean", str(endpoint_audit)],
                                         cwd=project, env=env, capture_output=True, text=True, timeout=600)
        endpoint_diagnostics = endpoint_result.stdout + endpoint_result.stderr
        (control / f"{name}-audit.log").write_text(endpoint_diagnostics)
        if (endpoint_result.returncode == 0 or "type mismatch" not in endpoint_diagnostics.lower()
                or name not in endpoint_diagnostics):
            raise ReplayIncomplete(f"wrong-type {name} did not refuse for the expected reason")
        termination_controls[f"{name}_wrong_type_refused"] = True
    (control / "receipt.json").write_text(json.dumps({
        "fixture_compiles": True, "typed_import_refuses": True,
        "no_strict_system_wrong_type_refused": True,
        **termination_controls,
        "reason": "right-name declarations prove True instead of the required checked propositions",
        "fixture_sha256": hashlib.sha256(source.read_bytes()).hexdigest()}, indent=2) + "\n")


def run(exporter: Path, project: Path, root: Path, output: Path,
        fixture: int | None = None) -> dict:
    if fixture is not None and fixture not in (0, 1):
        raise ReplayIncomplete("unsupported original fixture")
    output.mkdir(parents=True, exist_ok=True)
    if any(output.iterdir()):
        raise ReplayIncomplete("refuse stale or nonempty replay directory")
    pin = (project / "lean-toolchain").read_text().strip()
    lake_path = subprocess.check_output(
        ["elan", "run", pin, "lake", "--no-cache", "env", "printenv", "LEAN_PATH"],
        cwd=project, text=True).strip()
    audit_env = {**os.environ, "LEAN_PATH": str(output) + os.pathsep + lake_path}
    validate_negative_control(project, root, output, pin, lake_path)
    sources = []
    combined = output / "lean-emitted-payload.txt"
    with combined.open("w") as packet:
        packet.write("schema c4-archived-payload-v1\n")
        for index in ((0, 1) if fixture is None else (fixture,)):
            started = time.monotonic()
            source = output / f"Source{index}.lean"
            log = output / f"Audit{index}.log"
            with source.open("w") as stream, (output / f"Source{index}.exporter.log").open("w") as err:
                subprocess.run([str(exporter), str(index)], stdout=stream, stderr=err,
                               check=True, timeout=600)
            with (output / f"Source{index}.compile.log").open("w") as stream:
                subprocess.run(["elan", "run", pin, "lake", "--no-cache", "env", "lean",
                                "--root=" + str(output), "-o", str(source.with_suffix(".olean")), str(source)],
                               cwd=project, stdout=stream, stderr=subprocess.STDOUT,
                               check=True, timeout=7200)
            audit = output / f"Audit{index}.lean"
            audit.write_text(audit_source(index))
            with log.open("w") as stream, (output / f"Audit{index}.stderr").open("w") as err:
                subprocess.run(["elan", "run", pin, "lean", "--run", str(audit)],
                               cwd=project, env=audit_env, stdout=stream, stderr=err,
                               check=True, timeout=1200)
            counts = extract_packet(index, log, packet)
            sources.append({"fixture": index, "lean_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                            "seconds": round(time.monotonic() - started, 3),
                            "audit_sha256": hashlib.sha256(log.read_bytes()).hexdigest(), **counts})
            print(f"Original fixture {index}: concrete kernel checks, geometric, exclusion and termination theorem types, and axiom audit passed",
                  flush=True)
    command = [sys.executable, str(root / "oracles/python/c4_archived_payload.py"), "--native", str(combined)]
    if fixture is not None:
        command += ["--fixture", str(fixture)]
    oracle = subprocess.run(command, capture_output=True, text=True, check=True, timeout=1200)
    actual = json.loads(oracle.stdout)
    indices = (0, 1) if fixture is None else (fixture,)
    archive = json.loads((root / "evidence/c4-pair-overlap-graph-2026-11-05/receipt.json").read_text())
    addressed_archive = json.loads((root /
        "evidence/c4-archived-graph-refinement-2026-11-11/native-oracle/receipt.json").read_text())
    emitted_digest = hashlib.sha256(combined.read_bytes()).hexdigest()
    if (actual.get("schema") != "c4-archived-payload-v1"
            or actual.get("all_two_original_fixtures_verified") is not (fixture is None)
            or actual.get("kernel_acceptance_supplied_by_this_oracle") is not False
            or actual.get("payload_sha256") != emitted_digest
            or [s.get("fixture") for s in actual.get("fixtures", [])] != list(indices)):
        raise ReplayIncomplete("wrong-scope or unbound independent oracle receipt")
    for index, summary in zip(indices, actual["fixtures"]):
        archived = archive["fixtures"][index]
        if (summary.get("states") != COUNTS[index]
                or summary.get("packed_rows") != COUNTS[index]
                or summary.get("lookup_nodes") != COUNTS[index]
                or summary.get("positional_edges") != (34826, 34853)[index]
                or summary.get("historical_graph_sha256") != archived["canonical_graph_sha256"]
                or summary.get("addressed_packet_sha256") !=
                    addressed_archive["fixtures"][index]["addressed_packet_sha256"]
                or summary.get("rate") != archived["rate"]
                or summary.get("radii") != [16, 8]):
            raise ReplayIncomplete("independent receipt does not bind the original archive")
    (output / "oracle-receipt.json").write_text(oracle.stdout)
    relative_sources = [
        "proof/PscVerif/PscVerif/NamedArchivedDigits.lean",
        "proof/PscVerif/PscVerif/ArchivedPayload.lean",
        "proof/PscVerif/PscVerif/ArchivedPayloadConsumer.lean",
        "proof/PscVerif/PscVerif/ArchivedPayloadEmit.lean",
        "proof/PscVerif/PscVerif/NamedPositiveOverlap.lean",
        "proof/PscVerif/PscVerif/NamedPositiveOverlapControls.lean",
        "proof/PscVerif/PscVerif/NamedStrictExclusion.lean",
        "proof/PscVerif/PscVerif/NamedStrictExclusionControls.lean",
        "proof/PscVerif/PscVerif/FiniteProductivity.lean",
        "proof/PscVerif/PscVerif/NamedFiniteProductivity.lean",
        "proof/PscVerif/PscVerif/ForwardCarrier.lean",
        "proof/PscVerif/PscVerif/FastForwardCarrier.lean",
        "proof/PscVerif/PscVerif/NamedForwardCarrierData0.lean",
        "proof/PscVerif/PscVerif/NamedForwardCarrierData1.lean",
        "proof/PscVerif/PscVerif/NamedForwardCarrier.lean",
        "tests/fixtures/c4_archived_bad_binding.lean",
        "kernel/psc/c4_archived_payload.mojo", "kernel/c4_archived_lean_export.mojo",
        "oracles/python/c4_archived_payload.py", "tools/replay_archived_payload_lean.py",
        "tools/check_lean.sh", "evidence/c4-pair-overlap-graph-2026-11-05/receipt.json",
        "evidence/c4-archived-graph-refinement-2026-11-11/native-oracle/receipt.json",
    ]
    source_hashes = {p: hashlib.sha256((root / p).read_bytes()).hexdigest() for p in relative_sources}
    for relative in relative_sources:
        if relative.startswith("proof/PscVerif/"):
            isolated = project / relative.removeprefix("proof/PscVerif/")
            if hashlib.sha256(isolated.read_bytes()).hexdigest() != source_hashes[relative]:
                raise ReplayIncomplete("isolated checker source differs from candidate source")
    result = {
        "schema": "c4-archived-payload-lean-replay-v1",
        "fixtures_verified": len(sources), "both_original_fixtures_verified": fixture is None,
        "scope": "original sharp-box rooted inverse ancestry, strict-system exclusion, and coincidence termination for every ordered swap seed and its actual ChildNC descendants of the verified named fixtures; no arbitrary unlisted block, general C4 or PSC claim",
        "semantic_proofs": sorted(PROOFS), "strict_system_exclusion_fixtures": list(indices),
        "seed_and_reachable_termination_fixtures": list(indices),
        "kernel_evaluation": "decide +kernel; generated proof types and all transitive axioms audited",
        "allowed_axioms": sorted(ALLOWED), "lean_toolchain": pin,
        "exporter_sha256": hashlib.sha256(exporter.read_bytes()).hexdigest(),
        "complete_emitted_payload_sha256": emitted_digest,
        "source_sha256": source_hashes, "sources": sources,
        "oracle_receipt_sha256": hashlib.sha256(oracle.stdout.encode()).hexdigest(),
        "oracle_schema": actual.get("schema"),
    }
    (output / "receipt.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exporter", type=Path, required=True)
    parser.add_argument("--project", type=Path, required=True)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--fixture", type=int, choices=(0, 1),
                        help="Single-fixture development check; never issues a two-fixture verdict")
    args = parser.parse_args()
    try:
        result = run(args.exporter.resolve(), args.project.resolve(), args.root.resolve(),
                     args.output.resolve(), args.fixture)
    except (ReplayIncomplete, subprocess.SubprocessError, OSError, ValueError) as exc:
        raise SystemExit("Original archived payload acceptance incomplete: " + str(exc)) from exc
    print(json.dumps({k: v for k, v in result.items() if k not in {"sources", "source_sha256"}}, indent=2))


if __name__ == "__main__":
    main()
