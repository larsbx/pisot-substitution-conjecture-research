"""Replay both completed named Mojo exports and mutate their literal contract.

These controls use completed native packets. An earlier fixture 0 length
refusal is inconclusive and cannot be used as a positive baseline.
Neither these tests nor the Python receipt assert Lean or productivity status.
"""

from copy import deepcopy
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

import pytest


ROOT = Path(__file__).resolve().parents[1]
ORACLE_PATH = ROOT / "oracles/python/check_forward_carrier.py"
EVIDENCE = ROOT / "evidence/c4-forward-carrier-2026-11-12"
PACKET_PATHS = tuple(EVIDENCE / f"fixture{fixture}.json" for fixture in range(2))
SPEC = importlib.util.spec_from_file_location("forward_carrier_oracle", ORACLE_PATH)
oracle = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(oracle)


@pytest.fixture(scope="module")
def completed_packets():
    # Establish the positive baseline outside every expected-refusal context.
    packets = []
    for fixture, path in enumerate(PACKET_PATHS):
        packet = oracle.parse_packet(path.read_bytes())
        result = oracle.validate_packet(packet)
        assert result["fixture"] == fixture
        packets.append(packet)
    return tuple(packets)


@pytest.fixture(scope="module", params=(0, 1))
def native_packet(completed_packets, request):
    return completed_packets[request.param]


@pytest.fixture
def packet(native_packet):
    return deepcopy(native_packet)


def pair(record):
    return tuple(record["top"]), tuple(record["bottom"])


def refresh_metadata(packet):
    pairs = [pair(state) for state in packet["states"]]
    packet["state_count"] = len(pairs)
    packet["normalized_state_count"] = len({min(p, p[::-1]) for p in pairs})
    packet["max_state_length"] = max(len(p[0]) for p in pairs)


def remove_state(packet, removed):
    # Keep all surviving indices valid so the test reaches the semantic
    # seed/orientation/exit obligation rather than an unrelated index refusal.
    mapping = {old: new for new, old in enumerate(
        i for i in range(len(packet["states"])) if i != removed)}
    packet["states"] = [state for i, state in enumerate(packet["states"])
                        if i != removed]
    for state in packet["states"]:
        state["children"] = [mapping[j] for j in state["children"] if j != removed]
    refresh_metadata(packet)


def test_completed_native_export_has_source_bound_limited_receipt(native_packet):
    raw = PACKET_PATHS[native_packet["fixture"]].read_bytes()
    result = oracle.verify_bytes(raw)
    assert result["source_sha256"] == hashlib.sha256(raw).hexdigest()
    assert result["state_count"] == len(native_packet["states"])
    assert result["ordered_child_occurrences"] == sum(
        len(state["children"]) for state in native_packet["states"])
    assert result["ordered_seed_count"] == 6
    assert result["repeated_child_occurrences"] > 0
    assert result["literal_rows_verified"]
    assert result["finite_closed_carrier_verified"]
    assert not result["exact_reachability_claimed"]
    assert not result["lean_kernel_acceptance"]
    assert not result["productivity_claimed"]


def test_prefix_factorization_preserves_order_and_repeated_coincidences():
    assert oracle.balanced_factors((1, 2, 0, 2, 0, 2), (0, 2, 1, 2, 0, 2)) == (
        ((1, 2, 0), (0, 2, 1)), ((2,), (2,)), ((0,), (0,)), ((2,), (2,)))


@pytest.mark.parametrize("top,bottom,reason", [
    ((0, 1), (1,), "different lengths"),
    ((0, 1), (0, 2), "not balanced"),
])
def test_invalid_factorization_refuses(top, bottom, reason):
    with pytest.raises(oracle.InvalidCertificate, match=reason):
        oracle.balanced_factors(top, bottom)


@pytest.mark.parametrize("field,value", [
    ("schema", "psc-forward-carrier-v2"),
    ("fixture", True), ("fixture", -1), ("fixture", 2), ("fixture", 1.0),
    ("complete", False), ("complete", 1), ("complete", "true"),
    ("substitution", [[1], [2, 1, 0], [0, 0, 1]]),
    ("substitution", [[1], [0, 1, 2]]),
    ("substitution", [[1], [0, 1, 2], []]),
    ("states", None),
])
def test_header_domain_and_literal_binding_refuse(packet, field, value):
    packet[field] = value
    with pytest.raises(oracle.InvalidCertificate):
        oracle.validate_packet(packet)


def test_fixture_label_alone_cannot_rebind_literal_images(packet):
    # Relabeling AND changing images is a different closure question: a finite
    # state list can be closed under both substitutions. Only the label changes.
    packet["fixture"] = 1 - packet["fixture"]
    with pytest.raises(oracle.InvalidCertificate, match="substitution mismatch"):
        oracle.validate_packet(packet)


@pytest.mark.parametrize("field", [
    "state_cap", "length_cap", "normalized_state_count", "state_count", "max_state_length",
])
@pytest.mark.parametrize("value", [0, -1, True, 1.0, "1"])
def test_integer_metadata_is_strict(packet, field, value):
    packet[field] = value
    with pytest.raises(oracle.InvalidCertificate, match="positive exact integer"):
        oracle.validate_packet(packet)


@pytest.mark.parametrize("field,reason", [
    ("state_count", "complete state list"),
    ("normalized_state_count", "decoded swap classes"),
    ("max_state_length", "decoded words"),
])
def test_inaccurate_counts_refuse(packet, field, reason):
    packet[field] += 1
    with pytest.raises(oracle.InvalidCertificate, match=reason):
        oracle.validate_packet(packet)


@pytest.mark.parametrize("field,value_field", [
    ("state_cap", "normalized_state_count"), ("length_cap", "max_state_length"),
])
def test_caps_cannot_be_below_actual_carrier(packet, field, value_field):
    packet[field] = packet[value_field] - 1
    with pytest.raises(oracle.InvalidCertificate, match="budget"):
        oracle.validate_packet(packet)


@pytest.mark.parametrize("location,key", [
    ("packet", "capped"), ("packet", "partial"), ("state", "complete"),
])
def test_unknown_flags_and_fields_refuse(packet, location, key):
    record = packet if location == "packet" else packet["states"][0]
    record[key] = False
    with pytest.raises(oracle.InvalidCertificate, match="fields"):
        oracle.validate_packet(packet)


@pytest.mark.parametrize("location,key", [
    ("packet", "complete"), ("state", "children"),
])
def test_missing_required_fields_refuse(packet, location, key):
    record = packet if location == "packet" else packet["states"][0]
    del record[key]
    with pytest.raises(oracle.InvalidCertificate, match="fields"):
        oracle.validate_packet(packet)


@pytest.mark.parametrize("value", [[], [True, 1], [-1, 1], [3, 1], [0.0, 1], ["0", 1], "01"])
def test_corrupted_word_domain_refuses(packet, value):
    packet["states"][0]["top"] = value
    with pytest.raises(oracle.InvalidCertificate, match="word|letters"):
        oracle.validate_packet(packet)


@pytest.mark.parametrize("top,bottom,reason", [
    ([0], [1, 0], "different lengths"),
    ([0, 1], [0, 2], "not balanced"),
    ([0, 1], [0, 1], "not an irreducible balanced block"),
])
def test_nonblocks_refuse(packet, top, bottom, reason):
    packet["states"][0].update(top=top, bottom=bottom)
    with pytest.raises(oracle.InvalidCertificate, match=reason):
        oracle.validate_packet(packet)


def test_duplicate_ordered_state_refuses_even_with_adjusted_count(packet):
    packet["states"].append(deepcopy(packet["states"][0]))
    packet["state_count"] += 1
    with pytest.raises(oracle.InvalidCertificate, match="duplicate ordered word pair"):
        oracle.validate_packet(packet)


def test_missing_ordered_seed_refuses(packet):
    removed = next(i for i, state in enumerate(packet["states"]) if pair(state) in oracle.SEEDS)
    remove_state(packet, removed)
    with pytest.raises(oracle.InvalidCertificate, match="ordered swap seed"):
        oracle.validate_packet(packet)


def test_missing_nonseed_orientation_refuses(packet):
    removed = next(i for i, state in enumerate(packet["states"])
                   if state["top"] != state["bottom"] and pair(state) not in oracle.SEEDS)
    remove_state(packet, removed)
    with pytest.raises(oracle.InvalidCertificate, match="swapped orientation"):
        oracle.validate_packet(packet)


def test_missing_terminal_exit_refuses_even_with_edges_removed(packet):
    destinations = {j for state in packet["states"] for j in state["children"]}
    removed = next(i for i in sorted(destinations)
                   if packet["states"][i]["top"] == packet["states"][i]["bottom"])
    remove_state(packet, removed)
    with pytest.raises(oracle.InvalidCertificate, match="actual child exits"):
        oracle.validate_packet(packet)


@pytest.mark.parametrize("change", ["omit", "duplicate", "reorder", "collapse_repeats"])
def test_complete_child_occurrence_rows_are_required(packet, change):
    if change == "collapse_repeats":
        state = next(s for s in packet["states"] if len(s["children"]) > len(set(s["children"])))
        state["children"] = list(dict.fromkeys(state["children"]))
    else:
        state = next(s for s in packet["states"] if len(set(s["children"])) >= 2)
        row = state["children"]
        if change == "omit":
            row.pop()
        elif change == "duplicate":
            row.append(row[0])
        else:
            j = next(j for j in range(1, len(row)) if row[j] != row[0])
            row[0], row[j] = row[j], row[0]
    with pytest.raises(oracle.InvalidCertificate, match="complete ordered raw child row"):
        oracle.validate_packet(packet)


def test_flipped_noncoincident_child_orientation_refuses(packet):
    index = {pair(state): i for i, state in enumerate(packet["states"])}
    parent, ordinal = next((s, j) for s in packet["states"]
                           for j, child in enumerate(s["children"])
                           if packet["states"][child]["top"] != packet["states"][child]["bottom"])
    child = pair(packet["states"][parent["children"][ordinal]])
    parent["children"][ordinal] = index[child[::-1]]
    with pytest.raises(oracle.InvalidCertificate, match="complete ordered raw child row"):
        oracle.validate_packet(packet)


@pytest.mark.parametrize("value", [-1, True, 0.0, "0", None, "out_of_range"])
def test_bad_child_index_refuses(packet, value):
    if value == "out_of_range":
        value = packet["state_count"]
    state = next(s for s in packet["states"] if s["children"])
    state["children"][0] = value
    with pytest.raises(oracle.InvalidCertificate, match="child index"):
        oracle.validate_packet(packet)


def test_coincidence_cannot_have_a_child_row(packet):
    terminal = next(s for s in packet["states"] if s["top"] == s["bottom"])
    terminal["children"] = [0]
    with pytest.raises(oracle.InvalidCertificate, match="coincidence must be terminal"):
        oracle.validate_packet(packet)


def test_state_order_is_not_a_discovery_claim(packet):
    size = len(packet["states"])
    packet["states"].reverse()
    for state in packet["states"]:
        state["children"] = [size - 1 - child for child in state["children"]]
    assert oracle.validate_packet(packet)["finite_closed_carrier_verified"]


def test_unreachable_terminal_closed_superset_is_accepted(packet):
    present = {pair(state) for state in packet["states"]}
    missing = next(a for a in range(3) if ((a,), (a,)) not in present)
    packet["states"].append({"top": [missing], "bottom": [missing], "children": []})
    refresh_metadata(packet)
    result = oracle.validate_packet(packet)
    assert result["finite_closed_carrier_verified"]
    assert not result["exact_reachability_claimed"]


@pytest.mark.parametrize("raw", [
    b'{"fixture":1,"fixture":0}', b'{"states":[{"top":[0],"top":[1]}]}',
    b'{"value":NaN}', b'{"value":Infinity}', b'{} trailing', b'\xff',
])
def test_non_json_and_duplicate_keys_refuse(raw):
    with pytest.raises(oracle.InvalidCertificate):
        oracle.parse_packet(raw)


def test_cli_combines_source_bound_receipts(completed_packets):
    result = subprocess.run([sys.executable, str(ORACLE_PATH), *map(str, PACKET_PATHS)],
                            capture_output=True, text=True, check=True)
    receipt = json.loads(result.stdout)
    assert receipt["oracle_source_sha256"] == hashlib.sha256(ORACLE_PATH.read_bytes()).hexdigest()
    assert len(receipt["packets"]) == 2
    assert all(p["source_sha256"] == hashlib.sha256(path.read_bytes()).hexdigest()
               for p, path in zip(receipt["packets"], PACKET_PATHS))
    assert not receipt["lean_kernel_acceptance"]
    assert not receipt["productivity_claimed"]


@pytest.mark.parametrize("optimized", [False, True])
def test_cli_refusal_is_atomic_and_survives_optimization(packet, tmp_path, optimized):
    positive = PACKET_PATHS[packet["fixture"]]
    packet["complete"] = False
    corrupt = tmp_path / "incomplete.json"
    corrupt.write_text(json.dumps(packet))
    command = [sys.executable] + (["-O"] if optimized else [])
    result = subprocess.run(command + [str(ORACLE_PATH), str(positive), str(corrupt)],
                            capture_output=True, text=True)
    assert result.returncode != 0
    assert not result.stdout
    assert "partial or capped packet is inconclusive" in result.stderr


def generated_tracks(source, fixture):
    """Independently decode the deliberately small emitted literal grammar.

    This checks lossless representation against original native packets; it
    does not replace Lean's block, row, seed, or refinement checks.
    """
    prefix = f"fixture{fixture}"
    chunk_pattern = re.compile(
        rf"noncomputable def ({prefix}Chunk[0-9]+) : List \(Fin 3\) := \[([0-9]+(?:,[0-9]+)*)\]")
    chunks = {}
    for line in source.splitlines():
        if re.match(rf"(?:noncomputable )?def {prefix}Chunk", line) is None:
            continue
        match = chunk_pattern.fullmatch(line)
        if match is None or match[1] in chunks:
            raise ValueError("invalid or repeated chunk definition")
        letters = tuple(int(x) for x in match[2].split(","))
        if not 1 <= len(letters) <= 32 or any(x not in (0, 1, 2) for x in letters):
            raise ValueError("invalid typed chunk letters")
        chunks[match[1]] = letters
    state_pattern = re.compile(
        rf"^noncomputable def {prefix}State([0-9]+) : List \(Fin 3\) × List \(Fin 3\) :=\n"
        rf"  \(\[({prefix}Chunk[0-9]+(?:,{prefix}Chunk[0-9]+)*)\]\.flatten, "
        rf"\[({prefix}Chunk[0-9]+(?:,{prefix}Chunk[0-9]+)*)\]\.flatten\)$", re.MULTILINE)
    states = {}
    expected_states = sum(re.match(rf"(?:noncomputable )?def {prefix}State[0-9]+ ", line) is not None
                          for line in source.splitlines())
    for match in state_pattern.finditer(source):
        index = int(match[1])
        if index in states:
            raise ValueError("repeated state definition")
        try:
            states[index] = tuple(tuple(letter for ref in group.split(",")
                                        for letter in chunks[ref])
                                  for group in (match[2], match[3]))
        except KeyError as error:
            raise ValueError("unknown chunk reference") from error
    if not chunks or len(states) != expected_states:
        raise ValueError("missing state or invalid flattening")
    return states


def assert_generated_tracks_match(source, packet):
    tracks = generated_tracks(source, packet["fixture"])
    expected = {i: pair(state) for i, state in enumerate(packet["states"])}
    if tracks != expected:
        raise ValueError("generated words differ from original ordered packet")


def check_generated_module_header(source, expected_imports):
    """Check the deliberately restricted generated module/import grammar."""
    imports = []
    namespace_lines = []
    for line in source.splitlines():
        if re.match(r"(?:public )?import\b", line.lstrip()):
            match = re.fullmatch(r"import ([A-Za-z0-9_.]+)", line)
            if match is None:
                raise ValueError("malformed generated module import")
            imports.append(match[1])
        if re.match(r"(?:namespace|end)\b", line.lstrip()):
            namespace_lines.append(line)
    header = "".join(f"import {module}\n" for module in expected_imports)
    if imports != list(expected_imports) or not source.startswith(header):
        raise ValueError("generated module imports do not bind the expected fixture")
    if namespace_lines != ["namespace Psc.GeneratedForwardCarrier", "end Psc.GeneratedForwardCarrier"]:
        raise ValueError("generated declarations use an unexpected namespace")


def load_generated_carrier_source(fixture, directory=None):
    """Follow the verified explicit payload import for finite reconstruction.

    The returned text joins two source units only for this oracle's parser;
    Lean separately compiles their unchanged declarations in their own modules.
    """
    directory = directory or ROOT / "proof/PscVerif/PscVerif"
    checker = (directory / f"NamedForwardCarrierData{fixture}.lean").read_text()
    module = f"PscVerif.NamedForwardCarrierWords{fixture}"
    check_generated_module_header(checker, (module, "PscVerif.FastForwardCarrier"))
    # The import has been checked before resolving its generated filename.
    payload_path = directory / (module.rsplit(".", 1)[1] + ".lean")
    try:
        payload = payload_path.read_text()
    except FileNotFoundError as error:
        raise ValueError("imported generated payload is missing") from error
    check_generated_module_header(payload, ("Init",))
    return payload + "\n" + checker


def generated_array_lines(source, name, element_type):
    pattern = re.compile(
        rf"^noncomputable def {name} : {re.escape(element_type)} := #\[\n(.*?)^\]\n",
        re.MULTILINE | re.DOTALL)
    matches = list(pattern.finditer(source))
    if len(matches) != 1:
        raise ValueError("missing, repeated or incorrectly typed generated array")
    return matches[0][1].splitlines()


def generated_indexed_carrier(source, packet):
    """Reconstruct the actual ordered arrays and seed witnesses from checked aliases.

    This finite source oracle preserves the original packet's indices and
    occurrence multiplicity. Lean separately checks the propositions and proofs.
    """
    prefix = f"fixture{packet['fixture']}"
    count = len(packet["states"])
    alias_pattern = re.compile(
        rf"noncomputable def ({prefix}Index([0-9]+)) : Fin ([0-9]+) := ⟨([0-9]+), by decide⟩")
    aliases = {}
    for line in source.splitlines():
        if re.match(rf"(?:noncomputable )?def {prefix}Index", line) is None:
            continue
        match = alias_pattern.fullmatch(line)
        if match is None or match[1] in aliases:
            raise ValueError("invalid or repeated checked index declaration")
        index, bound, value = map(int, (match[2], match[3], match[4]))
        if bound != count or value != index or not 0 <= value < count:
            raise ValueError("checked index value or original bound changed")
        aliases[match[1]] = value
    if aliases != {f"{prefix}Index{i}": i for i in range(count)}:
        raise ValueError("incomplete checked index inventory")

    def resolve_alias(name):
        if name not in aliases:
            raise ValueError("unknown checked index reference")
        return aliases[name]

    tracks = generated_tracks(source, packet["fixture"])
    state_lines = generated_array_lines(source, prefix + "StateArray",
                                        "Array (List (Fin 3) × List (Fin 3))")
    ordered_states = []
    for i, line in enumerate(state_lines):
        match = re.fullmatch(rf"  {'' if i == 0 else ','}{prefix}State([0-9]+)", line)
        if match is None or int(match[1]) not in tracks:
            raise ValueError("invalid ordered state reference")
        ordered_states.append(tracks[int(match[1])])
    if ordered_states != [pair(state) for state in packet["states"]]:
        raise ValueError("generated state array differs from original ordered packet")

    row_lines = generated_array_lines(source, prefix + "RowsArray", f"Array (List (Fin {count}))")
    rows = []
    for i, line in enumerate(row_lines):
        match = re.fullmatch(rf"  {'' if i == 0 else ','}\[(.*?)\]", line)
        if match is None:
            raise ValueError("malformed ordered row")
        rows.append(tuple(resolve_alias(ref) for ref in match[1].split(",")) if match[1] else ())
    if rows != [tuple(state["children"]) for state in packet["states"]]:
        raise ValueError("generated ordered child rows differ from original packet")

    seed_pattern = re.compile(
        rf"^noncomputable def {prefix}Seed \(a b : Fin 3\) : Fin {count} :=\n"
        rf"  match a.val, b.val with\n((?:  \|[^\n]*\n)+)\n", re.MULTILINE)
    seed_matches = list(seed_pattern.finditer(source))
    if len(seed_matches) != 1:
        raise ValueError("missing, repeated or malformed seed table")
    seeds = {}
    seed_lines = seed_matches[0][1].splitlines()
    for line in seed_lines[:-1]:
        match = re.fullmatch(rf"  \| ([0-9]+), ([0-9]+) => ({prefix}Index[0-9]+)", line)
        if match is None:
            raise ValueError("malformed ordered seed branch")
        key = (int(match[1]), int(match[2]))
        if key in seeds:
            raise ValueError("repeated ordered seed branch")
        seeds[key] = resolve_alias(match[3])
    if not seed_lines or seed_lines[-1] != f"  | _, _ => {prefix}Index0":
        raise ValueError("invalid diagonal seed fallback")
    expected_seeds = {(a, b): ordered_states.index(((a, b), (b, a)))
                      for a in range(3) for b in range(3) if a != b}
    if seeds != expected_seeds:
        raise ValueError("generated ordered seeds differ from original packet")

    # Connect the reconstructed arrays to the actual packet being checked;
    # otherwise a correct unused array could conceal a different accessor.
    bindings = (
        f"noncomputable def {prefix}State (i : Fin {count}) : List (Fin 3) × List (Fin 3) :=\n"
        f"  {prefix}StateArray[i.val]'i.isLt",
        f"noncomputable def {prefix}Rows (i : Fin {count}) : List (Fin {count}) :=\n"
        f"  {prefix}RowsArray[i.val]'i.isLt",
        f"noncomputable def {prefix}Packet : Psc.FastForwardCarrier.Packet {count} where\n"
        f"  state := {prefix}State\n  rows := {prefix}Rows\n  seed := {prefix}Seed",
    )
    for binding in bindings:
        if len(re.findall(r"^" + re.escape(binding) + r"\n\n", source, re.MULTILINE)) != 1:
            raise ValueError("generated packet does not use the reconstructed arrays")
    return rows, seeds


def check_singleton_range_coverage(source, packet):
    """Require the complete source inventory before trusting range aggregation."""
    prefix = f"fixture{packet['fixture']}"
    count = len(packet["states"])
    pattern = re.compile(
        rf"^theorem {prefix}Range([0-9]+) :\n"
        rf"    {prefix}Packet.checkRange {prefix}Substitution ([0-9]+) ([0-9]+) "
        rf"= true := by decide \+kernel$", re.MULTILINE)
    ranges = [(int(match[1]), int(match[2]), int(match[3])) for match in pattern.finditer(source)]
    declarations = sum(line.startswith(f"theorem {prefix}Range") for line in source.splitlines())
    if len(ranges) != declarations or sorted(ranges) != [(i, i, 1) for i in range(count)]:
        raise ValueError("missing, duplicated or nonsingleton row-check coverage")


def test_shared_checked_indices_reconstruct_all_rows_and_ordered_seeds(native_packet):
    source = load_generated_carrier_source(native_packet["fixture"])
    generated_indexed_carrier(source, native_packet)
    check_singleton_range_coverage(source, native_packet)


@pytest.mark.parametrize("mutation", [
    "missing_payload_import", "wrong_fixture_import", "unknown_payload_import",
    "duplicate_payload_import", "commented_payload_import", "additional_payload_import",
    "missing_checker_import", "wrong_checker_import", "missing_init_import",
    "extra_payload_dependency", "missing_payload_file", "wrong_payload_fixture",
    "wrong_payload_namespace", "wrong_checker_namespace",
])
def test_split_payload_import_corruption_is_detected(native_packet, tmp_path, mutation):
    fixture = native_packet["fixture"]
    original = ROOT / "proof/PscVerif/PscVerif"
    checker_path = tmp_path / f"NamedForwardCarrierData{fixture}.lean"
    payload_path = tmp_path / f"NamedForwardCarrierWords{fixture}.lean"
    other_path = tmp_path / f"NamedForwardCarrierWords{1 - fixture}.lean"
    for path in (checker_path, payload_path, other_path):
        path.write_bytes((original / path.name).read_bytes())
    # Validate both complete imported objects before introducing a corruption.
    generated_indexed_carrier(load_generated_carrier_source(fixture, tmp_path), native_packet)
    checker, payload = checker_path.read_text(), payload_path.read_text()
    imported = f"import PscVerif.NamedForwardCarrierWords{fixture}\n"
    other_import = f"import PscVerif.NamedForwardCarrierWords{1 - fixture}\n"
    if mutation == "missing_payload_import":
        checker = checker.replace(imported, "", 1)
    elif mutation == "wrong_fixture_import":
        checker = checker.replace(imported, other_import, 1)
    elif mutation == "unknown_payload_import":
        # The wrong module exists and has valid bytes, so refusal must bind
        # the exact expected import rather than merely finding a readable file.
        (tmp_path / "NamedForwardCarrierWords999.lean").write_text(payload)
        checker = checker.replace(imported, "import PscVerif.NamedForwardCarrierWords999\n", 1)
    elif mutation == "duplicate_payload_import":
        checker = checker.replace(imported, imported + imported, 1)
    elif mutation == "commented_payload_import":
        checker = checker.replace(imported, "-- " + imported, 1)
    elif mutation == "additional_payload_import":
        checker = checker.replace(imported, imported + other_import, 1)
    elif mutation == "missing_checker_import":
        checker = checker.replace("import PscVerif.FastForwardCarrier\n", "", 1)
    elif mutation == "wrong_checker_import":
        checker = checker.replace("import PscVerif.FastForwardCarrier\n", "import Init\n", 1)
    elif mutation == "missing_init_import":
        payload = payload.replace("import Init\n", "", 1)
    elif mutation == "extra_payload_dependency":
        payload = payload.replace("import Init\n", "import Init\nimport PscVerif.FastForwardCarrier\n", 1)
    elif mutation == "wrong_payload_fixture":
        payload = other_path.read_text()
    elif mutation == "wrong_payload_namespace":
        payload = payload.replace("namespace Psc.GeneratedForwardCarrier\n", "namespace Psc.WrongCarrier\n", 1)
    elif mutation == "wrong_checker_namespace":
        checker = checker.replace("namespace Psc.GeneratedForwardCarrier\n", "namespace Psc.WrongCarrier\n", 1)
    checker_path.write_text(checker)
    payload_path.write_text(payload)
    if mutation == "missing_payload_file":
        payload_path.unlink()
    with pytest.raises(ValueError):
        generated_indexed_carrier(load_generated_carrier_source(fixture, tmp_path), native_packet)


@pytest.mark.parametrize("mutation", [
    "wrong_value", "wrong_bound", "out_of_bounds", "modular_numeral", "missing_alias",
    "duplicate_alias", "unknown_row_alias", "wrong_child", "omitted_occurrence",
    "reordered_children", "missing_row", "unknown_seed_alias", "wrong_seed",
    "missing_seed", "repeated_seed", "reordered_state_array", "wrong_packet_binding",
])
def test_checked_index_and_ordered_source_corruption_is_detected(native_packet, mutation):
    source = load_generated_carrier_source(native_packet["fixture"])
    generated_indexed_carrier(source, native_packet)
    prefix = f"fixture{native_packet['fixture']}"
    count = len(native_packet["states"])
    first = f"noncomputable def {prefix}Index0 : Fin {count} := ⟨0, by decide⟩"
    assert first in source
    if mutation == "wrong_value":
        corrupt = source.replace(first, first.replace("⟨0,", "⟨1,"), 1)
    elif mutation == "wrong_bound":
        corrupt = source.replace(first, first.replace(f"Fin {count}", f"Fin {count + 1}"), 1)
    elif mutation == "out_of_bounds":
        corrupt = source.replace(first, first.replace("⟨0,", f"⟨{count},"), 1)
    elif mutation == "modular_numeral":
        corrupt = source.replace(first, first.split(":=")[0] + ":= 0", 1)
    elif mutation == "missing_alias":
        corrupt = source.replace(first + "\n", "", 1)
    elif mutation == "duplicate_alias":
        corrupt = source.replace(first, first + "\n" + first, 1)
    elif mutation in {"unknown_row_alias", "wrong_child", "omitted_occurrence", "reordered_children", "missing_row"}:
        row_lines = generated_array_lines(source, prefix + "RowsArray", f"Array (List (Fin {count}))")
        index = next(i for i, state in enumerate(native_packet["states"])
                     if len(state["children"]) > 1 and len(set(state["children"])) > 1)
        row = row_lines[index]
        refs = re.findall(rf"{prefix}Index[0-9]+", row)
        if mutation == "unknown_row_alias":
            refs[0] = f"{prefix}Index999999"
        elif mutation == "wrong_child":
            old = int(refs[0].removeprefix(prefix + "Index"))
            refs[0] = f"{prefix}Index{(old + 1) % count}"
        elif mutation == "omitted_occurrence":
            refs.pop(0)
        elif mutation == "reordered_children":
            j = next(j for j in range(1, len(refs)) if refs[j] != refs[0])
            refs[0], refs[j] = refs[j], refs[0]
        new_row = f"  {'' if index == 0 else ','}[" + ",".join(refs) + "]"
        corrupt = source.replace(row + "\n", "" if mutation == "missing_row" else new_row + "\n", 1)
    elif mutation in {"unknown_seed_alias", "wrong_seed", "missing_seed", "repeated_seed"}:
        seed = re.search(rf"^  \| 0, 1 => {prefix}Index[0-9]+$", source, re.MULTILINE)[0]
        if mutation == "unknown_seed_alias":
            changed = seed.split("=>")[0] + f"=> {prefix}Index999999"
        elif mutation == "wrong_seed":
            original = int(seed.split("Index")[-1])
            changed = seed.split("=>")[0] + f"=> {prefix}Index{(original + 1) % count}"
        elif mutation == "missing_seed":
            changed = ""
        else:
            changed = seed + "\n" + seed
        corrupt = source.replace(seed + "\n", changed + "\n" if changed else "", 1)
    elif mutation == "reordered_state_array":
        marker = f"  {prefix}State0\n  ,{prefix}State1\n"
        assert marker in source
        corrupt = source.replace(marker, f"  {prefix}State1\n  ,{prefix}State0\n", 1)
    else:
        marker = f"  state := {prefix}State\n"
        assert marker in source
        corrupt = source.replace(marker, f"  state := fun _ => {prefix}State0\n", 1)
    with pytest.raises(ValueError):
        generated_indexed_carrier(corrupt, native_packet)


@pytest.mark.parametrize("mutation", ["missing", "duplicate", "wrong_start", "nonsingleton"])
def test_singleton_range_coverage_corruption_is_detected(native_packet, mutation):
    source = load_generated_carrier_source(native_packet["fixture"])
    check_singleton_range_coverage(source, native_packet)
    prefix = f"fixture{native_packet['fixture']}"
    declaration = (f"theorem {prefix}Range0 :\n"
                   f"    {prefix}Packet.checkRange {prefix}Substitution 0 1 = true := by decide +kernel")
    assert declaration in source
    if mutation == "missing":
        replacement = ""
    elif mutation == "duplicate":
        replacement = declaration + "\n\n" + declaration
    elif mutation == "wrong_start":
        replacement = declaration.replace("Substitution 0 1", "Substitution 1 1")
    else:
        replacement = declaration.replace("Substitution 0 1", "Substitution 0 8")
    corrupt = source.replace(declaration, replacement, 1)
    with pytest.raises(ValueError):
        check_singleton_range_coverage(corrupt, native_packet)


def test_typed_chunks_reconstruct_every_original_ordered_word(native_packet):
    source = load_generated_carrier_source(native_packet["fixture"])
    assert_generated_tracks_match(source, native_packet)


@pytest.mark.parametrize("mutation", [
    "empty_chunk", "nonternary_letter", "missing_chunk", "unknown_reference",
    "wrong_flattening", "reordered_references", "missing_chunk_modifier",
    "missing_state_modifier",
])
def test_chunk_encoding_corruption_is_detected(native_packet, mutation):
    source = load_generated_carrier_source(native_packet["fixture"])
    # Prove a complete positive baseline outside the rejection catcher.
    assert_generated_tracks_match(source, native_packet)
    prefix = f"fixture{native_packet['fixture']}"
    first = next(line for line in source.splitlines()
                 if line.startswith(f"noncomputable def {prefix}Chunk0 "))
    if mutation == "empty_chunk":
        corrupt = source.replace(first, first.split(":=")[0] + ":= []", 1)
    elif mutation == "nonternary_letter":
        corrupt = source.replace(first, first.replace("[", "[3,", 1), 1)
    elif mutation == "missing_chunk":
        corrupt = source.replace(first + "\n", "", 1)
    elif mutation == "unknown_reference":
        marker = f"[{prefix}Chunk0]"
        assert marker in source
        corrupt = source.replace(marker, f"[{prefix}Chunk999999]", 1)
    elif mutation == "wrong_flattening":
        corrupt = source.replace("].flatten", "]", 1)
    elif mutation == "missing_chunk_modifier":
        corrupt = source.replace(first, first.removeprefix("noncomputable "), 1)
    elif mutation == "missing_state_modifier":
        marker = f"noncomputable def {prefix}State0 "
        assert marker in source
        corrupt = source.replace(marker, marker.removeprefix("noncomputable "), 1)
    else:
        ref_pattern = re.compile(rf"\[({prefix}Chunk[0-9]+),({prefix}Chunk[0-9]+)")
        refs = ref_pattern.search(source)
        while refs is not None and refs[1] == refs[2]:
            refs = ref_pattern.search(source, refs.end())
        assert refs is not None
        corrupt = source[:refs.start()] + f"[{refs[2]},{refs[1]}" + source[refs.end():]
    with pytest.raises(ValueError):
        assert_generated_tracks_match(corrupt, native_packet)
