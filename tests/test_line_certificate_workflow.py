"""The evidence workflow re-certifies exactly the lines and wedges that are pinned.

kernel/symbolic_line_pins.txt is the single list of certified Theorem E lines
(`line`), norm-mode lines (`norm`, the wedges' boundary lines) and wedge cores
(`wedge`), read at run time by kernel/symbolic_line_certificate.mojo;
.github/workflows/class-b-lines-evidence.yml must run each of them once, in
the driver's `CLASS AP BP AQ BQ AR BR`, `norm CLASS ...` and
`wedge CLASS P0 PA PB Q0 QA QB R0 RA RB` forms, and nothing else.
"""

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PINS = ROOT / "kernel" / "symbolic_line_pins.txt"
WORKFLOW = ROOT / ".github" / "workflows" / "class-b-lines-evidence.yml"

ROW = re.compile(r"^(line|norm|wedge) ([ABCD])((?: -?\d+)+)$")
WIDTH = {"line": 11, "norm": 11, "wedge": 12}  # integers after the class letter
COEFFICIENTS = {"line": 6, "norm": 6, "wedge": 9}
LINE = re.compile(r"^\s*- \{ line: '([^']+)' \}\s*$", re.M)


def pin_rows():
    rows = []
    for text in PINS.read_text(encoding="utf-8").splitlines():
        if not text or text.startswith("#"):
            continue
        match = ROW.fullmatch(text)
        assert match, f"malformed pin row: {text!r}"
        kind, cls, ints = match.group(1), match.group(2), match.group(3).split()
        assert len(ints) == WIDTH[kind], f"wrong width: {text!r}"
        rows.append((kind, cls, ints))
    return rows


def pinned_lines():
    return [
        " ".join(([] if kind == "line" else [kind]) + [cls] + ints[:COEFFICIENTS[kind]])
        for kind, cls, ints in pin_rows()
    ]


def workflow_lines():
    return LINE.findall(WORKFLOW.read_text(encoding="utf-8"))


def test_the_pin_file_pins_lines():
    assert len(pinned_lines()) >= 15


def test_each_pin_is_listed_once():
    keys = pinned_lines()
    assert len(keys) == len(set(keys))


def test_the_workflow_runs_every_pinned_line_once():
    pins, runs = pinned_lines(), workflow_lines()
    assert len(runs) == len(set(runs))
    assert sorted(runs) == sorted(pins)


def test_a_re_pin_triggers_the_evidence_workflow():
    assert "      - 'kernel/symbolic_line_pins.txt'" in WORKFLOW.read_text(encoding="utf-8")


def test_shared_algebra_changes_trigger_the_symbolic_evidence_matrix():
    assert "      - 'kernel/psc/param_poly.mojo'" in WORKFLOW.read_text(encoding="utf-8")
