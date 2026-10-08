"""The evidence workflow re-certifies exactly the lines the driver pins.

`certified_lines()` in kernel/symbolic_line_certificate.mojo is the single list
of certified Theorem E lines; .github/workflows/class-b-lines-evidence.yml must
run each of them once, in the driver's `CLASS AP BP AQ BQ AR BR` form, and
nothing else.
"""

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DRIVER = ROOT / "kernel" / "symbolic_line_certificate.mojo"
WORKFLOW = ROOT / ".github" / "workflows" / "class-b-lines-evidence.yml"

ROW = re.compile(r"^\s*\[CLASS_([ABCD]),((?:\s*-?\d+,){10}\s*-?\d+)\],?\s*$", re.M)
LINE = re.compile(r"^\s*- \{ line: '([^']+)' \}\s*$", re.M)


def pinned_lines():
    body = DRIVER.read_text(encoding="utf-8").split("def certified_lines()", 1)[1].split("\n\n\n", 1)[0]
    return [
        " ".join([cls, *(x.strip() for x in ints.split(",")[:6])])
        for cls, ints in ROW.findall(body)
    ]


def workflow_lines():
    return LINE.findall(WORKFLOW.read_text(encoding="utf-8"))


def test_the_driver_pins_lines():
    assert len(pinned_lines()) >= 15


def test_the_workflow_runs_every_pinned_line_once():
    pins, runs = pinned_lines(), workflow_lines()
    assert len(runs) == len(set(runs))
    assert sorted(runs) == sorted(pins)
