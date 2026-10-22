"""The d=2 plus residue-ray carriers are the #312 parity carriers.

Rows of `kernel/psc/class_a_ray_d2p.mojo`, evaluated at l = n // 2, must equal
the typed-interval profile that the independent Fraction-field oracle
`oracles/python/class_a_d2_parity_carrier.py` computes from its own complete
graph. Finite calibration only; the uniform statement is the ray certificate.
"""
import importlib.util
import re
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("class_a_d2_parity_carrier",
                                              ROOT / "oracles/python/class_a_d2_parity_carrier.py")
PARITY = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(PARITY)
SOURCE = (ROOT / "kernel/psc/class_a_ray_d2p.mojo").read_text()


def ray_rows(r):
    start = SOURCE.index("def rows_r%d(" % r)
    body = SOURCE[start:SOURCE.find("\ndef ", start + 1)]
    return [tuple(map(int, m.split(","))) for m in re.findall(r"List\[Int\]\(\[(-?\d+(?:,-?\d+){7})\]\)", body)]


def ray_profile(n, r):
    l = n // 2
    return sorted((t, b, s, y, a * l + c, e * l + f) for t, b, s, y, a, c, e, f in ray_rows(r))


@pytest.mark.parametrize("n", [8, 9, 12, 13])
def test_ray_carrier_equals_independent_profile(n):
    assert ray_profile(n, n % 2) == sorted(PARITY.reference_profile(n)["intervals"])


def test_other_residue_carrier_differs():
    assert ray_profile(12, 1) != sorted(PARITY.reference_profile(12)["intervals"])
