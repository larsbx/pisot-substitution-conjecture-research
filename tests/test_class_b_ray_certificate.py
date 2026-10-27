"""Independent class-B ray verifier: current tables, one full ray, refusals."""
import importlib.util
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]


def load(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / f"oracles/python/{name}.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


m = load("class_b_ray_certificate")


def first_ray():
    i, spec, rows, pot = next(m.tables())
    assert i == 0 and spec[:4] == [1, 1, 0, 9]
    return m.Ray(1, 1, 0), rows, pot


def test_generated_tables_are_current():
    out = subprocess.run([sys.executable, str(ROOT / "oracles/python/class_b_ray_tables.py"), "--check"],
                         capture_output=True, text=True)
    assert out.returncode == 0, out.stdout + out.stderr


def test_plus_gap_one_certifies_with_the_native_counts():
    ray, rows, pot = first_ray()
    st = m.certify(ray, 9, rows, pot)
    assert (st["rows"], st["seeds_real"], st["seeds_unreal"]) == (389, 9, 3)
    assert (st["covered"], st["gap_geometry"], st["descent_intervals"]) == (14241, 10255, 1021)


def test_perron_data_are_derived_from_the_images():
    ray = m.Ray(1, 2, 1)
    ray.derive()
    assert ray.a_poly == m.sub(m.mul(m.mul([-2, 1], [-1, 1]), [-1, 1]), [0, 10])
    bad = m.Ray(1, 2, 1)
    bad.images_at = lambda q: [[0] + [2] * (3 * q + 11) + [0], [1] + [2] * q + [0], [1] + [2] * (q + 1) + [0]]
    with pytest.raises(ValueError):
        bad.derive()


def test_removed_row_escapes():
    ray, rows, pot = first_ray()
    with pytest.raises(ValueError):
        m.certify(ray, 9, rows[:68] + rows[69:], pot)


def test_lowered_potential_has_no_descent():
    ray, rows, pot = first_ray()
    key = next(k for k, v in sorted(pot.items()) if v > 0)
    with pytest.raises(ValueError, match="NO DESCENT"):
        m.certify(ray, 9, rows, {**pot, key: pot[key] - 1})


def test_below_floor_refuses():
    ray, rows, pot = first_ray()
    with pytest.raises(ValueError):
        m.certify(ray, 8, rows, pot)
