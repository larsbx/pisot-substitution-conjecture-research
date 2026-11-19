"""Independent literal-word oracle for the (NM_V) census.

The canonical census is kernel/nmv_census.mojo (kernel/psc/zero_fibre_asymptotes.mojo),
pinned by kernel/tests/test_zero_fibre_asymptotes.mojo, with its log in
evidence/nmv-census-2026-11-18/. This test runs the stdlib oracle
oracles/python/nmv_literal_rays.py, which shares no code with it, on every
failing pair of that log and requires each to be confirmed.
"""
import runpy
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ORACLE = runpy.run_path(str(ROOT / "oracles/python/nmv_literal_rays.py"))
LOG = ROOT / "evidence/nmv-census-2026-11-18/nmv-census.log"


def test_every_census_failure_is_a_literal_asymptote():
    assert ORACLE["confirm_log"](LOG) == 96


def test_census_totals_are_recorded():
    text = LOG.read_text()
    assert "domain (unit, >=2 periodic letters on both sides) 936" in text
    assert "NM_V holds 888 left failures 24 right failures 24" in text
    assert "scope: beta1 >= 2 492 of which NM_V holds 492" in text
    assert sum(1 for line in text.splitlines() if line.startswith("fail")) == 48
