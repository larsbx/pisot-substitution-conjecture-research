"""Exact rational-polytope physical-geometry proof and negative controls."""
import importlib.util
from pathlib import Path
import sys
import pytest

SRC=Path(__file__).resolve().parents[1]/"oracles/python/class_a_boundary_cy_symbolic_geometry.py"
spec=importlib.util.spec_from_file_location("_cy_exact_geometry",SRC)
m=importlib.util.module_from_spec(spec)
sys.modules[spec.name]=m
spec.loader.exec_module(m)


def test_every_symbolic_path_label_has_universal_strict_perron_margins():
    result=m.prove_all_strict_margins()
    assert result["polytope_vertices"]==4
    assert result["base_labels"]==35
    assert result["oriented_labels"]==61
    assert result["strict_margins"]==122
    assert not result["universal_BH"]


def test_reversed_label_interchanges_exact_physical_margins():
    w=m.every["CY"]
    r=m.every["reverse"](w)
    lower,upper=m.margin_coeff(w)
    rl,ru=m.margin_coeff(r)
    assert rl==upper and ru==lower


def test_disjoint_very_large_offset_fails_exact_guard():
    with pytest.raises(AssertionError):
        m.certify_label((0,0,0,0,10))
    with pytest.raises(ValueError):
        m.length_coeff(7)
