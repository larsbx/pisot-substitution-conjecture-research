"""Independent exact root and integer-affine checks of the all-n closure argument."""
import importlib.util
from pathlib import Path
import pytest

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location(
    "class_a_closure_oracle",ROOT/"oracles/python/class_a_uniform_closure.py")
oracle=importlib.util.module_from_spec(spec)
spec.loader.exec_module(oracle)


def test_uniform_tail_proof():
    assert oracle.check()=={"cells":1528,"gaps":1006,"left":505,"right":501}


@pytest.mark.parametrize("n,cells,gaps,left,right",[
    (4,1476,958,481,477),
    (5,1510,988,496,492),
    (6,1524,1002,503,499),
    (7,1528,1006,505,501),
])
def test_exact_finite_prefix(n,cells,gaps,left,right):
    assert oracle.check(n)=={
        "cells":cells,"gaps":gaps,"left":left,"right":right}


def test_polynomial_sign_and_actual_escape_mutation():
    assert oracle.nonnegative_tail((0,0,0,0))
    assert oracle.nonnegative_tail((0,1,0,0))
    assert not oracle.nonnegative_tail((0,-1,0,0))
    assert oracle.exact_root_nonnegative((0,1,0,0),4)
    assert not oracle.exact_root_nonnegative((0,-1,0,0),4)
    original=oracle.rows()
    assert len(original)==89
    modified=original.copy()
    narrowed=list(modified[0])
    narrowed[7]=0
    modified[0]=tuple(narrowed)
    with pytest.raises(ValueError,match="real child outside candidate"):
        oracle.check(template=modified)
    with pytest.raises(ValueError):
        oracle.check(template=original[:-1])
