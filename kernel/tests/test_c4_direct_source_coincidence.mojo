"""All 36 sources and the unbounded-in-paper 021 run-family witnesses.

These are positive literal certificates, not matrix-template acceptance.
"""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.bpa import apply_substitution, decompose
from psc.c4_direct_source_coincidence import (
    verify_simultaneous_prefix_certificate, tail_021_run_family,
    verify_tail_021_coincidence,
)


def _table() -> List[List[Int]]:
    return (
# BEGIN CERTIFICATE TABLE
[
    [4, 21, 3, 12, 6, 1],
    [5, 32, 4, 18, 10, 0],
    [4, 23, 3, 13, 7, 1],
    [4, 32, 4, 18, 10, 1],
    [5, 98, 16, 53, 29, 1],
    [4, 37, 5, 21, 11, 2],
    [2, 4, 1, 2, 1, 1],
    [4, 10, 2, 5, 3, 1],
    [3, 13, 2, 7, 4, 1],
    [4, 20, 3, 11, 6, 1],
    [6, 155, 25, 84, 46, 1],
    [5, 100, 16, 54, 30, 1],
    [2, 0, 0, 0, 0, 0],
    [2, 0, 0, 0, 0, 0],
    [5, 50, 8, 27, 15, 1],
    [7, 464, 75, 252, 137, 1],
    [3, 7, 2, 3, 2, 1],
    [3, 8, 2, 4, 2, 2],
    [2, 0, 0, 0, 0, 1],
    [2, 0, 0, 0, 0, 1],
    [1, 0, 0, 0, 0, 1],
    [1, 0, 0, 0, 0, 1],
    [4, 28, 4, 16, 8, 2],
    [4, 28, 4, 16, 8, 2],
    [2, 0, 0, 0, 0, 1],
    [2, 0, 0, 0, 0, 1],
    [1, 0, 0, 0, 0, 1],
    [1, 0, 0, 0, 0, 1],
    [5, 41, 7, 22, 12, 1],
    [3, 6, 1, 3, 2, 1],
    [6, 146, 24, 79, 43, 1],
    [6, 231, 38, 125, 68, 1],
    [5, 77, 12, 42, 23, 1],
    [5, 77, 12, 42, 23, 1],
    [2, 0, 0, 0, 0, 2],
    [2, 0, 0, 0, 0, 2],
]
# END CERTIFICATE TABLE
    )


def _swap_check(sigma: List[List[Int]], n: Int, p: Int, z: Int) raises:
    for a in range(3):
        for b in range(a+1,3):
            var top: List[Int] = [a,b]
            var bottom: List[Int] = [b,a]
            for _ in range(n):
                top = apply_substitution(sigma,top)
                bottom = apply_substitution(sigma,bottom)
            var factors = decompose(top,bottom)
            var offset = 0
            var found = False
            for i in range(len(factors)):
                if offset == p:
                    assert_equal(factors[i].u,[z])
                    assert_equal(factors[i].v,[z])
                    found = True
                offset += len(factors[i].u)
            assert_true(found)


def test_all_36_exact_certificates_and_actual_swaps() raises:
    var first: List[List[Int]] = [[0,1],[1,0]]
    var middle: List[List[Int]] = [[1,1,2],[1,2,1],[2,1,1]]
    var last: List[List[Int]] = [[0,1,2],[0,2,1],[1,0,2],[1,2,0],[2,0,1],[2,1,0]]
    var rows = _table()
    assert_equal(len(rows),36)
    var index = 0
    for i in range(2):
        for j in range(3):
            for k in range(6):
                var sigma = List[List[Int]]()
                sigma.append(first[i].copy())
                sigma.append(middle[j].copy())
                sigma.append(last[k].copy())
                var r = rows[index].copy()
                var Q: List[Int] = [r[2],r[3],r[4]]
                _ = verify_simultaneous_prefix_certificate(sigma,r[0],r[1],Q,r[5])
                _swap_check(sigma,r[0],r[1],r[5])
                index += 1
    assert_equal(index,36)


def test_tail_021_formula_grid_and_boundaries() raises:
    for a in range(9):
        for b in range(9):
            if a+b == 0 or a+b > 12:
                continue
            var cert = verify_tail_021_coincidence(a,b)
            assert_true(cert.generation <= 5)
            if a <= 4 and b <= 4:
                var sigma = tail_021_run_family(a,b)
                _swap_check(sigma,cert.generation,cert.cut,cert.next_letter)
    var exceptional = verify_tail_021_coincidence(1,0)
    assert_equal(exceptional.cut,16)
    assert_equal(exceptional.prefix_parikh,[4,7,5])


def test_false_prefix_and_malformed_source_refuse() raises:
    var refused = False
    try:
        _ = verify_simultaneous_prefix_certificate([[0,1],[1,3,1],[0,1,2]],2,0,[0,0,0],0)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = verify_simultaneous_prefix_certificate([[0,1],[1,2],[0,2,1]],5,16,[4,8,4],0)
    except:
        refused = True
    assert_true(refused)
    for a in [-1,0,9]:
        refused = False
        try:
            _ = verify_tail_021_coincidence(a,0)
        except:
            refused = True
        assert_true(refused)
    refused = False
    try:
        _ = verify_tail_021_coincidence(8,8)
    except:
        refused = True
    assert_true(refused)


def main() raises:
    test_all_36_exact_certificates_and_actual_swaps()
    test_tail_021_formula_grid_and_boundaries()
    test_false_prefix_and_malformed_source_refuse()
    print("36 direct source certificates and 021 family controls passed")
    require_contract("36 M2 source orders have positive simultaneous prefix witnesses by level seven; 021 run family by level five with explicit boundaries; actual swap diagonals, false-prefix and malformed-source refusal; no general PSC or pure-discreteness inference")
