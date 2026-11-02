"""Literal C4 newborn-cut tests, not a universal synchronization claim."""

from std.testing import assert_equal, assert_true, assert_false
from mojo_smoke.claims import require_contract
from psc.bpa import apply_substitution, coincidence_boundaries, decompose, normalise
from psc.derived_system import build_derived_system
from psc.c4_cut_alignment import classify_irreducible_birth
from psc.words import Pair


def _contains(whole: List[Int], part: List[Int]) -> Bool:
    if len(part) > len(whole):
        return False
    for i in range(len(whole) - len(part) + 1):
        var same = True
        for j in range(len(part)):
            if whole[i + j] != part[j]:
                same = False
                break
        if same:
            return True
    return False


def test_recurrent_pip_has_genuine_asynchronous_nonsync_cut() raises:
    # Tribonacci: 0 -> 01, 1 -> 02, 2 -> 0, primitive irreducible Pisot.
    # Each state is reached by an ACTUAL normalized child, not invented edges.
    var sigma: List[List[Int]] = [[0, 1], [0, 2], [0]]
    var seed = Pair([0, 1], [1, 0])
    var first = decompose(
        apply_substitution(sigma, seed.u), apply_substitution(sigma, seed.v)
    )
    assert_equal(len(first), 2)
    assert_equal(first[0].u, [0])
    assert_equal(first[0].v, [0])
    var b = Pair([1, 0, 2], [2, 0, 1])
    assert_equal(normalise(first[1]), normalise(b))

    var second = decompose(
        apply_substitution(sigma, b.u), apply_substitution(sigma, b.v)
    )
    assert_equal(len(second), 2)
    assert_equal(second[0].u, [0])
    assert_equal(second[0].v, [0])
    var parent = Pair([0, 1, 0, 2], [2, 0, 1, 0])
    assert_equal(normalise(second[1]), normalise(parent))

    var top = apply_substitution(sigma, parent.u)
    var bottom = apply_substitution(sigma, parent.v)
    assert_equal(top, [0, 1, 0, 2, 0, 1, 0])
    assert_equal(bottom, [0, 0, 1, 0, 2, 0, 1])
    assert_equal(coincidence_boundaries(top, bottom), [0, 1, 3, 5, 7])
    var third = decompose(top, bottom)
    assert_equal(len(third), 4)
    assert_equal(third[0].u, [0])
    assert_equal(third[0].v, [0])
    assert_equal(third[1].u, [1, 0])
    assert_equal(third[1].v, [0, 1])
    assert_equal(third[2].u, [2, 0])
    assert_equal(third[2].v, [0, 2])
    assert_equal(third[3].u, [1, 0])
    assert_equal(third[3].v, [0, 1])
    # Thus normalized seed -> B -> parent -> seed is a real
    # *noncoincident recurrent* BPA cycle, with coincidence exits.
    assert_equal(normalise(third[1]), normalise(seed))

    var witness = classify_irreducible_birth(sigma, parent, 3)
    assert_equal(witness.top_source, 1)
    assert_equal(witness.bottom_source, 2)
    assert_equal(witness.top_digit, 1)
    assert_equal(witness.bottom_digit, 0)
    assert_false(witness.top_boundary)
    assert_true(witness.bottom_boundary)
    assert_equal(witness.source_defect, [0, 0, -1])
    assert_equal(witness.local_correction, [1, 0, 0])
    # Left-adjacent and right-adjacent letters are BOTH distinct.
    # No immediate diagonal target discharges this newborn cut.
    assert_true(top[2] != bottom[2])
    assert_true(top[3] != bottom[3])
    # Parent sides are both legal factors, although this is
    # insufficient to couple their recognizable boundary flags.
    var supertile = sigma[0].copy()
    for _ in range(3):
        supertile = apply_substitution(sigma, supertile)
    assert_true(_contains(supertile, parent.u))
    assert_true(_contains(supertile, parent.v))
    # This support is NOT strict; it has actual diagonal children.
    var rejected = False
    var only: List[Pair] = [seed, b, parent]
    try:
        _ = build_derived_system(sigma, only)
    except:
        rejected = True
    assert_true(rejected)


def test_strict_nonpisot_born_cut_and_bad_inputs() raises:
    # Real two-state STRICT child-closed control; not Pisot.
    var sigma: List[List[Int]] = [[1], [0, 1, 2], [1]]
    var a = Pair([0, 1], [1, 0])
    var b = Pair([1, 2], [2, 1])
    var states: List[Pair] = [a, b]
    var system = build_derived_system(sigma, states)
    assert_equal(system.size(), 2)
    assert_equal(len(system.images[0]), 2)
    assert_equal(len(system.images[1]), 2)
    # This strict control is singular (sigma(0) == sigma(2)).
    # It is NOT an admissible positive test of the full-rank theorem.
    var top = apply_substitution(sigma, a.u)
    var bottom = apply_substitution(sigma, a.v)
    assert_equal(coincidence_boundaries(top, bottom), [0, 2, 4])
    var caught = False
    try:
        _ = classify_irreducible_birth(sigma, a, 2)
    except:
        caught = True
    assert_true(caught)

    # Essential hypothesis negative: the singular substitution can map an
    # irreducible balanced parent to a bilaterally aligned interior return.
    var singular_parent = Pair([0, 2], [2, 0])
    top = apply_substitution(sigma, singular_parent.u)
    bottom = apply_substitution(sigma, singular_parent.v)
    assert_equal(top, [1, 1])
    assert_equal(bottom, [1, 1])
    assert_equal(coincidence_boundaries(top, bottom), [0, 1, 2])
    caught = False
    try:
        _ = classify_irreducible_birth(sigma, singular_parent, 1)
    except:
        caught = True
    assert_true(caught)

    # Other fail-closed clauses on the nonsingular PIP fixture.
    var pip: List[List[Int]] = [[0, 1], [0, 2], [0]]
    var parent = Pair([0, 1, 0, 2], [2, 0, 1, 0])
    caught = False
    try:
        _ = classify_irreducible_birth(pip, parent, 2)
    except:
        caught = True
    assert_true(caught)
    caught = False
    try:
        _ = classify_irreducible_birth(pip, Pair([0, 0], [0, 0]), 1)
    except:
        caught = True
    assert_true(caught)


def main() raises:
    test_recurrent_pip_has_genuine_asynchronous_nonsync_cut()
    test_strict_nonpisot_born_cut_and_bad_inputs()
    print("C4 bilateral birth: literal PIP and singular strict-control regressions passed.")
    require_contract("irreducible nonsingular parents cannot have bilaterally aligned interior born zero returns; a recurrent legal PIP source still exhibits a one-sided locally nonsynchronizing birth; singular full-rank negative is rejected; strict PIP C4 remains open")
